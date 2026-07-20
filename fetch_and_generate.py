#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Weekly LinkedIn post-suggestion agent for Ran.

Flow:
  1. Query PubMed for articles added in the last N days across 10 journals.
  2. Fetch abstracts + metadata.
  3. Ask Claude to pick the 3 best for Ran's audience.
  4. For each of the 3, ask Claude to write a full Hebrew post draft in Ran's
     voice (per the embedded skill), TEXT ONLY, no image, no image prompt.
  5. Email the 3 drafts (RTL HTML) to the recipient.

Runs on GitHub Actions (see .github/workflows/weekly-posts.yml).
Requires secrets: ANTHROPIC_API_KEY, GMAIL_ADDRESS, GMAIL_APP_PASSWORD.
Optional: NCBI_API_KEY (raises PubMed rate limit), RECIPIENT, MODEL, RELDATE.
"""

import os
import sys
import json
import time
import html
import smtplib
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from datetime import datetime, timezone

# ----------------------------------------------------------------------------
# CONFIG
# ----------------------------------------------------------------------------

# The 10 journals (full NLM titles as indexed in PubMed).
JOURNALS = [
    "The American journal of clinical nutrition",
    "Cell metabolism",
    "Nature metabolism",
    "Nature aging",
    "The Lancet. Healthy longevity",
    "GeroScience",
    "Aging cell",
    "British journal of sports medicine",
    "Medicine and science in sports and exercise",
    "Sports medicine (Auckland, N.Z.)",
]

# How many days back to scan (8 = one week + a small buffer against missed runs).
RELDATE = int(os.environ.get("RELDATE", "8"))

# Model. NOTE: API model names/pricing change over time. Verify current strings
# at docs.claude.com if a call fails. "claude-opus-4-8" balances cost/quality.
MODEL = os.environ.get("MODEL", "claude-opus-4-8")

RECIPIENT = os.environ.get("RECIPIENT", "ranrosto@gmail.com")

# How many candidate abstracts to hand the ranker (keeps token cost sane).
MAX_CANDIDATES = int(os.environ.get("MAX_CANDIDATES", "40"))
# How many suggestions to produce.
N_SUGGESTIONS = 3

ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
NCBI_API_KEY = os.environ.get("NCBI_API_KEY", "")  # optional

EUTILS = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils"
ANTHROPIC_URL = "https://api.anthropic.com/v1/messages"

HERE = os.path.dirname(os.path.abspath(__file__))
VOICE_PATH = os.path.join(HERE, "ran_voice.md")

# Memory of articles already suggested (committed back to the repo each run).
SEEN_PATH = os.path.join(HERE, "seen_pmids.json")
SEEN_MAX = 3000  # cap the stored list so it never grows unbounded

# PubMed Central full-text (Open Access subset only).
PMC_IDCONV = "https://www.ncbi.nlm.nih.gov/pmc/utils/idconv/v1.0/"
FULLTEXT_MAX_CHARS = 14000  # truncate very long articles to control token cost

# Europe PMC: a second full-text source. Its open-access coverage is often
# broader than NCBI's PMC OA subset (it also holds author manuscripts), and its
# search endpoint can resolve a PMCID that NCBI's idconv misses.
EUROPE_PMC = "https://www.ebi.ac.uk/europepmc/webservices/rest"
FULLTEXT_MIN_CHARS = 800  # below this we treat the fetch as a failure


# ----------------------------------------------------------------------------
# PubMed
# ----------------------------------------------------------------------------

def _ncbi_params(extra):
    p = {"tool": "ran-post-agent", "email": RECIPIENT}
    if NCBI_API_KEY:
        p["api_key"] = NCBI_API_KEY
    p.update(extra)
    return p


def _get(url, params, is_json=False, retries=3):
    q = urllib.parse.urlencode(params or {})
    full = f"{url}?{q}" if q else url
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(full, timeout=60) as r:
                data = r.read().decode("utf-8", errors="replace")
            return json.loads(data) if is_json else data
        except Exception:
            if attempt == retries - 1:
                raise
            time.sleep(1.5 * (attempt + 1))


def esearch_pmids():
    """Return (pmids, per_journal_counts)."""
    per_journal = {}
    all_pmids = []
    for j in JOURNALS:
        term = f'"{j}"[Journal]'
        params = _ncbi_params({
            "db": "pubmed",
            "term": term,
            "reldate": RELDATE,
            "datetype": "edat",       # entrez date = when added to PubMed
            "retmax": 100,
            "retmode": "json",
            "sort": "date",
        })
        try:
            res = _get(f"{EUTILS}/esearch.fcgi", params, is_json=True)
            ids = res.get("esearchresult", {}).get("idlist", [])
        except Exception as e:
            print(f"[warn] esearch failed for {j}: {e}", file=sys.stderr)
            ids = []
        per_journal[j] = len(ids)
        all_pmids.extend(ids)
        time.sleep(0.34 if not NCBI_API_KEY else 0.11)  # NCBI rate etiquette
    # de-dup, preserve order
    seen, uniq = set(), []
    for pid in all_pmids:
        if pid not in seen:
            seen.add(pid)
            uniq.append(pid)
    return uniq[:MAX_CANDIDATES], per_journal


def _text(node):
    return "".join(node.itertext()).strip() if node is not None else ""


def efetch_articles(pmids):
    """Fetch metadata + abstracts. Returns list of dicts."""
    if not pmids:
        return []
    params = _ncbi_params({
        "db": "pubmed",
        "id": ",".join(pmids),
        "rettype": "abstract",
        "retmode": "xml",
    })
    xml_data = _get(f"{EUTILS}/efetch.fcgi", params)
    root = ET.fromstring(xml_data)
    out = []
    for art in root.findall(".//PubmedArticle"):
        pmid = _text(art.find(".//PMID"))
        title = _text(art.find(".//ArticleTitle"))
        journal = _text(art.find(".//Journal/Title"))
        year = _text(art.find(".//JournalIssue/PubDate/Year")) or \
            _text(art.find(".//ArticleDate/Year"))
        # abstract may be multiple labelled sections
        abs_parts = []
        for ab in art.findall(".//Abstract/AbstractText"):
            label = ab.get("Label")
            txt = _text(ab)
            abs_parts.append(f"{label}: {txt}" if label else txt)
        abstract = "\n".join(p for p in abs_parts if p).strip()
        # publication types help evidence grading
        ptypes = [_text(pt) for pt in art.findall(".//PublicationType")]
        # doi
        doi = ""
        for aid in art.findall(".//ArticleId"):
            if aid.get("IdType") == "doi":
                doi = _text(aid)
                break
        if not abstract:
            continue  # no abstract, cannot write responsibly
        out.append({
            "pmid": pmid,
            "title": title,
            "journal": journal,
            "year": year,
            "abstract": abstract,
            "pub_types": ptypes,
            "doi": doi,
            "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/",
        })
    return out


# ----------------------------------------------------------------------------
# Anthropic
# ----------------------------------------------------------------------------

def anthropic(messages, system, max_tokens=1600, temperature=0.7):
    body = {
        "model": MODEL,
        "max_tokens": max_tokens,
        "system": system,
        "messages": messages,
    }
    req = urllib.request.Request(
        ANTHROPIC_URL,
        data=json.dumps(body).encode("utf-8"),
        headers={
            "content-type": "application/json",
            "x-api-key": ANTHROPIC_API_KEY,
            "anthropic-version": "2023-06-01",
        },
        method="POST",
    )
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                data = json.loads(r.read().decode("utf-8"))
            return "".join(b.get("text", "") for b in data.get("content", [])
                           if b.get("type") == "text")
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", errors="replace")
            print(f"[anthropic HTTP {e.code}] {detail}", file=sys.stderr)
            if e.code in (429, 529) and attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            raise
        except Exception:
            if attempt < 2:
                time.sleep(3 * (attempt + 1))
                continue
            raise


def parse_json(text):
    """Strip code fences and parse JSON."""
    t = text.strip()
    if t.startswith("```"):
        t = t.split("```", 2)[1]
        if t.startswith("json"):
            t = t[4:]
        t = t.strip()
        if t.endswith("```"):
            t = t[:-3].strip()
    # find first { or [
    for opener, closer in (("[", "]"), ("{", "}")):
        i = t.find(opener)
        if i != -1:
            depth, j = 0, i
            for j in range(i, len(t)):
                if t[j] == opener:
                    depth += 1
                elif t[j] == closer:
                    depth -= 1
                    if depth == 0:
                        break
            return json.loads(t[i:j + 1])
    return json.loads(t)


def rank_articles(articles):
    """Return the indices of the top N articles for Ran's audience."""
    listing = []
    for i, a in enumerate(articles):
        ab = a["abstract"][:1400]
        listing.append(
            f'[{i}] journal="{a["journal"]}" ({a["year"]}) '
            f'types={a["pub_types"]}\ntitle: {a["title"]}\nabstract: {ab}\n'
        )
    system = (
        "You help select scientific articles for a Hebrew LinkedIn audience "
        "interested in clinical nutrition, longevity/aging, health, and sports "
        "science. Ran is a clinical dietitian with a PhD; his readers are "
        "educated laypeople and professionals. "
        "Pick the articles that will make the best, most accurate, most "
        "engaging posts. STRONGLY prefer: human studies, higher evidence "
        "(meta-analysis, systematic review, large RCT, large cohort), a clear "
        "practical takeaway, and a counter-intuitive or timely finding. "
        "AVOID: pure cell/animal studies unless the finding is striking and "
        "clearly framed as preliminary; narrow methodological papers; "
        "editorials; anything with no usable takeaway for a general audience. "
        f"Return ONLY a JSON array of exactly {N_SUGGESTIONS} objects (or fewer "
        "if fewer are suitable), each: "
        '{"index": <int>, "reason": "<one short sentence, Hebrew>"}. '
        "No prose, no markdown, JSON only."
    )
    user = "Candidate articles:\n\n" + "\n".join(listing)
    raw = anthropic([{"role": "user", "content": user}], system,
                    max_tokens=700, temperature=0.3)
    try:
        picks = parse_json(raw)
        idxs = [p["index"] for p in picks if isinstance(p.get("index"), int)
                and 0 <= p["index"] < len(articles)]
    except Exception as e:
        print(f"[warn] ranking parse failed: {e}; falling back to first N",
              file=sys.stderr)
        idxs = list(range(min(N_SUGGESTIONS, len(articles))))
    # de-dup, cap
    seen, final = set(), []
    for i in idxs:
        if i not in seen:
            seen.add(i)
            final.append(i)
    return final[:N_SUGGESTIONS]


def write_post(article, voice):
    system = (
        voice
        + "\n\n---\n\n## פורמט הפלט לסוכן זה\n"
        "כתוב טיוטת פוסט אחת בעברית בקול של רן על סמך ה-abstract שיסופק. "
        "החזר JSON תקין בלבד, בלי טקסט מסביב ובלי markdown, במבנה:\n"
        "{\n"
        '  "hook": "שורת הפתיחה או ההוק, בנפרד",\n'
        '  "post_body": "גוף הפוסט המלא בעברית, מוכן להעתקה, עם שבירות שורה (\\n) בין פסקאות",\n'
        '  "evidence_level": "מטא-אנליזה / סקירה שיטתית / RCT / קוהורט / תצפיתי / פרה-קליני / אחר",\n'
        '  "evidence_note": "משפט קצר בעברית: כמה הראיה חזקה, ואיזה סיוג נדרש",\n'
        '  "usable": true או false (false אם ה-abstract דק/מוקדם/לא אחראי לפוסט),\n'
        '  "usable_note": "אם usable=false, הסבר קצר בעברית למה"\n'
        "}\n"
        "אין תמונה, אין פרומפט לתמונה, אין שדה ויזואל. אל תמציא מספרים שלא "
        "מופיעים בחומר שסופק. חוזק הניסוח בפוסט לא יעלה על חוזק הראיה.\n"
        "אם סופק טקסט מלא (methods, results, discussion, limitations), נצל אותו "
        "לדיוק: התבסס על התוצאות המלאות והמגבלות שהחוקרים עצמם ציינו, לא רק על "
        "התקציר.\n"
        "דרישת אורך מחייבת: post_body הוא פוסט מלא של 200 עד 350 מילים, "
        "מספר פסקאות עם עמוד שדרה אחד, פתיחה, גוף וסיומת רכה. "
        "טיוטה של שורה או שתיים היא כישלון ואסורה."
    )
    src = article.get("source_type", "תקציר")
    content = article.get("content") or article["abstract"]
    meta = (
        f'כתב עת: {article["journal"]} ({article["year"]})\n'
        f'סוגי פרסום: {", ".join(article["pub_types"]) or "לא צוין"}\n'
        f'PMID: {article["pmid"]}\n'
        f'מקור החומר: {src}\n'
        f'כותרת: {article["title"]}\n\n'
        f'{content}'
    )
    raw = anthropic([{"role": "user", "content": meta}], system,
                    max_tokens=1800, temperature=0.75)
    try:
        return parse_json(raw)
    except Exception as e:
        print(f"[warn] post parse failed for PMID {article['pmid']}: {e}",
              file=sys.stderr)
        return {
            "hook": "(שגיאת עיבוד, ראו טקסט גולמי למטה)",
            "post_body": raw,
            "evidence_level": "לא זוהה",
            "evidence_note": "",
            "usable": True,
            "usable_note": "",
        }


# ----------------------------------------------------------------------------
# Email
# ----------------------------------------------------------------------------

def build_email_html(suggestions, per_journal, scanned_count):
    def esc(s):
        return html.escape(s or "")

    def nl2br(s):
        return esc(s).replace("\n", "<br>")

    blocks = []
    for n, (article, post) in enumerate(suggestions, 1):
        usable = post.get("usable", True)
        warn = ""
        if not usable:
            warn = (
                '<div style="background:#3a1f1f;border-right:4px solid #E6A23C;'
                'padding:10px 14px;margin:8px 0;color:#F5F1EA;border-radius:6px;">'
                '&#9888; שים לב: המחקר סומן כדק או מוקדם לפוסט אחראי. '
                + esc(post.get("usable_note", "")) + '</div>'
            )
        blocks.append(f"""
        <div style="background:#1c1813;border:1px solid #2b241c;border-radius:12px;
                    padding:22px;margin:0 0 26px 0;">
          <div style="color:#E6A23C;font-weight:800;font-size:15px;margin-bottom:6px;">
            הצעה {n}
          </div>
          {warn}
          <div style="color:#9A8F80;font-size:12px;margin-bottom:4px;">הוק</div>
          <div style="color:#F5F1EA;font-weight:700;font-size:17px;line-height:1.6;
                      margin-bottom:16px;">{nl2br(post.get('hook',''))}</div>

          <div style="color:#9A8F80;font-size:12px;margin-bottom:4px;">גוף הפוסט</div>
          <div style="color:#EDE7DD;font-size:15px;line-height:1.85;
                      white-space:normal;">{nl2br(post.get('post_body',''))}</div>

          <div style="border-top:1px solid #2b241c;margin-top:18px;padding-top:12px;
                      color:#9A8F80;font-size:13px;line-height:1.7;">
            <div><b style="color:#E6A23C;">רמת ראיה:</b> {esc(post.get('evidence_level',''))}
                 &nbsp;|&nbsp; {esc(post.get('evidence_note',''))}</div>
            <div style="margin-top:4px;"><b style="color:#E6A23C;">מקור:</b>
                 {esc(article['journal'])} ({esc(article['year'])}) &nbsp;|&nbsp;
                 PMID <a href="{esc(article['url'])}" style="color:#E6A23C;">
                 {esc(article['pmid'])}</a>
                 {(' | DOI ' + esc(article['doi'])) if article.get('doi') else ''}</div>
            <div style="margin-top:4px;"><b style="color:#E6A23C;">נכתב מ:</b>
                 {esc(article.get('source_type', 'תקציר'))}
                 {(' &middot; ' + esc(article['source_detail'])) if article.get('source_detail') else ''}</div>
          </div>
        </div>""")

    journal_diag = "; ".join(
        f"{j.split('(')[0].strip()}: {c}" for j, c in per_journal.items()
    )

    # Summary of how many of this run's suggestions reached full text, and from
    # where. Derived from the articles already annotated by upgrade_to_fulltext.
    n_total = len(suggestions)
    n_full = sum(1 for a, _ in suggestions
                 if a.get("source_type") == "טקסט מלא")
    src_counts = {}
    for a, _ in suggestions:
        if a.get("source_type") == "טקסט מלא":
            # source_detail looks like "PMC (NCBI OA) · PMCxxx · 1,234 תווים"
            label = a.get("source_detail", "").split(" · ")[0] or "לא ידוע"
            src_counts[label] = src_counts.get(label, 0) + 1
    if n_total:
        src_breakdown = (
            " (" + ", ".join(f"{k}: {v}" for k, v in src_counts.items()) + ")"
            if src_counts else ""
        )
        fulltext_diag = (
            f"טקסט מלא: {n_full} מתוך {n_total} הצעות{src_breakdown}. "
            f"היתר נכתבו מהתקציר."
        )
    else:
        fulltext_diag = ""

    today = datetime.now(timezone.utc).strftime("%d/%m/%Y")

    return f"""<!doctype html>
<html dir="rtl" lang="he"><head><meta charset="utf-8"></head>
<body style="margin:0;padding:0;background:#14110E;">
<div style="max-width:680px;margin:0 auto;padding:28px 20px;
            font-family:Arial,Helvetica,sans-serif;direction:rtl;text-align:right;">
  <div style="color:#F5F1EA;font-size:22px;font-weight:800;">
    3 הצעות לפוסט &middot; {today}
  </div>
  <div style="color:#9A8F80;font-size:13px;margin:6px 0 22px 0;line-height:1.6;">
    מבוסס על {scanned_count} מאמרים חדשים שנסרקו השבוע מ-10 כתבי העת. טיוטות בלבד,
    מיועדות לאימות שלך לפני פרסום. אין תמונות.
  </div>
  {''.join(blocks)}
  <div style="color:#6B6258;font-size:11px;line-height:1.7;border-top:1px solid #2b241c;
              padding-top:12px;margin-top:6px;">
    {(esc(fulltext_diag) + '<br>') if fulltext_diag else ''}ספירת מאמרים חדשים לכל כתב עת: {esc(journal_diag)}
  </div>
</div></body></html>"""


def send_email(subject, html_body):
    sender = os.environ["GMAIL_ADDRESS"]
    password = os.environ["GMAIL_APP_PASSWORD"]
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = sender
    msg["To"] = RECIPIENT
    msg.attach(MIMEText("הצעות הפוסט השבועיות מצורפות ב-HTML.", "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=60) as s:
        s.login(sender, password)
        s.sendmail(sender, [RECIPIENT], msg.as_string())


# ----------------------------------------------------------------------------
# Memory: articles already suggested
# ----------------------------------------------------------------------------

def load_seen():
    try:
        with open(SEEN_PATH, encoding="utf-8") as f:
            data = json.load(f)
        pmids = data.get("pmids", []) if isinstance(data, dict) else data
        return set(str(p) for p in pmids)
    except Exception:
        return set()  # first run, or file missing/corrupt


def save_seen(seen):
    lst = list(seen)[-SEEN_MAX:]
    with open(SEEN_PATH, "w", encoding="utf-8") as f:
        json.dump({"pmids": lst}, f, ensure_ascii=False, indent=0)


# ----------------------------------------------------------------------------
# PubMed Central full text (Open Access subset)
# ----------------------------------------------------------------------------

def get_pmcid(pmid):
    """Return 'PMCxxardxxx' if an Open Access full text exists, else None."""
    params = _ncbi_params({"ids": pmid, "idtype": "pmid", "format": "json"})
    try:
        res = _get(PMC_IDCONV, params, is_json=True)
        for rec in res.get("records", []):
            if rec.get("pmcid"):
                return rec["pmcid"]
    except Exception as e:
        print(f"[warn] idconv failed for {pmid}: {e}", file=sys.stderr)
    return None


def _local(tag):
    """Strip an XML namespace, returning just the local tag name."""
    return tag.split("}")[-1]


def _extract_body_text(root):
    """Extract readable body text from a JATS/PMC XML tree.

    Collects section titles and paragraphs inside <body> only, so <front>
    (metadata) and <back> (references) are skipped. Robust to namespaces and
    to trees where <body> is nested. Returns '' if no body is found.
    """
    body = None
    for el in root.iter():
        if _local(el.tag) == "body":
            body = el
            break
    if body is None:
        return ""

    wanted = {"title", "p"}
    parts = []
    for node in body.iter():
        if _local(node.tag) in wanted:
            txt = _text(node)
            if txt and len(txt) > 1:
                parts.append(txt)
    # collapse consecutive duplicates (captions/titles sometimes repeat)
    cleaned = []
    for p in parts:
        if not cleaned or cleaned[-1] != p:
            cleaned.append(p)
    return "\n".join(cleaned).strip()


def fetch_pmc_fulltext(pmcid):
    """Full text from NCBI PMC (Open Access subset), or '' if unavailable."""
    numeric = pmcid.replace("PMC", "")
    params = _ncbi_params({"db": "pmc", "id": numeric,
                           "rettype": "xml", "retmode": "xml"})
    try:
        xml_data = _get(f"{EUTILS}/efetch.fcgi", params)
        root = ET.fromstring(xml_data)
    except Exception as e:
        print(f"[warn] pmc efetch failed for {pmcid}: {e}", file=sys.stderr)
        return ""
    return _extract_body_text(root)[:FULLTEXT_MAX_CHARS]


def europepmc_lookup(pmid):
    """Ask Europe PMC to resolve a PMCID for this PMID.

    Europe PMC sometimes indexes an open-access PMCID that NCBI's idconv does
    not return. Returns the PMCID string (e.g. 'PMC123456') or None.
    """
    params = {"query": f"EXT_ID:{pmid} AND SRC:MED",
              "format": "json", "resultType": "core", "pageSize": 1}
    try:
        res = _get(f"{EUROPE_PMC}/search", params, is_json=True)
        results = res.get("resultList", {}).get("result", [])
        if results:
            return results[0].get("pmcid") or None
    except Exception as e:
        print(f"[warn] europepmc lookup failed for {pmid}: {e}",
              file=sys.stderr)
    return None


def fetch_europepmc_fulltext(pmcid):
    """Full text from Europe PMC's full-text XML endpoint, or ''."""
    try:
        xml_data = _get(f"{EUROPE_PMC}/{pmcid}/fullTextXML", {})
        root = ET.fromstring(xml_data)
    except Exception as e:
        print(f"[warn] europepmc fulltext failed for {pmcid}: {e}",
              file=sys.stderr)
        return ""
    return _extract_body_text(root)[:FULLTEXT_MAX_CHARS]


def upgrade_to_fulltext(article):
    """Try hard to attach full text to an article, in place.

    Strategy (stops at first success):
      1. Resolve candidate PMCIDs from TWO resolvers: NCBI idconv + Europe PMC.
      2. For each PMCID, try NCBI PMC OA efetch, then Europe PMC full-text XML.
    Falls back cleanly to the abstract. Sets these keys on `article`:
      source_type   -> 'טקסט מלא' | 'תקציר'
      source_detail -> human-readable provenance for the email footer
      fulltext_chars-> int, how many chars of body text were attached
      content       -> what write_post() actually sends to the model
    """
    pmid = article["pmid"]
    article["source_type"] = "תקציר"
    article["source_detail"] = "PubMed abstract"
    article["fulltext_chars"] = 0
    article["content"] = article["abstract"]

    # Collect PMCID candidates from both resolvers, de-duplicated, order kept.
    pmcids = []
    for resolver in (get_pmcid, europepmc_lookup):
        try:
            pmcid = resolver(pmid)
        except Exception as e:
            print(f"[warn] resolver {resolver.__name__} raised for {pmid}: {e}",
                  file=sys.stderr)
            pmcid = None
        if pmcid and pmcid not in pmcids:
            pmcids.append(pmcid)

    # Try each PMCID against each full-text source.
    for pmcid in pmcids:
        for label, fetch in (("PMC (NCBI OA)", fetch_pmc_fulltext),
                             ("Europe PMC", fetch_europepmc_fulltext)):
            ft = fetch(pmcid)
            if ft and len(ft) > FULLTEXT_MIN_CHARS:
                ft = ft[:FULLTEXT_MAX_CHARS]
                article["content"] = (
                    f'{article["abstract"]}\n\n--- טקסט מלא ---\n{ft}')
                article["source_type"] = "טקסט מלא"
                article["source_detail"] = (
                    f"{label} · {pmcid} · {len(ft):,} תווים")
                article["fulltext_chars"] = len(ft)
                article["pmcid"] = pmcid
                return
    # nothing usable found -> abstract stays


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------

def main():
    if not ANTHROPIC_API_KEY:
        print("Missing ANTHROPIC_API_KEY", file=sys.stderr)
        sys.exit(1)

    with open(VOICE_PATH, encoding="utf-8") as f:
        voice = f.read()

    print("Searching PubMed...")
    pmids, per_journal = esearch_pmids()
    print("Per-journal counts:", per_journal)
    print(f"Total unique candidates: {len(pmids)}")

    articles = efetch_articles(pmids)
    print(f"Articles with abstracts: {len(articles)}")

    # Drop anything already suggested in a previous week.
    seen = load_seen()
    before = len(articles)
    articles = [a for a in articles if a["pmid"] not in seen]
    print(f"Skipped {before - len(articles)} already-suggested; "
          f"{len(articles)} new remain.")

    if not articles:
        subject = "אין מאמרים חדשים השבוע - סוכן הפוסטים"
        body = build_email_html([], per_journal, 0)
        send_email(subject, body)
        print("No new articles this week. Notification sent.")
        return

    top_idx = rank_articles(articles)
    print("Selected indices:", top_idx)

    suggestions = []
    for i in top_idx:
        a = articles[i]
        # Try hard to upgrade from abstract to full text (two resolvers,
        # two full-text sources) before writing.
        upgrade_to_fulltext(a)
        print(f"Writing post for PMID {a['pmid']} "
              f"(source: {a['source_type']} | {a.get('source_detail','')})...")
        post = write_post(a, voice)
        suggestions.append((a, post))
        time.sleep(1)

    subject = f"3 הצעות לפוסט - {datetime.now(timezone.utc).strftime('%d/%m')}"
    body = build_email_html(suggestions, per_journal, len(articles))
    send_email(subject, body)
    print(f"Sent {len(suggestions)} suggestions to {RECIPIENT}.")

    # Record what we suggested so it never repeats.
    for a, _ in suggestions:
        seen.add(a["pmid"])
    save_seen(seen)
    print(f"Memory updated: {len(seen)} PMIDs recorded.")


if __name__ == "__main__":
    main()
