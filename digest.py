#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
============================================================================
  Health & Longevity Digest Agent  ("סוכן הבריאות והלונג'ביטי")
============================================================================
Runs inside GitHub Actions (see .github/workflows/health-digest.yml).

What it does, once every two weeks on Sunday morning:
  1. Reads RSS/Atom feeds from a curated list of reputable health,
     nutrition and longevity sites (full-text feeds).
  2. Removes any article it has already sent before (state in seen.json).
  3. Sorts the remaining NEW articles by publish date (newest first).
  4. Picks the top 6.
  5. Writes a short, original Hebrew summary of each one (via the Anthropic
     API). Summaries are in Claude's own words + a link back to the source,
     so nothing copyrighted is reproduced.
  6. Emails all 6 to you as a single nice HTML digest, via Gmail.
  7. Saves the 6 links into seen.json so they are never sent again.

Design goals (why it is built this way):
  - Self-contained: no database, no external service except Gmail + the
    Anthropic API. State lives in a JSON file committed back to the repo,
    exactly like a simple "seen articles" ledger.
  - Robust: one broken feed or one bad article never kills the whole run.
  - Legal & clean: we summarise in our own words and always link to the
    original. Several sources are Creative Commons / public domain anyway.
============================================================================
"""

import os
import re
import sys
import json
import ssl
import time
import html
import smtplib
import datetime as dt
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.utils import formataddr

import feedparser          # pip install feedparser
import requests            # pip install requests
from bs4 import BeautifulSoup  # pip install beautifulsoup4 lxml

# ---------------------------------------------------------------------------
# 0. CONFIG
# ---------------------------------------------------------------------------

# How many articles to send each run.
ARTICLES_PER_RUN = int(os.getenv("ARTICLES_PER_RUN", "6"))

# File that remembers which articles were already sent (relative to repo root).
SEEN_FILE = os.getenv("SEEN_FILE", "seen.json")

# Keep at most this many links in memory so seen.json never grows forever.
MAX_SEEN = 2000

# Only consider articles published within the last N days (avoids sending
# something ancient the first time a new feed is added). 45 days > 2 weeks,
# so nothing recent is ever missed.
MAX_AGE_DAYS = int(os.getenv("MAX_AGE_DAYS", "45"))

# Max articles from any single source per digest, so one prolific site (e.g.
# Fight Aging! posts daily) cannot fill the whole email. 0 = no limit.
MAX_PER_SOURCE = int(os.getenv("MAX_PER_SOURCE", "2"))

# If a feed's own text for an article is shorter than this many characters,
# the agent fetches the article page and extracts the full body, so the
# summary is based on the WHOLE article rather than a teaser.
MIN_FULLTEXT_CHARS = int(os.getenv("MIN_FULLTEXT_CHARS", "600"))

# Anthropic model used for the Hebrew summaries. Cheap + good enough.
# You can override with the ANTHROPIC_MODEL secret/variable if you like.
ANTHROPIC_MODEL = os.getenv("ANTHROPIC_MODEL", "claude-sonnet-5")

# A normal browser User-Agent. Some sites reject the default python UA.
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")

# --- The curated source list ------------------------------------------------
# Each entry: display name (Hebrew), primary feed URL, and the site homepage
# used as a fallback for auto-discovering the feed if the primary URL breaks.
FEEDS = [
    {"name": "Fight Aging!",
     "feed": "https://www.fightaging.org/feed/",
     "home": "https://www.fightaging.org/"},

    {"name": "The Conversation – Health",
     "feed": "https://theconversation.com/us/health/articles.atom",
     "home": "https://theconversation.com/us/health"},

    {"name": "NutritionFacts.org",
     "feed": "https://nutritionfacts.org/blog/feed/",
     "home": "https://nutritionfacts.org/blog/"},

    {"name": "Lifespan.io",
     "feed": "https://www.lifespan.io/feed/",
     "home": "https://www.lifespan.io/news/"},

    {"name": "ScienceDaily – Healthy Aging",
     "feed": "https://www.sciencedaily.com/rss/health_medicine/healthy_aging.xml",
     "home": "https://www.sciencedaily.com/news/health_medicine/healthy_aging/"},

    {"name": "Medical News Today",
     "feed": "https://www.medicalnewstoday.com/rss",
     "home": "https://www.medicalnewstoday.com/"},

    {"name": "Longevity.Technology",
     "feed": "https://longevity.technology/feed/",
     "home": "https://longevity.technology/news/"},

    {"name": "Harvard – Nutrition Source",
     "feed": "https://nutritionsource.hsph.harvard.edu/feed/",
     "home": "https://nutritionsource.hsph.harvard.edu/nutrition-news/"},

    {"name": "NIA (National Institute on Aging)",
     "feed": "https://www.nia.nih.gov/news/rss.xml",
     "home": "https://www.nia.nih.gov/news"},

    # ZOE has full-text articles but a less predictable feed. Auto-discovery
    # from the homepage handles it; if it ever returns nothing it is simply
    # skipped without affecting the run.
    {"name": "ZOE",
     "feed": "https://zoe.com/learn/rss.xml",
     "home": "https://zoe.com/learn"},
]


# ---------------------------------------------------------------------------
# 1. SMALL HELPERS
# ---------------------------------------------------------------------------

def log(msg):
    """Timestamped log line, visible in the Actions tab."""
    print(f"[{dt.datetime.now(dt.timezone.utc).strftime('%H:%M:%S')}] {msg}", flush=True)


def env(name, required=True, default=None):
    val = os.getenv(name, default)
    if required and not val:
        log(f"FATAL: missing required environment variable/secret: {name}")
        sys.exit(1)
    return val


def normalize_link(url):
    """Strip tracking junk so the same article is recognised across runs."""
    if not url:
        return ""
    url = url.split("#")[0]
    url = re.sub(r"([?&])(utm_[^=]+|fbclid|gclid|mc_cid|mc_eid)=[^&]*", r"\1", url)
    url = re.sub(r"[?&]+$", "", url)
    return url.strip().rstrip("/")


def load_seen():
    """Return a set of links already sent. Tolerates a missing/broken file."""
    try:
        with open(SEEN_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):          # supports {"links": [...]}
            data = data.get("links", [])
        return list(dict.fromkeys(data))    # de-dupe, keep order
    except (FileNotFoundError, json.JSONDecodeError):
        return []


def save_seen(seen_list):
    """Persist the seen links, newest last, capped at MAX_SEEN."""
    trimmed = seen_list[-MAX_SEEN:]
    with open(SEEN_FILE, "w", encoding="utf-8") as f:
        json.dump({"links": trimmed,
                   "updated": dt.datetime.now(dt.timezone.utc).isoformat()},
                  f, ensure_ascii=False, indent=2)


def entry_datetime(entry):
    """Best-effort published/updated time as an aware UTC datetime."""
    for key in ("published_parsed", "updated_parsed"):
        t = entry.get(key)
        if t:
            return dt.datetime.fromtimestamp(time.mktime(t), tz=dt.timezone.utc)
    # Unknown date -> treat as "now minus a bit" so it is not wrongly dropped.
    return dt.datetime.now(tz=dt.timezone.utc)


def clean_text(raw_html, limit=6000):
    """Turn feed HTML into plain text for the summariser."""
    if not raw_html:
        return ""
    soup = BeautifulSoup(raw_html, "lxml")
    for tag in soup(["script", "style", "figure", "img", "aside"]):
        tag.decompose()
    text = soup.get_text(" ", strip=True)
    text = re.sub(r"\s+", " ", text)
    return text[:limit]


# ---------------------------------------------------------------------------
# 2. FEED FETCHING (with auto-discovery fallback)
# ---------------------------------------------------------------------------

def http_get(url, timeout=30, tries=3):
    """GET with a real UA and a small backoff, so one transient error
    (a 503, a slow TLS handshake) does not silently drop a source."""
    headers = {
        "User-Agent": UA,
        "Accept": "application/rss+xml, application/atom+xml, application/xml;"
                  "q=0.9, text/html;q=0.8, */*;q=0.5",
    }
    last = None
    for i in range(tries):
        try:
            resp = requests.get(url, headers=headers, timeout=timeout)
            resp.raise_for_status()
            return resp
        except Exception as e:
            last = e
            if i < tries - 1:
                time.sleep(1.5 * (i + 1))
    raise last


def fetch_full_text(url, limit=6000):
    """Fetch an article page and extract its main body text.

    Used only when a feed gives just a short teaser, so the Hebrew summary
    is based on the FULL article. Best-effort: returns "" on any failure.
    """
    try:
        resp = http_get(url, timeout=25)
        soup = BeautifulSoup(resp.text, "lxml")
        for tag in soup(["script", "style", "nav", "header", "footer",
                         "aside", "form", "figure", "img", "noscript"]):
            tag.decompose()
        # Prefer semantic containers; fall back to the whole body.
        node = soup.find("article") or soup.find("main") or soup.body or soup
        text = re.sub(r"\s+", " ", node.get_text(" ", strip=True))
        return text[:limit]
    except Exception as e:
        log(f"    full-text fetch failed for {url}: {e}")
        return ""


def discover_feed(home_url):
    """If a hard-coded feed URL fails, find the real one from the homepage.

    Prefers the main feed and deliberately skips WordPress 'comments' feeds,
    which are also advertised via <link rel=alternate> on many of these sites.
    """
    from urllib.parse import urljoin
    try:
        r = http_get(home_url, timeout=25)
        soup = BeautifulSoup(r.text, "lxml")
        links = soup.find_all("link", attrs={"type": re.compile(r"rss|atom")})
        hrefs = [l.get("href") for l in links if l.get("href")]
        # First choice: a feed URL that is NOT a comments feed.
        for href in hrefs:
            if "comment" not in href.lower():
                return urljoin(home_url, href)
        # Fallback: whatever feed we found.
        if hrefs:
            return urljoin(home_url, hrefs[0])
    except Exception as e:
        log(f"    auto-discovery failed for {home_url}: {e}")
    return None


def _parse_feed(url):
    """Fetch a feed with requests (robust: gzip, redirects, real UA, retry)
    then hand the raw bytes to feedparser, which detects encoding itself."""
    resp = http_get(url, timeout=30)
    return feedparser.parse(resp.content)


def fetch_feed(source):
    """Return a list of normalised article dicts for one source."""
    articles = []

    # Try the configured feed URL; if it yields nothing, auto-discover.
    parsed = None
    for url in (source["feed"], "DISCOVER"):
        if url == "DISCOVER":
            url = discover_feed(source["home"])
            if not url:
                break
            log(f"    retrying with discovered feed: {url}")
        try:
            candidate = _parse_feed(url)
        except Exception as e:
            log(f"    error fetching {url}: {e}")
            continue
        if candidate.entries:
            parsed = candidate
            break

    if not parsed or not parsed.entries:
        log(f"  {source['name']}: 0 items (feed unavailable)")
        return articles

    for e in parsed.entries:
        link = normalize_link(e.get("link", ""))
        if not link:
            continue
        # Prefer the full <content:encoded>, then summary/description.
        body = ""
        if e.get("content"):
            body = e["content"][0].get("value", "")
        body = body or e.get("summary", "") or e.get("description", "")
        articles.append({
            "source": source["name"],
            "title": html.unescape((e.get("title") or "").strip()),
            "link": link,
            "when": entry_datetime(e),
            "text": clean_text(body),
        })

    log(f"  {source['name']}: {len(articles)} items")
    return articles


def _norm_title(t):
    """Lowercased, punctuation-stripped title for cross-source dedup.
    Keeps Hebrew (U+0590-05FF) and alphanumerics only."""
    return re.sub(r"[^a-z0-9\u0590-\u05ff]+", " ", (t or "").lower()).strip()


def gather_candidates():
    """All fresh, unseen articles across every source, newest first."""
    seen = set(load_seen())
    cutoff = dt.datetime.now(tz=dt.timezone.utc) - dt.timedelta(days=MAX_AGE_DAYS)

    pool = []
    empty_sources = []
    for source in FEEDS:
        got = fetch_feed(source)
        if not got:
            empty_sources.append(source["name"])
        for art in got:
            if art["link"] in seen:
                continue
            if art["when"] < cutoff:
                continue
            pool.append(art)

    # De-dupe by link (keep newest), then by normalised title across sources
    # (so the same wire story on two sites is not sent twice).
    by_link = {}
    for art in sorted(pool, key=lambda a: a["when"]):
        by_link[art["link"]] = art

    ordered, seen_titles = [], set()
    for art in sorted(by_link.values(), key=lambda a: a["when"], reverse=True):
        key = _norm_title(art["title"])
        if key and key in seen_titles:
            continue
        seen_titles.add(key)
        ordered.append(art)

    log(f"Total fresh & unseen candidates: {len(ordered)}")
    if empty_sources:
        log(f"Sources returning nothing this run: {', '.join(empty_sources)}")
    return ordered


def select_articles(candidates, n, max_per_source):
    """Pick n newest, but no more than max_per_source from any one site.
    If the cap leaves us short, top up with the next-newest regardless."""
    chosen, per = [], {}
    for art in candidates:                       # already newest-first
        if max_per_source and per.get(art["source"], 0) >= max_per_source:
            continue
        chosen.append(art)
        per[art["source"]] = per.get(art["source"], 0) + 1
        if len(chosen) >= n:
            return chosen
    # Not enough distinct-enough sources: fill remaining slots by recency.
    for art in candidates:
        if art not in chosen:
            chosen.append(art)
            if len(chosen) >= n:
                break
    return chosen


# ---------------------------------------------------------------------------
# 3. HEBREW SUMMARY (Anthropic API)
# ---------------------------------------------------------------------------

def summarize_he(article, api_key):
    """
    Original Hebrew summary in Claude's own words. No long verbatim quotes,
    so nothing copyrighted is reproduced - we always link to the source.
    Falls back to a short trimmed excerpt if the API call fails.
    """
    text = article["text"] or article["title"]
    prompt = (
        "לפניך כתבה בתחום הבריאות/תזונה/לונג'ביטי. כתוב סיכום קצר בעברית, "
        "במילים שלך בלבד (בלי ציטוטים ארוכים), 3-5 משפטים, בשפה נגישה ומדויקת. "
        "הסבר כל מונח טכני בסוגריים. הימנע מהגזמות ומקביעות סיבתיות שאין להן ביסוס. "
        "בשורה נפרדת בסוף, הוסף שורה אחת שמתחילה ב'למה זה חשוב:' עם המסקנה המעשית.\n\n"
        f"כותרת: {article['title']}\n\n"
        f"תוכן:\n{text}"
    )
    try:
        r = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={
                "x-api-key": api_key,
                "anthropic-version": "2023-06-01",
                "content-type": "application/json",
            },
            json={
                "model": ANTHROPIC_MODEL,
                "max_tokens": 700,
                "messages": [{"role": "user", "content": prompt}],
            },
            timeout=60,
        )
        r.raise_for_status()
        data = r.json()
        parts = [b.get("text", "") for b in data.get("content", [])
                 if b.get("type") == "text"]
        summary = "\n".join(p for p in parts if p).strip()
        if summary:
            return summary
    except Exception as e:
        log(f"    summary API failed for '{article['title'][:40]}': {e}")

    # Fallback: short excerpt, clearly marked.
    excerpt = (article["text"] or "")[:280].strip()
    return (excerpt + " …") if excerpt else "(לא הופק סיכום; ראה קישור למקור)"


# ---------------------------------------------------------------------------
# 4. EMAIL
# ---------------------------------------------------------------------------

def build_email_html(items, run_date):
    """A clean, RTL, mobile-friendly HTML digest."""
    cards = []
    for i, it in enumerate(items, 1):
        summary_html = html.escape(it["summary"]).replace("\n", "<br>")
        cards.append(f"""
        <div style="background:#ffffff;border:1px solid #ece7df;border-radius:14px;
                    padding:20px 22px;margin:0 0 18px 0;">
          <div style="font-size:13px;color:#B8925A;font-weight:700;
                      letter-spacing:.2px;margin-bottom:6px;">
            {i}. {html.escape(it['source'])}
            &nbsp;·&nbsp;{it['when'].strftime('%d.%m.%Y')}
          </div>
          <div style="font-size:18px;font-weight:800;line-height:1.4;
                      color:#1c1a17;margin-bottom:10px;">
            {html.escape(it['title'])}
          </div>
          <div style="font-size:15px;line-height:1.75;color:#3a352f;">
            {summary_html}
          </div>
          <a href="{html.escape(it['link'])}"
             style="display:inline-block;margin-top:14px;font-size:14px;
                    font-weight:700;color:#B8925A;text-decoration:none;">
            קריאת הכתבה המלאה ←
          </a>
        </div>""")

    return f"""<!DOCTYPE html>
<html dir="rtl" lang="he"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"></head>
<body style="margin:0;padding:24px 12px;background:#14110E;
             font-family:'Segoe UI',Arial,Helvetica,sans-serif;">
  <div style="max-width:640px;margin:0 auto;">
    <div style="text-align:center;padding:8px 0 22px 0;">
      <div style="font-size:24px;font-weight:800;color:#E6A23C;">
        כל מה שמעניין בבריאות
      </div>
      <div style="font-size:13px;color:#9a9186;margin-top:6px;">
        מקבץ דו-שבועי · {run_date.strftime('%d.%m.%Y')} · {len(items)} כתבות
      </div>
    </div>
    {''.join(cards)}
    <div style="text-align:center;color:#6f675d;font-size:12px;
                padding:14px 0 4px 0;">
      נאסף אוטומטית ממקורות בריאות, תזונה ולונג'ביטי מובילים.
      כל סיכום מנוסח מחדש ומקושר למקור.
    </div>
  </div>
</body></html>"""


def build_email_text(items, run_date):
    """A readable plain-text version (accessibility + if HTML is blocked)."""
    lines = [f"כל מה שמעניין בבריאות · {run_date.strftime('%d.%m.%Y')} · "
             f"{len(items)} כתבות", ""]
    for i, it in enumerate(items, 1):
        lines += [
            f"{i}. [{it['source']} · {it['when'].strftime('%d.%m.%Y')}]",
            it["title"],
            it["summary"],
            it["link"],
            "",
        ]
    return "\n".join(lines)


def send_email(html_body, text_body, subject, gmail_addr, gmail_pass, recipient):
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = formataddr(("Health Digest", gmail_addr))
    msg["To"] = recipient
    # Order matters: plain first, HTML second (clients pick the last they can show).
    msg.attach(MIMEText(text_body, "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))

    ctx = ssl.create_default_context()
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=ctx) as server:
        server.login(gmail_addr, gmail_pass)
        server.sendmail(gmail_addr, [recipient], msg.as_string())
    log(f"Email sent to {recipient}")


# ---------------------------------------------------------------------------
# 5. BIWEEKLY GATE
# ---------------------------------------------------------------------------

def should_run_today():
    """
    GitHub cron cannot express 'every 2 weeks', so the workflow fires every
    Sunday and we gate here: run only on EVEN ISO week numbers.

    - Manual runs (workflow_dispatch) always pass, via FORCE_RUN=1.
    - If the first automatic run lands on the 'wrong' week, either wait one
      week or flip EVEN_WEEKS to False.
    """
    if os.getenv("FORCE_RUN", "").strip() in ("1", "true", "yes"):
        log("FORCE_RUN set - bypassing biweekly gate.")
        return True

    even_weeks = os.getenv("EVEN_WEEKS", "true").lower() != "false"
    week = dt.date.today().isocalendar()[1]
    is_even = (week % 2 == 0)
    run = is_even if even_weeks else (not is_even)
    log(f"ISO week {week} (even={is_even}); biweekly gate -> {'RUN' if run else 'SKIP'}")
    return run


# ---------------------------------------------------------------------------
# 6. MAIN
# ---------------------------------------------------------------------------

def main():
    if not should_run_today():
        log("Not a scheduled digest week. Exiting cleanly.")
        return

    gmail_addr = env("GMAIL_ADDRESS")
    gmail_pass = env("GMAIL_APP_PASSWORD")
    # NOTE: the workflow always sets RECIPIENT (to "" when the secret is
    # undefined), so `getenv(..., default)` would return "" not the default.
    # `or` correctly falls back to the Gmail address when it is blank.
    recipient  = os.getenv("RECIPIENT") or gmail_addr
    api_key    = env("ANTHROPIC_API_KEY")

    log("Gathering candidate articles...")
    candidates = gather_candidates()
    if not candidates:
        log("No new articles this run. Nothing to send. Exiting.")
        return

    chosen = select_articles(candidates, ARTICLES_PER_RUN, MAX_PER_SOURCE)
    log(f"Selected {len(chosen)} articles. Enriching + summarising...")

    for it in chosen:
        # If the feed gave only a teaser, fetch the full article body first,
        # so the summary reflects the WHOLE article (the core requirement).
        if len(it["text"]) < MIN_FULLTEXT_CHARS:
            full = fetch_full_text(it["link"])
            if len(full) > len(it["text"]):
                it["text"] = full
        it["summary"] = summarize_he(it, api_key)
        log(f"  ✓ {it['source']}: {it['title'][:60]}")

    run_date = dt.date.today()
    subject = f"כל מה שמעניין בבריאות · {run_date.strftime('%d.%m.%Y')} · {len(chosen)} כתבות"
    html_body = build_email_html(chosen, run_date)
    text_body = build_email_text(chosen, run_date)

    # Send FIRST. Only if the email succeeds do we mark articles as seen,
    # so a failure never silently 'burns' articles.
    send_email(html_body, text_body, subject, gmail_addr, gmail_pass, recipient)

    seen = load_seen()
    seen.extend(it["link"] for it in chosen)
    seen = list(dict.fromkeys(seen))
    save_seen(seen)
    log(f"Updated {SEEN_FILE} (+{len(chosen)}, total {len(seen)}).")
    log("Done.")


if __name__ == "__main__":
    main()
