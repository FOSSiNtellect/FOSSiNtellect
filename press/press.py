#!/usr/bin/env python3
"""The FOSSiNtellect printing press.

Reads newsroom.toml and the live GitHub figures, then prints the profile:
assets/*.svg (the newspaper pages) and README.md (how they are laid out).
Standard library only, so it runs anywhere Python 3.11+ does.

    python press/press.py               # print this week's edition
    python press/press.py --offline     # skip the GitHub API, reuse the last figures
    python press/press.py --date 2026-01-01
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import html
import json
import math
import os
import random
import re
import tomllib
import urllib.error
import urllib.request
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from xml.sax.saxutils import escape

ROOT = Path(__file__).resolve().parent.parent
FONTS = ROOT / "press" / "fonts"
LEDGER = ROOT / "press" / "ledger.json"
ASSETS = ROOT / "assets"

W = 840  # every page is drawn on an 840-unit canvas, the width of GitHub's README column
# The day edition is printed in black and white; only the margin notes are in pen.
# Every colour here must be distinct, since the night edition swaps them one for one.
INK = "#141414"
INK_SOFT = "#595959"
ACCENT = "#262626"
PEN = "#23428c"  # the blue ballpoint of the margin notes
PAPER_TONES = ("#ffffff", "#fefefe", "#fdfdfd", "#fcfcfc")

# The night edition, for GitHub's dark theme: every day colour above maps to one here.
NIGHT = {INK: "#e9e4d8", INK_SOFT: "#a29b8d", ACCENT: "#e8826f", PEN: "#8cb2ff",
         **dict(zip(PAPER_TONES, ("#1c1f25", "#1e2128", "#1a1d23", "#20232a")))}

MONTHS = ("January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December")
AP_MONTHS = ("Jan.", "Feb.", "March", "April", "May", "June", "July",
             "Aug.", "Sept.", "Oct.", "Nov.", "Dec.")


# ── Type ────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Face:
    key: str
    css: str
    upm: int
    cap: float
    widths: dict[str, int]

    def width(self, text: str, size: float, tracking: float = 0.0) -> float:
        fallback = self.widths.get("n", self.upm // 2)
        units = sum(self.widths.get(ch, fallback) for ch in text)
        return units / self.upm * size + tracking * len(text)


def _load_faces() -> dict[str, Face]:
    metrics = json.loads((FONTS / "metrics.json").read_text(encoding="utf-8"))
    css = {"serif": "r", "serif-bold": "b", "serif-italic": "i", "hand": "h"}
    return {k: Face(k, css[k], m["upm"], m["capHeight"] / m["upm"], m["widths"])
            for k, m in metrics.items()}


FACES = _load_faces()
R, B, I, H = (FACES[k] for k in ("serif", "serif-bold", "serif-italic", "hand"))

FONT_RULES = {
    "serif": ("OldStandard", "normal", "normal"),
    "serif-bold": ("OldStandard", "700", "normal"),
    "serif-italic": ("OldStandard", "normal", "italic"),
    "hand": ("Caveat", "normal", "normal"),
}
BASE_CSS = (
    'text{fill:%s;font-family:OldStandard,Georgia,"Times New Roman",serif;'
    "font-kerning:none;font-variant-ligatures:none}"
    ".r{font-family:OldStandard,Georgia,serif}"
    ".b{font-family:OldStandard,Georgia,serif;font-weight:700}"
    ".i{font-family:OldStandard,Georgia,serif;font-style:italic}"
    '.h{font-family:Caveat,"Segoe Print","Bradley Hand",cursive;font-kerning:normal}' % INK
)
def paper_defs(grain: tuple, stain: tuple, edge: str, edge_opacity: float, shadow: float) -> str:
    """Shadow, grain, faint stains and darker edges for a sheet. grain/stain are RGB in 0-1."""
    (gr, gg, gb), (sr, sg, sb) = grain, stain
    return (
        '<filter id="shadow" x="-4%" y="-4%" width="108%" height="108%">'
        f'<feDropShadow dx="0" dy="1.6" stdDeviation="2.6" flood-color="#000" flood-opacity="{shadow:g}"/></filter>'
        '<filter id="grain" x="0" y="0" width="100%" height="100%">'
        '<feTurbulence type="fractalNoise" baseFrequency=".9" numOctaves="2" seed="3" stitchTiles="stitch"/>'
        f'<feColorMatrix values="0 0 0 0 {gr:g} 0 0 0 0 {gg:g} 0 0 0 0 {gb:g} 1.3 0 0 0 -.52"/></filter>'
        '<filter id="stain" x="0" y="0" width="100%" height="100%">'
        '<feTurbulence type="fractalNoise" baseFrequency=".005 .008" numOctaves="2" seed="11"/>'
        f'<feColorMatrix values="0 0 0 0 {sr:g} 0 0 0 0 {sg:g} 0 0 0 0 {sb:g} 1.7 0 0 0 -.8"/></filter>'
        '<radialGradient id="age" cx="50%" cy="45%" r="75%">'
        f'<stop offset=".62" stop-color="{edge}" stop-opacity="0"/>'
        f'<stop offset="1" stop-color="{edge}" stop-opacity="{edge_opacity:g}"/></radialGradient>'
    )


DEFS = paper_defs((.55, .55, .55), (1, 1, 1), "#000000", 0, 0.18)  # clean white: faint grain, no stains
NIGHT_DEFS = paper_defs((.36, .37, .4), (0, 0, 0), "#000000", 0.3, 0.55)


def night_edition(svg: str) -> str:
    """The same page for GitHub's dark theme: dark newsprint, light ink."""
    svg = svg.replace(DEFS, NIGHT_DEFS)
    for day, night in NIGHT.items():
        svg = svg.replace(day, night)
    return svg

Word = tuple[str, Face]


def words_of(text: str, face: Face) -> list[Word]:
    return [(w, face) for w in text.split()]


VOWELS = set("aeiouy")
UNSPLIT = {"th", "ch", "sh", "ph", "wh", "gh", "ck"}


def hyphen_points(word: str) -> list[int]:
    """Rough English syllable breaks (V-CV and VC-CV), longest prefix first."""
    if "-" in word:
        return [i + 1 for i, ch in enumerate(word[:-3]) if ch == "-" and i >= 2][::-1]
    core = word.rstrip(".,;:!?’”)")
    if len(core) < 7 or not core.isalpha() or not core.islower():  # never split names
        return []
    low = core.lower()
    points = []
    for i in range(3, len(core) - 3):
        a, b, c = low[i - 1], low[i], low[i + 1]
        if a in VOWELS and b not in VOWELS and c in VOWELS:
            points.append(i)
        elif a not in VOWELS and b not in VOWELS and low[i - 2] in VOWELS and c in VOWELS and a + b not in UNSPLIT:
            points.append(i)
    return points[::-1]


def break_lines(words: list[Word], size: float, width_for, hyphenate=False) -> list[list[Word]]:
    """Greedy line breaking; width_for(n) is the measure available to line n.

    With hyphenate, a word that would leave a loose line is split across it.
    """
    space = R.width(" ", size)
    lines: list[list[Word]] = []
    line: list[Word] = []
    used = 0.0
    queue = list(words)
    while queue:
        word = queue.pop(0)
        ww = word[1].width(word[0], size)
        limit = width_for(len(lines))
        if line and used + space + ww > limit:
            if hyphenate and limit - used > space * 1.6:
                text, face = word
                for i in hyphen_points(text):
                    head = text[:i] if text[i - 1] == "-" else text[:i] + "-"
                    if used + space + face.width(head, size) <= limit:
                        line.append((head, face))
                        queue.insert(0, (text[i:], face))
                        break
                else:
                    queue.insert(0, word)
            else:
                queue.insert(0, word)
            lines.append(line)
            line, used = [], 0.0
        else:
            used = ww if not line else used + space + ww
            line.append(word)
    if line:
        lines.append(line)
    return lines


def balanced(words: list[Word], size: float, width: float) -> list[list[Word]]:
    """Breaks into the fewest lines that fit, then evens out their lengths."""
    target = len(break_lines(words, size, lambda _: width))
    lo, hi = width * 0.4, width
    for _ in range(20):
        mid = (lo + hi) / 2
        if len(break_lines(words, size, lambda _: mid)) <= target:
            hi = mid
        else:
            lo = mid
    return break_lines(words, size, lambda _: hi)


def clamp_lines(lines: list[list[Word]], size: float, width: float, limit: int) -> list[list[Word]]:
    """Keeps at most `limit` lines, ending the last with an ellipsis if text was cut."""
    if len(lines) <= limit:
        return lines
    kept = [list(line) for line in lines[:limit]]
    last = kept[-1]
    while last:
        text, face = last[-1]
        last[-1] = (text.rstrip(",;:.-") + "…", face)
        if line_width(last, size) <= width:
            break
        last[-1] = (text, face)
        last.pop()
    return kept


def line_width(line: list[Word], size: float) -> float:
    return sum(f.width(w, size) for w, f in line) + R.width(" ", size) * (len(line) - 1)


def fit_size(text: str, face: Face, width: float, largest: float, smallest: float, tracking=0.0) -> float:
    size = largest
    while size > smallest and face.width(text, size, tracking) > width:
        size -= 0.5
    return size


def set_story(paragraphs: list[str], body: float, colw: float):
    """Breaks the lead story into column lines, with a three-line drop cap.

    Returns (leading, drop cap size, [(words, x offset, ends paragraph)]).
    """
    lead_h = round(body * 1.36, 1)
    cap_size = round((2 * lead_h + body * R.cap) / B.cap, 1)
    cap_w = B.width(paragraphs[0][0], cap_size) + 6
    lines = []
    for p, para in enumerate(paragraphs):
        def width_for(n, p=p):
            if p == 0 and n < 3:
                return colw - cap_w
            return colw - (16 if p > 0 and n == 0 else 0)
        text = para[1:].lstrip() if p == 0 else para
        broken = break_lines(words_of(text, R), body, width_for, hyphenate=True)
        lines += [(ln, colw - width_for(n), n == len(broken) - 1) for n, ln in enumerate(broken)]
    return lead_h, cap_size, lines


# ── Pages ───────────────────────────────────────────────────────────────

class Page:
    """An SVG page under construction. Fonts are embedded only if used."""

    def __init__(self, width: float = W):
        self.width = width
        self.under: list[str] = []
        self.parts: list[str] = []
        self.used: set[str] = set()

    def add(self, markup: str):
        self.parts.append(markup)

    def text(self, x, y, s, face: Face, size, *, anchor="start", fill=INK, tracking=0.0):
        self.used.add(face.key)
        if anchor == "middle" and tracking:
            x += tracking / 2  # letter-spacing also trails the last letter
        attrs = f' text-anchor="{anchor}"' if anchor != "start" else ""
        attrs += f' letter-spacing="{tracking:g}"' if tracking else ""
        attrs += f' fill="{fill}"' if fill != INK else ""
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" class="{face.css}" font-size="{size:g}"{attrs}>{escape(s)}</text>')

    def line(self, line: list[Word], x, y, size, *, justify_to=None, anchor="start"):
        """Sets one line of words; with justify_to, spreads it to that measure."""
        if not line:
            return
        self.used.update(f.key for _, f in line)
        space = R.width(" ", size)
        widths = [f.width(w, size) for w, f in line]
        gap = space
        if justify_to and len(line) > 1:
            gap = (justify_to - sum(widths)) / (len(line) - 1)
            if gap > space * 3:  # too loose to justify; leave it ragged
                gap = space
        total = sum(widths) + gap * (len(line) - 1)
        x -= {"start": 0, "middle": total / 2, "end": total}[anchor]
        spans = []
        for (w, f), ww in zip(line, widths):
            spans.append(f'<tspan x="{x:.1f}" class="{f.css}">{escape(w)}</tspan>')
            x += ww + gap
        self.add(f'<text y="{y:.1f}" font-size="{size:g}">{"".join(spans)}</text>')

    def rule(self, x1, y, x2, weight=0.8, dash=None, color=INK):
        extra = f' stroke-dasharray="{dash}" stroke-linecap="round"' if dash else ""
        self.add(f'<line x1="{x1:.1f}" y1="{y:.1f}" x2="{x2:.1f}" y2="{y:.1f}" stroke="{color}" stroke-width="{weight:g}"{extra}/>')

    def vrule(self, x, y1, y2, weight=0.6):
        self.add(f'<line x1="{x:.1f}" y1="{y1:.1f}" x2="{x:.1f}" y2="{y2:.1f}" stroke="{INK}" stroke-width="{weight:g}"/>')

    def box(self, x, y, w, h, weight=0.8, inset=0.0):
        self.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" fill="none" stroke="{INK}" stroke-width="{weight:g}"/>')
        if inset:
            self.add(f'<rect x="{x + inset:.1f}" y="{y + inset:.1f}" width="{w - 2 * inset:.1f}" height="{h - 2 * inset:.1f}" fill="none" stroke="{INK}" stroke-width=".5"/>')

    def triangle(self, x, y, size, direction="up", fill=INK):
        """A stock-table arrow sitting on baseline y, starting at x."""
        if direction == "up":
            pts = [(x, y), (x + size, y), (x + size / 2, y - size * 0.9)]
        elif direction == "down":
            pts = [(x, y - size * 0.9), (x + size, y - size * 0.9), (x + size / 2, y)]
        else:
            s = size * 0.62
            pts = [(x + (size - s) / 2, y - s), (x + (size + s) / 2, y - s), (x + (size + s) / 2, y), (x + (size - s) / 2, y)]
        self.add(f'<polygon points="{" ".join(f"{px:.1f},{py:.1f}" for px, py in pts)}" fill="{fill}"/>')

    def diamond(self, cx, cy, r, fill=INK):
        self.add(f'<polygon points="{cx:.1f},{cy - r:.1f} {cx + r:.1f},{cy:.1f} {cx:.1f},{cy + r:.1f} {cx - r:.1f},{cy:.1f}" fill="{fill}"/>')

    def star(self, cx, cy, r, fill=ACCENT):
        pts = []
        for k in range(10):
            rad = r if k % 2 == 0 else r * 0.45
            ang = -math.pi / 2 + k * math.pi / 5
            pts.append(f"{cx + rad * math.cos(ang):.1f},{cy + rad * math.sin(ang):.1f}")
        self.add(f'<polygon points="{" ".join(pts)}" fill="{fill}"/>')

    def note(self, x, y, text, size=23, tilt=-3.0, anchor="start") -> float:
        """A handwritten margin note in blue pen. Returns its width."""
        self.used.add("hand")
        a = f' text-anchor="{anchor}"' if anchor != "start" else ""
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" class="h" font-size="{size:g}" fill="{PEN}"{a} '
                 f'transform="rotate({tilt:g} {x:.1f} {y:.1f})">{escape(text)}</text>')
        return H.width(text, size)

    def arrow(self, x1, y1, x2, y2, bend=0.3):
        """A hand-drawn pen arrow. Positive bend bows it to the left of its travel."""
        dx, dy = x2 - x1, y2 - y1
        cx, cy = (x1 + x2) / 2 + dy * bend, (y1 + y2) / 2 - dx * bend
        ang = math.atan2(y2 - cy, x2 - cx)
        head = " ".join(f"M{x2:.1f} {y2:.1f} L{x2 - 9 * math.cos(ang + d):.1f} {y2 - 9 * math.sin(ang + d):.1f}"
                        for d in (0.5, -0.42))
        self.add(f'<path d="M{x1:.1f} {y1:.1f} Q{cx:.1f} {cy:.1f} {x2:.1f} {y2:.1f} {head}" fill="none" '
                 f'stroke="{PEN}" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"/>')

    def sheet(self, x, y, w, h, *, seed: int, tone=PAPER_TONES[0], ragged=1.1):
        """A piece of newsprint, cut a little unevenly, with grain and age."""
        rng = random.Random(seed)
        corners = [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]
        path = "M" + " L".join(f"{cx + rng.uniform(-ragged, ragged):.1f} {cy + rng.uniform(-ragged, ragged):.1f}"
                               for cx, cy in corners) + " Z"
        cid = f"cut{seed}"
        area = f'x="{x - 4:.1f}" y="{y - 4:.1f}" width="{w + 8:.1f}" height="{h + 8:.1f}"'
        self.under.append(
            f'<clipPath id="{cid}"><path d="{path}"/></clipPath>'
            f'<path d="{path}" fill="{tone}" filter="url(#shadow)"/>'
            f'<g clip-path="url(#{cid})"><rect {area} filter="url(#stain)" opacity=".15"/>'
            f'<rect {area} filter="url(#grain)" opacity=".3"/><rect {area} fill="url(#age)"/></g>'
        )

    def render(self, height: float, *, title: str, rotate: float = 0.0) -> str:
        fonts = []
        for key in sorted(self.used):
            family, weight, style = FONT_RULES[key]
            data = base64.b64encode((FONTS / f"{key}.woff2").read_bytes()).decode()
            fonts.append(f'@font-face{{font-family:{family};font-weight:{weight};font-style:{style};'
                         f'src:url(data:font/woff2;base64,{data}) format("woff2")}}')
        body = "".join(self.under) + "".join(self.parts)
        if rotate:
            body = f'<g transform="rotate({rotate:g} {self.width / 2:.1f} {height / 2:.1f})">{body}</g>'
        return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.width:g} {height:.0f}" '
                f'width="{self.width:g}" height="{height:.0f}" role="img">'
                f'<title>{escape(title)}</title><defs>{DEFS}</defs>'
                f'<style>{"".join(fonts)}{BASE_CSS}</style>{body}</svg>')


# ── Dates and figures ───────────────────────────────────────────────────

def roman(n: int) -> str:
    out = ""
    for value, numeral in ((1000, "M"), (900, "CM"), (500, "D"), (400, "CD"), (100, "C"), (90, "XC"),
                           (50, "L"), (40, "XL"), (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")):
        while n >= value:
            out, n = out + numeral, n - value
    return out


def week_line(d: dt.date) -> str:
    return f"Week of {MONTHS[d.month - 1]} {d.day}, {d.year}"


def ap_date(d: dt.date) -> str:
    return f"{AP_MONTHS[d.month - 1]} {d.day}, {d.year}"


def today_in(offset: str) -> dt.date:
    sign = -1 if offset.startswith("-") else 1
    hours, minutes = (int(p) for p in offset.lstrip("+-").split(":"))
    tz = dt.timezone(sign * dt.timedelta(hours=hours, minutes=minutes))
    return dt.datetime.now(tz).date()


def monday_of(d: dt.date) -> dt.date:
    """A weekly paper is dated by the Monday of its week."""
    return d - dt.timedelta(days=d.weekday())


def edition_numbers(today: dt.date, founded: dt.date) -> tuple[int, int]:
    """Volume counts years since founding; No. counts weekly editions."""
    years = today.year - founded.year - ((today.month, today.day) < (founded.month, founded.day))
    return years + 1, (today - monday_of(founded)).days // 7 + 1


GRAPHQL = """
query($login: String!) {
  user(login: $login) {
    followers { totalCount }
    contributionsCollection { contributionCalendar { totalContributions } }
    repositories(first: 100, ownerAffiliations: OWNER, privacy: PUBLIC, isFork: false,
                 orderBy: {field: STARGAZERS, direction: DESC}) {
      nodes { name description url stargazerCount forkCount pushedAt isArchived primaryLanguage { name } }
    }
  }
}"""


def github(url: str, token: str | None, payload: dict | None = None):
    req = urllib.request.Request(url, data=json.dumps(payload).encode() if payload else None,
                                 headers={"Accept": "application/vnd.github+json",
                                          "User-Agent": "fossintellect-press"})
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(req, timeout=20) as resp:
        return json.load(resp)


def fetch_figures(login: str, token: str | None) -> dict:
    """Public figures for `login`. GraphQL (with a token) also yields contributions."""
    if token:
        data = github("https://api.github.com/graphql", token, {"query": GRAPHQL, "variables": {"login": login}})
        if data.get("errors"):
            raise RuntimeError(data["errors"][0]["message"])
        user = data["data"]["user"]
        repos = [{"name": n["name"], "description": n["description"] or "", "url": n["url"],
                  "stars": n["stargazerCount"], "forks": n["forkCount"], "pushed": n["pushedAt"],
                  "archived": n["isArchived"], "language": (n["primaryLanguage"] or {}).get("name")}
                 for n in user["repositories"]["nodes"]]
        followers = user["followers"]["totalCount"]
        contributions = user["contributionsCollection"]["contributionCalendar"]["totalContributions"]
    else:
        user = github(f"https://api.github.com/users/{login}", None)
        raw = github(f"https://api.github.com/users/{login}/repos?per_page=100&type=owner", None)
        repos = [{"name": r["name"], "description": r["description"] or "", "url": r["html_url"],
                  "stars": r["stargazers_count"], "forks": r["forks_count"], "pushed": r["pushed_at"],
                  "archived": r["archived"], "language": r["language"]}
                 for r in raw if not r["fork"] and not r.get("private")]
        followers = user["followers"]
        contributions = None
    return {
        "repos": len(repos),
        "stars": sum(r["stars"] for r in repos),
        "followers": followers,
        "contributions": contributions,
        "projects": repos,
    }


def keep_figures(figures: dict | None) -> dict:
    """Files today's figures, or falls back to the last ones if the wire was down."""
    if figures is not None:
        LEDGER.write_text(json.dumps(figures, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        return figures
    if LEDGER.exists():
        return json.loads(LEDGER.read_text(encoding="utf-8"))
    return {"repos": 0, "stars": 0, "followers": 0, "contributions": None, "projects": []}


def pick_projects(figures: dict, login: str, featured: list[str], limit: int) -> list[dict]:
    projects = [p for p in figures["projects"] if p["name"].lower() != login.lower()]
    if featured:
        by_name = {p["name"].lower(): p for p in projects}
        return [by_name[n.lower()] for n in featured if n.lower() in by_name][:limit]
    # Most stars first; ties go to the most recently pushed (sorted() is stable).
    live = sorted((p for p in projects if not p["archived"]), key=lambda p: p["pushed"] or "", reverse=True)
    return sorted(live, key=lambda p: -p["stars"])[:limit]


# ── The front page ──────────────────────────────────────────────────────

def front_page(news: dict, today: dt.date, fig: dict) -> str:
    paper, lead, notes = news["paper"], news["lead"], news.get("notes", {})
    page = Page()
    top, x0, x1 = 10, 40, W - 40
    cw, mid = x1 - x0, W / 2
    y = top + 26

    # Flag: founding year, nameplate and motto.
    est = f"EST. {roman(paper['founded'].year)}"
    est_w = B.width(est, 10, 3.5)
    page.text(mid, y + 8, est, B, 10, anchor="middle", tracking=3.5)
    for side in (-1, 1):
        inner = mid + side * (est_w / 2 + 12)
        page.diamond(inner, y + 4.5, 2.6)
        page.rule(inner + side * 7, y + 4.5, inner + side * 60, 0.7)
    y += 24
    size = round(min(70.0, cw * 0.9 / B.width(paper["title"], 1)), 1)
    title_end = mid + B.width(paper["title"], size) / 2
    page.text(mid, y + size * 0.76, paper["title"], B, size, anchor="middle")
    if notes.get("masthead"):
        nw = page.note(title_end - 175, y - 4, notes["masthead"], 24, tilt=-4)
        page.arrow(title_end - 175 + nw + 8, y - 16, title_end - 6, y + 6, bend=0.45)
    y += size * 0.9
    page.text(mid, y + 14, paper["motto"], I, 14, anchor="middle")
    y += 28

    # Folio line.
    vol, number = edition_numbers(today, paper["founded"])
    folio = y
    date = week_line(today).upper()
    page.rule(x0, y, x1, 0.9)
    page.text(x0, y + 16.5, f"VOL. {roman(vol)} · NO. {number:,}", B, 9.5, tracking=1.6)
    page.text(mid, y + 16.5, date, B, 10.5, anchor="middle", tracking=2.2)
    page.text(x1, y + 16.5, paper["price"], B, 9.5, anchor="end", tracking=1.6)
    page.rule(x0, y + 24, x1, 0.9)
    page.rule(x0, y + 27.8, x1, 2.6)
    y += 58

    # Kicker, with the date note in the margin beside it.
    kicker_w = B.width(lead["kicker"], 10.5, 3.5)
    page.text(mid, y, lead["kicker"], B, 10.5, anchor="middle", fill=ACCENT, tracking=3.5)
    for side in (-1, 1):
        page.rule(mid + side * (kicker_w / 2 + 10), y - 3.6, mid + side * (kicker_w / 2 + 40), 0.8, color=ACCENT)
    if notes.get("date"):
        nw = page.note(x0 + 6, y + 4, notes["date"], 22, tilt=-3)
        page.arrow(x0 + 6 + nw + 6, y - 12, mid - B.width(date, 10.5, 2.2) / 2 - 10, folio + 13, bend=0.45)

    # Headline and deck.
    y += 16
    hl = fit_size(lead["headline"], B, cw, 50, 34)
    heads = [words_of(lead["headline"], B)] if B.width(lead["headline"], hl) <= cw else balanced(words_of(lead["headline"], B), 40, cw)
    hl = hl if len(heads) == 1 else 40
    for n, ln in enumerate(heads):
        page.line(ln, mid, y + hl * 0.72 + n * hl * 1.08, hl, anchor="middle")
    y += hl * 0.72 + (len(heads) - 1) * hl * 1.08 + 14
    deck = balanced(words_of(lead["deck"], I), 17, cw * 0.8)
    for n, ln in enumerate(deck):
        page.line(ln, mid, y + 13 + n * 22, 17, anchor="middle")
    y += 13 + (len(deck) - 1) * 22 + 30

    # Story on the left, tools of the trade on the right.
    gutter = 30
    sw = 450
    tw = cw - sw - gutter
    rx = x0 + sw + gutter
    by_w = B.width(lead["byline"], 10, 2.2)
    page.text(x0 + sw / 2, y, lead["byline"], B, 10, anchor="middle", tracking=2.2)
    for side in (-1, 1):
        page.rule(x0 + sw / 2 + side * (by_w / 2 + 12), y - 3.6, x0 + sw / 2 + side * sw / 2, 0.6)
    page.text(rx + tw / 2, y, "TOOLS OF THE TRADE", B, 10, anchor="middle", tracking=2.2)
    page.rule(rx, y + 9, rx + tw, 0.8)
    outlooks = {"bullish": "up", "rising": "up", "steady": "flat", "hold": "flat", "bearish": "down"}
    ty = y + 32
    for item in news["desk"]["stack"]:
        page.text(rx, ty, item["name"], B, 14.5)
        page.text(rx + 108, ty, item["sector"], I, 13.5, fill=INK_SOFT)
        page.triangle(rx + tw - 9, ty - 1, 8, outlooks.get(item["outlook"], "flat"))
        page.rule(rx, ty + 8.5, rx + tw, 0.6, dash="0.6 2.6")
        ty += 25
    col_bottom = ty - 16
    if notes.get("stack"):
        page.note(rx + 78, col_bottom + 36, notes["stack"], 23, tilt=-3)
        page.arrow(rx + 70, col_bottom + 26, rx + 40, col_bottom + 6, bend=-0.35)
        col_bottom += 44

    # The story's type size is picked so it runs about as deep as the tools column.
    story_top = y + 28
    for body in (14.5, 15.0, 15.5, 16.0, 16.5, 17.0):
        lead_h, cap_size, lines = set_story(lead["story"], body, sw)
        story_bottom = story_top + (len(lines) - 1) * lead_h + 6
        if story_bottom >= col_bottom - lead_h:
            break
    page.text(x0 - 1, story_top + 2 * lead_h, lead["story"][0][0], B, cap_size)
    for n, (ln, offset, last) in enumerate(lines):
        page.line(ln, x0 + offset, story_top + n * lead_h, body, justify_to=None if last else sw - offset)
    y = max(story_bottom, col_bottom) + 14
    page.vrule(x0 + sw + gutter / 2, story_top - 30, y - 6)

    # One line of figures.
    figures = [f"{fig['repos']:,} public repositories", f"{fig['stars']:,} stars", f"{fig['followers']:,} followers"]
    if fig.get("contributions") is not None:
        figures.append(f"{fig['contributions']:,} contributions this year")
    page.rule(x0, y, x1, 2.4)
    page.rule(x0, y + 4, x1, 0.8)
    page.used.update(("serif", "serif-bold"))
    page.add(f'<text x="{mid}" y="{y + 22:.1f}" text-anchor="middle" font-size="11.5">'
             f'<tspan class="b" letter-spacing="2.2">THE FIGURES</tspan>'
             f'<tspan class="r">{escape("   ·   " + "   ·   ".join(figures))}</tspan></text>')
    page.rule(x0, y + 32, x1, 0.8)
    page.rule(x0, y + 35.8, x1, 2.6)
    y += 37 + 24

    page.sheet(12, top, W - 24, y - top, seed=1)
    return page.render(y + 12, title=f"{paper['title']}: {lead['headline']}")


# ── Inside pages ────────────────────────────────────────────────────────

def section_banner(title: str, subtitle: str, seed: int) -> str:
    page = Page()
    tw = B.width(title, 15, 4.5)
    page.text(W / 2, 37, title, B, 15, anchor="middle", tracking=4.5)
    for side in (-1, 1):
        inner = W / 2 + side * (tw / 2 + 14)
        page.diamond(inner, 32, 3)
        page.rule(inner + side * 8, 32, inner + side * 150, 0.8)
    page.text(W / 2, 55, subtitle, I, 12, anchor="middle")
    page.sheet(12, 8, W - 24, 60, seed=seed, tone=PAPER_TONES[0])
    return page.render(76, title=title)


def project_clipping(project: dict, n: int) -> str:
    cw, ch = 420, 252
    page = Page(cw)
    x0, x1 = 30, cw - 30
    inner = x1 - x0
    language = (project["language"] or "DISPATCH").upper()
    page.text(x0, 38, language, B, 9.5, fill=ACCENT, tracking=2)
    stars = f"{project['stars']:,} {'STAR' if project['stars'] == 1 else 'STARS'}"
    page.text(x1, 38, stars, B, 9, anchor="end", tracking=1.2)
    page.star(x1 - B.width(stars, 9, 1.2) - 9, 34.6, 4.6)
    page.rule(x0, 46, x1, 0.8)
    name = project["name"].replace("-", " ").replace("_", " ").upper()
    size = fit_size(name, B, inner, 27, 17)
    heads = balanced(words_of(name, B), size, inner) if B.width(name, size) > inner else [words_of(name, B)]
    hy = 46 + size * 0.72 + 12
    for k, ln in enumerate(heads[:2]):
        page.line(ln, x0, hy + k * size * 1.05, size)
    y = hy + (min(len(heads), 2) - 1) * size * 1.05 + 10
    page.rule(x0, y, x0 + 44, 1.6)
    text = project["description"] or "No description filed yet; our reporter is still at the scene."
    face = R if project["description"] else I
    footer = ch - 34
    max_lines = max(1, int((footer - 14 - (y + 20)) // 18) + 1)
    lines = clamp_lines(break_lines(words_of(text, face), 13.8, lambda _: inner, hyphenate=True), 13.8, inner, max_lines)
    for k, ln in enumerate(lines):
        page.line(ln, x0, y + 20 + k * 18, 13.8, justify_to=None if k == len(lines) - 1 else inner)
    page.rule(x0, footer - 12, x1, 0.6)
    pushed = dt.date.fromisoformat(project["pushed"][:10]) if project.get("pushed") else None
    if pushed:
        page.text(x0, footer + 3, f"Last revised {ap_date(pushed)}", I, 11.5, fill=INK_SOFT)
    page.text(x1, footer + 3, "READ THE FULL STORY →", B, 9, anchor="end", tracking=1.4)
    page.sheet(12, 12, cw - 24, ch - 24, seed=20 + n, tone=PAPER_TONES[n % len(PAPER_TONES)])
    return page.render(ch, title=project["name"], rotate=(-0.7, 0.6, 0.4, -0.5)[n % 4])


def empty_clipping(login: str) -> str:
    page = Page()
    mid = W / 2
    page.text(mid, 46, "STOP THE PRESSES", B, 10.5, anchor="middle", fill=ACCENT, tracking=3.5)
    page.text(mid, 86, "THE FIRST RELEASES ARE BEING TYPESET", B, 29, anchor="middle")
    deck = (f"{login}’s debut open-source tools are on the composing stone. "
            "Follow the paper to be first in line for the opening edition.")
    for n, ln in enumerate(balanced(words_of(deck, I), 15.5, W * 0.7)):
        page.line(ln, mid, 116 + n * 21, 15.5, anchor="middle")
    page.rule(mid - 120, 160, mid + 120, 0.6)
    page.text(mid, 180, f"SUBSCRIBE FREE  →  GITHUB.COM/{login.upper()}", B, 9.5, anchor="middle", tracking=2)
    page.sheet(20, 14, W - 40, 186, seed=40, tone=PAPER_TONES[1])
    return page.render(214, title="The first releases are being typeset", rotate=-0.4)


@dataclass
class Ad:
    slug: str
    head: str
    sub: str
    body: str
    contact: str
    url: str


def classified_ads(login: str, contacts: dict) -> list[Ad]:
    profile = f"https://github.com/{login}"
    ads = [
        Ad("contributors", "Wanted", "CONTRIBUTORS",
           "Pull requests, bug reports and bold ideas. No experience necessary; curiosity required.",
           f"Apply within: github.com/{login}", f"{profile}?tab=repositories"),
        Ad("subscribe", "Subscribe", "TODAY · FREE FOREVER",
           "Every new release, delivered straight to your feed. Follow the paper on GitHub.",
           f"Follow @{login}", profile),
    ]
    if contacts.get("linkedin"):
        handle = contacts["linkedin"].rstrip("/").split("/")[-1]
        ads.append(Ad("linkedin", "Notices", "PROFESSIONAL",
                      "Collaborations, talks and open-source partnerships considered. References on file.",
                      f"LinkedIn: {handle}", contacts["linkedin"]))
    if contacts.get("email"):
        ads.append(Ad("email", "Letters", "TO THE EDITOR",
                      "Questions, ideas and kind words are read with care and answered promptly.",
                      contacts["email"], f"mailto:{contacts['email']}"))
    if contacts.get("x"):
        handle = contacts["x"].lstrip("@")
        ads.append(Ad("x", "Bulletins", "LATE & BREAKING",
                      "Release notes, works in progress and the occasional hot take.",
                      f"@{handle} on X", f"https://x.com/{handle}"))
    if contacts.get("website"):
        domain = re.sub(r"^https?://(www\.)?", "", contacts["website"]).rstrip("/")
        ads.append(Ad("website", "Archive", "THE COMPLETE",
                      "Long-form writing, project notes and the whole back catalogue.",
                      domain, contacts["website"]))
    return ads


def ad_clipping(ad: Ad, n: int) -> str:
    cw, ch = 280, 214
    page = Page(cw)
    bx, by, bw, bh = 24, 24, cw - 48, ch - 48
    page.box(bx, by, bw, bh, weight=1.4, inset=3.5)
    mid = cw / 2
    page.text(mid, by + 40, ad.head, B, 26, anchor="middle")
    page.text(mid, by + 58, ad.sub, B, 9.5, anchor="middle", tracking=2)
    page.rule(mid - 26, by + 67, mid + 26, 0.6)
    lines = clamp_lines(balanced(words_of(ad.body, R), 12, bw - 30), 12, bw - 30, 4)
    for k, ln in enumerate(lines):
        page.line(ln, mid, by + 85 + k * 15.5, 12, anchor="middle")
    size = fit_size(ad.contact, I, bw - 24, 11.5, 8.5)
    page.text(mid, by + bh - 13, ad.contact, I, size, anchor="middle")
    page.sheet(12, 12, cw - 24, ch - 24, seed=60 + n, tone=PAPER_TONES[(n + 2) % len(PAPER_TONES)])
    return page.render(ch, title=f"{ad.head} {ad.sub}", rotate=(0.6, -0.5, 0.3, -0.7)[n % 4])


def colophon(today: dt.date) -> str:
    page = Page()
    page.text(42, 32, "PAGE A1", B, 9, tracking=1.8)
    page.text(W - 42, 32, ap_date(today).upper(), B, 9, anchor="end", tracking=1.8)
    text = "Printed weekly by GitHub Actions · Set in Old Standard TT & Caveat · Every line of source is open"
    page.text(W / 2, 32, text, I, fit_size(text, I, W - 260, 11.5, 8.5), anchor="middle")
    page.sheet(12, 8, W - 24, 38, seed=80, tone=PAPER_TONES[2])
    return page.render(56, title="Colophon")


# ── README ──────────────────────────────────────────────────────────────

def attr(s: str) -> str:
    return html.escape(s, quote=True)


def picture(name: str, width: str, alt: str, href: str | None = None) -> str:
    """A page that GitHub swaps for its night edition under the dark theme."""
    tag = (f'<picture><source media="(prefers-color-scheme: dark)" srcset="assets/dark/{name}">'
           f'<img src="assets/{name}" width="{width}" alt="{attr(alt)}"></picture>')
    return f'<a href="{attr(href)}">{tag}</a>' if href else tag


def readme(news: dict, today: dt.date, fig: dict, projects: list[dict], ads: list[Ad]) -> str:
    paper, lead = news["paper"], news["lead"]
    vol, number = edition_numbers(today, paper["founded"])
    out = [
        "<!-- Printed by press/press.py. Edit newsroom.toml, not this file: the presses overwrite it. -->",
        '<div align="center">',
        "",
        picture("front-page.svg", "100%", f"{paper['title']}. {paper['motto']} "
                f"Lead story: {lead['headline']}. {lead['deck']}."),
        "",
        picture("section-print.svg", "100%", "Now in print"),
        "",
    ]
    if projects:
        out += [picture(f"print-{n}.svg", "49%", f"{p['name']}: {p['description'] or 'new release'}", p["url"])
                for n, p in enumerate(projects, 1)]
    else:
        out.append(picture("print-empty.svg", "100%", "Stop the presses: the first releases are being typeset. "
                           "Follow to be first in line.", f"https://github.com/{paper['login']}"))
    out += ["", picture("section-classifieds.svg", "100%", "Classifieds"), ""]
    per_row = math.ceil(len(ads) / math.ceil(len(ads) / 3))  # 4 ads sit 2 + 2, 5 sit 3 + 2
    for n, ad in enumerate(ads):
        if n and n % per_row == 0:
            out.append("<br>")
        out.append(picture(f"ad-{ad.slug}.svg", "32%", f"{ad.head} {ad.sub.lower()}: {ad.body} {ad.contact}", ad.url))
    out += ["", picture("colophon.svg", "100%", "Printed weekly by GitHub Actions"), "", "</div>", ""]

    # The plain-text edition: the same paper for screen readers, phones and search engines.
    stack = " · ".join(f"{s['name']} ({s['sector']})" for s in news["desk"]["stack"])
    figures = [f"{fig['repos']:,} public repositories", f"{fig['stars']:,} stars", f"{fig['followers']:,} followers"]
    if fig.get("contributions") is not None:
        figures.append(f"{fig['contributions']:,} contributions in the past year")
    out += [
        "<details>",
        "<summary><b>Read the plain-text edition</b> (for screen readers, small screens and search engines)</summary>",
        "",
        f"### {paper['title']}",
        f"*{paper['motto']}* · Vol. {roman(vol)}, No. {number:,} · {week_line(today)}",
        "",
        f"#### {lead['headline']}",
        f"*{lead['deck']}.*",
        "",
        f"**{lead['byline']}**",
        "",
        *[line for para in lead["story"] for line in (para, "")],
        f"**Tools of the trade:** {stack}",
        "",
        f"**The figures, {ap_date(today)}:** " + " · ".join(figures),
        "",
        "**Now in print:**",
        "",
    ]
    if projects:
        out += [f"- [{p['name']}]({p['url']}): {p['description'] or 'new release'}" for p in projects]
    else:
        out.append("- The first releases are being typeset. Follow to be first in line.")
    out += ["", "**Classifieds:** " + " · ".join(f"[{ad.head} {ad.sub.lower()}]({ad.url})" for ad in ads), "",
            "</details>", ""]
    return "\n".join(out)


# ── Main ────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--offline", action="store_true", help="skip the GitHub API and reuse the last figures")
    parser.add_argument("--date", type=dt.date.fromisoformat, help="print the edition for the week of this date")
    args = parser.parse_args()

    news = tomllib.loads((ROOT / "newsroom.toml").read_text(encoding="utf-8"))
    paper = news["paper"]
    today = monday_of(args.date or today_in(paper.get("utc_offset", "+00:00")))

    figures = None
    if not args.offline:
        token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
        # GraphQL needs a token; the public REST API is the fallback.
        for attempt in ([token, None] if token else [None]):
            try:
                figures = fetch_figures(paper["login"], attempt)
                break
            except (urllib.error.URLError, RuntimeError, KeyError, TypeError, TimeoutError) as err:
                print(f"wire trouble ({'GraphQL' if attempt else 'REST'}): {err}")
    fig = keep_figures(figures)
    projects = pick_projects(fig, paper["login"], news["press"].get("featured", []), news["press"].get("limit", 4))
    ads = classified_ads(paper["login"], news.get("classifieds", {}))

    (ASSETS / "dark").mkdir(parents=True, exist_ok=True)
    for stale in [*ASSETS.glob("**/print-*.svg"), *ASSETS.glob("**/ad-*.svg")]:
        stale.unlink()
    pages = {
        "front-page.svg": front_page(news, today, fig),
        "section-print.svg": section_banner("NOW IN PRINT", "Fresh off the press: the latest releases from the workshop", 90),
        "section-classifieds.svg": section_banner("CLASSIFIEDS", "Notices, wants and correspondence", 91),
        "colophon.svg": colophon(today),
    }
    if projects:
        pages.update({f"print-{n}.svg": project_clipping(p, n - 1) for n, p in enumerate(projects, 1)})
    else:
        pages["print-empty.svg"] = empty_clipping(paper["login"])
    pages.update({f"ad-{ad.slug}.svg": ad_clipping(ad, n) for n, ad in enumerate(ads)})
    for name, svg in pages.items():
        (ASSETS / name).write_text(svg, encoding="utf-8")
        (ASSETS / "dark" / name).write_text(night_edition(svg), encoding="utf-8")
    (ROOT / "README.md").write_text(readme(news, today, fig, projects, ads), encoding="utf-8")
    print(f"printed the edition for the {week_line(today).lower()}: {len(pages)} pages, "
          f"{fig['repos']} repos, {fig['stars']} stars")


if __name__ == "__main__":
    main()
