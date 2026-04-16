#!/usr/bin/env python3
"""
cnrtl — Look up a French word in the CNRTL TLFi dictionary.

Usage:
    cnrtl <word>               Show all definitions (clean summary)
    cnrtl <word> -e            Show definitions with one example per sense
    cnrtl <word> <sense>       Show full detail for a specific sense
    cnrtl <word> <sense> -e    (same — detail always shows all examples)
    cnrtl <word> --etym        Show minimal origin (date + source)
    cnrtl <word> --etym-full   Show full etymology and history
    cnrtl <word> --tab N       Show the Nth homograph entry (when multiple exist)
    cnrtl <word> -h            Show this help

Sense addressing:
    Senses in the summary are labelled with plan markers (I, II, A, B, 1, 2,
    a, b, α, β, …). Concatenate them to form a path:

        IIA1     →  Roman II › uppercase A › numeral 1
        I.A.1    →  same, dot-separated
        2B       →  Arabic "2" is accepted for Roman II

    Senses that contain hidden content (examples, common phrases, notes)
    are marked with \033[2m[+]\033[0m in summary view.


Anki:
    cnrtl <word> --anki              Add a card to the default deck (Français)
    cnrtl <word> --anki --deck NAME  Add a card to a specific deck
    Requires Anki to be open with the AnkiConnect add-on installed.
"""

import sys
import re
import json
import textwrap
from html import escape as html_escape
from html.parser import HTMLParser
from urllib.request import urlopen, Request
from urllib.parse import quote
from urllib.error import URLError, HTTPError

BASE_URL = "https://www.cnrtl.fr/definition/"

# ── Abbreviation expansions ────────────────────────────────────────────────
# Applied to POS codes and usage labels — NOT to definition text.
# Longer patterns first so they match before their sub-strings do.
ABBREVS = [
    ("subst. fém. et adj. inv.", "nom féminin (aussi adj. invariable)"),
    ("subst. masc. et adj. inv.", "nom masculin (aussi adj. invariable)"),
    ("subst. fém. et masc.", "nom féminin et masculin"),
    ("subst. masc. et fém.", "nom masculin et féminin"),
    ("subst. fém.", "nom féminin"),
    ("subst. masc.", "nom masculin"),
    ("subst.", "nom"),
    ("adj. et subst.", "adjectif et nom"),
    ("adv. et adj.", "adverbe et adjectif"),
    ("verbe trans. et intr.", "verbe transitif et intransitif"),
    ("verbe trans.", "verbe transitif"),
    ("verbe intr.", "verbe intransitif"),
    ("verbe pron.", "verbe pronominal"),
    ("v. tr. et intr.", "verbe transitif et intransitif"),
    ("v. tr.", "verbe transitif"),
    ("v. intr.", "verbe intransitif"),
    ("v. pron.", "verbe pronominal"),
    ("adj. inv.", "adjectif invariable"),
    ("adj.", "adjectif"),
    ("adv.", "adverbe"),
    ("prép.", "préposition"),
    ("conj.", "conjonction"),
    ("interj.", "interjection"),
    ("P. ext.", "par extension"),
    ("P. anal.", "par analogie"),
    ("P. métaph.", "par métaphore"),
    ("P. méton.", "par métonymie"),
    ("p. ext.", "par extension"),
    ("p. anal.", "par analogie"),
    ("p. métaph.", "par métaphore"),
    ("p. méton.", "par métonymie"),
    ("au fig.", "au sens figuré"),
    ("Synon.", "Synonymes :"),
    ("Anton.", "Antonymes :"),
    ("fam.", "familier"),
    ("pop.", "populaire"),
    ("arg.", "argot"),
    ("litt.", "littéraire"),
    ("vx.", "vieux"),
    ("spéc.", "spécialement"),
    ("absolt.", "absolument"),
    ("partic.", "particulièrement"),
    ("loc.", "locution"),
    ("Loc.", "Locution"),
]

def expand_abbrevs(text):
    """Case-insensitive abbreviation expansion (replacement is always lowercase)."""
    for old, new in ABBREVS:
        text = re.sub(re.escape(old), new, text, flags=re.IGNORECASE)
    return text


# ── Minimal DOM tree builder ───────────────────────────────────────────────
VOID_TAGS = {
    "area", "base", "br", "col", "embed", "hr", "img", "input",
    "link", "meta", "param", "source", "track", "wbr",
}

class Node:
    __slots__ = ("tag", "classes", "id", "children")

    def __init__(self, tag, classes, id_=""):
        self.tag = tag
        self.classes = set(classes)
        self.id = id_
        self.children = []  # list of Node | str

    def text(self):
        parts = []
        for c in self.children:
            parts.append(c if isinstance(c, str) else c.text())
        return "".join(parts)

    def direct_nodes(self):
        return [c for c in self.children if isinstance(c, Node)]

    def find_id(self, id_):
        if self.id == id_:
            return self
        for c in self.children:
            if isinstance(c, Node):
                r = c.find_id(id_)
                if r:
                    return r
        return None

    def find_class(self, cls):
        results = []
        if cls in self.classes:
            results.append(self)
        for c in self.children:
            if isinstance(c, Node):
                results.extend(c.find_class(cls))
        return results


class PageParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node("__root__", [])
        self.stack = [self.root]

    def handle_starttag(self, tag, attrs):
        d = dict(attrs)
        node = Node(tag, d.get("class", "").split(), d.get("id", ""))
        self.stack[-1].children.append(node)
        if tag not in VOID_TAGS:
            self.stack.append(node)

    def handle_endtag(self, tag):
        if tag in VOID_TAGS:
            return
        # Search backwards for matching tag (tolerates minor malformed HTML)
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                self.stack = self.stack[:i]
                return

    def handle_data(self, data):
        if self.stack:
            self.stack[-1].children.append(data)


# ── Text helpers ───────────────────────────────────────────────────────────

def clean(text):
    """Collapse whitespace."""
    return re.sub(r"\s+", " ", text).strip()

def clean_plan(text):
    """Strip trailing em-dash from section markers like 'I. −'."""
    return re.sub(r"\s*[−–\-]+\s*$", "", clean(text)).strip()

_CITATION_CLASSES = frozenset(
    ["tlf_cauteur", "tlf_ctitre", "tlf_cdate", "tlf_csource", "tlf_cpublication"]
)

def get_example(node):
    """
    Extract a short readable quote + attribution from a tlf_cexemple node.
    Returns  « quote text » (Author, year)  or empty string.

    Two formats in the TLFi:
      • Inline:   <i>full quote</i> (Author, Title, date, p. N).
      • Numbered: N. running text with <i>some words</i> in italics
                  Author, Title, date, p. N.
    Detected by whether the first meaningful child is a bare <i> tag.
    """
    author = date = ""
    for c in node.children:
        if not isinstance(c, Node):
            continue
        if "tlf_cauteur" in c.classes:
            author = clean(c.text()).strip(",. ")
        elif "tlf_cdate" in c.classes:
            date = clean(c.text()).strip(",. ")

    # Find first non-whitespace child
    first = None
    for c in node.children:
        if isinstance(c, str):
            if c.strip():
                first = c
                break
        else:
            first = c
            break

    if isinstance(first, Node) and first.tag in ("i", "em") and not first.classes:
        # Inline format: first child is the full italic quote
        quote = clean(first.text())
    else:
        # Numbered / mixed: collect all non-citation text
        parts = []
        for c in node.children:
            if isinstance(c, str):
                parts.append(c)
            elif isinstance(c, Node) and not (c.classes & _CITATION_CLASSES):
                parts.append(c.text())
        quote = clean("".join(parts))
        quote = re.sub(r"^\d+\.\s*", "", quote)          # strip "1. "
        quote = re.sub(r",?\s*p\.\s*\d[\d-]*\.?\s*$", "", quote).strip()

    if not quote:
        return ""
    if len(quote) > 200:
        quote = quote[:197] + "…"

    cite = ", ".join(p for p in [author, date] if p)
    return "« " + quote + " »" + (f" ({cite})" if cite else "")


# ── "Has more" detection ───────────────────────────────────────────────────

_MORE_INDICATOR = "  \033[2m[+]\033[0m"

def _has_more_content(node, show_ex):
    """
    True if this node contains content not shown in the current summary view:
      - any examples (when show_ex is False), or 2+ examples (when show_ex is True)
      - syntagme blocks (SYNT.)
      - notes / remarks
    """
    example_count = 0
    for c in node.direct_nodes():
        cls = c.classes
        if "tlf_cexemple" in cls:
            example_count += 1
        elif "tlf_tabulation" in cls:
            example_count += len(c.find_class("tlf_cexemple"))
        elif "tlf_parsynt" in cls:
            return True
        elif "tlf_parothers" in cls:
            if clean(c.text()):   # ignore empty remark blocks
                return True
    return example_count > (1 if show_ex else 0)


# ── Definition rendering ───────────────────────────────────────────────────

def render_parah(node, depth, show_ex, detail=False):
    """
    Recursively render a tlf_parah (or tlf_paraputir) node into lines.

    depth   — indentation level (0 = top)
    show_ex — show one example per sense in summary mode
    detail  — full mode: all examples, syntagmes, notes
    """
    lines = []
    pad = "  " * depth

    plan = emploi = defn = crochet = domaine = expr = ""
    synonymes = []
    all_examples = []   # collect ALL examples; decide how many to emit later
    syntagmes = []      # tlf_parsynt content (for detail mode)
    notes = []          # tlf_parothers content (for detail mode)
    sub_nodes = []
    defn_seen = False   # track whether tlf_cdefinition has appeared yet

    for c in node.direct_nodes():
        cls = c.classes

        if "tlf_cplan" in cls:
            plan = clean_plan(c.text())

        elif "tlf_cdomaine" in cls:
            domaine = clean(c.text())

        elif "tlf_csyntagme" in cls:
            # Capture as the expression being defined only if it precedes the
            # definition text. A tlf_csyntagme that follows tlf_cdefinition is a
            # collocation/usage example, not the headword expression.
            if not defn_seen:
                expr = clean(c.text())

        elif "tlf_cdefinition" in cls:
            defn = clean(c.text())
            defn_seen = True

        elif "tlf_cemploi" in cls:
            emploi = clean(expand_abbrevs(c.text())).strip(":").strip()

        elif "tlf_ccrochet" in cls and not crochet:
            crochet = clean(c.text())

        elif "tlf_csynonime" in cls:
            synonymes.append(clean(expand_abbrevs(c.text())))

        elif "tlf_cexemple" in cls:
            ex = get_example(c)
            if ex:
                all_examples.append(ex)

        elif "tlf_tabulation" in cls:
            for ex_node in c.find_class("tlf_cexemple"):
                ex = get_example(ex_node)
                if ex:
                    all_examples.append(ex)

        elif "tlf_parsynt" in cls:
            for syn_node in c.find_class("tlf_csyntagme"):
                # Strip leading "SYNT. " label from the text
                t = re.sub(r"^\s*SYNT\.\s*", "", clean(syn_node.text()))
                if t:
                    syntagmes.append(t)

        elif "tlf_parothers" in cls:
            t = clean(c.text())
            # Strip leading "Rem. " or "REM. "
            t = re.sub(r"^\s*Rem\.?\s*", "", t, flags=re.IGNORECASE)
            if t:
                notes.append(t)

        elif "tlf_parah" in cls or "tlf_paraputir" in cls:
            sub_nodes.append(c)

    # ── Header line ────────────────────────────────────────────────────
    parts = []
    if plan:
        parts.append(f"\033[1m{plan}\033[0m")
    if domaine:
        parts.append(domaine)
    if expr:
        parts.append(f"\033[3m{expr}\033[0m")
    if emploi:
        parts.append(f"({emploi})")
    if crochet and not emploi:
        parts.append(crochet)
    if defn:
        parts.append(defn)

    if parts:
        line = pad + " ".join(parts)
        if not detail and _has_more_content(node, show_ex):
            line += _MORE_INDICATOR
        lines.append(line)

    # ── Synonyms / antonyms ────────────────────────────────────────────
    for syn in synonymes:
        lines.append(pad + "    " + syn)

    # ── Examples ───────────────────────────────────────────────────────
    if detail:
        examples_to_show = all_examples
    elif show_ex:
        examples_to_show = all_examples[:1]
    else:
        examples_to_show = []

    for i, ex in enumerate(examples_to_show):
        label = f"Ex. {i+1} : " if detail and len(all_examples) > 1 else "Ex. : "
        wrapped = textwrap.fill(
            ex,
            width=88,
            initial_indent=pad + "    " + label,
            subsequent_indent=pad + "    " + " " * len(label),
        )
        lines.append(wrapped)

    # ── Syntagmes (detail mode only) ───────────────────────────────────
    if detail and syntagmes:
        lines.append("")
        lines.append(pad + "  Expressions courantes :")
        for s in syntagmes:
            wrapped = textwrap.fill(
                s,
                width=88,
                initial_indent=pad + "    ",
                subsequent_indent=pad + "    ",
            )
            lines.append(wrapped)

    # ── Notes / remarks (detail mode only) ────────────────────────────
    if detail and notes:
        lines.append("")
        for n in notes:
            lines.append(pad + "  Note : " + n)

    # ── Recurse into sub-senses ────────────────────────────────────────
    if sub_nodes:
        lines.append("")

    for sub in sub_nodes:
        lines.extend(render_parah(sub, depth + 1, show_ex, detail=detail))

    return lines


# ── Sense path resolution ──────────────────────────────────────────────────

def _to_roman(n):
    """Convert a small integer to uppercase Roman numeral string."""
    result = ""
    for val, sym in [(10,"X"),(9,"IX"),(5,"V"),(4,"IV"),(1,"I")]:
        while n >= val:
            result += sym
            n -= val
    return result

_SMALL_ROMANS = {
    "I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X",
    "XI", "XII", "XIII", "XIV", "XV", "XVI", "XVII", "XVIII", "XIX", "XX",
}

def tokenize_sense(sense_str):
    """
    Split a sense address string into a list of plan-marker tokens.

      "I.A.1"  →  ["I", "A", "1"]      (dot-separated)
      "IIA1b"  →  ["II", "A", "1", "b"]
      "2B"     →  ["2", "B"]   ("2" will match Roman II at top level)

    Works by greedy-matching valid small Roman numerals first (preventing
    "IIC" from being consumed as a single token instead of ["II", "C"]).
    """
    if "." in sense_str:
        return [t.strip() for t in sense_str.split(".") if t.strip()]

    tokens = []
    s = sense_str
    while s:
        # Try to match the longest valid small Roman numeral prefix
        matched_roman = None
        for length in range(min(len(s), 8), 0, -1):
            if s[:length].upper() in _SMALL_ROMANS:
                matched_roman = s[:length].upper()
                s = s[length:]
                break
        if matched_roman:
            tokens.append(matched_roman)
            continue

        m = (re.match(r"[A-Z]", s) or re.match(r"\d+", s)
             or re.match(r"[a-z]", s) or re.match(r"[\u03b1-\u03c9]", s))
        if m:
            tokens.append(m.group())
            s = s[len(m.group()):]
        else:
            s = s[1:]   # skip unrecognised character

    return tokens

def _matches_plan(plan_text, token):
    """
    True if a plan marker (e.g. "I.", "A.", "1.", "a)", "α)") matches a
    user-supplied token (e.g. "I", "A", "1", "a", "2" for Roman II).
    """
    p = re.sub(r"[\.\)]+$", "", plan_text).strip()
    if p == token or p.upper() == token.upper():
        return True
    # Accept Arabic numeral as Roman numeral equivalent
    try:
        roman = _to_roman(int(token))
        if p.upper() == roman:
            return True
    except (ValueError, TypeError):
        pass
    return False

def find_sense_node(top_parahs, path):
    """
    Walk the parah tree following the path token list.
    Returns (node, breadcrumb_string) or (None, None) if not found.
    """
    current_level = top_parahs
    node = None
    crumbs = []

    for token in path:
        found = None
        for n in current_level:
            plan_span = next(
                (c for c in n.direct_nodes() if "tlf_cplan" in c.classes),
                None,
            )
            if plan_span and _matches_plan(clean_plan(plan_span.text()), token):
                found = n
                crumbs.append(clean_plan(plan_span.text()))
                break
        if found is None:
            return None, None
        node = found
        current_level = [
            c for c in node.direct_nodes()
            if "tlf_parah" in c.classes or "tlf_paraputir" in c.classes
        ]

    return node, " › ".join(crumbs)


# ── Pronunciation extraction ───────────────────────────────────────────────

# Patterns that introduce the etymological analysis (after historical attestations)
_ORIGIN_MARKER = re.compile(
    r'(?:'
    r'Empr\.?\s+au\s'
    r'|Du\s+(?:(?:b|a|m|moy)\.?\s+)?(?:lat|gr|frq|germ|frk)\b'
    r'|De\s+l\'(?:a\.?\s+)?(?:angl|esp|ital|arab|all|néerl|prov|occit|turc|persan|hébr)\b'
    r'|Mot\s+\w+'
    r'|[A-C]\s+[Dd]u\s+(?:(?:b|a)\.?\s+)?lat\b'
    r'|Dér(?:ivé)?\.?\s+(?:de|du)\b'
    r'|Comp(?:osé)?\.?\s+(?:de|du)\b'
    r'|Issu\s+de\b'
    r'|[ÉE]tymol\.?\s+(?:incertaine|controversée|obscure|inconnue|mal\s+conn|discutée)\b'
    r'|D\'orig(?:ine)?\.?\s+\w+'
    r')',
    re.IGNORECASE,
)

# Date/period patterns for the first attestation
_FIRST_DATE = re.compile(
    r'(?:ca\.?\s*|vers?\s+|env\.?\s+|fin\s+|début\s+)?'
    r'(?:'
    r'\d{3,4}'                                                 # plain year: 881, 1370
    r'|(?:\d+[erème]+\s+\w+\s+)?[ivxlcIVXLC]{1,6}e[sr]?s?\.'  # century: xes., 1re moitié xes.
    r')',
    re.IGNORECASE,
)


def extract_origin(etym_text):
    """
    From a full 'Étymol. et Hist.' block, extract a minimal one-line origin
    summary: the first attestation date + the etymological source statement
    (source language, borrowed word, and its gloss).  Historical attestation
    dates, citations, and scholarly discussion are omitted.
    """
    # Strip section header
    text = re.sub(r'^[ÉE]tymol\.?\s+et\s+Hist\.?\s*', '', etym_text,
                  flags=re.IGNORECASE).strip()

    # Locate the transition from attestations to etymology analysis
    m = _ORIGIN_MARKER.search(text)
    origin_pos = m.start() if m else len(text)

    # First attestation date (from the block before the analysis)
    dm = _FIRST_DATE.search(text[:origin_pos])
    first_date = dm.group(0).strip() if dm else ''

    if not m:
        snippet = (text[:200].rsplit(' ', 1)[0] + '…') if len(text) > 200 else text
        return (f"{first_date}  ·  {snippet}" if first_date else snippet)

    origin = text[origin_pos:]

    # Uncertain/controversial: just label it as such
    if re.match(r'[ÉE]tymol\.?\s+(?:incertaine|controversée|obscure|inconnue)', origin,
                re.IGNORECASE):
        m2 = re.match(r'[ÉE]tymol\.?\s+\w+', origin, re.IGNORECASE)
        label = (m2.group(0) if m2 else 'Étymol. incertaine') + '.'
        return (f"{first_date}  ·  {label}" if first_date else label)

    # Strip a leading section marker like "A " or "B " (e.g. "A du b. lat. cattus")
    origin = re.sub(r'^[A-C]\s+', '', origin)

    # Stop right after the first closing guillemet (end of source-word gloss)
    idx = origin.find('»')
    if 0 < idx <= 350:
        snippet = origin[:idx + 1].strip()
        rest = origin[idx + 1:].lstrip()
        if rest and rest[0] in '.,':
            snippet += rest[0]
        return (f"{first_date}  ·  {snippet}" if first_date else snippet)

    # No guillemet: truncate at 200 chars on a word boundary
    if len(origin) > 200:
        snippet = origin[:200].rsplit(' ', 1)[0] + '…'
    else:
        snippet = origin.strip()
    return (f"{first_date}  ·  {snippet}" if first_date else snippet)


def extract_etymology(art_div):
    """
    Find the 'Étymol. et Hist.' section inside any tlf_parothers block and
    return its text, stripped of everything before it (pronunciation, etc.)
    and after it (bibliography 'Bbg.', frequency 'Fréq. abs.', etc.).

    Returns a non-empty string or "" if the section is absent.
    """
    for c in art_div.direct_nodes():
        if "tlf_parothers" not in c.classes:
            continue
        txt = clean(c.text())
        m = re.search(r"Étymol\b", txt, re.IGNORECASE)
        if not m:
            continue
        text = txt[m.start():]
        # Truncate at the next scholarly section that follows etymology
        end = re.search(
            r"\s+(?:Bbg\.|Fréq\.?\s+abs\.|Homon\.|Stat\.|DÉR\.|COMP\.)",
            text,
        )
        if end:
            text = text[: end.start()]
        return text.strip()
    return ""


def extract_pronunciation(art_div):
    """
    Find the tlf_parothers block (anywhere in the article div) that contains
    the pronunciation section and return just the IPA / phonetic notation.

    The block may appear before the senses (simple entries) or after them
    (complex entries like 'beau'), so we scan all direct children.

    Returns a string like "[pyzil(l)animite]" or "" if not found.
    """
    for c in art_div.direct_nodes():
        if "tlf_parothers" not in c.classes:
            continue
        text = clean(c.text())
        if not re.search(r"prononc", text, re.IGNORECASE):
            continue
        # Skip to the first '[' — start of the IPA transcription
        idx = text.find("[")
        if idx == -1:
            continue
        text = text[idx:]
        # Truncate at the first sentence boundary: a period (not after a digit)
        # followed by whitespace and an uppercase letter — that marks the start
        # of the next sub-section (Enq., Homon., Att. ds, Étymol., etc.)
        m = re.search(
            r"(?<!\d)\.\s+(?=[A-ZÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÐÑÒÓÔÕÖÙÚÛÜÝ])",
            text,
        )
        if m:
            text = text[: m.start()]
        # Collapse any whitespace that ended up before a combining diacritic
        # (the TLFi source sometimes puts combining chars on a new line)
        text = re.sub(r"\s+([\u0300-\u036f\u1dc0-\u1dff])", r"\1", text)
        return text.strip()
    return ""


# ── Anki card builder ─────────────────────────────────────────────────────

def _collect_definitions(node, results=None):
    """
    Recursively walk a tlf_parah tree and collect every definition string.
    Each entry is optionally prefixed with its usage label (emploi) or
    usage constraint (crochet) in parentheses.
    """
    if results is None:
        results = []

    defn = emploi = crochet = domaine = expr = ""
    sub_nodes = []
    defn_seen = False

    for c in node.direct_nodes():
        cls = c.classes
        if "tlf_cdomaine" in cls:
            domaine = clean(c.text())
        elif "tlf_csyntagme" in cls:
            if not defn_seen:
                expr = clean(c.text())
        elif "tlf_cdefinition" in cls:
            defn = clean(c.text())
            defn_seen = True
        elif "tlf_cemploi" in cls:
            emploi = clean(expand_abbrevs(c.text())).strip(":").strip()
        elif "tlf_ccrochet" in cls and not crochet:
            crochet = clean(c.text())
        elif "tlf_parah" in cls or "tlf_paraputir" in cls:
            sub_nodes.append(c)

    if defn:
        # Build plain-text version (for terminal display / selection list)
        plain_parts = []
        if domaine:
            plain_parts.append(domaine)
        if expr:
            plain_parts.append(expr)
        if emploi:
            plain_parts.append(f"({emploi})")
        elif crochet:
            plain_parts.append(crochet)
        plain = (" ".join(plain_parts) + " " if plain_parts else "") + defn

        # Build HTML version (for Anki card back)
        html_parts = []
        if domaine:
            html_parts.append(html_escape(domaine))
        if expr:
            html_parts.append(f"<i>{html_escape(expr)}</i>")
        if emploi:
            html_parts.append(f"({html_escape(emploi)})")
        elif crochet:
            html_parts.append(html_escape(crochet))
        html_parts.append(html_escape(defn))
        html = " ".join(html_parts)

        results.append((plain, html))

    for sub in sub_nodes:
        _collect_definitions(sub, results)

    return results


def _noun_article(pos):
    """
    Given an expanded POS string, return the definite article for a noun,
    or None if the word is not a noun.

      "nom féminin"              → "la"
      "nom masculin"             → "le"
      "nom masculin et féminin"
      "nom féminin et masculin"  → "le/la"
      "nom" (no gender given)    → "le/la"  (common/variable gender)

    Uses a word-boundary check so "pronom" and "pronominal" are not matched.
    """
    p = pos.lower()
    if not re.search(r"\bnom\b", p):
        return None
    masc = "masculin" in p
    fem  = "féminin" in p
    if masc and fem:
        return "le/la"
    if masc:
        return "le"
    if fem:
        return "la"
    # "nom" present but gender unspecified → common / variable gender
    return "le/la"


def extract_anki_data(root):
    """
    Parse the CNRTL page and return (front_html, definitions, pron) where:
      front_html   — the card front: word with article, ready for AnkiConnect
      definitions  — list of (plain, html) definition tuples (unfiltered)
      pron         — IPA pronunciation string, or "" if absent

    Returns (None, None, None) if the page could not be parsed.
    """
    contentbox = root.find_id("contentbox")
    if not contentbox:
        return None, None, None

    mot_nodes  = contentbox.find_class("tlf_cmot")
    code_nodes = contentbox.find_class("tlf_ccode")
    if not mot_nodes:
        return None, None, None

    word = clean(mot_nodes[0].text()).rstrip(",").strip()
    # Strip trailing homograph digit from the first token only:
    # "CHAT1, CHATTE" → "CHAT, CHATTE"
    word = re.sub(r"^([^\W\d_]+)\d+", r"\1", word, flags=re.UNICODE)
    word = word.lower()

    pos     = clean(expand_abbrevs(code_nodes[0].text())) if code_nodes else ""
    article = _noun_article(pos)

    lexicontent = contentbox.find_id("lexicontent")
    art_div = None
    if lexicontent:
        for c in lexicontent.direct_nodes():
            if c.id.startswith("art"):
                art_div = c
                break
    if not art_div:
        art_div = contentbox

    pron = extract_pronunciation(art_div)

    if article:
        # Detect aspirated h: TLFi marks it as "init. asp" in the pronunciation block.
        # Aspirated h blocks elision/liaison; mute h (l'heure, l'homme) allows it.
        aspirated_h = (
            word.startswith("h") and
            bool(re.search(r"init\.\s*asp", pron, re.IGNORECASE))
        )

        vowel_or_mute_h = re.match(r"[aeiouyàâäéèêëîïôùûüœæh]", word, re.IGNORECASE)

        if aspirated_h:
            display = f"{article} *{word}"
        elif vowel_or_mute_h:
            display = f"({article}) {word}"
        else:
            display = f"{article} {word}"
    else:
        display = word

    front_html = (
        '<div style="font-size:1.5em;text-align:center;font-weight:bold;">'
        + html_escape(display)
        + "</div>"
    )

    top_parahs  = [c for c in art_div.direct_nodes() if "tlf_parah" in c.classes]
    definitions = []

    if top_parahs:
        for parah in top_parahs:
            _collect_definitions(parah, definitions)

    # If no definitions came from the parah tree (e.g. sections only carry usage
    # labels / examples but the real definition sits in the article preamble),
    # or if there are no parah sections at all, fall back to the preamble.
    if not definitions:
        _, defn, _, domaine, _, _, _, _ = _collect_pre_parah(art_div)
        if defn:
            plain = (domaine + " " if domaine else "") + defn
            html  = (html_escape(domaine) + " " if domaine else "") + html_escape(defn)
            definitions.append((plain, html))

    return front_html, definitions, pron


def build_anki_card(front_html, definitions, pron=""):
    """
    Given a pre-built front_html, a (possibly filtered) list of definition
    tuples, and an optional IPA string, return (front_html, back_html) ready
    for AnkiConnect.  The IPA is shown above the definitions list when present.
    """
    parts = []
    if pron:
        parts.append(
            '<div style="text-align:center;color:#555;margin-bottom:0.6em;">'
            + html_escape(pron)
            + "</div>"
        )
    if definitions:
        items = "".join(f"<li>{d[1]}</li>" for d in definitions)
        parts.append(f"<ol>{items}</ol>")
    back_html = "".join(parts)
    return front_html, back_html


def _anki_request(action, **params):
    """
    Send a single AnkiConnect request and return the parsed JSON response.
    Raises SystemExit on network error; returns the response dict otherwise.
    """
    payload = {"action": action, "version": 6, "params": params}
    data    = json.dumps(payload).encode("utf-8")
    req     = Request(
        "http://localhost:8765",
        data=data,
        headers={"Content-Type": "application/json"},
    )
    try:
        with urlopen(req, timeout=5) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except URLError as e:
        print(f"Impossible de joindre AnkiConnect : {e.reason}", file=sys.stderr)
        print(
            "Vérifiez qu'Anki est ouvert et que l'extension AnkiConnect est installée.",
            file=sys.stderr,
        )
        sys.exit(1)


def anki_add_card(front_html, back_html, deck="Français"):
    """
    Add a Basic note to an Anki deck via AnkiConnect (http://localhost:8765).
    Creates the deck first if it doesn't exist.
    Returns the new note ID on success; exits on error.
    """
    # Ensure the deck exists (createDeck is a no-op when it already does)
    r = _anki_request("createDeck", deck=deck)
    if r.get("error"):
        print(f"Erreur AnkiConnect (createDeck) : {r['error']}", file=sys.stderr)
        sys.exit(1)

    r = _anki_request(
        "addNote",
        note={
            "deckName": deck,
            "modelName": "Basic",
            "fields": {"Front": front_html, "Back": back_html},
            "tags": ["cnrtl"],
        },
    )
    if r.get("error"):
        print(f"Erreur AnkiConnect : {r['error']}", file=sys.stderr)
        sys.exit(1)

    return r["result"]


# ── Top-level renderer ─────────────────────────────────────────────────────

def _collect_pre_parah(art_div):
    """
    Scan art_div direct children that appear BEFORE any tlf_parah block and
    collect content that belongs to the entry's preamble: usage label, main
    definition, synonymes, usage constraint, examples, syntagmes, notes, and
    sub-usage blocks (tlf_paraputir).

    These elements appear in simple single-sense entries (e.g. "pusillanimité")
    where the TLFi puts everything directly in the article div rather than
    inside a tlf_parah hierarchy, and also as a global definition header in
    complex multi-sense entries (e.g. "aimer").
    """
    emploi = defn = crochet = domaine = ""
    synon      = []
    examples   = []
    syntagmes  = []
    subs       = []   # tlf_paraputir nodes

    for c in art_div.direct_nodes():
        cls = c.classes
        if "tlf_parah" in cls:
            break                               # stop at first sectioned sense
        if "tlf_cvedette" in cls:
            continue
        elif "tlf_cdomaine" in cls and not domaine:
            domaine = clean(c.text())
        elif "tlf_cdefinition" in cls and not defn:
            defn = clean(c.text())
        elif "tlf_cemploi" in cls and not emploi:
            emploi = clean(expand_abbrevs(c.text())).strip(":").strip()
        elif "tlf_ccrochet" in cls and not crochet:
            crochet = clean(c.text())
        elif "tlf_csynonime" in cls:
            synon.append(clean(expand_abbrevs(c.text())))
        elif "tlf_csyntagme" in cls:
            t = re.sub(r"^\s*SYNT\.\s*", "", clean(c.text()))
            if t:
                syntagmes.append(t)
        elif "tlf_cexemple" in cls:
            ex = get_example(c)
            if ex:
                examples.append(ex)
        elif "tlf_tabulation" in cls:
            for ex_node in c.find_class("tlf_cexemple"):
                ex = get_example(ex_node)
                if ex:
                    examples.append(ex)
        elif "tlf_parsynt" in cls:
            for syn_node in c.find_class("tlf_csyntagme"):
                t = re.sub(r"^\s*SYNT\.\s*", "", clean(syn_node.text()))
                if t:
                    syntagmes.append(t)
        # tlf_parothers is intentionally skipped here: at the article level it
        # contains pronunciation, etymology, and frequency data — scholarly
        # apparatus the user does not want. Usage remarks inside tlf_parah nodes
        # are handled separately by render_parah().
        elif "tlf_paraputir" in cls:
            subs.append(c)

    return emploi, defn, crochet, domaine, synon, examples, syntagmes, subs


def render(root, show_ex, sense_path=None):
    """Walk the parsed DOM and return the formatted output string."""
    contentbox = root.find_id("contentbox")
    if not contentbox:
        return None

    mot_nodes = contentbox.find_class("tlf_cmot")
    code_nodes = contentbox.find_class("tlf_ccode")
    if not mot_nodes:
        return None

    word = clean(mot_nodes[0].text()).rstrip(",").strip()
    pos  = clean(expand_abbrevs(code_nodes[0].text())) if code_nodes else ""

    # Find the article div (id="artNNNN") inside lexicontent before building
    # the header so we can include the pronunciation on the same line.
    lexicontent = contentbox.find_id("lexicontent")
    art_div = None
    if lexicontent:
        for c in lexicontent.direct_nodes():
            if c.id.startswith("art"):
                art_div = c
                break
    if not art_div:
        art_div = contentbox

    pron = extract_pronunciation(art_div)

    header = f"\033[1m{word}\033[0m"
    if pron:
        header += f" {pron}"
    if pos:
        header += f"  —  {pos}"

    lines = [header, ""]

    emploi, defn, crochet, domaine, synon, examples, syntagmes, pre_subs = (
        _collect_pre_parah(art_div)
    )
    top_parahs = [c for c in art_div.direct_nodes() if "tlf_parah" in c.classes]
    is_flat    = not top_parahs   # single-sense entry with no sectioned hierarchy

    # ── Render preamble (global definition / flat entry) ──────────────
    if defn or emploi or crochet or domaine:
        parts = []
        if domaine:
            parts.append(domaine)
        if emploi:
            parts.append(f"({emploi})")
        if crochet and not emploi:
            parts.append(crochet)
        if defn:
            parts.append(defn)

        line = " ".join(parts)

        # [+] indicator: only for flat entries in non-detail summary view.
        # Syntagmes are shown when show_ex=True, so only count them as hidden
        # in plain summary mode.
        if is_flat and not sense_path:
            hidden = (
                len(examples) > (1 if show_ex else 0)
                or (not show_ex and bool(syntagmes))
            )
            if hidden:
                line += _MORE_INDICATOR

        lines.append(line)

        if is_flat:
            # Synonymes
            for syn in synon:
                lines.append("    " + syn)

            # Examples
            if sense_path:
                ex_to_show = examples           # full detail
            elif show_ex:
                ex_to_show = examples[:1]
            else:
                ex_to_show = []

            for i, ex in enumerate(ex_to_show):
                label = f"Ex. {i+1} : " if len(examples) > 1 else "Ex. : "
                wrapped = textwrap.fill(
                    ex,
                    width=88,
                    initial_indent="    " + label,
                    subsequent_indent="    " + " " * len(label),
                )
                lines.append(wrapped)

            # Syntagmes — only in full detail (sense_path or -e for flat entries)
            if (sense_path or show_ex) and syntagmes:
                lines.append("")
                lines.append("  Expressions courantes :")
                for s in syntagmes:
                    lines.append(textwrap.fill(
                        s, width=88, initial_indent="    ", subsequent_indent="    "
                    ))

            # Sub-usages (tlf_paraputir at article level)
            if pre_subs:
                lines.append("")
                for sub in pre_subs:
                    lines.extend(
                        render_parah(sub, 1, show_ex, detail=bool(sense_path or show_ex))
                    )

            return "\n".join(lines)

        else:
            # Sectioned entry: preamble definition is just a header; blank line then sections
            for syn in synon:
                lines.append("    " + syn)
            lines.append("")

    # ── Sense drill-down mode ──────────────────────────────────────────
    if sense_path:
        tokens = tokenize_sense(sense_path)
        node, breadcrumb = find_sense_node(top_parahs, tokens)

        if node is None:
            lines.append(
                f"Sens « {sense_path} » introuvable. "
                "Vérifiez les marqueurs (ex. : IIA1, I.A.1, 2B)."
            )
            return "\n".join(lines)

        lines.append(f"\033[2mSens : {breadcrumb}\033[0m")
        lines.append("")
        lines.extend(render_parah(node, 0, show_ex, detail=True))

    # ── Summary mode ──────────────────────────────────────────────────
    else:
        for parah in top_parahs:
            lines.extend(render_parah(parah, 0, show_ex))
            lines.append("")

    return "\n".join(lines)


# ── Network ────────────────────────────────────────────────────────────────

def fetch(word, tab=None):
    url = BASE_URL + quote(word.lower(), safe="")
    if tab is not None:
        url += f"//{tab}"
    req = Request(url, headers={"User-Agent": "Mozilla/5.0 (cnrtl-cli/1.0)"})
    try:
        with urlopen(req, timeout=10) as resp:
            return resp.read().decode("utf-8", errors="replace")
    except HTTPError as e:
        print(f"Erreur HTTP {e.code} pour : {url}", file=sys.stderr)
        sys.exit(1)
    except URLError as e:
        print(f"Impossible de joindre le CNRTL : {e.reason}", file=sys.stderr)
        sys.exit(1)


# ── Tab bar ────────────────────────────────────────────────────────────────

_VTOOLBAR_RE = re.compile(
    r'<li([^>]*)>'              # <li> or <li id="vitemselected">
    r'.*?//(\d+)\'[^>]*>'      # sendRequest URL containing the tab index
    r'(.*?)'                    # visible content: <span>WORD</span>, POS
    r'</a>',
    re.DOTALL,
)
_SUP_DIGITS = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def parse_tabs(html):
    """
    Parse the vtoolbar section and return (tabs, current_idx).

    tabs        — list of (int_index, label_string) in document order
    current_idx — 0-based index of the currently displayed tab (matches an
                  int_index in tabs)

    Returns ([], 0) when no vtoolbar is present (single-entry words).
    """
    m = re.search(r'<div id="vtoolbar">(.*?)</div>', html, re.DOTALL)
    if not m:
        return [], 0

    tabs = []
    current_idx = 0
    for item in _VTOOLBAR_RE.finditer(m.group(1)):
        li_attrs   = item.group(1)
        tab_index  = int(item.group(2))
        content    = item.group(3)

        # Convert <sup>N</sup> → superscript Unicode, then strip remaining tags
        content = re.sub(
            r'<sup>(.*?)</sup>',
            lambda s: s.group(1).translate(_SUP_DIGITS),
            content,
        )
        label = re.sub(r'<[^>]+>', '', content)    # strip all other tags
        label = re.sub(r'\s*,\s*', ' ', label)     # commas → spaces
        label = re.sub(r'\s+', ' ', label).strip() # collapse whitespace

        tabs.append((tab_index, label))
        if 'vitemselected' in li_attrs:
            current_idx = tab_index

    return tabs, current_idx


def _format_tab_bar(tabs, current_idx):
    """Return a one-line tab bar string, or '' when there is only one tab."""
    if len(tabs) <= 1:
        return ""
    parts = []
    for idx, label in tabs:
        num = idx + 1   # display as 1-based
        if idx == current_idx:
            parts.append(f"\033[1m{num} {label}\033[0m")
        else:
            parts.append(f"\033[2m{num} {label}\033[0m")
    return "\n" + "  \033[2m·\033[0m  ".join(parts)


# ── Entry point ────────────────────────────────────────────────────────────

_INTERACTIVE_HELP = """\
  <mot>                      Chercher un mot
  <mot> -e                   Afficher une définition avec exemples
  <mot> <sens>               Détail d'un sens précis (ex: IIA1, I.A.1, 2B)
  <mot> --etym               Afficher l'origine du mot (date + source, minimal)
  <mot> --etym-full          Afficher l'étymologie et l'histoire complètes
  <mot> --tab N              Afficher l'entrée N (si plusieurs entrées existent)
  <mot> --anki               Créer une carte Anki (paquet par défaut : Français)
  <mot> --anki --deck NOM    Créer une carte Anki dans un paquet spécifique
  help                       Afficher cette aide
  quit / exit                Quitter\
"""


def _run_command(args):
    """
    Execute one lookup command given a list of argument strings.
    Raises SystemExit on hard errors (bad flags, network failure, etc.)
    so that the interactive loop can catch and ignore them.
    """
    if "-h" in args or "--help" in args:
        print(_INTERACTIVE_HELP)
        return

    show_ex       = "-e" in args or "--examples" in args
    do_anki       = "--anki" in args
    do_etym_full  = "--etym-full" in args
    do_etym       = "--etym" in args and not do_etym_full

    # Parse --deck NAME
    deck = "Français"
    if "--deck" in args:
        idx = args.index("--deck")
        if idx + 1 >= len(args):
            print("--deck requiert un nom de paquet.", file=sys.stderr)
            sys.exit(1)
        deck = args[idx + 1]

    # Parse --tab N (1-based user input → 0-based URL index)
    tab = None
    if "--tab" in args:
        idx = args.index("--tab")
        if idx + 1 >= len(args):
            print("--tab requiert un numéro d'entrée.", file=sys.stderr)
            sys.exit(1)
        try:
            tab = int(args[idx + 1]) - 1
            if tab < 0:
                raise ValueError
        except ValueError:
            print("--tab requiert un entier positif.", file=sys.stderr)
            sys.exit(1)

    # Collect positional args, skipping the values after --deck and --tab
    non_flags = []
    skip_next = False
    for a in args:
        if skip_next:
            skip_next = False
            continue
        if a in ("--deck", "--tab"):
            skip_next = True
            continue
        if not a.startswith("-"):
            non_flags.append(a)

    if not non_flags:
        print("Usage : <mot> [sens] [-e] [--anki [--deck NOM]] [--tab N]", file=sys.stderr)
        sys.exit(1)

    word       = non_flags[0]
    sense_path = non_flags[1] if len(non_flags) > 1 else None

    html   = fetch(word, tab=tab)
    parser = PageParser()
    parser.feed(html)

    tabs, current_tab = parse_tabs(html)
    tab_bar = _format_tab_bar(tabs, current_tab)

    if do_anki:
        front_html, definitions, pron = extract_anki_data(parser.root)
        if front_html is None:
            print(
                f"Le mot « {word} » est introuvable ou la page n'a pas pu être analysée.",
                file=sys.stderr,
            )
            sys.exit(1)

        print()
        for i, (plain, _) in enumerate(definitions, 1):
            wrapped = textwrap.fill(
                plain,
                width=88,
                initial_indent=f"  {i}. ",
                subsequent_indent=" " * (len(str(i)) + 4),
            )
            print(wrapped)
        print()

        while True:
            raw = input('Définitions à inclure (ex: "1 3 5", ou "all") : ').strip()
            if not raw:
                continue
            if raw.lower() == "all":
                selected = definitions
                break
            try:
                indices = [int(x) for x in raw.split()]
                if not indices:
                    continue
                out_of_range = [i for i in indices if not (1 <= i <= len(definitions))]
                if out_of_range:
                    print(
                        f"Numéros hors limite : {out_of_range}. "
                        f"Entrez des nombres entre 1 et {len(definitions)}."
                    )
                    continue
                selected = [definitions[i - 1] for i in indices]
                break
            except ValueError:
                print('Format invalide. Entrez des numéros séparés par des espaces, ou "all".')

        front_html, back_html = build_anki_card(front_html, selected, pron)
        note_id = anki_add_card(front_html, back_html, deck)
        print(f"Carte ajoutée au paquet « {deck} » (note ID : {note_id}).")
        return

    if do_etym or do_etym_full:
        # Locate art_div (same logic as in render/extract_anki_data)
        contentbox  = parser.root.find_id("contentbox")
        lexicontent = contentbox.find_id("lexicontent") if contentbox else None
        art_div     = None
        if lexicontent:
            for c in lexicontent.direct_nodes():
                if c.id.startswith("art"):
                    art_div = c
                    break
        if not art_div and contentbox:
            art_div = contentbox

        etym = extract_etymology(art_div) if art_div else ""
        if not etym:
            print(f"Aucune section étymologie trouvée pour « {word} ».", file=sys.stderr)
            sys.exit(1)

        mot_nodes  = contentbox.find_class("tlf_cmot") if contentbox else []
        word_label = clean(mot_nodes[0].text()).rstrip(",").strip() if mot_nodes else word
        print(f"\033[1m{word_label}\033[0m\n")

        if do_etym_full:
            print(textwrap.fill(etym, width=88))
        else:
            print(extract_origin(etym))

        if tab_bar:
            print(tab_bar)
        return

    result = render(parser.root, show_ex, sense_path=sense_path)

    if result is None:
        print(
            f"Le mot « {word} » est introuvable ou la page n'a pas pu être analysée.",
            file=sys.stderr,
        )
        sys.exit(1)

    if tab_bar:
        result += "\n" + tab_bar
    print(result)


_DIVIDER = "\033[2m" + "─" * 88 + "\033[0m"


def _interactive_loop():
    import shlex
    try:
        import readline  # noqa: F401 — side-effect: enables arrow-key history in input()
    except ImportError:
        pass

    print("cnrtl — tapez un mot pour le chercher, « help » pour l'aide, « quit » pour quitter.")
    print()
    while True:
        try:
            line = input("> ").strip()
        except EOFError:       # Ctrl-D
            print()
            break
        except KeyboardInterrupt:  # Ctrl-C — cancel current line, stay in loop
            print()
            continue

        if not line:
            continue

        if line.lower() in ("quit", "exit", "q"):
            break

        if line.lower() in ("help", "aide", "?", "-h", "--help"):
            print()
            print(_INTERACTIVE_HELP)
            print()
            continue

        try:
            args = shlex.split(line)
        except ValueError as e:
            print(f"Erreur de syntaxe : {e}", file=sys.stderr)
            continue

        print(_DIVIDER)
        try:
            _run_command(args)
        except SystemExit:
            pass   # error already printed; stay in loop


def main():
    args = sys.argv[1:]

    if not args:
        _interactive_loop()
        return

    if "-h" in args or "--help" in args:
        print(__doc__)
        sys.exit(0)

    _run_command(args)


if __name__ == "__main__":
    main()
