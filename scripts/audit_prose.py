#!/usr/bin/env python3
"""
scripts/audit_prose.py — prose <-> Lean consistency audit for Euclids-path.

Exhaustively cross-checks the backticked identifiers cited in the prose
(prose/*.md + README.md) against the actual Lean environment, and re-confirms
the global status counters. It answers four questions:

  1. EXISTENCE  — does every cited Lean-declaration-shaped name actually exist?
  2. LABELS     — does every 🟢/🟡 badge match the declaration's real axiom taint?
  3. COUNTERS   — do the "16 / one axiom / one sorry / one boundary" claims hold?
  4. OVERCLAIM  — does any sentence claim an open problem is *solved*?

Oracles (produced by a Lean dump — see scripts/dump_audit_data.lean, or pass
--data DIR pointing at a dir holding all_names.txt + euclids_decls.tsv):
  all_names.txt      one Lean constant full-name per line (whole environment)
  euclids_decls.tsv  name<TAB>kind<TAB>tainted(0/1)<TAB>sorry(0/1) for EuclidsPath decls

Exit code 0 iff no phantom names, no confirmed label mismatches, and counters OK.
"""
import sys, os, re, glob, argparse

EXPECTED_TAINT = 16          # tainted thm/def (all twins; RH/NS/Collatz withdrawn, Option A)
EXPECTED_SORRY = 1
EXPECTED_BOUNDARIES = 1       # the axiom decrees ONLY the twin seriality boundary

SRC_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def load_oracles(data_dir, root):
    full = set()
    last = {}          # last component -> set of full names
    with open(os.path.join(data_dir, "all_names.txt"), encoding="utf-8") as f:
        for line in f:
            n = line.strip()
            if not n:
                continue
            full.add(n)
            last.setdefault(n.rsplit(".", 1)[-1], set()).add(n)
    decls = {}         # last component -> list of (full, tainted, sorry)
    with open(os.path.join(data_dir, "euclids_decls.tsv"), encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 4:
                continue
            name, kind, tainted, has_sorry = parts
            decls.setdefault(name.rsplit(".", 1)[-1], []).append(
                (name, tainted == "1", has_sorry == "1"))
    # source-text identifier oracle: every identifier that literally appears in the
    # Lean sources (catches local `have`s, structure fields, tactics, section vars —
    # real names that are cited in prose but are not top-level environment constants)
    src = set()
    for pat in ("EuclidsPath/**/*.lean", "EuclidsPath.lean", "scripts/*.lean"):
        for p in glob.glob(os.path.join(root, pat), recursive=True):
            try:
                for tok in SRC_IDENT.findall(open(p, encoding="utf-8", errors="ignore").read()):
                    src.add(tok)
            except OSError:
                pass
    return full, last, decls, src

# repo files that legitimately appear in backticks (harnesses, results, modules)
def repo_files(root):
    fs = set()
    for p in glob.glob(os.path.join(root, "**", "*"), recursive=True):
        fs.add(os.path.basename(p))
    return fs

IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
FILE_EXT = re.compile(r"\.(lean|py|md|txt|toml|json|sh|yml|yaml|png)$")
# math-variable notation written in backticks, e.g. P_A, X_A, S_0, M_p, M_11, H_RH, R_fc, D_a
NOTATION = re.compile(r"^[A-Za-z][A-Za-z]?_[A-Za-z0-9]{1,3}$")

# a token worth existence-checking: looks like a Lean decl (has _ or .), not a prose word,
# not a file reference, not a short math-variable subscript
def is_declish(tok):
    if not IDENT.match(tok) or tok.endswith("."):
        return False
    if FILE_EXT.search(tok) or NOTATION.match(tok):
        return False
    return "_" in tok or "." in tok

def name_exists(tok, full, last, src):
    if tok in full:
        return True
    tail = tok.rsplit(".", 1)[-1]
    # appears anywhere in the Lean source text (local have/field/tactic/section var)?
    if tail in src or tok in src:
        return True
    if "." not in tok:
        return tail in last
    suffix = "." + tok
    cands = last.get(tail, ())
    return any(n.endswith(suffix) or n == tok for n in cands)

def decl_matches(tok, decls):
    tail = tok.rsplit(".", 1)[-1]
    cands = decls.get(tail, [])
    if "." in tok:
        suffix = "." + tok
        cands = [c for c in cands if c[0].endswith(suffix) or c[0] == tok]
    return cands

EMOJI_G, EMOJI_Y, EMOJI_R = "🟢", "🟡", "🔴"
BADGE = re.compile(r"[🟢🟡🔴]")
BACKTICK = re.compile(r"`([^`]+)`")

SPAN = re.compile(r"`([^`]+)`")
def audit(files, full, last, decls, src, files_set):
    phantoms, missing_files, mislabels, ambiguous = [], [], [], []
    cited = set()
    for path in files:
        with open(path, encoding="utf-8") as f:
            text = f.read()
        for i, line in enumerate(text.splitlines(), 1):
            for m in SPAN.finditer(line):
                tok = m.group(1).strip()
                # badge adjacent to this backtick span (house pattern: `name`, 🟢),
                # but not across a clause separator ';' (table rows chain several clauses)
                after = line[m.end(): m.end() + 14].split(";")[0]
                adj_badges = set(BADGE.findall(after))
                # file references: check the file exists in the repo (skip glob patterns)
                if FILE_EXT.search(tok) and "/" not in tok and " " not in tok and "*" not in tok:
                    if os.path.basename(tok) not in files_set:
                        missing_files.append((tok, os.path.basename(path), i))
                    continue
                if not IDENT.match(tok):
                    continue
                cited.add(tok)
                if is_declish(tok) and not name_exists(tok, full, last, src):
                    phantoms.append((tok, os.path.basename(path), i))
                d = decl_matches(tok, decls)
                if d and adj_badges:
                    any_taint = any(t for _, t, _ in d)
                    all_taint = all(t for _, t, _ in d)
                    where = (os.path.basename(path), i)
                    if EMOJI_Y in adj_badges and EMOJI_G not in adj_badges and not any_taint:
                        (mislabels if len(d) == 1 else ambiguous).append(("🟡-but-green", tok, *where))
                    if EMOJI_G in adj_badges and EMOJI_Y not in adj_badges and all_taint:
                        (mislabels if len(d) == 1 else ambiguous).append(("🟢-but-tainted", tok, *where))
    return cited, phantoms, missing_files, mislabels, ambiguous

def counter_check(files):
    issues = []
    taint_re = re.compile(r"(?:ровно\s*\**|таких\s+|AXIOM-TAINTED\D{0,20})(\d{2,3})")
    for path in files:
        txt = open(path, encoding="utf-8").read()
        base = os.path.basename(path)
        for m in re.finditer(r"(\d{2,3})\s*(?:AXIOM-TAINTED|таких деклараци|деклараци[йяи][^.]{0,40}аксиом)", txt):
            if m.group(1) != str(EXPECTED_TAINT):
                issues.append((base, f"taint count {m.group(1)} != {EXPECTED_TAINT}: …{txt[max(0,m.start()-30):m.start()+40]}…"))
        for stale in ("ровно 52", "ровно 45", "ровно 47", "с четырьмя границами", "четырьмя причинными границами",
                      "тремя причинными границами", "три границы декрета", "три жёлтые границы", "три живые границы",
                      "exactly 52", "exactly 45", "exactly 47", "four causal boundaries", "four decree boundaries",
                      "three causal boundaries", "three decree boundaries", "three living boundaries"):
            if stale in txt:
                issues.append((base, f"stale phrase: {stale!r}"))

        # Historical/withdrawn marker: a line carrying one is exempt from the boundary checks below.
        HIST = re.compile(r"(?i)(was |were |Option A|withdrawn|detached|отсоедин|снят|сняты|был[аои]?\b|"
                          r"истори|history|прежде|раньше|earlier|(?:once|когда-то)|"
                          r"на тот момент|at (?:that|the) moment)")

        def _line(ms, me, _txt=txt):
            ls = _txt.rfind("\n", 0, ms) + 1
            le = _txt.find("\n", me);  le = len(_txt) if le < 0 else le
            return _txt[ls:le]

        # (a) "three boundaries" / "три|трёх|трех границ*" — the decree carries ONLY the twin boundary.
        #     Skip lines carrying a historical/withdrawn marker.
        for m in re.finditer(r"(?i)\b(?:three boundaries|(?:три|трёх|трех)\s+границ\w*)", txt):
            if not HIST.search(_line(m.start(), m.end())):
                issues.append((base, f"'three boundaries' phrasing (decree has one, the twins): "
                                     f"…{txt[max(0,m.start()-30):m.end()+30]}…"))

        # (b) "second|third boundary of the decree" / "вторая|третья граница декрета" asserted as LIVE.
        for m in re.finditer(r"(?i)(?:(?:second|third)\s+boundary\s+of\s+the\s+decree|"
                             r"(?:втор\w+|треть\w+)\s+границ\w+\s+декрета)", txt):
            if not HIST.search(_line(m.start(), m.end())):
                issues.append((base, f"'second/third boundary of the decree' as LIVE (Riemann/NS withdrawn, "
                                     f"Option A): …{txt[max(0,m.start()-20):m.end()+30]}…"))

        # (c) taint numbers other than 16 in count phrasings: "declarations depending on it" /
        #     "зависящих от" / "currently NN" / "сейчас их NN" / "Taint NN" / "toll NN" / "NN -> NN".
        #     A number is 2-3 digits NOT followed by another digit (so citation years like 2025
        #     are not partially matched), keywords are whole words (so "Stoll" != "toll").
        N = r"(\d{2,3})(?!\d)"
        TAINT_PHRASE = re.compile(
            r"(?i)"
            r"(?:\*\*" + N + r"\*\*|\b" + N + r"\b)\s*(?:declarations\s+depending\s+on\s+it|"
            r"деклараци\w*\s+зависящ\w+\s+от|зависящ\w+\s+от\s+неё\s+деклараци\w*)"
            r"|\b(?:currently|сейчас\s+их|Taint|Таинт|toll|такса)\b[^0-9\n]{0,25}?\(?\**\s*" + N)
        for m in TAINT_PHRASE.finditer(txt):
            nums = [g for g in m.groups() if g is not None]
            bad = [n for n in nums if n != str(EXPECTED_TAINT)]
            if bad:
                issues.append((base, f"taint count(s) {bad} != {EXPECTED_TAINT} in count phrasing: "
                                     f"…{txt[max(0,m.start()-20):m.end()+20]}…"))
        # (c') a "NN -> NN" taint delta, but only on a line that also mentions taint/toll/такса —
        #      so chapter ranges like "00→56" or "chs. 39→42" are not mistaken for taint counts.
        DELTA = re.compile(r"\b(\d{2,3})(?!\d)\s*(?:->|→|-->)\s*(\d{2,3})(?!\d)\b")
        TAINT_WORD = re.compile(r"(?i)\b(?:taint|таинт|toll|такса|declarations|деклараци)")
        for m in DELTA.finditer(txt):
            ls = txt.rfind("\n", 0, m.start()) + 1
            le = txt.find("\n", m.end());  le = len(txt) if le < 0 else le
            if TAINT_WORD.search(txt[ls:le]) and any(g != str(EXPECTED_TAINT) for g in m.groups()):
                issues.append((base, f"taint delta {m.group(1)}→{m.group(2)} != {EXPECTED_TAINT} "
                                     f"(restate as 16): …{txt[max(0,m.start()-20):m.end()+20]}…"))
    return issues

CONJ = r"(Риман|Riemann|Коллатц|Collatz|близнец|twin|Ходж|Hodge|Бёрч|Birch|Свиннертон|Swinnerton|Янг|Yang|Навье|Navier|P/NP|P\\?/NP)"
CLAIM = r"(доказал|доказана|доказано|решена|решено|solved|proven|proof of|мы доказали)"
DISCLAIM = r"(не\s|not\s|без\s|условно|редукц|reduction|decree|декрет|sorry|🟡|🔴)"
def overclaim_check(files):
    hits = []
    cre = re.compile(CLAIM, re.I); jre = re.compile(CONJ, re.I); dre = re.compile(DISCLAIM, re.I)
    for path in files:
        for i, line in enumerate(open(path, encoding="utf-8"), 1):
            if cre.search(line) and jre.search(line) and not dre.search(line):
                hits.append((os.path.basename(path), i, line.strip()[:140]))
    return hits

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default=os.environ.get("AUDIT_DATA", "."))
    ap.add_argument("--root", default=".")
    args = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8")
    full, last, decls, src = load_oracles(args.data, args.root)
    files_set = repo_files(args.root)
    files = sorted(glob.glob(os.path.join(args.root, "prose", "*.md"))) + \
            [os.path.join(args.root, "README.md"),
             os.path.join(args.root, "README.ru.md")]
    files = [f for f in files if os.path.exists(f)]
    cited, phantoms, missing_files, mislabels, ambiguous = audit(files, full, last, decls, src, files_set)
    counters = counter_check(files)
    overclaims = overclaim_check(files)

    print(f"Cited identifier-like tokens: {len(cited)} distinct")
    print(f"Oracle: {len(full)} env names, {len(src)} source identifiers, {len(decls)} decl last-components")
    print(f"\n[1] PHANTOM names (decl-shaped, not in env or source): {len(phantoms)}")
    for t, f, ln in phantoms:
        print(f"    {t}   ({f}:{ln})")
    print(f"\n[1b] file references not in repo (informational — external source docs etc.): {len(missing_files)}")
    for t, f, ln in missing_files:
        print(f"    {t}   ({f}:{ln})")
    print(f"\n[2] LABEL mismatches (badge adjacent, unambiguous): {len(mislabels)}")
    for kind, t, f, ln in mislabels:
        print(f"    {kind}: {t}   ({f}:{ln})")
    print(f"\n[2b] LABEL ambiguous (same last-name in >1 namespace): {len(ambiguous)}")
    for kind, t, f, ln in ambiguous:
        print(f"    {kind}: {t}   ({f}:{ln})")
    print(f"\n[3] COUNTER issues: {len(counters)}")
    for f, msg in counters:
        print(f"    {f}: {msg}")
    print(f"\n[4] OVERCLAIM candidates (informational, verify context): {len(overclaims)}")
    for f, ln, s in overclaims:
        print(f"    {f}:{ln}: {s}")

    # hard gate = honesty-critical checks; missing-file refs + overclaims are informational
    clean = not phantoms and not mislabels and not counters
    print(f"\n=== {'CLEAN' if clean else 'ISSUES FOUND'} "
          f"(missing-file refs & overclaims are informational) ===")
    return 0 if clean else 1

if __name__ == "__main__":
    sys.exit(main())
