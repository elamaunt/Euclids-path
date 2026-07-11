#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Emit the twin-chain completeness census data for `Step00TwinChainCensus.lean`.

Self-contained pipeline (no external input files):

  1. sieve the wings `6m -+ 1` for every center `m in [1, 10^4]` (wings <= 60001);
  2. classify every center: TWIN (both wings prime) / KILLED (some clock
     `q in {5, 7, 11, 13}` divides a wing with `q <` wing) / SURVIVOR (needs one
     explicit factor witness `(m, p, side)`, `side = true` for the `6m - 1` wing);
  3. RE-VERIFY every emitted literal with an INDEPENDENT primality test (pure trial
     division, no sieve reuse): twins by primality of both wings, witnesses by the
     actual division `1 < p < w`, `w % p == 0` (and `p` prime, a stronger check than
     the Lean side needs);
  4. SIMULATE the Lean checker `twinSegB` exactly (same branch order: twin head,
     then witness head, then clock kill; final full consumption of both lists) on
     every chunk before anything is written — a data error must die here, not as a
     kernel timeout (the `gen_paths_lean.py` precedent);
  5. print the census statistics and emit the Lean chunk section.

Usage:
    python tools/gen_twinchain_lean.py                 # stats only (verification always runs)
    python tools/gen_twinchain_lean.py --emit          # print the generated Lean data section
    python tools/gen_twinchain_lean.py --inject PATH   # splice the section between the markers in PATH
    python tools/gen_twinchain_lean.py --calib PATH    # write the standalone chunk-5 calibration file
"""
import math
import sys

N = 10_000                      # census range: centers m in [1, N]
CHUNK = 1_000                   # centers per kernel chunk (frozen after calibration)
QS = [5, 7, 11, 13]             # the clock list (B = 13)
WING_MAX = 6 * N + 1            # largest wing = 60001
WIDTH = 98
MARK_START = "-- GENERATED DATA START (tools/gen_twinchain_lean.py, chunk %d)" % CHUNK
MARK_END = "-- GENERATED DATA END"
CALIB_CHUNK = 5                 # the heaviest chunk (most twin primality ladders x wing size)


# ----------------------------------------------------------------------------- primality


def sieve(limit: int) -> bytearray:
    pr = bytearray([1]) * (limit + 1)
    pr[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(limit) + 1):
        if pr[i]:
            pr[i * i:: i] = bytearray(len(pr[i * i:: i]))
    return pr


def is_prime_td(n: int) -> bool:
    """Independent re-verification primality: pure trial division, no sieve reuse."""
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def spf(n: int) -> int:
    """Smallest prime factor of a composite n (trial division)."""
    d = 2
    while d * d <= n:
        if n % d == 0:
            return d
        d += 1
    return n


# ----------------------------------------------------------------------------- classification


def kill_b(m: int) -> bool:
    """EXACT mirror of the Lean `killB [5,7,11,13] m` (q < wing guard, no primality)."""
    a, b = 6 * m - 1, 6 * m + 1
    return any((a % q == 0 and q < a) or (b % q == 0 and q < b) for q in QS)


def classify(pr: bytearray):
    """-> (twins, wits, killed): twins = [m..], wits = [(m, p, side)..], killed = [m..]."""
    twins, wits, killed = [], [], []
    for m in range(1, N + 1):
        a, b = 6 * m - 1, 6 * m + 1
        if pr[a] and pr[b]:
            twins.append(m)
        elif kill_b(m):
            killed.append(m)
        else:
            # survivor: at least one wing composite, no clock divides either wing
            cand = []
            if not pr[a]:
                cand.append((spf(a), True))       # side true = 6m - 1 wing
            if not pr[b]:
                cand.append((spf(b), False))      # side false = 6m + 1 wing
            assert cand, m
            p, side = min(cand)                    # smallest factor available
            wits.append((m, p, side))
    return twins, wits, killed


# ----------------------------------------------------------------------------- re-verification


def verify(twins, wits, killed) -> None:
    """Independent arithmetic re-verification of EVERY emitted literal."""
    # (a) partition: every center accounted for exactly once
    seen = sorted(twins + [m for (m, _, _) in wits] + killed)
    assert seen == list(range(1, N + 1)), "partition broken"
    # (b) twins: both wings prime by INDEPENDENT trial division
    for m in twins:
        assert is_prime_td(6 * m - 1) and is_prime_td(6 * m + 1), ("twin", m)
    # (c) witnesses: actual division, nontriviality, primality of p, wing really composite,
    #     and the center genuinely survives the clock kill without being a twin
    for (m, p, side) in wits:
        w = 6 * m - 1 if side else 6 * m + 1
        assert 1 < p < w and w % p == 0, ("wit-div", m, p, side)
        assert is_prime_td(p), ("wit-p-prime", m, p)
        assert not is_prime_td(w), ("wit-wing-composite", m, p, side)
        assert not kill_b(m), ("wit-not-killed", m)
        assert not (is_prime_td(6 * m - 1) and is_prime_td(6 * m + 1)), ("wit-not-twin", m)
        assert p not in QS, ("wit-clock-leak", m, p)
    # (d) killed: the kill is real AND kills a genuinely composite wing (q < wing, q > 1)
    for m in killed:
        assert kill_b(m), ("kill", m)
        assert not (is_prime_td(6 * m - 1) and is_prime_td(6 * m + 1)), ("kill-not-twin", m)


def twin_b(m: int) -> bool:
    """Mirror of Lean `twinB` (primeB is complete on odd wings >= 5)."""
    a, b = 6 * m - 1, 6 * m + 1
    assert a % 2 == 1 and b % 2 == 1 and a >= 5
    return m >= 1 and is_prime_td(a) and is_prime_td(b)


def wit_b(m: int, p: int, side: bool) -> bool:
    w = 6 * m - 1 if side else 6 * m + 1
    return 1 < p and p < w and w % p == 0


def sim_twin_seg(m0: int, n: int, twins, wits) -> bool:
    """EXACT mirror of the Lean `twinSegB QS m0 n twins wits` (branch order included)."""
    twins, wits = list(twins), list(wits)
    for i in range(n):
        m = m0 + i
        if twins and twins[0] == m:
            if not twin_b(m):
                return False
            twins.pop(0)
        elif wits and wits[0][0] == m:
            mw, p, side = wits.pop(0)
            if not wit_b(m, p, side):
                return False
        else:
            if not kill_b(m):
                return False
    return not twins and not wits


# ----------------------------------------------------------------------------- stats


def chunk_slices(twins, wits):
    """Per-chunk (lo, twins_i, wits_i) with chunk i covering [1000(i-1)+1, 1000i]."""
    out = []
    for i in range(N // CHUNK):
        lo, hi = CHUNK * i + 1, CHUNK * (i + 1)
        tw = [m for m in twins if lo <= m <= hi]
        wt = [w for w in wits if lo <= w[0] <= hi]
        out.append((lo, tw, wt))
    return out


def ladder_ops(w: int) -> int:
    """Elementary kernel ops of one primeB ladder on wing w (mod+mul+cmp per rung)."""
    return 3 * ((math.isqrt(w) - 1) // 2 + 2) + 3


def kill_ops(m: int) -> int:
    a, b = 6 * m - 1, 6 * m + 1
    ops = 0
    for q in QS:
        ops += 4
        if (a % q == 0 and q < a) or (b % q == 0 and q < b):
            break
    return ops + 2


def stats(twins, wits, killed) -> None:
    print("centers [1, %d]: %d twins, %d witnesses, %d clock-killed"
          % (N, len(twins), len(wits), len(killed)))
    print("first twin: %d   last twin: %d" % (twins[0], twins[-1]))
    gaps = [(twins[i + 1] - twins[i], twins[i]) for i in range(len(twins) - 1)]
    g, at = max(gaps)
    print("max twin-center gap: %d (after m = %d, next twin %d)" % (g, at, at + g))
    print("max witness factor: %d" % max(p for (_, p, _) in wits))
    kill_scan = []
    for m in killed:
        a, b = 6 * m - 1, 6 * m + 1
        for j, q in enumerate(QS):
            if (a % q == 0 and q < a) or (b % q == 0 and q < b):
                kill_scan.append(j + 1)
                break
    print("kill scan average: %.3f clocks (over %d killed)"
          % (sum(kill_scan) / len(kill_scan), len(killed)))
    print("chunk plan (%d chunks x %d centers):" % (N // CHUNK, CHUNK))
    for i, (lo, tw, wt) in enumerate(chunk_slices(twins, wits), 1):
        ops = sum(ladder_ops(6 * m - 1) + ladder_ops(6 * m + 1) + 4 for m in tw)
        ops += sum(7 for _ in wt)
        ops += sum(kill_ops(m) for m in range(lo, lo + CHUNK)
                   if m not in set(tw) and m not in set(w[0] for w in wt))
        print("  chunk %2d: m in [%4d, %4d]  %3d twins  %3d witnesses  ~%5.1fk kernel ops"
              % (i, lo, lo + CHUNK - 1, len(tw), len(wt), ops / 1000.0))


# ----------------------------------------------------------------------------- emission


def wrap(prefix: str, items, close: str, indent: str, sep: str = ", ") -> str:
    lines, cur = [], prefix
    for i, it in enumerate(items):
        tok = it + (sep if i + 1 < len(items) else close)
        if len(cur) + len(tok) > WIDTH:
            lines.append(cur.rstrip())
            cur = indent + tok
        else:
            cur += tok
    lines.append(cur.rstrip())
    return "\n".join(lines)


def render_wit(w) -> str:
    m, p, side = w
    return "(%d, %d, %s)" % (m, p, "true" if side else "false")


def emit_section(twins, wits) -> str:
    sl = chunk_slices(twins, wits)
    out = [MARK_START]
    for i, (lo, tw, wt) in enumerate(sl, 1):
        out.append(wrap("private def tc_%d : List ℕ := [" % i,
                        [str(m) for m in tw], "]", "  "))
        out.append(wrap("private def wc_%d : List (ℕ × ℕ × Bool) := [" % i,
                        [render_wit(w) for w in wt], "]", "  "))
    for i, (lo, tw, wt) in enumerate(sl, 1):
        out.append("")
        out.append("set_option maxRecDepth 100000 in")
        out.append("/-- Census chunk %d: centers `[%d, %d]` — %d twins, %d factor witnesses,"
                   % (i, lo, lo + CHUNK - 1, len(tw), len(wt)))
        out.append("    clock kill for the remaining %d centers (`decide +kernel`). -/"
                   % (CHUNK - len(tw) - len(wt)))
        out.append("theorem twinSeg_chunk_%d : twinSegB clock13 %d %d tc_%d wc_%d = true := by"
                   % (i, lo, CHUNK, i, i))
        out.append("  decide +kernel")
    out.append("")
    out.append("/-- All %d twin centers on `[1, %d]` in increasing order — the chunk lists" % (len(twins), N))
    out.append("    concatenated (parenthesised to match the right-to-left glue fold). -/")
    names = ["tc_%d" % i for i in range(1, len(sl) + 1)]
    tail = names[-1]
    for nm in reversed(names[:-1]):
        tail = "%s ++ (%s)" % (nm, tail)
    # explicit right-associated parenthesisation
    out.append("def twinList10k : List ℕ :=")
    out.append(wrap("  ", [tail], "", "    ", sep=""))
    out.append(MARK_END)
    return "\n".join(out)


CHECKER_DEFS = """/-- Factor witness check at center `m`: `(p, side)` certifies compositeness of one wing,
    `side = true` for the `6m - 1` wing, `side = false` for `6m + 1`.  A nontrivial
    divisor `1 < p <` wing kills that wing's primality — no primality of `p` needed. -/
def witB (m : ℕ) : ℕ × Bool → Bool
  | (p, true) => Nat.blt 1 p && Nat.blt p (6 * m - 1) && ((6 * m - 1) % p == 0)
  | (p, false) => Nat.blt 1 p && Nat.blt p (6 * m + 1) && ((6 * m + 1) % p == 0)

/-- Small-clock kill: some `q` in the clock list divides a wing with `q <` wing.
    The guard `Nat.blt q` wing keeps the divisor nontrivial from above; nontriviality
    from below (`2 ≤ q`) is a side condition on the clock list, not re-checked here. -/
def killB (qs : List ℕ) (m : ℕ) : Bool :=
  qs.any fun q =>
    ((6 * m - 1) % q == 0 && Nat.blt q (6 * m - 1)) ||
      ((6 * m + 1) % q == 0 && Nat.blt q (6 * m + 1))

/-- The fused two-list census walk: `twinSegB qs m n twins wits` visits the `n` centers
    `m, m + 1, …, m + n - 1` in order, consuming the sorted twin list and the sorted
    witness list.  Twin head match ⟹ `twinB`; otherwise witness head match ⟹ `witB`;
    otherwise the clock kill must fire.  Terminal case: BOTH lists fully consumed.
    Structural recursion on the fuel `n` with inner list matches (the `chainB` shape —
    the kernel unfolds it literally). -/
def twinSegB (qs : List ℕ) : ℕ → ℕ → List ℕ → List (ℕ × ℕ × Bool) → Bool
  | _, 0, twins, wits => twins.isEmpty && wits.isEmpty
  | m, n + 1, twins, wits =>
    match twins with
    | t :: ts =>
      cond (t == m)
        (twinB m && twinSegB qs (m + 1) n ts wits)
        (match wits with
          | (mw, p, s) :: ws =>
            cond (mw == m)
              (witB m (p, s) && twinSegB qs (m + 1) n (t :: ts) ws)
              (killB qs m && twinSegB qs (m + 1) n (t :: ts) ((mw, p, s) :: ws))
          | [] => killB qs m && twinSegB qs (m + 1) n (t :: ts) [])
    | [] =>
      match wits with
      | (mw, p, s) :: ws =>
        cond (mw == m)
          (witB m (p, s) && twinSegB qs (m + 1) n [] ws)
          (killB qs m && twinSegB qs (m + 1) n [] ((mw, p, s) :: ws))
      | [] => killB qs m && twinSegB qs (m + 1) n [] []
"""


def emit_calib(twins, wits, path: str) -> None:
    lo, tw, wt = chunk_slices(twins, wits)[CALIB_CHUNK - 1]
    body = [
        "import EuclidsPath.Engine.Step00GraveDepthKernel",
        "",
        "set_option autoImplicit false",
        "",
        "/-! Calibration probe for `Step00TwinChainCensus`: chunk %d standalone" % CALIB_CHUNK,
        "    (the heaviest chunk of the frozen plan).  NOT part of the repo build. -/",
        "",
        "namespace EuclidsPath",
        "namespace TwinChainCensusCalib",
        "",
        "open EuclidsPath.GraveDepthKernel",
        "",
        CHECKER_DEFS,
        wrap("private def calib_tc : List ℕ := [", [str(m) for m in tw], "]", "  "),
        wrap("private def calib_wc : List (ℕ × ℕ × Bool) := [",
             [render_wit(w) for w in wt], "]", "  "),
        "",
        "set_option maxRecDepth 100000 in",
        "theorem twinSeg_chunk_%d_calib :" % CALIB_CHUNK,
        "    twinSegB [5, 7, 11, 13] %d %d calib_tc calib_wc = true := by" % (lo, CHUNK),
        "  decide +kernel",
        "",
        "end TwinChainCensusCalib",
        "end EuclidsPath",
        "",
    ]
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(body))
    print("calibration file written: %s (chunk %d, %d twins, %d witnesses)"
          % (path, CALIB_CHUNK, len(tw), len(wt)))


def inject(path: str, section: str) -> None:
    with open(path, encoding="utf-8") as f:
        src = f.read()
    i, j = src.index(MARK_START), src.index(MARK_END) + len(MARK_END)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(src[:i] + section + src[j:])
    print("injected generated section into %s" % path)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    pr = sieve(WING_MAX)
    twins, wits, killed = classify(pr)
    verify(twins, wits, killed)
    # exact checker simulation per chunk + the full range in one run
    for i, (lo, tw, wt) in enumerate(chunk_slices(twins, wits), 1):
        assert sim_twin_seg(lo, CHUNK, tw, wt), ("sim-chunk", i)
    assert sim_twin_seg(1, N, twins, wits), "sim-full"
    # negative controls: the simulator must actually reject corrupted data
    assert not sim_twin_seg(1, CHUNK, [m for m in twins if m <= CHUNK][1:],
                            [w for w in wits if w[0] <= CHUNK]), "control-drop-twin"
    assert not sim_twin_seg(1, CHUNK, [m for m in twins if m <= CHUNK] + [999],
                            [w for w in wits if w[0] <= CHUNK]), "control-fake-twin"
    print("verification: OK (partition, trial-division re-check, checker simulation, controls)")
    stats(twins, wits, killed)
    if "--emit" in sys.argv:
        print(emit_section(twins, wits))
    if "--inject" in sys.argv:
        inject(sys.argv[sys.argv.index("--inject") + 1], emit_section(twins, wits))
    if "--calib" in sys.argv:
        emit_calib(twins, wits, sys.argv[sys.argv.index("--calib") + 1])


if __name__ == "__main__":
    main()
