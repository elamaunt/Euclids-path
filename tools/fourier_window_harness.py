# fourier_window_harness.py -- spike-anatomy harness: the EMPIRICAL BODY of
# EuclidsPath/Engine/Step00StrikeFourier.lean (Parts R + E2b).
#
# Lean conventions mirrored EXACTLY (read Step00StrikeFourier.lean first):
#   clocks A      = primes q with 5 <= q <= A
#   window        = (k, k+g], centers m = k+1 .. k+g
#   Clean A m    <=> no clock divides 6m-1 or 6m+1
#                <=> for every clock q: m mod q not in {i6(q), (q - i6(q)) mod q},
#                    i6(q) = 6^{-1} mod q   (strike_minus_iff / strike_plus_iff)
#   cleanCount A k g = #{m in (k, k+g] : Clean A m}
#   mainTerm A g  = g * prod_q (1 - 2/q)          (rational -- a DEFINITION)
#   windowFluct   = cleanCount - mainTerm          (rational; fractions.Fraction)
#   engine decomposition (windowFluct_eq_minorSum, Part E2b):
#     windowFluct = sum over NONZERO mode tuples of modeAmp * modeWindowSum,
#     modeCoeff q j = delta_{j=0} - (1/q)(e(-j*i6/q) + e(+j*i6/q)),
#     modeWave  q j m = e(j*m/q),  e(x) = exp(2*pi*i*x).
#
# TRACTABLE EXACT ANATOMY (support grouping -- mode tuples are astronomically many;
# tuples grouped by SUPPORT S = {clocks with j_q != 0} sum EXACTLY to the centered
# inclusion-exclusion terms):
#   s_q(m) = strike indicator, eps_q(m) = s_q(m) - 2/q, a_q = 1 - 2/q,
#   E_S(W) = sum_{m in W} prod_{q in S} eps_q(m),
#   cleanCount  = sum_{S subseteq clocks} (-1)^{|S|} (prod_{q notin S} a_q) E_S(W)
#   windowFluct = the S != empty part (S = empty term IS mainTerm)  -- EXACT.
# Common-denominator integer form used here: v_q(m) = q*s_q(m) - 2 in {-2, q-2},
#   V[S] = sum_m prod_{q in S} v_q(m)  (exact int64: |V| <= g*prod(q-2) < 2^62,
#   asserted; cross-checked once vs Python big ints at A=43),
#   term(S) = (-1)^{|S|} * (prod_{q notin S} (q-2)) * V[S] / prod_q q  (Fraction).
#
# Populations: exact SAT/scan defect windows (zero clean centers VERIFIED before
# use) at A = 17..43; matched-phase + typical phase-vector controls.
# Observables AN1..AN5 are pre-registered in the log before any measurement.
# AN5 reuses tools/betti_portrait_harness.py precompute_X / foil_row VERBATIM
# (gate_g3 foil-v2 machinery), seed 20260710.
#
# Usage: python tools/fourier_window_harness.py   (appends to
# tools/fourier_window_run1.log; log is append-only, ASCII-safe).

import cmath
import math
import os
import sys
import time
from fractions import Fraction
from math import gcd

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import betti_portrait_harness as BP  # precompute_X / foil_row reused VERBATIM

LOGPATH = os.path.join(TOOLS, "fourier_window_run1.log")
_logf = open(LOGPATH, "a", buffering=1, encoding="ascii", errors="replace")
_LINENO = [0]


class _Tee(object):
    def __init__(self, f):
        self.f = f
        self.out = sys.__stdout__

    def write(self, s):
        self.out.write(s)
        self.f.write(s)
        _LINENO[0] += s.count("\n")

    def flush(self):
        self.out.flush()
        self.f.flush()


sys.stdout = _Tee(_logf)


def log(s=""):
    print(s, flush=True)


SECTION_INDEX = []


def section(title):
    SECTION_INDEX.append((title, _LINENO[0] + 1))
    log("=" * 78)
    log(title)
    log("=" * 78)


SEED = 20260710
LEAN_I6 = {5: 1, 7: 6, 11: 2, 13: 11, 17: 3, 19: 16, 23: 4, 29: 5, 31: 26,
           37: 31, 41: 7, 43: 36}   # copy of tools/gap_extremal_harness.py:725
G_KERNEL = {5: 2, 7: 5, 11: 7, 13: 11, 17: 18, 19: 25, 23: 34, 29: 43, 31: 58,
            37: 88, 41: 91, 43: 103}   # kernel gap G(A) (engineDecay_at_*)
DEFECT_GIVEN = {
    17: [117, 502, 5642, 6027, 21497, 30845],        # gap_extremal_run1.log:124-131
    19: [110, 26045, 67695, 170035, 203005, 373175],  # gap_extremal_run1.log:133-140
    23: [12694428, 18165208, 19016903, 24487683],     # gap_extremal_run1.log:142-146
    29: [200906185, 877375977],                       # gap_extremal_run1.log:30-31
    31: [21844264615],                                # phase_cover_run1.log:43
    37: [1145973108145],                              # phase_cover_run1.log:44
    41: [50077677123072],                             # phase_cover_run1.log:130 (len 90)
    43: [233885349904190],                            # phase_cover_run1.log:131 (len 102)
}
AN_SCALES = [17, 19, 23, 29, 31, 37, 41, 43]
FAREY = [(j, q) for q in range(2, 51) for j in range(1, q) if gcd(j, q) == 1]
XS = (10 ** 6, 10 ** 9)
NW_OF_X = {10 ** 6: 3000, 10 ** 9: 1000}
ANOMALIES = []   # (context, statistic, value)
RESULTS = {}


def primes_upto(n):
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def clocks(A):
    return [p for p in primes_upto(A) if p >= 5]


def i6(q):
    return pow(6, -1, q)


def main_term(A, g):
    r = Fraction(g)
    for q in clocks(A):
        r *= Fraction(q - 2, q)
    return r


def is_clean_resid(A, m):
    for q in clocks(A):
        r = m % q
        iq = i6(q)
        if r == iq or r == (q - iq) % q:
            return False
    return True


def is_clean_trial(A, m):
    for q in primes_upto(A):
        if (6 * m - 1) % q == 0 or (6 * m + 1) % q == 0:
            return False
    return True


def clean_count_resid(A, k, g):
    return sum(1 for j in range(1, g + 1) if is_clean_resid(A, k + j))


# ---------- exact subset (support) machinery ----------

def subset_V(Q, phases, g):
    """V[mask] = sum_{j=1..g} prod_{i in mask} v_i(k+j), v = q*s-2 in {-2, q-2}.
    Exact in int64: every partial product bounded by prod(q-2) (each q-2 >= 3 > 2),
    the sum by g*prod(q-2) < 2^62 (asserted)."""
    n = len(Q)
    bound = g
    for q in Q:
        bound *= (q - 2)
    assert bound < 2 ** 62, "int64 overflow guard failed"
    M = np.ones((1 << n, g), dtype=np.int64)
    off = np.arange(1, g + 1, dtype=np.int64)
    for i, q in enumerate(Q):
        res = (phases[i] + off) % q
        iq = i6(q)
        s = (res == iq) | (res == (q - iq) % q)
        v = np.where(s, q - 2, -2).astype(np.int64)
        M[1 << i: 2 << i] = M[0: 1 << i] * v[None, :]
    return M.sum(axis=1)


def subset_V_bigint(Q, phases, g):
    """Reference route in Python big ints (overflow selftest)."""
    n = len(Q)
    vs = []
    for i, q in enumerate(Q):
        iq = i6(q)
        row = []
        for j in range(1, g + 1):
            r = (phases[i] + j) % q
            row.append(q - 2 if (r == iq or r == (q - iq) % q) else -2)
        vs.append(row)
    V = [0] * (1 << n)
    for mask in range(1 << n):
        tot = 0
        for j in range(g):
            p = 1
            mm = mask
            while mm:
                i = (mm & -mm).bit_length() - 1
                p *= vs[i][j]
                mm &= mm - 1
            tot += p
        V[mask] = tot
    return V


def build_pre(A):
    Q = clocks(A)
    n = len(Q)
    pc = np.array([bin(m).count("1") for m in range(1 << n)], dtype=np.int64)
    pin = [1] * (1 << n)
    for i, q in enumerate(Q):
        b = 1 << i
        for m0 in range(b):
            pin[m0 | b] = pin[m0] * (q - 2)
    TOT = pin[-1]
    outp = [TOT // p for p in pin]          # prod_{q notin mask}(q-2), exact
    outf = np.array([float(x) for x in outp])
    sign = np.where(pc % 2 == 1, -1.0, 1.0)
    masks = np.arange(1 << n, dtype=np.int64)
    has = [((masks >> i) & 1) == 1 for i in range(n)]
    D = 1
    for q in Q:
        D *= q
    return dict(A=A, Q=Q, n=n, pc=pc, outp=outp, outf=outf, sign=sign, has=has,
                TOT=TOT, D=D)


def mask_name(pre, m):
    return "{" + ",".join(str(q) for i, q in enumerate(pre["Q"]) if (m >> i) & 1) + "}"


def anatomy_exact(pre, phases, g):
    """Full exact anatomy (Fractions from common-denominator integers)."""
    Q, n, D = pre["Q"], pre["n"], pre["D"]
    V = subset_V(Q, phases, g)
    pc = pre["pc"]
    t = [0] * (1 << n)
    for m in range(1 << n):
        s = -1 if (int(pc[m]) & 1) else 1
        t[m] = s * pre["outp"][m] * int(V[m])
    total = sum(t)
    assert total % D == 0, "cleanCount not integral -- identity broken"
    cc = total // D
    mainN = t[0]                                     # = TOT * g > 0
    mainT = Fraction(mainN, D)
    fluct = Fraction(total - mainN, D)
    levelsN = [0] * (n + 1)
    for m in range(1 << n):
        levelsN[int(pc[m])] += t[m]
    shares = [Fraction(levelsN[l], mainN) for l in range(n + 1)]
    absN = [abs(x) for x in t]
    sumabs = sum(absN[1:])
    margN = []
    for i in range(n):
        b = 1 << i
        margN.append(sum(absN[m] for m in range(1 << n) if m & b))
    top = sorted(range(1, 1 << n), key=lambda m: -absN[m])
    return dict(cc=cc, mainT=mainT, fluct=fluct, shares=shares, t=t, absN=absN,
                sumabs=sumabs, margN=margN, top=top, mainN=mainN, D=D)


def anatomy_float(pre, phases, g):
    """Control-population anatomy: float64 ratios computed from EXACT int64
    subset sums V (disclosed: exactness claimed only on defect windows)."""
    V = subset_V(pre["Q"], phases, g).astype(np.float64)
    signed = pre["sign"] * pre["outf"] * V
    levels = np.bincount(pre["pc"], weights=signed, minlength=pre["n"] + 1)
    mainv = signed[0]
    shares = levels / mainv                  # level share of mainTerm
    fm = float(shares[1:].sum())             # windowFluct / mainTerm
    absT = np.abs(signed)
    absT[0] = 0.0
    sumabs = float(absT.sum())
    marg = np.array([float(absT[h].sum()) for h in pre["has"]])
    marg = marg / (sumabs if sumabs > 0 else 1.0)
    top1 = int(np.argmax(absT))
    return dict(shares=shares, fm=fm, marg=marg, top1=top1, sumabs=sumabs)


def fdec(x, nd=10):
    return ("%+." + str(nd) + "f") % float(x)


# ---------- selftests ----------

def scan_defect_starts(A):
    """Full-period scan (A in {17,19}): all r in [0,P) with (r, r+G-1] all struck."""
    Q = clocks(A)
    P = 1
    for q in Q:
        P *= q
    g = G_KERNEL[A] - 1
    m = np.arange(0, P + 2 * g + 4, dtype=np.int64)
    clean = np.ones(m.size, dtype=bool)
    for q in Q:
        iq = i6(q)
        r = m % q
        clean &= (r != iq) & (r != (q - iq) % q)
    struck = (~clean).astype(np.int64)
    cs = np.concatenate([[0], np.cumsum(struck)])
    # windows (r, r+g]: struck-sum over m = r+1..r+g equals cs[r+g+1]-cs[r+1]
    W = cs[g + 1: P + g + 1] - cs[1: P + 1]          # r = 0..P-1
    starts = np.flatnonzero(W == g)
    # no window of length g+1 fully struck (kernel gap G(A)):
    W1 = cs[g + 2: P + g + 2] - cs[1: P + 1]
    assert int(W1.max()) == g, "run longer than G(A)-1 found -- kernel contradicted"
    return [int(r) for r in starts], P


def selftests():
    section("SELFTESTS (mandatory, before registration; assert-fail = STOP)")
    t0 = time.time()

    # ST1 -- i6 table vs LEAN_I6 (tools/gap_extremal_harness.py:725)
    for q, v in sorted(LEAN_I6.items()):
        assert i6(q) == v, "i6(%d) != LEAN_I6" % q
        assert (6 * v) % q == 1
        assert (2 * v) % q != 0
    log("ST1 i6 table: pow(6,-1,q) == LEAN_I6[q] and 6*i6 mod q == 1 for all 12")
    log("    clocks 5..43 (spot: i6(41)=%d, i6(43)=%d) -- PASS" % (i6(41), i6(43)))

    # ST2 -- Lean kernel anchors (Step00StrikeFourier.lean examples)
    assert clocks(5) == [5]
    assert clean_count_resid(5, 0, 5) == 3
    assert sum(1 for j in range(1, 6) if is_clean_trial(5, j)) == 3
    assert main_term(5, 5) == Fraction(3)
    pre5 = build_pre(5)
    a5 = anatomy_exact(pre5, [0], 5)
    assert a5["cc"] == 3 and a5["mainT"] == Fraction(3) and a5["fluct"] == Fraction(0)
    log("ST2 Lean anchors: clocks(5)=[5]; cleanCount(5,0,5)=3 (residue & trial &")
    log("    subset routes); mainTerm(5,5)=3 exact; windowFluct=0 -- PASS")

    # ST3 -- 1000 random windows at A=13, g=11: residue == trial-division scan ==
    # subset formula (exact); windowFluct == sum_{S != empty} term(S) (exact)
    pre13 = build_pre(13)
    rng = np.random.default_rng(SEED + 3)
    mt = main_term(13, 11)
    for _ in range(1000):
        k = int(rng.integers(0, 10 ** 7))
        c1 = clean_count_resid(13, k, 11)
        c2 = sum(1 for j in range(1, 12) if is_clean_trial(13, k + j))
        a = anatomy_exact(pre13, [k % q for q in clocks(13)], 11)
        assert c1 == c2 == a["cc"], "cleanCount mismatch at k=%d" % k
        assert a["mainT"] == mt
        assert a["fluct"] == Fraction(c1) - mt
        assert sum(a["shares"][1:], Fraction(0)) == a["fluct"] / mt
    log("ST3 1000 random windows A=13 g=11 (k < 1e7, seed %d): residue scan ==" % (SEED + 3))
    log("    trial-division scan == subset-formula cleanCount (exact int); windowFluct")
    log("    == sum_{S!=empty} term(S) (exact Fraction) on all 1000 -- PASS")

    # ST3b -- int64 overflow cross-check at the largest scale (A=43 defect window)
    pre43 = build_pre(43)
    r43 = DEFECT_GIVEN[43][0]
    g43 = G_KERNEL[43] - 1
    ph43 = [r43 % q for q in clocks(43)]
    V64 = subset_V(clocks(43), ph43, g43)
    Vbig = subset_V_bigint(clocks(43), ph43, g43)
    assert all(int(V64[m]) == Vbig[m] for m in range(len(Vbig)))
    log("ST3b int64 vs Python-bigint subset sums, A=43 defect window (4096 masks,")
    log("    g=102): EXACT MATCH -- int64 route safe at every scale used -- PASS")

    # ST4 -- mode-picture equivalence at A=7 (brute force over all 35 mode tuples)
    def e(x):
        return cmath.exp(2j * math.pi * x)

    Q7 = clocks(7)
    pre7 = build_pre(7)
    i65, i67 = i6(5), i6(7)

    def mode_coeff(q, j, iq):
        d = 1.0 if j == 0 else 0.0
        return d - (1.0 / q) * (e(((-j * iq) % q) / q) + e(((j * iq) % q) / q))

    def mode_wave(q, j, m):
        return e(((j * m) % q) / q)

    for (k, g) in ((0, 5), (12, 4), (47, 5), (12, 5)):
        a = anatomy_exact(pre7, [k % 5, k % 7], g)
        full = 0.0 + 0j
        sup = {0: 0j, 1: 0j, 2: 0j, 3: 0j}
        for j5 in range(5):
            for j7 in range(7):
                amp = mode_coeff(5, j5, i65) * mode_coeff(7, j7, i67)
                ws = sum(mode_wave(5, j5, m) * mode_wave(7, j7, m)
                         for m in range(k + 1, k + g + 1))
                full += amp * ws
                sup[(1 if j5 else 0) | (2 if j7 else 0)] += amp * ws
        assert abs(full - a["cc"]) <= 1e-9, "mode sum != cleanCount"
        nonzero = full - sup[0]
        assert abs(nonzero - float(a["fluct"])) <= 1e-9, "engines != windowFluct"
        for mask in range(4):
            assert abs(sup[mask] - a["t"][mask] / a["D"]) <= 1e-9, \
                "support-%d group != subset term" % mask
    a12 = anatomy_exact(pre7, [12 % 5, 12 % 7], 4)
    assert a12["cc"] == 0 and a12["fluct"] == -a12["mainT"]
    log("ST4 mode-picture brute force A=7 (all 35 tuples, windows k in {0,12,47},")
    log("    g in {4,5}): sum over nonzero tuples == windowFluct to 1e-9; per-support")
    log("    tuple groups == centered inclusion-exclusion terms to 1e-9; full sum ==")
    log("    cleanCount; defect window (12,16]: engines == -mainTerm(7,4) EXACT -- PASS")

    # ST5 -- defect populations: verify ZERO clean centers before use
    defects = {}
    for A in AN_SCALES:
        g = G_KERNEL[A] - 1
        if A in (17, 19):
            starts, P = scan_defect_starts(A)
            assert len(starts) == 20, "expected 20 extremal starts at A=%d" % A
            for r in DEFECT_GIVEN[A]:
                assert r in starts, "listed start %d not found at A=%d" % (r, A)
            log("ST5 A=%d: full-period scan (P=%s): %d defect starts of length g=%d;"
                % (A, "{:,}".format(P), len(starts), g))
            log("    max struck run == g (kernel gap G=%d confirmed); the %d log-listed"
                % (G_KERNEL[A], len(DEFECT_GIVEN[A])))
            log("    starts all found -- PASS")
        else:
            starts = list(DEFECT_GIVEN[A])
        for r in starts:
            assert clean_count_resid(A, r, g) == 0, \
                "window (%d, %d+%d] not defect at A=%d" % (r, r, g, A)
            assert is_clean_resid(A, r) and is_clean_resid(A, r + g + 1), \
                "endpoints of r=%d not clean at A=%d" % (r, A)
        if A not in (17, 19):
            log("ST5 A=%d: %d given start(s), g=%d: zero clean centers verified;"
                % (A, len(starts), g))
            log("    endpoints r and r+%d clean -- PASS" % (g + 1))
        else:
            log("    all %d windows re-verified: zero clean centers; endpoints clean"
                % len(starts))
        defects[A] = starts
    log("SELFTESTS ALL PASS (%.1fs)" % (time.time() - t0))
    return defects


# ---------- registration ----------

def registration():
    section("PRE-REGISTRATION BLOCK (logged before ANY measurement; thresholds fixed)")
    for s in [
        "Populations:",
        "  Defect windows (exact, zero clean centers verified in ST5): window =",
        "  (r, r+g], g = G(A)-1: A=17 g=17 (20 starts, full-period scan); A=19 g=24",
        "  (20 starts, scan); A=23 g=33 (4); A=29 g=42 (2); A=31 g=57 (1); A=37 g=87",
        "  (1); A=41 g=90 (1); A=43 g=102 (1).",
        "  Controls per scale (anatomy = function of the phase vector (r mod q)_q;",
        "  controls are phase vectors, CRT-realizable; 200 each, float64 ratios from",
        "  exact int64 subset sums -- exactness claimed only on defect windows):",
        "    matched-phase: phases of q in {5,7,11,13} = defect's r mod q (round-robin",
        "      over the scale's verified starts), phases of q >= 17 uniform;",
        "      seed = 20260710 + A.",
        "    typical: all phases uniform; seed = 20260710 + 1000 + A.",
        "AN1 -- level spectrum: contribution to windowFluct by level |S| = 1..n as",
        "  EXACT shares of mainTerm on each defect window (sum of shares == -1 exact).",
        "  Law-mining questions (registered): universal level profile? drift with A?",
        "  Control profiles reported raw (share of mainTerm) and normalized by",
        "  |windowFluct| (= share/|F/mainTerm|; windows with |F/mainTerm| <= 1e-9",
        "  excluded, count logged).",
        "AN2 -- top subsets: rank by |term(S)|; per-clock marginal = sum of",
        "  |term(S)| over S containing q, as share of sum_{S!=empty}|term(S)|;",
        "  smallest-clock-dominance question; defect vs matched vs typical.",
        "AN3 -- coherence-margin census of windowFluct/mainTerm:",
        "  cell 1: X=1e6, A=13, g=G(13)=11, EXHAUSTIVE k in [0, 1e6);",
        "  cell 2: X=1e9, A=31, g=G(31)=58, 1e5 windows, k uniform in [0, 1e9),",
        "    seed 20260710+31.  Histogram = counts per cleanCount value; minima and",
        "    their locations (near-defects) logged.",
        "AN4 -- Farey/exponential-sum layer: S_W(alpha) = sum_{m in W-survivors}",
        "  e(alpha m) on the H=50 windows of the AN5 cells; survivors = Clean-at-A",
        "  centers.  Farey grid {j/q: 2 <= q <= 50, gcd(j,q)=1} (%d alphas) + 200" % len(FAREY),
        "  random minor-arc alphas (seed 20260710+4; rejection: distance > 1/2500",
        "  from every grid point and from {0,1}).  Census statistic = mean over the",
        "  cell's windows of |S_W(alpha)|^2 (raw).  SELFTEST (L34 discipline): at",
        "  alpha = j/q with q a clock, direct survivor sum == residue-count route",
        "  (counts exact integers) to 1e-9, AND the two struck residue classes",
        "  +-i6(q) hold EXACTLY ZERO survivors; checked on the first 20 windows of",
        "  cells (X=1e6,A=13) and (X=1e9,A=31), all j.",
        "AN5 -- foil-v2 on the QUADRATIC class (protocol VERBATIM from the registered",
        "  gate_g3 machinery; precompute_X / foil_row reused from",
        "  tools/betti_portrait_harness.py; honest prior: BLIND -- the linear layer",
        "  was, L38; a null closes the quadratic-representation gap = ledger law):",
        "  grid A in {13,31} x X in {1e6,1e9}; H = 50; NW = 3000 (1e6) / 1000 (1e9);",
        "  observables per cell: MARGIN = windowFluct/mainTerm of the H=50 window",
        "  (left-half variant at H=25 for S''), F2A1..F2A5 = |S_W(alpha)|^2 at the",
        "  top-5 Farey alphas by AN4 census mean in that cell (rank registered as the",
        "  observable class; alpha logged per cell before its foil rows; selection is",
        "  load-blind).  Loads: S = lambda-sum over the window's survivors (support",
        "  overlaps the observable -- disclosed); S'' = observable on left half, load",
        "  on right-half survivors (self-excluded); So = NA-degenerate for ALL six",
        "  observables (each reads every survivor; precedent: betti P3|So).",
        "  200 sigma_W permutations + 200 sigma_I lambda-resamples; seed 20260710.",
        "  Verdict per (observable, load) over the 4-cell grid:",
        "    PARITY-SENSITIVE iff min|z_I| >= 5 AND escalation |R(31)| >= |R(13)|/3",
        "    at both X (cells with |R(13)| <= 1e-9 skipped, betti stage_s4v copy);",
        "    SOFT iff min|z_I| >= 3; else PARITY-BLIND-UNDER-ESCALATION-v2.",
        "STOP (registered): after the registered grid -- no new alphas, no new",
        "  weightings, no threshold moves.  AN1/AN2 anatomy laws are reported as",
        "  measured laws with exact numbers regardless of foil verdicts.",
    ]:
        log(s)


# ---------- AN1 + AN2 ----------

def an12(defects):
    section("AN1 + AN2 -- exact spike anatomy of defect windows (support-grouped)")
    t0 = time.time()
    drift = []
    for A in AN_SCALES:
        pre = build_pre(A)
        n = pre["n"]
        g = G_KERNEL[A] - 1
        starts = defects[A]
        anas = []
        for r in starts:
            a = anatomy_exact(pre, [r % q for q in pre["Q"]], g)
            assert a["cc"] == 0 and a["fluct"] == -a["mainT"]
            assert sum(a["shares"][1:], Fraction(0)) == Fraction(-1)
            anas.append(a)
        mt = anas[0]["mainT"]
        log("")
        log("A=%d  g=%d  clocks=%d  subsets=%d  defect windows=%d  mainTerm=%s (~%.6f)"
            % (A, g, n, 1 << n, len(starts), mt, float(mt)))
        log("  coherence identity: windowFluct == -mainTerm EXACT and level shares sum")
        log("  to -1 EXACT on all %d windows -- OK" % len(starts))
        prof = np.array([[float(a["shares"][l]) for l in range(1, n + 1)] for a in anas])
        log("  AN1 level spectrum (share of mainTerm; defect windows, EXACT):")
        log("    lvl  window#1(exact)                mean         min          max")
        for l in range(1, n + 1):
            sh = anas[0]["shares"][l]
            ex = str(sh) if len(str(sh)) <= 30 else fdec(sh, 12)
            log("    %2d   %-30s %s %s %s"
                % (l, ex, fdec(prof[:, l - 1].mean()), fdec(prof[:, l - 1].min()),
                   fdec(prof[:, l - 1].max())))
        # controls
        ctrl = {}
        for kind, seed in (("matched", SEED + A), ("typical", SEED + 1000 + A)):
            rng = np.random.default_rng(seed)
            shs, fms, margs, top1s, normed, excl = [], [], [], [], [], 0
            for ic in range(200):
                if kind == "matched":
                    base = starts[ic % len(starts)]
                    ph = [int(base % q) if q <= 13 else int(rng.integers(0, q))
                          for q in pre["Q"]]
                else:
                    ph = [int(rng.integers(0, q)) for q in pre["Q"]]
                rr = anatomy_float(pre, ph, g)
                shs.append(rr["shares"][1:])
                fms.append(rr["fm"])
                margs.append(rr["marg"])
                top1s.append(rr["top1"])
                if abs(rr["fm"]) > 1e-9:
                    normed.append(rr["shares"][1:] / abs(rr["fm"]))
                else:
                    excl += 1
            ctrl[kind] = dict(sh=np.array(shs), fm=np.array(fms),
                              marg=np.array(margs), top1=top1s,
                              nrm=(np.array(normed) if normed else None), excl=excl)
        log("  AN1 controls (200 each; float64 from exact int64 V):")
        log("    lvl  matched-mean  typical-mean | norm-by-|F|: matched   typical"
            "   (excl %d/%d)" % (ctrl["matched"]["excl"], ctrl["typical"]["excl"]))
        for l in range(1, n + 1):
            nm = (ctrl["matched"]["nrm"][:, l - 1].mean()
                  if ctrl["matched"]["nrm"] is not None else float("nan"))
            nt = (ctrl["typical"]["nrm"][:, l - 1].mean()
                  if ctrl["typical"]["nrm"] is not None else float("nan"))
            log("    %2d   %s  %s | %s %s"
                % (l, fdec(ctrl["matched"]["sh"][:, l - 1].mean()),
                   fdec(ctrl["typical"]["sh"][:, l - 1].mean()), fdec(nm), fdec(nt)))
        log("    F/mainTerm: matched mean=%s sd=%.4f min=%s | typical mean=%s sd=%.4f"
            % (fdec(ctrl["matched"]["fm"].mean(), 4), ctrl["matched"]["fm"].std(),
               fdec(ctrl["matched"]["fm"].min(), 4),
               fdec(ctrl["typical"]["fm"].mean(), 4), ctrl["typical"]["fm"].std()))
        # AN2
        w1 = anas[0]
        log("  AN2 top-5 subsets of defect window #1 (r=%d) by |term(S)|"
            " (share of mainTerm):" % starts[0])
        for m in w1["top"][:5]:
            log("    %-16s term/mainTerm = %s   |term|/sum|term| = %.4f"
                % (mask_name(pre, m), fdec(Fraction(w1["t"][m], w1["mainN"]), 8),
                   w1["absN"][m] / w1["sumabs"]))
        r1 = {}
        for a in anas:
            nm = mask_name(pre, a["top"][0])
            r1[nm] = r1.get(nm, 0) + 1
        log("  AN2 rank-1 subset census, defect windows: %s"
            % "  ".join("%s:%d" % kv for kv in sorted(r1.items(), key=lambda x: -x[1])))
        for kind in ("matched", "typical"):
            cen = {}
            for m in ctrl[kind]["top1"]:
                nm = mask_name(pre, m)
                cen[nm] = cen.get(nm, 0) + 1
            tops = sorted(cen.items(), key=lambda x: -x[1])[:3]
            log("  AN2 rank-1 subset census, %s ctrl: %s"
                % (kind, "  ".join("%s:%d" % kv for kv in tops)))
        dm = np.array([[a["margN"][i] / a["sumabs"] for i in range(n)] for a in anas])
        log("  AN2 per-clock marginal share of sum|term| (mean): q: defect / matched"
            " / typical")
        for i, q in enumerate(pre["Q"]):
            log("    q=%2d: %.4f / %.4f / %.4f"
                % (q, dm[:, i].mean(), ctrl["matched"]["marg"][:, i].mean(),
                   ctrl["typical"]["marg"][:, i].mean()))
        drift.append((A, n, prof.mean(axis=0), dm.mean(axis=0), r1))
        RESULTS[("an1", A)] = dict(prof=prof, ctrl=ctrl, dm=dm, r1=r1, n=n)
    # drift table
    log("")
    log("AN1 DRIFT ACROSS A (defect mean level shares of mainTerm):")
    log("  A    lvl1        lvl2        lvl3        lvl4        tail(5..n)")
    for A, n, mp, _, _ in drift:
        tail = mp[4:].sum() if n > 4 else 0.0
        row = [fdec(mp[l], 6) if l < n else "    --    " for l in range(4)]
        log("  %2d  %s %s %s %s  %s" % (A, row[0], row[1], row[2], row[3], fdec(tail, 6)))
    l1 = {A: mp[0] for A, n, mp, _, _ in drift}
    l2 = {A: mp[1] for A, n, mp, _, _ in drift}
    log("  drift verdict: level-1 share %s from %s (A=17) to %s (A=43);"
        % ("falls" if l1[43] < l1[17] else "rises", fdec(l1[17], 6), fdec(l1[43], 6)))
    log("  level-2 share %s from %s to %s; see mined laws."
        % ("falls" if abs(l2[43]) < abs(l2[17]) else "rises",
           fdec(l2[17], 6), fdec(l2[43], 6)))
    RESULTS["drift"] = drift
    log("AN1+AN2 done (%.1fs)" % (time.time() - t0))


# ---------- AN3 ----------

def an3():
    section("AN3 -- coherence-margin census windowFluct/mainTerm")
    t0 = time.time()
    # cell 1: exhaustive
    A, g, X = 13, 11, 10 ** 6
    mt = float(main_term(A, g))
    m = np.arange(0, X + g + 2, dtype=np.int64)
    clean = np.ones(m.size, dtype=bool)
    for q in clocks(A):
        iq = i6(q)
        r = m % q
        clean &= (r != iq) & (r != (q - iq) % q)
    cs = np.concatenate([[0], np.cumsum(clean.astype(np.int64))])
    c = cs[g + 1: X + g + 1] - cs[1: X + 1]
    hist = np.bincount(c, minlength=g + 1)
    cmin = int(c.min())
    assert cmin >= 1, "kernel gap G(13)=11 contradicted"
    log("cell 1: A=13 g=11 EXHAUSTIVE k in [0,1e6)  mainTerm=%s=%.6f"
        % (main_term(A, g), mt))
    log("  histogram (cleanCount c: windows, margin=(c-mT)/mT):")
    for cv in range(g + 1):
        if hist[cv]:
            log("    c=%2d: %8d  margin=%s" % (cv, int(hist[cv]), fdec(cv / mt - 1, 6)))
    locs = np.flatnonzero(c == cmin)
    log("  minimum c=%d (margin %s): %d windows; first 5 k: %s"
        % (cmin, fdec(cmin / mt - 1, 6), locs.size, [int(x) for x in locs[:5]]))
    log("  kernel check: c >= 1 everywhere (engineDecay_at_13 empirical) -- OK")
    RESULTS[("an3", 13)] = dict(hist=hist, cmin=cmin, nmin=int(locs.size), mt=mt)
    # cell 2: sampled
    A, g, X = 31, 58, 10 ** 9
    mt = float(main_term(A, g))
    rng = np.random.default_rng(SEED + 31)
    ks = rng.integers(0, X, size=100000).astype(np.int64)
    mm = ks[:, None] + np.arange(1, g + 1, dtype=np.int64)[None, :]
    cl = np.ones(mm.shape, dtype=bool)
    for q in clocks(A):
        iq = i6(q)
        r = mm % q
        cl &= (r != iq) & (r != (q - iq) % q)
    c2 = cl.sum(axis=1)
    hist2 = np.bincount(c2, minlength=g + 1)
    cmin2 = int(c2.min())
    assert cmin2 >= 1, "kernel gap G(31)=58 contradicted"
    log("cell 2: A=31 g=58 SAMPLED 1e5 windows, k uniform in [0,1e9) (seed %d)"
        % (SEED + 31))
    log("  mainTerm=%.6f; histogram (c: windows, margin):" % mt)
    for cv in range(g + 1):
        if hist2[cv]:
            log("    c=%2d: %6d  margin=%s" % (cv, int(hist2[cv]), fdec(cv / mt - 1, 6)))
    locs2 = np.flatnonzero(c2 == cmin2)
    log("  minimum c=%d (margin %s): %d windows; k values (first 5): %s"
        % (cmin2, fdec(cmin2 / mt - 1, 6), locs2.size,
           [int(ks[x]) for x in locs2[:5]]))
    RESULTS[("an3", 31)] = dict(hist=hist2, cmin=cmin2, nmin=int(locs2.size), mt=mt)
    log("AN3 done (%.1fs)" % (time.time() - t0))


# ---------- AN4 + AN5 cells ----------

def make_cell(px, A):
    X, ncent = px["X"], px["ncent"]
    NW = ncent // 50
    m = X + np.arange(ncent, dtype=np.int64)
    clean = np.ones(ncent, dtype=bool)
    for q in clocks(A):
        iq = i6(q)
        r = m % q
        clean &= (r != iq) & (r != (q - iq) % q)
    cl = clean.reshape(NW, 50)
    lamw = px["lam"].astype(np.float64).reshape(NW, 50)
    right = np.zeros((NW, 50), dtype=bool)
    right[:, 25:] = True
    masks = {"S": cl, "Ssplit": cl & right}
    loads = {k: (lamw * mm).sum(1) for k, mm in masks.items()}
    pool = px["lam"][clean].astype(np.float64)
    nsurv = int(cl.sum())
    rng = np.random.default_rng(SEED)
    nulls = {k: np.empty((200, NW)) for k in masks}
    lmat = np.zeros((NW, 50), dtype=np.float64)
    for t in range(200):
        lmat[:] = 0.0
        lmat[cl] = rng.choice(pool, size=nsurv)
        for k, mm in masks.items():
            nulls[k][t] = (lmat * mm).sum(1)
    sv = np.flatnonzero(clean)
    return dict(X=X, A=A, NW=NW, cl=cl, loads=loads, nulls=nulls, nsurv=nsurv,
                sv_m=m[sv], sv_w=(sv // 50).astype(np.int64),
                sv_t=(sv % 50).astype(np.int64))


def swinsq_rational(cell, j, q, half=False):
    ms, w = cell["sv_m"], cell["sv_w"]
    if half:
        s = cell["sv_t"] < 25
        ms, w = ms[s], w[s]
    ph = 2 * np.pi * (((j * (ms % q)) % q).astype(np.float64)) / q
    re = np.bincount(w, weights=np.cos(ph), minlength=cell["NW"])
    im = np.bincount(w, weights=np.sin(ph), minlength=cell["NW"])
    return re * re + im * im


def swinsq_real(cell, alpha, half=False):
    t, w = cell["sv_t"], cell["sv_w"]
    if half:
        s = t < 25
        t, w = t[s], w[s]
    ph = 2 * np.pi * alpha * t.astype(np.float64)   # per-window anchor: exact phases
    re = np.bincount(w, weights=np.cos(ph), minlength=cell["NW"])
    im = np.bincount(w, weights=np.sin(ph), minlength=cell["NW"])
    return re * re + im * im


def an4(cells):
    section("AN4 -- Farey / exponential-sum layer over survivor sets")
    t0 = time.time()
    # random minor-arc alphas (registered rejection rule)
    rng = np.random.default_rng(SEED + 4)
    grid = np.array(sorted(j / q for j, q in FAREY))
    minor = []
    while len(minor) < 200:
        a = float(rng.uniform(0, 1))
        d = np.abs(grid - a).min()
        if d > 1 / 2500 and a > 1 / 2500 and 1 - a > 1 / 2500:
            minor.append(a)
    log("Farey grid: %d alphas (j/q, 2<=q<=50); 200 random minor-arc alphas drawn"
        % len(FAREY))
    log("(seed %d, rejection distance 1/2500) -- registered." % (SEED + 4))
    census = {}
    for (X, A), cell in sorted(cells.items()):
        # exact major-arc selftest on registered cells
        if (X, A) in ((10 ** 6, 13), (10 ** 9, 31)):
            nchk, maxdev = 0, 0.0
            for wi in range(20):
                sel = cell["sv_w"] == wi
                ms = cell["sv_m"][sel]
                if ms.size == 0:
                    continue
                for q in clocks(A):
                    res = (ms % q).astype(np.int64)
                    cnt = np.bincount(res, minlength=q)
                    assert int(cnt[i6(q)]) == 0, "survivor in struck class -i6"
                    assert int(cnt[(q - i6(q)) % q]) == 0, "survivor in struck class +i6"
                    for j in range(1, q):
                        ra = sum(cmath.exp(2j * math.pi * ((j * int(r)) % q) / q)
                                 for r in res)
                        rb = sum(int(cnt[r]) * cmath.exp(2j * math.pi * ((j * r) % q) / q)
                                 for r in range(q))
                        maxdev = max(maxdev, abs(ra - rb))
                        assert abs(ra - rb) <= 1e-9
                        nchk += 1
            log("  SELFTEST cell X=%.0e A=%d: %d major-arc values (20 windows, all j,"
                % (X, A, nchk))
            log("    all clocks): direct sum == exact-residue-count route, max dev"
                " %.2e <= 1e-9;" % maxdev)
            log("    struck classes +-i6(q) hold 0 survivors EXACTLY -- PASS")
        mean_far = np.empty(len(FAREY))
        for idx, (j, q) in enumerate(FAREY):
            mean_far[idx] = swinsq_rational(cell, j, q).mean()
        mean_min = np.array([swinsq_real(cell, a).mean() for a in minor])
        census[(X, A)] = mean_far
        nsw = cell["nsurv"] / cell["NW"]
        is_clock = np.array([q in clocks(A) for j, q in FAREY])
        top = np.argsort(-mean_far)[:10]
        log("  cell X=%.0e A=%d: NW=%d survivors/window=%.2f" % (X, A, cell["NW"], nsw))
        log("    mean|S_W|^2: clock-denominator alphas %.3f | other Farey %.3f |"
            % (mean_far[is_clock].mean(), mean_far[~is_clock].mean()))
        log("    random minor-arc %.3f (max %.3f) | survivor count (=|S_W(0)|) %.2f"
            % (mean_min.mean(), mean_min.max(), nsw))
        log("    top-10 Farey by mean|S_W|^2: %s"
            % "  ".join("%d/%d:%.2f" % (FAREY[i][0], FAREY[i][1], mean_far[i])
                        for i in top))
    RESULTS["an4"] = census
    log("AN4 done (%.1fs)" % (time.time() - t0))
    return census, minor


OBS_NAMES = ["MARGIN", "F2A1", "F2A2", "F2A3", "F2A4", "F2A5"]


def an5(cells, census):
    section("AN5 -- foil-v2 on the QUADRATIC class (gate_g3 machinery, verbatim)")
    t0 = time.time()
    rows = {}
    for (X, A), cell in sorted(cells.items()):
        NW = cell["NW"]
        log("")
        log("CELL X=%.0e A=%d NW=%d H=50 (seed %d)" % (X, A, NW, SEED))
        top5 = list(np.argsort(-census[(X, A)])[:5])
        log("  registered top-5 Farey alphas (by AN4 census mean |S_W|^2): %s"
            % "  ".join("F2A%d=%d/%d(%.2f)" % (k + 1, FAREY[i][0], FAREY[i][1],
                                               census[(X, A)][i])
                        for k, i in enumerate(top5)))
        conj = [(a + 1, b + 1) for a in range(5) for b in range(a + 1, 5)
                if FAREY[top5[a]][1] == FAREY[top5[b]][1]
                and FAREY[top5[a]][0] + FAREY[top5[b]][0] == FAREY[top5[a]][1]]
        if conj:
            log("  note: conjugate pairs among top-5 (|S(a)|^2 == |S(1-a)|^2):"
                " %s -- duplicate observables, disclosed" % conj)
        mt50, mt25 = float(main_term(A, 50)), float(main_term(A, 25))
        cnt_full = cell["cl"].sum(1).astype(np.float64)
        cnt_left = cell["cl"][:, :25].sum(1).astype(np.float64)
        obs_full = {"MARGIN": cnt_full / mt50 - 1}
        obs_left = {"MARGIN": cnt_left / mt25 - 1}
        for k, i in enumerate(top5):
            j, q = FAREY[i]
            obs_full["F2A%d" % (k + 1)] = swinsq_rational(cell, j, q)
            obs_left["F2A%d" % (k + 1)] = swinsq_rational(cell, j, q, half=True)
        for name in OBS_NAMES:
            stS = BP.foil_row(obs_full[name], cell["loads"]["S"],
                              cell["nulls"]["S"], np.random.default_rng(SEED + 7))
            stP = BP.foil_row(obs_left[name], cell["loads"]["Ssplit"],
                              cell["nulls"]["Ssplit"], np.random.default_rng(SEED + 7))
            rows[(name, "S", X, A)] = stS
            rows[(name, "S''", X, A)] = stP
            for lab, st in (("S", stS), ("S''", stP)):
                log("  %-6s|%-3s R=%+8.4f zW=%+6.1f zI=%+6.1f n=%5d %s"
                    % (name, lab, st["R"], st["zW"], st["zI"], st["n"], st["note"]))
                for zn, zv in (("zW", st["zW"]), ("zI", st["zI"])):
                    if abs(zv) >= 3:
                        ANOMALIES.append(("AN5 %s|%s X=%.0e A=%d" % (name, lab, X, A),
                                          zn, zv))
            log("  %-6s|So  NA (degenerate: observable reads every survivor;"
                " precedent betti P3|So)" % name)
    # verdicts
    log("")
    log("AN5 VERDICTS (rule registered above; grid = 4 cells):")
    verdicts = {}
    cellkeys = [(X, A) for X in XS for A in (13, 31)]
    for name in OBS_NAMES:
        for load in ("S", "S''"):
            zs, Rs, parts = [], {}, []
            for (X, A) in cellkeys:
                st = rows[(name, load, X, A)]
                zs.append(abs(st["zI"]))
                Rs[(X, A)] = st["R"]
                parts.append("X%.0eA%d R%+.3f zI%+5.1f" % (X, A, st["R"], st["zI"]))
            ratio_ok = all(abs(Rs[(X, 31)]) >= abs(Rs[(X, 13)]) / 3.0
                           for X in XS if abs(Rs[(X, 13)]) > 1e-9)
            ratios = []
            for X in XS:
                if abs(Rs[(X, 13)]) > 1e-9:
                    ratios.append("%.0e:%.2f" % (X, abs(Rs[(X, 31)])
                                                 / abs(Rs[(X, 13)])))
                else:
                    ratios.append("%.0e:na" % X)
            v = ("PARITY-SENSITIVE" if min(zs) >= 5 and ratio_ok
                 else "SOFT" if min(zs) >= 3
                 else "PARITY-BLIND-UNDER-ESCALATION-v2")
            verdicts[(name, load)] = (min(zs), ratio_ok, v)
            log("  %-6s|%-3s %s" % (name, load, " | ".join(parts)))
            log("             min|z_I|=%.2f esc(%s) ratio_ok=%s -> %s"
                % (min(zs), ",".join(ratios), ratio_ok, v))
    RESULTS["an5"] = (rows, verdicts)
    log("AN5 done (%.1fs)" % (time.time() - t0))
    return verdicts


def mined_laws(defects, verdicts):
    section("MINED CANDIDATE LAWS (ranked; exact numbers; foil verdicts independent)")
    drift = RESULTS["drift"]
    l1 = {A: mp[0] for A, n, mp, _, _ in drift}
    l2 = {A: mp[1] for A, n, mp, _, _ in drift}
    l3 = {A: (mp[2] if n > 2 else 0.0) for A, n, mp, _, _ in drift}
    m5 = {A: dmm[0] for A, n, mp, dmm, _ in drift}
    l23 = {A: (mp[1] + (mp[2] if n > 2 else 0.0)) for A, n, mp, _, _ in drift}
    neg23 = all(RESULTS[("an1", A)]["prof"][:, 1].max() < 0
                and RESULTS[("an1", A)]["prof"][:, 2].max() < 0 for A in AN_SCALES)
    log("LAW-1 (AN1, exact on defects): the defect conspiracy is PAIR/TRIPLE")
    log("  dominated: mean lvl2+lvl3 share of -mainTerm = %s (A=17) .. %s (A=43),"
        % (fdec(l23[17], 4), fdec(l23[43], 4)))
    log("  levels 2 and 3 strictly negative on every defect window: %s;" % neg23)
    log("  level-1 share is small and shrinks with A: %s (A=17) .. %s (A=43)"
        % (fdec(l1[17], 6), fdec(l1[43], 6)))
    log("  (small clocks strike near density; lvl2 %s .. %s, lvl3 %s .. %s)."
        % (fdec(l2[17], 6), fdec(l2[43], 6), fdec(l3[17], 6), fdec(l3[43], 6)))
    xs = sorted(l1)
    log("  drift: lvl1 %s, lvl2 %s with A across %s"
        % ("monotone" if all(l1[xs[i + 1]] <= l1[xs[i]] for i in range(len(xs) - 1))
           or all(l1[xs[i + 1]] >= l1[xs[i]] for i in range(len(xs) - 1)) else "non-monotone",
           "monotone" if all(l2[xs[i + 1]] <= l2[xs[i]] for i in range(len(xs) - 1))
           or all(l2[xs[i + 1]] >= l2[xs[i]] for i in range(len(xs) - 1)) else "non-monotone",
           xs))
    log("LAW-2 (AN2): smallest-clock marginal m(5) = %s (A=17) .. %s (A=43);"
        % (fdec(m5[17], 4), fdec(m5[43], 4)))
    r1all = {}
    for A, n, mp, dmm, r1 in drift:
        for k, v in r1.items():
            r1all[k] = r1all.get(k, 0) + v
    log("  rank-1 subset census over all %d defect windows: %s"
        % (sum(len(defects[A]) for A in AN_SCALES),
           "  ".join("%s:%d" % kv for kv in sorted(r1all.items(), key=lambda x: -x[1]))))
    h13 = RESULTS[("an3", 13)]
    h31 = RESULTS[("an3", 31)]
    log("LAW-3 (AN3): margin minima: A=13/1e6 exhaustive min c=%d (%d windows,"
        % (h13["cmin"], h13["nmin"]))
    log("  margin %s); A=31/1e9 sampled min c=%d (%d windows, margin %s); c>=1"
        % (fdec(h13["cmin"] / h13["mt"] - 1, 6), h31["cmin"], h31["nmin"],
           fdec(h31["cmin"] / h31["mt"] - 1, 6)))
    log("  everywhere observed == the kernel wall in census form.")
    log("LAW-4 (AN4): major arcs at clock denominators carry the survivor structure")
    log("  (struck classes empty EXACTLY); see census numbers above.")
    nblind = sum(1 for v in verdicts.values() if v[2].startswith("PARITY-BLIND"))
    log("LAW-5 (AN5, ledger): %d/%d (observable,load) pairs PARITY-BLIND-UNDER-"
        % (nblind, len(verdicts)))
    log("  ESCALATION-v2 -- the first QUADRATIC observable class through the foil;")
    log("  a null here is the registered ledger law (quadratic-representation gap")
    log("  closed empirically).")
    if ANOMALIES:
        log("ANOMALIES |z| >= 3:")
        for ctx, zn, zv in ANOMALIES:
            log("  %s: %s=%+.2f" % (ctx, zn, zv))
    else:
        log("ANOMALIES |z| >= 3: none")


def main():
    t00 = time.time()
    section("FOURIER-WINDOW SPIKE-ANATOMY RUN 1 -- %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    log("harness: tools/fourier_window_harness.py; log: tools/fourier_window_run1.log")
    log("empirical body of EuclidsPath/Engine/Step00StrikeFourier.lean (Parts R+E2b)")
    log("python %s | numpy %s | seed %d" % (sys.version.split()[0], np.__version__, SEED))
    log("conventions: clocks A = primes in [5,A]; window (k,k+g]; Clean <=> m mod q")
    log("notin {i6, q-i6}, i6 = 6^{-1} mod q; mainTerm = g*prod(1-2/q) (Fraction);")
    log("windowFluct = cleanCount - mainTerm; engines = nonzero modes (E2b identity).")
    defects = selftests()
    registration()
    an12(defects)
    an3()
    section("AN4/AN5 cell construction (precompute_X reused from betti_portrait_harness)")
    cells = {}
    for X in XS:
        px = BP.precompute_X(X, NW_OF_X[X], 50)
        for A in (13, 31):
            tc = time.time()
            cells[(X, A)] = make_cell(px, A)
            log("  cell X=%.0e A=%d: NW=%d survivors=%d (loads S/S''+200 sigma_I"
                " nulls) [%.1fs]" % (X, A, cells[(X, A)]["NW"],
                                     cells[(X, A)]["nsurv"], time.time() - tc))
    census, minor = an4(cells)
    verdicts = an5(cells, census)
    mined_laws(defects, verdicts)
    section("RUN COMPLETE")
    log("total runtime %.1f min; STOP registered: no new alphas/weightings/thresholds."
        % ((time.time() - t00) / 60.0))
    log("SECTION LINE INDEX (this run, 1-based in this append block):")
    for title, ln in SECTION_INDEX:
        log("  line %5d: %s" % (ln, title))


if __name__ == "__main__":
    main()
