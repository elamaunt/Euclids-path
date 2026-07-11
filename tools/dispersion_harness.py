# dispersion_harness.py -- the NUMERIC CORE of the dispersion pass: the
# measured half of the dispersion-blindness law over the strike-clock window
# system of EuclidsPath/Engine/Step00StrikeFourier.lean.
#
# Lean conventions mirrored EXACTLY (read Step00StrikeFourier.lean first):
#   clocks A    = primes q with 5 <= q <= A
#   Clean A m  <=> for every clock q: m mod q notin {i6(q), (q - i6(q)) mod q},
#                  i6(q) = 6^{-1} mod q   (strike_minus_iff / strike_plus_iff)
#   window      = (k, k+g], centers m = k+1 .. k+g
#   cleanCount A k g = #{m in (k, k+g] : Clean A m}
#   mainTerm A g = g * prod_q (1 - 2/q)      (rational -- fractions.Fraction)
#   windowFluct  = cleanCount - mainTerm
#   period P_A   = prod_q q
#
# Stages (closed list; the registration block is written to the log FIRST):
#   s0  selftests ST-A..ST-F: pairCorr CRT trichotomy (independently derived),
#       window-variance three-way identity (direct / pair-correlation /
#       spectral), Lean-constant byte-checks (L34 1485@5005, the G(A) table,
#       the 50 defect windows), r4 = 8*sigma for odd n <= 1e6 (exact),
#       Cornacchia a^2+27b^2 <=> 2 cubic residue mod p (p = 1 mod 3, p < 1e5).
#       ANY selftest failure = STOP exit 1.
#   s1  the Markov-gap table: exact defect-window counts per period at
#       g = G(A)-1 / G(A) / floor(A^2/14) vs the dispersion (Markov) bound
#       VarSum/mainTerm^2 -- the pass's calibration number.
#   s2  the Farey m-class profile of the level-1 x level-1 cross-terms (the
#       pass's NEW measurement): ceiling segments K = ceil(A^2/6); defect-
#       centered vs typical segments at A = 17/19.
#   s3  the shifted-convolution deviation table (incomplete segment counts vs
#       the complete CRT local product) + the ensemble kloos probe (the
#       registered extension of circle_sum stage D; kloos(u,u) over ZMod q
#       reuses tools/circle_sum_harness.py implementation patterns).
#
# Conventions copied from tools/fourier_window_harness.py: append-only ASCII
# log with a section line-index, seed 20260710, Fraction-exact wherever
# feasible, numpy elsewhere; gate_g3 foil machinery (foil_row) reused VERBATIM
# from tools/betti_portrait_harness.py (CONDITIONAL -- see the foil note in
# the registration block).
#
# Usage: python tools/dispersion_harness.py   (appends to
# tools/dispersion_run1.log; the env var DISPERSION_LOG overrides the log
# path for development dry-runs only).

import cmath
import math
import os
import sys
import time
from fractions import Fraction

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import betti_portrait_harness as BP  # foil_row reused VERBATIM (conditional)

LOGPATH = os.environ.get("DISPERSION_LOG") or os.path.join(TOOLS,
                                                           "dispersion_run1.log")
SEED = 20260710
STAGE_TIME_CAP = 5400.0   # seconds per stage (registered)

_LINENO = [0]
SECTION_INDEX = []


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


_logf = open(LOGPATH, "a", buffering=1, encoding="ascii", errors="replace")
sys.stdout = _Tee(_logf)


def log(s=""):
    print(s, flush=True)


def section(title):
    SECTION_INDEX.append((title, _LINENO[0] + 1))
    log("=" * 78)
    log(title)
    log("=" * 78)


# ------------------------------------------------------------------ constants

G_KERNEL = {5: 2, 7: 5, 11: 7, 13: 11, 17: 18, 19: 25, 23: 34, 29: 43,
            31: 58, 37: 88, 41: 91, 43: 103}   # kernel gap G(A) (Lean gates)
# defect-window starts: A=17/19 from the full-period scans (re-derived here);
# A >= 23 from tools/pratt_wing_harness.py DEFECT_R (solver certificates)
DEFECT_R = {
    17: [117, 502, 5642, 6027, 21497, 30845],
    19: [110, 26045, 67695, 170035, 203005, 373175],
    23: [12694428, 18165208, 19016903, 24487683],
    29: [200906185, 877375977],
    31: [21844264615],
    37: [1145973108145],
    41: [50077677123072],
    43: [233885349904190],
}
# complete per-period defect counts at g = G(A)-1 known from logs
# (gap_extremal_run1.log:101-142 census + :28 A=29 full-period scan)
KNOWN_TRUE = {5: 2, 7: 2, 11: 4, 13: 12, 17: 20, 19: 20, 23: 4, 29: 2}

ANOMALIES = []   # (context, statistic, value)


# ----------------------------------------------------------------- primitives

def primes_upto(n):
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def clocks(A):
    return [p for p in primes_upto(A) if p >= 5]


def i6(q):
    return pow(6, -1, q)


def period(A):
    P = 1
    for q in clocks(A):
        P *= q
    return P


def main_term(A, g):
    r = Fraction(g)
    for q in clocks(A):
        r *= Fraction(q - 2, q)
    return r


def clean_bool(A, lo, n, chunk=1 << 23):
    """Boolean Clean(A, m) for m = lo .. lo+n-1 (chunked numpy)."""
    out = np.ones(n, dtype=bool)
    Q = clocks(A)
    iqs = [(q, i6(q)) for q in Q]
    for c0 in range(0, n, chunk):
        c1 = min(n, c0 + chunk)
        m = np.arange(lo + c0, lo + c1, dtype=np.int64)
        acc = out[c0:c1]
        for q, iq in iqs:
            r = m % q
            acc &= (r != iq) & (r != (q - iq) % q)
    return out


def is_clean_int(A, m):
    for q in clocks(A):
        r = m % q
        iq = i6(q)
        if r == iq or r == (q - iq) % q:
            return False
    return True


def cq_direct(q, d):
    """|{i6,-i6} union {i6-d,-i6-d}| mod q -- the struck-pair class count."""
    iq = i6(q)
    return len({iq, (q - iq) % q, (iq - d) % q, (q - iq - d) % q})


def cq_tri(q, d):
    """The registered trichotomy: 2 (d=0 mod q), 3 (3d = +-1 mod q), 4 else."""
    dd = d % q
    if dd == 0:
        return 2
    if (3 * dd) % q in (1, q - 1):
        return 3
    return 4


def paircorr_crt(A, d):
    """#{r < P_A : Clean r and Clean (r+d)} by the CRT product prod(q-c_q(d))."""
    v = 1
    for q in clocks(A):
        v *= q - cq_tri(q, d)
    return v


def var_sum_exact(A, g):
    """Sum_{k<P} windowFluct^2 EXACT via the pair-correlation formula:
    sum_{|d|<g} (g-|d|) pairCorr(|d|) - P*mainTerm^2  (Fraction)."""
    P = period(A)
    mt = main_term(A, g)
    s = Fraction(g * paircorr_crt(A, 0))
    for d in range(1, g):
        s += 2 * (g - d) * paircorr_crt(A, d)
    return s - P * mt * mt


def kloos_val(q, a, b):
    """kloos(a,b) over Z/q, direct definition (exact integer phases) --
    tools/circle_sum_harness.py implementation pattern, verbatim."""
    tot = 0j
    for xx in range(1, q):
        tot += cmath.exp(2j * math.pi * ((a * xx + b * pow(xx, -1, q)) % q) / q)
    return tot


def fdec(x, nd=6):
    return ("%+." + str(nd) + "f") % float(x)


def halve_to_fit(n, per_unit, remaining, what):
    """Registered halving fallback: halve the ensemble knob until the
    projection fits the remaining stage budget; each halving is logged."""
    proj = n * per_unit
    while proj > remaining and n > 1:
        n //= 2
        proj = n * per_unit
        log("  FALLBACK (registered halving): %s halved to %d "
            "(projection %.0fs > remaining budget)" % (what, n, proj * 2))
    return n


def stage_close(name, t0):
    el = time.time() - t0
    log("%s done (%.1fs%s)" % (name, el,
                               "" if el <= STAGE_TIME_CAP
                               else "; STAGE_TIME_CAP EXCEEDED -- logged"))
    return el


# --------------------------------------------------------------- registration

CEIL_K = {13: 29, 17: 49, 19: 61, 23: 89, 31: 161, 43: 309}  # ceil(A^2/6)


def registration():
    section("PRE-REGISTRATION BLOCK (written FIRST, before ANY measurement; "
            "closed lists)")
    for s in [
        "CONVENTIONS (mirror EuclidsPath/Engine/Step00StrikeFourier.lean and",
        "  tools/fourier_window_harness.py): clocks A = primes in [5,A];",
        "  Clean A m <=> m mod q notin {i6, q-i6} for every clock q, i6 =",
        "  6^{-1} mod q; window (k, k+g], centers k+1..k+g; cleanCount;",
        "  mainTerm A g = g*prod(1-2/q) EXACT Fraction; windowFluct =",
        "  cleanCount - mainTerm; period P_A = prod q.  Seed 20260710 wherever",
        "  sampling occurs; append-only ASCII log; Fraction-exact wherever",
        "  feasible (all counting identities, pair terms, variance sums,",
        "  Markov bounds); float64 numpy elsewhere, disclosed inline.",
        "CLOSED STAGE LIST: s0, s1, s2, s3 -- no additions after this block.",
        "",
        "s0 SELFTESTS (mandatory; ANY failure = STOP exit 1):",
        "  ST-A  pair-class trichotomy c_q(d), INDEPENDENTLY DERIVED here:",
        "    the allowed residues for {r clean, r+d clean} at clock q exclude",
        "    U = {i6,-i6} union {i6-d,-i6-d}; |U| = 2 iff d = 0 mod q; else",
        "    the overlap of the two doubletons is nonempty iff d = +-2*i6",
        "    (elementwise: i6 = -i6-d gives d = -2*i6; -i6 = i6-d gives",
        "    d = 2*i6; the same-sign equations force d = 0; both signs at",
        "    once force 4*i6 = 0, impossible), the overlap then has size",
        "    EXACTLY 1, and 2*i6 = 2/6 = 3^{-1} mod q, so d = +-2*i6 <=>",
        "    3d = +-1 mod q.  Hence c_q(d) = 2 / 3 / 4 as registered.",
        "    CHECK (byte-exact): |U| by direct set construction == trichotomy",
        "    for EVERY clock q <= 43 and EVERY d in [0,q); the overlap-1 class",
        "    {d : |U|=3} == {+-2*i6 mod q} == {d : 3d = +-1 mod q} as SETS.",
        "  ST-B  pairCorr(A,d) = #{r < P : Clean r and Clean r+d} by direct",
        "    full-period scan == CRT product prod_q (q - c_q(d)): byte-exact",
        "    at A in {5,7,11,13} for ALL d < 100, and for ALL d in [0, P) at",
        "    A = 5 (P=5) and A = 7 (P=35).",
        "  ST-C  window variance Sum_{k<P} windowFluct^2, three ways:",
        "    (a) direct scan (exact integers Sum cc, Sum cc^2 -> Fraction);",
        "    (b) pair-correlation formula Sum_{|d|<g}(g-|d|)*pairCorr(|d|)",
        "        - P*mainTerm^2 (exact Fraction, pairCorr via CRT product);",
        "    (c) spectral side P * Sum_{p != 0} |c(p)|^2 |W_g(theta_p)|^2,",
        "        c(p) = DFT of the clean indicator over Z_P, theta_p = p/P,",
        "        W_g(theta) = sum_{t=1..g} e(theta t)  (complex float64).",
        "    (a) == (b) BYTE-EXACT as Fractions; |(c)-(a)| <= 1e-9*max(1,(a))",
        "    at every cell A in {5,7,11,13} x g in {2,5,11}.",
        "  ST-D  Lean-constant byte-checks:",
        "    L34: #{r in [0,P): Clean(13,r)} == 1485 == 3*5*9*11 at P = 5005",
        "      (Step00SideCollision.lean / Step00PackingGeometry.lean).",
        "    G(A) table {5:2, 7:5, 11:7, 13:11, 17:18, 19:25, 23:34, 29:43,",
        "      31:58, 37:88, 41:91, 43:103}: for A <= 19 the full-period scan",
        "      here must give max struck run == G(A)-1 (byte-exact); A = 23 is",
        "      scan-confirmed in s1 (registered deferral: the same scan",
        "      delivers the s1 counts); for A in {23..43} every DEFECT_R",
        "      witness r must have (r, r+G-1] fully struck with r and r+G",
        "      clean (certifies G(A) >= table value; the upper side is the",
        "      Lean kernel gate ladder, phase_cover_run1.log, cited not rerun).",
        "    50 defect windows: A=17 scan -> exactly 20 starts, first r=117,",
        "      502 present, all 6 listed present; A=19 scan -> exactly 20",
        "      starts, first r=110, all 6 listed present; DEFECT_R witnesses",
        "      at A in {23,29,31,37,41,43} (4+2+1+1+1+1) verified struck;",
        "      total 20+20+10 = 50 (tools/pratt_wing_harness.py lineage).",
        "  ST-E  r4(n) == 8*sigma(n) for EVERY odd n <= 1e6 (anchors the",
        "    gated-Jacobi claim).  Route (EXACT, no float): r2(n) by direct",
        "    lattice count (x^2+y^2 = n over Z^2, sign/zero multiplicities",
        "    explicit); r4 = r2 * r2 by Kronecker-substitution convolution in",
        "    Python big integers, base 2^64 (carry-safe: max coefficient <=",
        "    max r2 * sum r2, asserted < 2^63); sigma by divisor sieve.",
        "    0 mismatches required; spot anchors r4(1)=8, r4(3)=32 asserted.",
        "  ST-F  Cornacchia gate: for EVERY prime p = 1 mod 3, p < 1e5:",
        "    (exists a,b: p = a^2 + 27 b^2)  <=>  2^((p-1)/3) = 1 mod p",
        "    (2 a cubic residue).  0 failures required (pre-validates the",
        "    sphere harness's cubic probe).",
        "",
        "s1 THE MARKOV-GAP TABLE (the pass's calibration number):",
        "  For A in {5,7,11,13,17,19,23}: exact defect-window count per",
        "  period N(g) = #{k < P : cleanCount(A,k,g) = 0} by direct scan",
        "  (A=23: chunked numpy over P = 37,182,145) at:",
        "    g = G(A)-1  (maximal defect length; N known nonzero -- byte-",
        "      check vs gap_extremal_run1.log census: 2/2/4/12/20/20/4);",
        "    g = G(A)    (MUST be zero -- kernel gap cross-check, STOP if not);",
        "    g = floor(A^2/14) (Sharp window) where distinct from both.",
        "  Markov/dispersion bound at each g: B(g) = VarSum(g)/mainTerm(g)^2",
        "  EXACT Fraction via the ST-C-validated pair-correlation formula",
        "  (a defect window has Fluct^2 = mainTerm^2, so N(g) <= B(g)).",
        "  THE deliverable: the ratio table B/N -- how far is Markov from",
        "  the wall.  A in {29,31}: true counts from logged solver data where",
        "  complete (A=29: 2, full-period scan gap_extremal_run1.log:28);",
        "  A=31 census incomplete -> bound-only, labeled.",
        "",
        "s2 THE FAREY m-CLASS PROFILE (the pass's NEW measurement).",
        "  Object: level-1 modes c(q,j) = -(1/q)(e(-j*i6/q) + e(j*i6/q)),",
        "  j in [1,q-1] (Step00StrikeFourier modeCoeff, j != 0).  For ordered",
        "  clock pairs (q,q'), q != q', the window second moment of the",
        "  level-1 strike-density fluctuation f1(m) = sum_q sum_j c(q,j)",
        "  e(jm/q) = -sum_q eps_q(m) decomposes into cross-terms at the",
        "  DIFFERENCE frequencies theta = (jq'-j'q)/(qq') = m/(qq'), m the",
        "  integer Farey class, 0 < |m| < qq'; the cross-term of the pair is",
        "  c(q,j) c(q',j') S_W(theta) with |S_W(theta)| = |D_K(m/(qq'))|,",
        "  D_K(theta) = sum_{t=1..K} e(theta t) (Dirichlet kernel).",
        "  M-OBS-1 (position-independent, ceiling segments K = ceil(A^2/6):",
        "    29/49/89/161/309 at A = 13/17/23/31/43): TOTAL cross-term mass",
        "    profile by |m|: mass(|m|) = sum over ordered pairs and (j,j')",
        "    with |jq'-j'q| = |m| of |c(q,j)|*|c(q',j')|*|D_K(m/(qq'))|;",
        "    reported: total, the m = +-1 (Farey-adjacent) layer and share,",
        "    bands |m| in [2,5],[6,10],[11,20],[21,50],[51,200],[201,max),",
        "    top-10 classes.  Float64 (absolute values have no rational",
        "    form -- disclosed); frequencies m/(qq') exact.",
        "  M-OBS-2 (position-dependent, SIGNED): X(m; W) = sum over ordered",
        "    pairs mapping to class m of c(q,j) c(q',j') Re S_W(m/(qq')),",
        "    S_W(theta) = e(theta k) D_K(theta) for W = (k, k+K].  Statistics",
        "    per segment (registered BEFORE measurement): S1 = X(1)+X(-1);",
        "    SL5 = sum_{1<=|m|<=5} X(m); STOT = sum_m X(m); T = sum_m |X(m)|;",
        "    R1 = S1/T; RL5 = SL5/T.",
        "    EXACTNESS TIE (selftest, STOP on fail): STOT == 2 * sum_{q<q'}",
        "    E_{q,q'}(W) where E_{q,q'}(W) = sum_{m in W} eps_q(m) eps_q'(m)",
        "    is the EXACT Fraction pair term (L52 convention, circle_sum T4);",
        "    match to 1e-9*max(1,|value|) on every segment; plus 40 random",
        "    (pair,j,j') closed-form-vs-brute checks per scale at 1e-9.",
        "  Populations at A in {17,19}: the 12 exact defect windows (6+6,",
        "    DEFECT_R lists, re-verified zero-clean before use), segment",
        "    centered: k = r - (K - g)//2, g = G(A)-1, K = 49/61; vs 20",
        "    typical segments per scale, k uniform in [0, P_A), seed",
        "    20260710 + 100 + A.  ('matched' = same K, same scale; no other",
        "    matching -- disclosed.)",
        "  REGISTERED QUESTION: does the defect vicinity overweight",
        "    small-|m| (Farey-adjacent) interference?  Registered comparison:",
        "    z(stat) = (defect mean - typical mean)/typical sd (ddof=1) for",
        "    stat in {S1, SL5, STOT, T, R1, RL5}; any |z| >= 3 on R1 or RL5",
        "    (the m-profile mass RATIOS) fires the conditional foil below.",
        "",
        "s3 SHIFTED-CONVOLUTION TABLE + ENSEMBLE KLOOS PROBE (the measured",
        "  half of the dispersion-blindness law; EXACT-MEASURED, no verdicts",
        "  beyond the registered expectation check):",
        "  S3-T1 deviation table: R(d; W) = #{m in W : Clean m and Clean m+d}",
        "    on ceiling segments W (K = ceil(A^2/6)), complete-side prediction",
        "    pred(d) = K * prod_q (q - c_q(d))/q (EXACT Fraction; grounded:",
        "    the full-period mean of R(d;.) equals pred(d) exactly -- brute-",
        "    verified at A=13 for d in {1,7,30,100}, STOP on fail).  Ensemble:",
        "    200 segments per A in {13,17,23}, k uniform in [0,P_A), seed",
        "    20260710 + 200 + A.  Table by d = 0..100: pred, mean dev, sd,",
        "    sampling z = mean_dev/(sd/sqrt(n)), min, max.  |z| >= 3 entries",
        "    are counted and listed.  DISCLOSED: the 101 cells of one scale",
        "    share the SAME segment draw, so deviations across d are strongly",
        "    correlated (a clean-poor draw depresses every R(d) at once);",
        "    the independent-cell chance figure (~0.8 hits at 3 sigma over",
        "    303 cells) is a heuristic only; deviations are sampling",
        "    fluctuations, the identity fixes the mean.",
        "  S3-T2 ensemble kloos probe (stage-D extension, REGISTERED here):",
        "    scales A in {17,19}; segments = the 6 defect-centered + the 20",
        "    typical of s2 (same starts, same K).  Second-moment data per",
        "    segment: M2(W) = sum_{d=1..100} (R(d;W) - pred(d))^2.  Complete-",
        "    side features at u = k mod q (k = segment start): K_q(W) =",
        "    kloos_q(u*inv2_q, u*inv2_q), inv2_q = (q+1)/2 (the circle_sum T4",
        "    comparand; u = 0 degenerates to kloos(0,0) = q-1, marked deg).",
        "    Fits (least squares): pooled n=26: M2 ~ [1, K_q ... for all",
        "    clocks q <= A]; typical-only n=20 with defect residuals",
        "    reported; R^2, jackknife leave-one-out coefficient ranges and",
        "    sign-stability -- reporting AS IN stage D.  Group means of M2",
        "    (defect vs typical) + z reported.",
        "    REGISTERED EXPECTATION: NO stable re-expression -- confirmed",
        "    unless BOTH pooled R^2 >= 0.9 AND all coefficients jackknife-",
        "    sign-stable.  No other verdict vocabulary.",
        "",
        "FOIL NOTE (registered): the pure identities (s0 selftests, the s1",
        "  counts and bounds, the s3 deviation-table identity layer) need NO",
        "  foil -- they are weight-independent counting/identity statements",
        "  (honest exclusion).  The NEW measured observables -- the s2",
        "  m-profile mass ratios R1, RL5 on defect vs typical segments -- get",
        "  a gate_g3 foil run ONLY IF the registered trigger fires (any",
        "  |z| >= 3 on R1 or RL5 at A in {17,19}).  Conditional protocol,",
        "  spelled out now: observable I = the triggering statistic over the",
        "  26 segments of that scale; load L = lambda-sum over the segment's",
        "  Clean survivors, lambda(m) = twin indicator [6m-1 and 6m+1 both",
        "  prime] (sieve-exact); 200 sigma_W permutations + 200 sigma_I",
        "  lambda-resamples over the pooled survivor lambdas; foil_row",
        "  VERBATIM from tools/betti_portrait_harness.py; rng seed 20260710+7;",
        "  report R, zW, zI ONLY -- no threshold moves, no new statistics.",
        "  EXPECTATION: BLIND (L52d genus -- the linear character layer was",
        "  parity-blind, L38; whether difference-frequency interference",
        "  carries defect structure is not predicted by the ledger).",
        "",
        "DISCIPLINE: STAGE_TIME_CAP = 5400 s per stage.  Registered fallback",
        "  if a measured projection exceeds the remaining stage budget:",
        "  ensemble knobs (s3 deviation ensemble 200/A; s2-s3 typical 20 per",
        "  scale) are HALVED repeatedly, each halving logged, until the",
        "  projection fits; the s1 A=23 full-period scan (the only heavy",
        "  non-ensemble task) degrades to bound-only with the true count",
        "  labeled UNSCANNED-BUDGET.  Projections come from timing probes",
        "  logged before the task runs.  Tolerances: byte-exact wherever the",
        "  word appears; float routes 1e-9 relative to max(1, |value|).",
        "  STOP rule: any s0 assert, any registered byte-check, any s2/s3",
        "  exactness-tie selftest failure -> STOP exit 1.  Measured outcomes",
        "  (z values, ratios, R^2) never STOP.",
    ]:
        log(s)


# ------------------------------------------------------------------------- s0

def st_a():
    for q in clocks(43):
        iq = i6(q)
        set_direct = set(d for d in range(q) if cq_direct(q, d) == 3)
        set_2i6 = {(2 * iq) % q, (-2 * iq) % q}
        set_3d = set(d for d in range(q) if (3 * d) % q in (1, q - 1))
        assert set_direct == set_2i6 == set_3d, "ST-A overlap sets at q=%d" % q
        for d in range(q):
            assert cq_direct(q, d) == cq_tri(q, d), \
                "ST-A trichotomy at q=%d d=%d" % (q, d)
        assert cq_direct(q, 0) == 2
    log("ST-A c_q trichotomy: direct |{i6,-i6} u {i6-d,-i6-d}| == registered")
    log("  2/3/4 trichotomy for EVERY clock q <= 43, EVERY d in [0,q);")
    log("  overlap-1 class {d:|U|=3} == {+-2*i6} == {d: 3d=+-1 mod q} as sets")
    log("  at every clock (the class derivation CONFIRMED independently) -- PASS")


def st_b():
    for A in (5, 7, 11, 13):
        P = period(A)
        cl = clean_bool(A, 0, P)
        drange = range(P) if A in (5, 7) else range(100)
        for d in drange:
            direct = int(np.sum(cl & np.roll(cl, -d)))
            assert direct == paircorr_crt(A, d), \
                "ST-B pairCorr mismatch A=%d d=%d" % (A, d)
        log("ST-B A=%2d (P=%7d): pairCorr direct scan == CRT product"
            " prod(q - c_q(d))" % (A, P))
        log("  byte-exact for %s -- PASS"
            % ("ALL d in [0,P)" if A in (5, 7) else "all d < 100"))
    log("  spot: pairCorr(13,0) = %d = 3*5*9*11 (the L34 survivor count)"
        % paircorr_crt(13, 0))


def st_c():
    for A in (5, 7, 11, 13):
        P = period(A)
        for g in (2, 5, 11):
            mt = main_term(A, g)
            cl = clean_bool(A, 0, P + g + 1)
            cs = np.concatenate([[0], np.cumsum(cl.astype(np.int64))])
            cc = cs[g + 1: P + g + 1] - cs[1: P + 1]
            scc = int(cc.sum())
            scc2 = int((cc.astype(np.int64) ** 2).sum())
            va = Fraction(scc2) - 2 * mt * scc + P * mt * mt
            vb = var_sum_exact(A, g)
            assert va == vb, "ST-C (a)!=(b) at A=%d g=%d" % (A, g)
            c = np.fft.fft(cl[:P].astype(np.float64)) / P
            p = np.arange(1, P)
            th = p / P
            w2 = (np.sin(np.pi * g * th) / np.sin(np.pi * th)) ** 2
            vc = P * float((np.abs(c[1:]) ** 2 * w2).sum())
            dev = abs(vc - float(va)) / max(1.0, float(va))
            assert dev <= 1e-9, "ST-C (c) dev=%.2e at A=%d g=%d" % (dev, A, g)
        log("ST-C A=%2d: VarSum direct == pair-correlation formula (Fraction,"
            " byte-exact)" % A)
        log("  == spectral P*sum|c(p)|^2|W_g|^2 (<=1e-9 rel) at g in {2,5,11}"
            " -- PASS")
    log("  spot exact: VarSum(13,11) = %s (~%.6f), mainTerm = %s"
        % (var_sum_exact(13, 11), float(var_sum_exact(13, 11)),
           main_term(13, 11)))


def scan_defect_starts(A):
    """All r in [0,P) with (r, r+G-2+1] fully struck; also max-run check."""
    P = period(A)
    g = G_KERNEL[A] - 1
    cl = clean_bool(A, 0, P + 2 * g + 4)
    cs = np.concatenate([[0], np.cumsum((~cl).astype(np.int64))])
    W = cs[g + 1: P + g + 1] - cs[1: P + 1]
    starts = [int(r) for r in np.flatnonzero(W == g)]
    W1 = cs[g + 2: P + g + 2] - cs[1: P + 1]
    assert int(W1.max()) == g, "struck run of length G found at A=%d" % A
    return starts


def st_d():
    # L34
    n1485 = int(clean_bool(13, 0, 5005).sum())
    assert n1485 == 1485 == 3 * 5 * 9 * 11, "L34 survivor count"
    log("ST-D L34: #{r in [0,5005): Clean(13,r)} = %d = 3*5*9*11 -- PASS" % n1485)
    # G(A) scans A <= 19
    for A in (5, 7, 11, 13, 17, 19):
        P = period(A)
        cl = clean_bool(A, 0, 2 * P)
        struck = ~cl
        # max run of struck over one period (window into 2P to catch wraps)
        best = run = 0
        for v in struck[:P + G_KERNEL[A] + 2]:
            run = run + 1 if v else 0
            best = max(best, run)
        assert best == G_KERNEL[A] - 1, \
            "G(%d): max struck run %d != G-1" % (A, best)
        log("ST-D G(%2d) = %2d: full-period max struck run == %2d == G-1 -- PASS"
            % (A, G_KERNEL[A], best))
    # defect windows: scans at 17/19
    d17 = scan_defect_starts(17)
    assert len(d17) == 20 and d17[0] == 117 and 502 in d17, "A=17 scan calib"
    assert all(r in d17 for r in DEFECT_R[17])
    d19 = scan_defect_starts(19)
    assert len(d19) == 20 and d19[0] == 110, "A=19 scan calib"
    assert all(r in d19 for r in DEFECT_R[19])
    log("ST-D A=17 scan: 20 defect starts, first r=117, 502 present, all 6")
    log("  DEFECT_R-listed present; A=19 scan: 20 starts, first r=110, all 6")
    log("  listed present -- PASS (pratt_wing S7 calibration reproduced)")
    # witnesses A >= 23
    nw = 0
    for A in (23, 29, 31, 37, 41, 43):
        G = G_KERNEL[A]
        for r in DEFECT_R[A]:
            assert is_clean_int(A, r) and is_clean_int(A, r + G), \
                "endpoint not clean at A=%d r=%d" % (A, r)
            assert all(not is_clean_int(A, r + t) for t in range(1, G)), \
                "window not fully struck at A=%d r=%d" % (A, r)
            nw += 1
    assert 20 + 20 + nw == 50, "expected 50 defect windows"
    log("ST-D DEFECT_R witnesses A in {23,29,31,37,41,43}: all %d windows" % nw)
    log("  (r, r+G-1] fully struck, r and r+G clean (certifies G(A) >= table;")
    log("  upper side = Lean kernel gates, phase_cover_run1.log) -- PASS")
    log("ST-D 50 defect windows CONFIRMED: 20 + 20 + %d -- PASS" % nw)
    return d17, d19


def st_e():
    N = 10 ** 6
    t0 = time.time()
    r2 = np.zeros(2 * N + 1, dtype=np.int64)   # r2 up to 2N for carry bound
    x = 0
    while x * x <= 2 * N:
        rem = 2 * N - x * x
        ymax = math.isqrt(rem)
        ys = np.arange(0, ymax + 1, dtype=np.int64)
        w = np.full(ys.size, 4, dtype=np.int64)
        if x == 0:
            w //= 2
        w[0] //= 2
        if x == 0:
            w[0] = 1
        np.add.at(r2, x * x + ys * ys, w)
        x += 1
    assert r2[0] == 1 and r2[1] == 4 and r2[2] == 4 and r2[3] == 0 \
        and r2[25] == 12, "r2 lattice anchors"
    r2 = r2[:N + 1]
    smax, ssum = int(r2.max()), int(r2.sum())
    assert smax * ssum < 2 ** 63, "Kronecker carry guard"
    a = int.from_bytes(b"".join(int(v).to_bytes(8, "little") for v in r2),
                       "little")
    c = a * a
    raw = c.to_bytes(8 * (2 * N + 1) + 8, "little")
    r4 = np.frombuffer(raw[: 8 * (N + 1)], dtype="<u8").astype(np.int64)
    assert r4[1] == 8 and r4[3] == 32, "r4 anchors"
    sig = np.zeros(N + 1, dtype=np.int64)
    for d in range(1, N + 1):
        sig[d::d] += d
    odd = np.arange(1, N + 1, 2)
    bad = np.flatnonzero(r4[odd] != 8 * sig[odd])
    assert bad.size == 0, "r4 != 8 sigma at odd n=%d" % (int(odd[bad[0]])
                                                         if bad.size else -1)
    log("ST-E r4 = 8*sigma: r2 by exact lattice count (anchors 1,4,4,0;")
    log("  r2(25)=12); r4 = r2*r2 by EXACT base-2^64 Kronecker convolution")
    log("  (carry guard max_r2 * sum_r2 = %d * %d < 2^63); sigma by" % (smax, ssum))
    log("  divisor sieve; r4(n) == 8*sigma(n) for ALL %d odd n <= 1e6," % odd.size)
    log("  0 mismatches (spot r4(1)=8, r4(3)=32, r4(999999)=%d=8*%d)"
        % (int(r4[999999]), int(sig[999999])))
    log("  -- PASS (%.1fs) -- the gated-Jacobi anchor holds" % (time.time() - t0))


def st_f():
    t0 = time.time()
    ps = [p for p in primes_upto(10 ** 5 - 1) if p % 3 == 1]
    nrep = 0
    for p in ps:
        rep = False
        b = 1
        while 27 * b * b < p:
            t = p - 27 * b * b
            s = math.isqrt(t)
            if s * s == t:
                rep = True
                break
            b += 1
        cub = pow(2, (p - 1) // 3, p) == 1
        assert rep == cub, "Cornacchia gate FAILED at p=%d (rep=%s cub=%s)" \
            % (p, rep, cub)
        nrep += rep
    log("ST-F Cornacchia gate: p = a^2 + 27 b^2 solvable <=> 2^((p-1)/3) = 1")
    log("  mod p, checked on ALL %d primes p = 1 mod 3 below 1e5:" % len(ps))
    log("  0 failures; %d representable (~1/3 as the cubic-class heuristic"
        % nrep)
    log("  expects) -- PASS (%.1fs) -- the sphere harness cubic probe is"
        % (time.time() - t0))
    log("  pre-validated")


def s0():
    section("s0 -- SELFTESTS (closed list ST-A..ST-F; ANY failure = STOP exit 1)")
    t0 = time.time()
    st_a()
    st_b()
    st_c()
    d17, d19 = st_d()
    st_e()
    st_f()
    log("s0 ALL SELFTESTS PASS")
    stage_close("s0", t0)
    return d17, d19


# ------------------------------------------------------------------------- s1

def defect_counts_scanned(A, gs, t0_stage):
    """Exact N(g) = #{k < P : cleanCount(A,k,g) = 0} for each g in gs."""
    P = period(A)
    gmax = max(gs)
    n = P + gmax + 1
    if P > 10 ** 7:   # probe + registered budget fallback
        tp = time.time()
        clean_bool(A, 0, 1 << 22)
        per = (time.time() - tp) / (1 << 22)
        proj = per * n * 1.5 + 8.0
        rem = STAGE_TIME_CAP - (time.time() - t0_stage)
        log("  budget probe A=%d: projected scan %.0fs vs remaining %.0fs"
            % (A, proj, rem))
        if proj > rem:
            log("  FALLBACK (registered): A=%d scan degraded to bound-only;"
                " true counts labeled UNSCANNED-BUDGET" % A)
            return None
    cl = clean_bool(A, 0, n)
    cs = np.empty(n + 1, dtype=np.int64)
    cs[0] = 0
    np.cumsum(cl, dtype=np.int64, out=cs[1:])
    del cl
    out = {}
    for g in gs:
        cnt = 0
        chunk = 1 << 23
        for k0 in range(0, P, chunk):
            k1 = min(P, k0 + chunk)
            W = cs[k0 + g + 1: k1 + g + 1] - cs[k0 + 1: k1 + 1]
            cnt += int((W == 0).sum())
        out[g] = cnt
    return out


def s1():
    section("s1 -- THE MARKOV-GAP TABLE (exact counts vs the dispersion bound)")
    t0 = time.time()
    log("N(g) = #{k < P : cleanCount = 0} exact scan; B(g) = VarSum/mainTerm^2")
    log("exact Fraction (pair-correlation formula, ST-C-validated); a defect")
    log("window has windowFluct^2 = mainTerm^2, so N(g) <= B(g) (Markov).")
    log("")
    hdr = ("  A   g  label      true N(g)   bound B(g)      B/N      "
           "mainTerm    VarSum")
    log(hdr)
    rows = []
    for A in (5, 7, 11, 13, 17, 19, 23):
        G = G_KERNEL[A]
        sharp = (A * A) // 14
        gs = [G - 1, G]
        labels = {G - 1: "G-1", G: "G"}
        if sharp not in gs and sharp >= 1:
            gs.append(sharp)
            labels[sharp] = "sharp"
        scanned = defect_counts_scanned(A, gs, t0)
        for g in sorted(gs):
            mt = main_term(A, g)
            vs = var_sum_exact(A, g)
            bound = vs / (mt * mt)
            if scanned is None:
                truev, tlab = None, "UNSCANNED-BUDGET"
            else:
                truev, tlab = scanned[g], "scan"
            if g == G - 1 and truev is not None:
                assert truev == KNOWN_TRUE[A], \
                    "N(G-1) byte-check failed at A=%d: %d != %d" \
                    % (A, truev, KNOWN_TRUE[A])
                tlab = "scan==census"
            if g == G and truev is not None:
                assert truev == 0, "kernel gap contradicted at A=%d" % A
                tlab = "scan==kernel"
            if g > G and truev is not None:
                assert truev == 0, "monotone zero violated at A=%d g=%d" % (A, g)
            ratio = ("%10.2f" % (float(bound) / truev)) if truev \
                else ("   inf(N=0)" if truev == 0 else "        --")
            log("  %2d %3d  %-6s  %10s  %12.4f %s  %9.4f  %12.4f"
                % (A, g, labels[g],
                   ("%d" % truev) if truev is not None else "--",
                   float(bound), ratio, float(mt), float(vs)))
            log("        [%s] exact B = %s" % (tlab, bound))
            rows.append((A, g, labels[g], truev, bound))
    # A = 29, 31 -- solver-data / bound-only tier
    for A, true_gm1, src in ((29, 2, "gap_extremal_run1.log:28 FULL-period "
                              "scan"), (31, None, "census incomplete (1 "
                              "witness known, phase_cover); bound-only")):
        G = G_KERNEL[A]
        sharp = (A * A) // 14
        for g, lab in ((G - 1, "G-1"), (G, "G"), (sharp, "sharp")):
            mt = main_term(A, g)
            bound = var_sum_exact(A, g) / (mt * mt)
            if g == G - 1:
                truev = true_gm1
            else:
                truev = 0   # g >= G: zero by the kernel gap G(A) (labeled)
            ratio = ("%10.2f" % (float(bound) / truev)) if truev \
                else ("   inf(N=0)" if truev == 0 else "        --")
            log("  %2d %3d  %-6s  %10s  %12.4f %s  %9.4f"
                % (A, g, lab,
                   ("%d" % truev) if truev is not None else "--",
                   float(bound), ratio, float(mt)))
            src_lab = (src if g == G - 1
                       else "zero via kernel gap G(%d)=%d (g >= G)" % (A, G))
            log("        [%s]" % src_lab)
            rows.append((A, g, lab, truev, bound))
    log("")
    log("READING (measured): the dispersion bound B at the wall g = G(A):")
    for A in (5, 7, 11, 13, 17, 19, 23, 29, 31):
        b = [r for r in rows if r[0] == A and r[2] == "G"][0][4]
        log("  A=%2d: B(G) = %10.2f  %s" %
            (A, float(b), "< 1 -- Markov ALONE sees the wall here"
             if b < 1 else ">= 1 -- Markov is blind to the wall"))
    g1 = [(r[0], float(r[4]) / r[3]) for r in rows
          if r[2] == "G-1" and r[3]]
    log("  overshoot at g = G-1 (B/N): %s"
        % "  ".join("A=%d:%.1fx" % t for t in g1))
    stage_close("s1", t0)
    return rows


# ------------------------------------------------------------------------- s2

def mode_c(q):
    j = np.arange(1, q, dtype=np.int64)
    return -(2.0 / q) * np.cos(2 * np.pi * ((j * i6(q)) % q) / q)


def build_pairs(A):
    """Ordered clock pairs with per-pair (m matrix, signed coeff product)."""
    Q = clocks(A)
    cs = {q: mode_c(q) for q in Q}
    pairs = []
    for q in Q:
        for qp in Q:
            if q == qp:
                continue
            j = np.arange(1, q, dtype=np.int64)[:, None]
            jp = np.arange(1, qp, dtype=np.int64)[None, :]
            m = j * qp - jp * q
            cprod = cs[q][:, None] * cs[qp][None, :]
            pairs.append((q, qp, m, cprod))
    maxM = max(int(np.abs(p[2]).max()) for p in pairs)
    return pairs, maxM


def dirichlet_mag(m, QQ, K):
    th = m / QQ
    return np.abs(np.sin(np.pi * K * th) / np.sin(np.pi * th))


def ceiling_mass_table(A, K):
    pairs, maxM = build_pairs(A)
    mass = np.zeros(maxM + 1)
    for q, qp, m, cprod in pairs:
        contrib = np.abs(cprod) * dirichlet_mag(m, q * qp, K)
        np.add.at(mass, np.abs(m).ravel(), contrib.ravel())
    total = float(mass.sum())
    bands = [(2, 5), (6, 10), (11, 20), (21, 50), (51, 200), (201, maxM)]
    log("  A=%2d K=%3d clocks=%d ordered pairs=%d max|m|=%d" %
        (A, K, len(clocks(A)), len(pairs), maxM))
    log("    total cross-term mass = %.6f ; |m|=1 (Farey-adjacent) mass ="
        " %.6f  share %.4f" % (total, mass[1], mass[1] / total))
    for lo, hi in bands:
        if lo > maxM:
            continue
        s = float(mass[lo: min(hi, maxM) + 1].sum())
        log("    band |m| in [%3d,%4d]: mass %10.6f  share %.4f"
            % (lo, hi, s, s / total))
    top = np.argsort(-mass)[:10]
    log("    top-10 |m| classes: %s"
        % "  ".join("%d:%.4f" % (int(i), mass[int(i)]) for i in top))
    return mass, total


def eps_pair_exact(A, k, K):
    """2 * sum_{q<q'} E_{q,q'}(W), E = sum_{m in W} eps_q eps_q' EXACT."""
    Q = clocks(A)
    sflags = {}
    t = np.arange(1, K + 1, dtype=np.int64)
    for q in Q:
        iq = i6(q)
        r = (k + t) % q
        sflags[q] = ((r == iq) | (r == (q - iq) % q)).astype(np.int64)
    tot = Fraction(0)
    for a in range(len(Q)):
        for b in range(a + 1, len(Q)):
            q, qp = Q[a], Q[b]
            V = int(((q * sflags[q] - 2) * (qp * sflags[qp] - 2)).sum())
            tot += Fraction(V, q * qp)
    return 2 * tot


def segment_signed_profile(A, K, k, pairs, maxM):
    Xm = np.zeros(2 * maxM + 1)
    for q, qp, m, cprod in pairs:
        QQ = q * qp
        red = ((m % QQ) * (k % QQ)) % QQ
        phase = 2 * np.pi * red / QQ + np.pi * m * (K + 1) / QQ
        ReS = np.cos(phase) * np.sin(np.pi * K * m / QQ) / np.sin(np.pi * m / QQ)
        np.add.at(Xm, (m + maxM).ravel(), (cprod * ReS).ravel())
    return Xm


def seg_stats(Xm, maxM):
    S1 = Xm[maxM + 1] + Xm[maxM - 1]
    a = np.abs(np.arange(-maxM, maxM + 1))
    SL5 = float(Xm[(a >= 1) & (a <= 5)].sum())
    STOT = float(Xm.sum())
    T = float(np.abs(Xm).sum())
    return dict(S1=float(S1), SL5=SL5, STOT=STOT, T=T,
                R1=float(S1) / T, RL5=SL5 / T)


def spot_brute(A, K, k, pairs, rng):
    """40 random (pair, j, j'): closed form vs brute sum -- 1e-9."""
    worst = 0.0
    for _ in range(40):
        q, qp, m, cprod = pairs[int(rng.integers(0, len(pairs)))]
        jx = int(rng.integers(0, m.shape[0]))
        jy = int(rng.integers(0, m.shape[1]))
        mm = int(m[jx, jy])
        QQ = q * qp
        brute = sum(math.cos(2 * math.pi * ((mm * (k + t)) % QQ) / QQ)
                    for t in range(1, K + 1))
        red = ((mm % QQ) * (k % QQ)) % QQ
        closed = (math.cos(2 * math.pi * red / QQ + math.pi * mm * (K + 1) / QQ)
                  * math.sin(math.pi * K * mm / QQ)
                  / math.sin(math.pi * mm / QQ))
        worst = max(worst, abs(brute - closed))
    assert worst <= 1e-9, "spot brute closed-form dev %.2e" % worst
    return worst


def s2(d17, d19):
    section("s2 -- THE FAREY m-CLASS PROFILE (level-1 x level-1 cross-terms)")
    t0 = time.time()
    log("M-OBS-1: position-independent ceiling-segment mass profile by |m|")
    log("(mass = |c(q,j)|*|c(q',j')|*|D_K(m/(qq'))| over ordered clock pairs):")
    for A in (13, 17, 23, 31, 43):
        ceiling_mass_table(A, CEIL_K[A])
    log("")
    log("M-OBS-2: SIGNED profiles X(m;W) on defect-centered vs typical")
    log("segments (statistics registered above; exactness tie per segment).")
    triggers = []
    seg_store = {}
    for A, dlist in ((17, DEFECT_R[17]), (19, DEFECT_R[19])):
        K = CEIL_K[A]
        g = G_KERNEL[A] - 1
        P = period(A)
        pairs, maxM = build_pairs(A)
        # re-verify defect windows before use (registered)
        for r in dlist:
            assert is_clean_int(A, r) and is_clean_int(A, r + g + 1)
            assert all(not is_clean_int(A, r + t) for t in range(1, g + 1))
        ks_def = [r - (K - g) // 2 for r in dlist]
        rng = np.random.default_rng(SEED + 100 + A)
        ks_typ = [int(v) for v in rng.integers(0, P, size=20)]
        wb = spot_brute(A, K, ks_def[0], pairs,
                        np.random.default_rng(SEED + 300 + A))
        log("  A=%d K=%d g=%d: 6 defect windows re-verified (zero clean" % (A, K, g))
        log("    centers); defect segment starts k = r - %d: %s"
            % ((K - g) // 2, ks_def))
        log("    typical starts (seed %d): %s" % (SEED + 100 + A, ks_typ))
        log("    spot brute vs closed form (40 samples): max dev %.2e -- PASS" % wb)
        stats = {"defect": [], "typical": []}
        worst_tie = 0.0
        for kind, ks in (("defect", ks_def), ("typical", ks_typ)):
            for k in ks:
                Xm = segment_signed_profile(A, K, k, pairs, maxM)
                st = seg_stats(Xm, maxM)
                exact = eps_pair_exact(A, k, K)
                dev = abs(st["STOT"] - float(exact)) / max(1.0,
                                                           abs(float(exact)))
                worst_tie = max(worst_tie, dev)
                assert dev <= 1e-9, \
                    "exactness tie FAILED at A=%d k=%d dev=%.2e" % (A, k, dev)
                st["k"] = k
                st["exact"] = exact
                stats[kind].append(st)
        log("    exactness tie: STOT == 2*sum_{q<q'} E_{q,q'}(W) (exact")
        log("    Fractions) on all 26 segments, max rel dev %.2e -- PASS"
            % worst_tie)
        log("    per-segment table (%s):" %
            "S1, SL5, STOT, T, R1=S1/T, RL5=SL5/T")
        for kind in ("defect", "typical"):
            for st in stats[kind]:
                log("      %-7s k=%8d  S1=%+9.5f SL5=%+9.5f STOT=%+9.5f"
                    "  T=%9.5f  R1=%+8.5f RL5=%+8.5f"
                    % (kind, st["k"], st["S1"], st["SL5"], st["STOT"],
                       st["T"], st["R1"], st["RL5"]))
        log("    spot exact STOT (defect #1): %s" % stats["defect"][0]["exact"])
        zrow = []
        for name in ("S1", "SL5", "STOT", "T", "R1", "RL5"):
            dv = np.array([st[name] for st in stats["defect"]])
            tv = np.array([st[name] for st in stats["typical"]])
            sd = tv.std(ddof=1)
            z = (dv.mean() - tv.mean()) / sd if sd > 1e-15 else float("nan")
            zrow.append((name, dv.mean(), tv.mean(), sd, z))
            if abs(z) >= 3:
                ANOMALIES.append(("s2 A=%d %s defect-vs-typical" % (A, name),
                                  "z", z))
            if name in ("R1", "RL5") and abs(z) >= 3:
                triggers.append((A, name, z))
        log("    defect-vs-typical (z = (mean_d - mean_t)/sd_t, n_d=6 n_t=20):")
        for name, md, mt_, sd, z in zrow:
            log("      %-4s  defect mean %+9.5f  typical mean %+9.5f  sd_t"
                " %8.5f  z = %+6.2f%s"
                % (name, md, mt_, sd, z, "  <-- |z|>=3" if abs(z) >= 3 else ""))
        seg_store[A] = dict(ks_def=ks_def, ks_typ=ks_typ, K=K, stats=stats)
    # conditional foil (registered)
    log("")
    if not triggers:
        log("  CONDITIONAL FOIL TRIGGER: no |z| >= 3 on R1 or RL5 at either")
        log("  scale -- the gate_g3 foil run is NOT fired (registered")
        log("  conditional; the registration stands, nothing was run).")
    else:
        log("  CONDITIONAL FOIL TRIGGER FIRED: %s" %
            ["A=%d %s z=%+.2f" % t for t in triggers])
        run_conditional_foil(triggers, seg_store)
    stage_close("s2", t0)
    return seg_store, triggers


def run_conditional_foil(triggers, seg_store):
    """Registered gate_g3 conditional foil: foil_row VERBATIM from BP."""
    lim = 10 ** 7 + 10
    sieve = np.ones(lim, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(lim ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    for A, name, ztrig in triggers:
        ss = seg_store[A]
        K = ss["K"]
        ks = ss["ks_def"] + ss["ks_typ"]
        I = np.array([st[name] for st in
                      ss["stats"]["defect"] + ss["stats"]["typical"]])
        surv, seg_of = [], []
        for si, k in enumerate(ks):
            for t in range(1, K + 1):
                if is_clean_int(A, k + t):
                    surv.append(k + t)
                    seg_of.append(si)
        surv = np.array(surv, dtype=np.int64)
        seg_of = np.array(seg_of, dtype=np.int64)
        lam = (sieve[6 * surv - 1] & sieve[6 * surv + 1]).astype(np.float64)
        L = np.bincount(seg_of, weights=lam, minlength=len(ks))
        rng = np.random.default_rng(SEED)
        Ln = np.empty((200, len(ks)))
        for t in range(200):
            Ln[t] = np.bincount(seg_of, weights=rng.choice(lam, size=lam.size),
                                minlength=len(ks))
        st = BP.foil_row(I, L, Ln, np.random.default_rng(SEED + 7))
        log("    FOIL A=%d obs=%s: R=%+8.4f zW=%+6.1f zI=%+6.1f n=%d %s"
            % (A, name, st["R"], st["zW"], st["zI"], st["n"], st["note"]))
        for zn in ("zW", "zI"):
            if abs(st[zn]) >= 3:
                ANOMALIES.append(("s2 foil A=%d %s" % (A, name), zn, st[zn]))


# ------------------------------------------------------------------------- s3

def pred_fraction(A, d, K):
    v = Fraction(K)
    for q in clocks(A):
        v *= Fraction(q - cq_tri(q, d), q)
    return v


def seg_R_matrix(A, ks, K, dmax=100):
    """R[i, d] = #{m in (k_i, k_i+K] : Clean m and Clean m+d}, d = 0..dmax."""
    ks = np.asarray(ks, dtype=np.int64)
    t = np.arange(1, K + dmax + 1, dtype=np.int64)
    m = ks[:, None] + t[None, :]
    cl = np.ones(m.shape, dtype=bool)
    for q in clocks(A):
        iq = i6(q)
        r = m % q
        cl &= (r != iq) & (r != (q - iq) % q)
    R = np.empty((ks.size, dmax + 1), dtype=np.int64)
    for d in range(dmax + 1):
        R[:, d] = (cl[:, :K] & cl[:, d: d + K]).sum(axis=1)
    return R


def s3(seg_store):
    section("s3 -- SHIFTED-CONVOLUTION TABLE + ENSEMBLE KLOOS PROBE")
    t0 = time.time()
    # grounding: full-period mean of R(d;.) == pred(d) exactly at A=13
    A, K = 13, CEIL_K[13]
    P = period(A)
    cl = clean_bool(A, 0, P + K + 101)
    for d in (1, 7, 30, 100):
        tot = 0
        for tt in range(1, K + 1):
            tot += int((cl[tt: tt + P] & cl[tt + d: tt + d + P]).sum())
        pf = pred_fraction(A, d, K)
        assert Fraction(tot, P) == pf, "full-period grounding failed d=%d" % d
    log("grounding: sum_{k<P} R(d;k) == P * pred(d) EXACT at A=13 for")
    log("d in {1,7,30,100} (the complete side is the true segment mean) -- PASS")
    log("")
    log("S3-T1 deviation table: 200 segments/A (seeds %d+200+A), K=ceil(A^2/6);"
        % SEED)
    log("dev = R(d;W) - pred(d); z = mean_dev/(sd/sqrt(200)) (sampling z).")
    nz3 = []
    for A in (13, 17, 23):
        K = CEIL_K[A]
        P = period(A)
        rng = np.random.default_rng(SEED + 200 + A)
        nseg = 200
        tp = time.time()
        Rp = seg_R_matrix(A, [int(v) for v in rng.integers(0, P, size=10)], K)
        per = (time.time() - tp) / 10.0
        nseg = halve_to_fit(nseg, per, STAGE_TIME_CAP - (time.time() - t0),
                            "s3 deviation ensemble A=%d" % A)
        rng = np.random.default_rng(SEED + 200 + A)   # re-draw, registered seed
        ks = [int(v) for v in rng.integers(0, P, size=nseg)]
        R = seg_R_matrix(A, ks, K)
        log("")
        log("  A=%2d K=%3d n=%d segments:" % (A, K, nseg))
        log("      d  pred      mean_dev   sd      z      min    max")
        for d in range(0, 101):
            pf = float(pred_fraction(A, d, K))
            dev = R[:, d] - pf
            sd = dev.std(ddof=1)
            z = dev.mean() / (sd / math.sqrt(nseg)) if sd > 1e-15 else 0.0
            mark = ""
            if abs(z) >= 3:
                nz3.append((A, d, z))
                mark = "  <-- |z|>=3"
            log("    %5d  %8.4f  %+8.4f  %6.3f  %+6.2f  %+5.0f  %+5.0f%s"
                % (d, pf, dev.mean(), sd, z, dev.min(), dev.max(), mark))
    log("")
    log("  |z| >= 3 cells: %d of 303: %s"
        % (len(nz3),
           (["A=%d d=%d z=%+.2f" % t for t in nz3] if nz3 else "none")))
    log("  (registered disclosure: cells within a scale share one segment")
    log("  draw -- correlated across d; ~0.8 independent-cell hits expected")
    log("  at 3 sigma is heuristic only; the identity fixes the mean, so")
    log("  these are draw-level sampling fluctuations, not d-structure.)")
    for A, d, z in nz3:
        ANOMALIES.append(("s3 deviation A=%d d=%d" % (A, d), "z", z))
    # ---- S3-T2 ensemble kloos probe
    log("")
    log("S3-T2 ensemble kloos probe (stage-D extension; registered):")
    log("M2(W) = sum_{d=1..100} (R(d;W)-pred(d))^2; features K_q(W) =")
    log("kloos_q(u*inv2_q, u*inv2_q), u = k mod q (deg -> q-1 at u=0);")
    log("kloos wiring check vs circle_sum T1(c) bridge below.")
    for q in clocks(19):
        inv2q = (q + 1) // 2
        assert (2 * inv2q) % q == 1
        kv = kloos_val(q, 0, 0)
        assert abs(kv - (q - 1)) <= 1e-9
        # circle_sum T1(c) diagonal energy: sum_{u!=0} kloos(u/2,u/2)^2
        # = q^2 - 2q - 1 (the bridge constant; wiring check, STOP on fail)
        en = 0.0
        for u in range(1, q):
            kv = kloos_val(q, (u * inv2q) % q, (u * inv2q) % q)
            assert abs(kv.imag) <= 1e-9
            en += kv.real ** 2
        assert abs(en - (q * q - 2 * q - 1)) <= 1e-9 * q * q, \
            "kloos diag energy at q=%d" % q
    log("  kloos wiring: kloos(0,0) = q-1 and sum_{u!=0} kloos(u*inv2,u*inv2)^2")
    log("  == q^2-2q-1 (circle_sum T1(c) diagonal energy) at every clock q <= 19")
    log("  -- PASS")
    expectation_met = True
    for A in (17, 19):
        ss = seg_store[A]
        K = ss["K"]
        ks = ss["ks_def"] + ss["ks_typ"]
        n = len(ks)
        R = seg_R_matrix(A, ks, K)
        preds = np.array([float(pred_fraction(A, d, K)) for d in range(101)])
        M2 = ((R[:, 1:] - preds[1:]) ** 2).sum(axis=1)
        Q = clocks(A)
        feats = np.empty((n, len(Q)))
        ndeg = 0
        for i, k in enumerate(ks):
            for jq, q in enumerate(Q):
                u = k % q
                if u == 0:
                    feats[i, jq] = q - 1.0
                    ndeg += 1
                else:
                    inv2q = (q + 1) // 2
                    kv = kloos_val(q, (u * inv2q) % q, (u * inv2q) % q)
                    assert abs(kv.imag) <= 1e-9
                    feats[i, jq] = kv.real
        y = M2.astype(np.float64)
        gd = y[:6]
        gt = y[6:]
        sd = gt.std(ddof=1)
        zM2 = (gd.mean() - gt.mean()) / sd if sd > 1e-15 else float("nan")
        log("")
        log("  A=%2d n=%d (6 defect + 20 typical), %d deg feature cells:"
            % (A, n, ndeg))
        log("    M2 defect mean %.2f | typical mean %.2f sd %.2f | z = %+.2f"
            % (gd.mean(), gt.mean(), sd, zM2))
        if abs(zM2) >= 3:
            ANOMALIES.append(("s3 M2 defect-vs-typical A=%d" % A, "z", zM2))
        X = np.column_stack([np.ones(n)] + [feats[:, j]
                                            for j in range(len(Q))])
        for tag, idx in (("pooled n=26", np.arange(n)),
                         ("typical-only n=20", np.arange(6, n))):
            Xi, yi = X[idx], y[idx]
            coef = np.linalg.lstsq(Xi, yi, rcond=None)[0]
            pred = Xi @ coef
            sst = float(((yi - yi.mean()) ** 2).sum())
            r2 = 1.0 - float(((yi - pred) ** 2).sum()) / sst if sst > 1e-15 \
                else float("nan")
            jack = []
            for i in range(len(idx)):
                msk = np.ones(len(idx), dtype=bool)
                msk[i] = False
                jack.append(np.linalg.lstsq(Xi[msk], yi[msk], rcond=None)[0])
            jack = np.array(jack)
            signs = ["Y" if (jack[:, c].min() > 0) or (jack[:, c].max() < 0)
                     else "N" for c in range(X.shape[1])]
            allstab = all(s == "Y" for s in signs)
            log("    fit [%s]: R2 = %.4f  rank(X) = %d/%d  all-sign-stable=%s"
                % (tag, r2, int(np.linalg.matrix_rank(Xi)), X.shape[1],
                   "Y" if allstab else "N"))
            log("      coef [1%s] = [%s]"
                % ("".join(", K_%d" % q for q in Q),
                   ", ".join("%+.3f" % c for c in coef)))
            log("      jackknife sign-stability per coef: [%s]"
                % " ".join(signs))
            if tag.startswith("pooled"):
                if r2 >= 0.9 and allstab:
                    expectation_met = False
            else:
                res_def = y[:6] - X[:6] @ coef
                log("      defect residuals under the typical-only fit: %s"
                    % " ".join("%+.1f" % v for v in res_def))
    log("")
    log("  REGISTERED EXPECTATION CHECK (no other verdict vocabulary):")
    if expectation_met:
        log("  NO stable re-expression -- CONFIRMED (no pooled fit reached")
        log("  R2 >= 0.9 with all-coefficient jackknife sign stability).")
        log("  The complete kloos values at the segment's clock frequencies do")
        log("  not re-express the incomplete shifted-convolution second moment")
        log("  -- the measured half of the dispersion-blindness law.")
    else:
        log("  registered expectation CONTRADICTED: a pooled fit reached")
        log("  R2 >= 0.9 with all-sign-stable coefficients -- reported as")
        log("  measured; no further vocabulary (registered).")
    stage_close("s3", t0)


# ------------------------------------------------------------------------ main

def main():
    t00 = time.time()
    section("DISPERSION HARNESS RUN 1 -- %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    log("harness: tools/dispersion_harness.py; log: tools/dispersion_run1.log")
    log("the numeric core of the dispersion pass over the strike-clock window")
    log("system of EuclidsPath/Engine/Step00StrikeFourier.lean.")
    log("python %s | numpy %s | seed %d | STAGE_TIME_CAP %ds/stage"
        % (sys.version.split()[0], np.__version__, SEED, int(STAGE_TIME_CAP)))
    registration()
    d17, d19 = s0()
    s1()
    seg_store, triggers = s2(d17, d19)
    s3(seg_store)
    section("RUN COMPLETE")
    if ANOMALIES:
        log("ANOMALIES |z| >= 3 (registered contexts):")
        for ctx, zn, zv in ANOMALIES:
            log("  %s: %s = %+.2f" % (ctx, zn, zv))
    else:
        log("ANOMALIES |z| >= 3: none")
    log("total runtime %.1f min; closed stage list executed: s0, s1, s2, s3;"
        % ((time.time() - t00) / 60.0))
    log("no thresholds moved; the conditional foil %s."
        % ("FIRED (see s2)" if triggers else "did not fire"))
    log("SECTION LINE INDEX (this run, 1-based in this append block):")
    for title, ln in SECTION_INDEX:
        log("  line %5d: %s" % (ln, title))


if __name__ == "__main__":
    try:
        main()
    except AssertionError as exc:
        log("")
        log("STOP: registered selftest/byte-check FAILED -- surfacing before")
        log("anything downstream consumes these numbers.  AssertionError: %s"
            % (exc,))
        log("exit 1")
        sys.exit(1)
