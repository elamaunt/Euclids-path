# circle_volume_harness.py -- Stage C of the circle-volume pass: the volume-deficit
# WINDOW observables through the FULL foil-v2 protocol -- the first imaginary-geometry
# layer to which the foil applies.  Empirical body of
# EuclidsPath/Engine/Step00CircleVolume.lean (+ the Step00ImaginaryCircle kernel
# counter circleCountN).
#
# Protocol lineage (read before editing):
#   tools/betti_portrait_harness.py  -- precompute_X / foil_row reused VERBATIM
#     (gate_g3 foil-v2 machinery: 200 sigma_W perms + 200 sigma_I lambda-resamples;
#     thresholds immovable; verdict grid copied from stage_s4v);
#   tools/fourier_window_harness.py  -- the house pattern of a recent verbatim reuse
#     (make_cell mask/load/null construction copied, So mask added);
#   tools/pratt_wing_harness.py + tools/grave_depth_harness.py -- factorization tier
#     lineage (SPF sieve / numpy trial division / Brent rho + 12-base deterministic
#     Miller-Rabin) and the DEFECT_R defect-window witnesses (incl. the 41/43 ones).
#
# Discipline: PRE-REGISTRATION FIRST in the log (closed observable list V1-V5,
# populations, selftest list, thresholds VERBATIM, registered EXPECTATION), then
# selftests (any failure = STOP exit 1), then measurements.  Seed 20260710.
# STAGE_TIME_CAP 5400 s with the documented halving fallback.  Log append-only ASCII.
#
# Usage: python tools/circle_volume_harness.py   (single invocation; appends to
# tools/circle_volume_run1.log).

import math
import os
import sys
import time

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import betti_portrait_harness as BP  # precompute_X / foil_row reused VERBATIM

LOGPATH = os.path.join(TOOLS, "circle_volume_run1.log")
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


def STOP(msg):
    log("STOP -- " + msg)
    log("STAGE VERDICT: STOP (selftest/design violation; run is void)")
    sys.exit(1)


SEED = 20260710
STAGE_TIME_CAP = 5400          # s; registered fallback: halve remaining workload, LOG it
H = 50
XS = (10 ** 6, 10 ** 9)
NW_OF_X = {10 ** 6: 3000, 10 ** 9: 1000}
OBS = ("V1", "V2", "V3", "V4")

SPF_LIM = 7_000_000            # registered adaptation of the planned 6.1e6 (see reg.)
PTD_LIM = 78_500               # isqrt(6.1e9) = 78102 < 78500
TD_LIM = 6_100_000_000
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)   # deterministic < 3.186e23
MR_VALID = 318 * 10 ** 21

G_EXACT = {17: 18, 19: 25, 23: 34, 29: 43, 31: 58, 37: 88, 41: 91, 43: 103}
DEFECT_R = {                   # tools/pratt_wing_harness.py DEFECT_R (verbatim)
    23: [12694428, 18165208, 19016903, 24487683],
    29: [200906185, 877375977],
    31: [21844264615],
    37: [1145973108145],
    41: [50077677123072],      # the A=41 witness (L=90)
    43: [233885349904190],     # the A=43 witness (L=102)
}
DEFECT_SCALES = (17, 19, 23, 29, 31, 37, 41, 43)
N_CTL = 20                     # matched typical windows per defect window (registered)

ANOMALIES = []                 # (context, statistic, value)
TIER_STATS = {"spf": 0, "td": 0, "rho": 0}


class StageClock(object):
    """Registered halving fallback (pratt_wing copy): call .factor() at boundaries."""

    def __init__(self):
        self.t0 = time.time()
        self.halved = False

    def factor(self):
        if not self.halved and time.time() - self.t0 > STAGE_TIME_CAP:
            self.halved = True
            log("  RUNTIME FALLBACK: cap %ds exceeded -- HALVING the remaining"
                " per-population workload (registered fallback, logged)"
                % STAGE_TIME_CAP)
        return 2 if self.halved else 1


# ------------------------------------------------------------------ number theory

def prime_sieve(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def primes_upto(n):
    return [int(p) for p in np.flatnonzero(prime_sieve(n))]


def clocks(A):
    return [p for p in primes_upto(A) if p >= 5]


def jacobi(a, n):
    """pratt_wing_harness copy."""
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


_CHI = {2: {}, 3: {}}


def chi(d, l):
    """chi_d(l) = Jacobi (d|l) in {+1,-1}; l an odd prime >= 5 coprime to d."""
    m = _CHI[d]
    v = m.get(l)
    if v is None:
        v = jacobi(d, l)
        if v == 0:
            STOP("chi_%d(%d) = 0 (l divides d -- impossible for wings)" % (d, l))
        m[l] = v
    return v


_SPF = None
_PTD = None
_SMALL = None


def setup_tables():
    """SPF sieve to 7.0e6 (in-memory) + trial-division prime table to 78500
    (pratt_wing / grave_depth tier lineage)."""
    global _SPF, _PTD, _SMALL
    if _SPF is not None:
        return
    t0 = time.time()
    spf = np.zeros(SPF_LIM + 1, dtype=np.int32)
    for i in range(2, int(math.isqrt(SPF_LIM)) + 1):
        if spf[i] == 0:
            sl = spf[i * i::i]
            sl[sl == 0] = i
    _SPF = spf
    sieve = prime_sieve(PTD_LIM)
    _PTD = np.flatnonzero(sieve).astype(np.int64)
    _SMALL = [int(p) for p in _PTD[_PTD <= 3000]]
    log("  tables: SPF <= %d (in-memory), %d TD primes <= %d (%.1fs)"
        % (SPF_LIM, _PTD.size, PTD_LIM, time.time() - t0))


def is_prime_mr(n):
    assert n < MR_VALID
    if n < 2:
        return False
    for p in MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rho_brent(n):
    if n % 2 == 0:
        return 2
    for c in range(1, 100):
        y, m_, g, r, q = 2, 128, 1, 1, 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m_, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m_
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g
    raise RuntimeError("rho failed on %d" % n)


def fac_pairs_spf(x):
    out = []
    while x > 1:
        q = int(_SPF[x])
        if q == 0:
            out.append((x, 1))
            break
        e = 0
        while x % q == 0:
            x //= q
            e += 1
        out.append((q, e))
    return out


def _fac_large(x, out):
    """Distinct primes of x (rho tier; grave_depth / pratt_wing lineage)."""
    for p in _SMALL:
        if p * p > x:
            break
        if x % p == 0:
            out.add(p)
            while x % p == 0:
                x //= p
    if x == 1:
        return
    stack = [x]
    while stack:
        y = stack.pop()
        if y == 1:
            continue
        if y <= TD_LIM:
            for q, _ in fac_pairs_any(y):
                out.add(q)
            continue
        if is_prime_mr(y):
            out.add(y)
            continue
        d = rho_brent(y)
        stack.append(d)
        stack.append(y // d)


def fac_pairs_any(x):
    """Full factorization [(q, e), ...] ascending on every tier (pratt_wing copy)."""
    x = int(x)
    if x <= SPF_LIM:
        return fac_pairs_spf(x)
    if x <= TD_LIM:
        out = []
        rem = x
        lim = math.isqrt(x)
        k = int(np.searchsorted(_PTD, lim, 'right'))
        sub = _PTD[:k]
        hits = sub[(x % sub) == 0]
        for p in hits.tolist():
            p = int(p)
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            out.append((p, e))
        if rem > 1:
            out.append((rem, 1))   # remainder > sqrt(x) after full TD -> prime
        return out
    ps = set()
    _fac_large(x, ps)
    out = []
    rem = x
    for p in sorted(ps):
        e = 0
        while rem % p == 0:
            rem //= p
            e += 1
        out.append((p, e))
    if rem != 1:
        return None
    return out


def fac_checked(w):
    """Tier dispatch + FULL verification: the reconstruction product must equal w
    (completeness is therefore 100% by construction or the run STOPs)."""
    if w <= SPF_LIM:
        TIER_STATS["spf"] += 1
    elif w <= TD_LIM:
        TIER_STATS["td"] += 1
    else:
        TIER_STATS["rho"] += 1
    fp = fac_pairs_any(w)
    if fp is None:
        STOP("incomplete factorization at w=%d (rho tier)" % w)
    prod = 1
    for l, e in fp:
        prod *= l ** e
    if prod != w:
        STOP("factorization reconstruction failed at w=%d: %r" % (w, fp))
    return fp


# ------------------------------------------------- the registered functionals

def circ_vol(fp, d):
    c = 1
    for l, e in fp:
        c *= l ** (e - 1) * (l - chi(d, l))
    return c


def lcm_bound(fp, d):
    L = 1
    for l, e in fp:
        f = l ** (e - 1) * (l - chi(d, l))
        L = L * f // math.gcd(L, f)
    return L


def functionals(w, fp):
    """(circVol_2/w, volGap_2/w, ordDef_2/(w+1), (circVol_2-circVol_3)/w)."""
    c2, c3, L2 = 1, 1, 1
    for l, e in fp:
        pe = l ** (e - 1)
        f2 = pe * (l - chi(2, l))
        c2 *= f2
        c3 *= pe * (l - chi(3, l))
        L2 = L2 * f2 // math.gcd(L2, f2)
    wf = float(w)
    return (c2 / wf, (w + 1 - c2) / wf, (w + 1 - L2) / float(w + 1), (c2 - c3) / wf)


# ------------------------------------------------- brute-force circle machinery

def circle_count_brute(n, d):
    """#{(a,b) in [0,n)^2 : a^2 % n == (1 + d*b^2) % n} -- direct enumeration of
    the Lean kernel counter circleCountN n d (residue-count route)."""
    a = np.arange(n, dtype=np.int64)
    ca = np.bincount((a * a) % n, minlength=n)
    cb = np.bincount((1 + d * (a * a)) % n, minlength=n)
    return int((ca * cb).sum())


def circle_points(n, d):
    """All pairs (a,b) with a^2 == 1 + d b^2 (mod n) (for the order-bound check)."""
    sq = {}
    for a in range(n):
        sq.setdefault((a * a) % n, []).append(a)
    pts = []
    for b in range(n):
        for a in sq.get((1 + d * b * b) % n, ()):
            pts.append((a, b))
    return pts


def qmulN(d, n, x, y):
    """Step00ImaginaryCircle.qmulN mirror (componentwise mod n)."""
    return ((x[0] * y[0] + d * (x[1] * y[1])) % n, (x[0] * y[1] + x[1] * y[0]) % n)


def qpow_fast(d, n, x, k):
    """Binary ladder over qmulN (same semantics as the kernel qpowN fold)."""
    r = (1 % n, 0)
    b = x
    while k:
        if k & 1:
            r = qmulN(d, n, r, b)
        b = qmulN(d, n, b, b)
        k >>= 1
    return r


# ------------------------------------------------------------------ registration

def registration():
    section("PRE-REGISTRATION BLOCK (logged before ANY measurement; nothing may be"
            " added below)")
    for s in [
        "DEFINITIONS (for an integer w with known factorization w = prod l^a;",
        "  l runs over the odd prime factors; wings 6m+-1 are odd and coprime to 6,",
        "  hence coprime to d in {2,3} ALWAYS -- the skip/mark counter for w even or",
        "  gcd(w,d)>1 is registered and must equal 0):",
        "  chi_d(l)   = +1 if d is a nonzero QR mod l else -1 (Jacobi/Euler; l odd",
        "               prime; selftest ST5 checks Jacobi == Euler criterion and the",
        "               closed forms chi_2 <=> l mod 8 in {1,7}, chi_3 <=> l mod 12",
        "               in {1,11}).",
        "  circVol_d(w)  = prod_{l^a || w} l^(a-1) * (l - chi_d(l))",
        "                = w * prod_{l | w} (1 - chi_d(l)/l)   [multiplicative].",
        "  volGap_d(w)   = (w+1) - circVol_d(w)  -- the SIGNED volume gap.  Registered",
        "               as SIGNED, deliberately NOT called a deficit: it goes NEGATIVE",
        "               (example w = 55 = 5*11, d = 2: circVol = 6*12 = 72, gap = -16).",
        "  lcmBound_d(w) = lcm_{l^a || w} l^(a-1)*(l - chi_d(l)).",
        "  ordDef_d(w)   = (w+1) - lcmBound_d(w)  -- the order-budget deficit, SIGNED",
        "               (on prime-power wings l^a, a >= 2, chi = -1 the local factor",
        "               exceeds w+1: w = 25, d = 2 gives lcmBound 30, ordDef -4 --",
        "               disclosed).",
        "  LEAN SCOPE DISCLOSURE: the Lean module Step00CircleVolume proves the volume",
        "  formula and the order bound for SEMIPRIMES p*q (circle_card_semiprime,",
        "  circle_order_bound_semiprime); the per-prime-power factor l^(a-1)(l-chi)",
        "  and the multi-factor lcm used here are the NUMERIC generalization (Quad d",
        "  l^k is not etale; deliberately out of the Lean scope).  Selftests ST2/ST3b",
        "  check the numeric generalization by brute force; ST4 checks the order",
        "  bound at semiprimes (the Lean scope).",
        "",
        "GRID POPULATION (foil-v2, the L38/L52 house grid): A in {13,31} x X in",
        "  {1e6 (NW=3000), 1e9 (NW=1000)}, H = 50; windows [x0, x0+50), x0 = X + 50w.",
        "  READ SET per window: the composite-wing centers = centers with at least",
        "  one composite wing = the NON-TWIN centers (a twin center has both wings",
        "  prime); BOTH wings of every read center enter, including a prime co-wing.",
        "  Window value = mean over the 2*|read| wings.  The observable is",
        "  A-INDEPENDENT (it reads all non-twin centers, not survivors); the",
        "  A-escalation acts through the LOAD (survivor set) -- disclosed.",
        "  Twin flags are exact (Omega(6m-1) = Omega(6m+1) = 1 from the house sieve,",
        "  cross-checked against the harness factorization in ST7).",
        "",
        "OBSERVABLES (CLOSED LIST -- nothing may be added after this block):",
        "  V1 = window mean of circVol_2(w)/w        over the read wings.",
        "  V2 = window mean of volGap_2(w)/w         (SIGNED) over the read wings.",
        "  V3 = window mean of ordDef_2(w)/(w+1)     (SIGNED) over the read wings.",
        "  V4 = window mean of (circVol_2(w) - circVol_3(w))/w  -- the d-contrast",
        "       (character-twist differential) over the read wings.",
        "  V5 = DESCRIPTIVE defect-vs-typical contrast of V1..V3 on the 50 exact",
        "       defect windows A = 17..43 vs matched typical windows (small n --",
        "       NEVER part of the foil verdict; populations below).",
        "  The foil verdict applies to V1-V4.",
        "",
        "LOADS (foil-v2 verbatim; lambda(m) = (-1)^(Omega(6m-1)+Omega(6m+1))):",
        "  S    = sum of lambda over the window's A-survivors (clean centers);",
        "         support overlaps the read set -- disclosed (fourier AN5 precedent).",
        "  S''  = split-window: observable on the LEFT half [x0, x0+25), load = sum",
        "         of lambda over RIGHT-half survivors (disjoint support).",
        "  So   = self-excluded: load over survivors NOT read by the observable",
        "         = the TWIN survivors only.  Frame fact: lambda == +1 identically on",
        "         twin centers (Omega = 1+1), so the So lambda-load is a twin-COUNT",
        "         load, not a parity load -> INFORMATIONAL ROW ONLY, excluded from",
        "         the verdict (precedent: betti P3|So NA, fourier So NA).",
        "  Verdict rows: V1-V4 x {S, S''} over the 4-cell grid.",
        "",
        "FOIL MACHINERY (verbatim reuse): BP.precompute_X / BP.foil_row from",
        "  tools/betti_portrait_harness.py; 200 sigma_W permutations + 200 sigma_I",
        "  lambda-resamples per (cell, load); mask/load/null construction copied from",
        "  tools/fourier_window_harness.py make_cell (So mask added).  Seed 20260710;",
        "  substreams: default_rng(SEED) sigma_I nulls per cell; default_rng(SEED+7)",
        "  per foil row (betti cell_run copy); [SEED,5] selftest draws; [SEED,A,i]",
        "  V5 control draws.",
        "",
        "THRESHOLDS (gate_g3 foil-v2, VERBATIM, immovable):",
        "  PARITY-SENSITIVE (MANAGED-PASS) iff min|z_I| >= 5 over the 4-cell grid",
        "    AND escalation |R(31)| >= |R(13)|/3 at both X (cells with |R(13)| <=",
        "    1e-9 skipped -- betti stage_s4v copy);",
        "  SOFT iff min|z_I| >= 3;",
        "  else PARITY-BLIND-UNDER-ESCALATION-v2.",
        "",
        "REGISTERED EXPECTATION: PARITY-BLIND-UNDER-ESCALATION-v2.",
        "  Honest reasoning: circVol_d / volGap_d / ordDef_d are congruence-AND-",
        "  factorization-determined multiplicative functionals of the wings --",
        "  circVol_d(w)/w = prod_{l|w}(1 - chi_d(l)/l) is a character-twisted",
        "  weighting of the wing's prime support: a new MEMBER of an old class, not",
        "  a new class.  The ledger closes the family: L38 (five foil-v2 candidates",
        "  blind), L41 (grave depth / strata blind), L53 (quadratic imaginary layer",
        "  collapsed over the twin panel), L55 (bilinear/peel observables outside",
        "  the window blind), L58 (trajectory class blind), L63 (beyond-phase",
        "  quartic/Gaussian class NULL).  A MANAGED-PASS here would be the FIRST",
        "  parity-sensitive window observable under foil-v2 and ESCALATES IMMEDIATELY",
        "  per protocol (no threshold moves, no re-runs; escalation = a registered",
        "  follow-up pass).",
        "",
        "V5 POPULATIONS (descriptive stratum):",
        "  Defect windows (the 50 exact ones, A = 17..43): window = centers r+1..r+L,",
        "  L = G(A)-1 with exact G = {17:18, 19:25, 23:34, 29:43, 31:58, 37:88,",
        "  41:91, 43:103}; starts: A=17 -- 20 starts by full-period scan (calibration:",
        "  first r=117, must contain 502); A=19 -- 20 starts (first r=110); A=23..43",
        "  from the pratt_wing DEFECT_R witness list incl. the 41/43 witnesses",
        "  50077677123072 (L=90) and 233885349904190 (L=102).  Every start is",
        "  re-verified (r clean, r+1..r+L struck, r+L+1 clean) in ST8 -- STOP on",
        "  mismatch.  Read set as in the grid (non-twin centers; in a defect window",
        "  every center is struck hence composite-winged hence read -- asserted).",
        "  Matched typical windows: per defect window i at scale A, %d control" % N_CTL,
        "  windows of the SAME length L, starts r' seeded uniform (rng [SEED,A,i])",
        "  in [max(1, r//2), r + r//2), redrawn while |r' - r| <= L (no overlap);",
        "  unconditioned (typical).  Contrast: Welch z on V1..V3 per scale where",
        "  n_def >= 2; sigma-distance (v_def - mean_ctl)/sd_ctl where n_def = 1;",
        "  ALL labeled DESCRIPTIVE (small n) -- no foil verdict.",
        "",
        "FACTORIZATION TIERS (grave_depth / pratt_wing lineage): SPF sieve (int32) to",
        "  7.0e6 -- REGISTERED ADAPTATION of the planned 6.1e6 (the 1e6-scale wings",
        "  reach 6*(1e6+150000)+1 = 6,900,001 > 6.1e6); numpy trial division over",
        "  sieved primes <= 78,500 for values <= 6.1e9 (covers the 1e9 scale: wings",
        "  <= 6*(1e9+50000)+1 = 6,000,300,001); Brent rho + deterministic 12-base",
        "  Miller-Rabin above (deterministic < 3.186e23; A=43 control wings reach",
        "  ~2.1e15).  EVERY factorization is verified by reconstruction product == w",
        "  (STOP otherwise): completeness target 100% is enforced, not sampled.",
        "",
        "SELFTEST LIST (all STOP exit 1):",
        "  ST1 kernel constants: brute circle count == the landed Lean constants",
        "      circleCountN_5_2 = 6, circleCountN_11_2 = 12 (Step00ImaginaryCircle),",
        "      circleCountN_35_2 = 36, circleCountN_127_3 = 128 (Step00CircleVolume),",
        "      AND == the circVol formula value on each.",
        "  ST2 multiplicativity: brute circle count == circVol_d at 3 seeded random",
        "      semiprimes p*q (p,q distinct primes in [5,113], rng [SEED,5]), both",
        "      d in {2,3}; plus the fixed beyond-semiprime instances 175 = 5^2*7 and",
        "      385 = 5*7*11.",
        "  ST3 per-prime volume: brute count == l - chi_d(l) on 20 seeded primes in",
        "      [5,400) (rng [SEED,5]), both d.",
        "  ST3b prime-power face (numeric generalization): brute count ==",
        "      l^(a-1)(l - chi_d(l)) on {25, 125, 49, 121, 169}, both d.",
        "  ST4 order bound at the ST2 semiprimes (the Lean scope): EVERY brute circle",
        "      point satisfies point^lcmBound_d == (1,0) via the qmulN ladder",
        "      (circle_order_bound_semiprime used numerically).",
        "  ST5 chi: Jacobi == Euler criterion on 300 seeded (d,l) + closed-form",
        "      mod-8 / mod-12 agreement on every prime < 10^4.",
        "  ST6 factor tiers: fac == independent trial division on 2000 seeded values",
        "      <= 7e6 (SPF tier) and 40 seeded values in (7e6, 6.1e9] (TD tier);",
        "      5 seeded rho-tier values in (6.1e9, 1e13]: reconstruction + MR",
        "      primality of every factor.",
        "  ST7 grid Omega-consistency (runs at grid construction, STOP semantics):",
        "      sum of exponents of the harness factorization == the house sieve",
        "      Omega (BP.omega_range arrays) on EVERY wing of both scales; twin",
        "      flags follow (Omega = 1 <=> prime wing).",
        "  ST8 defect calibration: A=17 scan -> 20 starts, first 117, contains 502;",
        "      A=19 scan -> 20 starts, first 110; every DEFECT_R witness re-verified",
        "      (r clean, r+1..r+L struck, r+L+1 clean).",
        "",
        "STOP RULE (registered): after the grid + V5 -- no new observables, no new",
        "  weightings, no threshold moves.  STAGE_TIME_CAP %d s; fallback: HALVE the"
        % STAGE_TIME_CAP,
        "  remaining per-population workload and LOG the shrink -- never silently.",
        "PRE-REGISTRATION ENDS -- measurements begin below this line.",
    ]:
        log(s)


# ------------------------------------------------------------------ selftests

def defect_scan(A):
    """Full-period scan (pratt_wing copy): starts r with r clean, r+1..r+L struck,
    r+L+1 clean, L = G(A)-1."""
    qs = clocks(A)
    P = 1
    for q in qs:
        P *= q
    L = G_EXACT[A] - 1
    struck = np.zeros(P + 2 * L + 2, dtype=bool)
    for q in qs:
        i6 = pow(6, -1, q)
        for cls in (i6 % q, (q - i6) % q):
            struck[cls::q] = True
    clean = np.flatnonzero(~struck)
    d = np.diff(clean)
    starts = clean[np.flatnonzero(d == L + 1)]
    return sorted(int(r) for r in starts if r + L + 1 < P)


def struck_ok(r, L, A):
    qs = clocks(A)
    arr = np.arange(r, r + L + 2, dtype=np.int64)
    sm = np.zeros(arr.size, dtype=bool)
    for q in qs:
        i6 = pow(6, -1, q)
        sm |= (arr % q == i6) | (arr % q == (q - i6) % q)
    return (not sm[0]) and bool(sm[1:L + 1].all()) and (not sm[L + 1])


def selftests():
    section("SELFTESTS (ST1-ST6, ST8; ST7 runs at grid construction; any failure"
            " = STOP)")
    t0 = time.time()
    setup_tables()
    rng = np.random.default_rng([SEED, 5])

    # ST1 -- Lean kernel constants
    lean = [(5, 2, 6, "circleCountN_5_2"), (11, 2, 12, "circleCountN_11_2"),
            (35, 2, 36, "circleCountN_35_2"), (127, 3, 128, "circleCountN_127_3")]
    for n, d, want, name in lean:
        got = circle_count_brute(n, d)
        form = circ_vol(fac_checked(n), d)
        if got != want or form != want:
            STOP("ST1: %s: brute=%d formula=%d Lean=%d" % (name, got, form, want))
    log("ST1 kernel constants: brute count == Lean constant == formula on all 4:")
    log("    (5,d=2)=6  (11,d=2)=12  (35,d=2)=36  (127,d=3)=128 -- PASS")

    # ST2 -- multiplicativity at 3 seeded semiprimes + fixed composites
    P113 = [p for p in primes_upto(113) if p >= 5]
    semis = []
    while len(semis) < 3:
        i, j = rng.integers(0, len(P113), 2)
        if i != j:
            pq = (int(P113[min(i, j)]), int(P113[max(i, j)]))
            if pq not in semis:
                semis.append(pq)
    st2 = []
    for p, q in semis:
        n = p * q
        for d in (2, 3):
            got = circle_count_brute(n, d)
            form = circ_vol([(p, 1), (q, 1)], d)
            if got != form:
                STOP("ST2: semiprime %d=%d*%d d=%d: brute=%d formula=%d"
                     % (n, p, q, d, got, form))
        st2.append("%d=%d*%d" % (n, p, q))
    for n in (175, 385):
        for d in (2, 3):
            got = circle_count_brute(n, d)
            form = circ_vol(fac_checked(n), d)
            if got != form:
                STOP("ST2: composite %d d=%d: brute=%d formula=%d" % (n, d, got, form))
    log("ST2 multiplicativity (seeds [SEED,5]): brute == formula at semiprimes %s"
        % ", ".join(st2))
    log("    (both d) + fixed 175=5^2*7, 385=5*7*11 (both d) -- PASS")

    # ST3 -- per-prime volume on 20 seeded primes
    P400 = [p for p in primes_upto(399) if p >= 5]
    picks = sorted({int(P400[i]) for i in rng.integers(0, len(P400), 40)})[:20]
    if len(picks) < 20:
        STOP("ST3: fewer than 20 distinct seeded primes drawn")
    for l in picks:
        for d in (2, 3):
            got = circle_count_brute(l, d)
            if got != l - chi(d, l):
                STOP("ST3: l=%d d=%d brute=%d formula=%d" % (l, d, got, l - chi(d, l)))
    log("ST3 per-prime volume: brute == l - chi_d(l) on 20 seeded primes"
        " (%d..%d), both d -- PASS" % (picks[0], picks[-1]))

    # ST3b -- prime-power face (numeric generalization beyond the Lean scope)
    for n in (25, 125, 49, 121, 169):
        fp = fac_checked(n)
        for d in (2, 3):
            got = circle_count_brute(n, d)
            form = circ_vol(fp, d)
            if got != form:
                STOP("ST3b: prime power %d d=%d: brute=%d formula=%d"
                     % (n, d, got, form))
    log("ST3b prime-power face: brute == l^(a-1)(l-chi) on {25,125,49,121,169},"
        " both d -- PASS")

    # ST4 -- order bound at the ST2 semiprimes (Lean circle_order_bound, numeric)
    npts = 0
    for p, q in semis:
        n = p * q
        for d in (2, 3):
            pts = circle_points(n, d)
            if len(pts) != circ_vol([(p, 1), (q, 1)], d):
                STOP("ST4: point census != volume at n=%d d=%d" % (n, d))
            L = lcm_bound([(p, 1), (q, 1)], d)
            for pt in pts:
                if qpow_fast(d, n, pt, L) != (1 % n, 0):
                    STOP("ST4: order bound violated at n=%d d=%d pt=%r L=%d"
                         % (n, d, pt, L))
            npts += len(pts)
    log("ST4 order bound: pt^lcmBound == (1,0) for ALL %d circle points of the 3"
        % npts)
    log("    semiprimes (both d; qmulN ladder) -- circle_order_bound numerically"
        " -- PASS")

    # ST5 -- chi selftests
    P2000 = [p for p in primes_upto(2000) if p >= 5]
    for _ in range(300):
        l = int(P2000[int(rng.integers(0, len(P2000)))])
        d = int((2, 3)[int(rng.integers(0, 2))])
        e = pow(d, (l - 1) // 2, l)
        e = -1 if e == l - 1 else e
        if jacobi(d, l) != e:
            STOP("ST5: jacobi(%d,%d) != Euler" % (d, l))
    for l in [p for p in primes_upto(10 ** 4) if p >= 5]:
        if chi(2, l) != (1 if l % 8 in (1, 7) else -1):
            STOP("ST5: chi_2 closed form fails at l=%d" % l)
        if chi(3, l) != (1 if l % 12 in (1, 11) else -1):
            STOP("ST5: chi_3 closed form fails at l=%d" % l)
    log("ST5 chi: Jacobi == Euler on 300 seeded (d,l); closed forms mod 8 / mod 12"
        " on all primes in [5,1e4) -- PASS")

    # ST6 -- factor tier cross-checks
    def td_ref(x):
        out = []
        dd = 2
        while dd * dd <= x:
            if x % dd == 0:
                e = 0
                while x % dd == 0:
                    x //= dd
                    e += 1
                out.append((dd, e))
            dd += 1
        if x > 1:
            out.append((x, 1))
        return out

    for x in rng.integers(2, SPF_LIM + 1, 2000).tolist():
        if fac_pairs_spf(int(x)) != td_ref(int(x)):
            STOP("ST6: SPF != reference at x=%d" % x)
    for x in rng.integers(SPF_LIM + 1, TD_LIM + 1, 40).tolist():
        if fac_pairs_any(int(x)) != td_ref(int(x)):
            STOP("ST6: TD tier != reference at x=%d" % x)
    nrho = 0
    for x in rng.integers(TD_LIM + 1, 10 ** 13, 5).tolist():
        fp = fac_pairs_any(int(x))
        if fp is None:
            STOP("ST6: rho tier incomplete at x=%d" % x)
        prod = 1
        for l, e in fp:
            prod *= l ** e
            if not is_prime_mr(l):
                STOP("ST6: rho factor %d of %d not prime" % (l, x))
        if prod != int(x):
            STOP("ST6: rho reconstruction failed at x=%d" % x)
        nrho += 1
    log("ST6 tiers: SPF == reference on 2000 seeded <= 7e6; TD tier == reference on"
        " 40 seeded")
    log("    in (7e6, 6.1e9]; %d rho-tier values verified (reconstruction + MR"
        " factors) -- PASS" % nrho)

    # ST8 -- defect calibration
    d17 = defect_scan(17)
    if len(d17) != 20 or d17[0] != 117 or 502 not in d17:
        STOP("ST8: A=17 scan failed: n=%d first=%s" % (len(d17), d17[:3]))
    d19 = defect_scan(19)
    if len(d19) != 20 or d19[0] != 110:
        STOP("ST8: A=19 scan failed: n=%d first=%s" % (len(d19), d19[:3]))
    defects = {17: d17, 19: d19}
    for A, rs in sorted(DEFECT_R.items()):
        for r in rs:
            if not struck_ok(r, G_EXACT[A] - 1, A):
                STOP("ST8: witness r=%d at A=%d not a defect window" % (r, A))
        defects[A] = list(rs)
    ntot = sum(len(v) for v in defects.values())
    if ntot != 50:
        STOP("ST8: defect census %d != 50" % ntot)
    log("ST8 defect calibration: A=17 20 starts (first 117, 502 present); A=19 20"
        " starts (first 110);")
    log("    all %d witnesses A=23..43 re-verified (clean-struck-clean); census ="
        " 50 -- PASS" % sum(len(v) for v in DEFECT_R.values()))
    log("SELFTESTS ST1-ST6, ST8 ALL PASS (%.1fs)" % (time.time() - t0))
    return defects


# ------------------------------------------------------------------ grid stage

def scale_build(X):
    """precompute_X + wing factorization + ST7 + the per-center observable arrays."""
    NW = NW_OF_X[X]
    px = BP.precompute_X(X, NW, H)
    ncent = px['ncent']
    OL = px['OLb'][BP.BAND:]
    OR_ = px['ORb'][BP.BAND:]
    V = np.empty((4, ncent), np.float64)
    skip = 0
    t0 = time.time()
    for i in range(ncent):
        m = X + i
        a0 = a1 = a2 = a3 = 0.0
        for side, w in ((0, 6 * m - 1), (1, 6 * m + 1)):
            if w % 2 == 0 or w % 3 == 0:
                skip += 1
                continue
            fp = fac_checked(w)
            om = sum(e for _, e in fp)
            if om != int(OL[i] if side == 0 else OR_[i]):
                STOP("ST7: Omega mismatch at m=%d side=%d: mine=%d sieve=%d"
                     % (m, side, om, int(OL[i] if side == 0 else OR_[i])))
            f = functionals(w, fp)
            a0 += f[0]
            a1 += f[1]
            a2 += f[2]
            a3 += f[3]
        V[0, i], V[1, i], V[2, i], V[3, i] = a0 / 2, a1 / 2, a2 / 2, a3 / 2
        if (i + 1) % 50000 == 0:
            log("    [X=%.0e] %d/%d centers factorized (%.0fs)"
                % (X, i + 1, ncent, time.time() - t0))
    if skip:
        STOP("skip counter nonzero at X=%.0e: %d (wings must be coprime to 6)"
             % (X, skip))
    lam_tw = px['lam'][px['twin']]
    if lam_tw.size and not np.all(lam_tw == 1):
        STOP("frame fact violated: lambda != +1 on a twin center")
    log("  [X=%.0e] ST7 Omega-consistency on all %d wings -- PASS; skip counter = 0;"
        % (X, 2 * ncent))
    log("    lambda == +1 on all %d twin centers (frame fact) -- OK (%.0fs)"
        % (int(px['twin'].sum()), time.time() - t0))
    return px, V


def make_cell(px, A):
    """fourier make_cell copy + the So (twin-survivor) mask."""
    X, ncent = px['X'], px['ncent']
    NW = ncent // H
    m = X + np.arange(ncent, dtype=np.int64)
    clean = np.ones(ncent, dtype=bool)
    for q in clocks(A):
        iq = pow(6, -1, q)
        r = m % q
        clean &= (r != iq) & (r != (q - iq) % q)
    cl = clean.reshape(NW, H)
    twm = px['twin'].reshape(NW, H)
    right = np.zeros((NW, H), dtype=bool)
    right[:, H // 2:] = True
    masks = {"S": cl, "Ssplit": cl & right, "So": cl & twm}
    lamw = px['lam'].astype(np.float64).reshape(NW, H)
    loads = {k: (lamw * mm).sum(1) for k, mm in masks.items()}
    pool = px['lam'][clean].astype(np.float64)
    nsurv = int(cl.sum())
    rng = np.random.default_rng(SEED)
    nulls = {k: np.empty((200, NW)) for k in masks}
    lmat = np.zeros((NW, H), dtype=np.float64)
    for t in range(200):
        lmat[:] = 0.0
        lmat[cl] = rng.choice(pool, size=nsurv)
        for k, mm in masks.items():
            nulls[k][t] = (lmat * mm).sum(1)
    return dict(X=X, A=A, NW=NW, loads=loads, nulls=nulls, nsurv=nsurv,
                ntwin=int((cl & twm).sum()))


def window_means(V, ntw, NW):
    """Full-window and left-half window means over the read (non-twin) centers."""
    ntww = ntw.reshape(NW, H)
    full, left = {}, {}
    df = ntww.sum(1).astype(np.float64)
    dl = ntww[:, :H // 2].sum(1).astype(np.float64)
    for k, name in enumerate(OBS):
        vv = V[k].reshape(NW, H)
        with np.errstate(invalid='ignore', divide='ignore'):
            full[name] = np.where(df > 0, (vv * ntww).sum(1) / np.maximum(df, 1),
                                  np.nan)
            left[name] = np.where(dl > 0,
                                  (vv[:, :H // 2] * ntww[:, :H // 2]).sum(1)
                                  / np.maximum(dl, 1), np.nan)
    return full, left, int((df == 0).sum()), int((dl == 0).sum())


def grid_stage():
    section("FOIL GRID -- A in {13,31} x X in {1e6,1e9}, H=50 (foil-v2 verbatim)")
    rows = {}
    clock = StageClock()
    for X in XS:
        px, V = scale_build(X)
        ntw = ~px['twin']
        NW = px['NW']
        full, left, nf0, nl0 = window_means(V, ntw, NW)
        log("  [X=%.0e] read centers/window mean=%.2f (of %d); empty windows:"
            " full=%d left=%d" % (X, float(ntw.reshape(NW, H).sum(1).mean()), H,
                                  nf0, nl0))
        log("  [X=%.0e] observable means/sd over %d windows:" % (X, NW))
        for name in OBS:
            log("    %s full: mean=%+.6f sd=%.6f | left: mean=%+.6f sd=%.6f"
                % (name, np.nanmean(full[name]), np.nanstd(full[name]),
                   np.nanmean(left[name]), np.nanstd(left[name])))
        for A in (13, 31):
            tc = time.time()
            cell = make_cell(px, A)
            log("")
            log("CELL X=%.0e A=%d NW=%d H=50 (seed %d): survivors=%d twin-survivors"
                "=%d [%.1fs]" % (X, A, NW, SEED, cell['nsurv'], cell['ntwin'],
                                 time.time() - tc))
            for name in OBS:
                stS = BP.foil_row(full[name], cell['loads']['S'],
                                  cell['nulls']['S'], np.random.default_rng(SEED + 7))
                stP = BP.foil_row(left[name], cell['loads']['Ssplit'],
                                  cell['nulls']['Ssplit'],
                                  np.random.default_rng(SEED + 7))
                stO = BP.foil_row(full[name], cell['loads']['So'],
                                  cell['nulls']['So'],
                                  np.random.default_rng(SEED + 7))
                rows[(name, "S", X, A)] = stS
                rows[(name, "S''", X, A)] = stP
                rows[(name, "So", X, A)] = stO
                for lab, st in (("S", stS), ("S''", stP)):
                    log("  %-3s|%-3s R=%+8.4f zW=%+6.1f zI=%+6.1f n=%5d %s"
                        % (name, lab, st['R'], st['zW'], st['zI'], st['n'],
                           st['note']))
                    for zn, zv in (("zW", st['zW']), ("zI", st['zI'])):
                        if abs(zv) >= 3:
                            ANOMALIES.append(("grid %s|%s X=%.0e A=%d"
                                              % (name, lab, X, A), zn, zv))
                log("  %-3s|So  R=%+8.4f zW=%+6.1f zI=%+6.1f n=%5d %s"
                    "  [INFORMATIONAL: twin-count load, lambda==+1 on twins]"
                    % (name, stO['R'], stO['zW'], stO['zI'], stO['n'], stO['note']))
                for zn, zv in (("zW", stO['zW']), ("zI", stO['zI'])):
                    if abs(zv) >= 3:
                        ANOMALIES.append(("grid %s|So(info) X=%.0e A=%d"
                                          % (name, X, A), zn, zv))
            clock.factor()
        del px, V, full, left
    return rows


def verdict_stage(rows):
    section("FOIL VERDICTS (gate_g3 thresholds VERBATIM, immovable; V1-V4 x"
            " {S, S''})")
    cellkeys = [(X, A) for X in XS for A in (13, 31)]
    verdicts = {}
    for name in OBS:
        for load in ("S", "S''"):
            zs, Rs, parts = [], {}, []
            for (X, A) in cellkeys:
                st = rows[(name, load, X, A)]
                zs.append(abs(st['zI']))
                Rs[(X, A)] = st['R']
                parts.append("X%.0eA%d R%+.3f zI%+5.1f" % (X, A, st['R'], st['zI']))
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
            log("  %-3s|%-3s %s" % (name, load, " | ".join(parts)))
            log("           min|z_I|=%.2f esc(%s) ratio_ok=%s -> %s"
                % (min(zs), ",".join(ratios), ratio_ok, v))
    log("-" * 78)
    log("VERDICT SUMMARY:")
    for (name, load), (mz, ro, v) in verdicts.items():
        log("  %-3s|%-3s min|z_I|=%5.2f ratio_ok=%-5s -> %s" % (name, load, mz, ro, v))
    nblind = sum(1 for v in verdicts.values() if v[2].startswith("PARITY-BLIND"))
    log("  %d/%d verdict rows PARITY-BLIND-UNDER-ESCALATION-v2 (registered"
        " expectation: BLIND)" % (nblind, len(verdicts)))
    return verdicts


# ------------------------------------------------------------------ V5 stage

def window_V(r, L):
    """(V1, V2, V3, n_read, n_twin) over centers r+1..r+L (read = non-twin)."""
    s1 = s2 = s3 = 0.0
    nread = ntwin = 0
    for m in range(r + 1, r + L + 1):
        wl, wr = 6 * m - 1, 6 * m + 1
        fl = fac_checked(wl)
        fr = fac_checked(wr)
        if len(fl) == 1 and fl[0] == (wl, 1) and len(fr) == 1 and fr[0] == (wr, 1):
            ntwin += 1
            continue
        for w, fp in ((wl, fl), (wr, fr)):
            f = functionals(w, fp)
            s1 += f[0]
            s2 += f[1]
            s3 += f[2]
        nread += 1
    k = max(2 * nread, 1)
    return s1 / k, s2 / k, s3 / k, nread, ntwin


def welch_z(m1, s1, n1, m2, s2, n2):
    se = math.sqrt(s1 * s1 / max(n1, 1) + s2 * s2 / max(n2, 1))
    return (m1 - m2) / se if se > 0 else float('nan')


def v5_stage(defects):
    section("V5 -- defect vs matched typical windows (DESCRIPTIVE, small n;"
            " no foil verdict)")
    clock = StageClock()
    signs = {0: [], 1: [], 2: []}
    for A in DEFECT_SCALES:
        L = G_EXACT[A] - 1
        starts = defects[A]
        nctl = max(N_CTL // clock.factor(), 1)
        if nctl != N_CTL:
            log("  A=%d: control count halved to %d (registered fallback)" % (A, nctl))
        t0 = time.time()
        dvals = []
        for r in starts:
            v1, v2, v3, nread, ntw = window_V(r, L)
            if ntw != 0:
                STOP("V5: twin center inside defect window r=%d A=%d" % (r, A))
            if nread != L:
                STOP("V5: read census %d != L=%d in defect window r=%d" % (nread, L, r))
            dvals.append((v1, v2, v3))
        cvals = []
        ctwin = cread = 0
        for i, r in enumerate(starts):
            rng = np.random.default_rng([SEED, A, i])
            lo, hi = max(1, r // 2), r + r // 2
            drawn = 0
            while drawn < nctl:
                rp = int(rng.integers(lo, max(hi, lo + 1)))
                if abs(rp - r) <= L:
                    continue
                v1, v2, v3, nread, ntw = window_V(rp, L)
                cvals.append((v1, v2, v3))
                ctwin += ntw
                cread += nread
                drawn += 1
        dv = np.array(dvals)
        cv = np.array(cvals)
        nd, nc = dv.shape[0], cv.shape[0]
        log("")
        log("A=%2d L=%3d: n_def=%d n_ctl=%d (starts ~%.3g; ctl twin-skipped"
            " centers=%d of %d) [%.0fs]"
            % (A, L, nd, nc, float(starts[0]), ctwin, ctwin + cread,
               time.time() - t0))
        for k, name in enumerate(("V1", "V2", "V3")):
            md, sd = float(dv[:, k].mean()), float(dv[:, k].std())
            mc, sc = float(cv[:, k].mean()), float(cv[:, k].std())
            signs[k].append(1 if md > mc else -1)
            if nd >= 2:
                z = welch_z(md, sd, nd, mc, sc, nc)
                log("  %s: def %+0.6f (sd %.6f, n=%d) vs ctl %+0.6f (sd %.6f,"
                    " n=%d)  Welch z=%+.2f  [DESCRIPTIVE small n]"
                    % (name, md, sd, nd, mc, sc, nc, z))
                if abs(z) >= 3:
                    ANOMALIES.append(("V5 %s A=%d (descriptive)" % (name, A),
                                      "welch_z", z))
            else:
                sdist = (md - mc) / sc if sc > 0 else float('nan')
                log("  %s: def %+0.6f (n=1) vs ctl %+0.6f (sd %.6f, n=%d)"
                    "  sigma-dist=%+.2f  [DESCRIPTIVE n=1]"
                    % (name, md, mc, sc, nc, sdist))
                if abs(sdist) >= 3:
                    ANOMALIES.append(("V5 %s A=%d (descriptive n=1)" % (name, A),
                                      "sigma", sdist))
    log("")
    log("V5 sign census over the 8 scales (def > ctl: +1): V1 %s | V2 %s | V3 %s"
        % tuple(str(signs[k]) for k in range(3)))
    log("  (descriptive only; 8 scales, n_def in {20,20,4,2,1,1,1,1} -- honest"
        " small-n label)")


# ------------------------------------------------------------------ main

def main():
    t00 = time.time()
    section("CIRCLE-VOLUME RUN 1 (Stage C) -- %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    log("harness: tools/circle_volume_harness.py; log: tools/circle_volume_run1.log")
    log("empirical body of EuclidsPath/Engine/Step00CircleVolume.lean (volume-deficit"
        " layer)")
    log("python %s | numpy %s | seed %d | STAGE_TIME_CAP %ds"
        % (sys.version.split()[0], np.__version__, SEED, STAGE_TIME_CAP))
    log("foil-v2 machinery reused VERBATIM from tools/betti_portrait_harness.py"
        " (precompute_X, foil_row);")
    log("mask/load/null construction from tools/fourier_window_harness.py;"
        " factor tiers from")
    log("tools/pratt_wing_harness.py / tools/grave_depth_harness.py (SPF / numpy TD"
        " / Brent rho + 12-base MR).")
    registration()
    defects = selftests()
    rows = grid_stage()
    v5_stage(defects)
    verdict_stage(rows)
    section("ANOMALIES + RUN SUMMARY")
    if ANOMALIES:
        log("ANOMALIES |z| >= 3 (all contexts, incl. informational/descriptive):")
        for ctx, zn, zv in ANOMALIES:
            log("  %s: %s=%+.2f" % (ctx, zn, zv))
    else:
        log("ANOMALIES |z| >= 3: none anywhere (grid verdict rows, So informational"
            " rows, V5 descriptive)")
    log("factorization tier usage: SPF=%d TD=%d rho=%d; completeness 100%% (every"
        " factorization" % (TIER_STATS['spf'], TIER_STATS['td'], TIER_STATS['rho']))
    log("  verified by reconstruction product == w; ST7 Omega-consistency on every"
        " grid wing)")
    log("total runtime %.1f min; STOP registered: no new observables, no new"
        " weightings, no threshold moves." % ((time.time() - t00) / 60.0))
    log("SECTION LINE INDEX (this append block, 1-based):")
    for title, ln in SECTION_INDEX:
        log("  line %5d: %s" % (ln, title))


if __name__ == "__main__":
    main()
