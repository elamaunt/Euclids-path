#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Pratt-wing harness -- numeric reconnaissance of the structure UNDER the primes:
the p-1 / p+1 anatomy and Pratt genealogy of twin wings, including the program's
FIRST beyond-phase observable class (O7: quartic residuacity + Gaussian a^2+b^2).

House discipline: pre-registration FIRST (stage `selftest` writes the registration
block to the log before any measurement line), closed observable list O1-O7,
seed 20260710, STAGE_TIME_CAP 5400 s with documented halving fallback, append-only
ASCII log tools/pratt_wing_run1.log, every selftest failure exits 1 (STOP).

NULL DESIGN, decision (b): these are PRIME-CONDITIONED populations; the
window-foil protocol's sigma_I has no analogue here; NO parity verdicts are
issuable.  EXACT-MEASURED laws only; Dickman / Artin / E4-truncated curves are
DISCLOSED REFERENCES, never verdicts.

Stages (argv modes; every stage APPENDS to tools/pratt_wing_run1.log):
  selftest   registration block + S1-S7 STOP selftests incl. the L35 gate
             (exact +0.211442 at 1e7, n_twin=280557, packing_walk w3 protocol).
  anatomy7   P1/P2/P4 at m <= 1e7: O1 (P+ tiers), O2 (smoothness), O3
             (omega/Omega/powerDefect), O6 (c-anatomy vs omega-matched P4).
  pratt7     O4: Pratt depth/nodes/breadth memoized over ALL primes <= 6.1e7
             (SPF sieve), per-population stats + DAG summary.
  orders7    O5: ord_p(2),(3),(5), cyclic index, Artin reference, mod-8 assert.
  quartic7   O7 at 1e7: quartic symbols of 2/3/5 on 1-mod-4 wings, Cornacchia
             a^2+b^2, Gauss hard selftest, non-phase-ness joints.
  probe9     the 1e9 window per the L35 protocol: window gate (+0.224068,
             n_twin=15577) then O1-O5 + O7 on P1w/P2w, O6 on window centers.
  defect     P3: prime wings of the 50 exact defect windows A=17..43
             (descriptive stratum; rho tier + 12-base MR, disclosed).
  summary    cross-population collation + candidate-law escalation notes.

Reuse lineage: factorization tiers follow tools/grave_depth_harness.py (SPF /
numpy trial division / Brent rho + deterministic MR); the registration/staged-log
skeleton follows tools/peel_bilinear_harness.py; the L35 gate reproduces
tools/packing_walk_harness.py stage w3 verbatim in protocol.
Intermediate JSON/NPY artifacts go to the scratch dir (env PRATT_WING_CACHE or
system temp); the repo stays clean except this file and the log.
"""

import json
import math
import os
import sys
import tempfile
import time
from fractions import Fraction

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
LOG_PATH = os.path.join(TOOLS, "pratt_wing_run1.log")
SCRATCH = os.environ.get("PRATT_WING_CACHE") or os.path.join(
    tempfile.gettempdir(), "pratt_wing_scratch")

SEED = 20260710
STAGE_TIME_CAP = 5400          # s; registered fallback: halve remaining workload, LOG it

N_BIG = 6 * 10 ** 7 + 2        # omega/prime sieve ceiling (L35 gate, packing_walk verbatim)
M_MED = 10 ** 7                # main m-scale
SPF_LIM = 61_000_000           # SPF sieve ceiling (covers p+1 <= 6e7+2 for every wing)
TD_LIM = 6_100_000_000         # numpy trial-division tier ceiling
PTD_LIM = 78_500               # trial-division prime table (isqrt(6.1e9) = 78102 < 78500)
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)   # deterministic < 3.186e23
MR_VALID = 318 * 10 ** 21

X9, W9 = 10 ** 9, 10 ** 6      # the L35 window protocol (packing_walk stage w3)
N_TWIN_7 = 280557              # L35 census counts (asserted)
N_TWIN_9 = 15577
P4_FACTOR = 4                  # P4 size = 4 x n_twin (registered)

Q31 = (5, 7, 11, 13, 17, 19, 23, 29, 31)

# exact true gaps G(A) and defect-window starts (peel_bilinear registration lineage)
G_EXACT = {17: 18, 19: 25, 23: 34, 29: 43, 31: 58, 37: 88, 41: 91, 43: 103}
DEFECT_R = {
    23: [12694428, 18165208, 19016903, 24487683],
    29: [200906185, 877375977],
    31: [21844264615],
    37: [1145973108145],
    41: [50077677123072],
    43: [233885349904190],
}
DEFECT_SCALES = (17, 19, 23, 29, 31, 37, 41, 43)


# ---------------------------------------------------------------- logging (append-only)

class Tee(object):
    def __init__(self, *streams):
        self.streams = streams

    def write(self, s):
        for st in self.streams:
            st.write(s)

    def flush(self):
        for st in self.streams:
            st.flush()


def install_log():
    fh = open(LOG_PATH, "a", encoding="ascii", errors="replace")
    try:
        sys.__stdout__.reconfigure(errors="replace")
    except Exception:
        pass
    sys.stdout = Tee(fh, sys.__stdout__)


def banner(name, sub=""):
    print("=" * 78)
    print("[%s] PRATT-WING %s  %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), name, sub))
    print("  seed=%d  numpy=%s  STAGE_TIME_CAP=%ds" % (SEED, np.__version__, STAGE_TIME_CAP))
    print("=" * 78)
    sys.stdout.flush()


def STOP(msg):
    print("STOP -- " + msg)
    print("STAGE VERDICT: STOP (selftest/design violation; later stages must not run)")
    sys.stdout.flush()
    sys.exit(1)


def assert_registered():
    if not os.path.exists(LOG_PATH):
        STOP("registration missing: run the selftest stage first")
    with open(LOG_PATH, "r", encoding="ascii", errors="replace") as f:
        if "PRE-REGISTRATION ENDS" not in f.read():
            STOP("registration missing: run the selftest stage first")


# ------------------------------------------------------- registration (printed FIRST)

WING_REF_B31 = sum(Fraction(1, q - 2) - Fraction(1, q - 1) for q in Q31)
CENTER_REF_B31 = sum(Fraction(1, q - 2) - Fraction(1, q) for q in Q31)

REGISTRATION = """
PRE-REGISTRATION -- PRATT-WING campaign (numeric reconnaissance of the structure
UNDER the primes: p-1 / p+1 anatomy and Pratt genealogy of twin wings, plus the
program's FIRST beyond-phase observable class O7).  Registered BEFORE any
measurement line.  Seed 20260710 (numpy default_rng; documented substreams
[SEED, k]: k=0 selftest samples, k=2 P2 matching at 1e7, k=4 P4 at 1e7,
k=9 populations at the 1e9 window).  STAGE_TIME_CAP = 5400 s per stage;
registered fallback: if a stage threatens the cap, HALVE the remaining
per-population workload and LOG the shrink -- never silently.  Log append-only,
ASCII; stages are separate argv invocations (house crash-resilience pattern).

NULL DESIGN -- decision (b), registered: prime-conditioned population; no parity
verdict is defined here; deviations from reference curves are navigation, not
laws.  Protocol: EXACT-MEASURED laws only; local-model reference curves
(Dickman for smoothness, cyclic-index/Artin constants, the E4-truncated
prediction for omega) are printed as DISCLOSED REFERENCES, never verdicts.
The window-foil protocol's sigma_I has no analogue in these populations; NO
parity verdicts are issuable anywhere in this campaign.

POPULATIONS (closed)
 P1 twin wings: all twin centers m <= 1e7 (expected n = 280557, MUST equal the
    L35 census count exactly); wings p = 6m-1 (type L) and q = 6m+1 (type R).
    PLUS the 1e9 probe stratum: m in [1e9, 1e9+1e6) per the L35 window protocol
    (packing_walk stage w3, segmented exact; expected n_twin = 15577).
 P2 isolated 6k+-1 primes, size-matched to P1 wings: same count per wing type,
    sampled seeded WITHOUT replacement from primes of the same type in the same
    m-bins (1e7 scale: 100 bins of width 1e5; 1e9 window: 20 bins of width 5e4)
    that are NOT twin wings (type L: 6k-1 prime AND 6k+1 composite; type R
    mirrored; twins pair only as (6m-1, 6m+1) since 6m+3 == 0 mod 3).
 P3 wings of the 50 exact defect windows A=17..43 (descriptive stratum, tiny n):
    A=17: 20 starts (full-period scan, calibration: first r=117); A=19: 20
    starts (first r=110); A=23: {12694428, 18165208, 19016903, 24487683};
    A=29: {200906185, 877375977}; A=31: {21844264615}; A=37: {1145973108145};
    A=41: {50077677123072} (L=90); A=43: {233885349904190} (L=102); window =
    centers r+1..r+L with L = G(A)-1; population = the PRIME wings among the
    2L wings of each window (a struck center can still carry one prime wing).
 P4 random centers 6m (control for c-anatomy): seeded sample of NON-twin m,
    n = 4 x n_twin at each scale (1e7: 1122228; 1e9 window: 62308).

OBSERVABLES (CLOSED LIST -- nothing may be added after this block)
 O1 largest-prime-factor tiers of p-1 AND p+1 per population: shares with
    P+ > x^(1/2); in (x^(1/3), x^(1/2)]; in (x^(1/4), x^(1/3)]; <= x^(1/4)
    (x = the factored value; integer-exact comparisons P^2 > x, P^3 > x, ...).
 O2 smoothness fractions of p-1 / p+1: P+ <= x^(1/2) and P+ <= x^(1/3).
 O3 omega / Omega / powerDefect (= Omega - omega) of p-1 and p+1.  NOTE
    (registered): omega(c) for twin centers IS the L35 collision law -- it is
    used as a CROSS-CHECK ONLY; re-claiming it is barred.
 O4 Pratt tree of each wing (recursive primality certificate down p-1 to 2):
    depth(2) = 0, depth(p) = 1 + max over distinct primes q | p-1 of depth(q);
    nodes(2) = 1, nodes(p) = 1 + sum over distinct q | p-1 of nodes(q) (tree
    semantics, DAG-memoized); breadth(p) = omega(p-1) (root degree).  Memoized
    over ALL primes <= 6.1e7 via the SPF sieve; TD/rho tiers per prime above.
    The Pratt DAG (all primes connected through their predecessors) summary:
    depth histogram by magnitude decade, max depth + witness chain.
 O5 multiplicative order of 2, 3, 5 in F_p per wing; cyclic index
    i_b = (p-1)/ord_b; share i_b = 1 (primitive root) vs the Artin reference;
    v_2(i_2) layer distribution.  CROSS-CHECK/HARD SELFTEST on every prime:
    i_2 even <=> 2 is a QR mod p <=> p == +-1 (mod 8).
 O6 c-anatomy beyond omega: P+(c) tiers and powerDefect(c) for twin centers vs
    omega-MATCHED reweighted P4 (the anti-L35 device): P4 reweighted so its
    omega(c) distribution equals P1's (weights w_k = share_P1(k)/share_P4(k);
    unmatched omega cells disclosed and dropped with their mass logged);
    surviving weighted contrasts of P+/powerDefect are ORTHOGONAL to the known
    collision law.  Unweighted contrast printed as reference.  Descriptive
    z only (weighted side uses effective n = (sum w)^2 / sum w^2).
 O7 THE BEYOND-PHASE CLASS (the program's FIRST beyond-phase observable class):
    for the 1-mod-4 wing of each twin (exactly one per pair: the wings sum to
    12m, so they are 1 and 3 mod 4): quartic residuacity of 2, 3, 5:
    s_b = b^((p-1)/4) mod p classified in mu_4 = {+1, -1, i, -i} (i.e. mu_4 via
    the order of s_b), with i canonicalized as x0 = min(x, p-x) where
    x^2 == -1 (mod p) (registered convention; the i/-i split is symmetric under
    the other choice).  PLUS the Gaussian representation p = a^2 + b^2
    (Cornacchia; normalized a odd > 0, b even > 0).  HARD SELFTEST on EVERY
    such prime: (2|p)_4 = 1 <=> 8 | b (Gauss's criterion) -- any single failure
    exits 1.  Comparison: quartic-symbol distributions, twin 1-mod-4 wings vs
    isolated 1-mod-4 primes (P2 members == 1 mod 4), overall and CONDITIONAL on
    the phase layer (p mod 8 for b=2; the QR layer s_b^2 = +1 vs -1 for every
    base).  REGISTERED EXPECTATION: NULL (Chebotarev equidistribution,
    twin-independent); the value is closing or cracking the last uncovered
    observable class.  Also logged: joint distribution (quartic symbol of 2) x
    (m mod 5 / m mod 7 / m mod 8) to confirm non-phase-ness empirically (no
    congruence in m should predict the CONDITIONAL symbol; the p mod 8
    stratification itself IS phase and is disclosed as such).

DISCLOSED REFERENCE CURVES (never verdicts):
 - Dickman (RANDOM-integer model): P(P+ > x^(1/2)) = ln 2 = 0.693147;
   P(P+ <= x^(1/2)) = 0.306853; P(P+ <= x^(1/3)) = rho(3) = 0.048608;
   P(P+ <= x^(1/4)) = rho(4) = 0.004911.  p-1 / p+1 of PRIMES are known to
   deviate (shifted-prime smoothness); any deviation is navigation.
 - Artin: density of primes with ord_b(p) = p-1 (i_b = 1) = 0.3739558136...
   for b in {2, 3, 5} (GRH reference).
 - E4-truncated omega references (exact L34 1/1/1/(q-3) split):
   center enrichment (L35): sum_(5<=q<=31)(1/(q-2) - 1/q) = 41209978/166424895
   = +0.247619 (all q <= 1e5 reference: +0.260416).  Wing-side twin-vs-isolated
   reference, derived BEFORE measurement from the same split: the twin
   condition makes each fixed side-class hit 1/(q-2), a single-prime condition
   makes it 1/(q-1); predicted omega(p+-1) excess (twin wing minus isolated
   wing, either side, q >= 5 layer), truncated B=31:
   sum_(5<=q<=31)(1/(q-2) - 1/(q-1)) = %s = %+0.6f.
   Forced small-prime layer (mechanical, disclosed): outer sides 6m-2 / 6m+2
   have v3 = 0 and v2 >= 1; inner sides equal the center 6m (v2, v3 >= 1) --
   the inner side of a twin wing IS the twin center; matching P1-vs-P2
   contrasts are always same-type same-side.
 - O7: Chebotarev NULL -- conditional symbol splits 1/2 : 1/2 within each phase
   layer, twin-independent.

SELFTESTS (all STOP: any failure exits 1)
 S1 SPF sieve vs independent trial division: full factorization match on a
    1e4-value seeded sample in [2, 6.1e7].
 S2 Pratt depth AND node count: memoized values vs brute-force recursion over
    an independent trial-division factorizer, ALL primes < 1e4.
 S3 multiplicative order of 2, 3, 5: factored-exponent algorithm vs brute-force
    cycle, ALL primes < 1e3 (bases coprime to p).
 S4 Gauss O7 criterion: brute-force quartic solvability of y^4 == 2 (mod p)
    vs (s_2 == 1) vs (8 | b), ALL primes p == 1 (mod 4) below 2000; PLUS the
    registered hard per-prime assert in every O7 measurement.
 S5 jacobi vs Euler criterion on 500 seeded (a, p).
 S6 L35 REGRESSION GATE (before ANY new observable is logged): reproduce the
    L35 collision law on P1 EXACTLY, per the packing_walk stage-w3 protocol
    (omega sieve to 6e7+2 counting DISTINCT primes; twin <=> both wings in the
    prime sieve; contrast = E[omega(6m)|twin] - E[omega(6m)|no-twin], m <= 1e7,
    printed %%+.6f): MUST print +0.211442 with n_twin = 280557.  The 1e9 stage
    carries its own gate: +0.224068 with n_twin = 15577 on the segmented-exact
    window.  Mismatch = STOP, report.
 S7 defect calibration: A=17 full-period scan yields 20 defect starts, first
    r = 117; A=19 yields 20 starts, first r = 110; every listed witness r has
    r clean, r+1..r+L struck, r+L+1 clean.

FACTORIZATION TIERS (house, grave_depth lineage): SPF sieve to 6.1e7 (int32);
numpy trial division over sieved primes <= 78500 for values <= 6.1e9 (remainder
after stripping all sub-sqrt hits is prime); Pollard rho (Brent) + deterministic
Miller-Rabin above, bases = the first 12 primes (2..37), deterministic for
n < 3.186e23 (Sorenson-Webster 2015) -- REGISTERED ADAPTATION (A=43 wings reach
1.5e15 > the 3.4e14 bound of the 7-base tier); completeness counted, target 0.

STAGES: selftest (this registration + S1-S7) -> anatomy7 (O1/O2/O3/O6 at 1e7)
-> pratt7 (O4) -> orders7 (O5) -> quartic7 (O7) -> probe9 (1e9 window: gate +
O1-O5 + O7 + O6 control) -> defect (P3, descriptive) -> summary.  The
observable list is CLOSED at this registration.
PRE-REGISTRATION ENDS -- measurements begin below this line.
""" % (WING_REF_B31, float(WING_REF_B31))

# ------------------------------------------------------------------ sieves / tiers

def prime_sieve(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def primes_upto(n):
    return [int(p) for p in np.flatnonzero(prime_sieve(n))]


def omega_sieve(n):
    """int8: number of DISTINCT prime factors (packing_walk_harness verbatim)."""
    lit = np.zeros(n + 1, dtype=np.int8)
    isp = prime_sieve(n)
    for p in np.flatnonzero(isp):
        p = int(p)
        lit[p::p] += 1
    return lit


def omega_cached():
    """omega(n) for n <= N_BIG; shares the packing_walk cache when present."""
    for d in (os.environ.get("PACKING_WALK_CACHE"), SCRATCH, tempfile.gettempdir()):
        if not d:
            continue
        path = os.path.join(d, "packing_walk_omega_6e7.npy")
        if os.path.exists(path):
            lit = np.load(path)
            if lit.size == N_BIG + 1:
                print("[omega sieve] loaded cache %s" % path)
                return lit
    t0 = time.time()
    lit = omega_sieve(N_BIG)
    print("[omega sieve] built omega(n), n <= %d in %.1fs" % (N_BIG, time.time() - t0))
    try:
        os.makedirs(SCRATCH, exist_ok=True)
        np.save(os.path.join(SCRATCH, "packing_walk_omega_6e7.npy"), lit)
    except OSError:
        pass
    return lit


_SPF = None
_PTD = None
_SMALL = None


def setup_tables():
    """SPF sieve to 6.1e7 (cached npy) + trial-division prime table to 78500."""
    global _SPF, _PTD, _SMALL
    if _SPF is not None:
        return
    t0 = time.time()
    os.makedirs(SCRATCH, exist_ok=True)
    spf_path = os.path.join(SCRATCH, "pratt_wing_spf_61e6.npy")
    if os.path.exists(spf_path):
        _SPF = np.load(spf_path)
        assert _SPF.size == SPF_LIM + 1
        src = "cache"
    else:
        spf = np.zeros(SPF_LIM + 1, dtype=np.int32)
        for i in range(2, int(math.isqrt(SPF_LIM)) + 1):
            if spf[i] == 0:
                sl = spf[i * i::i]
                sl[sl == 0] = i
        _SPF = spf
        try:
            np.save(spf_path, spf)
        except OSError:
            pass
        src = "built"
    sieve = np.ones(PTD_LIM + 1, bool)
    sieve[:2] = False
    for i in range(2, int(PTD_LIM ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    _PTD = np.flatnonzero(sieve).astype(np.int64)
    _SMALL = [int(p) for p in _PTD[_PTD <= 3000]]
    print("  tables: SPF <= %d (%s), %d TD primes <= %d (%.1fs)"
          % (SPF_LIM, src, _PTD.size, PTD_LIM, time.time() - t0))
    sys.stdout.flush()


def fac_pairs_spf(x):
    """[(q, e), ...] ascending for 2 <= x <= SPF_LIM (SPF walk; spf==0 <=> prime)."""
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


FAC_STATS = dict(incomplete=0, total=0)


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


def _fac_large(x, out):
    """Distinct primes of x (rho tier) -> set `out` (grave_depth lineage)."""
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
    """Full factorization [(q, e), ...] ascending on every tier; completeness counted."""
    x = int(x)
    FAC_STATS['total'] += 1
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
            out.append((rem, 1))    # remainder-prime argument (two > sqrt would exceed x)
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
        FAC_STATS['incomplete'] += 1
        return None
    return out


def is_prime_any(v):
    v = int(v)
    if v < 2:
        return False
    if v <= SPF_LIM:
        return _SPF[v] == 0
    if v <= TD_LIM:
        lim = math.isqrt(v)
        k = int(np.searchsorted(_PTD, lim, 'right'))
        return not np.any((v % _PTD[:k]) == 0)
    return is_prime_mr(v)


def jacobi(a, n):
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


# ------------------------------------------------------------------ anatomy / orders

def anatomy_of(fp):
    """(omega, Omega, powerDefect, P+) from factor pairs."""
    om = len(fp)
    Om = sum(e for _, e in fp)
    return om, Om, Om - om, fp[-1][0]


def tier_of(x, P):
    """0: P+ > x^(1/2); 1: (x^(1/3), x^(1/2)]; 2: (x^(1/4), x^(1/3)]; 3: <= x^(1/4)."""
    if P * P > x:
        return 0
    if P * P * P > x:
        return 1
    if P * P * P * P > x:
        return 2
    return 3


def mult_order(b, p, fp):
    """ord_p(b) from the factorization fp of p-1 (b coprime to p)."""
    o = p - 1
    for q, e in fp:
        for _ in range(e):
            if o % q:
                break
            if pow(b, o // q, p) == 1:
                o //= q
            else:
                break
    return o


# ------------------------------------------------------------------ Pratt layer

_DEPTH = None      # int8 over [0, SPF_LIM]: Pratt depth at prime indices
_NODES = None      # int32: Pratt tree node count at prime indices
_BIGP = {}         # big-tier memo p -> (depth, nodes)


def setup_pratt():
    """Memoize Pratt depth/nodes for ALL primes <= SPF_LIM (ascending SPF walk)."""
    global _DEPTH, _NODES
    if _DEPTH is not None:
        return
    setup_tables()
    dpath = os.path.join(SCRATCH, "pratt_wing_depth.npy")
    npath = os.path.join(SCRATCH, "pratt_wing_nodes.npy")
    if os.path.exists(dpath) and os.path.exists(npath):
        _DEPTH = np.load(dpath)
        _NODES = np.load(npath)
        assert _DEPTH.size == SPF_LIM + 1 and _NODES.size == SPF_LIM + 1
        print("  pratt memo: loaded cache (%s)" % SCRATCH)
        sys.stdout.flush()
        return
    t0 = time.time()
    depth = np.zeros(SPF_LIM + 1, dtype=np.int8)
    nodes = np.zeros(SPF_LIM + 1, dtype=np.int32)
    depth[2] = 0
    nodes[2] = 1
    spf = _SPF
    primes = np.flatnonzero(spf[2:] == 0) + 2
    for p in primes[1:].tolist():                    # ascending, factors of p-1 < p
        x = p - 1
        dmax = 0
        nsum = 1
        while x > 1:
            q = int(spf[x])
            if q == 0:
                q = x
            d = depth[q]
            if d > dmax:
                dmax = d
            nsum += nodes[q]
            while x % q == 0:
                x //= q
        depth[p] = dmax + 1
        nodes[p] = nsum
    _DEPTH = depth
    _NODES = nodes
    try:
        np.save(dpath, depth)
        np.save(npath, nodes)
    except OSError:
        pass
    print("  pratt memo: depth/nodes for %d primes <= %d built in %.1fs"
          % (primes.size, SPF_LIM, time.time() - t0))
    sys.stdout.flush()


def pratt_big(p):
    """(depth, nodes) on any tier (recursive above SPF_LIM; memoized)."""
    if p <= SPF_LIM:
        return int(_DEPTH[p]), int(_NODES[p])
    r = _BIGP.get(p)
    if r is not None:
        return r
    fp = fac_pairs_any(p - 1)
    if fp is None:
        STOP("incomplete factorization of p-1 in pratt_big at p=%d" % p)
    d = 0
    n = 1
    for q, _ in fp:
        dq, nq = pratt_big(q)
        if dq > d:
            d = dq
        n += nq
    _BIGP[p] = (d + 1, n)
    return _BIGP[p]


def deep_chain(p):
    """Witness chain p -> q -> ... -> 2 following a max-depth child each step."""
    chain = [p]
    while p != 2:
        fp = fac_pairs_any(p - 1) if p > SPF_LIM else fac_pairs_spf(p - 1)
        want = (pratt_big(p)[0] if p > SPF_LIM else int(_DEPTH[p])) - 1
        nxt = None
        for q, _ in fp:
            dq = pratt_big(q)[0] if q > SPF_LIM else int(_DEPTH[q])
            if dq == want and (nxt is None or q > nxt):
                nxt = q
        p = nxt
        chain.append(p)
    return chain


# ------------------------------------------------------------------ quartic layer (O7)

GAUSS_CHECKS = dict(n=0, fail=0)


def sqrt_m1(p):
    """Canonical x0 = min(x, p-x) with x^2 == -1 (mod p); p == 1 (mod 4)."""
    d = 2
    while jacobi(d, p) != -1:
        d += 1
    x = pow(d, (p - 1) // 4, p)
    if x * x % p != p - 1:
        STOP("sqrt(-1) failed at p=%d (d=%d)" % (p, d))
    return min(x, p - x)


def cornacchia(p, x0):
    """p = a^2 + b^2, a odd > 0, b even > 0 (p == 1 mod 4)."""
    r0, r1 = p, x0
    lim = math.isqrt(p)
    while r1 > lim:
        r0, r1 = r1, r0 % r1
    a = r1
    b2 = p - a * a
    b = math.isqrt(b2)
    if b * b != b2:
        STOP("cornacchia failed at p=%d" % p)
    if a % 2 == 0:
        a, b = b, a
    return a, b


def quartic_symbol(b, p, x0):
    """0: +1, 1: -1, 2: i, 3: -i  (s = b^((p-1)/4) mod p in mu_4)."""
    s = pow(b, (p - 1) // 4, p)
    if s == 1:
        return 0
    if s == p - 1:
        return 1
    if s == x0:
        return 2
    if s == p - x0:
        return 3
    STOP("quartic symbol outside mu_4 at p=%d b=%d" % (p, b))


def o7_measure(p):
    """(cls2, cls3, cls5, a, b) with the Gauss hard selftest; p == 1 (mod 4).
    A base b with p == b (only p=5) yields symbol code -1 (excluded from tables)."""
    x0 = sqrt_m1(p)
    a, bb = cornacchia(p, x0)
    cls = []
    for base in (2, 3, 5):
        cls.append(-1 if p == base else quartic_symbol(base, p, x0))
    GAUSS_CHECKS['n'] += 1
    if (cls[0] == 0) != (bb % 8 == 0):
        GAUSS_CHECKS['fail'] += 1
        STOP("GAUSS CRITERION FAILED at p=%d: cls2=%d b=%d" % (p, cls[0], bb))
    return cls[0], cls[1], cls[2], a, bb


# ------------------------------------------------------------------ statistics helpers

def welch_z(m1, s1, n1, m2, s2, n2):
    se = math.sqrt(s1 * s1 / max(n1, 1) + s2 * s2 / max(n2, 1))
    return (m1 - m2) / se if se > 0 else float('nan')


def share_z(p1, n1, p2, n2):
    se = math.sqrt(p1 * (1 - p1) / max(n1, 1) + p2 * (1 - p2) / max(n2, 1))
    return (p1 - p2) / se if se > 0 else float('nan')


def ms(arr):
    a = np.asarray(arr, dtype=np.float64)
    return float(a.mean()), float(a.std()), a.size


class StageClock(object):
    """Registered halving fallback: call .factor() at population boundaries."""

    def __init__(self):
        self.t0 = time.time()
        self.halved = False

    def factor(self):
        if not self.halved and time.time() - self.t0 > STAGE_TIME_CAP:
            self.halved = True
            print("  RUNTIME FALLBACK: stage cap %ds exceeded -- HALVING the remaining"
                  " per-population workload (registered fallback, logged)" % STAGE_TIME_CAP)
            sys.stdout.flush()
        return 2 if self.halved else 1


# ------------------------------------------------------------------ populations

def build_pop7():
    """P1 twins / P2 isolated (bin-matched) / P4 random centers at m <= 1e7 (cached)."""
    path = os.path.join(SCRATCH, "pratt_wing_pop7.npz")
    if os.path.exists(path):
        z = np.load(path)
        return z['twins'], z['isoL'], z['isoR'], z['p4']
    isp = prime_sieve(N_BIG)
    m = np.arange(1, M_MED + 1, dtype=np.int64)
    pl = isp[6 * m - 1]
    pr = isp[6 * m + 1]
    twin = pl & pr
    twins = m[twin]
    if twins.size != N_TWIN_7:
        STOP("twin census mismatch at 1e7: %d != %d" % (twins.size, N_TWIN_7))
    candL = m[pl & ~pr]           # isolated type L: 6k-1 prime, 6k+1 composite
    candR = m[pr & ~pl]           # isolated type R
    rng = np.random.default_rng([SEED, 2])
    isoL, isoR = [], []
    BINW = 10 ** 5
    for b0 in range(1, M_MED + 1, BINW):
        b1 = b0 + BINW
        need = int(((twins >= b0) & (twins < b1)).sum())
        for cand, out in ((candL, isoL), (candR, isoR)):
            pool = cand[(cand >= b0) & (cand < b1)]
            if pool.size < need:
                STOP("isolated pool too small in bin %d (%d < %d)" % (b0, pool.size, need))
            out.append(np.sort(rng.choice(pool, size=need, replace=False)))
    isoL = np.concatenate(isoL)
    isoR = np.concatenate(isoR)
    rng4 = np.random.default_rng([SEED, 4])
    nontwin = m[~twin]
    p4 = np.sort(rng4.choice(nontwin, size=P4_FACTOR * N_TWIN_7, replace=False))
    np.savez(path, twins=twins, isoL=isoL, isoR=isoR, p4=p4)
    print("  populations 1e7: twins=%d isoL=%d isoR=%d p4=%d (bin width %d, seeds"
          " [%d,2]/[%d,4]) -> cached" % (twins.size, isoL.size, isoR.size, p4.size,
                                         BINW, SEED, SEED))
    sys.stdout.flush()
    return twins, isoL, isoR, p4


def window_triple9():
    """Segmented exact (Omega, omega) triple over m in [X9, X9+W9) --
    packing_walk_harness.window_triple protocol verbatim (want_center=True)."""
    lim = int(math.isqrt(6 * (X9 + W9) + 2)) + 1
    ps = primes_upto(lim)
    out = {}
    t0 = time.time()
    for off in (-1, 1, 0):
        vals = 6 * (X9 + np.arange(W9, dtype=np.int64)) + off
        rem = vals.copy()
        big = np.zeros(W9, dtype=np.int16)
        lit = np.zeros(W9, dtype=np.int16)
        for p in ps:
            if p < 5:
                if off != 0:
                    continue
                idx = np.arange(W9)
            else:
                if off == 0:
                    r = 0
                else:
                    inv6 = pow(6, -1, p)
                    r = inv6 if off == -1 else (p - inv6) % p
                first = (r - X9) % p
                if first >= W9:
                    continue
                idx = np.arange(first, W9, p)
            lit[idx] += 1
            rem[idx] //= p
            big[idx] += 1
            cur = idx[rem[idx] % p == 0]
            while cur.size:
                rem[cur] //= p
                big[cur] += 1
                cur = cur[rem[cur] % p == 0]
        left = rem > 1
        big[left] += 1
        lit[left] += 1
        out[off] = (big.astype(np.int32), lit.astype(np.int32))
    print("  [window X=%.1e W=%.0e] exact triple grades in %.1fs (primes to %d)"
          % (X9, W9, time.time() - t0, ps[-1]))
    sys.stdout.flush()
    return out


def build_pop9():
    """Window populations at [1e9, 1e9+1e6): twins / isolated (bin-matched) / P4."""
    path = os.path.join(SCRATCH, "pratt_wing_pop9.npz")
    if os.path.exists(path):
        z = np.load(path)
        return z['twins'], z['isoL'], z['isoR'], z['p4'], float(z['gate']), int(z['gaten'])
    g = window_triple9()
    bigL, litL = g[-1]
    bigC, litC = g[0]
    bigR, litR = g[1]
    m = X9 + np.arange(W9, dtype=np.int64)
    pl = bigL == 1
    pr = bigR == 1
    twin = pl & pr
    twins = m[twin]
    wC = litC.astype(np.float64)
    gate = float(wC[twin].mean() - wC[~twin].mean())
    twins_n = int(twins.size)
    candL = m[pl & ~pr]
    candR = m[pr & ~pl]
    rng = np.random.default_rng([SEED, 9])
    isoL, isoR = [], []
    BINW = 5 * 10 ** 4
    for b0 in range(X9, X9 + W9, BINW):
        b1 = b0 + BINW
        need = int(((twins >= b0) & (twins < b1)).sum())
        for cand, out in ((candL, isoL), (candR, isoR)):
            pool = cand[(cand >= b0) & (cand < b1)]
            if pool.size < need:
                STOP("isolated pool too small in 1e9 bin %d" % b0)
            out.append(np.sort(rng.choice(pool, size=need, replace=False)))
    isoL = np.concatenate(isoL)
    isoR = np.concatenate(isoR)
    p4 = np.sort(rng.choice(m[~twin], size=P4_FACTOR * twins_n, replace=False))
    np.savez(path, twins=twins, isoL=isoL, isoR=isoR, p4=p4, gate=gate, gaten=twins_n)
    return twins, isoL, isoR, p4, gate, twins_n


# ------------------------------------------------------------------ defect scan (P3)

def defect_scan(A):
    """Full-period scan for struck runs of length exactly G(A)-1 (clean ends);
    returns sorted starts r (r clean, r+1..r+L struck, r+L+1 clean)."""
    qs = [q for q in primes_upto(A) if q >= 5]
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
    qs = [q for q in primes_upto(A) if q >= 5]
    arr = np.arange(r, r + L + 2, dtype=np.int64)
    sm = np.zeros(arr.size, dtype=bool)
    for q in qs:
        i6 = pow(6, -1, q)
        sm |= (arr % q == i6) | (arr % q == (q - i6) % q)
    return (not sm[0]) and bool(sm[1:L + 1].all()) and (not sm[L + 1])


# ================================================================== stage: selftest

def stage_selftest():
    banner("SELFTEST", "pre-registration + S1-S7 STOP selftests")
    print(REGISTRATION)
    print("registration constants: wing-side truncated reference (B=31) = %s = %+.6f;"
          % (WING_REF_B31, float(WING_REF_B31)))
    print("  center reference (L34/E4, B=31) = %s = %+.6f"
          % (CENTER_REF_B31, float(CENTER_REF_B31)))
    sys.stdout.flush()
    t0 = time.time()
    setup_tables()
    rng = np.random.default_rng([SEED, 0])

    # S1: SPF vs independent trial division on 1e4 sample
    def td_pairs(x):
        out = []
        d = 2
        while d * d <= x:
            if x % d == 0:
                e = 0
                while x % d == 0:
                    x //= d
                    e += 1
                out.append((d, e))
            d += 1
        if x > 1:
            out.append((x, 1))
        return out
    xs = rng.integers(2, SPF_LIM + 1, 10 ** 4)
    for x in xs.tolist():
        if fac_pairs_spf(int(x)) != td_pairs(int(x)):
            STOP("S1: SPF != trial division at x=%d" % x)
    print("S1 SPF vs trial division on 1e4 sample in [2, %d] -> PASS" % SPF_LIM)
    sys.stdout.flush()

    # S2: Pratt depth/nodes memo vs brute force below 1e4
    setup_pratt()

    def pratt_brute(p, memo):
        if p == 2:
            return 0, 1
        r = memo.get(p)
        if r is not None:
            return r
        d = 0
        n = 1
        for q, _ in td_pairs(p - 1):
            dq, nq = pratt_brute(q, memo)
            d = max(d, dq)
            n += nq
        memo[p] = (d + 1, n)
        return memo[p]
    memo = {}
    for p in primes_upto(10 ** 4):
        bd, bn = pratt_brute(p, memo)
        if bd != int(_DEPTH[p]) or bn != int(_NODES[p]):
            STOP("S2: Pratt memo mismatch at p=%d: (%d,%d) vs (%d,%d)"
                 % (p, int(_DEPTH[p]), int(_NODES[p]), bd, bn))
    print("S2 Pratt depth+nodes memo vs brute-force recursion, ALL primes < 1e4 -> PASS")
    sys.stdout.flush()

    # S3: multiplicative order vs brute force below 1e3
    for p in primes_upto(10 ** 3 - 1):
        if p < 7:
            continue
        fp = fac_pairs_spf(p - 1)
        for b in (2, 3, 5):
            t = b % p
            k = 1
            while t != 1:
                t = t * b % p
                k += 1
            if k != mult_order(b, p, fp):
                STOP("S3: order mismatch at p=%d b=%d" % (p, b))
    print("S3 mult_order(2,3,5) vs brute-force cycle, ALL primes in [7, 1e3) -> PASS")

    # S4: Gauss O7 criterion brute force below 2000
    n4 = 0
    for p in primes_upto(2000):
        if p % 4 != 1:
            continue
        x0 = sqrt_m1(p)
        a, bb = cornacchia(p, x0)
        if a * a + bb * bb != p or a % 2 != 1 or bb % 2 != 0:
            STOP("S4: Cornacchia normalization failed at p=%d" % p)
        s2 = quartic_symbol(2, p, x0)
        brute = any(pow(y, 4, p) == 2 % p for y in range(1, p))
        if brute != (s2 == 0) or brute != (bb % 8 == 0):
            STOP("S4: Gauss criterion mismatch at p=%d (brute=%s s2=%d b=%d)"
                 % (p, brute, s2, bb))
        n4 += 1
    print("S4 Gauss criterion (y^4==2 solvable <=> s_2==1 <=> 8|b), %d primes"
          " p==1 mod 4 below 2000 -> PASS" % n4)

    # S5: jacobi vs Euler criterion
    small_primes = primes_upto(2000)
    for _ in range(500):
        p = int(small_primes[int(rng.integers(3, len(small_primes)))])
        a = int(rng.integers(1, p))
        e = pow(a, (p - 1) // 2, p)
        e = -1 if e == p - 1 else e
        if jacobi(a, p) != e:
            STOP("S5: jacobi(%d,%d) != Euler criterion" % (a, p))
    print("S5 jacobi == Euler criterion on 500 seeded (a, p) -> PASS")
    sys.stdout.flush()

    # S6: L35 REGRESSION GATE (packing_walk stage-w3 protocol, verbatim)
    lit = omega_cached()
    isp = prime_sieve(N_BIG)
    m = np.arange(1, M_MED + 1, dtype=np.int64)
    wC = lit[6 * m].astype(np.float64)
    twin = isp[6 * m - 1] & isp[6 * m + 1]
    n1 = int(twin.sum())
    d = float(wC[twin].mean() - wC[~twin].mean())
    m1, s1 = float(wC[twin].mean()), float(wC[twin].std())
    m2, s2 = float(wC[~twin].mean()), float(wC[~twin].std())
    z = welch_z(m1, s1, n1, m2, s2, int((~twin).sum()))
    print("S6 L35 REGRESSION GATE (m <= 1e7, exhaustive):")
    print("    E[omega_C | twin]    = %.6f   (n_twin = %d)" % (m1, n1))
    print("    E[omega_C | no-twin] = %.6f   (n = %d)" % (m2, int((~twin).sum())))
    print("    contrast = %+.6f   z = %+8.2f" % (d, z))
    if ("%+.6f" % d) != "+0.211442" or n1 != N_TWIN_7:
        STOP("S6: L35 gate mismatch: contrast %+.6f (need +0.211442), n_twin %d"
             " (need %d)" % (d, n1, N_TWIN_7))
    print("    reproduces L35 EXACTLY (+0.211442, n_twin=280557) -> PASS")
    sys.stdout.flush()

    # S7: defect calibration + witness verification
    d17 = defect_scan(17)
    if len(d17) != 20 or d17[0] != 117 or 502 not in d17:
        STOP("S7: A=17 scan calibration failed: n=%d first=%s" % (len(d17), d17[:3]))
    d19 = defect_scan(19)
    if len(d19) != 20 or d19[0] != 110:
        STOP("S7: A=19 scan calibration failed: n=%d first=%s" % (len(d19), d19[:3]))
    for A, rs in sorted(DEFECT_R.items()):
        L = G_EXACT[A] - 1
        for r in rs:
            if not struck_ok(r, L, A):
                STOP("S7: defect witness fails at A=%d r=%d" % (A, r))
    print("S7 defect calibration: A=17 -> 20 starts, first r=117 (502 present);"
          " A=19 -> 20 starts, first r=110; all listed witnesses verified -> PASS")
    os.makedirs(SCRATCH, exist_ok=True)
    with open(os.path.join(SCRATCH, "pratt_wing_defects.json"), "w") as f:
        json.dump({"17": d17, "19": d19}, f)
    print("SELFTEST verdict: ALL S1-S7 PASS (%.1fs); defect starts cached -> %s"
          % (time.time() - t0, SCRATCH))
    sys.stdout.flush()


# ------------------------------------------------------------------ measurement cores

def measure_values(vals):
    """(omega, Omega, powdef, tier) int arrays for a list of values <= SPF_LIM."""
    n = len(vals)
    om = np.empty(n, np.int16)
    Om = np.empty(n, np.int16)
    tr = np.empty(n, np.int8)
    for i, x in enumerate(vals):
        fp = fac_pairs_spf(x)
        o, O, _, P = anatomy_of(fp)
        om[i] = o
        Om[i] = O
        tr[i] = tier_of(x, P)
    return om, Om, (Om - om), tr


def fmt_anatomy(label, om, Om, pd, tr):
    n = om.size
    sh = [float((tr == k).mean()) for k in range(4)]
    print("  %-14s n=%7d | tiers >x^1/2:%.4f (x^1/3,x^1/2]:%.4f (x^1/4,x^1/3]:%.4f"
          " <=x^1/4:%.4f" % (label, n, sh[0], sh[1], sh[2], sh[3]))
    print("  %-14s smooth: P+<=x^1/2 %.4f  P+<=x^1/3 %.4f | omega %.4f+-%.3f"
          "  Omega %.4f+-%.3f  powdef %.4f+-%.3f"
          % ("", 1 - sh[0], sh[2] + sh[3], om.mean(), om.std(), Om.mean(), Om.std(),
             float(pd.mean()), float(pd.std())))
    return dict(n=int(n), tiers=sh, om=float(om.mean()), om_sd=float(om.std()),
                Om=float(Om.mean()), Om_sd=float(Om.std()),
                pd=float(pd.mean()), pd_sd=float(pd.std()))


def contrast_line(tag, a, b, stat_keys=("om", "Om", "pd")):
    parts = []
    for k in stat_keys:
        z = welch_z(a[k], a[k + "_sd"], a["n"], b[k], b[k + "_sd"], b["n"])
        parts.append("%s %+9.6f z %+7.2f" % (k, a[k] - b[k], z))
    zt = [share_z(a["tiers"][j], a["n"], b["tiers"][j], b["n"]) for j in range(4)]
    print("  DESCRIPTIVE contrast %-18s %s" % (tag, " | ".join(parts)))
    print("    tier-share deltas: " + "  ".join(
        "t%d %+8.5f z %+6.1f" % (j, a["tiers"][j] - b["tiers"][j], zt[j])
        for j in range(4)))


# ================================================================== stage: anatomy7

def stage_anatomy7():
    assert_registered()
    banner("ANATOMY7", "O1/O2/O3 on p-1 and p+1; O6 c-anatomy (m <= 1e7)")
    clock = StageClock()
    setup_tables()
    twins, isoL, isoR, p4 = build_pop7()
    print("  populations: twins=%d isoL=%d isoR=%d p4=%d" %
          (twins.size, isoL.size, isoR.size, p4.size))
    print("  DISCLOSED REFERENCES (never verdicts): Dickman t0=0.6931 t1=0.2582"
          " t2=0.0437 t3=0.0049; smooth(1/2)=0.3069 smooth(1/3)=0.0486;")
    print("    E4 wing-side twin-vs-isolated omega excess (B=31) = %+.6f;"
          " center (L35) = %+.6f (trunc) / +0.260416 (q<=1e5)"
          % (float(WING_REF_B31), float(CENTER_REF_B31)))
    print("  NOTE: inner side of a twin wing IS the center 6m; outer sides 6m-2/6m+2"
          " have v3=0, v2>=1 (mechanical layer, disclosed).")
    sys.stdout.flush()

    pops = {}
    res = {}
    plan = [("P1.L", (6 * twins - 1).tolist()), ("P1.R", (6 * twins + 1).tolist()),
            ("P2.L", (6 * isoL - 1).tolist()), ("P2.R", (6 * isoR + 1).tolist())]
    for name, ps in plan:
        f = clock.factor()
        if f > 1:
            ps = ps[::f]
            print("  (halved %s to n=%d)" % (name, len(ps)))
        t0 = time.time()
        for delta, dlab in ((-1, "p-1"), (1, "p+1")):
            vals = [p + delta for p in ps]
            om, Om, pd, tr = measure_values(vals)
            res[(name, dlab)] = fmt_anatomy("%s %s" % (name, dlab), om, Om, pd, tr)
        pops[name] = ps
        print("  [%s measured in %.1fs]" % (name, time.time() - t0))
        sys.stdout.flush()

    print("\n-- O1/O2/O3 twin-vs-isolated contrasts (same type, same side;"
          " DESCRIPTIVE, no verdicts) --")
    for t in ("L", "R"):
        for dlab in ("p-1", "p+1"):
            contrast_line("P1.%s-P2.%s %s" % (t, t, dlab),
                          res[("P1.%s" % t, dlab)], res[("P2.%s" % t, dlab)])
    print("  reference (E4-truncated, disclosed): omega excess ~ %+.6f on each"
          " side; deviations are navigation, not laws." % float(WING_REF_B31))
    sys.stdout.flush()

    # ---- O6: c-anatomy beyond omega (anti-L35 reweighting device)
    print("\n-- O6: c-anatomy of twin centers vs omega-MATCHED reweighted P4 --")
    f = clock.factor()
    tw_use = twins.tolist()[::f]
    p4_use = p4.tolist()[::f]
    if f > 1:
        print("  (halved O6 populations)")
    t0 = time.time()
    om1, Om1, pd1, tr1 = measure_values([6 * m for m in tw_use])
    om4, Om4, pd4, tr4 = measure_values([6 * m for m in p4_use])
    print("  [O6 centers measured in %.1fs]" % (time.time() - t0))
    a1 = fmt_anatomy("P1 c=6m", om1, Om1, pd1, tr1)
    a4 = fmt_anatomy("P4 c=6m", om4, Om4, pd4, tr4)
    print("  O3 CROSS-CHECK ONLY (re-claiming barred; L35 owns this): "
          "E[omega_C|twin] - E[omega_C|P4] = %+.6f" % (a1["om"] - a4["om"]))
    contrast_line("O6 unweighted (ref)", a1, a4, stat_keys=("pd",))
    # reweight P4 to P1's omega(c) distribution
    kmax = int(max(om1.max(), om4.max()))
    c1 = np.bincount(om1, minlength=kmax + 1).astype(np.float64)
    c4 = np.bincount(om4, minlength=kmax + 1).astype(np.float64)
    s1, s4 = c1 / c1.sum(), c4 / c4.sum()
    wk = np.zeros(kmax + 1)
    ok = (c4 > 0)
    wk[ok] = s1[ok] / np.maximum(s4[ok], 1e-300)
    dropped = float(s1[~ok].sum())
    print("  reweighting: omega cells 1..%d, P1 mass in cells absent from P4:"
          " %.6f (disclosed%s)" % (kmax, dropped,
                                   "; dropped" if dropped > 0 else ""))
    w = wk[om4]
    sw = float(w.sum())
    neff = sw * sw / float((w * w).sum())
    print("  weighted P4: sum w = %.1f, effective n = %.1f" % (sw, neff))

    def wmean_std(x):
        mu = float((w * x).sum() / sw)
        var = float((w * (x - mu) ** 2).sum() / sw)
        return mu, math.sqrt(max(var, 0.0))

    wm_om = wmean_std(om4.astype(np.float64))
    print("  check: weighted E[omega(c)|P4] = %.6f vs P1 %.6f (must match to ~1e-6"
          " up to dropped mass)" % (wm_om[0], a1["om"]))
    rows = [("powdef(c)", pd1.astype(np.float64), pd4.astype(np.float64))]
    for j in range(4):
        rows.append(("tier%d(c)" % j, (tr1 == j).astype(np.float64),
                     (tr4 == j).astype(np.float64)))
    o6 = {}
    for lab, x1, x4 in rows:
        mu1, sd1 = float(x1.mean()), float(x1.std())
        mu4w, sd4w = wmean_std(x4)
        z = welch_z(mu1, sd1, x1.size, mu4w, sd4w, neff)
        o6[lab] = dict(p1=mu1, p4w=mu4w, d=mu1 - mu4w, z=z)
        print("  O6 %-10s P1 %.6f | P4-reweighted %.6f | delta %+.6f  z %+7.2f"
              " (DESCRIPTIVE; orthogonal to L35 by construction)"
              % (lab, mu1, mu4w, mu1 - mu4w, z))
    with open(os.path.join(SCRATCH, "pratt_wing_anatomy7.json"), "w") as f2:
        json.dump(dict(res={"%s|%s" % k: v for k, v in res.items()},
                       o6=o6, c_p1=a1, c_p4=a4), f2)
    print("[anatomy7 done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: pratt7

def stage_pratt7():
    assert_registered()
    banner("PRATT7", "O4: Pratt depth/nodes/breadth per wing + DAG summary (m <= 1e7)")
    clock = StageClock()
    setup_tables()
    setup_pratt()
    twins, isoL, isoR, p4 = build_pop7()
    plan = [("P1.L", 6 * twins - 1), ("P1.R", 6 * twins + 1),
            ("P2.L", 6 * isoL - 1), ("P2.R", 6 * isoR + 1)]
    res = {}
    for name, ps in plan:
        f = clock.factor()
        ps = ps[::f]
        if f > 1:
            print("  (halved %s)" % name)
        dep = _DEPTH[ps].astype(np.int64)
        nod = _NODES[ps].astype(np.int64)
        t0 = time.time()
        bre = np.empty(ps.size, np.int16)
        for i, p in enumerate(ps.tolist()):
            bre[i] = len(fac_pairs_spf(p - 1))
        hist = np.bincount(dep, minlength=13).astype(np.float64)
        hist /= hist.sum()
        imax = int(np.argmax(dep))
        pmax = int(ps[imax])
        res[name] = dict(n=int(ps.size),
                         dep=float(dep.mean()), dep_sd=float(dep.std()),
                         nod=float(nod.mean()), nod_sd=float(nod.std()),
                         bre=float(bre.mean()), bre_sd=float(bre.std()),
                         dmax=int(dep.max()), nmax=int(nod.max()),
                         hist=[float(h) for h in hist[:13]])
        print("  %-5s n=%7d depth %.4f+-%.3f (max %d) | nodes %.2f+-%.2f (max %d)"
              " | breadth %.4f+-%.3f  [%.1fs]"
              % (name, ps.size, dep.mean(), dep.std(), dep.max(), nod.mean(),
                 nod.std(), nod.max(), bre.mean(), bre.std(), time.time() - t0))
        print("        depth hist %%: " + " ".join(
            "%d:%.3f" % (k, 100 * hist[k]) for k in range(len(hist)) if hist[k] > 0))
        print("        max-depth witness p=%d chain %s"
              % (pmax, "->".join(str(c) for c in deep_chain(pmax))))
        sys.stdout.flush()
    print("\n-- O4 twin-vs-isolated contrasts (DESCRIPTIVE) --")
    for t in ("L", "R"):
        a, b = res["P1.%s" % t], res["P2.%s" % t]
        for k in ("dep", "nod", "bre"):
            z = welch_z(a[k], a[k + "_sd"], a["n"], b[k], b[k + "_sd"], b["n"])
            print("  P1.%s-P2.%s %-4s delta %+9.6f  z %+7.2f" %
                  (t, t, k, a[k] - b[k], z))
    # DAG summary over ALL primes <= SPF_LIM
    print("\n-- Pratt DAG summary (ALL primes <= %d; all primes connected through"
          " their predecessors) --" % SPF_LIM)
    primes = np.flatnonzero(_SPF[2:] == 0) + 2
    dall = _DEPTH[primes].astype(np.int64)
    h = np.bincount(dall)
    print("  primes: %d; depth histogram: %s"
          % (primes.size, {int(k): int(v) for k, v in enumerate(h) if v}))
    gmax = int(dall.max())
    wit = int(primes[int(np.argmax(dall == gmax))])
    print("  max depth = %d at p = %d; chain %s"
          % (gmax, wit, "->".join(str(c) for c in deep_chain(wit))))
    for lo, hi in ((10 ** 4, 10 ** 5), (10 ** 5, 10 ** 6), (10 ** 6, 10 ** 7),
                   (10 ** 7, SPF_LIM)):
        sel = (primes >= lo) & (primes < hi)
        print("  decade [%.0e, %.0e): mean depth %.4f  mean nodes %.2f  (n=%d)"
              % (lo, hi, float(dall[sel].mean()),
                 float(_NODES[primes[sel]].mean()), int(sel.sum())))
    with open(os.path.join(SCRATCH, "pratt_wing_pratt7.json"), "w") as f2:
        json.dump(res, f2)
    print("[pratt7 done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: orders7

def order_block(name, ps, clock):
    """O5 per population: cyclic indices of 2/3/5 + the mod-8 hard assert."""
    f = clock.factor()
    ps = ps[::f] if isinstance(ps, list) else ps.tolist()[::f]
    if f > 1:
        print("  (halved %s to n=%d)" % (name, len(ps)))
    n = len(ps)
    idx = {b: np.empty(n, np.int64) for b in (2, 3, 5)}
    v2i2 = np.empty(n, np.int8)
    t0 = time.time()
    for i, p in enumerate(ps):
        fp = fac_pairs_spf(p - 1) if p <= SPF_LIM else fac_pairs_any(p - 1)
        for b in (2, 3, 5):
            if p == b:
                idx[b][i] = 0
                continue
            o = mult_order(b, p, fp)
            idx[b][i] = (p - 1) // o
        i2 = int(idx[2][i])
        if ((i2 % 2) == 0) != (p % 8 in (1, 7)):
            STOP("O5 mod-8 assert failed at p=%d (index %d)" % (p, i2))
        v2i2[i] = (i2 & -i2).bit_length() - 1 if i2 > 0 else 0
    out = dict(n=n)
    parts = []
    for b in (2, 3, 5):
        ib = idx[b][idx[b] > 0].astype(np.float64)
        pr = float((ib == 1).mean())
        out["b%d" % b] = dict(prim=pr, prim_sd=math.sqrt(pr * (1 - pr)),
                              mean=float(ib.mean()), med=float(np.median(ib)),
                              even=float((ib % 2 == 0).mean()))
        parts.append("b=%d prim %.5f mean_i %.3f med %d even_i %.5f"
                     % (b, pr, ib.mean(), int(np.median(ib)),
                        float((ib % 2 == 0).mean())))
    h = np.bincount(v2i2, minlength=6).astype(np.float64)
    h /= h.sum()
    out["v2i2"] = [float(x) for x in h[:6]]
    print("  %-5s n=%7d %s  [%.1fs]" % (name, n, " | ".join(parts), time.time() - t0))
    print("        v2(i_2) %%: " + " ".join("%d:%.3f" % (k, 100 * h[k])
                                            for k in range(len(h)) if h[k] > 0)
          + "   mod-8 assert: PASS on all %d" % n)
    sys.stdout.flush()
    return out


def stage_orders7():
    assert_registered()
    banner("ORDERS7", "O5: ord_p(2/3/5), cyclic index, Artin reference (m <= 1e7)")
    clock = StageClock()
    setup_tables()
    twins, isoL, isoR, p4 = build_pop7()
    print("  DISCLOSED REFERENCE: Artin density of i_b = 1 is 0.3739558136 (GRH);"
          " navigation only.")
    res = {}
    for name, ps in [("P1.L", 6 * twins - 1), ("P1.R", 6 * twins + 1),
                     ("P2.L", 6 * isoL - 1), ("P2.R", 6 * isoR + 1)]:
        res[name] = order_block(name, ps, clock)
    print("\n-- O5 twin-vs-isolated contrasts (DESCRIPTIVE) --")
    for t in ("L", "R"):
        a, b = res["P1.%s" % t], res["P2.%s" % t]
        for base in (2, 3, 5):
            x, y = a["b%d" % base], b["b%d" % base]
            zp = share_z(x["prim"], a["n"], y["prim"], b["n"])
            ze = share_z(x["even"], a["n"], y["even"], b["n"])
            print("  P1.%s-P2.%s b=%d: prim delta %+9.6f z %+6.2f | even-index"
                  " delta %+9.6f z %+6.2f | mean_i delta %+9.4f"
                  % (t, t, base, x["prim"] - y["prim"], zp, x["even"] - y["even"],
                     ze, x["mean"] - y["mean"]))
    with open(os.path.join(SCRATCH, "pratt_wing_orders7.json"), "w") as f2:
        json.dump(res, f2)
    print("[orders7 done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: quartic7

def quartic_block(name, pm_list, clock):
    """O7 on a list of (p, m) with p == 1 (mod 4); returns per-pop tables."""
    f = clock.factor()
    pm_list = pm_list[::f]
    if f > 1:
        print("  (halved %s to n=%d)" % (name, len(pm_list)))
    n = len(pm_list)
    cls = {b: np.empty(n, np.int8) for b in (2, 3, 5)}
    p8 = np.empty(n, np.int8)
    bmod8 = np.empty(n, np.int8)
    mm = np.empty(n, np.int64)
    t0 = time.time()
    g0 = GAUSS_CHECKS['n']
    for i, (p, m) in enumerate(pm_list):
        c2, c3, c5, a, bb = o7_measure(p)
        cls[2][i], cls[3][i], cls[5][i] = c2, c3, c5
        p8[i] = p % 8
        bmod8[i] = bb % 8
        mm[i] = m
    print("  %-8s n=%7d  [%.1fs]  Gauss hard selftest: PASS on all %d"
          % (name, n, time.time() - t0, GAUSS_CHECKS['n'] - g0))
    out = dict(n=n)
    for b in (2, 3, 5):
        c = cls[b]
        val = c >= 0
        tot = int(val.sum())
        sh = [float((c == k).sum()) / tot for k in range(4)]
        qr = (c == 0) | (c == 1)         # s^2 = +1 layer
        nqr = (c == 2) | (c == 3)
        pq = float((c[qr | nqr] <= 1).mean())
        c0q = float((c == 0).sum()) / max(int(qr.sum()), 1)
        ciq = float((c == 2).sum()) / max(int(nqr.sum()), 1)
        out["b%d" % b] = dict(sh=sh, qr=pq, nqr_n=int(nqr.sum()), qr_n=int(qr.sum()),
                              p1_in_qr=c0q, pi_in_nqr=ciq)
        print("    b=%d symbols %%: +1 %.4f  -1 %.4f  i %.4f  -i %.4f | QR layer"
              " %.4f | P(+1|QR) %.5f  P(i|NQR) %.5f"
              % (b, sh[0], sh[1], sh[2], sh[3], pq, c0q, ciq))
    hb = np.bincount(bmod8, minlength=8).astype(np.float64)
    hb /= hb.sum()
    print("    Gaussian b mod 8 %%: " + " ".join(
        "%d:%.4f" % (k, hb[k]) for k in range(8) if hb[k] > 0))
    out["bmod8"] = [float(x) for x in hb]
    out["_arrays"] = (cls, p8, mm)
    sys.stdout.flush()
    return out


def nonphase_table(cls2, p8, mm, mod):
    """Conditional symbol of 2 vs m mod `mod` -- within each p-mod-8 layer."""
    print("    joint (quartic symbol of 2) x (m mod %d)  [conditional shares; z vs"
          " pooled, DESCRIPTIVE]" % mod)
    for layer, codes, lab in ((1, (0, 1), "p==1(8): P(+1 | {+1,-1})"),
                              (5, (2, 3), "p==5(8): P(i | {i,-i})")):
        sel = (p8 == layer)
        c = cls2[sel]
        r = (mm[sel] % mod).astype(np.int64)
        inl = (c == codes[0]) | (c == codes[1])
        pool = float((c[inl] == codes[0]).mean())
        zs = []
        row = []
        for v in range(mod):
            s = inl & (r == v)
            nn = int(s.sum())
            if nn == 0:
                row.append("m=%d: -" % v)
                continue
            pv = float((c[s] == codes[0]).mean())
            z = share_z(pv, nn, pool, int(inl.sum()))
            zs.append(abs(z))
            row.append("m=%d:%.4f(z%+.1f)" % (v, pv, z))
        print("      %s pooled %.5f | %s | max|z| %.2f"
              % (lab, pool, " ".join(row), max(zs) if zs else float('nan')))


def stage_quartic7():
    assert_registered()
    banner("QUARTIC7", "O7 THE BEYOND-PHASE CLASS: quartic symbols + Cornacchia"
                       " (m <= 1e7)")
    clock = StageClock()
    setup_tables()
    twins, isoL, isoR, p4 = build_pop7()
    # 1-mod-4 wing of each twin: 6m-1 if m odd else 6m+1
    tw14 = [(int(6 * m - 1), int(m)) if m % 2 == 1 else (int(6 * m + 1), int(m))
            for m in twins.tolist()]
    iso14 = ([(int(6 * k - 1), int(k)) for k in isoL.tolist() if k % 2 == 1] +
             [(int(6 * k + 1), int(k)) for k in isoR.tolist() if k % 2 == 0])
    iso14.sort()
    print("  populations: twin 1-mod-4 wings n=%d (one per pair, exact); isolated"
          " 1-mod-4 (from P2) n=%d" % (len(tw14), len(iso14)))
    print("  REGISTERED EXPECTATION: NULL (Chebotarev; conditional splits 1/2:1/2"
          " within each phase layer, twin-independent).")
    sys.stdout.flush()
    rt = quartic_block("P1(1m4)", tw14, clock)
    ri = quartic_block("P2(1m4)", iso14, clock)
    print("\n-- O7 twin-vs-isolated contrasts (DESCRIPTIVE; beyond-phase layer) --")
    for b in (2, 3, 5):
        x, y = rt["b%d" % b], ri["b%d" % b]
        z1 = share_z(x["p1_in_qr"], x["qr_n"], y["p1_in_qr"], y["qr_n"])
        z2 = share_z(x["pi_in_nqr"], x["nqr_n"], y["pi_in_nqr"], y["nqr_n"])
        zq = share_z(x["qr"], rt["n"], y["qr"], ri["n"])
        print("  b=%d: P(+1|QR) twin %.5f iso %.5f z %+6.2f | P(i|NQR) twin %.5f"
              " iso %.5f z %+6.2f | QR-layer share z %+6.2f (phase-carried,"
              " disclosed)" % (b, x["p1_in_qr"], y["p1_in_qr"], z1,
                               x["pi_in_nqr"], y["pi_in_nqr"], z2, zq))
    print("\n-- O7 non-phase-ness joints (twin population) --")
    cls, p8, mm = rt["_arrays"]
    for mod in (5, 7, 8):
        nonphase_table(cls[2], p8, mm, mod)
    print("  Gauss criterion checks so far: %d, failures %d (STOP guarantees 0)"
          % (GAUSS_CHECKS['n'], GAUSS_CHECKS['fail']))
    for r in (rt, ri):
        r.pop("_arrays", None)
    with open(os.path.join(SCRATCH, "pratt_wing_quartic7.json"), "w") as f2:
        json.dump(dict(twin=rt, iso=ri), f2)
    print("[quartic7 done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: probe9

def measure_values_any(vals):
    """(omega, Omega, powdef, tier) on any tier (TD/rho); STOP on incomplete."""
    n = len(vals)
    om = np.empty(n, np.int16)
    Om = np.empty(n, np.int16)
    tr = np.empty(n, np.int8)
    for i, x in enumerate(vals):
        fp = fac_pairs_any(x)
        if fp is None:
            STOP("incomplete factorization at x=%d" % x)
        o, O, _, P = anatomy_of(fp)
        om[i] = o
        Om[i] = O
        tr[i] = tier_of(x, P)
    return om, Om, (Om - om), tr


def wing_block9(name, ps, res_anat, clock):
    """Full wing measurement at the 1e9 window: O1/O2/O3 + O4 + O5 per prime."""
    f = clock.factor()
    ps = ps[::f]
    if f > 1:
        print("  (halved %s to n=%d)" % (name, len(ps)))
    n = len(ps)
    arr = {("p-1", k): np.empty(n, np.int16) for k in ("om", "Om")}
    arr.update({("p+1", k): np.empty(n, np.int16) for k in ("om", "Om")})
    tr = {"p-1": np.empty(n, np.int8), "p+1": np.empty(n, np.int8)}
    dep = np.empty(n, np.int16)
    nod = np.empty(n, np.int64)
    bre = np.empty(n, np.int16)
    idx = {b: np.empty(n, np.int64) for b in (2, 3, 5)}
    t0 = time.time()
    for i, p in enumerate(ps):
        fpm = fac_pairs_any(p - 1)
        fpp = fac_pairs_any(p + 1)
        if fpm is None or fpp is None:
            STOP("incomplete factorization of p+-1 at p=%d" % p)
        for dlab, fp in (("p-1", fpm), ("p+1", fpp)):
            o, O, _, P = anatomy_of(fp)
            arr[(dlab, "om")][i] = o
            arr[(dlab, "Om")][i] = O
            tr[dlab][i] = tier_of(p - 1 if dlab == "p-1" else p + 1, P)
        bre[i] = len(fpm)
        d_, n_ = pratt_big(p)
        dep[i] = d_
        nod[i] = n_
        for b in (2, 3, 5):
            idx[b][i] = (p - 1) // mult_order(b, p, fpm)
        if ((int(idx[2][i]) % 2) == 0) != (p % 8 in (1, 7)):
            STOP("O5 mod-8 assert failed at p=%d" % p)
    for dlab in ("p-1", "p+1"):
        om, Om = arr[(dlab, "om")], arr[(dlab, "Om")]
        res_anat[(name, dlab)] = fmt_anatomy("%s %s" % (name, dlab), om, Om,
                                             Om - om, tr[dlab])
    imax = int(np.argmax(dep))
    stats = dict(n=n, dep=float(dep.mean()), dep_sd=float(dep.std()),
                 nod=float(nod.mean()), nod_sd=float(nod.std()),
                 bre=float(bre.mean()), bre_sd=float(bre.std()),
                 dmax=int(dep.max()), dmax_p=int(ps[imax]))
    for b in (2, 3, 5):
        ib = idx[b].astype(np.float64)
        stats["b%d" % b] = dict(prim=float((ib == 1).mean()),
                                mean=float(ib.mean()), even=float((ib % 2 == 0).mean()))
    print("  %-6s O4 depth %.4f+-%.3f (max %d at p=%d) nodes %.2f breadth %.4f |"
          " O5 prim(2/3/5) %.5f/%.5f/%.5f | mod-8 assert PASS on all %d  [%.1fs]"
          % (name, stats["dep"], stats["dep_sd"], stats["dmax"], stats["dmax_p"],
             stats["nod"], stats["bre"], stats["b2"]["prim"], stats["b3"]["prim"],
             stats["b5"]["prim"], n, time.time() - t0))
    sys.stdout.flush()
    return stats


def stage_probe9():
    assert_registered()
    banner("PROBE9", "the 1e9 window per the L35 protocol: gate + O1-O5, O6, O7")
    clock = StageClock()
    setup_tables()
    setup_pratt()
    twins, isoL, isoR, p4, gate, gaten = build_pop9()
    print("  1e9 WINDOW GATE (L35 protocol, segmented exact, m in [1e9, 1e9+1e6)):")
    print("    contrast E[omega_C|twin] - E[omega_C|no-twin] = %+.6f  n_twin = %d"
          % (gate, gaten))
    if ("%+.6f" % gate) != "+0.224068" or gaten != N_TWIN_9:
        STOP("1e9 gate mismatch: %+.6f / %d (need +0.224068 / %d)"
             % (gate, gaten, N_TWIN_9))
    print("    reproduces the L35 window value EXACTLY -> PASS")
    print("  populations: twins=%d isoL=%d isoR=%d p4=%d"
          % (twins.size, isoL.size, isoR.size, p4.size))
    sys.stdout.flush()
    res_anat = {}
    res = {}
    res["P1.L"] = wing_block9("P1.L", (6 * twins - 1).tolist(), res_anat, clock)
    res["P1.R"] = wing_block9("P1.R", (6 * twins + 1).tolist(), res_anat, clock)
    res["P2.L"] = wing_block9("P2.L", (6 * isoL - 1).tolist(), res_anat, clock)
    res["P2.R"] = wing_block9("P2.R", (6 * isoR + 1).tolist(), res_anat, clock)
    print("\n-- 1e9 twin-vs-isolated contrasts (same type/side; DESCRIPTIVE) --")
    for t in ("L", "R"):
        for dlab in ("p-1", "p+1"):
            contrast_line("P1.%s-P2.%s %s" % (t, t, dlab),
                          res_anat[("P1.%s" % t, dlab)],
                          res_anat[("P2.%s" % t, dlab)])
        a, b = res["P1.%s" % t], res["P2.%s" % t]
        for k in ("dep", "nod", "bre"):
            z = welch_z(a[k], a[k + "_sd"], a["n"], b[k], b[k + "_sd"], b["n"])
            print("  P1.%s-P2.%s %-4s delta %+9.6f  z %+7.2f"
                  % (t, t, k, a[k] - b[k], z))
        for base in (2, 3, 5):
            x, y = a["b%d" % base], b["b%d" % base]
            zp = share_z(x["prim"], a["n"], y["prim"], b["n"])
            print("  P1.%s-P2.%s b=%d prim delta %+9.6f z %+6.2f"
                  % (t, t, base, x["prim"] - y["prim"], zp))
    print("  reference (E4-truncated, disclosed): wing-side omega excess ~ %+.6f;"
          " navigation, not laws." % float(WING_REF_B31))
    sys.stdout.flush()

    # O6 at the window
    print("\n-- O6 (1e9): twin centers vs omega-MATCHED reweighted P4 --")
    f = clock.factor()
    om1, Om1, pd1, tr1 = measure_values_any([int(6 * m) for m in twins.tolist()[::f]])
    om4, Om4, pd4, tr4 = measure_values_any([int(6 * m) for m in p4.tolist()[::f]])
    a1 = fmt_anatomy("P1 c=6m", om1, Om1, pd1, tr1)
    a4 = fmt_anatomy("P4 c=6m", om4, Om4, pd4, tr4)
    print("  O3 CROSS-CHECK ONLY (re-claiming barred): E[omega_C|twin]-E[omega_C|P4]"
          " = %+.6f" % (a1["om"] - a4["om"]))
    kmax = int(max(om1.max(), om4.max()))
    c1 = np.bincount(om1, minlength=kmax + 1).astype(np.float64)
    c4 = np.bincount(om4, minlength=kmax + 1).astype(np.float64)
    s1, s4 = c1 / c1.sum(), c4 / c4.sum()
    wk = np.zeros(kmax + 1)
    ok = c4 > 0
    wk[ok] = s1[ok] / np.maximum(s4[ok], 1e-300)
    print("  reweighting: dropped P1 mass %.6f (cells absent from P4, disclosed)"
          % float(s1[~ok].sum()))
    w = wk[om4]
    sw = float(w.sum())
    neff = sw * sw / float((w * w).sum())
    o6 = {}
    for lab, x1, x4 in [("powdef(c)", pd1.astype(np.float64), pd4.astype(np.float64))] + \
            [("tier%d(c)" % j, (tr1 == j).astype(np.float64),
              (tr4 == j).astype(np.float64)) for j in range(4)]:
        mu1, sd1 = float(x1.mean()), float(x1.std())
        mu4 = float((w * x4).sum() / sw)
        sd4 = math.sqrt(max(float((w * (x4 - mu4) ** 2).sum() / sw), 0.0))
        z = welch_z(mu1, sd1, x1.size, mu4, sd4, neff)
        o6[lab] = dict(p1=mu1, p4w=mu4, d=mu1 - mu4, z=z)
        print("  O6 %-10s P1 %.6f | P4-reweighted %.6f | delta %+.6f  z %+7.2f"
              " (DESCRIPTIVE)" % (lab, mu1, mu4, mu1 - mu4, z))
    sys.stdout.flush()

    # O7 at the window
    print("\n-- O7 (1e9): quartic symbols, twin vs isolated 1-mod-4 --")
    tw14 = [(int(6 * m - 1), int(m)) if m % 2 == 1 else (int(6 * m + 1), int(m))
            for m in twins.tolist()]
    iso14 = ([(int(6 * k - 1), int(k)) for k in isoL.tolist() if k % 2 == 1] +
             [(int(6 * k + 1), int(k)) for k in isoR.tolist() if k % 2 == 0])
    iso14.sort()
    rt = quartic_block("P1(1m4)", tw14, clock)
    ri = quartic_block("P2(1m4)", iso14, clock)
    for b in (2, 3, 5):
        x, y = rt["b%d" % b], ri["b%d" % b]
        z1 = share_z(x["p1_in_qr"], x["qr_n"], y["p1_in_qr"], y["qr_n"])
        z2 = share_z(x["pi_in_nqr"], x["nqr_n"], y["pi_in_nqr"], y["nqr_n"])
        print("  b=%d: P(+1|QR) twin %.5f iso %.5f z %+6.2f | P(i|NQR) twin %.5f"
              " iso %.5f z %+6.2f" % (b, x["p1_in_qr"], y["p1_in_qr"], z1,
                                      x["pi_in_nqr"], y["pi_in_nqr"], z2))
    cls, p8, mm = rt["_arrays"]
    for mod in (5, 7, 8):
        nonphase_table(cls[2], p8, mm, mod)
    for r in (rt, ri):
        r.pop("_arrays", None)
    print("  factorization completeness: %d incomplete of %d calls (target 0)"
          % (FAC_STATS['incomplete'], FAC_STATS['total']))
    with open(os.path.join(SCRATCH, "pratt_wing_probe9.json"), "w") as f2:
        json.dump(dict(anat={"%s|%s" % k: v for k, v in res_anat.items()},
                       pratt_ord=res, o6=o6, o7=dict(twin=rt, iso=ri),
                       gate=gate, gaten=gaten), f2)
    print("[probe9 done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: defect

def stage_defect():
    assert_registered()
    banner("DEFECT", "P3: prime wings of the 50 exact defect windows A=17..43"
                     " (DESCRIPTIVE stratum)")
    clock = StageClock()
    setup_tables()
    setup_pratt()
    print("  MR bases = first 12 primes, deterministic < 3.186e23 (registered"
          " adaptation; A=43 wings ~ 1.4e15).")
    cache_p = os.path.join(SCRATCH, "pratt_wing_defects.json")
    if os.path.exists(cache_p):
        with open(cache_p) as f:
            sc = json.load(f)
        d17, d19 = sc["17"], sc["19"]
    else:
        d17, d19 = defect_scan(17), defect_scan(19)
    windows = ([(17, r) for r in d17] + [(19, r) for r in d19] +
               [(A, r) for A in (23, 29, 31, 37, 41, 43) for r in DEFECT_R[A]])
    if len(windows) != 50:
        STOP("expected 50 defect windows, got %d" % len(windows))
    agg = {}
    all_rows = []
    for A, r in windows:
        L = G_EXACT[A] - 1
        if not struck_ok(r, L, A):
            STOP("defect witness fails at A=%d r=%d" % (A, r))
        pws = []
        for m in range(r + 1, r + L + 1):
            for off in (-1, 1):
                p = 6 * m + off
                if is_prime_any(p):
                    pws.append((p, m))
        agg.setdefault(A, []).extend(pws)
        all_rows.append((A, r, L, len(pws)))
    print("  windows verified: 50 (A=17:20, A=19:20, 23:4, 29:2, 31:1, 37:1, 41:1,"
          " 43:1); prime wings per window:")
    for A in DEFECT_SCALES:
        rows = [x for x in all_rows if x[0] == A]
        print("    A=%2d L=%3d: n_windows=%2d prime wings %s (total %d of %d wings)"
              % (A, G_EXACT[A] - 1, len(rows),
                 [n for _, _, _, n in rows] if len(rows) <= 6 else
                 "%s..." % [n for _, _, _, n in rows[:6]],
                 sum(n for _, _, _, n in rows),
                 sum(2 * ln for _, _, ln, _ in rows)))
    sys.stdout.flush()
    pooled = []
    o7pool = dict(qr=[0, 0], nqr=[0, 0])
    for A in DEFECT_SCALES:
        pws = agg.get(A, [])
        if not pws:
            print("  A=%2d: no prime wings (disclosed)" % A)
            continue
        clock.factor()
        oms, deps, nods, tiers0, prim2 = [], [], [], 0, 0
        dmax, dmax_p = -1, 0
        for p, m in pws:
            fpm = fac_pairs_any(p - 1)
            fpp = fac_pairs_any(p + 1)
            if fpm is None or fpp is None:
                STOP("incomplete factorization at defect wing p=%d" % p)
            o, O, _, P = anatomy_of(fpm)
            oms.append(o)
            tiers0 += int(tier_of(p - 1, P) == 0)
            d_, n_ = pratt_big(p)
            deps.append(d_)
            nods.append(n_)
            if d_ > dmax:
                dmax, dmax_p = d_, p
            i2 = (p - 1) // mult_order(2, p, fpm)
            if ((i2 % 2) == 0) != (p % 8 in (1, 7)):
                STOP("O5 mod-8 assert failed at defect wing p=%d" % p)
            prim2 += int(i2 == 1)
            if p % 4 == 1:
                c2, c3, c5, a_, bb = o7_measure(p)
                if c2 <= 1:
                    o7pool['qr'][0] += int(c2 == 0)
                    o7pool['qr'][1] += 1
                else:
                    o7pool['nqr'][0] += int(c2 == 2)
                    o7pool['nqr'][1] += 1
            pooled.append((A, p, o, d_))
        no = len(pws)
        print("  A=%2d prime wings n=%3d | omega(p-1) %.3f | P+>sqrt share %.3f |"
              " Pratt depth %.3f (max %d at p=%d) nodes %.1f | prim2 share %.3f"
              % (A, no, float(np.mean(oms)), tiers0 / no, float(np.mean(deps)),
                 dmax, dmax_p, float(np.mean(nods)), prim2 / no))
        sys.stdout.flush()
    dp = [d for _, _, _, d in pooled]
    print("  P3 pooled: %d prime wings; depth mean %.3f max %d; omega(p-1) mean %.3f"
          % (len(pooled), float(np.mean(dp)), max(dp),
             float(np.mean([o for _, _, o, _ in pooled]))))
    big = max(pooled, key=lambda x: x[1])
    print("  deepest/biggest witness: p=%d (A=%d) depth %d chain %s"
          % (big[1], big[0], pratt_big(big[1])[0],
             "->".join(str(c) for c in deep_chain(big[1]))))
    print("  O7 on P3 (pooled, tiny n, DESCRIPTIVE): P(+1|QR) = %d/%d; P(i|NQR)"
          " = %d/%d; Gauss hard selftest PASS on all measured"
          % (o7pool['qr'][0], o7pool['qr'][1], o7pool['nqr'][0], o7pool['nqr'][1]))
    print("  factorization completeness: %d incomplete of %d calls (target 0)"
          % (FAC_STATS['incomplete'], FAC_STATS['total']))
    with open(os.path.join(SCRATCH, "pratt_wing_defect.json"), "w") as f2:
        json.dump(dict(rows=all_rows, pooled=pooled[:2000],
                       o7=o7pool), f2)
    print("[defect done in %.1fs]" % (time.time() - clock.t0))
    sys.stdout.flush()


# ================================================================== stage: summary

def stage_summary():
    assert_registered()
    banner("SUMMARY", "cross-population collation + escalation candidates"
                      " (NO verdicts by design)")
    data = {}
    for tag in ("anatomy7", "pratt7", "orders7", "quartic7", "probe9", "defect"):
        p = os.path.join(SCRATCH, "pratt_wing_%s.json" % tag)
        if os.path.exists(p):
            with open(p) as f:
                data[tag] = json.load(f)
        else:
            print("  (missing stage JSON: %s -- stage not run?)" % tag)
    print("REMINDER (registered): prime-conditioned population; no parity verdict"
          " is defined here;")
    print("  deviations from reference curves are navigation, not laws.")
    if "anatomy7" in data:
        r = data["anatomy7"]["res"]
        print("\nO3 omega(p+-1) twin-vs-isolated excesses at 1e7 (reference"
              " %+.6f trunc B=31):" % float(WING_REF_B31))
        for t in ("L", "R"):
            for d in ("p-1", "p+1"):
                a, b = r["P1.%s|%s" % (t, d)], r["P2.%s|%s" % (t, d)]
                print("  type %s side %s: %+.6f" % (t, d, a["om"] - b["om"]))
    if "probe9" in data:
        r = data["probe9"]["anat"]
        print("O3 omega(p+-1) excesses at the 1e9 window:")
        for t in ("L", "R"):
            for d in ("p-1", "p+1"):
                a, b = r["P1.%s|%s" % (t, d)], r["P2.%s|%s" % (t, d)]
                print("  type %s side %s: %+.6f" % (t, d, a["om"] - b["om"]))
    print("\nESCALATION CANDIDATES (subject to a NEW pre-registration; proposed"
          " Fraction-exact census forms):")
    print("  C-A wing-side collision law: E[d_B(p-+1)|twin] - E[d_B|isolated] =")
    print("      sum_(5<=q<=B)(1/(q-2) - 1/(q-1)) -- provable via the L34 pgf with")
    print("      the isolated condition (q excludes ONE class) vs twin (q excludes")
    print("      TWO); full-period Fraction census at B=7 (period 35) and B=13")
    print("      (period 5005) over side values 6m-2 / 6m+2, exactly as L34/E1-E4.")
    print("  C-B any surviving O6 weighted contrast: powerDefect/P+ tier census")
    print("      conditioned on fixed omega(c) -- Fraction-exact truncated form:")
    print("      joint pgf of (d_B(C), 1[q^2|C]) from the 1/1/1/(q-3) split.")
    print("  C-C O7: if any conditional |z| >= 5 appeared, register a dedicated")
    print("      quartic campaign; the Chebotarev NULL otherwise CLOSES the class.")
    print("  (Escalation decisions belong to the next registration, not this log.)")
    sys.stdout.flush()


# ================================================================== main

STAGES = dict(selftest=stage_selftest, anatomy7=stage_anatomy7, pratt7=stage_pratt7,
              orders7=stage_orders7, quartic7=stage_quartic7, probe9=stage_probe9,
              defect=stage_defect, summary=stage_summary)


def main():
    install_log()
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in STAGES:
        print("usage: python tools/pratt_wing_harness.py {%s}" % "|".join(STAGES))
        sys.exit(2)
    os.makedirs(SCRATCH, exist_ok=True)
    STAGES[mode]()


if __name__ == "__main__":
    main()
