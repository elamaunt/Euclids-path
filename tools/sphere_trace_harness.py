#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Sphere-trace harness -- the numeric stages s6-s7 of the sphere ladder of the
dispersion pass (companion Lean modules: EuclidsPath/Engine/Step00SphereTrace.lean
and EuclidsPath/Engine/Step00HexCubicUnits.lean).

Stage numbering continues the dispersion pass (tools/dispersion_harness.py owns
s0-s3; s4-s5 are reserved for the window ladder); this file owns:

  s6  THE CUBIC BEYOND-PHASE PROBE: cubic residuacity of 2, 3, 5 at twin RIGHT
      wings (all = 1 mod 3) vs size-matched isolated 1-mod-3 primes (populations
      per the L62 pratt_wing protocol, m <= 1e7, 100 bins of width 1e5, seeded
      without replacement); the volume-trichotomy observable of the cubic sphere
      (which Step00HexCubicUnits volume the wing carries: split (p-1)^2 vs inert
      p^2+p+1; left wings carry the welded (p-1)(p+1) unconditionally -- frame);
      HARD Cornacchia selftest on EVERY population prime:
      2 is a cubic residue mod p  <=>  p = a^2 + 27 b^2   (0 failures required).
      Registered expectation: NULL (the L63 Chebotarev prior).  Descriptive z
      only; NO parity verdicts are issuable (prime-conditioned populations).

  s7  the registered search for ONE non-congruence sphere observable at fixed
      SL2(Z) matrices reduced mod wing primes, PLUS the byte-check selftest of
      the Lean crown: sphereSum u = p * kloos(u,u) by DIRECT SL2 enumeration at
      p = 5, 11, 17 (exact integer form N(t) - p*H(t) = p^2 - p AND complex
      form; STOP on mismatch).

House discipline (conventions from tools/pratt_wing_harness.py): registration
block written to the log FIRST (stage s6 emits it; s7 asserts its presence);
seed 20260710 (numpy default_rng; documented substreams [SEED, k]: k=6 the s6
isolated-population matching, k=7 the s7 order-observable subsample);
STAGE_TIME_CAP 5400 s with the documented halving fallback; append-only ASCII
log tools/sphere_trace_run1.log; every selftest failure exits 1 (STOP).

Usage:  python tools/sphere_trace_harness.py s6
        python tools/sphere_trace_harness.py s7
(env var SPHERE_TRACE_LOG overrides the log path for development dry-runs only;
 env var SPHERE_TRACE_DEV_M shrinks the m-scale for dry-runs -- both leave the
 registered protocol untouched and are NEVER used for the committed log).
"""

import cmath
import math
import os
import sys
import time

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
LOG_PATH = os.environ.get("SPHERE_TRACE_LOG") or os.path.join(
    TOOLS, "sphere_trace_run1.log")

SEED = 20260710
STAGE_TIME_CAP = 5400          # s; registered fallback: halve remaining workload, LOG it

M_MED = int(os.environ.get("SPHERE_TRACE_DEV_M") or 10 ** 7)   # main m-scale
SIEVE_LIM = 6 * M_MED + 2      # covers both wings
N_TWIN_7 = 280557              # the L35 census count at 1e7 (asserted)
N_BINS = 100                   # L62 protocol: 100 bins of width M_MED/100
SUBSAMPLE = 20000              # s7 order-observable subsample per population

FIXED_MATRICES = (             # (name, matrix, trace, D = tr^2 - 4)
    ("F1", ((2, 1), (1, 1)), 3, 5),
    ("F2", ((3, 1), (2, 1)), 4, 12),
    ("F3", ((4, 1), (3, 1)), 5, 21),
)


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
    print("[%s] SPHERE-TRACE %s  %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), name, sub))
    print("  seed=%d  numpy=%s  STAGE_TIME_CAP=%ds  m-scale=%d"
          % (SEED, np.__version__, STAGE_TIME_CAP, M_MED))
    print("=" * 78)
    sys.stdout.flush()


def STOP(msg):
    print("STOP -- " + msg)
    print("STAGE VERDICT: STOP (selftest/design violation; later stages must not run)")
    sys.stdout.flush()
    sys.exit(1)


def assert_registered():
    if not os.path.exists(LOG_PATH):
        STOP("registration missing: run stage s6 first")
    with open(LOG_PATH, "r", encoding="ascii", errors="replace") as f:
        if "PRE-REGISTRATION ENDS" not in f.read():
            STOP("registration missing: run stage s6 first")


# ------------------------------------------------------- registration (printed FIRST)

REGISTRATION = """
PRE-REGISTRATION -- SPHERE-TRACE stages s6-s7 (the sphere ladder of the
dispersion pass).  Registered BEFORE any measurement line.  Seed 20260710
(numpy default_rng; substreams [SEED, k]: k=6 the s6 isolated-population
matching, k=7 the s7 order-observable subsample).  STAGE_TIME_CAP = 5400 s per
stage; registered fallback: if a stage threatens the cap, HALVE the remaining
per-population workload and LOG the shrink -- never silently.  Log append-only,
ASCII; stages are separate argv invocations (house crash-resilience pattern).

NULL DESIGN (registered): prime-conditioned populations -- NO parity verdicts
are issuable anywhere in these stages (pratt_wing decision (b) inherited).
THE REGISTERED EXPECTATION IS NULL ON EVERY CONTRAST (the L63 Chebotarev
prior): the cubic residuacity classes and the volume trichotomy are governed by
the splitting of p in non-abelian cubic fields (Q(cbrt(-2)), Q(cbrt(2), w)),
and L63 measured that twinness is invisible even to the quartic/Gaussian
beyond-phase layer; nothing in the ledger predicts a cubic-layer signal.
Deviations, if any, are navigation -- descriptive z only.

POPULATIONS (closed; the L62 pratt_wing protocol at the 1e7 scale)
 P1R twin RIGHT wings: q = 6m+1 for all twin centers m <= 1e7 (expected
     n = 280557, MUST equal the L35 census count exactly; every q = 1 mod 3).
 P2R isolated 1-mod-3 primes, size-matched to P1R: same count, sampled seeded
     WITHOUT replacement (substream k=6) from right-type isolated primes
     (6k+1 prime AND 6k-1 composite, k <= 1e7, k not a twin center) in the
     same 100 m-bins of width 1e5.
 (Left wings q = 6m-1 are 2 mod 3: their cubic sphere volume is (p-1)(p+1)
  UNCONDITIONALLY -- proved in Step00HexCubicUnits.cubic_sphere_card_two_mod_
  three; there is nothing to measure on the left, stated as frame.)

OBSERVABLES (CLOSED LIST -- nothing may be added after this block)
 O-C1 cubic residuacity classes of b = 2, 3, 5 at every population prime:
      s_b = b^((p-1)/3) mod p, classified in {1, w, w^2} with w canonicalized
      as the SMALLER of the two primitive cube roots of unity mod p (as
      integers in (0, p)); class shares per population, per base; contrast
      P1R vs P2R, descriptive two-proportion z per class (9 contrasts).
 O-C2 the volume-trichotomy observable: which cubic sphere volume the wing
      carries -- SPLIT (p-1)^2 iff -2 is a cube mod p (s_{-2} = 1), else
      INERT p^2+p+1 (the two 1-mod-3 branches of Step00HexCubicUnits;
      root count 0 or 3 -- the machine dichotomy); split share vs the
      Chebotarev reference 1/3 (DISCLOSED REFERENCE, not a verdict);
      contrast P1R vs P2R, descriptive z (1 contrast).
 O-C3 (GATE, not an observable) HARD Cornacchia selftest on EVERY population
      prime: 2 cubic residue mod p <=> p = a^2 + 27 b^2 (Gauss).  Cornacchia
      with d = 27 via Tonelli-Shanks sqrt(-27) + Euclid descent; the
      implementation is itself pre-validated against brute force on all
      p = 1 mod 3, p < 1e5 (ST-1) and was independently pre-validated by
      dispersion_harness ST-F.  0 failures required; any failure = STOP.
 O-S1 torus type of the three FIXED matrices F1 = [[2,1],[1,1]] (tr 3, D=5),
      F2 = [[3,1],[2,1]] (tr 4, D=12), F3 = [[4,1],[3,1]] (tr 5, D=21) in
      SL2(F_p): split/nonsplit by chi_p(D) (parabolic impossible: D != 0 for
      p not dividing D; such p are skipped and counted).  REGISTERED SENTENCE
      (the expected verdict): the torus type of a FIXED matrix is CONGRUENCE
      DATA -- a function of p mod 4D by quadratic reciprocity; the stage
      machine-checks this (the map (p mod 4D) -> type must be single-valued
      across BOTH populations, 0 exceptions) and contrasts the type shares
      P1R vs P2R (descriptive z; NULL expected since congruence classes are
      equidistributed in both populations by construction).
 O-S2 the ONE reachable candidate beyond congruence data: the multiplicative
      order of F1 in SL2(F_p) (the Artin-class observable; analogous to O5
      ord_p(2) of pratt_wing, which closed NULL).  Cyclic index
      i = (p - chi_p(5)) / ord(F1); distribution of i in {1, 2, 3, >=4} on a
      seeded subsample of 20000 per population (substream k=7); contrast
      P1R vs P2R, descriptive z (4 contrasts).  EXPECTED VERDICT (registered):
      NULL -- all reachable sphere observables at fixed matrices are
      congruence data or order data of the O5 class; the stage confirms or
      surprises.
 GATE-S7 the Lean-crown byte-check: for p in {5, 11, 17}, enumerate SL2(F_p)
      COMPLETELY (p^4 matrices filtered by det = 1); assert |SL2| = p^3 - p,
      the trace-fiber law N(t) = p^2 + p*chi(t^2-4), the EXACT integer form
      of the crown N(t) - p*H(t) = p^2 - p for every t (H(t) = the hyperbola
      fiber count #{y != 0 : y + 1/y = t}), and the complex identity
      sphereSum(u) = p * kloos(u,u) for every u != 0 (tolerance 1e-6, sums of
      at most p^3 unit complex numbers).  ANY mismatch = STOP.

PRE-REGISTRATION ENDS
"""


# ----------------------------------------------------------------- primitives

def sieve_bool(n):
    """Boolean primality array 0..n (numpy)."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def tonelli(a, p):
    """Square root of a mod p (p odd prime, a a QR); Tonelli-Shanks."""
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    # factor p-1 = q * 2^s
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    # find a non-residue z
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t = t * c % p
        r = r * b % p
    return r


def cornacchia27(p, r3):
    """p = x^2 + 27 y^2 solvable?  r3 = sqrt(-3) mod p (precomputed).
    Cornacchia with d = 27: r0 = sqrt(-27) = 3*r3, Euclid descent."""
    r0 = 3 * r3 % p
    if r0 * r0 % p != (p - 27) % p:
        STOP("cornacchia27: bad sqrt(-27) at p=%d" % p)
    if 2 * r0 < p:
        r0 = p - r0
    a, b = p, r0
    lim = math.isqrt(p)
    while b > lim:
        a, b = b, a % b
    t = p - b * b
    if t % 27 != 0:
        return False
    y2 = t // 27
    y = math.isqrt(y2)
    return y * y == y2


def cornacchia27_brute(p):
    b = 1
    while 27 * b * b < p:
        t = p - 27 * b * b
        s = math.isqrt(t)
        if s * s == t:
            return True
        b += 1
    return False


def cube_class(b, p, wcan):
    """Class of b under the cubic character: 0 if cube, 1 if b^((p-1)/3) = wcan,
    2 otherwise (wcan = the canonical primitive cube root of unity)."""
    s = pow(b, (p - 1) // 3, p)
    if s == 1:
        return 0
    if s == wcan:
        return 1
    return 2


def matmul2(A, B, p):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0]) % p,
            (A[0][0] * B[0][1] + A[0][1] * B[1][1]) % p,
            (A[1][0] * B[0][0] + A[1][1] * B[1][0]) % p,
            (A[1][0] * B[0][1] + A[1][1] * B[1][1]) % p)


def matpow2(M, e, p):
    """M^e mod p for a 2x2 matrix given as ((a,b),(c,d)); returns flat tuple."""
    R = (1, 0, 0, 1)
    B = (M[0][0] % p, M[0][1] % p, M[1][0] % p, M[1][1] % p)
    while e:
        if e & 1:
            R = ((R[0] * B[0] + R[1] * B[2]) % p, (R[0] * B[1] + R[1] * B[3]) % p,
                 (R[2] * B[0] + R[3] * B[2]) % p, (R[2] * B[1] + R[3] * B[3]) % p)
        B = ((B[0] * B[0] + B[1] * B[2]) % p, (B[0] * B[1] + B[1] * B[3]) % p,
             (B[2] * B[0] + B[3] * B[2]) % p, (B[2] * B[1] + B[3] * B[3]) % p)
        e >>= 1
    return R


def factorize_spf(n, spf):
    fs = []
    while n > 1:
        f = int(spf[n])
        fs.append(f)
        while n % f == 0:
            n //= f
    return fs


def mat_order(M, n, spf, p):
    """Multiplicative order of M in SL2(F_p), given order divides n (factored
    via the SPF table)."""
    o = n
    for f in factorize_spf(n, spf):
        while o % f == 0 and matpow2(M, o // f, p) == (1, 0, 0, 1):
            o //= f
    return o


def two_prop_z(k1, n1, k2, n2):
    p1, p2 = k1 / n1, k2 / n2
    pb = (k1 + k2) / (n1 + n2)
    den = math.sqrt(pb * (1 - pb) * (1 / n1 + 1 / n2)) if 0 < pb < 1 else float("inf")
    return (p1 - p2) / den if den > 0 else 0.0


# -------------------------------------------------------------- population build

def build_populations():
    """P1R twin right wings and the matched isolated pool, per registration."""
    t0 = time.time()
    isp = sieve_bool(SIEVE_LIM)
    ms = np.arange(1, M_MED + 1, dtype=np.int64)
    left = isp[6 * ms - 1]
    right = isp[6 * ms + 1]
    twin_m = ms[left & right]
    iso_right_m = ms[right & ~left]          # 6k+1 prime, 6k-1 composite
    n_twin = int(twin_m.size)
    if M_MED == 10 ** 7 and n_twin != N_TWIN_7:
        STOP("L35 census gate: n_twin=%d != %d" % (n_twin, N_TWIN_7))
    print("populations: n_twin=%d  isolated-right pool=%d  (sieve %.1fs)"
          % (n_twin, int(iso_right_m.size), time.time() - t0))
    # size-matched seeded sampling per 100 bins (L62 protocol, substream k=6)
    rng = np.random.default_rng([SEED, 6])
    width = M_MED // N_BINS
    picks = []
    short = 0
    for b in range(N_BINS):
        lo, hi = b * width + 1, (b + 1) * width
        tw = twin_m[(twin_m >= lo) & (twin_m <= hi)]
        pool = iso_right_m[(iso_right_m >= lo) & (iso_right_m <= hi)]
        need = tw.size
        if pool.size < need:
            short += need - pool.size
            need = pool.size
        picks.append(rng.choice(pool, size=need, replace=False))
    iso_m = np.concatenate(picks)
    if short:
        print("  NOTE: %d bin-shortfalls (disclosed; matched count=%d)"
              % (short, int(iso_m.size)))
    p1r = (6 * twin_m + 1).tolist()
    p2r = (6 * np.sort(iso_m) + 1).tolist()
    return p1r, p2r


# ------------------------------------------------------------------------- s6

def stage_s6():
    banner("s6", "THE CUBIC BEYOND-PHASE PROBE (registration first)")
    need_reg = True
    if os.path.exists(LOG_PATH):
        with open(LOG_PATH, "r", encoding="ascii", errors="replace") as f:
            if "PRE-REGISTRATION ENDS" in f.read():
                need_reg = False
    if need_reg:
        print(REGISTRATION)
        sys.stdout.flush()
    t_stage = time.time()

    # ST-1: Cornacchia implementation pre-validation (brute force, p < 1e5)
    t0 = time.time()
    small = sieve_bool(10 ** 5)
    ps_small = [int(p) for p in np.nonzero(small)[0] if p % 3 == 1 and p > 3]
    for p in ps_small:
        r3 = tonelli(p - 3, p)
        if cornacchia27(p, r3) != cornacchia27_brute(p):
            STOP("ST-1 Cornacchia mismatch at p=%d" % p)
    print("ST-1 Cornacchia impl == brute force on ALL %d primes 1 mod 3 < 1e5"
          % len(ps_small))
    print("  -- PASS (%.1fs)" % (time.time() - t0))

    p1r, p2r = build_populations()
    pops = (("P1R-twin-right", p1r), ("P2R-isolated", p2r))

    # per-population measurement
    results = {}
    corn_checked, corn_rep = 0, 0
    for name, plist in pops:
        t0 = time.time()
        cls = {b: [0, 0, 0] for b in (2, 3, 5)}
        split_n = 0
        n = len(plist)
        done = 0
        for p in plist:
            if (p - 1) % 3 != 0:
                STOP("population prime %d is not 1 mod 3" % p)
            r3 = tonelli(p - 3, p)                    # sqrt(-3) mod p
            w1 = (p - 1 + r3) * pow(2, p - 2, p) % p  # (-1 + r3)/2
            w2 = (p - 1 - r3 + p) * pow(2, p - 2, p) % p
            wcan = min(w1, w2)
            for b in (2, 3, 5):
                cls[b][cube_class(b, p, wcan)] += 1
            # volume trichotomy: split iff -2 is a cube
            cube_m2 = pow(p - 2, (p - 1) // 3, p) == 1
            split_n += cube_m2
            # O-C3 hard Cornacchia gate on EVERY prime
            rep = cornacchia27(p, r3)
            cube2 = pow(2, (p - 1) // 3, p) == 1
            if rep != cube2:
                STOP("O-C3 Cornacchia gate FAILED at p=%d (rep=%s cube2=%s)"
                     % (p, rep, cube2))
            corn_checked += 1
            corn_rep += rep
            done += 1
            if time.time() - t_stage > STAGE_TIME_CAP:
                STOP("stage cap exceeded mid-population (%d/%d) -- rerun with "
                     "the registered halving fallback" % (done, n))
        results[name] = (n, cls, split_n)
        print("%s: n=%d measured (%.1fs)" % (name, n, time.time() - t0))

    print("")
    print("O-C3 HARD CORNACCHIA GATE: %d primes checked, 0 failures;"
          % corn_checked)
    print("  representable (= 2-is-cube) count %d (share %.5f; Chebotarev"
          % (corn_rep, corn_rep / max(corn_checked, 1)))
    print("  reference 1/3 -- DISCLOSED REFERENCE, not a verdict)")

    print("")
    print("O-C1 CUBIC RESIDUACITY CLASSES (class 0 = cube; 1 = w_can; 2 = other)")
    n1 = results["P1R-twin-right"][0]
    n2 = results["P2R-isolated"][0]
    for b in (2, 3, 5):
        c1 = results["P1R-twin-right"][1][b]
        c2 = results["P2R-isolated"][1][b]
        print("  base %d:" % b)
        print("    P1R shares: %s" % "  ".join(
            "c%d %.5f" % (i, c1[i] / n1) for i in range(3)))
        print("    P2R shares: %s" % "  ".join(
            "c%d %.5f" % (i, c2[i] / n2) for i in range(3)))
        zs = ["z(c%d) %+.2f" % (i, two_prop_z(c1[i], n1, c2[i], n2))
              for i in range(3)]
        print("    contrasts:  %s   (descriptive z only)" % "  ".join(zs))

    print("")
    print("O-C2 VOLUME TRICHOTOMY (right wings: SPLIT (p-1)^2 vs INERT p^2+p+1;")
    print("  left wings carry (p-1)(p+1) UNCONDITIONALLY -- proved frame, not")
    print("  measured)")
    s1n = results["P1R-twin-right"][2]
    s2n = results["P2R-isolated"][2]
    print("  P1R split share %.5f (n=%d)   P2R split share %.5f (n=%d)"
          % (s1n / n1, n1, s2n / n2, n2))
    print("  contrast z %+.2f   (Chebotarev reference 1/3: disclosed, not a"
          % two_prop_z(s1n, n1, s2n, n2))
    print("  verdict; deviations of BOTH populations from 1/3 are population-")
    print("  conditioning, not twin signal)")

    print("")
    print("STAGE VERDICT s6: gate O-C3 PASSED (0 failures on %d primes);"
          % corn_checked)
    zmax = 0.0
    for b in (2, 3, 5):
        c1 = results["P1R-twin-right"][1][b]
        c2 = results["P2R-isolated"][1][b]
        for i in range(3):
            zmax = max(zmax, abs(two_prop_z(c1[i], n1, c2[i], n2)))
    zmax = max(zmax, abs(two_prop_z(s1n, n1, s2n, n2)))
    print("  max |z| over the 10 registered contrasts = %.2f -- %s"
          % (zmax, "NULL CONFIRMED (registered expectation)" if zmax < 3
             else "DEVIATION (navigation; NOT a law -- see registration)"))
    print("  (%.1fs total)" % (time.time() - t_stage))
    sys.stdout.flush()


# ------------------------------------------------------------------------- s7

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def byte_check_sphere(p):
    """Enumerate SL2(F_p) completely; check the Lean trace-fiber law and the
    crown sphereSum = p * kloos, exact-integer and complex forms."""
    N = [0] * p
    count = 0
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a * d - b * c) % p == 1:
                        N[(a + d) % p] += 1
                        count += 1
    if count != p ** 3 - p:
        STOP("byte-check |SL2(%d)| = %d != p^3-p" % (p, count))
    H = [0] * p
    for y in range(1, p):
        H[(y + pow(y, p - 2, p)) % p] += 1
    for t in range(p):
        if legendre(t * t - 4, p) * p + p * p != N[t]:
            STOP("byte-check N(t) law fails at p=%d t=%d" % (p, t))
        if N[t] - p * H[t] != p * p - p:
            STOP("byte-check N-pH != p^2-p at p=%d t=%d" % (p, t))
    for u in range(1, p):
        S = sum(N[t] * cmath.exp(2j * cmath.pi * u * t / p) for t in range(p))
        K = sum(cmath.exp(2j * cmath.pi * (u * y + u * pow(y, p - 2, p)) / p)
                for y in range(1, p))
        if abs(S - p * K) > 1e-6:
            STOP("byte-check sphereSum != p*kloos at p=%d u=%d (|diff|=%.2e)"
                 % (p, u, abs(S - p * K)))
    return count


def stage_s7():
    assert_registered()
    banner("s7", "non-congruence sphere observable search + Lean byte-check")
    t_stage = time.time()

    # GATE-S7: the Lean-crown byte-check (STOP on mismatch)
    t0 = time.time()
    for p in (5, 11, 17):
        cnt = byte_check_sphere(p)
        print("GATE-S7 p=%2d: |SL2|=%6d = p^3-p; N(t) = p^2 + p*chi(t^2-4) all t;"
              % (p, cnt))
        print("  N(t) - p*H(t) = p^2 - p all t (EXACT); sphereSum u = p*kloos(u,u)")
        print("  all u != 0 (complex, tol 1e-6)")
    print("GATE-S7 PASSED (%.1fs) -- the Lean crown sphereSum_eq_p_mul_kloos is"
          % (time.time() - t0))
    print("  byte-confirmed by direct enumeration at p = 5, 11, 17")

    p1r, p2r = build_populations()
    pops = (("P1R-twin-right", p1r), ("P2R-isolated", p2r))

    # O-S1: torus types + the congruence machine-check
    print("")
    print("O-S1 TORUS TYPES of F1 (D=5), F2 (D=12), F3 (D=21)")
    congr = {}     # (name, p mod 4D) -> set of types
    shares = {}
    for name, plist in pops:
        n = len(plist)
        stat = {fn: [0, 0, 0] for fn, _, _, _ in FIXED_MATRICES}  # split/nonsplit/skip
        for p in plist:
            for fn, _, _, D in FIXED_MATRICES:
                if D % p == 0:
                    stat[fn][2] += 1
                    continue
                chi = legendre(D, p)
                stat[fn][0 if chi == 1 else 1] += 1
                key = (fn, p % (4 * D))
                v = congr.setdefault(key, chi)
                if v != chi:
                    STOP("O-S1 congruence check FAILED: %s type not a function "
                         "of p mod %d at p=%d" % (fn, 4 * D, p))
        shares[name] = (n, stat)
        for fn, _, tr, D in FIXED_MATRICES:
            s = stat[fn]
            print("  %s %s (tr %d, D=%d): split %.5f  nonsplit %.5f  skipped %d"
                  % (name, fn, tr, D, s[0] / n, s[1] / n, s[2]))
    print("  CONGRUENCE MACHINE-CHECK: the map (p mod 4D) -> torus type is")
    print("  single-valued across both populations for F1/F2/F3 (0 exceptions)")
    print("  -- torus type IS congruence data, as registered")
    n1, n2 = shares["P1R-twin-right"][0], shares["P2R-isolated"][0]
    for fn, _, _, D in FIXED_MATRICES:
        k1 = shares["P1R-twin-right"][1][fn][0]
        k2 = shares["P2R-isolated"][1][fn][0]
        print("  contrast %s split-share z %+.2f (descriptive)"
              % (fn, two_prop_z(k1, n1, k2, n2)))

    # O-S2: the order observable on the seeded subsample (substream k=7)
    print("")
    print("O-S2 CYCLIC INDEX of F1 = [[2,1],[1,1]] (order in SL2(F_p);")
    print("  n_p = p - chi_p(5); subsample %d per population, substream k=7)"
          % SUBSAMPLE)
    t0 = time.time()
    spf = np.zeros(SIEVE_LIM + 1, dtype=np.int32)
    for i in range(2, SIEVE_LIM + 1):
        if spf[i] == 0:
            spf[i::i] = np.where(spf[i::i] == 0, i, spf[i::i])
    print("  (SPF sieve to %d: %.1fs)" % (SIEVE_LIM, time.time() - t0))
    rng = np.random.default_rng([SEED, 7])
    F1 = FIXED_MATRICES[0][1]
    idx_stats = {}
    for name, plist in pops:
        take = min(SUBSAMPLE, len(plist))
        sample = rng.choice(np.array(plist, dtype=np.int64), size=take,
                            replace=False)
        hist = {1: 0, 2: 0, 3: 0, 4: 0}   # 4 means >= 4
        t0 = time.time()
        for p in (int(q) for q in sample):
            chi = legendre(5, p)
            npo = p - chi
            o = mat_order(F1, npo, spf, p)
            i = npo // o
            hist[i if i in (1, 2, 3) else 4] += 1
            if time.time() - t_stage > STAGE_TIME_CAP:
                STOP("stage cap exceeded in O-S2 -- rerun with the registered "
                     "halving fallback")
        idx_stats[name] = (take, hist)
        print("  %s (n=%d, %.1fs): i=1 %.5f  i=2 %.5f  i=3 %.5f  i>=4 %.5f"
              % (name, take, time.time() - t0,
                 hist[1] / take, hist[2] / take, hist[3] / take, hist[4] / take))
    m1, h1 = idx_stats["P1R-twin-right"]
    m2, h2 = idx_stats["P2R-isolated"]
    zmax = 0.0
    zrow = []
    for i in (1, 2, 3, 4):
        z = two_prop_z(h1[i], m1, h2[i], m2)
        zmax = max(zmax, abs(z))
        zrow.append("z(i%s) %+.2f" % ("<=3" if i != 4 else ">=4", z))
    print("  contrasts: %s (descriptive)" % "  ".join(
        "z(i=%d) %+.2f" % (i, two_prop_z(h1[i], m1, h2[i], m2)) if i != 4
        else "z(i>=4) %+.2f" % two_prop_z(h1[4], m1, h2[4], m2)
        for i in (1, 2, 3, 4)))

    print("")
    print("STAGE VERDICT s7: GATE-S7 passed; torus types machine-confirmed to be")
    print("  congruence data (the registered sentence CONFIRMED); the one order-")
    print("  class candidate (O-S2) max |z| = %.2f -- %s" % (zmax,
          "NULL (as registered; the sphere adds volume, not new observables)"
          if zmax < 3 else "DEVIATION (navigation only; NOT a law)"))
    print("  (%.1fs total)" % (time.time() - t_stage))
    sys.stdout.flush()


# ----------------------------------------------------------------------- main

STAGES = dict(s6=stage_s6, s7=stage_s7)

if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in STAGES:
        sys.stderr.write("usage: python tools/sphere_trace_harness.py {s6|s7}\n")
        sys.exit(2)
    install_log()
    STAGES[sys.argv[1]]()
