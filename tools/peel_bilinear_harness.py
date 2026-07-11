#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Peel-bilinear harness (imaginary-objects phase, PRIORITY candidate; Lean side:
EuclidsPath/Engine/Step00PeelBilinear.lean).

The first observable class supported OUTSIDE the window (outside the foil's reweighting
locus), with classical parity-crossing precedents (Vinogradov Type-II; Friedlander-Iwaniec).
Edges = ALL peel edges of window centers: wing 6m+-1 = p * cofactor, p prime >= 5,
cofactor = 6t+-1 a wing of the target center t (grave_depth_harness.peel_steps model,
== betti_portrait_harness.peel_targets, == GenealogyForest.PeelStep -- selftested).

Stages (argv modes; every stage APPENDS to tools/peel_bilinear_run1.log):
  selftest   PRE-REGISTRATION block (before any measurement), then STOP-selftests:
             edge model == peel_targets (1e4 sample); Lean-statement cross-checks
             (parity transport int-exact on 1e5 edges; peel_target_window intervals by
             enumeration; window_edge_count vs canonical peel; defect witness checks);
             jacobi vs Euler criterion; scan calibration (A=17: 20 starts first 117;
             A=19: 20 starts first 110); mechanical-part exactness.
  defect     populations (a)-(d) at scales A in {17,19,23,29,31,37,41,43}: O1-O5 per
             window; defect-vs-matched-phase and defect-vs-typical Welch z; defect-depth
             regression over run-length strata; per-scale JSON to scratch.
  foil       foil-v2 ensemble grid A in {13,31,101} x X in {1e6,1e9}, H=50,
             NW=3000/1000, seed 20260710: O2/O3/O4 per window, loads S / So / S'',
             foil_row (200 sigma_W perms + 200 sigma_I lambda-resamples) per row.
  summary    verdict matrix per observable per gate_g3 (verbatim thresholds), the
             interpretation gate, the registered STOP evaluation.

House reuse: betti_portrait_harness.precompute_X / foil_row / demech / primes_upto
(imported, VERBATIM); grave_depth_harness factorization tiers (SPF sieve at 1e6 scale,
numpy trial division at 1e9 scale, Pollard-rho(Brent)+Miller-Rabin at 1e12+ scale;
imported, gd.log redirected into THIS log). MR base extension for wings up to 1.5e15
disclosed in the registration block.

Intermediate JSONs go to the scratch dir (env PEEL_BILINEAR_SCRATCH or system temp);
the repo stays clean except this file, the log and the Lean module.
"""

import json
import math
import os
import sys
import tempfile
import time

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
LOG_PATH = os.path.join(TOOLS, "peel_bilinear_run1.log")
SCRATCH = os.environ.get("PEEL_BILINEAR_SCRATCH") or os.path.join(
    tempfile.gettempdir(), "peel_bilinear_scratch")

import betti_portrait_harness as bp          # noqa: E402  (precompute_X, foil_row, demech)
import grave_depth_harness as gd             # noqa: E402  (factorization tiers, peel_steps)

SEED = 20260710

# exact true gaps G(A) (kernel-pinned 17..37: Step00PhaseCoverKernel; 41/43:
# tools/phase_cover_run1.log lines 105-166, solver certificate + trial division)
G_EXACT = {17: 18, 19: 25, 23: 34, 29: 43, 31: 58, 37: 88, 41: 91, 43: 103}
SCALES = (17, 19, 23, 29, 31, 37, 41, 43)

# SAT defect-window starts (window = centers r+1 .. r+G-1, all struck; r clean).
# A=17/19: harvested by full-period scan in-stage (20 starts each; calibrated in selftest
# against tools/gap_extremal_run1.log:124-141 -- first starts 117 / 110).
DEFECT_R = {
    23: [12694428, 18165208, 19016903, 24487683],
    29: [200906185, 877375977],
    31: [21844264615],
    37: [1145973108145],
    41: [50077677123072],
    43: [233885349904190],
}

WPRIMES = {A: [q for q in bp.primes_upto(A) if q >= 5] for A in (13, 101) + SCALES}


def _period(A):
    P = 1
    for q in WPRIMES[A]:
        P *= q
    return P


PERIODS = {A: _period(A) for A in SCALES}

# registered population parameters
NCTRL = {17: 40, 19: 40, 23: 40, 29: 40, 31: 40, 37: 24, 41: 24, 43: 24}
# controls r' = r + 5005*u, u in [1, U_A] w/o replacement; U_A = min(320, P_A/5005 - 1)
# keeps every control inside ONE period copy (magnitude matched to the witness span)
CTRL_U_MAX = {A: int(min(320, PERIODS[A] // 5005 - 1)) for A in SCALES}
# typicals r' = r + w, w in [1, min(320*5005, P_A)] w/o replacement (same band)
TYP_W_MAX = {A: int(min(320 * 5005, PERIODS[A])) for A in SCALES}
NEAR_CAP = 60                      # near-defect harvest cap per (A, ell)
SCAN_LIMIT = {17: PERIODS[17], 19: PERIODS[19], 23: PERIODS[23], 29: PERIODS[29],
              31: 2 * 10 ** 9}     # A=31 partial (period 3.34e10); A>=37: no scan
R_MIN_HARVEST = 10                 # windows with r < 10 excluded (tiny-wing cofactor guard)
MIN_BLOCK_POOL = 30                # O1 per-block two-sample needs pooled count >= 30
STAGE_TIME_CAP = 5400              # per-stage hard cap (s); documented fallback: halve
                                   # NCTRL (defect) / NW (foil) for the remaining cells
                                   # and LOG the shrink -- never silently.

FOIL_A = (13, 31, 101)
FOIL_X = ((10 ** 6, 3000), (10 ** 9, 1000))
H = 50

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
    fh = open(LOG_PATH, "a", encoding="utf-8")
    try:                    # Windows consoles may be cp1251: never let the console
        sys.__stdout__.reconfigure(errors="replace")   # encoding kill a log write
    except Exception:
        pass
    sys.stdout = Tee(fh, sys.__stdout__)               # log file written FIRST
    gd.log = print          # redirect grave_depth internal logging into THIS log


def banner(name, sub=""):
    print("=" * 78)
    print("[%s] PEEL-BILINEAR %s  %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), name, sub))
    print("=" * 78)
    sys.stdout.flush()


def STOP(msg):
    print("STOP -- " + msg)
    print("STAGE VERDICT: STOP (design violation; later stages must not run)")
    sys.stdout.flush()
    sys.exit(1)


# ------------------------------------------------------- registration (printed FIRST)

REGISTRATION = """
PRE-REGISTRATION -- peel-bilinear campaign (registered BEFORE any measurement line).
Seed 20260710 everywhere (numpy default_rng; documented substreams [SEED, k]).

EDGE MODEL (fixed): edges of a window (r, r+L] = for every center m in the window and
  every wing v = 6m-1, 6m+1, one edge per DISTINCT prime q >= 5 of v with cofactor
  c = v/q >= 5; target t = center of c (c = 6t+-1); label p = q; fresh wing = the OTHER
  wing of t (6t-1 if c = 6t+1, else 6t+1).  Identical to grave_depth_harness.peel_steps
  == betti_portrait_harness.peel_targets == GenealogyForest.PeelStep (selftested; STOP
  on any mismatch).  Twin centers carry no out-edges (both wings prime).

POPULATIONS
 (a) DEFECT windows (exact SAT witnesses; window length L = G(A)-1):
     A=17: 20 starts, full-period scan (calibration: first r=117, count 20; matches
           tools/gap_extremal_run1.log:124-131);
     A=19: 20 starts, full-period scan (first r=110; log:133-140);
     A=23: r in {12694428, 18165208, 19016903, 24487683};
     A=29: r in {200906185, 877375977};
     A=31: r = 21844264615 (n=1) + any length-57 runs found by the partial scan;
     A=37: r = 1145973108145 (n=1);
     A=41: r = 50077677123072 (L=90; tools/phase_cover_run1.log:105-166);
     A=43: r = 233885349904190 (L=102; same log).  n=1 at A>=37 (and effectively at 31):
     the two-sample test there is NOT oversold -- reported as descriptive sigma-offsets.
 (b) NEAR-DEFECT strata: maximal struck runs of length ell in {G-3, G-2, G-1}, harvested
     by scan over [0, P_A) for A in {17,19,23,29}, over [0, 2e9) at A=31 (PARTIAL,
     period 3.34e10 -- disclosed); NO scan at A>=37 (period >= 1.24e12): regression
     unavailable there, said so in the verdicts.  Harvest cap 60 runs per (A, ell)
     (uniform subsample, seeded); windows with r < 10 excluded (cofactor >= 5 guard).
 (c) MATCHED-PHASE controls, per defect witness r: r'_i = r + 5005*u_i, u_i drawn
     uniformly WITHOUT replacement from [1, U_A], U_A = min(320, P_A/5005 - 1) -- every
     control stays inside ONE period copy of the witness (magnitude matched; at A=17
     the orbit has only U=16 distinct controls per witness, disclosed).  Same residues
     mod 5005 = same small-clock phase tuple (r mod 5,7,11,13); the big-clock phases
     cycle along the 5005-step orbit (near-uniform individually, NOT iid-CRT jointly;
     disclosed).  n_ctrl = min(40, U_A) per witness at A <= 31, min(24, U_A) at
     A >= 37 (rho-tier cost).  Same window length L.
 (d) TYPICAL windows, per defect witness r: r'_i = r + w_i, w_i uniform WITHOUT
     replacement from [1, min(320*5005, P_A)] (same magnitude band as (c), no phase
     constraint); same counts as (c).
 (e) foil-v2 ensemble grid: A in {13, 31, 101} x X in {1e6, 1e9}, H = 50,
     NW = 3000 (1e6) / 1000 (1e9), seed 20260710 (betti_portrait precompute_X reused).

PRE-REGISTERED OBSERVABLES (per window; factorization tiers per grave_depth_harness:
SPF sieve < 6e6, numpy trial division <= 6.1e9, Pollard-rho(Brent) + Miller-Rabin
above; ADAPTATION disclosed: MR bases extended to the first 12 primes (2..37),
deterministic for n < 3.186e23 (Sorenson-Webster 2015), because A=43 wings reach
1.5e15 > the 3.4e14 bound of the 7-base tier; factorization completeness at rho-tier
scales is counted and reported).
 O1  dyadic label profile N_j(W) = #edges with label p in [2^j, 2^(j+1)).  The
     MECHANICAL part is subtracted EXACTLY: for every q <= A the number of label-q
     edges equals the phase-determined strike count of q in the window (Lean
     struck_wing_minFac_le / defect_edges_small_labels_17 side; exactness re-verified
     per window, STOP in selftest on mismatch).  Residual profile = blocks restricted
     to labels p > A.  Primary scalar: residual edge rate = #(p > A edges)/L.
     Secondary: per-block Welch z for blocks with pooled count >= 30 (family size
     disclosed).  Verdict on the residual ONLY.
 O2  edge spins S(W) = sum over edges with label p in the primary block of
     jacobi(cofactor mod p | p).  Registered ONLY for labels p > A (small-p spin is a
     proven level-p^2 function -- excluded BEFORE measurement; cite
     Step00WingJacobiCollapse.spin_fixed_label_periodic, built in parallel).  Primary
     block: defect stage p in [w^(1/4), w^(1/2)], w = 6(r+1)+1 (per-window); foil grid
     p in [X^(1/4), X^(1/2)].  Scalar: spin_norm = S / sqrt(#block edges) (random-walk
     normalization).  Defect-depth regression + foil-v2.
 O3  teleported fresh parity F(W) = mean over edges of lambda(fresh wing 6t-delta)
     (Liouville).  The mechanical channel lambda(cofactor) = -lambda(source wing) is
     EXCLUDED by construction (the read value is the OTHER wing of the target).
     P3d-style de-mechanization ADDITIONALLY: residual after removing 20-quantile-bin
     means in the window Omega-profile (betti demech, verbatim).  Loads S / So / S''.
 O4  twin-hit rate: fraction of edges whose target t is a twin center (cofactor prime
     AND fresh wing prime).  Defect vs typical; foil-v2 with primary load S -- O4 reads
     NO lambda of window members (targets sit below X/5 + 1, outside every window at
     X >= 1e6), so the plain load S is already self-excluded.
 O5  cascade strike density: for each label p in [5, A], the renormalized interval
     [(6r+5-p)/(6p), (6(r+L)+1+p)/(6p)] (EXACT nat-floor-division endpoints of Lean
     peel_target_window); scalar = mean over p of the fraction of interval centers
     struck at scale A.  O5 is fully phase-determined (strike density is a function of
     r mod P_A) -- it carries NO parity content by construction; reported against
     L32(b) (rank transfer), not re-derived, not claimed new.
 OMP window Omega-profile = mean over window wings of Omega (for O3 de-mechanization).
 Also recorded per window: n_struck (struck centers), factorization completeness.

LOADS (foil grid; betti conventions): lambda-load L(W) = sum over scale-A-clean window
 centers of lambda(6m-1)lambda(6m+1).  S = full window; S'' = split-window (invariant
 from LEFT half edges, load from RIGHT half survivors); So = self-excluded: excludes
 window members whose own wings enter the invariant -- at X >= 1e6 every peel target
 sits below (6(X+H)+1)/30 << X, so NO member's wings are read and So == S (DISCLOSED
 degenerate; reported anyway).  200 sigma_W permutations + 200 sigma_I lambda-resamples
 (pool = cell survivors), seed 20260710 -- gate_g3 foil-v2 machinery (bp.foil_row,
 verbatim).

PRIMARY ROWS (verdict-carrying): O2|S, O3|S'', O4|S.  Secondary (information): O2|S'',
 O3|S, O3|So, O4|S'', O3d|S'' (de-mechanized; the interpretation gate reads it).

THRESHOLDS (gate_g3 foil-v2, VERBATIM; never moved):
 PARITY-SENSITIVE (MANAGED-PASS) iff min |z_I| >= 5 over the grid AND escalation ratio
 |R(A_hi)| >= |R(A_lo)|/3 for BOTH consecutive pairs (13->31, 31->101) at both X;
 SOFT-PASS iff min |z_I| >= 3; else PARITY-BLIND-UNDER-ESCALATION-v2.
 Two-sample (defect stage): Welch z; FLAG iff |z| >= 3.  Defect-depth regression:
 Pearson r of (observable, ell) over strata ell in {G-3, G-2, G-1}; permutation z from
 200 seeded shuffles; TREND iff |z| >= 3.

INTERPRETATION GATE (registered): because bilinear observables are the one class where
 classical theory predicts possible sensitivity, a PASS is claimed as content ONLY if
 the de-mechanized version also passes; the harness computes the predicted-from-identity
 mechanical part exactly and subtracts (O1: exact small-label subtraction; O3: excluded
 channel + demech residual O3d; O2: small-p exclusion before measurement).

STOP (registered VERBATIM): if O2, O3, O4 are all PARITY-BLIND-UNDER-ESCALATION-v2 AND
 the defect-vs-matched-phase residuals of O1/O5 show no |z| >= 3 trend in the
 defect-depth regression at >= 2 scales -- write the ledger null ("the bilinear/peel
 layer is parity-blind and phase-determined"), keep the Lean identities, STOP: no new
 weightings, no threshold moves, no extra blocks.  A null verdict is a deliverable.

SECONDARY (clearly labeled): tree-profile stats live ONLY in the deterministic
 lean-model mode of tools/phase_cover_harness.py (proof-search shadow, NOT an
 arithmetic object, NO Lean statements); the logged node counts are quoted in the
 summary, nothing new is computed.

RUNTIME FALLBACK (registered): per-stage cap 5400 s; if a cell would blow past, halve
 NCTRL (defect) / NW (foil) for the REMAINING cells and log the shrink -- never
 silently.
PRE-REGISTRATION ENDS -- measurements begin below this line.
"""


def assert_registered():
    if not os.path.exists(LOG_PATH):
        STOP("registration missing: run the selftest stage first")
    with open(LOG_PATH, "r", encoding="utf-8") as f:
        if "PRE-REGISTRATION ENDS" not in f.read():
            STOP("registration missing: run the selftest stage first")


# ------------------------------------------------------------------ number theory

def setup():
    # ADAPTATION (registered): extend deterministic MR to the first 12 primes.
    gd.MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    gd.MR_VALID = 318 * 10 ** 21
    gd.setup_tables()


FAC_STATS = dict(incomplete=0, total=0)


def factor_pairs(x):
    """Full factorization [(p, e), ...] via the grave_depth tiers; completeness
    counted (rem must reach 1 -- fac_distinct is complete by construction)."""
    x0 = int(x)
    ps = gd.fac_distinct(x0)
    out = []
    rem = x0
    for p in ps:
        e = 0
        while rem % p == 0:
            rem //= p
            e += 1
        out.append((int(p), e))
    FAC_STATS['total'] += 1
    if rem != 1:
        FAC_STATS['incomplete'] += 1
        return None
    return out


def bigomega(x):
    fp = factor_pairs(x)
    return None if fp is None else sum(e for _, e in fp)


def lam_of(x):
    o = bigomega(x)
    return None if o is None else (1 - 2 * (o & 1))


def jacobi(a, n):
    """Jacobi symbol (a|n), n odd positive."""
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


def peel_edges(m):
    """Annotated peel edges from center m: (t, p, cofactor, fresh_wing).
    Same enumeration as gd.peel_steps (side minus first, primes ascending)."""
    out = []
    for off in (-1, 1):
        v = 6 * m + off
        for q in gd.fac_distinct(v):
            if q == v:
                continue
            cof = v // q
            if cof < 5:
                continue
            r6 = cof % 6
            if r6 == 5:
                t = (cof + 1) // 6
                fresh = 6 * t + 1          # cof = 6t-1 -> fresh wing is 6t+1
            elif r6 == 1:
                t = (cof - 1) // 6
                fresh = 6 * t - 1          # cof = 6t+1 -> fresh wing is 6t-1
            else:
                continue
            out.append((t, int(q), cof, fresh))
    return out


def canonical_peel(m):
    """Python mirror of GenealogyBasins.canonicalPeel (left-wing-first, minFac)."""
    wl, wr = 6 * m - 1, 6 * m + 1
    if gd.is_prime(wl):
        if gd.is_prime(wr):
            return None                     # twin: root, junk value in Lean
        S = wr
    else:
        S = wl
    p = min(gd.fac_distinct(S))
    s = S // p
    return (s - 1) // 6 if s % 6 == 1 else (s + 1) // 6


def mech_counts(r, L, A):
    """EXACT phase-determined per-clock strike counts of the window (r, r+L]."""
    out = {}
    for q in WPRIMES[A]:
        i6 = pow(6, -1, q)
        c = 0
        for cls in (i6 % q, (q - i6) % q):
            o0 = (cls - r - 1) % q          # smallest o >= 1 with r+o = cls (mod q)
            c += len(range(1 + o0, L + 1, q))
        out[q] = c
    return out


def struck_mask(rs, A):
    rs = np.asarray(rs, dtype=np.int64)
    struck = np.zeros(rs.size, bool)
    for q in WPRIMES[A]:
        i6 = pow(6, -1, q)
        struck |= (rs % q == i6) | (rs % q == (q - i6) % q)
    return struck


# ------------------------------------------------------------------ scan (near-defect)

def scan_runs(A, limit, chunk=10 ** 8):
    """Maximal struck runs (r = clean center before the run, ell) with
    ell in {G-3, G-2, G-1}, over m in [0, limit).  gap_extremal chunked-scan pattern."""
    G = G_EXACT[A]
    want = (G - 3, G - 2, G - 1)
    cls = []
    for q in WPRIMES[A]:
        a = pow(6, -1, q)
        cls.append((q, a % q, (q - a) % q))
    runs = []
    prev_clean = None
    t0 = time.time()
    for lo in range(0, limit, chunk):
        hi = min(lo + chunk, limit)
        struck = np.zeros(hi - lo, dtype=bool)
        for q, a1, a2 in cls:
            struck[(a1 - lo) % q::q] = True
            struck[(a2 - lo) % q::q] = True
        cl = np.flatnonzero(~struck).astype(np.int64) + lo
        if cl.size == 0:
            continue
        if prev_clean is not None:
            ell = int(cl[0]) - prev_clean - 1
            if ell in want:
                runs.append((prev_clean, ell))
        d = np.diff(cl)
        for ell in want:
            idx = np.flatnonzero(d == ell + 1)
            runs.extend((int(cl[i]), ell) for i in idx)
        prev_clean = int(cl[-1])
    print("  scan A=%d m<%s: runs ell=G-3/G-2/G-1: %d/%d/%d [%.1fs]"
          % (A, "{:,}".format(limit),
             sum(1 for _, e in runs if e == G - 3),
             sum(1 for _, e in runs if e == G - 2),
             sum(1 for _, e in runs if e == G - 1), time.time() - t0))
    sys.stdout.flush()
    return sorted(runs)


# ------------------------------------------------------------------ window measurement

def measure_window(r, L, A):
    """All registered observables of the window (r, r+L].  Returns a dict."""
    wp = WPRIMES[A]
    mech = mech_counts(r, L, A)
    obs_small = {q: 0 for q in wp}
    dy_resid = {}
    spin_sum = 0
    spin_n = 0
    o3_sum = 0.0
    o3_n = 0
    o4_hit = 0
    omega_sum = 0
    n_wings = 0
    inc0 = FAC_STATS['incomplete']
    w0 = 6 * (r + 1) + 1
    blo = math.ceil(w0 ** 0.25)
    bhi = math.isqrt(w0)
    resid_edges = 0
    for m in range(r + 1, r + L + 1):
        for off in (-1, 1):
            fp = factor_pairs(6 * m + off)
            if fp is not None:
                omega_sum += sum(e for _, e in fp)
            n_wings += 1
        for (t, p, cof, fresh) in peel_edges(m):
            if p <= A:
                if p in obs_small:
                    obs_small[p] += 1
            else:
                resid_edges += 1
                j = p.bit_length() - 1
                dy_resid[j] = dy_resid.get(j, 0) + 1
                if blo <= p <= bhi:
                    spin_sum += jacobi(cof % p, p)
                    spin_n += 1
            of = bigomega(fresh)
            if of is not None:
                o3_sum += 1 - 2 * (of & 1)
                o3_n += 1
                if of == 1 and gd.is_prime(cof):
                    o4_hit += 1
            # completeness counted in FAC_STATS
    mech_ok = all(obs_small[q] == mech[q] for q in wp)
    dens = []
    for p in wp:
        lo_p = (6 * r + 5 - p) // (6 * p)
        hi_p = (6 * (r + L) + 1 + p) // (6 * p)
        if hi_p < lo_p or hi_p < 1:
            continue
        lo_p = max(lo_p, 1)
        ns = np.arange(lo_p, hi_p + 1, dtype=np.int64)
        dens.append(float(struck_mask(ns, A).mean()))
    n_struck = int(struck_mask(np.arange(r + 1, r + L + 1, dtype=np.int64), A).sum())
    return dict(
        r=int(r), L=int(L),
        o1=resid_edges / float(L),
        dy={int(k): int(v) for k, v in dy_resid.items()},
        mech_ok=bool(mech_ok),
        spin=float(spin_sum), spin_n=int(spin_n),
        o2=(spin_sum / math.sqrt(spin_n)) if spin_n > 0 else float('nan'),
        o3=(o3_sum / o3_n) if o3_n > 0 else float('nan'), o3_n=int(o3_n),
        o4=(o4_hit / float(o3_n)) if o3_n > 0 else float('nan'),
        o5=float(np.mean(dens)) if dens else float('nan'),
        omp=(omega_sum / float(n_wings)) if n_wings else float('nan'),
        n_struck=n_struck,
        fac_inc=int(FAC_STATS['incomplete'] - inc0))


# ------------------------------------------------------------------ statistics

def welch(a, b):
    a = np.asarray(a, float)
    b = np.asarray(b, float)
    a = a[np.isfinite(a)]
    b = b[np.isfinite(b)]
    if a.size < 2 or b.size < 2:
        return float('nan'), int(a.size), int(b.size)
    se = math.sqrt(a.var(ddof=1) / a.size + b.var(ddof=1) / b.size)
    if se < 1e-15:
        return 0.0 if abs(a.mean() - b.mean()) < 1e-15 else float('inf'), int(a.size), int(b.size)
    return float((a.mean() - b.mean()) / se), int(a.size), int(b.size)


def sigma_offset(y, b):
    b = np.asarray(b, float)
    b = b[np.isfinite(b)]
    if b.size < 2 or not np.isfinite(y) or b.std(ddof=1) < 1e-15:
        return float('nan')
    return float((y - b.mean()) / b.std(ddof=1))


def perm_reg_z(y, x, rng):
    y = np.asarray(y, float)
    x = np.asarray(x, float)
    v = np.isfinite(y) & np.isfinite(x)
    n = int(v.sum())
    if n < 10 or y[v].std() < 1e-12 or x[v].std() < 1e-12:
        return float('nan'), float('nan'), n
    r = float(np.corrcoef(y[v], x[v])[0, 1])
    xc = x[v].copy()
    perm = np.empty(200)
    for t in range(200):
        rng.shuffle(xc)
        perm[t] = np.corrcoef(y[v], xc)[0, 1]
    return r, float(r / (perm.std() + 1e-15)), n


# ================================================================== stage: selftest

def stage_selftest():
    banner("SELFTEST", "pre-registration + STOP selftests")
    print(REGISTRATION)
    sys.stdout.flush()
    t0 = time.time()
    setup()
    rng = np.random.default_rng([SEED, 0])

    # (a) edge model == gd.peel_steps == bp.peel_targets on 1e4 sample
    bp.setup_factor_tables()
    ms = np.concatenate([rng.integers(2, 10 ** 6, 5000),
                         rng.integers(10 ** 6, 10 ** 7, 3000),
                         rng.integers(10 ** 9, 10 ** 9 + 10 ** 5, 2000)])
    for m in ms:
        m = int(m)
        mine = [(t, p) for (t, p, c, f) in peel_edges(m)]
        gds = [(t, p) for (t, p, s, tp) in gd.peel_steps(m)]
        if mine != gds:
            STOP("edge model != gd.peel_steps at m=%d: %s vs %s" % (m, mine, gds))
        if sorted(t for t, _ in mine) != sorted(bp.peel_targets(m)):
            STOP("edge targets != bp.peel_targets at m=%d" % m)
    print("  (a) edge model == gd.peel_steps AND targets == bp.peel_targets on 10^4"
          " sample (m in [2,1e6] u [1e6,1e7] u [1e9,1e9+1e5]) -> PASS")

    # (b) Lean parity transport int-exact on 1e5 edges
    checked = 0
    m = 1
    ms2 = rng.integers(2, 10 ** 6, 40000)
    for m in ms2:
        m = int(m)
        for (t, p, cof, fresh) in peel_edges(m):
            wing = p * cof
            if wing != 6 * m - 1 and wing != 6 * m + 1:
                STOP("edge wing mismatch at m=%d" % m)
            if cof != 6 * t - 1 and cof != 6 * t + 1:
                STOP("edge cofactor not a wing of t at m=%d" % m)
            if bigomega(wing) != bigomega(cof) + 1:
                STOP("parity transport Omega(wing) != Omega(cof)+1 at m=%d p=%d" % (m, p))
            checked += 1
            if checked >= 10 ** 5:
                break
        if checked >= 10 ** 5:
            break
    print("  (b) Lean peel_parity_transport int-exact (Omega(wing) = Omega(cof) + 1,"
          " wing = p*cof, cof a wing of t) on %d edges -> PASS" % checked)

    # (c) peel_target_window intervals by enumeration on small cases
    viol = 0
    for k in (0, 5, 100, 1000, 5000):
        for g in (5, 18):
            for m in range(k + 1, k + g + 1):
                for (t, p, cof, fresh) in peel_edges(m):
                    lo_p = (6 * k + 5 - p) // (6 * p)
                    hi_p = (6 * (k + g) + 1 + p) // (6 * p)
                    if not (lo_p <= t <= hi_p):
                        viol += 1
                        print("  COUNTEREXAMPLE k=%d g=%d m=%d p=%d t=%d not in [%d,%d]"
                              % (k, g, m, p, t, lo_p, hi_p))
    if viol:
        STOP("peel_target_window interval violated %d times" % viol)
    print("  (c) Lean peel_target_window intervals verified by enumeration"
          " (k in {0,5,100,1000,5000} x g in {5,18}, every edge) -> PASS")

    # (d) window_edge_count: canonical peel defined exactly on non-twins; count law
    for (k, g) in ((0, 30), (100, 50), (10 ** 5, 40), (10 ** 6, 30)):
        nt = 0
        edges = set()
        for m in range(k + 1, k + g + 1):
            tw = gd.is_twin(m)
            cp = canonical_peel(m)
            if tw != (cp is None):
                STOP("canonicalPeel defined-iff-non-twin fails at m=%d" % m)
            if not tw:
                nt += 1
                edges.add((m, cp))
                # verify the canonical edge is a genuine peel edge
                if cp not in [t for (t, p, c, f) in peel_edges(m)]:
                    STOP("canonical edge (m=%d, t=%d) is not a peel edge" % (m, cp))
        if nt != len(edges):
            STOP("window_edge_count violated on (k,g)=(%d,%d)" % (k, g))
    print("  (d) Lean window_edge_count: #nonTwins == #canonical out-edges on 4 windows;"
          " canonical edge is a PeelStep -> PASS")

    # (e) defect witnesses verified (r clean, r+1..r+L struck, r+L+1 clean)
    for A, rs in sorted(DEFECT_R.items()):
        L = G_EXACT[A] - 1
        for r in rs:
            arr = np.arange(r, r + L + 2, dtype=np.int64)
            sm = struck_mask(arr, A)
            if sm[0] or not sm[1:L + 1].all() or sm[L + 1]:
                STOP("defect witness fails at A=%d r=%d" % (A, r))
    print("  (e) listed defect witnesses A in {23,29,31,37,41,43}: r clean,"
          " r+1..r+L all struck, r+L+1 clean -> PASS")
    # Lean small-label instances (r=117 and r=502 at A=17)
    for r in (117, 502):
        for j in range(17):
            m = r + 1 + j
            ok = False
            for wing in (6 * m - 1, 6 * m + 1):
                mf = min(gd.fac_distinct(wing))
                if mf <= 17:
                    ok = True
            if not ok:
                STOP("defect_edges_small_labels_17 fails at r=%d j=%d" % (r, j))
    print("      Lean defect_edges_small_labels_17 instances (r=117 kernel-pinned"
          " upstream, r=502 in Step00PeelBilinear): minFac <= 17 per center -> PASS")

    # (f) mechanical-part exactness on 60 random windows (A=17 and A=23)
    for A, rmax in ((17, 10 ** 5), (23, 10 ** 6)):
        for r in rng.integers(50, rmax, 30):
            r = int(r)
            L = G_EXACT[A] - 1
            w = measure_window(r, L, A)
            if not w['mech_ok']:
                STOP("mechanical small-label counts != phase prediction at A=%d r=%d"
                     % (A, r))
    print("  (f) O1 mechanical part EXACT (observed label-q counts == phase-determined"
          " counts, q <= A) on 60 random windows (A=17, A=23) -> PASS")

    # (g) jacobi vs Euler criterion
    for _ in range(500):
        p = int(gd._PTD[rng.integers(3, 2000)])
        a = int(rng.integers(1, p))
        e = pow(a, (p - 1) // 2, p)
        e = -1 if e == p - 1 else e
        if jacobi(a, p) != e:
            STOP("jacobi(%d,%d) != Euler criterion" % (a, p))
    print("  (g) jacobi == Euler criterion on 500 random (a, p) -> PASS")

    # (h) scan calibration at A=17/19
    runs17 = scan_runs(17, SCAN_LIMIT[17])
    d17 = sorted(r for r, e in runs17 if e == 17)
    if len(d17) != 20 or d17[0] != 117 or 502 not in d17:
        STOP("A=17 scan calibration failed: %s" % d17[:6])
    runs19 = scan_runs(19, SCAN_LIMIT[19])
    d19 = sorted(r for r, e in runs19 if e == 24)
    if len(d19) != 20 or d19[0] != 110:
        STOP("A=19 scan calibration failed: %s" % d19[:6])
    print("  (h) scan calibration: A=17 -> 20 defect starts, first r=117 (r=502 present);"
          " A=19 -> 20 starts, first r=110; matches gap_extremal_run1.log -> PASS")

    # (i) twin shortcut == gd.is_twin on a sample
    for t in rng.integers(1, 10 ** 6, 2000):
        t = int(t)
        short = gd.is_prime(6 * t - 1) and gd.is_prime(6 * t + 1)
        if short != gd.is_twin(t):
            STOP("twin shortcut mismatch at t=%d" % t)
    print("  (i) twin-hit shortcut (cof prime AND fresh prime) == gd.is_twin on 2000"
          " sample -> PASS")

    os.makedirs(SCRATCH, exist_ok=True)
    with open(os.path.join(SCRATCH, "peel_scan_runs.json"), "w") as f:
        json.dump({"17": runs17, "19": runs19}, f)
    print("SELFTEST verdict: ALL STOP-SELFTESTS PASS (%.1fs); scan cache -> %s"
          % (time.time() - t0, SCRATCH))
    sys.stdout.flush()


# ================================================================== stage: defect

def stage_defect():
    assert_registered()
    banner("DEFECT", "populations (a)-(d), observables O1-O5, scales 17..43")
    setup()
    t_stage = time.time()
    os.makedirs(SCRATCH, exist_ok=True)
    cache_p = os.path.join(SCRATCH, "peel_scan_runs.json")
    scan_cache = {}
    if os.path.exists(cache_p):
        with open(cache_p) as f:
            scan_cache = {int(k): [tuple(x) for x in v] for k, v in json.load(f).items()}
    results = {}
    nctrl_shrink = 1
    for A in SCALES:
        G = G_EXACT[A]
        L = G - 1
        t0 = time.time()
        if time.time() - t_stage > STAGE_TIME_CAP and nctrl_shrink == 1:
            nctrl_shrink = 2
            print("  RUNTIME FALLBACK: stage cap %ds exceeded -- halving NCTRL for the"
                  " remaining scales (registered fallback, logged)" % STAGE_TIME_CAP)
        print("-" * 78)
        print("SCALE A=%d  G=%d  L=%d  P_A=%s" % (A, G, L, "{:,}".format(PERIODS[A])))
        # ---- populations
        runs = []
        if A in SCAN_LIMIT:
            if A in scan_cache:
                runs = scan_cache[A]
                print("  scan cache hit: %d runs" % len(runs))
            else:
                runs = scan_runs(A, SCAN_LIMIT[A])
                scan_cache[A] = runs
        defects = sorted(DEFECT_R.get(A, []))
        if A in SCAN_LIMIT:
            scan_defects = sorted(r for r, e in runs if e == L and r >= R_MIN_HARVEST)
            defects = sorted(set(defects) | set(scan_defects))
        rng_h = np.random.default_rng([SEED, A, 1])
        near = {}
        for ell in (G - 3, G - 2):
            cand = [r for r, e in runs if e == ell and r >= R_MIN_HARVEST]
            tot = len(cand)
            if tot > NEAR_CAP:
                cand = sorted(int(c) for c in
                              rng_h.choice(cand, size=NEAR_CAP, replace=False))
                print("  near-defect ell=%d: %d found, capped to %d (registered cap)"
                      % (ell, tot, NEAR_CAP))
            near[ell] = cand
        nc = min(max(NCTRL[A] // nctrl_shrink, 8), CTRL_U_MAX[A])
        rng_c = np.random.default_rng([SEED, A, 2])
        ctrls, typs = [], []
        for r in defects:
            us = rng_c.choice(np.arange(1, CTRL_U_MAX[A] + 1), size=nc, replace=False)
            ctrls.extend(int(r + 5005 * u) for u in us)
            ws = rng_c.choice(np.arange(1, TYP_W_MAX[A] + 1), size=nc, replace=False)
            typs.extend(int(r + w) for w in ws)
        print("  populations: defect n=%d (%s%s), near G-3/G-2 n=%d/%d, matched-phase"
              " n=%d, typical n=%d"
              % (len(defects),
                 ",".join(str(r) for r in defects[:4]),
                 ",..." if len(defects) > 4 else "",
                 len(near[G - 3]), len(near[G - 2]), len(ctrls), len(typs)))
        if A >= 37:
            print("  DISCLOSED: n=1 defect at A=%d, no scan (period %s) -- two-sample"
                  " read as descriptive sigma-offset, NOT a test; no depth regression."
                  % (A, "{:,}".format(PERIODS[A])))
        sys.stdout.flush()
        # ---- measurement
        pops = {}
        for name, rl in (("defect", [(r, L) for r in defects]),
                         ("near", [(r, e) for e in (G - 3, G - 2) for r in near[e]]),
                         ("ctrl", [(r, L) for r in ctrls]),
                         ("typ", [(r, L) for r in typs])):
            rows = []
            tm = time.time()
            for (r, ell) in rl:
                rows.append(measure_window(r, ell, A))
            pops[name] = rows
            if rl:
                print("  measured %-6s n=%4d  [%.1fs]  fac_incomplete(sum)=%d"
                      % (name, len(rl), time.time() - tm,
                         sum(w['fac_inc'] for w in rows)))
            sys.stdout.flush()
        mech_bad = sum(1 for rows in pops.values() for w in rows if not w['mech_ok'])
        if mech_bad:
            print("  WARNING: mechanical-part mismatch on %d windows (small-label"
                  " subtraction NOT exact there -- excluded from O1)" % mech_bad)
        # ---- statistics
        res = dict(A=A, G=G, L=L, n=dict((k, len(v)) for k, v in pops.items()),
                   mech_bad=mech_bad)
        keyfmt = "  %-3s defect mean %+9.4f | matched %+9.4f | typical %+9.4f |" \
                 " z(d-m) %+7.2f (n=%d/%d) | z(d-t) %+7.2f%s"
        for key in ("o1", "o2", "o3", "o4", "o5"):
            dv = [w[key] for w in pops['defect'] if w['mech_ok'] or key != 'o1']
            cv = [w[key] for w in pops['ctrl'] if w['mech_ok'] or key != 'o1']
            tv = [w[key] for w in pops['typ'] if w['mech_ok'] or key != 'o1']
            zdm, ndm, ncm = welch(dv, cv)
            zdt, _, _ = welch(dv, tv)
            note = ""
            if len(dv) == 1:
                so_m = sigma_offset(dv[0], cv)
                so_t = sigma_offset(dv[0], tv)
                note = " | n=1: sigma-offset vs matched %+.2f, vs typical %+.2f" \
                       " (descriptive, NOT a test)" % (so_m, so_t)
                zdm = zdt = float('nan')
            flag = ""
            if np.isfinite(zdm) and abs(zdm) >= 3:
                flag = "  FLAG|z|>=3"
            if np.isfinite(zdt) and abs(zdt) >= 3:
                flag += "  FLAG(d-t)|z|>=3"
            print((keyfmt + "%s")
                  % (key.upper(), np.nanmean(dv) if dv else float('nan'),
                     np.nanmean(cv) if cv else float('nan'),
                     np.nanmean(tv) if tv else float('nan'),
                     zdm, len(dv), len(cv), zdt, note, flag))
            res[key] = dict(dmean=float(np.nanmean(dv)) if dv else None,
                            cmean=float(np.nanmean(cv)) if cv else None,
                            tmean=float(np.nanmean(tv)) if tv else None,
                            zdm=None if not np.isfinite(zdm) else float(zdm),
                            zdt=None if not np.isfinite(zdt) else float(zdt),
                            nd=len(dv), ncm=len(cv))
        # O3 de-mechanized (pooled demech vs OMP, all populations of this scale)
        allw = [w for rows in pops.values() for w in rows]
        P3 = np.array([w['o3'] for w in allw])
        OMP = np.array([w['omp'] for w in allw])
        P3d = bp.demech(P3, OMP)
        tags = np.array(sum(([nm] * len(rows) for nm, rows in pops.items()), []))
        z3d, n1, n2 = welch(P3d[tags == 'defect'], P3d[tags == 'ctrl'])
        z3dt, _, _ = welch(P3d[tags == 'defect'], P3d[tags == 'typ'])
        if (tags == 'defect').sum() == 1:
            so = sigma_offset(float(P3d[tags == 'defect'][0]), P3d[tags == 'ctrl'])
            print("  O3d (demech) n=1: sigma-offset vs matched %+.2f (descriptive)" % so)
            res['o3d'] = dict(zdm=None, sigma=None if not np.isfinite(so) else float(so))
        else:
            print("  O3d (demech vs 20-bin OMP): z(d-m) %+7.2f (n=%d/%d) | z(d-t) %+7.2f%s"
                  % (z3d, n1, n2, z3dt,
                     "  FLAG|z|>=3" if np.isfinite(z3d) and abs(z3d) >= 3 else ""))
            res['o3d'] = dict(zdm=None if not np.isfinite(z3d) else float(z3d),
                              zdt=None if not np.isfinite(z3dt) else float(z3dt))
        # O1 per-dyadic-block two-sample (pooled count >= MIN_BLOCK_POOL)
        blocks = sorted(set(j for w in pops['defect'] + pops['ctrl'] for j in w['dy']))
        nblk = 0
        for j in blocks:
            dj = [w['dy'].get(j, 0) / float(w['L']) for w in pops['defect'] if w['mech_ok']]
            cj = [w['dy'].get(j, 0) / float(w['L']) for w in pops['ctrl'] if w['mech_ok']]
            pooled = sum(w['dy'].get(j, 0) for w in pops['defect'] + pops['ctrl'])
            if pooled < MIN_BLOCK_POOL:
                continue
            nblk += 1
            zj, _, _ = welch(dj, cj)
            if np.isfinite(zj) and abs(zj) >= 3:
                print("  O1 block 2^%d..2^%d: z(d-m) = %+.2f  FLAG|z|>=3 (rate d=%.4f"
                      " m=%.4f)" % (j, j + 1, zj, np.mean(dj), np.mean(cj)))
        print("  O1 per-block family: %d blocks tested (pooled>=%d), flags printed above"
              " if any" % (nblk, MIN_BLOCK_POOL))
        # ---- defect-depth regression over ell strata
        rng_r = np.random.default_rng([SEED, A, 3])
        strat = pops['near'] + pops['defect']
        ells = [w['L'] for w in strat]
        res['reg'] = {}
        if len(set(ells)) >= 2 and len(ells) >= 10:
            for key in ("o1", "o2", "o3", "o4", "o5"):
                y = [w[key] for w in strat]
                rr, zz, nn = perm_reg_z(y, ells, rng_r)
                trend = np.isfinite(zz) and abs(zz) >= 3
                print("  depth-regression %-3s vs ell: r=%+.4f z=%+7.2f n=%d%s"
                      % (key.upper(), rr if np.isfinite(rr) else float('nan'),
                         zz if np.isfinite(zz) else float('nan'), nn,
                         "  TREND|z|>=3" if trend else ""))
                res['reg'][key] = dict(r=None if not np.isfinite(rr) else float(rr),
                                       z=None if not np.isfinite(zz) else float(zz),
                                       n=nn)
        else:
            print("  depth-regression: UNAVAILABLE (strata %s, n=%d) -- disclosed"
                  % (sorted(set(ells)), len(ells)))
        res['fac_incomplete'] = sum(w['fac_inc'] for rows in pops.values() for w in rows)
        res['fac_total_windows'] = sum(len(rows) for rows in pops.values())
        print("  factorization completeness at A=%d: %d incomplete of %d factor calls"
              " so far (cumulative counter %d/%d)"
              % (A, res['fac_incomplete'], FAC_STATS['total'],
                 FAC_STATS['incomplete'], FAC_STATS['total']))
        results[A] = res
        print("  scale A=%d done [%.1fs]" % (A, time.time() - t0))
        sys.stdout.flush()
    with open(cache_p, "w") as f:
        json.dump({str(k): v for k, v in scan_cache.items()}, f)
    with open(os.path.join(SCRATCH, "peel_defect.json"), "w") as f:
        json.dump({str(k): v for k, v in results.items()}, f)
    print("DEFECT stage done [%.1fs total]; JSON -> %s"
          % (time.time() - t_stage, os.path.join(SCRATCH, "peel_defect.json")))
    sys.stdout.flush()


# ================================================================== stage: foil

def edge_invariants(X, NW):
    """Per-window O2/O3/O4 invariant arrays (A-dependent spin variants for FOIL_A)."""
    ncent = NW * H
    blo = math.ceil(X ** 0.25)
    bhi = math.isqrt(X)
    spinF = {A: np.zeros(NW) for A in FOIL_A}
    spinFn = {A: np.zeros(NW) for A in FOIL_A}
    spinL = {A: np.zeros(NW) for A in FOIL_A}
    spinLn = {A: np.zeros(NW) for A in FOIL_A}
    o3F = np.zeros(NW)
    o3Fn = np.zeros(NW)
    o3L = np.zeros(NW)
    o3Ln = np.zeros(NW)
    o4F = np.zeros(NW)
    o4L = np.zeros(NW)
    t0 = time.time()
    for w in range(NW):
        for i in range(H):
            m = X + w * H + i
            left = i < H // 2
            for (t, p, cof, fresh) in peel_edges(m):
                of = bigomega(fresh)
                if of is None:
                    continue
                lf = 1 - 2 * (of & 1)
                o3F[w] += lf
                o3Fn[w] += 1
                hit = 1.0 if (of == 1 and gd.is_prime(cof)) else 0.0
                o4F[w] += hit
                if left:
                    o3L[w] += lf
                    o3Ln[w] += 1
                    o4L[w] += hit
                if blo <= p <= bhi:
                    s = jacobi(cof % p, p)
                    for A in FOIL_A:
                        if p > A:
                            spinF[A][w] += s
                            spinFn[A][w] += 1
                            if left:
                                spinL[A][w] += s
                                spinLn[A][w] += 1
        if (w + 1) % 500 == 0:
            print("    edges: %d/%d windows (%.0fs)" % (w + 1, NW, time.time() - t0))
            sys.stdout.flush()
    inv = dict(
        o3F=np.where(o3Fn > 0, o3F / np.maximum(o3Fn, 1), np.nan),
        o3L=np.where(o3Ln > 0, o3L / np.maximum(o3Ln, 1), np.nan),
        o4F=np.where(o3Fn > 0, o4F / np.maximum(o3Fn, 1), np.nan),
        o4L=np.where(o3Ln > 0, o4L / np.maximum(o3Ln, 1), np.nan))
    for A in FOIL_A:
        inv['o2F%d' % A] = np.where(spinFn[A] > 0,
                                    spinF[A] / np.sqrt(np.maximum(spinFn[A], 1)), np.nan)
        inv['o2L%d' % A] = np.where(spinLn[A] > 0,
                                    spinL[A] / np.sqrt(np.maximum(spinLn[A], 1)), np.nan)
        inv['o2n%d' % A] = float(spinFn[A].sum())
    print("  edge invariants: %d windows, block p in [%d, %d], O3 edges/window mean"
          " %.1f [%.0fs]" % (NW, blo, bhi, float(np.nanmean(o3Fn)), time.time() - t0))
    sys.stdout.flush()
    return inv


def foil_cell(px, A, inv, jpath):
    X, ncent = px['X'], px['ncent']
    NW = ncent // H
    banner("FOIL-CELL", "X=%.0e A=%d NW=%d H=%d (foil-v2, seed %d)"
           % (X, A, NW, H, SEED))
    m_arr = X + np.arange(ncent, dtype=np.int64)
    clean = np.ones(ncent, bool)
    for q in WPRIMES[A] if A in WPRIMES else [p for p in bp.primes_upto(A) if p >= 5]:
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    cl = clean.reshape(NW, H)
    lamw = px['lam'][:ncent].reshape(NW, H).astype(np.float64)
    right = np.zeros((NW, H), bool)
    right[:, H // 2:] = True
    masks = {'S': cl, 'Ssplit': cl & right, 'So': cl}   # So == S (disclosed degenerate)
    loads = {k: (lamw * msk).sum(1) for k, msk in masks.items()}
    pool = px['lam'][:ncent][clean].astype(np.float64)
    rng = np.random.default_rng(SEED)
    nulls = {k: np.empty((200, NW)) for k in masks}
    lmat = np.zeros((NW, H))
    nsurv = int(cl.sum())
    for t2 in range(200):
        lmat[:] = 0.0
        lmat[cl] = rng.choice(pool, size=nsurv)
        for k, msk in masks.items():
            nulls[k][t2] = (lmat * msk).sum(1)
    om = (px['OLb'][bp.BAND:bp.BAND + ncent] + px['ORb'][bp.BAND:bp.BAND + ncent])
    ompF = om.reshape(NW, H).mean(1) / 2.0
    ompL = om.reshape(NW, H)[:, :H // 2].mean(1) / 2.0
    o3dL = bp.demech(inv['o3L'], ompL)
    rows = [("O2|S", inv['o2F%d' % A], 'S'),
            ("O2|S''", inv['o2L%d' % A], 'Ssplit'),
            ("O3|S''", inv['o3L'], 'Ssplit'),
            ("O3|S", inv['o3F'], 'S'),
            ("O3|So", inv['o3F'], 'So'),
            ("O3d|S''", o3dL, 'Ssplit'),
            ("O4|S", inv['o4F'], 'S'),
            ("O4|S''", inv['o4L'], 'Ssplit')]
    print("  survivors=%d | O2 block edges (p>A) total=%d | So==S disclosed degenerate"
          % (nsurv, int(inv['o2n%d' % A])))
    res = {}
    for name, I, lk in rows:
        st = bp.foil_row(I, loads[lk], nulls[lk], np.random.default_rng(SEED + 7))
        res[name] = st
        print("  %-8s R=%+8.4f zW=%+6.1f zI=%+6.1f n=%5d %s"
              % (name, st['R'], st['zW'], st['zI'], st['n'], st['note']))
    meta = dict(X=X, A=A, NW=NW, nsurv=nsurv,
                o2edges=int(inv['o2n%d' % A]),
                means={k: float(np.nanmean(inv[k]))
                       for k in ('o3F', 'o3L', 'o4F', 'o4L')})
    with open(jpath, 'w') as f:
        json.dump(dict(meta=meta, rows=res), f)
    print("  cell JSON -> %s" % jpath)
    sys.stdout.flush()


def stage_foil():
    assert_registered()
    banner("FOIL", "foil-v2 ensemble grid A in {13,31,101} x X in {1e6,1e9}")
    setup()
    bp.setup_factor_tables()
    t0 = time.time()
    for X, NW in FOIL_X:
        if time.time() - t0 > STAGE_TIME_CAP:
            NW = NW // 2
            print("  RUNTIME FALLBACK: stage cap exceeded -- NW halved to %d for"
                  " X=%.0e (registered fallback, logged)" % (NW, X))
        px = bp.precompute_X(X, NW)
        inv = edge_invariants(X, NW)
        inc = FAC_STATS['incomplete']
        print("  fresh-wing factorization completeness at X=%.0e: %d incomplete of %d"
              % (X, inc, FAC_STATS['total']))
        for A in FOIL_A:
            jpath = os.path.join(SCRATCH, "peel_foil_%d_%d.json" % (X, A))
            foil_cell(px, A, inv, jpath)
    print("FOIL stage done [%.1fs total]" % (time.time() - t0))
    sys.stdout.flush()


# ================================================================== stage: summary

def stage_summary():
    assert_registered()
    banner("SUMMARY", "verdict matrix (gate_g3 verbatim) + interpretation gate + STOP")
    cells = [(X, A) for X, _ in FOIL_X for A in FOIL_A]
    data = {}
    for X, A in cells:
        jp = os.path.join(SCRATCH, "peel_foil_%d_%d.json" % (X, A))
        with open(jp) as f:
            data[(X, A)] = json.load(f)
    with open(os.path.join(SCRATCH, "peel_defect.json")) as f:
        ddata = {int(k): v for k, v in json.load(f).items()}

    print("FOIL-v2 verdicts (thresholds verbatim: MANAGED-PASS iff min|z_I| >= 5 over"
          " the grid AND |R(A_hi)| >= |R(A_lo)|/3 for pairs (13->31),(31->101) at both"
          " X; SOFT-PASS iff min|z_I| >= 3; else PARITY-BLIND-UNDER-ESCALATION-v2):")
    primary = [("O2", "O2|S"), ("O3", "O3|S''"), ("O4", "O4|S")]
    verdicts = {}
    for label, row in primary + [("O3d", "O3d|S''")]:
        zs, Rs, parts = [], {}, []
        for (X, A) in cells:
            st = data[(X, A)]['rows'][row]
            zs.append(abs(st['zI']))
            Rs[(X, A)] = st['R']
            parts.append("A=%3d X=%.0e R%+.4f zI%+6.2f" % (A, X, st['R'], st['zI']))
        ratios = []
        ratio_ok = True
        for X, _ in FOIL_X:
            for alo, ahi in ((13, 31), (31, 101)):
                lo, hi_ = abs(Rs[(X, alo)]), abs(Rs[(X, ahi)])
                ratios.append("%.0e:%d->%d=%.2f" % (X, alo, ahi,
                              (hi_ / lo) if lo > 1e-9 else float('inf')))
                if lo > 1e-9 and hi_ < lo / 3.0:
                    ratio_ok = False
        v = ("MANAGED-PASS" if min(zs) >= 5 and ratio_ok
             else "SOFT-PASS" if min(zs) >= 3
             else "PARITY-BLIND-UNDER-ESCALATION-v2")
        verdicts[label] = (min(zs), ratio_ok, v)
        print("  %-4s (%s):" % (label, row))
        for p_ in parts:
            print("        %s" % p_)
        print("        min|z_I|=%.2f  escalation ratios [%s] ratio_ok=%s  -> %s"
              % (min(zs), ", ".join(ratios), ratio_ok, v))
    print("-" * 78)
    print("  secondary rows (information, not verdicts):")
    for row in ("O2|S''", "O3|S", "O3|So", "O4|S''"):
        parts = []
        for (X, A) in cells:
            st = data[(X, A)]['rows'][row]
            parts.append("R%+.3f zI%+5.1f" % (st['R'], st['zI']))
        print("  %-8s %s" % (row, " | ".join(parts)))
    print("-" * 78)
    print("INTERPRETATION GATE: O3 content = O3 verdict AND O3d verdict:")
    o3v, o3dv = verdicts['O3'][2], verdicts['O3d'][2]
    o3content = o3v if (o3v != "PARITY-BLIND-UNDER-ESCALATION-v2"
                        and o3dv != "PARITY-BLIND-UNDER-ESCALATION-v2") \
        else "PARITY-BLIND-UNDER-ESCALATION-v2"
    print("  O3=%s, O3d=%s -> O3 content verdict: %s" % (o3v, o3dv, o3content))
    print("-" * 78)
    print("DEFECT-STAGE trends (O1/O5 defect-vs-matched residuals + depth regression):")
    trend_scales = []
    for A in SCALES:
        if A not in ddata:
            continue
        d = ddata[A]
        reg = d.get('reg', {})
        parts = []
        any_trend = False
        for key in ("o1", "o5"):
            zdm = d[key].get('zdm')
            rz = reg.get(key, {}).get('z')
            tr = rz is not None and abs(rz) >= 3
            any_trend = any_trend or tr
            parts.append("%s: z(d-m)=%s reg-z=%s%s"
                         % (key.upper(),
                            "%+.2f" % zdm if zdm is not None else "n=1",
                            "%+.2f" % rz if rz is not None else "NA",
                            " TREND" if tr else ""))
        if any_trend:
            trend_scales.append(A)
        print("  A=%2d  %s" % (A, " | ".join(parts)))
    print("  O1/O5 depth-regression TREND (|z|>=3) at scales: %s (need >= 2 to block"
          " STOP)" % (trend_scales if trend_scales else "none"))
    print("-" * 78)
    print("SECONDARY (deterministic lean-model tree profile; proof-search shadow, no")
    print("  Lean statements, quoted from tools/phase_cover_run1.log): no-mirror UNSAT")
    print("  B&B nodes A=17:464 19:2,626 23:5,301 29:11,527 31:30,079 37:25,543")
    print("  41:473,293 43:4,889,831; UNSAT trees SHRINK above G(A) (x13.6 at 41,")
    print("  x16.0 at 43).")
    print("-" * 78)
    blind = all(verdicts[k][2] == "PARITY-BLIND-UNDER-ESCALATION-v2"
                for k in ("O2", "O3", "O4"))
    no_trend = len(trend_scales) < 2
    print("REGISTERED STOP EVALUATION:")
    print("  O2/O3/O4 all PARITY-BLIND-UNDER-ESCALATION-v2: %s" % blind)
    print("  O1/O5 defect-depth |z|>=3 trend at >= 2 scales: %s (scales: %s)"
          % (not no_trend, trend_scales if trend_scales else "none"))
    if blind and no_trend:
        print("  STOP TRIGGERED -- ledger null: the bilinear/peel layer is parity-blind")
        print("  and phase-determined.  The Lean identities (peel_parity_transport /")
        print("  peel_sign_flip / window_edge_count / struck_wing_minFac_le +")
        print("  defect_edges_small_labels_17 / peel_target_window) are kept as the")
        print("  exact conservation laws of the layer.  No new weightings, no threshold")
        print("  moves, no extra blocks.")
    else:
        print("  STOP NOT TRIGGERED -- surviving signals listed above; next step is")
        print("  outside this pre-registration (no threshold moves inside it).")
    sys.stdout.flush()


# ================================================================== main

if __name__ == "__main__":
    install_log()
    mode = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if mode == "selftest":
        stage_selftest()
    elif mode == "defect":
        stage_defect()
    elif mode == "foil":
        stage_foil()
    elif mode == "summary":
        stage_summary()
    else:
        print("unknown mode %r" % mode)
        sys.exit(2)
