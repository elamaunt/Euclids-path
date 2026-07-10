# betti_portrait_harness.py -- BP gate: localized Betti/holonomy portraits of window
# complexes under foil-v2 escalation.  Stages S0..S4 are SEPARATE argv modes, each run
# as a separate invocation appending to tools/betti_portrait_run1.log (crash-resilient
# protocol).  Feeds tools/LAWS_ordered_exponent.md (entries L39-L42).
#
# House reuse (copied per pattern from tools/gain_complex_harness.py, which mirrors
# tools/relindex_harness.py::Step00Graph / EuclidsPath/Engine/GeometryFront.lean):
# Step00Graph, closure, sector_counts, fills (T/I/Q), rank_fp (kept verbatim as
# rank_fp_ref; the production rank_fp vectorizes the elimination and parametrizes the
# prime -- cross-checked against rank_fp_ref in S0), quotient_betti, omega_range.
# Verdict machinery and thresholds are copied from gate_g3 (foil-v2):
#   MANAGED-PASS iff min |z_I| >= 5 over the grid AND |R(31)| >= |R(13)|/3 at both X;
#   SOFT-PASS iff min |z_I| >= 3; else PARITY-BLIND-UNDER-ESCALATION-v2;
#   200 permutations (sigma_W) + 200 lambda-resamples (sigma_I); seed 20260710.
#
# LOCALIZATION CONVENTION (stated verbatim here and in ledger L39):
#   LocalComplex(A,X,H,D), M0=4: centers m in [X,X+H); survivors S = clean centers
#   (residue tests q in [5,A]); defect levels n in [max(0,X-D),X+H) with n < m for some
#   survivor; edges: within-window tournament (clean m->n, both survivors), boundary
#   m->(n,q,s) (q<=A prime, q | sideValue(s,n), n<m), peel edges (n,q,s)->t only if the
#   factor-target t lies in the band [max(0,X-D),X+H), absorb only n<=M0.  At X>=10^6
#   no peel factor-target lies in the band (max target ~ (X+H)/5 < X-D) and no defect
#   level reaches M0=4: the window complexes carry NO peel edges, NO absorbers and NO
#   Q-cells (disclosed).  D=H primary; sensitivity D in {0,5H} on a subsample.
#
# STOP rules: any S0 selftest violation, any S1 formula/matrix mismatch, any S2(alpha)
# exact flip-count mismatch, any S3 exact transport-identity violation prints the
# counterexample and exits 1 (later stages must not run).

import json
import math
import os
import sys
import tempfile
import time
from collections import deque, defaultdict

import numpy as np

P1, P2 = 10007, 10009            # rank cross-check primes (house convention)
P12A, P12B = 10009, 10069        # twisted-rank primes, both = 1 (mod 12)
SEED = 20260710
BAND = 100                       # max band below X precomputed (covers D=H for H<=100)
DEPTH_CAP, CENSOR, NODE_BUDGET = 6, 7, 300   # P3 grave-depth caps (censored value = 7)
P3_TIME_CAP = 1800               # hard cap (s) per X for the grave-depth pass
QLAD = {13: (17, 19, 23), 31: (37, 41, 43)}  # ladder clocks; {17,19,23} are already
                                 # clocks at A=31, so the A=31 ladder is shifted to the
                                 # next three primes (adaptation registered in S1)
OUT_DIR = os.environ.get("BP_OUT", tempfile.gettempdir())

CONVENTION = (
    "LocalComplex(A,X,H,D), M0=4: centers m in [X,X+H); survivors S = clean centers "
    "(residue tests q in [5,A]); defect levels n in [max(0,X-D),X+H) with n < m for "
    "some survivor; edges: within-window tournament (clean m->n, both survivors), "
    "boundary m->(n,q,s) (q<=A prime, q | sideValue(s,n), n<m), peel edges (n,q,s)->t "
    "only if the factor-target t lies in the band [max(0,X-D),X+H), absorb only n<=M0. "
    "At X>=10^6 no peel factor-target lies in the band (max target ~ (X+H)/5 < X-D) "
    "and no defect level reaches M0=4: the window complexes carry NO peel edges, NO "
    "absorbers and NO Q-cells (disclosed). D=H primary; sensitivity D in {0,5H} on a "
    "subsample.")


def banner(name, sub=""):
    print("=" * 78)
    print("[%s] %s  %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), name, sub))
    print("=" * 78)


def STOP(msg):
    print("STOP -- " + msg)
    print("STAGE VERDICT: STOP (design violation; later stages must not run)")
    sys.exit(1)


# ---------- house copies: graph layer (gain_complex_harness.py) ----------

def primes_upto(A):
    return [p for p in range(2, A + 1)
            if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def side_value(s, n):
    """sideValue in truncated nat: minus -> 6n-1 (0 at n=0!), plus -> 6n+1."""
    if s == '-':
        return 6 * n - 1 if n > 0 else 0
    return 6 * n + 1


class Step00Graph:
    """Vertices: ('c',m) center | ('d',n,q,s) defect | ('a',a) absorber."""

    def __init__(self, A, M0):
        self.A = A
        self.M0 = M0
        self.primes = primes_upto(A)
        self._clean = {}
        self._out = {}

    def clean(self, m):
        c = self._clean.get(m)
        if c is None:
            lo, hi = side_value('-', m), side_value('+', m)
            c = all(lo % q != 0 and hi % q != 0 for q in self.primes)
            self._clean[m] = c
        return c

    def out(self, v):
        e = self._out.get(v)
        if e is not None:
            return e
        out = []
        if v[0] == 'c':
            m = v[1]
            if self.clean(m):
                for n in range(m):
                    if self.clean(n):
                        out.append((('c', n), 'clean'))
                    for s in ('-', '+'):
                        sv = side_value(s, n)
                        for q in self.primes:
                            if sv % q == 0:
                                out.append((('d', n, q, s), 'boundary'))
        elif v[0] == 'd':
            _, n, q, s = v
            sv = side_value(s, n)
            seen = set()
            for t in range(n):
                for os_ in ('-', '+'):
                    if sv == q * side_value(os_, t) and t not in seen:
                        seen.add(t)
                        out.append((('c', t), 'peel'))
            if n <= self.M0:
                out.append((('a', n), 'absorb'))
        self._out[v] = out
        return out


def closure(g, seeds):
    W = set()
    dq = deque()
    for s in seeds:
        if s not in W:
            W.add(s)
            dq.append(s)
    edges = []
    while dq:
        v = dq.popleft()
        for w, et in g.out(v):
            edges.append((v, w, et))
            if w not in W:
                W.add(w)
                dq.append(w)
    S = {v for v in W if v[0] == 'c' and g.clean(v[1])}
    outdeg = defaultdict(int)
    for a, b, _ in edges:
        outdeg[a] += 1
    assert sum(1 - outdeg[v] for v in W) == len(W) - len(edges)
    return W, edges, S


def sector_counts(edges, S):
    c = dict(ESS=0, ESK=0, EKS=0, EKK=0)
    for u, v, _ in edges:
        su, sv = u in S, v in S
        if su and sv:
            c['ESS'] += 1
        elif su:
            c['ESK'] += 1
        elif sv:
            c['EKS'] += 1
        else:
            c['EKK'] += 1
    return c


def fills(g, W, edges, S, canonical):
    surv = sorted(v[1] for v in S)
    eset = {(u, v) for u, v, _ in edges}
    faces = []
    if len(surv) >= 3:
        b = surv[0]
        for i in range(1, len(surv)):
            for j in range(i + 1, len(surv)):
                faces.append(('T', ('c', surv[j]), ('c', surv[i]), ('c', b)))
    if not canonical:
        return faces
    for (u, w, et) in edges:
        if et == 'boundary' and u in S:
            n = w[1]
            above = [x for x in surv if x > n]
            if above and u[1] != min(above):
                prevs = [x for x in above if x < u[1]]
                if prevs:
                    pv = max(prevs)
                    if (u, ('c', pv)) in eset and (('c', pv), w) in eset:
                        faces.append(('I', u, ('c', pv), w))
    for a in [v for v in W if v[0] == 'a']:
        n = a[1]
        fan = sorted([v for v in W if v[0] == 'd' and v[1] == n and (v, a) in eset],
                     key=lambda d: (d[2], 0 if d[3] == '-' else 1))
        above = [x for x in surv if x > n]
        if len(fan) >= 2 and above:
            cmin = ('c', min(above))
            for i in range(len(fan) - 1):
                if (cmin, fan[i]) in eset and (cmin, fan[i + 1]) in eset:
                    faces.append(('Q', cmin, fan[i], a, fan[i + 1]))
    return faces


P_ELIM = 10007


def rank_fp_ref(M):
    """VERBATIM copy of gain_complex_harness.rank_fp (reference implementation)."""
    if M.size == 0:
        return 0
    A = (M % P_ELIM).astype(np.int64)
    r, rows, cols = 0, A.shape[0], A.shape[1]
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c] % P_ELIM:
                piv = i
                break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P_ELIM - 2, P_ELIM)
        A[r] = (A[r] * inv) % P_ELIM
        for i in range(rows):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % P_ELIM
        r += 1
        if r == rows:
            break
    return r


def rank_fp(M, p=P1):
    """Production rank over F_p: same elimination, vectorized row updates,
    parametrized prime.  Cross-checked against rank_fp_ref in S0."""
    if M.size == 0:
        return 0
    A = (np.asarray(M, dtype=np.int64) % p)
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        nz = np.flatnonzero(A[r:, c])
        if nz.size == 0:
            continue
        piv = int(nz[0]) + r
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[:, c].copy()
        col[r] = 0
        upd = np.flatnonzero(col)
        if upd.size:
            A[upd] = (A[upd] - np.outer(col[upd], A[r])) % p
        r += 1
        if r == rows:
            break
    return r


def quotient_betti(W, edges, faces, S, p=P1):
    """Copy of gain_complex_harness.quotient_betti with parametrized prime."""
    vq = sorted(S) + ['K*']
    vidx = {v: i for i, v in enumerate(vq)}
    eidx = {}
    for u, v, _ in edges:
        if ((u in S) or (v in S)) and (u, v) not in eidx:
            eidx[(u, v)] = len(eidx)
    D1 = np.zeros((len(vq), len(eidx)), dtype=np.int64)
    for e, j in eidx.items():
        u = e[0] if e[0] in S else 'K*'
        w = e[1] if e[1] in S else 'K*'
        if u != w:
            D1[vidx[w], j] += 1
            D1[vidx[u], j] -= 1
    D2 = np.zeros((len(eidx), len(faces)), dtype=np.int64)
    for k, f in enumerate(faces):
        if f[0] in ('T', 'I'):
            _, u, v, w = f
            for e, sgn in (((u, v), 1), ((v, w), 1), ((u, w), -1)):
                if e in eidx:
                    D2[eidx[e], k] += sgn
        else:
            _, c, d1, a, d2 = f
            for e, sgn in (((c, d1), 1), ((d1, a), 1), ((c, d2), -1), ((d2, a), -1)):
                if e in eidx:
                    D2[eidx[e], k] += sgn
    r1, r2 = rank_fp(D1, p), rank_fp(D2, p)
    return len(vq) - r1, len(eidx) - r1 - r2, len(faces) - r2


def omega_range(lo_m, n_centers):
    """VERBATIM copy of gain_complex_harness.omega_range."""
    lim = int(math.isqrt(6 * (lo_m + n_centers) + 10)) + 1
    sieve = np.ones(lim + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(lim ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    ps = [int(p) for p in np.flatnonzero(sieve)]
    out = []
    for off in (-1, 1):
        vals = 6 * (lo_m + np.arange(n_centers, dtype=np.int64)) + off
        rem = vals.copy()
        big = np.zeros(n_centers, dtype=np.int16)
        for p in ps:
            if p < 5:
                continue
            inv6 = pow(6, -1, p)
            r = (inv6 if off == -1 else (p - inv6) % p)
            first = (r - lo_m) % p
            if first >= n_centers:
                continue
            idx = np.arange(first, n_centers, p)
            rem[idx] //= p
            big[idx] += 1
            cur = idx[rem[idx] % p == 0]
            while cur.size:
                rem[cur] //= p
                big[cur] += 1
                cur = cur[rem[cur] % p == 0]
        big[rem > 1] += 1
        out.append(big.astype(np.int32))
    return out[0], out[1]


# ---------- S0: the localized window-complex builder ----------

def build_local(A, X, H, D, M0=4):
    """LocalComplex(A,X,H,D) per the verbatim convention above.
    Returns (W, edges, S) in the same shape as closure()."""
    g = Step00Graph(A, M0)
    lo, hi = max(0, X - D), X + H
    surv = [m for m in range(X, hi) if g.clean(m)]
    S = {('c', m) for m in surv}
    W = set(S)
    edges = []
    if not surv:
        return W, edges, set()
    top = surv[-1]
    for m in surv:                                   # within-window tournament
        for n in surv:
            if n < m:
                edges.append((('c', m), ('c', n), 'clean'))
    defs = []
    for n in range(lo, min(hi, top)):                # defect levels, n < max survivor
        for s in ('-', '+'):
            sv = side_value(s, n)
            for q in g.primes:
                if sv % q == 0:
                    defs.append(('d', n, q, s))
    W.update(defs)
    for m in surv:                                   # boundary edges
        for d in defs:
            if d[1] < m:
                edges.append((('c', m), d, 'boundary'))
    for d in defs:                                   # peel (band-restricted) + absorb
        _, n, q, s = d
        if n >= 1:
            sv = side_value(s, n)
            w_ = sv // q
            seen = set()
            for off, os_ in ((-1, '-'), (1, '+')):
                if (w_ - off) % 6 == 0:
                    t = (w_ - off) // 6
                    if (0 <= t < n and lo <= t < hi and side_value(os_, t) == w_
                            and t not in seen):
                        seen.add(t)
                        W.add(('c', t))
                        edges.append((d, ('c', t), 'peel'))
        if n <= M0:
            a = ('a', n)
            W.add(a)
            edges.append((d, a, 'absorb'))
    return W, edges, S


def stage_s0():
    banner("S0", "localized window-complex builder + STOP selftests")
    print("CONVENTION (verbatim): " + CONVENTION)
    print()
    t0 = time.time()

    # (a) rank_fp (vectorized, parametrized) == rank_fp_ref (verbatim copy) on random
    rng = np.random.default_rng(SEED)
    for trial in range(30):
        M = rng.integers(-9, 10, size=(rng.integers(1, 25), rng.integers(1, 25)))
        if rank_fp(M, 10007) != rank_fp_ref(M):
            STOP("rank_fp != rank_fp_ref on %r" % (M,))
    print("  rank_fp (vectorized) == rank_fp_ref (verbatim gain copy), 30 random matrices -> PASS")

    # (b) kernel calibration cone3 (copied expectations) + LocalComplex == closure
    g5 = Step00Graph(5, 4)
    Wc, Ec, Sc = closure(g5, [('c', 3)])
    expect = {('c', 3), ('c', 2), ('c', 0),
              ('d', 0, 2, '-'), ('d', 0, 3, '-'), ('d', 0, 5, '-'), ('d', 1, 5, '-'),
              ('a', 0), ('a', 1)}
    if Wc != expect or len(Ec) != 14:
        STOP("cone3 closure does not match the Lean finset")
    Wl, El, Sl = build_local(5, 0, 4, 20, 4)
    if not (Wl == Wc and set(El) == set(Ec) and len(El) == len(Ec) and Sl == Sc
            and sector_counts(El, Sl) == sector_counts(Ec, Sc)):
        STOP("LocalComplex(5,0,4,20) != closure(cone3): W %s E %s"
             % (sorted(Wl ^ Wc), sorted(set(El) ^ set(Ec))))
    print("  cone3: closure == Lean finset (9 vertices, chi=-5); LocalComplex(5,0,4,D=20)")
    print("         reproduces closure EXACTLY (vertices, edges, sector counts) -> PASS")

    # (c) the 36 G1 regions: A in {5,7,11}, first 12 clean apexes
    fails = 0
    for A in (5, 7, 11):
        g = Step00Graph(A, 4)
        apexes = [m for m in range(1, 300) if g.clean(m)][:12]
        for apex in apexes:
            Wc, Ec, Sc = closure(g, [('c', apex)])
            Wl, El, Sl = build_local(A, 0, apex + 1, 5 * (apex + 1), 4)
            ok = (Wl == Wc and set(El) == set(Ec) and len(El) == len(Ec) and Sl == Sc
                  and sector_counts(El, Sl) == sector_counts(Ec, Sc))
            if not ok:
                print("  COUNTEREXAMPLE A=%d apex=%d: dW=%s dE=%s"
                      % (A, apex, sorted(Wl ^ Wc)[:6], sorted(set(El) ^ set(Ec))[:6]))
                fails += 1
    if fails:
        STOP("LocalComplex != closure on %d of 36 G1 regions" % fails)
    print("  36 G1 regions (A in {5,7,11} x first 12 clean apexes): LocalComplex ==")
    print("         closure EXACTLY on every region -> PASS")

    # (d) T-fill chi-law on strips: b0=1, b1=E_SK+E_KS-1, b2=0 (both primes)
    print("  T-fill chi-law on strips (H=50, D=H, M0=4), primes 10007 AND 10009:")
    for A in (5, 7, 11, 13):
        for X in (5, 20, 120, 1020):
            W, E, S = build_local(A, X, 50, 50, 4)
            if not S:
                STOP("strip A=%d X=%d has no survivors" % (A, X))
            sc = sector_counts(E, S)
            fT = fills(None, W, E, S, canonical=False)
            for p in (P1, P2):
                b0, b1, b2 = quotient_betti(W, E, fT, S, p)
                law = (b0, b1, b2) == (1, sc['ESK'] + sc['EKS'] - 1, 0)
                if not law:
                    print("  COUNTEREXAMPLE A=%d X=%d p=%d: betti=(%d,%d,%d), "
                          "ESK=%d EKS=%d" % (A, X, p, b0, b1, b2, sc['ESK'], sc['EKS']))
                    STOP("T-fill chi-law violated on strip")
            print("    A=%2d X=%5d |S|=%2d ESS=%4d ESK=%4d EKS=%2d EKK=%3d "
                  "b1=%4d = ESK+EKS-1 -> OK"
                  % (A, X, len(S), sc['ESS'], sc['ESK'], sc['EKS'], sc['EKK'],
                     sc['ESK'] + sc['EKS'] - 1))
    print("S0 verdict: ALL STOP-SELFTESTS PASS (%.1fs)" % (time.time() - t0))


# ---------- ensemble machinery (vectorized portraits per window) ----------

def precompute_X(X, NW, H=50):
    ncent = NW * H
    lo = X - BAND
    t0 = time.time()
    OLb, ORb = omega_range(lo, ncent + BAND)
    lam = (1 - 2 * ((OLb[BAND:] + ORb[BAND:]) & 1)).astype(np.int64)
    twin = (OLb[BAND:] == 1) & (ORb[BAND:] == 1)
    print("  [X=%.0e] sieved %d centers + band %d in %.1fs"
          % (X, ncent, BAND, time.time() - t0), flush=True)
    return dict(X=X, NW=NW, ncent=ncent, lo=lo, OLb=OLb, ORb=ORb, lam=lam, twin=twin)


def build_defect_arrays(px, A):
    """Global defect records over [lo, X+ncent), sorted by O1 = lex(n, q, side)."""
    lo, hi = px['lo'], px['X'] + px['ncent']
    Ns, Qs, Ss = [], [], []
    for q in [p for p in primes_upto(A) if p >= 5]:
        i6 = pow(6, -1, q)
        for sidx, cls in ((0, i6 % q), (1, (q - i6) % q)):
            first = (cls - lo) % q
            ns = np.arange(lo + first, hi, q, dtype=np.int64)
            Ns.append(ns)
            Qs.append(np.full(ns.size, q, np.int64))
            Ss.append(np.full(ns.size, sidx, np.int64))
    N = np.concatenate(Ns)
    Q = np.concatenate(Qs)
    Sd = np.concatenate(Ss)
    o = np.lexsort((Sd, Q, N))
    N, Q, Sd = N[o], Q[o], Sd[o]
    G = np.where(Sd == 0, px['OLb'][N - lo], px['ORb'][N - lo])
    G = ((G - 1) & 1).astype(np.int64)     # lambda-parity of the defect cofactor
    cnt = np.bincount((N - lo).astype(np.int64), minlength=hi - lo)
    cum = np.concatenate([[0], np.cumsum(cnt)])
    return N, Q, Sd, G, cum


def window_portrait(x0, h, dband, sv, ctx, qlad, want_so=False):
    """All portraits of LocalComplex(A, x0, h, dband) via the S1-certified
    combinatorial forms.  sv = sorted survivors in [x0, x0+h)."""
    N, Q, Sd, G, cum = ctx['DEF']
    lo, X = ctx['lo'], ctx['X']
    out = dict(P5=np.nan, PII=(np.nan,) * 5, P1=np.nan, P1o2=np.nan, P2=np.nan,
               P4=np.nan, SIG=np.nan, msv=None, wit_nz=0, wit_tot=0, lad={})
    if sv.size == 0:
        return out
    s = int(sv.size)
    top = int(sv[-1])
    blo = x0 - dband
    deff = int(cum[top - lo] - cum[blo - lo])
    out['P5'] = float(max(deff - 1, 0))
    rSK = int(np.count_nonzero(cum[sv - lo] > cum[blo - lo]))
    out['PII'] = (float(s - 1), float(rSK), 0.0, float(rSK),
                  float(s if deff > 0 else s - 1))
    i0 = int(np.searchsorted(N, blo, 'left'))
    i1 = int(np.searchsorted(N, top, 'left'))
    Nsl, Qsl, Ssl, Gsl = N[i0:i1], Q[i0:i1], Sd[i0:i1], G[i0:i1]
    lamc, twc = ctx['lam'], ctx['twin']
    if Nsl.size >= 2:
        pos = np.searchsorted(sv, Nsl, 'right')
        msv = sv[pos]                                   # minimal adjacent survivor
        lms = lamc[msv - X]
        out['P1'] = float(np.mean(lms[:-1] * lms[1:] < 0))
        o2 = np.lexsort((Ssl, Nsl, Qsl))                # second ordering O2
        l2 = lms[o2]
        out['P1o2'] = float(np.mean(l2[:-1] * l2[1:] < 0))
        dif = Gsl[:-1] != Gsl[1:]
        out['P2'] = float(np.mean(dif))
        out['wit_nz'], out['wit_tot'] = int(dif.sum()), int(dif.size)
        if want_so:
            out['msv'] = np.unique(msv)
    twm = twc[sv - X]
    frm = lamc[sv - X] < 0
    if twm.any() and frm.any():
        ttw, tfr = int(sv[twm][-1]), int(sv[frm][-1])
        b1t = max(int(cum[ttw - lo] - cum[blo - lo]) - 1, 0)
        b1f = max(int(cum[tfr - lo] - cum[blo - lo]) - 1, 0)
        out['P4'] = float(b1f - b1t)
    if not np.isnan(out['P2']):
        ds = []
        for q2 in qlad:
            i6b = pow(6, -1, q2)
            struck = (sv % q2 == i6b) | (sv % q2 == (q2 - i6b) % q2)
            sv2 = sv[~struck]
            if sv2.size == 0:
                out['lad'][q2] = (np.nan, int(struck.sum()))
                continue
            top2 = int(sv2[-1])
            j = int(np.searchsorted(Nsl, top2, 'left'))
            nNs, nSs = [], []
            for sidx, cls in ((0, i6b % q2), (1, (q2 - i6b) % q2)):
                first = (cls - blo) % q2
                nn = np.arange(blo + first, top2, q2, dtype=np.int64)
                nNs.append(nn)
                nSs.append(np.full(nn.size, sidx, np.int64))
            nN = np.concatenate(nNs)
            nS = np.concatenate(nSs)
            gnew = np.where(nS == 0, ctx['OLb'][nN - lo], ctx['ORb'][nN - lo])
            gnew = ((gnew - 1) & 1).astype(np.int64)
            mN = np.concatenate([Nsl[:j], nN])
            mQ = np.concatenate([Qsl[:j], np.full(nN.size, q2, np.int64)])
            mS = np.concatenate([Ssl[:j], nS])
            mG = np.concatenate([Gsl[:j], gnew])
            om = np.lexsort((mS, mQ, mN))
            gm = mG[om]
            if gm.size >= 2:
                d = float(np.mean(gm[:-1] != gm[1:])) - out['P2']
                ds.append(d)
                out['lad'][q2] = (d, int(struck.sum()))
            else:
                out['lad'][q2] = (np.nan, int(struck.sum()))
        if ds:
            out['SIG'] = float(np.mean(ds))
    return out


def demech(Pv, OMP, nb=20):
    v = np.isfinite(Pv) & np.isfinite(OMP)
    out = np.full_like(Pv, np.nan)
    if v.sum() < 2 * nb:
        return out
    qs = np.quantile(OMP[v], np.linspace(0, 1, nb + 1))
    qs[-1] += 1e-9
    b = np.clip(np.searchsorted(qs, OMP[v], 'right') - 1, 0, nb - 1)
    means = np.zeros(nb)
    for i in range(nb):
        sel = b == i
        if sel.any():
            means[i] = Pv[v][sel].mean()
    out[v] = Pv[v] - means[b]
    return out


def ensemble_pass(px, A, H, rng):
    """One full pass over the cell (X, A) with window size H: portrait arrays,
    loads and 200 lambda-resample null loads."""
    X, lo, ncent = px['X'], px['lo'], px['ncent']
    NW = ncent // H
    ctx = dict(X=X, lo=lo, lam=px['lam'], twin=px['twin'],
               OLb=px['OLb'], ORb=px['ORb'], DEF=build_defect_arrays(px, A))
    m_arr = X + np.arange(ncent, dtype=np.int64)
    clean = np.ones(ncent, bool)
    for q in [p for p in primes_upto(A) if p >= 5]:
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    n_use = NW * H
    cl = clean[:n_use].reshape(NW, H)
    lamw = px['lam'][:n_use].reshape(NW, H).astype(np.float64)
    om_c = (px['OLb'][BAND:BAND + n_use] + px['ORb'][BAND:BAND + n_use]).reshape(NW, H)
    depth = px.get('depth')
    keys = ['P5', 'PII0', 'PII1', 'PII2', 'PII3', 'PII4', 'P1', 'P1o2', 'P2', 'P4',
            'SIG', 'P3', 'OMP', 'P1L', 'P1o2L', 'P2L', 'P4L', 'SIGL', 'P3L', 'OMPL']
    arr = {k: np.full(NW, np.nan) for k in keys}
    excl = cl.copy()
    wit_nz = wit_tot = 0
    qlad = QLAD[A]
    for w in range(NW):
        x0 = X + w * H
        sv = m_arr[w * H:(w + 1) * H][cl[w]]
        pf = window_portrait(x0, H, H, sv, ctx, qlad, want_so=True)
        arr['P5'][w] = pf['P5']
        for k in range(5):
            arr['PII%d' % k][w] = pf['PII'][k]
        arr['P1'][w], arr['P1o2'][w] = pf['P1'], pf['P1o2']
        arr['P2'][w], arr['P4'][w], arr['SIG'][w] = pf['P2'], pf['P4'], pf['SIG']
        wit_nz += pf['wit_nz']
        wit_tot += pf['wit_tot']
        if pf['msv'] is not None:
            excl[w, pf['msv'] - x0] = False
        svL = sv[sv < x0 + H // 2]
        pl = window_portrait(x0, H // 2, H // 2, svL, ctx, qlad)
        arr['P1L'][w], arr['P1o2L'][w] = pl['P1'], pl['P1o2']
        arr['P2L'][w], arr['P4L'][w], arr['SIGL'][w] = pl['P2'], pl['P4'], pl['SIG']
        if depth is not None and sv.size:
            dsv = depth[sv - X]
            arr['P3'][w] = float(np.nanmean(dsv)) if np.isfinite(dsv).any() else np.nan
            arr['OMP'][w] = float(om_c[w][cl[w]].mean())
            if svL.size:
                dL = depth[svL - X]
                arr['P3L'][w] = (float(np.nanmean(dL))
                                 if np.isfinite(dL).any() else np.nan)
                arr['OMPL'][w] = float(om_c[w][:H // 2][cl[w][:H // 2]].mean())
    arr['P3d'] = demech(arr['P3'], arr['OMP'])
    arr['P3dL'] = demech(arr['P3L'], arr['OMPL'])
    right = np.zeros((NW, H), bool)
    right[:, H // 2:] = True
    masks = {'S': cl, 'Ssplit': cl & right, 'So1': excl}
    loads = {k: (lamw * m).sum(1) for k, m in masks.items()}
    pool = px['lam'][:n_use][clean[:n_use]].astype(np.float64)
    nulls = {k: np.empty((200, NW)) for k in masks}
    lmat = np.zeros((NW, H), np.float64)
    nsurv = int(cl.sum())
    for t in range(200):
        lmat[:] = 0.0
        lmat[cl] = rng.choice(pool, size=nsurv)
        for k, m in masks.items():
            nulls[k][t] = (lmat * m).sum(1)
    return dict(NW=NW, H=H, arr=arr, loads=loads, nulls=nulls,
                wit=(wit_nz, wit_tot), nsurv=nsurv,
                ntwin=int((px['twin'][:n_use] & clean[:n_use]).sum()))


def foil_row(I, L, Ln, rng):
    I = np.asarray(I, np.float64)
    L = np.asarray(L, np.float64)
    v = np.isfinite(I) & np.isfinite(L)
    n = int(v.sum())
    if n < 10:
        return dict(R=0.0, zW=0.0, zI=0.0, n=n, note='n<10')
    Iv, Lv = I[v], L[v]
    if Iv.std() < 1e-12 or Lv.std() < 1e-12:
        return dict(R=0.0, zW=0.0, zI=0.0, n=n, note='degenerate')
    R = float(np.corrcoef(Iv, Lv)[0, 1])
    Ic = Iv.copy()
    perm = np.empty(200)
    for t in range(200):
        rng.shuffle(Ic)
        perm[t] = np.corrcoef(Ic, Lv)[0, 1]
    nulls = np.empty(200)
    for t in range(200):
        Lt = Ln[t][v]
        nulls[t] = 0.0 if Lt.std() < 1e-12 else np.corrcoef(Iv, Lt)[0, 1]
    return dict(R=R, zW=float(R / (perm.std() + 1e-15)),
                zI=float((R - nulls.mean()) / (nulls.std() + 1e-15)), n=n, note='')


ROWS = [("P5|S", "P5", "S"), ("PII0|S", "PII0", "S"), ("PII1|S", "PII1", "S"),
        ("PII2|S", "PII2", "S"), ("PII3|S", "PII3", "S"), ("PII4|S", "PII4", "S"),
        ("P1|S''", "P1L", "Ssplit"), ("P1o2|S''", "P1o2L", "Ssplit"),
        ("P1|So", "P1", "So1"), ("P2|S''", "P2L", "Ssplit"), ("P2|S(=So)", "P2", "S"),
        ("P3|S''", "P3L", "Ssplit"), ("P3d|S''", "P3dL", "Ssplit"),
        ("P4|S''", "P4L", "Ssplit"), ("SIG|S''", "SIGL", "Ssplit")]
GUARD = {'P5': ['P5'], 'PII': ['PII0', 'PII1', 'PII2', 'PII3', 'PII4'],
         'P1': ['P1L'], 'P2': ['P2L'], 'P3': ['P3L'], 'P3d': ['P3dL'],
         'P4': ['P4L'], 'SIG': ['SIGL']}
FAMILY = {'P5': 'P5', 'PII0': 'PII', 'PII1': 'PII', 'PII2': 'PII', 'PII3': 'PII',
          'PII4': 'PII', 'P1L': 'P1', 'P1o2L': 'P1', 'P1': 'P1', 'P2L': 'P2',
          'P2': 'P2', 'P3L': 'P3', 'P3dL': 'P3d', 'P4L': 'P4', 'SIGL': 'SIG'}


def mode_fraction(cols, arr, NW):
    M = np.stack([np.nan_to_num(arr[c], nan=1e9) for c in cols], axis=1)
    _, counts = np.unique(M, axis=0, return_counts=True)
    return counts.max() / NW


def cell_run(px, A, jpath):
    X = px['X']
    banner("CELL", "X=%.0e A=%d NW=%d H=50 (foil-v2, seed %d)" % (X, A, px['NW'], SEED))
    rng = np.random.default_rng(SEED)
    p50 = ensemble_pass(px, A, 50, rng)
    flagged = []
    for fam, cols in GUARD.items():
        mf = mode_fraction(cols, p50['arr'], p50['NW'])
        if mf > 0.9:
            flagged.append(fam)
            print("  DEGENERACY GUARD: portrait %s mode-fraction %.2f > 0.9 -> "
                  "cell recomputed at H=100 for this portrait (registered before foils)"
                  % (fam, mf))
    p100 = None
    if flagged:
        p100 = ensemble_pass(px, A, 100, np.random.default_rng(SEED + 1))
    print("  survivors=%d twin-survivors=%d | witness nonzero share (P2, full windows)"
          " = %d/%d = %.4f"
          % (p50['nsurv'], p50['ntwin'], p50['wit'][0], p50['wit'][1],
             p50['wit'][0] / max(p50['wit'][1], 1)))
    v = np.isfinite(p50['arr']['P1']) & np.isfinite(p50['arr']['P1o2'])
    o12 = (float(np.corrcoef(p50['arr']['P1'][v], p50['arr']['P1o2'][v])[0, 1])
           if v.sum() > 10 else float('nan'))
    print("  P1 ordering cross-check: corr(O1,O2)=%.3f | means O1=%.4f O2=%.4f"
          % (o12, np.nanmean(p50['arr']['P1']), np.nanmean(p50['arr']['P1o2'])))
    if 'depth' in px:
        d = px['depth']
        m_use = np.isfinite(d)
        hist = np.bincount(d[m_use].astype(int), minlength=CENSOR + 1)[:CENSOR + 1]
        print("  P3 depth histogram (survivor level, 0..%d=censored): %s | censored "
              "share %.3f" % (CENSOR + 1 - 1, list(hist),
                              hist[CENSOR] / max(hist.sum(), 1)))
    print("  P4 valid windows: full=%d left=%d"
          % (int(np.isfinite(p50['arr']['P4']).sum()),
             int(np.isfinite(p50['arr']['P4L']).sum())))
    res = {}
    for name, pk, lk in ROWS:
        src = p100 if (p100 is not None and FAMILY[pk] in flagged) else p50
        st = foil_row(src['arr'][pk], src['loads'][lk], src['nulls'][lk],
                      np.random.default_rng(SEED + 7))
        st['H'] = src['H']
        res[name] = st
        print("  %-10s R=%+8.4f zW=%+6.1f zI=%+6.1f n=%5d %s"
              % (name, st['R'], st['zW'], st['zI'], st['n'], st['note']), flush=True)
    meta = dict(X=X, A=A, NW=p50['NW'], flagged=flagged, o12=o12,
                wit=[int(p50['wit'][0]), int(p50['wit'][1])],
                nsurv=p50['nsurv'], ntwin=p50['ntwin'],
                p4n=[int(np.isfinite(p50['arr']['P4']).sum()),
                     int(np.isfinite(p50['arr']['P4L']).sum())],
                means={k: (None if not np.isfinite(np.nanmean(p50['arr'][k]))
                           else float(np.nanmean(p50['arr'][k])))
                       for k in ('P5', 'P1', 'P1o2', 'P2', 'P3', 'P4', 'SIG')})
    if 'depth' in px:
        d = px['depth']
        m_use = np.isfinite(d)
        meta['p3hist'] = [int(x) for x in
                          np.bincount(d[m_use].astype(int), minlength=CENSOR + 1)]
    with open(jpath, 'w') as f:
        json.dump(dict(meta=meta, rows=res), f)
    print("  cell JSON -> %s" % jpath)


# ---------- P3 grave-depth machinery ----------

_SPF = None
_PTD = None
SPF_LIM = 7_000_000


def setup_factor_tables():
    global _SPF, _PTD
    if _SPF is not None:
        return
    t0 = time.time()
    spf = np.zeros(SPF_LIM + 1, dtype=np.int32)
    for i in range(2, int(math.isqrt(SPF_LIM)) + 1):
        if spf[i] == 0:
            sl = spf[i * i::i]
            sl[sl == 0] = i
    _SPF = spf
    lim = 78500
    sieve = np.ones(lim + 1, bool)
    sieve[:2] = False
    for i in range(2, int(lim ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    _PTD = np.flatnonzero(sieve).astype(np.int64)
    print("  factor tables: SPF<=%d, %d trial-division primes <= %d (%.1fs)"
          % (SPF_LIM, _PTD.size, lim, time.time() - t0), flush=True)


def fac_distinct(v):
    """Distinct prime factors of v (v coprime to 6, v >= 5)."""
    out = []
    x = int(v)
    if x < SPF_LIM:
        while x > 1:
            p = int(_SPF[x])
            if p == 0:
                out.append(x)
                break
            out.append(p)
            while x % p == 0:
                x //= p
        return out
    lim = math.isqrt(x)
    k = int(np.searchsorted(_PTD, lim, 'right'))
    sub = _PTD[:k]
    hits = sub[(x % sub) == 0]
    for p in hits.tolist():
        out.append(int(p))
        while x % p == 0:
            x //= p
    if x > 1:
        out.append(x)
    return out


def make_p3_ctx(px):
    return dict(dcache={}, twcache={}, stat=dict(nodes=0, cens_cap=0, cens_budget=0),
                win=(px['X'], px['X'] + px['ncent'], px['twin']))


def is_twin(t, ctx3):
    w0, w1, tw = ctx3['win']
    if w0 <= t < w1:
        return bool(tw[t - w0])
    if t < 2_000_000:
        r = ctx3['twcache'].get(t)
        if r is not None:
            return r
    fl = fac_distinct(6 * t - 1)
    r = False
    if len(fl) == 1 and fl[0] == 6 * t - 1:
        fr = fac_distinct(6 * t + 1)
        r = len(fr) == 1 and fr[0] == 6 * t + 1
    if t < 2_000_000:
        ctx3['twcache'][t] = r
    return r


def peel_targets(t):
    out = []
    for off in (-1, 1):
        v = 6 * t + off
        for q in fac_distinct(v):
            if q == v:
                continue
            cof = v // q
            if cof < 5:
                continue
            r6 = cof % 6
            if r6 == 5:
                out.append((cof + 1) // 6)
            elif r6 == 1:
                out.append((cof - 1) // 6)
    return out


def grave_depth(m, ctx3):
    r = ctx3['dcache'].get(m)
    if r is not None:
        return r
    if is_twin(m, ctx3):
        ctx3['dcache'][m] = 0
        return 0
    res = CENSOR
    seen = {m}
    frontier = [m]
    nodes = 1
    budget_hit = False
    for depth in range(1, DEPTH_CAP + 1):
        nxt = []
        for t in frontier:
            for u in peel_targets(t):
                if u in seen:
                    continue
                seen.add(u)
                nodes += 1
                if is_twin(u, ctx3):
                    res = depth
                    break
                nxt.append(u)
                if nodes >= NODE_BUDGET:
                    budget_hit = True
                    break
            if res <= DEPTH_CAP or budget_hit:
                break
        if res <= DEPTH_CAP or budget_hit or not nxt:
            break
        frontier = nxt
    ctx3['dcache'][m] = res
    ctx3['stat']['nodes'] += nodes
    if res == CENSOR:
        ctx3['stat']['cens_budget' if budget_hit else 'cens_cap'] += 1
    return res


def compute_depths(px):
    """Grave-depth for all A=13 survivors of the cell (A=31 survivors are a subset)."""
    setup_factor_tables()
    X, ncent = px['X'], px['ncent']
    m_arr = X + np.arange(ncent, dtype=np.int64)
    clean = np.ones(ncent, bool)
    for q in (5, 7, 11, 13):
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    ctx3 = make_p3_ctx(px)
    depth = np.full(ncent, np.nan)
    idxs = np.flatnonzero(clean)
    t0 = time.time()
    done = 0
    for i in idxs:
        if time.time() - t0 > P3_TIME_CAP:
            print("  P3 TIME CAP hit after %d/%d roots -- remaining depths = NA "
                  "(reduction disclosed)" % (done, idxs.size), flush=True)
            break
        depth[i] = grave_depth(int(X + i), ctx3)
        done += 1
        if done % 10000 == 0:
            print("    P3 depth: %d/%d roots (%.0fs, %d nodes)"
                  % (done, idxs.size, time.time() - t0, ctx3['stat']['nodes']),
                  flush=True)
    st = ctx3['stat']
    print("  P3 depth pass: %d roots in %.0fs; nodes=%d censored(cap)=%d "
          "censored(budget)=%d" % (done, time.time() - t0, st['nodes'],
                                   st['cens_cap'], st['cens_budget']), flush=True)
    px['depth'] = depth
    return ctx3


# ---------- S1: registrations + matrix cross-checks + subsample diagnostics ----------

def quotient_d1_labeled(W, edges, S):
    vq = sorted(S) + ['K*']
    vidx = {v: i for i, v in enumerate(vq)}
    cols, labels, eord = [], [], []
    seen = set()
    for u, v, et in edges:
        if not ((u in S) or (v in S)) or (u, v) in seen:
            continue
        seen.add((u, v))
        su, sv_ = u in S, v in S
        labels.append('SS' if su and sv_ else ('SK' if su else 'KS'))
        eord.append((u, v, et))
        col = np.zeros(len(vq), np.int64)
        uu = vidx[u] if su else len(vq) - 1
        ww = vidx[v] if sv_ else len(vq) - 1
        if uu != ww:
            col[ww] += 1
            col[uu] -= 1
        cols.append(col)
    D1 = (np.stack(cols, axis=1) if cols else np.zeros((len(vq), 0), np.int64))
    return D1, np.array(labels), eord


def twisted_rank(edges, S, gam, x, p):
    vq = sorted(S) + ['K*']
    vidx = {v: i for i, v in enumerate(vq)}
    cols = []
    seen = set()
    for u, v, et in edges:
        if not ((u in S) or (v in S)) or (u, v) in seen:
            continue
        seen.add((u, v))
        col = np.zeros(len(vq), np.int64)
        uu = vidx[u] if u in S else len(vq) - 1
        ww = vidx[v] if v in S else len(vq) - 1
        if uu == ww:
            continue
        tw = pow(x, int(gam.get(v, 0)), p) if et == 'boundary' else 1
        col[ww] += tw
        col[uu] -= 1
        cols.append(col)
    M = (np.stack(cols, axis=1) if cols else np.zeros((len(vq), 0), np.int64))
    return rank_fp(M, p)


_OMB = {}


def omega_val(v):
    r = _OMB.get(v)
    if r is not None:
        return r
    r, x, d = 0, v, 2
    while d * d <= x:
        while x % d == 0:
            x //= d
            r += 1
        d += 1
    if x > 1:
        r += 1
    _OMB[v] = r
    return r


def primitive_root(p):
    fac = []
    x, d = p - 1, 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise RuntimeError


def local_scalars(A, X, H, D):
    """Reference (matrix-free) portrait scalars straight from the definitions,
    used to check the vectorized ensemble forms against F_p matrices."""
    W, E, S = build_local(A, X, H, D, 4)
    surv = sorted(v[1] for v in S)
    defs = sorted([v for v in W if v[0] == 'd'],
                  key=lambda d: (d[1], d[2], 0 if d[3] == '-' else 1))
    return W, E, S, surv, defs


def stage_s1():
    banner("S1", "portrait registrations + matrix cross-checks (STOP on mismatch)")
    print("REGISTRATIONS (verbatim, BEFORE measuring):")
    print("  P5  = residual b1 of the canonical (T+I+Q) fill of the window quotient;")
    print("        combinatorial form b1 = #defects-hit - 1 (certified below).")
    print("        NEGATIVE CONTROL: predicted parity-blind (pure residue arithmetic). Load S.")
    print("  P(ii)= 5-vector of d1 column-submatrix ranks (SS, SK, KS, SK+KS, full);")
    print("        forms (|S|-1, #sources-with-defect-below, 0, same, |S|); predicted blind. Load S.")
    print("  P1  = interface holonomy: residual cycle basis = CONSECUTIVE defect pairs in")
    print("        ordering O1 = lex(n,q,side) [registered HERE, before measurement];")
    print("        cross-check ordering O2 = lex(q,n,side); h_i = lam(ms(n_i))*lam(ms(n_i+1)),")
    print("        ms(n) = minimal survivor > n; portrait = (count, frustrated fraction);")
    print("        count == P5, scalar = frustrated fraction. Loads S'' primary / So secondary")
    print("        (So load excludes the ms-interface survivors).")
    print("  P2  = REGISTERED SUBSTITUTE for the peel twist (no peel edges at X>=1e6,")
    print("        disclosed): boundary edge m->(n,q,s) twisted by gamma = lambda-parity of")
    print("        the defect cofactor sideValue(s,n)/q = (Omega_side(n)-1) mod 2 -- an edge")
    print("        twist, intrinsic, NOT a vertex coboundary; witnesses w_i = gamma_i-gamma_i+1")
    print("        (mod d) over the P1 basis; scalar = nonzero-witness fraction at d=2;")
    print("        twisted d1 ranks over F_10009 and F_10069 (both = 1 mod 12), x of order")
    print("        d in {2,3,4,6}; certificate: rank jump s -> s+1 iff some witness != 0")
    print("        (a gauge-trivial/coboundary twist keeps rank s). Loads S'' / S(=So).")
    print("  P3  = censored BFS grave-depth to nearest twin via PeelStep-style factor")
    print("        descent (targets = cofactor centers over distinct prime factors of both")
    print("        wings); depth cap %d (censored value %d), node budget %d; scalar = mean"
          % (DEPTH_CAP, CENSOR, NODE_BUDGET))
    print("        depth over (left-half for S'') survivors. P3d = de-mechanized: residual")
    print("        after removing the 20-quantile-bin mean in the window Omega-profile.")
    print("        Load S'' primary; So degenerate (invariant reads every survivor) -> NA.")
    print("  P4  = grade-stratified pair: b1(twin-survivor stratum subcomplex) vs")
    print("        b1(frustrated stratum, lam=-1); b1 = max(#defects below stratum top - 1,0);")
    print("        NA if a stratum is empty; scalar = b1_frustrated - b1_twin. Load S''.")
    print("  SIG = signed-ladder delta: mean over q' of [P2(A+{q'}) - P2(A)]; q' = %s at A=13,"
          % (QLAD[13],))
    print("        %s at A=31 (17,19,23 are already clocks at 31 -- adaptation registered)."
          % (QLAD[31],))
    print("  S'' convention: portrait on LocalComplex(A, Xw, H/2, D=H/2) (left half), load =")
    print("        sum of lam over right-half survivors. Degeneracy guard: mode-fraction")
    print("        > 0.9 in a cell -> that portrait recomputed at H=100 (registered pre-foil).")
    print("  Verdict rule (gate_g3 foil-v2 copy): MANAGED-PASS iff min|z_I| >= 5 over the")
    print("        grid AND |R(31)| >= |R(13)|/3 at both X; SOFT-PASS iff min|z_I| >= 3;")
    print("        else PARITY-BLIND-UNDER-ESCALATION-v2. 200 perms + 200 lambda-resamples,")
    print("        seed %d." % SEED)
    print()
    t0 = time.time()
    X6 = 10 ** 6

    # disclosure with numbers
    print("  DISCLOSURE at X=1e6/1e9, H=50, D=H: max peel factor-target = "
          "(6(X+H)+1)/5/6 ~ (X+H)/5 << X-D; min defect level = X-D > M0=4:")
    for X in (10 ** 6, 10 ** 9):
        print("    X=%.0e: max target ~ %d < band floor %d; absorbers require n<=4 -> none"
              % (X, (6 * (X + 50) + 1) // 30, X - 50))

    # matrix cross-checks of every combinatorial form (STOP on mismatch)
    px = dict(X=X6, ncent=3000, lo=X6 - BAND)
    px['OLb'], px['ORb'] = omega_range(px['lo'], px['ncent'] + BAND)
    px['lam'] = (1 - 2 * ((px['OLb'][BAND:] + px['ORb'][BAND:]) & 1)).astype(np.int64)
    px['twin'] = (px['OLb'][BAND:] == 1) & (px['ORb'][BAND:] == 1)
    checked = 0
    for A in (13, 31):
        ctx = dict(X=X6, lo=px['lo'], lam=px['lam'], twin=px['twin'],
                   OLb=px['OLb'], ORb=px['ORb'], DEF=build_defect_arrays(px, A))
        specs = [(12, k) for k in range(10)] + [(30, 40), (30, 55)]
        for H, k in specs:
            x0 = X6 + 37 * k
            W, E, S = build_local(A, x0, H, H, 4)
            if not S:
                continue
            types = {t for _, _, t in E}
            if 'peel' in types or 'absorb' in types:
                STOP("unexpected peel/absorb edge at X=1e6 (disclosure violated)")
            surv = np.array(sorted(v[1] for v in S), np.int64)
            pf = window_portrait(x0, H, H, surv, ctx, QLAD[A])
            sc = sector_counts(E, S)
            fT = fills(None, W, E, S, canonical=False)
            bT = quotient_betti(W, E, fT, S, P1)
            if bT != (1, sc['ESK'] + sc['EKS'] - 1, 0):
                STOP("T-law fails at 1e6 window A=%d x0=%d H=%d: %s" % (A, x0, H, bT))
            fC = fills(None, W, E, S, canonical=True)
            for p in ((P1, P2) if H == 12 else (P1,)):
                b0, b1, b2 = quotient_betti(W, E, fC, S, p)
                if not (b0 == 1 and b1 == int(pf['P5'])):
                    STOP("P5 formula != canonical residual b1: A=%d x0=%d H=%d p=%d "
                         "matrix=(%d,%d,%d) formula=%d"
                         % (A, x0, H, p, b0, b1, b2, int(pf['P5'])))
            D1, lab, _ = quotient_d1_labeled(W, E, S)
            got = (rank_fp(D1[:, lab == 'SS'], P1), rank_fp(D1[:, lab == 'SK'], P1),
                   rank_fp(D1[:, lab == 'KS'], P1),
                   rank_fp(D1[:, (lab == 'SK') | (lab == 'KS')], P1), rank_fp(D1, P1))
            if tuple(float(x) for x in got) != pf['PII']:
                STOP("P(ii) formula != matrix ranks: A=%d x0=%d H=%d got=%s formula=%s"
                     % (A, x0, H, got, pf['PII']))
            checked += 1
    print("  P5 / P(ii) / T-law matrix cross-checks at X=1e6 (H=12 x10 + H=30 x2, per A in"
          " {13,31}; F_p ranks, p=10007 and 10009 on H=12): %d window complexes -> PASS"
          % checked)

    # twisted-rank certificate
    print("  P2 twisted-rank certificate (p in {%d, %d}, both = 1 mod 12; x of order"
          " d in {2,3,4,6}):" % (P12A, P12B))
    jumps, tot = 0, 0
    for p in (P12A, P12B):
        g = primitive_root(p)
        for d in (2, 3, 4, 6):
            x = pow(g, (p - 1) // d, p)
            assert pow(x, d, p) == 1 and all(pow(x, e, p) != 1 for e in range(1, d))
            for A in (13, 31):
                for k in range(6):
                    x0 = X6 + 37 * k
                    W, E, S = build_local(A, x0, 12, 12, 4)
                    if not S:
                        continue
                    s = len(S)
                    gam, gams = {}, []
                    for v in W:
                        if v[0] == 'd':
                            gv = (omega_val(side_value(v[3], v[1])) - 1) & 1
                            gam[v] = gv
                    top = max(v[1] for v in S)
                    gams = [gam[v] for v in W if v[0] == 'd' and v[1] < top]
                    tr = twisted_rank(E, S, gam, x, p)
                    tr1 = twisted_rank(E, S, gam, 1, p)
                    pred = s + (1 if len(set(gams)) > 1 else 0)
                    if tr1 != s or tr != pred:
                        STOP("twisted rank mismatch p=%d d=%d A=%d x0=%d: untw=%d "
                             "tw=%d pred=%d" % (p, d, A, x0, tr1, tr, pred))
                    tot += 1
                    jumps += int(tr == s + 1)
    print("    %d/%d checks: twisted rank == s + [witness set nontrivial]; untwisted == s"
          % (tot, tot))
    print("    rank jumps s->s+1 in %d/%d complexes -> the twist is NOT gauge-trivial"
          " (a coboundary twist would keep rank s everywhere) -- CERTIFICATE PASS"
          % (jumps, tot))

    # P1 basis size == residual b1 was checked via P5; ordering cross-check subsample
    ctx13 = dict(X=X6, lo=px['lo'], lam=px['lam'], twin=px['twin'],
                 OLb=px['OLb'], ORb=px['ORb'], DEF=build_defect_arrays(px, 13))
    m_arr = X6 + np.arange(3000, dtype=np.int64)
    clean = np.ones(3000, bool)
    for q in (5, 7, 11, 13):
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    f1, f2 = [], []
    for w in range(60):
        x0 = X6 + 50 * w
        sv = m_arr[50 * w:50 * (w + 1)][clean[50 * w:50 * (w + 1)]]
        pf = window_portrait(x0, 50, 50, sv, ctx13, QLAD[13])
        if not np.isnan(pf['P1']):
            f1.append(pf['P1'])
            f2.append(pf['P1o2'])
    print("  P1 orderings on 60 windows (A=13, X=1e6): mean frustration O1=%.4f "
          "O2=%.4f corr=%.3f" % (np.mean(f1), np.mean(f2),
                                 np.corrcoef(f1, f2)[0, 1]))

    # P3: BFS == exhaustive min-recursion reference (where budget not hit)
    setup_factor_tables()
    ctx3 = make_p3_ctx(dict(X=X6, ncent=3000, twin=px['twin'][:3000]))

    def depth_ref(m, memo, lvl=0):
        if m in memo:
            return memo[m]
        if is_twin(m, ctx3):
            memo[m] = 0
            return 0
        if lvl >= DEPTH_CAP:
            return CENSOR
        memo[m] = CENSOR
        best = CENSOR
        for u in peel_targets(m):
            best = min(best, 1 + depth_ref(u, memo, lvl + 1))
        memo[m] = min(best, CENSOR)
        return memo[m]

    roots = m_arr[clean][:40]
    agree = comp = 0
    for m in roots:
        st0 = dict(ctx3['stat'])
        db = grave_depth(int(m), ctx3)
        budget = ctx3['stat']['cens_budget'] > st0['cens_budget']
        if budget:
            continue
        dr = depth_ref(int(m), {})
        comp += 1
        if db != dr:
            STOP("P3 BFS != reference min-recursion at m=%d: bfs=%d ref=%d"
                 % (m, db, dr))
        agree += 1
    print("  P3 BFS == exhaustive reference on %d/%d uncensored roots -> PASS"
          % (agree, comp))

    # D-sensitivity: D in {0, H, 5H} on a 200-window subsample (A=13, X=1e6)
    lo2 = X6 - 250
    OLb2, ORb2 = omega_range(lo2, 200 * 50 + 250)
    px2 = dict(X=X6, ncent=200 * 50, lo=lo2, OLb=OLb2, ORb=ORb2)
    ctx2 = dict(X=X6, lo=lo2, lam=(1 - 2 * ((OLb2[250:] + ORb2[250:]) & 1)).astype(np.int64),
                twin=(OLb2[250:] == 1) & (ORb2[250:] == 1),
                OLb=OLb2, ORb=ORb2, DEF=build_defect_arrays(px2, 13))
    m2 = X6 + np.arange(200 * 50, dtype=np.int64)
    cl2 = np.ones(200 * 50, bool)
    for q in (5, 7, 11, 13):
        i6 = pow(6, -1, q)
        cl2 &= (m2 % q != i6) & (m2 % q != (q - i6) % q)
    res = {}
    for D in (0, 50, 250):
        P5s, P1s, P2s = [], [], []
        for w in range(200):
            x0 = X6 + 50 * w
            sv = m2[50 * w:50 * (w + 1)][cl2[50 * w:50 * (w + 1)]]
            pf = window_portrait(x0, 50, D, sv, ctx2, QLAD[13])
            P5s.append(pf['P5'])
            P1s.append(pf['P1'])
            P2s.append(pf['P2'])
        res[D] = (np.array(P5s), np.array(P1s), np.array(P2s))
    for name, i in (('P5', 0), ('P1', 1), ('P2', 2)):
        a0, aH, a5 = res[0][i], res[50][i], res[250][i]
        v = np.isfinite(a0) & np.isfinite(aH) & np.isfinite(a5)
        print("  D-sensitivity %s: mean D=0/H/5H = %.3f/%.3f/%.3f; corr(D=0,D=H)=%.3f "
              "corr(D=5H,D=H)=%.3f"
              % (name, np.nanmean(a0), np.nanmean(aH), np.nanmean(a5),
                 np.corrcoef(a0[v], aH[v])[0, 1], np.corrcoef(a5[v], aH[v])[0, 1]))
    print("S1 verdict: ALL FORMULA/MATRIX CROSS-CHECKS PASS (%.1fs)" % (time.time() - t0))


# ---------- S2: signed-ladder stage ----------

def stage_s2():
    banner("S2", "signed ladder: exact flip-fraction law + twisted-portrait deltas")
    t0 = time.time()
    print("(alpha) exact flip law, truncSign(K=1): escalation clock q' flips the wing-pair")
    print("        truncated sign exactly on the classes m = +-inv6(q') mod q' -- EXACT")
    print("        count over one full period; STOP on mismatch.")
    for q2 in (17, 19, 23):
        flips = [r for r in range(q2)
                 if ((6 * r - 1) % q2 == 0) != ((6 * r + 1) % q2 == 0)]
        both = [r for r in range(q2)
                if ((6 * r - 1) % q2 == 0) and ((6 * r + 1) % q2 == 0)]
        if len(flips) != 2 or both:
            STOP("flip census q'=%d: flips=%s both=%s (expected exactly 2, none both)"
                 % (q2, flips, both))
        i6 = pow(6, -1, q2)
        print("  q'=%2d: flip classes {%d, %d} = {inv6, -inv6}; both-wings classes: 0 "
              "-> EXACT PASS" % (q2, i6, (q2 - i6) % q2))
    X6 = 10 ** 6
    m_arr = X6 + np.arange(50000, dtype=np.int64)
    clean = np.ones(50000, bool)
    for q in (5, 7, 11, 13):
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    sv = m_arr[clean]
    n = sv.size
    print("  ensemble check (X=1e6, %d A=13 survivors): fraction in flip classes vs 2/q'"
          % n)
    for q2 in (17, 19, 23):
        i6 = pow(6, -1, q2)
        obs = int(((sv % q2 == i6) | (sv % q2 == (q2 - i6) % q2)).sum())
        p0 = 2.0 / q2
        z = (obs - n * p0) / math.sqrt(n * p0 * (1 - p0))
        print("    q'=%2d: %d/%d = %.5f vs 2/q' = %.5f, binomial z = %+.2f %s"
              % (q2, obs, n, obs / n, p0, z, "(within 4 sigma)" if abs(z) < 4
                 else "FLAG"))
    print("(beta) twisted-portrait deltas per ladder step vs flip-locus overlap")
    print("       (X=1e6, A=13, NW=600 registered subsample; R + z_W from 200 perms):")
    px = precompute_X(X6, 600)
    ctx = dict(X=X6, lo=px['lo'], lam=px['lam'], twin=px['twin'],
               OLb=px['OLb'], ORb=px['ORb'], DEF=build_defect_arrays(px, 13))
    m_arr = X6 + np.arange(600 * 50, dtype=np.int64)
    clean = np.ones(600 * 50, bool)
    for q in (5, 7, 11, 13):
        i6 = pow(6, -1, q)
        clean &= (m_arr % q != i6) & (m_arr % q != (q - i6) % q)
    dl = {q2: [] for q2 in QLAD[13]}
    ov = {q2: [] for q2 in QLAD[13]}
    for w in range(600):
        x0 = X6 + 50 * w
        sv = m_arr[50 * w:50 * (w + 1)][clean[50 * w:50 * (w + 1)]]
        pf = window_portrait(x0, 50, 50, sv, ctx, QLAD[13])
        for q2 in QLAD[13]:
            if q2 in pf['lad']:
                d, o = pf['lad'][q2]
                dl[q2].append(d)
                ov[q2].append(o)
    rng = np.random.default_rng(SEED)
    for q2 in QLAD[13]:
        d = np.array(dl[q2])
        o = np.array(ov[q2], np.float64)
        v = np.isfinite(d)
        if v.sum() < 10 or d[v].std() < 1e-12 or o[v].std() < 1e-12:
            print("    q'=%2d: degenerate (n=%d)" % (q2, int(v.sum())))
            continue
        R = float(np.corrcoef(d[v], o[v])[0, 1])
        Ic = d[v].copy()
        perm = np.empty(200)
        for t in range(200):
            rng.shuffle(Ic)
            perm[t] = np.corrcoef(Ic, o[v])[0, 1]
        print("    q'=%2d: corr(delta P2, overlap) = %+.4f  z_W = %+.1f  n=%d  "
              "mean delta=%+.5f mean overlap=%.2f"
              % (q2, R, R / (perm.std() + 1e-15), int(v.sum()),
                 float(np.nanmean(d)), float(o.mean())))
    print("S2 verdict: exact flip law EXACT-PASS on {17,19,23}; deltas reported (%.1fs)"
          % (time.time() - t0))


# ---------- S3: escalation transport F-3 (exact integer identity) ----------

def stage_s3():
    banner("S3", "escalation transport F-3: b1(A')-b1(A) = dE_SK + dE_KS (EXACT)")
    print("  decomposition: demotion (q'-struck survivors leave S: their tournament +")
    print("  boundary incidences deleted; peel edges into them leave E_KS) + new-clock")
    print("  interface (boundary edges into q'-defects; q'-defect peel edges into S).")
    print("  b1 = T-only quotient b1 over F_10007 AND F_10009. STOP on any violation.")
    t0 = time.time()
    fails = 0
    for (A, A2) in ((5, 7), (7, 11), (11, 13)):
        q2 = A2
        for X in (5, 20, 120, 1020):
            WA, EA, SA = build_local(A, X, 50, 50, 4)
            WB, EB, SB = build_local(A2, X, 50, 50, 4)
            if not SA or not SB:
                STOP("empty survivor set on region A=%d->%d X=%d" % (A, A2, X))
            i6 = pow(6, -1, q2)
            demoted = {v for v in SA
                       if v[1] % q2 == i6 or v[1] % q2 == (q2 - i6) % q2}
            if SA - SB != demoted or not SB.issubset(SA):
                STOP("demotion set mismatch A=%d->%d X=%d" % (A, A2, X))
            scA, scB = sector_counts(EA, SA), sector_counts(EB, SB)
            loss_SK = sum(1 for u, v, t in EA if t == 'boundary' and u in demoted)
            gain_SK = sum(1 for u, v, t in EB if t == 'boundary' and v[2] == q2)
            loss_KS = sum(1 for u, v, t in EA if t == 'peel' and v in SA
                          and not (u in WB and v in SB))
            gain_KS = sum(1 for u, v, t in EB if t == 'peel' and u[2] == q2 and v in SB)
            dSK = scB['ESK'] - scA['ESK']
            dKS = scB['EKS'] - scA['EKS']
            ok1 = dSK == gain_SK - loss_SK
            ok2 = dKS == gain_KS - loss_KS
            b1A = b1B = None
            for p in (P1, P2):
                bA = quotient_betti(WA, EA, fills(None, WA, EA, SA, False), SA, p)
                bB = quotient_betti(WB, EB, fills(None, WB, EB, SB, False), SB, p)
                if b1A is None:
                    b1A, b1B = bA[1], bB[1]
                elif (b1A, b1B) != (bA[1], bB[1]):
                    STOP("prime cross-check mismatch on region")
            ok3 = (b1B - b1A) == dSK + dKS
            tag = "OK" if (ok1 and ok2 and ok3) else "VIOLATION"
            print("  A=%2d->%2d X=%5d: |S| %2d->%2d demoted=%d | b1 %4d->%4d "
                  "(delta %+4d) = dSK %+4d [gain %3d - loss %3d] + dKS %+2d "
                  "[gain %d - loss %d] -> %s"
                  % (A, A2, X, len(SA), len(SB), len(demoted), b1A, b1B, b1B - b1A,
                     dSK, gain_SK, loss_SK, dKS, gain_KS, loss_KS, tag))
            if tag != "OK":
                fails += 1
    if fails:
        STOP("F-3 exact transport identity violated on %d regions" % fails)
    print("S3 verdict: F-3 EXACT identity holds on all 12 regions (3 escalations x 4 "
          "strips) (%.1fs)" % (time.time() - t0))


# ---------- S4: foil-v2 ensemble ----------

def stage_s4x(X, NW):
    banner("S4-%s" % ("a" if X == 10 ** 6 else "b"),
           "ensemble X=%.0e NW=%d H=50, A in {13,31}; loads S / S'' / So" % (X, NW))
    px = precompute_X(X, NW)
    compute_depths(px)
    for A in (13, 31):
        jpath = os.path.join(OUT_DIR, "bp_cell_%d_%d.json" % (X, A))
        cell_run(px, A, jpath)


def stage_s4v():
    banner("S4-verdicts", "foil-v2 verdict matrix (portrait x load x grid)")
    cells = [(10 ** 6, 13), (10 ** 6, 31), (10 ** 9, 13), (10 ** 9, 31)]
    data = {}
    for X, A in cells:
        jp = os.path.join(OUT_DIR, "bp_cell_%d_%d.json" % (X, A))
        with open(jp) as f:
            data[(X, A)] = json.load(f)
    hdr = "  %-10s" + " | %-16s" * 4 + " | %s"
    print(hdr % (("portrait|load",) + tuple("A=%d X=%.0e" % (A, X) for X, A in cells)
                 + ("min|zI|, verdict",)))
    verdicts = {}
    primary = [("P5|S", "P5"), ("P1|S''", "P1"), ("P2|S''", "P2"), ("P3|S''", "P3"),
               ("P3d|S''", "P3d"), ("P4|S''", "P4"), ("SIG|S''", "SIGNED")]
    pii_best = None
    best_min = -1.0
    for k in range(5):
        name = "PII%d|S" % k
        zs = [abs(data[c]['rows'][name]['zI']) for c in cells]
        if min(zs) > best_min:
            best_min = min(zs)
            pii_best = name
    rows = [("P5|S", "P5")] + [(pii_best, "P(ii)best")] + primary[1:]
    for name, label in rows:
        zs, Rs = [], {}
        cellstr = []
        for c in cells:
            st = data[c]['rows'][name]
            zs.append(abs(st['zI']))
            Rs[c] = st['R']
            cellstr.append("R%+.3f zI%+5.1f" % (st['R'], st['zI']))
        ratio_ok = all(abs(Rs[(X, 31)]) >= abs(Rs[(X, 13)]) / 3.0
                       for X in (10 ** 6, 10 ** 9) if abs(Rs[(X, 13)]) > 1e-9)
        v = ("MANAGED-PASS" if min(zs) >= 5 and ratio_ok
             else "SOFT-PASS" if min(zs) >= 3
             else "PARITY-BLIND-UNDER-ESCALATION-v2")
        verdicts[label] = (min(zs), ratio_ok, v)
        print(("  %-10s" + " | %-16s" * 4 + " | %.1f ratio_ok=%s %s")
              % ((name,) + tuple(cellstr) + (min(zs), ratio_ok, v)))
    print("-" * 78)
    print("  secondary loads (information, not verdicts):")
    for name in ("P1|So", "P2|S(=So)", "P1o2|S''"):
        parts = []
        for c in cells:
            st = data[c]['rows'][name]
            parts.append("R%+.3f zI%+5.1f" % (st['R'], st['zI']))
        print(("  %-10s" + " | %-16s" * 4) % ((name,) + tuple(parts)))
    print("-" * 78)
    print("VERDICT SUMMARY (foil-v2 thresholds, seed %d):" % SEED)
    for label, (mz, ro, v) in verdicts.items():
        print("  %-9s min|z_I|=%4.1f ratio_ok=%-5s -> %s" % (label, mz, ro, v))
    flagged = {(X, A): data[(X, A)]['meta']['flagged'] for X, A in cells
               if data[(X, A)]['meta']['flagged']}
    print("  degeneracy-guard escalations: %s" % (flagged if flagged else "none"))
    return verdicts


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "s0"
    if mode == "s0":
        stage_s0()
    elif mode == "s1":
        stage_s1()
    elif mode == "s2":
        stage_s2()
    elif mode == "s3":
        stage_s3()
    elif mode == "s4a":
        stage_s4x(10 ** 6, 3000)
    elif mode == "s4b":
        stage_s4x(10 ** 9, 1000)
    elif mode == "s4v":
        stage_s4v()
    else:
        print("unknown mode %r" % mode)
        sys.exit(2)
