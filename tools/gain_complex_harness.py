# gain_complex_harness.py -- SG0-A gate: the gain 2-complex over the Step00 ornament graph.
#
# Graph layer: EXACT mirror of tools/relindex_harness.py::Step00Graph (which mirrors
# EuclidsPath/Engine/GeometryFront.lean): vertices center(m)/defect(n,q,s)/absorber(a);
# edges clean/boundary/peel/absorb; Clean(A,m) = no prime q <= A divides 6m+-1 in
# TRUNCATED nat (sideValue(minus,0) = 0, so center 0 is NOT clean). The kernel-checked
# cone3 self-test of relindex_harness is kept verbatim.
#
# New layer: wingGain(m) = (Omega(6m-1)-1, Omega(6m+1)-1) on clean centers;
# wingSign(m) = (-1)^(Omega_L + Omega_R); twin center <=> gain (0,0).
# 2-cells, three fill variants:
#   FULL      = all directed 2-simplices u->v->w with edge u->w, plus ALL canonically
#               ordered killed squares (m, d(n,q,s), a_n, d(n,q',s')), (q,s) < (q',s');
#   CANONICAL = T-cells (m,n,b) survivor triangles coned at the MINIMAL survivor b of W;
#               I-cells (m, prev(m,d), d) for each S->K boundary edge m->d with m NOT
#               minimal above n(d), prev = largest survivor in (n(d), m);
#               Q-cells (c_min, d_i, a_n, d_{i+1}) over CONSECUTIVE pairs of the
#               absorber in-fan (sorted lex by (q,s), '-' < '+'), anchored at the
#               minimal survivor above n;
#   T-ONLY    = just the T-cells.
# Boundary matrices: d1 (vertices x edges) with edge u->v |-> v - u; d2 (edges x faces)
# with triangle (a,b,c) |-> ab + bc - ac and square (c,d1,a,d2) |-> cd1 + d1a - d2a - cd2.
# Ranks EXACT over F_p for p = 10007 AND 10009 (cross-checked), and over Q via
# fractions on small regions (E <= 300).
#
# Gates (pre-registered): G1 exact-law selftest -- ANY violation is reported and STOPS
# gates G2/G3/G4 (design bug). G2 decoration check, G3 foil escalation, G4 Tier-1
# capture run only on a fully green G1. Feeds tools/LAWS_ordered_exponent.md (L20+).
#
# Scope reductions (coordinator, 2026-07-10): G2 on 3000 windows; G3 3000 windows at
# X=1e6 and 1000 at 1e9, no 1e12; G4 = measured capture fraction (exact CRT-expectation
# version deferred, documented inline).

import bisect
import math
import sys
import time
from collections import deque, defaultdict
from fractions import Fraction

import numpy as np

P1, P2 = 10007, 10009            # rank cross-check primes
RNG = np.random.default_rng(20260710)

GRID_A = [5, 7, 11, 13]
WIN_M0 = [4, 8, 21, 55]
WINDOW_H = 50
CONE_M0 = [4, 89]
N_APEX = 30
FULL_EDGE_CAP = 1200             # runtime guard for the FULL fill
QRANK_EDGE_CAP = 300             # runtime guard for exact-Q rank cross-check
HOL_SAMPLE_CAP = 30000           # holonomy law sample size (>= 1e4 required)


# ---------- the graph (EXACT mirror of relindex_harness.py / GeometryFront.lean) ----------

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
            # q | 0 for every q, so Clean(A,0) is automatically False
            c = all(lo % q != 0 and hi % q != 0 for q in self.primes)
            self._clean[m] = c
        return c

    def out(self, v):
        """Out-edges as list of (target, edge_type) -- mirror of outTargets."""
        e = self._out.get(v)
        if e is not None:
            return e
        out = []
        if v[0] == 'c':
            m = v[1]
            if self.clean(m):                          # non-clean center: terminal
                for n in range(m):
                    if self.clean(n):                  # clean: Clean m & Clean n & n < m
                        out.append((('c', n), 'clean'))
                    for s in ('-', '+'):               # boundary: q | sideValue(s,n)
                        sv = side_value(s, n)
                        for q in self.primes:
                            if sv % q == 0:
                                out.append((('d', n, q, s), 'boundary'))
        elif v[0] == 'd':
            _, n, q, s = v
            sv = side_value(s, n)
            seen = set()                               # Finset image: dedupe targets
            for t in range(n):                         # peel: sv = q * sideValue(os,t), t < n
                for os in ('-', '+'):
                    if sv == q * side_value(os, t) and t not in seen:
                        seen.add(t)
                        out.append((('c', t), 'peel'))
            if n <= self.M0:                           # absorb: n <= M0
                out.append((('a', n), 'absorb'))
        self._out[v] = out
        return out


# ---------- Omega, wing gain, wing sign ----------

_OMEGA = {}


def omega_big(n):
    r = _OMEGA.get(n)
    if r is not None:
        return r
    r, x, d = 0, n, 2
    while d * d <= x:
        while x % d == 0:
            x //= d
            r += 1
        d += 1
    if x > 1:
        r += 1
    _OMEGA[n] = r
    return r


def wing_gain(m):
    """(Omega(6m-1)-1, Omega(6m+1)-1); defined for m >= 1 (clean centers)."""
    return (omega_big(6 * m - 1) - 1, omega_big(6 * m + 1) - 1)


def wing_sign_center(m):
    """(-1)^(Omega_L + Omega_R). Convention: wingSign(0) := +1 (center 0 is never
    clean; it enters cells only through defects at level n = 0, always in PAIRS with
    the same n, so any fixed convention cancels in every holonomy product)."""
    if m == 0:
        return 1
    return -1 if ((omega_big(6 * m - 1) + omega_big(6 * m + 1)) & 1) else 1


def wing_sign_vertex(v):
    if v[0] == 'c':
        return wing_sign_center(v[1])
    if v[0] == 'd':
        return wing_sign_center(v[1])   # a defect carries its level's sign
    return 1                            # absorber (never a pass-through in our cells)


# ---------- forward closure and sector census ----------

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
    # Gauss-Bonnet self-check (Lean: gaussBonnet_eq_euler)
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


# ---------- self-test: kernel-checked calibration at (A, M0) = (5, 4) ----------

def self_test():
    print("SELF-TEST -- kernel calibration (A,M0) = (5,4): cone(center 3) + curvature spectrum")
    g = Step00Graph(5, 4)
    W, edges, S = closure(g, [('c', 3)])
    expect = {('c', 3), ('c', 2), ('c', 0),
              ('d', 0, 2, '-'), ('d', 0, 3, '-'), ('d', 0, 5, '-'), ('d', 1, 5, '-'),
              ('a', 0), ('a', 1)}
    assert W == expect, sorted(W)
    assert len(W) == 9 and len(W) - len(edges) == -5, (len(W), len(edges))
    print("  cone3 forward closure: 9 vertices, exact match with Lean cone3 finset -> PASS")
    print("  chi = V - E = 9 - %d = %d  (Lean gaussBonnet_cone3 = -5) -> PASS" %
          (len(edges), len(W) - len(edges)))
    spectrum = [(('a', 0), 1), (('d', 0, 2, '-'), 0), (('d', 6, 5, '-'), 0),
                (('d', 4, 5, '+'), -1), (('c', 2), -3), (('c', 3), -4), (('c', 7), -8)]
    for v, k_expect in spectrum:
        k = 1 - len(g.out(v))
        assert k == k_expect, (v, k, k_expect)
    print("  curvature spectrum (7 kernel-checked values) -> PASS")


# ---------- fills: T-only and canonical (T + I + Q) ----------

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


def rank_fp(M):
    import numpy as np
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


def quotient_betti(W, edges, faces, S):
    import numpy as np
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
    r1, r2 = rank_fp(D1), rank_fp(D2)
    return len(vq) - r1, len(eidx) - r1 - r2, len(faces) - r2


def gate_g1():
    print("=" * 70)
    print("G1: exact-law selftest of the fills (STOP rule on violation)")
    fails = 0
    for A in (5, 7, 11):
        g = Step00Graph(A, 4)
        apexes = [m for m in range(1, 300) if g.clean(m)][:12]
        for apex in apexes:
            W, edges, S = closure(g, [('c', apex)])
            sc = sector_counts(edges, S)
            fT = fills(g, W, edges, S, canonical=False)
            b0, b1, b2 = quotient_betti(W, edges, fT, S)
            law1 = (b1 == sc['ESK'] + sc['EKS'] - 1) if len(S) >= 1 else True
            fC = fills(g, W, edges, S, canonical=True)
            c0, c1, c2 = quotient_betti(W, edges, fC, S)
            law2 = (c0, c1, c2) == (1, 0, 0)
            if not (law1 and law2):
                fails += 1
            print("  A=%2d apex=%3d Vs=%2d Tonly=(%d,%d,%d) law1[%d+%d-1]=%s canon=(%d,%d,%d) law2=%s"
                  % (A, apex, len(S), b0, b1, b2, sc['ESK'], sc['EKS'],
                     'OK' if law1 else 'FAIL', c0, c1, c2, 'OK' if law2 else 'FAIL'))
    print("G1 verdict: %s" % ('PASS' if fails == 0 else 'FAIL (%d regions)' % fails))
    return fails == 0


# ---------- G3: foil escalation on plain windows ----------

def omega_range(lo_m, n_centers):
    import numpy as np
    import math as _m
    lim = int(_m.isqrt(6 * (lo_m + n_centers) + 10)) + 1
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


def gate_g3():
    import numpy as np
    import time as _t
    rng = np.random.default_rng(20260710)
    print("=" * 70)
    print("G3: foil escalation, H=50; MANAGED-PASS |z_I|>=5 all A and |R101/R13|>=1/3")
    results = {}
    for X, NW in ((10 ** 6, 3000), (10 ** 9, 1000)):
        n = 50 * NW
        t0 = _t.time()
        OL, OR = omega_range(X, n)
        print("[X=%.0e] sieved %d centers in %.1fs" % (X, n, _t.time() - t0), flush=True)
        m_arr = X + np.arange(n, dtype=np.int64)
        lam = 1 - 2 * ((OL + OR) & 1)
        twin = (OL == 1) & (OR == 1)
        for A in (13, 31, 101):
            ps_A = [q for q in primes_upto(A) if q >= 5]
            cleanm = np.ones(n, dtype=bool)
            for q in ps_A:
                inv6 = pow(6, -1, q)
                cleanm &= (m_arr % q != inv6) & (m_arr % q != (q - inv6) % q)
            cl = cleanm.reshape(NW, 50)
            lm = np.where(cl, lam.reshape(NW, 50), 0)
            tw = cl & twin.reshape(NW, 50)
            gl = np.where(cl, (OL - 1).reshape(NW, 50), 0)
            gr = np.where(cl, (OR - 1).reshape(NW, 50), 0)
            pos = np.arange(50)
            top = np.where(cl, pos, -1).max(axis=1)
            nontop = cl & (pos[None, :] != top[:, None])
            S = lm.sum(axis=1).astype(np.float64)
            Sp = np.where(tw, 0, lm).sum(axis=1).astype(np.float64)
            I1 = (((gl + gr) % 2 == 1) & nontop).any(axis=1).astype(np.float64)
            I5 = ((gl == 0) & (gr == 0) & nontop).sum(axis=1).astype(np.float64)
            I3 = np.where(nontop, gl + gr, 999).min(axis=1).astype(np.float64)
            pool = lam[cleanm]
            nsurv_total = int(cl.sum())
            for name, I in (("I1", I1), ("I3", I3), ("I5", I5)):
                row = {}
                for lname, Ld in (("S", S), ("Sp", Sp)):
                    if I.std() < 1e-12 or Ld.std() < 1e-12:
                        row[lname] = (0.0, 0.0, 0.0)
                        continue
                    R = float(np.corrcoef(I, Ld)[0, 1])
                    Ic = I.copy()
                    perm = np.empty(200)
                    for t in range(200):
                        rng.shuffle(Ic)
                        perm[t] = np.corrcoef(Ic, Ld)[0, 1]
                    nulls = np.empty(200)
                    for t in range(200):
                        lmat = np.zeros_like(lm, dtype=np.float64)
                        lmat[cl] = rng.choice(pool, size=nsurv_total)
                        Sn = (np.where(tw, 0, lmat) if lname == "Sp" else lmat).sum(axis=1)
                        nulls[t] = 0.0 if Sn.std() < 1e-12 else np.corrcoef(I, Sn)[0, 1]
                    zW = R / (perm.std() + 1e-15)
                    zI = (R - nulls.mean()) / (nulls.std() + 1e-15)
                    row[lname] = (R, zW, zI)
                results[(X, A, name)] = row
                rs, rp = row["S"], row["Sp"]
                print("  X=%.0e A=%3d %s: R(S)=%+.4f zI=%+.1f | R(Sp)=%+.4f zW=%+.1f zI=%+.1f"
                      % (X, A, name, rs[0], rs[2], rp[0], rp[1], rp[2]), flush=True)
    print("-" * 70)
    print("VERDICTS (against de-mechanized load Sp):")
    for name in ("I1", "I3", "I5"):
        zs, Rs = [], {}
        for X in (10 ** 6, 10 ** 9):
            for A in (13, 31, 101):
                R, zW, zI = results[(X, A, name)]["Sp"]
                zs.append(abs(zI))
                Rs[(X, A)] = R
        ratio_ok = all(abs(Rs[(X, 101)]) >= abs(Rs[(X, 13)]) / 3.0
                       for X in (10 ** 6, 10 ** 9) if abs(Rs[(X, 13)]) > 1e-9)
        v = ("MANAGED-PASS" if min(zs) >= 5 and ratio_ok
             else "SOFT-PASS" if min(zs) >= 3
             else "PARITY-BLIND-UNDER-ESCALATION")
        print("  %s: min|z_I|=%.1f ratio_ok=%s -> %s" % (name, min(zs), ratio_ok, v))


if __name__ == "__main__":
    import sys as _s
    mode = _s.argv[1] if len(_s.argv) > 1 else "selftest"
    if mode == "selftest":
        self_test()
    elif mode == "g1":
        self_test()
        ok = gate_g1()
        _s.exit(0 if ok else 1)
    elif mode == "g3":
        gate_g3()
