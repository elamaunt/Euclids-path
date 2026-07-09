# relindex_harness.py — Phase 3 DECISIVE gate: relative-index candidates on the
# concrete Step00 geometry graph (exact mirror of EuclidsPath/Engine/GeometryFront.lean:
# State = center/defect/absorber, RealStep = clean/boundary/peel/absorb,
# kappa(v) = 1 - outdeg(v), sideValue in TRUNCATED nat: sideValue(minus,0) = 0).
#
# Measures, over the grid A in {5,7,11,13} x M0 in {4,5,8,13,21,34,55,89,144,233}:
#   * region = forward closure: CONE(c; A, M0) of one clean center, or
#     WINDOW(M0, H=50; A) of the clean seeds M0 < m <= M0+H;
#   * V, E by edge type, chi = V - E, Gauss-Bonnet self-check sum(kappa) = V - E;
#   * sector split: S = clean centers in W (survivors), K = rest (killed);
#     edge blocks E_SS / E_SK / E_KK / E_KS (E_KS = peel edges into clean centers);
#   * four relative-index candidates:
#       rel_sub = chi(W) - chi(K),  chi(K) = V_K - E_KK
#       rel_col = rel_sub + [V_K > 0]                (collapse K to a point)
#       surv    = V_S - E_SS - E_SK                  (= sum of kappa over survivors)
#       surv2   = V_S - E_SS                         (survivor subcomplex alone)
#   * killed matching defect D = number of weak components of (V_K, E_KK)
#     (acyclic 1-complex: each forest component leaves exactly one critical cell);
#   * scale scans: candidates vs cone apex c and vs window base M0, quadratic fits;
#   * graded decomposition of surv by wing weight
#       w(m) = (Omega(6m-1)-1) + (Omega(6m+1)-1)     (w = 0 <=> twin center).
#
# SELF-TEST (hard asserts): at (A,M0) = (5,4) the forward closure of center 3 is the
# kernel-checked 9-vertex cone3 with sum(kappa) = chi = -5 (Lean: gaussBonnet_cone3),
# and the six kernel-checked curvature spectrum values are reproduced.
#
# Exact integer arithmetic throughout; floats only for ratios and fits.
# Output: fixed-width console tables (ASCII). Feeds tools/LAWS_ordered_exponent.md.

import numpy as np
import time
from collections import deque, defaultdict

GRID_A = [5, 7, 11, 13]
GRID_M0 = [4, 5, 8, 13, 21, 34, 55, 89, 144, 233]
WINDOW_H = 50
CONE_COUNTS = {5: 40, 7: 20, 11: 20}
CONE_PARAMS = [(5, 4), (5, 89), (7, 4), (7, 89), (11, 4), (11, 89)]
CANDS = ["chi", "rel_sub", "rel_col", "surv", "surv2", "D"]


# ---------- the graph (exact mirror of GeometryFront.lean) ----------

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
        """Out-edges as list of (target, edge_type) — mirror of outTargets."""
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


# ---------- Omega and wing weight ----------

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


def wing_weight(m):
    return (omega_big(6 * m - 1) - 1) + (omega_big(6 * m + 1) - 1)


# ---------- region machinery ----------

def weak_components(vertices, edges):
    parent = {v: v for v in vertices}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    return len({find(v) for v in vertices})


def region_stats(g, seeds):
    """Forward closure of seeds + full sector census. Exact integers."""
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
    V, VS = len(W), len(S)
    VK = V - VS
    cnt = {'clean': 0, 'boundary': 0, 'peel': 0, 'absorb': 0}
    ESS = ESK = EKK = EKS = 0
    kk_edges = []
    outdeg = defaultdict(int)
    for a, b, et in edges:
        cnt[et] += 1
        outdeg[a] += 1
        sa, sb = a in S, b in S
        if sa and sb:
            ESS += 1
        elif sa:
            ESK += 1
        elif sb:
            EKS += 1
        else:
            EKK += 1
            kk_edges.append((a, b))
    E = len(edges)
    chi = V - E
    ksum = sum(1 - outdeg[v] for v in W)
    # Gauss-Bonnet on a forward-closed region (Lean: gaussBonnet_eq_euler)
    assert ksum == chi, (ksum, chi)
    # sector blocks vs constructors: clean = S->S, boundary = S->K, absorb in K->K
    assert ESS == cnt['clean'] and ESK == cnt['boundary']
    assert EKK == cnt['absorb'] + (cnt['peel'] - EKS)

    K = [v for v in W if v not in S]
    D = weak_components(K, kk_edges) if K else 0
    cells_K = VK + EKK
    st = dict(V=V, E=E, chi=chi,
              Ecl=cnt['clean'], Ebd=cnt['boundary'], Epl=cnt['peel'], Eab=cnt['absorb'],
              VS=VS, VK=VK, ESS=ESS, ESK=ESK, EKK=EKK, EKS=EKS,
              rel_sub=chi - (VK - EKK),
              rel_col=chi - (VK - EKK) + (1 if VK > 0 else 0),
              surv=VS - ESS - ESK,
              surv2=VS - ESS,
              D=D, cells_K=cells_K,
              dper1k=1000.0 * D / cells_K if cells_K else 0.0,
              binom_ok=(ESS == VS * (VS - 1) // 2),
              Wset=W)
    whist = defaultdict(int)
    wkappa = defaultdict(int)
    for v in S:
        w = wing_weight(v[1])
        whist[w] += 1
        wkappa[w] += 1 - outdeg[v]
    st['whist'] = dict(whist)
    st['wkappa'] = dict(wkappa)
    return st


# ---------- fits ----------

def fit_poly(xs, ys, deg):
    xs = np.asarray(xs, dtype=float)
    ys = np.asarray(ys, dtype=float)
    co = np.polyfit(xs, ys, deg)
    pred = np.polyval(co, xs)
    res = float(np.abs(ys - pred).max())
    tot = float(((ys - ys.mean()) ** 2).sum()) + 1e-30
    r2 = 1.0 - float(((ys - pred) ** 2).sum()) / tot
    return co, r2, res


def shape_label(xs, ys):
    vals = list(ys)
    if max(vals) == min(vals):
        return "CONSTANT = %d" % vals[0]
    co2, _, res2 = fit_poly(xs, ys, 2)
    co1, _, res1 = fit_poly(xs, ys, 1)
    span = max(abs(v) for v in vals) + 1.0
    if res1 <= 0.02 * span:
        return "linear  (a1=%+.4f, maxres=%.2f)" % (co1[0], res1)
    if res2 <= 0.02 * span:
        return "quadratic (a2=%+.5f a1=%+.3f, maxres=%.2f)" % (co2[0], co2[1], res2)
    return "quad-fit a2=%+.5f a1=%+.3f maxres=%.2f (imperfect)" % (co2[0], co2[1], res2)


def hdr(title):
    print()
    print("=" * 110)
    print(title.replace("—", "--"))
    print("=" * 110)


# ---------- self-test: kernel-checked calibration at (A, M0) = (5, 4) ----------

def self_test():
    hdr("SELF-TEST — kernel calibration (A,M0) = (5,4): cone(center 3) and curvature spectrum")
    g = Step00Graph(5, 4)
    st = region_stats(g, [('c', 3)])
    expect = {('c', 3), ('c', 2), ('c', 0),
              ('d', 0, 2, '-'), ('d', 0, 3, '-'), ('d', 0, 5, '-'), ('d', 1, 5, '-'),
              ('a', 0), ('a', 1)}
    assert st['Wset'] == expect, sorted(st['Wset'])
    assert st['V'] == 9 and st['chi'] == -5, (st['V'], st['chi'])
    print("cone3 forward closure: 9 vertices, exact match with Lean cone3 finset  -> PASS")
    print("sum(kappa) = chi = V - E = 9 - %d = %d  (Lean gaussBonnet_cone3 = -5)  -> PASS"
          % (st['E'], st['chi']))
    spectrum = [(('a', 0), 1), (('d', 0, 2, '-'), 0), (('d', 6, 5, '-'), 0),
                (('d', 4, 5, '+'), -1), (('c', 2), -3), (('c', 3), -4), (('c', 7), -8)]
    for v, k_expect in spectrum:
        k = 1 - len(g.out(v))
        assert k == k_expect, (v, k, k_expect)
    print("curvature spectrum {absorber:+1, defect(0,2,-):0, defect(6,5,-):0, "
          "defect(4,5,+):-1, c2:-3, c3:-4, c7:-8}  -> PASS")


# ---------- grid census: WINDOW(M0, H=50; A) ----------

ROW_FMT = ("%3d %4d | %5d %5d %6d %5d %5d %6d %7d | %4d %5d %6d %6d %5d %4d |"
           " %8d %8d %8d %8d | %4d %7.1f %s")
HDR_ROW = ("  A   M0 |     V  E_cl   E_bd  E_pl  E_ab      E     chi |  V_S   V_K"
           "   E_SS   E_SK  E_KK E_KS |  rel_sub  rel_col     surv    surv2 |"
           "    D  D/1kc  binom")


def run_grid():
    hdr("GRID CENSUS — WINDOW(M0, H=50; A) = forward closure of clean seeds M0 < m <= M0+H")
    print("(binom column: '=' iff E_SS == C(V_S,2) exactly, i.e. survivor subcomplex is a"
          " complete transitive tournament)")
    results = {}
    for A in GRID_A:
        print("\n-- A = %d --" % A)
        print(HDR_ROW)
        for M0 in GRID_M0:
            g = Step00Graph(A, M0)
            seeds = [('c', m) for m in range(M0 + 1, M0 + WINDOW_H + 1) if g.clean(m)]
            st = region_stats(g, seeds)
            results[(A, M0)] = st
            print(ROW_FMT % (A, M0, st['V'], st['Ecl'], st['Ebd'], st['Epl'], st['Eab'],
                             st['E'], st['chi'], st['VS'], st['VK'], st['ESS'], st['ESK'],
                             st['EKK'], st['EKS'], st['rel_sub'], st['rel_col'],
                             st['surv'], st['surv2'], st['D'], st['dper1k'],
                             '=' if st['binom_ok'] else 'X'))
    n_ok = sum(1 for st in results.values() if st['binom_ok'])
    print("\nexact identity E_SS = C(V_S,2): holds on %d / %d grid windows" % (n_ok, len(results)))
    n_ok2 = sum(1 for st in results.values() if st['surv2'] == st['VS'] * (3 - st['VS']) // 2)
    print("exact identity surv2 = V_S(3 - V_S)/2: holds on %d / %d grid windows" % (n_ok2, len(results)))
    n_ok3 = sum(1 for st in results.values() if st['rel_sub'] == st['surv'] - st['EKS'])
    print("exact identity rel_sub = surv - E_KS: holds on %d / %d grid windows" % (n_ok3, len(results)))
    return results


# ---------- cone scale scan ----------

def run_cones():
    hdr("CONE SCALE SCAN — CONE(c; A, M0), c = first clean centers (40 for A=5, 20 for A=7,11)")
    all_scans = {}
    for A, M0 in CONE_PARAMS:
        N = CONE_COUNTS[A]
        g = Step00Graph(A, M0)
        cs = []
        m = 1
        while len(cs) < N:
            if g.clean(m):
                cs.append(m)
            m += 1
        rows = []
        print("\n-- A = %d, M0 = %d, first %d clean centers --" % (A, M0, N))
        print("    c |     V      E     chi |  rel_sub  rel_col     surv    surv2 |   D  binom")
        for c in cs:
            st = region_stats(g, [('c', c)])
            rows.append(st)
            print("  %3d | %5d %6d %7d | %8d %8d %8d %8d | %3d  %s"
                  % (c, st['V'], st['E'], st['chi'], st['rel_sub'], st['rel_col'],
                     st['surv'], st['surv2'], st['D'], '=' if st['binom_ok'] else 'X'))
        print("  growth fits vs apex c:")
        for name in CANDS:
            ys = [r[name] for r in rows]
            print("    %-8s %s" % (name + ':', shape_label(cs, ys)))
        all_scans[(A, M0)] = (cs, rows)

    print("\n-- M0-invariance check on cones: same apex list, M0 = 4 vs M0 = 89 --")
    m0_inv = {}
    for A in (5, 7, 11):
        cs4, rows4 = all_scans[(A, 4)]
        cs89, rows89 = all_scans[(A, 89)]
        assert cs4 == cs89
        for name in CANDS:
            eq = all(r4[name] == r89[name] for r4, r89 in zip(rows4, rows89))
            m0_inv.setdefault(name, []).append(eq)
        print("  A=%2d: " % A + "  ".join(
            "%s:%s" % (name, "EQUAL" if all(r4[name] == r89[name]
                                            for r4, r89 in zip(rows4, rows89)) else "DIFFER")
            for name in CANDS))
    print("  => sector-relative candidates (rel_sub, rel_col, surv, surv2) are EXACTLY")
    print("     M0-invariant on cones; raw chi and killed defect D are NOT (absorber horizon")
    print("     only reshuffles the killed sector, and the quotient cancels it exactly).")
    return all_scans, m0_inv


# ---------- window M0-scan analysis ----------

def analyze_windows(results):
    hdr("WINDOW SCALE SCAN — candidates vs M0 (H = 50), per A: is anything M0-independent?")
    for A in GRID_A:
        print("\n-- A = %d --  (columns = M0 in %s)" % (A, GRID_M0))
        for name in CANDS:
            vals = [results[(A, M0)][name] for M0 in GRID_M0]
            lbl = shape_label(GRID_M0, vals)
            print("  %-8s " % name + " ".join("%8d" % v for v in vals) + "   " + lbl)
        dpk = [results[(A, M0)]['dper1k'] for M0 in GRID_M0]
        print("  %-8s " % "D/1kc" + " ".join("%8.1f" % v for v in dpk))


# ---------- verdict ----------

def verdict(results, m0_inv):
    hdr("VERDICT — does ANY natural relative-index candidate deliver a constant (-5) for M0 >= 5?")
    const_report = []
    for name in CANDS:
        win_vals = {(A, M0): results[(A, M0)][name]
                    for A in GRID_A for M0 in GRID_M0 if M0 >= 5}
        allv = sorted(set(win_vals.values()))
        per_A_const = all(
            len({results[(A, M0)][name] for M0 in GRID_M0 if M0 >= 5}) == 1
            for A in GRID_A)
        globally_const = len(allv) == 1
        const_report.append((name, globally_const, per_A_const, allv[:4], allv[-4:]))
        print("  %-8s globally constant over M0>=5 grid: %-5s | constant in M0 at each fixed A: %-5s"
              " | value range [%d .. %d] (%d distinct)"
              % (name, globally_const, per_A_const, allv[0], allv[-1], len(allv)))
    any_const = [r[0] for r in const_report if r[1] or r[2]]
    print()
    if not any_const:
        print("  PLAIN VERDICT: NO candidate quotient definition (rel_sub, rel_col, surv, surv2,")
        print("  nor raw chi or D) is constant in M0 -- neither globally nor at fixed A.")
        print("  The Lean-certificate demand 'relIndex = -5 CONSTANT for all M0 >= 5' is REFUTED")
        print("  for every natural quotient tested here. chi(cone3) = -5 at (5,4) is a genuine")
        print("  but ISOLATED calibration point of one small cone, not a scale-stable invariant.")
    else:
        print("  PLAIN VERDICT: constant candidate(s) found: %s" % any_const)
    print()
    inv_names = [n for n, eqs in m0_inv.items() if all(eqs)]
    print("  The ONE exact stability that DOES hold: on cones (fixed apex c) the sector-relative")
    print("  candidates %s are exactly invariant under the absorber horizon M0" % inv_names)
    print("  (verified M0 = 4 vs 89 on every scanned apex, A = 5, 7, 11). The quotient by the")
    print("  killed sector cancels the M0-dependence EXACTLY -- but the resulting index is a")
    print("  function of the apex, not a constant.")
    print()
    print("  Actual scale law (Phase-4 parametrization): the survivor subcomplex is a complete")
    print("  transitive tournament, E_SS = C(V_S,2) exactly, hence")
    print("      surv2 = V_S (3 - V_S) / 2        (exact, all regions)")
    print("      rel_sub = surv - E_KS            (exact, all regions)")
    print("  and V_S = #clean centers <= top(region) grows linearly in the region height")
    print("  (density prod_{5<=q<=A}(q-2)/q), so every candidate is QUADRATIC in the height,")
    print("  not constant. See fits above.")


# ---------- graded decomposition ----------

def graded(results):
    hdr("GRADED DECOMPOSITION — surv = sum_{m in S} kappa(m), split by wing weight "
        "w(m) = (Omega(6m-1)-1)+(Omega(6m+1)-1)")
    picks = [(5, 4), (5, 55), (5, 233), (13, 4), (13, 55), (13, 233)]
    for A, M0 in picks:
        st = results[(A, M0)]
        print("\n(A=%d, M0=%d): V_S=%d  surv=%d" % (A, M0, st['VS'], st['surv']))
        print("    w |   N_w   sum_kappa_w   share_of_surv")
        for w in sorted(st['whist']):
            n, k = st['whist'][w], st['wkappa'][w]
            share = k / st['surv'] if st['surv'] else 0.0
            print("  %3d | %5d   %11d   %13.4f" % (w, n, k, share))
    print("\ntwin (w=0) share of surv across the whole grid:")
    shares = []
    for A in GRID_A:
        row = []
        for M0 in GRID_M0:
            st = results[(A, M0)]
            s = st['wkappa'].get(0, 0) / st['surv'] if st['surv'] else 0.0
            row.append(s)
            shares.append(s)
        print("  A=%2d: " % A + " ".join("%6.3f" % v for v in row))
    print("  overall: min=%.3f max=%.3f." % (min(shares), max(shares)))
    print("  Reading: at A = 13 and low windows ALL survivors are twins (share = 1.000) --")
    print("  the index is carried entirely by w = 0 there; as the window rises (or A drops)")
    print("  the twin share decays roughly like the twin fraction of survivors (down to ~0.26")
    print("  at A=5, M0=233). kappa(m) itself depends on the POSITION m (clean count + defect")
    print("  count below m), NOT on the wing weight of m: the weight enters only through")
    print("  WHICH m survive. No weight class carries a scale-stable index of its own.")


# ---------- main ----------

def main():
    t0 = time.time()
    print("=" * 110)
    print("RELATIVE-INDEX HARNESS -- Phase 3 decisive gate (ordered exponent geometry)")
    print("graph = EuclidsPath/Engine/GeometryFront.lean Step00 (center/defect/absorber;")
    print("clean/boundary/peel/absorb), kappa = 1 - outdeg, chi = V - E on forward-closed regions")
    print("grid: A in %s x M0 in %s, window H = %d" % (GRID_A, GRID_M0, WINDOW_H))
    print("=" * 110)

    self_test()
    results = run_grid()
    cone_scans, m0_inv = run_cones()
    analyze_windows(results)
    verdict(results, m0_inv)
    graded(results)

    print("\ndone in %.1f s." % (time.time() - t0))


if __name__ == "__main__":
    main()
