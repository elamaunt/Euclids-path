#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Grave-depth harness (W4, ledger L43): UNCONDITIONED grave-depth census, drop profiles,
reverse-generation M(N), basin/dichotomy census, and Lean path-witness emission.

Depth model (matches EuclidsPath/Engine/GenealogyForest.lean :: PeelStep EXACTLY):
a peel step m -> t exists iff for some side eps in {+1,-1} (wing 6m-eps) and some prime
p >= 5 dividing the wing, the FULL cofactor wing//p equals 6t+delta (delta in {+1,-1})
with t >= 1.  One prime is peeled off; the cofactor keeps all remaining multiplicity —
the same target set as tools/betti_portrait_harness.py::peel_targets (REUSED, new caps).
Depth 0 = twin center (both wings prime).  BFS caps: DEPTH_CAP=8, NODE_BUDGET=3000
(censored counts reported; target 0).

Stages (argv modes; every stage APPENDS to tools/grave_depth_run1.log):

  selftest    known-fact selftests: depth(4229)=4 with path 4229->846->169->34->5;
              [1,200] histogram {0:40,1:139,2:20,3:1} with the depth-3 root at m=146;
              min-path ratio hits ~5e-5 near m=19994; BFS == exact recursion cross-check.
  census6     exhaustive unconditioned BFS census m in [1,10^6] (SPF sieve) + full
              exact-DP cross-check on ALL 10^6 roots; saves the DP depth array.
  census9     window [10^9, 10^9+50000): wings <= 6.0003e9 factored by numpy trial
              division over sieved primes <= 78500 (isqrt(6.0003e9)=77462 — remainder
              after stripping all hits is prime: two factors > sqrt would exceed x).
  census12    window [10^12, 10^12+50000): Pollard rho (Brent) + deterministic
              Miller-Rabin, bases [2,3,5,7,11,13,17] (deterministic for n < 3.4e14;
              wings <= 6.0000003e12, three orders of margin).
  drops6/9/12 drop profiles per scale: per-step ratios t/m along (a) the MIN-depth path
              (tie-break: smallest t among targets one depth level down) and (b) the
              MAX-TARGET path (greedy: always peel to the largest target — the surviving
              drop-control candidate).  Quantiles (min, 1%, 50%) + verdicts.
  mn          M(N) reverse generation: R_3(twins <= N) prefix; M(N) = largest M with
              [1,M] fully inside the 3-step reverse-peel closure; N in {10,10^2,10^3,10^4}.
  basins      canonical grave (left-wing-first minFac rule) for all m <= 10^5: basin
              sizes, adjacent-pair boundary density, and full reach-set intersection for
              adjacent twin-free pairs (BFS both sides, cap 200 nodes): does any
              DISJOINT-reach twin-free adjacent pair exist?
  emit        min-depth path witnesses for m in [1,2000] as (t, p, side_is_minus,
              target_is_plus) tuples, each step re-verified against the PeelStep
              arithmetic, written as JSON for tools/gen_paths_lean.py.

Intermediate artifacts go to the scratch dir (env GRAVE_DEPTH_SCRATCH or the system temp
dir) — the repo stays clean except this file, the log, gen_paths_lean.py and the Lean module.
"""

import json
import math
import os
import sys
import time

import numpy as np

TOOLS = os.path.dirname(os.path.abspath(__file__))
LOG_PATH = os.path.join(TOOLS, "grave_depth_run1.log")
SCRATCH = os.environ.get("GRAVE_DEPTH_SCRATCH") or os.path.join(
    os.environ.get("TEMP", "/tmp"), "grave_depth_scratch")

DEPTH_CAP = 8          # BFS depth cap (censored value = CENSOR)
CENSOR = 9
NODE_BUDGET = 3000     # BFS node budget
WINDOW = 50000         # window width at X = 10^9 and X = 10^12
TIME_CAP = 5400        # hard per-stage cap (s); reductions disclosed betti-P3 style

SPF_LIM = 6_000_001    # SPF sieve covers every wing 6m+1 for m <= 10^6
TD_LIM = 6_100_000_000  # numpy trial-division tier (covers wings at X = 10^9)
PTD_LIM = 78_500       # trial-division prime table (isqrt(6.0003e9) = 77462 < 78500)
MR_BASES = (2, 3, 5, 7, 11, 13, 17)  # deterministic Miller-Rabin below 3.4e14
MR_VALID = 330_000_000_000_000       # we assert below this (conservative)


def log(msg=""):
    print(msg, flush=True)
    with open(LOG_PATH, "a", encoding="utf-8") as f:
        f.write(str(msg) + "\n")


# ---------- factorization tiers ----------

_SPF = None
_PTD = None
_TWIN = None           # twin table for centers t in [0, 10^6]
_SMALL = None          # python list of primes <= 3000 (rho pre-strip)


def setup_tables():
    global _SPF, _PTD, _TWIN, _SMALL
    if _SPF is not None:
        return
    t0 = time.time()
    spf = np.zeros(SPF_LIM + 1, dtype=np.int32)
    for i in range(2, int(math.isqrt(SPF_LIM)) + 1):
        if spf[i] == 0:
            sl = spf[i * i::i]
            sl[sl == 0] = i
    _SPF = spf
    sieve = np.ones(PTD_LIM + 1, bool)
    sieve[:2] = False
    for i in range(2, int(PTD_LIM ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    _PTD = np.flatnonzero(sieve).astype(np.int64)
    _SMALL = [int(p) for p in _PTD[_PTD <= 3000]]
    ar = 6 * np.arange(0, 10 ** 6 + 1, dtype=np.int64)
    tw = np.zeros(10 ** 6 + 1, bool)
    tw[1:] = (spf[ar[1:] - 1] == 0) & (spf[ar[1:] + 1] == 0)
    _TWIN = tw
    log("  tables: SPF<=%d, %d TD primes <= %d, twin table <= 10^6 (%.1fs)"
        % (SPF_LIM, _PTD.size, PTD_LIM, time.time() - t0))


def is_prime_mr(n):
    """Deterministic Miller-Rabin for n < 3.4e14 with bases (2,3,5,7,11,13,17)."""
    assert n < MR_VALID
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
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
    """Brent's rho: a nontrivial factor of composite odd n (deterministic c-sweep)."""
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
    """Distinct primes of x (rho tier), appended to set `out`."""
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
        if y < SPF_LIM:
            for p in fac_distinct(y):
                out.add(p)
            continue
        if is_prime_mr(y):
            out.add(y)
            continue
        d = rho_brent(y)
        stack.append(d)
        stack.append(y // d)


def fac_distinct(v):
    """Distinct prime factors of v, ascending (v >= 2)."""
    x = int(v)
    if x < SPF_LIM:
        out = []
        while x > 1:
            p = int(_SPF[x])
            if p == 0:
                out.append(x)
                break
            out.append(p)
            while x % p == 0:
                x //= p
        return out
    if x <= TD_LIM:
        out = []
        lim = math.isqrt(x)
        k = int(np.searchsorted(_PTD, lim, 'right'))
        sub = _PTD[:k]
        hits = sub[(x % sub) == 0]
        for p in hits.tolist():
            out.append(int(p))
            while x % p == 0:
                x //= p
        if x > 1:
            out.append(x)   # remainder-prime: two factors > sqrt would exceed x
        return out
    out = set()
    _fac_large(x, out)
    return sorted(out)


def is_prime(v):
    v = int(v)
    if v < 2:
        return False
    if v < SPF_LIM:
        return _SPF[v] == 0
    if v <= TD_LIM:
        lim = math.isqrt(v)
        k = int(np.searchsorted(_PTD, lim, 'right'))
        return not np.any((v % _PTD[:k]) == 0)
    return is_prime_mr(v)


# ---------- peel steps / targets / twins ----------

def peel_steps(m):
    """Annotated peel steps from center m: list of (t, p, side_is_minus, target_is_plus),
    side minus first, primes ascending — the registered enumeration order."""
    out = []
    for off, e in ((-1, True), (1, False)):
        v = 6 * m + off
        for q in fac_distinct(v):
            if q == v:
                continue
            cof = v // q
            if cof < 5:
                continue
            r6 = cof % 6
            if r6 == 5:
                out.append(((cof + 1) // 6, q, e, False))
            elif r6 == 1:
                out.append(((cof - 1) // 6, q, e, True))
    return out


def peel_targets(m):
    return [s[0] for s in peel_steps(m)]


def make_ctx():
    return dict(dcache={}, twcache={}, stat=dict(nodes=0, cens_cap=0, cens_budget=0))


def is_twin(t, ctx=None):
    if t <= 10 ** 6:
        return bool(_TWIN[t])
    if ctx is not None:
        r = ctx['twcache'].get(t)
        if r is not None:
            return r
    r = is_prime(6 * t - 1) and is_prime(6 * t + 1)
    if ctx is not None:
        ctx['twcache'][t] = r
    return r


def grave_depth(m, ctx):
    """Censored BFS min-depth to the nearest twin (betti_portrait_harness BFS, caps
    DEPTH_CAP=8 / NODE_BUDGET=3000)."""
    r = ctx['dcache'].get(m)
    if r is not None:
        return r
    if is_twin(m, ctx):
        ctx['dcache'][m] = 0
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
                if is_twin(u, ctx):
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
    ctx['dcache'][m] = res
    ctx['stat']['nodes'] += nodes
    if res == CENSOR:
        ctx['stat']['cens_budget' if budget_hit else 'cens_cap'] += 1
    return res


def depth_exact(m, memo):
    """Exact (uncapped) min-depth by full recursion — the cross-check oracle."""
    r = memo.get(m)
    if r is not None:
        return r
    memo[m] = 10 ** 9  # cycle guard (targets are strictly below m, never fires)
    if is_twin(m):
        memo[m] = 0
        return 0
    best = 10 ** 9
    for u in peel_targets(m):
        best = min(best, 1 + depth_exact(u, memo))
    memo[m] = best
    return best


# ---------- stage: census ----------

def dp_depth_upto(lim):
    """Exact DP min-depth for all m in [1, lim] (targets are strictly below m)."""
    D = np.full(lim + 1, 9999, dtype=np.int16)
    t0 = time.time()
    for m in range(1, lim + 1):
        if _TWIN[m]:
            D[m] = 0
        else:
            best = 9999
            for t in peel_targets(m):
                d = D[t]
                if d < best:
                    best = d
            D[m] = best + 1
        if m % 200000 == 0:
            log("    DP: %d/%d (%.0fs)" % (m, lim, time.time() - t0))
    return D


def run_census(X, n, tag):
    """BFS census over roots [X, X+n); histogram, max-depth witness, censored counts."""
    setup_tables()
    log("== census %s: roots [%d, %d), DEPTH_CAP=%d NODE_BUDGET=%d ==" % (tag, X, X + n, DEPTH_CAP, NODE_BUDGET))
    ctx = make_ctx()
    depths = np.zeros(n, dtype=np.int16)
    t0 = time.time()
    capped = None
    for i in range(n):
        if time.time() - t0 > TIME_CAP:
            capped = i
            log("  TIME CAP hit after %d/%d roots — reduction disclosed" % (i, n))
            break
        depths[i] = grave_depth(X + i, ctx)
        if (i + 1) % 50000 == 0:
            log("    census: %d/%d roots (%.0fs, %d nodes)" % (i + 1, n, time.time() - t0, ctx['stat']['nodes']))
    done = capped if capped is not None else n
    d = depths[:done]
    hist = {int(k): int((d == k).sum()) for k in np.unique(d)}
    mx = int(d.max())
    wit = int(X + int(np.argmax(d == mx)))
    st = ctx['stat']
    log("  histogram (depth: count): %s" % hist)
    log("  max depth = %d at m = %d; censored(cap)=%d censored(budget)=%d; %d roots, %d nodes, %.0fs"
        % (mx, wit, st['cens_cap'], st['cens_budget'], done, st['nodes'], time.time() - t0))
    os.makedirs(SCRATCH, exist_ok=True)
    np.save(os.path.join(SCRATCH, "census_%s.npy" % tag), depths[:done])
    return d, hist, mx, wit, st


def stage_census6():
    d, hist, mx, wit, st = run_census(1, 10 ** 6, "1e6")
    log("  exact-DP cross-check over ALL of [1, 10^6]:")
    D = dp_depth_upto(10 ** 6)
    np.save(os.path.join(SCRATCH, "dp_1e6.npy"), D)
    same = int((D[1:1 + d.size] == d).sum())
    log("  BFS == DP on %d/%d roots%s" % (same, d.size, "  [EXACT MATCH]" if same == d.size else "  [MISMATCH!]"))
    dpmax = int(D[1:].max())
    log("  DP max depth on [1,10^6] = %d at m = %d" % (dpmax, int(np.argmax(D[1:] == dpmax)) + 1))
    for lim in (2000, 10 ** 4, 10 ** 5, 10 ** 6):
        sub = D[1:lim + 1]
        log("    DP histogram [1,%d]: %s" % (lim, {int(k): int((sub == k).sum()) for k in np.unique(sub)}))


def stage_census9():
    run_census(10 ** 9, WINDOW, "1e9")


def stage_census12():
    run_census(10 ** 12, WINDOW, "1e12")


# ---------- stage: drop profiles ----------

def min_path_steps(m, depth_of):
    """MIN-depth path from m (tie-break: smallest t among targets one level down)."""
    path = []
    cur = m
    dcur = depth_of(cur)
    while dcur > 0:
        best = None
        for (t, p, e, dd) in peel_steps(cur):
            if depth_of(t) == dcur - 1 and (best is None or t < best[0]):
                best = (t, p, e, dd)
        assert best is not None, "min-path reconstruction failed at %d" % cur
        path.append(best)
        cur = best[0]
        dcur -= 1
    return path


def max_target_walk(m, nxt_cache, cap=200):
    """MAX-TARGET path from m: greedy largest target until a twin; returns ratio list."""
    ratios = []
    cur = m
    for _ in range(cap):
        if is_twin(cur):
            return ratios, True
        t = nxt_cache.get(cur)
        if t is None:
            t = max(peel_targets(cur))
            nxt_cache[cur] = t
        ratios.append(t / cur)
        cur = t
    return ratios, False


def report_quantiles(name, arr):
    a = np.asarray(arr, dtype=np.float64)
    if a.size == 0:
        log("  %s: EMPTY" % name)
        return None
    q = (a.min(), np.quantile(a, 0.01), np.quantile(a, 0.50))
    log("  %s: n=%d  min=%.3e  q01=%.3e  q50=%.3e" % (name, a.size, q[0], q[1], q[2]))
    return q


def run_drops(X, n, tag, use_dp):
    setup_tables()
    log("== drops %s: roots [%d, %d) — min-path (smallest-t tie-break) vs max-target ==" % (tag, X, X + n))
    t0 = time.time()
    if use_dp:
        dp_path = os.path.join(SCRATCH, "dp_1e6.npy")
        D = np.load(dp_path) if os.path.exists(dp_path) else dp_depth_upto(10 ** 6)
        depth_of = lambda t: int(D[t])
    else:
        ctx = make_ctx()
        depth_of = lambda t: grave_depth(t, ctx)
    min_ratios, max_ratios, max_depths = [], [], []
    nxt_cache = {}
    min_extreme = (1.0, None)
    uncapped_fail = 0
    done = 0
    for i in range(n):
        if time.time() - t0 > TIME_CAP:
            log("  TIME CAP hit after %d/%d roots — reduction disclosed" % (i, n))
            break
        m = X + i
        d0 = depth_of(m)
        if d0 >= CENSOR:
            continue  # censored (counted by census stage; target 0)
        if d0 > 0:
            steps = min_path_steps(m, depth_of)
            cur = m
            for (t, p, e, dd) in steps:
                r = t / cur
                min_ratios.append(r)
                if r < min_extreme[0]:
                    min_extreme = (r, (cur, t, p))
                cur = t
            rr, ok = max_target_walk(m, nxt_cache)
            if not ok:
                uncapped_fail += 1
            else:
                max_ratios.extend(rr)
                max_depths.append(len(rr))
        done += 1
        if (i + 1) % 50000 == 0:
            log("    drops: %d/%d roots (%.0fs)" % (i + 1, n, time.time() - t0))
    log("  processed %d roots (%.0fs)" % (done, time.time() - t0))
    qmin = report_quantiles("MIN-path  per-step ratio t/m", min_ratios)
    qmax = report_quantiles("MAX-target per-step ratio t/m", max_ratios)
    log("  MIN-path extreme step: ratio %.3e at %s" % (min_extreme[0], min_extreme[1]))
    if max_depths:
        md = np.asarray(max_depths)
        log("  MAX-target depth: mean=%.2f max=%d (walk cap misses: %d)" % (md.mean(), md.max(), uncapped_fail))
    if qmax is not None:
        log("  VERDICT %s: max-target min ratio = %.3e — %s" % (
            tag, qmax[0],
            "bounded away from 0 so far (>= ~1/8 would be drop-control; judge across scales)"
            if qmax[0] > 1e-3 else "NOT drop-controlled (ratio reaches ~0)"))


def stage_drops6():
    run_drops(1, 10 ** 6, "1e6", use_dp=True)


def stage_drops9():
    run_drops(10 ** 9, WINDOW, "1e9", use_dp=False)


def stage_drops12():
    run_drops(10 ** 12, WINDOW, "1e12", use_dp=False)


# ---------- stage: M(N) reverse generation ----------

def stage_mn():
    setup_tables()
    log("== M(N): largest M with [1,M] inside R_3(twins <= N) ==")
    MAX_SCAN = 10 ** 6
    for N in (10, 100, 1000, 10000):
        f = np.full(MAX_SCAN + 1, 9999, dtype=np.int16)
        M = None
        for m in range(1, MAX_SCAN + 1):
            if _TWIN[m]:
                f[m] = 0 if m <= N else 9999   # twins > N are dead ends (no peel out)
            else:
                best = 9999
                for t in peel_targets(m):
                    if f[t] < best:
                        best = f[t]
                f[m] = min(best + 1, 9999)
            if f[m] > 3:
                M = m - 1
                break
        if M is None:
            log("  M(%d) >= %d (scan cap hit — disclosed)" % (N, MAX_SCAN))
        else:
            log("  M(%d) = %d  (first failure at m = %d, min steps to a twin <= %d there: %s)"
                % (N, M, M + 1, N, ">3"))


# ---------- stage: basins ----------

def canonical_next(m):
    """Left-wing-first minFac rule: peel the LEFT wing 6m-1 if composite (p = its minFac),
    else the RIGHT wing 6m+1 (m is not a twin so one wing is composite)."""
    for off in (-1, 1):
        v = 6 * m + off
        p = int(_SPF[v])
        if p == 0:
            continue  # wing prime
        cof = v // p
        if cof < 5:
            continue
        r6 = cof % 6
        return (cof + 1) // 6 if r6 == 5 else (cof - 1) // 6
    raise RuntimeError("no canonical peel at %d" % m)


def reach_set(m, cap=200):
    """Full reach set of m under arbitrary peel steps (BFS, node cap). Returns (set, capped)."""
    seen = {m}
    frontier = [m]
    while frontier:
        nxt = []
        for t in frontier:
            if is_twin(t):
                continue  # twins are sinks
            for u in peel_targets(t):
                if u not in seen:
                    seen.add(u)
                    nxt.append(u)
                    if len(seen) >= cap:
                        return seen, True
        frontier = nxt
    return seen, False


def stage_basins():
    setup_tables()
    LIM = 10 ** 5
    log("== basins: canonical grave (left-wing-first minFac) for m <= %d ==" % LIM)
    t0 = time.time()
    g = np.zeros(LIM + 1, dtype=np.int64)
    for m in range(1, LIM + 1):
        g[m] = m if _TWIN[m] else g[canonical_next(m)]
    twins = int(_TWIN[1:LIM + 1].sum())
    graves, counts = np.unique(g[1:], return_counts=True)
    order = np.argsort(-counts)
    top = [(int(graves[i]), int(counts[i])) for i in order[:10]]
    log("  twins <= %d: %d; nonempty basins: %d; top-10 basin sizes: %s"
        % (LIM, twins, graves.size, top))
    log("  basin size stats: mean=%.2f median=%d max=%d" % (counts.mean(), int(np.median(counts)), counts.max()))
    bd = int((g[1:LIM] != g[2:LIM + 1]).sum())
    log("  boundary pairs g(m) != g(m+1): %d / %d  (density %.4f)" % (bd, LIM - 1, bd / (LIM - 1)))
    # adjacent twin-free pairs: full reach-set intersection (cap 200 both sides)
    disjoint, unresolved, checked = [], 0, 0
    prev_reach = None  # rolling cache: reach(m+1) of this pair is reach(m) of the next
    t1 = time.time()
    for m in range(1, LIM):
        if _TWIN[m] or _TWIN[m + 1]:
            prev_reach = None
            continue
        if prev_reach is None:
            ra, ca = reach_set(m)
        else:
            ra, ca = prev_reach
        rb, cb = reach_set(m + 1)
        prev_reach = (rb, cb)
        checked += 1
        if ra & rb:
            pass  # provably intersecting
        elif ca or cb:
            unresolved += 1
        else:
            disjoint.append(m)
        if m % 20000 == 0:
            log("    basins reach: %d/%d (%.0fs)" % (m, LIM, time.time() - t1))
        if time.time() - t0 > TIME_CAP:
            log("  TIME CAP hit at m=%d — reduction disclosed" % m)
            break
    log("  adjacent twin-free pairs checked: %d; DISJOINT-reach pairs: %d; unresolved (cap 200): %d"
        % (checked, len(disjoint), unresolved))
    if disjoint:
        log("  disjoint examples (first 10): %s" % disjoint[:10])
    log("  VERDICT: disjoint-reach twin-free adjacent pair exists <= 1e5: %s"
        % ("YES" if disjoint else ("NO (none proven disjoint; %d unresolved by cap)" % unresolved)))


# ---------- stage: emit (Lean path witnesses) ----------

def verify_step(m, t, p, e, d):
    """The EXACT PeelStep arithmetic: side 6m-1 (e) or 6m+1 (!e) equals p * cofactor,
    cofactor = 6t+1 (d) or 6t-1 (!d); p prime >= 5; 1 <= t < m."""
    assert 1 <= t < m, (m, t)
    assert p >= 5 and is_prime(p), (m, p)
    side = 6 * m - 1 if e else 6 * m + 1
    targ = 6 * t + 1 if d else 6 * t - 1
    assert side == p * targ, (m, t, p, e, d)


def stage_emit():
    setup_tables()
    LIM = 2000
    log("== emit: min-depth path witnesses for m in [1,%d] ==" % LIM)
    D = np.full(LIM + 1, 9999, dtype=np.int16)
    for m in range(1, LIM + 1):
        if _TWIN[m]:
            D[m] = 0
        else:
            D[m] = 1 + min(int(D[t]) for t in peel_targets(m))
    mx = int(D[1:].max())
    hist = {int(k): int((D[1:] == k).sum()) for k in np.unique(D[1:])}
    log("  depth histogram [1,%d]: %s ; max = %d" % (LIM, hist, mx))
    if mx > 3:
        log("  !! depth > 3 inside [1,%d] — falling back to [1,1000] (disclosed)" % LIM)
        LIM = 1000
        assert int(D[1:LIM + 1].max()) <= 3
    depth_of = lambda t: int(D[t])
    data = []
    for m in range(1, LIM + 1):
        steps = min_path_steps(m, depth_of) if D[m] > 0 else []
        cur = m
        for (t, p, e, d) in steps:
            verify_step(cur, t, p, e, d)
            cur = t
        assert is_twin(cur), (m, cur)
        assert len(steps) == int(D[m]) <= 3
        data.append([[int(t), int(p), bool(e), bool(d)] for (t, p, e, d) in steps])
    os.makedirs(SCRATCH, exist_ok=True)
    out = os.path.join(SCRATCH, "paths_1_%d.json" % LIM)
    with open(out, "w", encoding="utf-8") as f:
        json.dump(data, f)
    log("  emitted %d verified path entries -> %s" % (len(data), out))
    log("  every step re-verified: 6m-eps == p*(6t+delta), p prime >= 5, 1 <= t < m; terminal twin checked")


# ---------- stage: selftest ----------

def stage_selftest():
    setup_tables()
    log("== selftest (known facts) ==")
    memo = {}
    # (1) [1,200] histogram
    d200 = [depth_exact(m, memo) for m in range(1, 201)]
    hist = {}
    for v in d200:
        hist[v] = hist.get(v, 0) + 1
    ok1 = hist == {0: 40, 1: 139, 2: 20, 3: 1}
    m3 = [m for m in range(1, 201) if d200[m - 1] == 3]
    ok1b = m3 == [146]
    log("  [1,200] histogram: %s  expected {0:40,1:139,2:20,3:1}  -> %s; depth-3 root(s) %s (expect [146]) -> %s"
        % (hist, "PASS" if ok1 else "FAIL", m3, "PASS" if ok1b else "FAIL"))
    # (2) depth(4229) = 4 with path 4229 -> 846 -> 169 -> 34 -> 5
    d4229 = depth_exact(4229, memo)
    chain = [4229, 846, 169, 34, 5]
    okc = all(b in peel_targets(a) for a, b in zip(chain, chain[1:])) and is_twin(5)
    ctx = make_ctx()
    dbfs = grave_depth(4229, ctx)
    log("  depth(4229): exact=%d BFS=%d (expect 4) -> %s; chain %s valid peel steps + twin sink -> %s"
        % (d4229, dbfs, "PASS" if d4229 == dbfs == 4 else "FAIL", chain, "PASS" if okc else "FAIL"))
    # (3) min-path ratio ~5e-5 near m = 19994
    depth_of = lambda t: depth_exact(t, memo)
    best = (1.0, None)
    for m in range(19894, 20095):
        if is_twin(m):
            continue
        cur = m
        for (t, p, e, dd) in min_path_steps(m, depth_of):
            r = t / cur
            if r < best[0]:
                best = (r, (cur, t, p))
            cur = t
    log("  min-path ratio near 19994: min=%.4e at %s (expect ~5.00e-5) -> %s"
        % (best[0], best[1], "PASS" if best[0] <= 5.1e-5 else "FAIL"))
    # (4) BFS == exact recursion on [1,400] and a spot sample
    ok4 = True
    for m in list(range(1, 401)) + list(range(99000, 99040)):
        if grave_depth(m, ctx) != depth_exact(m, memo):
            ok4 = False
            log("    BFS/exact mismatch at %d" % m)
    log("  BFS == exact recursion on [1,400] + 40 spot roots -> %s" % ("PASS" if ok4 else "FAIL"))


# ---------- main ----------

STAGES = dict(selftest=stage_selftest, census6=stage_census6, census9=stage_census9,
              census12=stage_census12, drops6=stage_drops6, drops9=stage_drops9,
              drops12=stage_drops12, mn=stage_mn, basins=stage_basins, emit=stage_emit)


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in STAGES:
        print("usage: grave_depth_harness.py {%s}" % "|".join(STAGES))
        sys.exit(2)
    log("")
    log("#### %s @ %s (caps: depth %d, budget %d, time %ds) ####"
        % (sys.argv[1], time.strftime("%Y-%m-%d %H:%M:%S"), DEPTH_CAP, NODE_BUDGET, TIME_CAP))
    STAGES[sys.argv[1]]()


if __name__ == "__main__":
    main()
