"""SG0-B gate -- extremal gap geometry for the twin-Jacobsthal wall.

Clean(A, m)  <=>  no prime q in [5, A] divides 6m-1 or 6m+1.
P_A = prod primes 5..A;  Clean is P_A-periodic;  G(A) = largest cyclic gap
between consecutive clean residues over one full period.

Tasks
  1. Reduced witness lists for Lean kernel certificates (A = 17, 19):
     minimal-ish chains of clean residues with consecutive cyclic gaps <= L,
     L = floor(A^2/7).  Files: tools/witness_a17.lean.txt, tools/witness_a19.lean.txt,
     tools/witness_a17_meta.txt.
  2. Exact G(A) for A = 29 (full-period chunked scan) and A = 31, 37
     (exact phase-cover branch-and-bound; cross-validated against scans).
     Margins table G(A) vs A^2/7 and A^2/6 for all A in 5..37.
  3. Extremal phase portraits (all maximal gaps, per-clock kill patterns,
     mirror-orbit count) for A <= 23, plus transfer hypotheses:
     (a) embedding of A'-extremal windows into the gap ranking of scale A,
     (b) Spearman rank transfer of gap lengths across consecutive scales,
     (c) waste (multiplicity) profiles of extremal vs random windows.

Exact arithmetic everywhere a claim is exact: sieves are integer numpy,
the solver works on exact bitmasks, certificates are re-verified by trial
division.  Log: tools/gap_extremal_run1.log.

Usage:  python tools/gap_extremal_harness.py [--parts 1,2,3] [--budget 900]
"""

import argparse
import sys
import time

import numpy as np

# ---------------------------------------------------------------- utilities

PRIMES_SMALL = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

KNOWN_G = {5: 2, 7: 5, 11: 7, 13: 11, 17: 18, 19: 25, 23: 34}  # short_survivor_run1.log

T0 = time.time()


def wing_primes(A):
    return [q for q in PRIMES_SMALL if q <= A]


def primorial(A):
    P = 1
    for q in wing_primes(A):
        P *= q
    return P


def inv6(q):
    return pow(6, -1, q)


class Tee:
    def __init__(self, path):
        self.f = open(path, "w", encoding="utf-8")

    def write(self, s):
        sys.__stdout__.write(s)
        self.f.write(s)

    def flush(self):
        sys.__stdout__.flush()
        self.f.flush()


def log(msg=""):
    print(msg)
    sys.stdout.flush()


def stamp():
    return f"[{time.time() - T0:7.1f}s]"


# ------------------------------------------------- full-period clean sieves

_POS_CACHE = {}


def clean_positions(A):
    """Sorted numpy array of all clean residues in [0, P_A). Residue 0 is clean."""
    if A in _POS_CACHE:
        return _POS_CACHE[A]
    P = primorial(A)
    mask = np.ones(P, dtype=bool)
    for q in wing_primes(A):
        a = inv6(q)
        mask[a::q] = False
        mask[(q - a) % q::q] = False
    pos = np.flatnonzero(mask)
    _POS_CACHE[A] = pos
    return pos


def cyclic_gaps(pos, P):
    """All consecutive gaps over the cycle (len == len(pos)); gaps[i] = pos[i+1]-pos[i], last wraps."""
    g = np.empty(len(pos), dtype=np.int64)
    g[:-1] = np.diff(pos)
    g[-1] = P - pos[-1] + pos[0]
    return g


def max_gap_starts(pos, P):
    """(G, list of clean residues r such that the following cyclic gap has length G)."""
    g = cyclic_gaps(pos, P)
    G = int(g.max())
    starts = [int(pos[i]) for i in np.flatnonzero(g == G)]
    return G, starts


# ------------------------------------------------- chunked scan (large P)

def chunked_gap_scan(A, m_limit, chunk=50_000_000, label=""):
    """Scan m in [0, m_limit): return (max_gap, [gap-start residues], n_clean, first_clean, last_clean).

    If m_limit == P_A the wraparound gap is included and the result is EXACT G(A).
    Otherwise it is a lower bound on G(A).
    """
    qs = wing_primes(A)
    cls = []
    for q in qs:
        a = inv6(q)
        cls.append((q, a, (q - a) % q))
    best, best_rs = 0, []
    prev_clean = None
    first_clean = None
    n_clean = 0
    t0 = time.time()
    for lo in range(0, m_limit, chunk):
        hi = min(lo + chunk, m_limit)
        struck = np.zeros(hi - lo, dtype=bool)
        for q, a1, a2 in cls:
            struck[(a1 - lo) % q::q] = True
            struck[(a2 - lo) % q::q] = True
        cl = np.flatnonzero(~struck).astype(np.int64) + lo
        if cl.size == 0:
            continue
        n_clean += cl.size
        if first_clean is None:
            first_clean = int(cl[0])
        if prev_clean is not None:
            g0 = int(cl[0]) - prev_clean
            if g0 > best:
                best, best_rs = g0, [prev_clean]
            elif g0 == best:
                best_rs.append(prev_clean)
        gaps = np.diff(cl)
        if gaps.size:
            mx = int(gaps.max())
            if mx >= best:
                idx = np.flatnonzero(gaps == mx)
                if mx > best:
                    best, best_rs = mx, []
                best_rs.extend(int(cl[i]) for i in idx)
        prev_clean = int(cl[-1])
    P = primorial(A)
    if m_limit == P:
        gw = first_clean + P - prev_clean
        if gw > best:
            best, best_rs = gw, [prev_clean]
        elif gw == best:
            best_rs.append(prev_clean)
    log(f"  {stamp()} scan A={A} m<{m_limit:,}{label}: max gap {best} "
        f"({len(best_rs)} start(s), first at r={best_rs[0]}), {n_clean:,} clean [{time.time()-t0:.1f}s]")
    return best, best_rs, n_clean, first_clean, prev_clean


# ------------------------------------------------- exact phase-cover solver
#
# Offset o in [1, g] is struck by clock q iff o = t_q +- inv6(q) (mod q), where
# t_q = (-r) mod q is a free phase (CRT realises every phase tuple as some r).
# G(A) = M(A) + 1 where M(A) = max g such that some phase tuple covers all of [1, g].

def _offsets_mask(q, c, g):
    o0 = c if c >= 1 else q
    m = 0
    for o in range(o0, g + 1, q):
        m |= 1 << (o - 1)
    return m


def _phase_masks(q, g):
    i = inv6(q)
    return tuple(_offsets_mask(q, (t + i) % q, g) | _offsets_mask(q, (t - i) % q, g)
                 for t in range(q))


class SolverTimeout(Exception):
    pass


def decision(g, A, deadline=None):
    """Exact decision: is there a phase tuple covering all offsets 1..g?

    Returns (True, [(q, t_q) placed clocks], nodes) or (False, None, nodes).
    Complete search: small clocks (<=13) by phase enumeration with mirror
    reduction on the first clock; large clocks by first-uncovered anchored
    DFS with exact residual-capacity pruning.
    """
    qs = wing_primes(A)
    smalls = [q for q in qs if q <= 13]
    bigs = tuple(sorted((q for q in qs if q > 13), reverse=True))
    masks = {q: _phase_masks(q, g) for q in qs}
    static_cap = {q: max(m.bit_count() for m in masks[q]) for q in qs}
    sc_bigs = sum(static_cap[q] for q in bigs)
    full = (1 << g) - 1
    inv = {q: inv6(q) for q in qs}
    nodes = 0

    def dfs(U, rem):
        nonlocal nodes
        nodes += 1
        if deadline is not None and (nodes & 0xFFF) == 0 and time.time() > deadline:
            raise SolverTimeout
        if U == 0:
            return []
        if not rem:
            return None
        # exact residual capacity prune
        need = U.bit_count()
        tot = 0
        for q in rem:
            best = 0
            for m in masks[q]:
                b = (U & m).bit_count()
                if b > best:
                    best = b
            tot += best
            if tot >= need:
                break
        if tot < need:
            return None
        o = (U & -U).bit_length()  # smallest uncovered offset (1-based)
        for idx in range(len(rem)):
            q = rem[idx]
            rem2 = rem[:idx] + rem[idx + 1:]
            i6 = inv[q]
            t1 = (o - i6) % q
            for tq in ((t1, (o + i6) % q) if (2 * i6) % q else (t1,)):
                sub = dfs(U & ~masks[q][tq], rem2)
                if sub is not None:
                    return [(q, tq)] + sub
        return None

    # enumerate small-clock phases; mirror reduction (o -> g+1-o maps phase t -> (g+1-t) mod q)
    if not smalls:
        sol = dfs(full, bigs)
        return (sol is not None), sol, nodes
    q0 = smalls[0]
    reps0 = [t for t in range(q0) if t <= (g + 1 - t) % q0]
    rest = smalls[1:]

    def small_loop(i, acc, placed):
        nonlocal nodes
        if i == len(rest):
            U0 = full & ~acc
            if U0 == 0:
                return list(placed)
            if U0.bit_count() > sc_bigs:
                return None
            sub = dfs(U0, bigs)
            if sub is not None:
                return list(placed) + sub
            return None
        q = rest[i]
        for t in range(q):
            r = small_loop(i + 1, acc | masks[q][t], placed + [(q, t)])
            if r is not None:
                return r
        return None

    for t0 in reps0:
        sol = small_loop(0, masks[q0][t0], [(q0, t0)])
        if sol is not None:
            return True, sol, nodes
    return False, None, nodes


def crt_pair(r1, m1, r2, m2):
    """x = r1 mod m1, x = r2 mod m2 (coprime)."""
    inv = pow(m1, -1, m2)
    return (r1 + m1 * ((r2 - r1) * inv % m2)) % (m1 * m2), m1 * m2


def certificate_r(placed, M, A):
    """From placed phases (q, t_q) reconstruct clean residue r with the gap
    r -> r+M+1 (offsets 1..M struck, 0 and M+1 clean). Verified by trial division."""
    qs = wing_primes(A)
    r, mod = 0, 1
    for q, t in placed:
        r, mod = crt_pair(r, mod, (-t) % q, q)
    P = primorial(A)
    k = 0
    while True:
        cand = r + k * mod
        if cand >= P:
            cand %= P
        ok = True
        for off in (0, M + 1):
            x = cand + off
            for q in qs:
                if (6 * x - 1) % q == 0 or (6 * x + 1) % q == 0:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            r = cand
            break
        k += 1
        if k * mod > P:
            raise RuntimeError("no clean-endpoint completion found (should not happen)")
    # full verification
    for off in range(1, M + 1):
        x = r + off
        assert any((6 * x - 1) % q == 0 or (6 * x + 1) % q == 0 for q in qs), \
            f"offset {off} not struck -- certificate invalid"
    return r


def exact_G_solver(A, g_start, deadline=None):
    """Climb g upward from g_start until UNSAT; returns (G, placed_at_max, nodes_unsat)."""
    g = g_start
    last_sol = None
    while True:
        t0 = time.time()
        sat, sol, nodes = decision(g, A, deadline)
        log(f"  {stamp()} decision(A={A}, g={g}): {'SAT' if sat else 'UNSAT'} "
            f"nodes={nodes:,} [{time.time()-t0:.1f}s]")
        if sat:
            last_sol = (g, sol)
            g += 1
        else:
            return g, last_sol, nodes


# ================================================================= TASK 1

def task1():
    log("=" * 78)
    log("TASK 1 -- reduced witness lists for Lean kernel certificates (A = 17, 19)")
    log("=" * 78)
    for A in (17, 19):
        P = primorial(A)
        L = (A * A) // 7
        pos = clean_positions(A)
        # clean residues in [1, P]: drop residue 0, append P (Clean(A,P) holds: 6P+-1 = -+1 mod q)
        assert pos[0] == 0
        cl = np.concatenate([pos[1:], [P]]).astype(np.int64)
        gaps = np.diff(cl)
        wrap = int(cl[0])  # (first + P) - last = first, since last == P
        Gmax = max(int(gaps.max()), wrap)
        assert Gmax == KNOWN_G[A], f"G({A}) mismatch: {Gmax} vs known {KNOWN_G[A]}"
        log(f"\nA={A}: P={P:,}  clean in [1,P]: {len(cl):,}  max cyclic gap = {Gmax} "
            f"(= known G({A})) OK   L = floor(A^2/7) = {L}")

        # greedy reduction: farthest clean residue within distance L
        cl_ext = np.concatenate([cl, cl + P])
        first = int(cl[0])
        target = first + P
        wit = [first]
        cur = first
        while cur + L < target:
            idx = int(np.searchsorted(cl_ext, cur + L, side="right")) - 1
            nxt = int(cl_ext[idx])
            assert nxt > cur, "gap > L in clean list -- impossible since G(A) <= L"
            wit.append(nxt)
            cur = nxt
        wrap_gap = target - cur
        w = np.array(wit, dtype=np.int64)
        assert w.max() <= P and w.min() >= 1
        # verify every witness is clean and gaps <= L
        assert np.all(np.isin(w, cl)), "witness not clean"
        dg = np.diff(w)
        max_int = int(dg.max())
        assert max_int <= L and wrap_gap <= L
        log(f"  reduced witness chain: count={len(w):,} (info-lower-bound ceil(P/L)={-(-P // L):,})")
        log(f"  max internal gap={max_int}  wraparound gap={wrap_gap}  first={w[0]}  last={w[-1]}")

        fname = f"tools/witness_a{A}.lean.txt"
        with open(fname, "w", encoding="ascii") as f:
            f.write(f"-- A={A} P={P} L={L} count={len(w)} maxgap={max(max_int, wrap_gap)} "
                    f"(reduced clean-witness chain, cyclic gaps <= L; wraparound gap {wrap_gap})\n")
            line = ""
            for i, v in enumerate(w):
                tok = str(int(v)) + ("," if i < len(w) - 1 else "")
                if len(line) + len(tok) > 100:
                    f.write(line + "\n")
                    line = ""
                line += tok
            if line:
                f.write(line + "\n")
        log(f"  wrote {fname}")
        if A == 17:
            with open("tools/witness_a17_meta.txt", "w", encoding="ascii") as f:
                f.write(f"A=17 reduced witness chain (clean residues in [1,P], cyclic cover step L={L})\n")
                f.write(f"count={len(w)}\n")
                f.write(f"max_internal_gap={max_int}\n")
                f.write(f"wraparound_gap={wrap_gap}\n")
                f.write(f"first={int(w[0])}\n")
                f.write(f"last={int(w[-1])}\n")
            log("  wrote tools/witness_a17_meta.txt")


# ================================================================= TASK 2

def task2(budget):
    log("")
    log("=" * 78)
    log("TASK 2 -- exact G(A) for A = 29, 31, 37")
    log("=" * 78)
    results = dict(KNOWN_G)

    # -- solver validation on known values
    log("\nsolver validation against known exact G (SAT at G-1 must hold, UNSAT at G):")
    for A in (13, 17, 19, 23):
        G = KNOWN_G[A]
        sat1, _, n1 = decision(G - 1, A)
        t0 = time.time()
        sat2, _, n2 = decision(G, A)
        dt = time.time() - t0
        verdict = "OK" if (sat1 and not sat2) else "FAIL"
        log(f"  A={A}: decision({G-1})={'SAT' if sat1 else 'UNSAT'} (nodes {n1:,}), "
            f"decision({G})={'SAT' if sat2 else 'UNSAT'} (nodes {n2:,}, {dt:.1f}s) -> {verdict}")
        assert verdict == "OK"

    # -- A = 29: exact by full-period scan, cross-checked by solver
    log("\nA=29: full-period chunked scan (P_29 = 1,078,282,205):")
    P29 = primorial(29)
    G29, starts29, n29, _, _ = chunked_gap_scan(29, P29, label=" (FULL period)")
    log(f"  EXACT G(29) = {G29}, {len(starts29)} extremal start(s): {starts29[:8]}"
        f"{' ...' if len(starts29) > 8 else ''}")
    log("  solver cross-check:")
    sat1, _, n1 = decision(G29 - 1, 29)
    sat2, _, n2 = decision(G29, 29)
    log(f"  decision({G29-1})={'SAT' if sat1 else 'UNSAT'} (nodes {n1:,}), "
        f"decision({G29})={'SAT' if sat2 else 'UNSAT'} (nodes {n2:,}) -> "
        f"{'OK (solver == scan)' if sat1 and not sat2 else 'FAIL'}")
    assert sat1 and not sat2
    results[29] = G29

    # -- A = 31, 37: partial scan for a lower bound, then exact solver climb
    for A in (31, 37):
        log(f"\nA={A}: partial scan for lower bound, then exact branch-and-bound:")
        lb_gap, lb_starts, _, _, _ = chunked_gap_scan(A, 300_000_000, label=" (partial)")
        deadline = time.time() + budget
        try:
            G, last_sol, nodes_unsat = exact_G_solver(A, lb_gap, deadline)
            gM, placed = last_sol if last_sol else (lb_gap - 1, None)
            if placed is not None:
                r = certificate_r(placed, gM, A)
                log(f"  EXACT G({A}) = {G}  (UNSAT at g={G} exhausts the phase space; "
                    f"SAT at g={G-1})")
                log(f"  certificate: clean r={r}, offsets 1..{gM} all struck, r and r+{G} clean "
                    f"(verified by trial division); placed phases: {placed}")
            else:
                log(f"  EXACT G({A}) = {G} (scan already realised G-1 = {lb_gap-1}? unusual path)")
            results[A] = G
        except SolverTimeout:
            log(f"  TIMEOUT after {budget}s: bracket G({A}) in [{lb_gap}, ???] -- "
                f"lower bound from scan; upper bound NOT established")
            results[A] = None

    # -- margins table
    log("\n" + "-" * 78)
    log("margins table: G(A) vs A^2/7 (wall constant) and A^2/6")
    log("-" * 78)
    log(f"  {'A':>3} {'G(A)':>6} {'A^2/7':>8} {'G/(A^2/7)':>10} {'A^2/6':>8} "
        f"{'G/(A^2/6)':>10}  {'G<=A^2/7':>9}")
    violation = False
    for A in PRIMES_SMALL:
        G = results.get(A)
        if G is None:
            log(f"  {A:>3} {'??':>6}  (bracket only, see above)")
            continue
        w7 = A * A / 7
        w6 = A * A / 6
        ok7 = 7 * G <= A * A  # exact integer comparison
        if not ok7:
            violation = True
        log(f"  {A:>3} {G:>6} {w7:>8.2f} {G / w7:>10.3f} {w6:>8.2f} {G / w6:>10.3f}  "
            f"{'YES' if ok7 else '*** VIOLATED ***':>9}")
    if violation:
        log("\n*** MAJOR FINDING: G(A) <= A^2/7 VIOLATED -- the wall constant must change ***")
    else:
        log("\nG(A) <= A^2/7 holds for every exactly-known A -- wall constant A^2/7 stands.")
    return results, starts29


# ================================================================= TASK 3

def clock_pattern(r, G, q):
    """Offsets o in [1, G-1] struck by clock q for the window after clean residue r."""
    a = inv6(q)
    return tuple(o for o in range(1, G) if (r + o) % q in (a % q, (q - a) % q))


def portrait(r, G, A):
    return tuple((q, clock_pattern(r, G, q)) for q in wing_primes(A))


def avg_rank(x):
    uniq, inv, counts = np.unique(x, return_inverse=True, return_counts=True)
    csum = np.cumsum(counts)
    start = csum - counts
    return ((start + 1 + csum) / 2.0)[inv]


def spearman(x, y):
    rx, ry = avg_rank(x), avg_rank(y)
    rx -= rx.mean()
    ry -= ry.mean()
    return float((rx * ry).sum() / np.sqrt((rx * rx).sum() * (ry * ry).sum()))


def gap_at(ms, pos, P):
    """Length of the clean-gap [pos[i], pos[i+1]) containing each m (cyclic)."""
    idx = np.searchsorted(pos, ms, side="right")
    left = pos[idx - 1]
    right = np.where(idx < len(pos), pos[np.minimum(idx, len(pos) - 1)], pos[0] + P)
    return (right - left).astype(np.int64)


def window_counts(rs, W, A):
    """Strike-multiplicity per offset: rs (n,) window starts -> counts (n, W) over offsets 1..W."""
    rs = np.asarray(rs, dtype=np.int64).reshape(-1, 1)
    offs = np.arange(1, W + 1, dtype=np.int64).reshape(1, -1)
    x = rs + offs
    c = np.zeros(x.shape, dtype=np.int16)
    for q in wing_primes(A):
        a = inv6(q)
        rem = x % q
        c += ((rem == a) | (rem == (q - a) % q)).astype(np.int16)
    return c


def task3(scan29_starts=None):
    log("")
    log("=" * 78)
    log("TASK 3 -- extremal phase portraits and the transfer hypothesis (A <= 23)")
    log("=" * 78)
    A_LIST = [5, 7, 11, 13, 17, 19, 23]
    info = {}
    for A in A_LIST:
        P = primorial(A)
        pos = clean_positions(A)
        G, starts = max_gap_starts(pos, P)
        assert G == KNOWN_G[A]
        # mirror orbits: r -> (P - r - G) mod P
        sset = set(starts)
        orbits = []
        seen = set()
        for r in starts:
            if r in seen:
                continue
            rm = (P - r - G) % P
            assert rm in sset, f"mirror partner of extremal start missing (A={A}, r={r})"
            seen.add(r)
            seen.add(rm)
            orbits.append((r, rm))
        info[A] = dict(P=P, pos=pos, G=G, starts=starts, orbits=orbits)
        log(f"\nA={A}: P={P:,}  G={G}  extremal starts: {len(starts)}  "
            f"mirror orbits: {len(orbits)} "
            f"({sum(1 for a, b in orbits if a == b)} palindromic)")
        show = starts if len(starts) <= 6 else starts[:6]
        for r in show:
            pat = portrait(r, G, A)
            pat_s = "  ".join(f"q{q}:{','.join(map(str, off)) if off else '-'}" for q, off in pat)
            log(f"    r={r}: {pat_s}")
        if len(starts) > 6:
            log(f"    ... ({len(starts) - 6} more)")

    # ---- (a) embedding: extremal window of A' vs the gap ranking of scale A
    log("\n(a) embedding hypothesis: A'-extremal window start rho = r' mod P_A;")
    log("    entry gap = distance rho -> next Clean(A) residue; is it top-decile among A-gaps?")
    log(f"  {'pair':>10} {'r_ext(A_hi)':>14} {'entry gap':>9} {'G(A_lo)':>7} {'p90 thr':>8} "
        f"{'pctile':>7} {'top10%?':>8} {'max inner gap':>13}")
    pairs = list(zip(A_LIST[:-1], A_LIST[1:]))
    verdict_a = {}
    for A, A2 in pairs:
        P, pos = info[A]["P"], info[A]["pos"]
        gaps_all = cyclic_gaps(pos, P)
        thr = int(np.percentile(gaps_all, 90, method="lower"))
        n = len(gaps_all)
        allin = True
        starts2 = info[A2]["starts"]
        G2 = info[A2]["G"]
        for r2 in starts2:
            rho = r2 % P
            i = int(np.searchsorted(pos, rho, side="right"))
            assert int(pos[i - 1]) == rho, "A'-clean start must be clean at scale A"
            nxt = int(pos[i]) if i < len(pos) else int(pos[0]) + P
            entry = nxt - rho
            # percentile rank of entry among all A-gaps
            pct = 100.0 * (np.count_nonzero(gaps_all < entry)
                           + 0.5 * np.count_nonzero(gaps_all == entry)) / n
            top = entry >= thr
            allin &= top
            # max A-gap fully inside the A'-window [rho, rho+G2]
            j0 = int(np.searchsorted(pos, rho))
            j1 = int(np.searchsorted(pos, rho + G2, side="right"))
            inner = pos[j0:j1]
            if len(inner) >= 2:
                maxin = int(np.diff(inner).max())
            else:
                maxin = entry  # no interior clean residue at scale A
            log(f"  ({A:>2},{A2:>2}) {r2:>14,} {entry:>9} {info[A]['G']:>7} {thr:>8} "
                f"{pct:>6.1f}% {'YES' if top else 'no':>8} {maxin:>13}")
        verdict_a[(A, A2)] = allin
    if scan29_starts:
        A, A2, G2 = 23, 29, None
        P, pos = info[23]["P"], info[23]["pos"]
        gaps_all = cyclic_gaps(pos, P)
        thr = int(np.percentile(gaps_all, 90, method="lower"))
        n = len(gaps_all)
        for r2 in scan29_starts[:4]:
            rho = r2 % P
            i = int(np.searchsorted(pos, rho, side="right"))
            nxt = int(pos[i]) if i < len(pos) else int(pos[0]) + P
            entry = nxt - rho
            pct = 100.0 * (np.count_nonzero(gaps_all < entry)
                           + 0.5 * np.count_nonzero(gaps_all == entry)) / n
            log(f"  (23,29) {r2:>14,} {entry:>9} {info[23]['G']:>7} {thr:>8} "
                f"{pct:>6.1f}% {'YES' if entry >= thr else 'no':>8} {'(bonus row)':>13}")
    ok_pairs = [p for p, v in verdict_a.items() if v]
    log(f"  verdict (a): embedding holds for {len(ok_pairs)}/{len(pairs)} pairs: "
        f"{'ALL -- embedding survives' if len(ok_pairs) == len(pairs) else 'FAILS on ' + str([p for p, v in verdict_a.items() if not v])}")

    # ---- (b) statistical transfer: Spearman(gap_A(m), gap_A'(m)) over 1e6 samples
    log("\n(b) statistical transfer: Spearman rank corr of gap lengths at the same residues")
    rng = np.random.default_rng(20260710)
    N = 1_000_000
    log(f"  {'pair':>10} {'rho_S':>8} {'~z':>8}")
    rho_list = {}
    for A, A2 in pairs:
        P, pos = info[A]["P"], info[A]["pos"]
        P2, pos2 = info[A2]["P"], info[A2]["pos"]
        ms = rng.integers(0, P2, N)
        gA = gap_at(ms % P, pos, P)
        gA2 = gap_at(ms, pos2, P2)
        rho = spearman(gA, gA2)
        z = rho * np.sqrt(N - 1)
        rho_list[(A, A2)] = rho
        log(f"  ({A:>2},{A2:>2}) {rho:>8.4f} {z:>8.0f}")
    log("  verdict (b): rank transfer strictly positive on all pairs"
        if all(v > 0 for v in rho_list.values())
        else "  verdict (b): MIXED signs -- see table")

    # ---- (c) waste profiles: multiplicity in extremal vs random windows
    log("\n(c) waste profiles: strike multiplicity per offset, extremal vs random windows")
    log(f"  {'A':>3} {'W':>4} | extremal: {'cover':>6} {'mult':>6} {'dbl+/W':>7} | "
        f"random(20k): {'cover':>6} {'mult|cov':>8} {'dbl+/cov':>8} {'z(dbl)':>7}")
    rng2 = np.random.default_rng(7)
    for A in A_LIST:
        P, G, starts = info[A]["P"], info[A]["G"], info[A]["starts"]
        W = G - 1
        ce = window_counts(starts, W, A)  # extremal windows: all offsets covered
        assert np.all(ce >= 1), "extremal window has uncovered offset?!"
        mult_e = float(ce.mean())
        dbl_e = float((ce >= 2).mean())
        R = 20000
        rr = rng2.integers(0, P, R)
        cr = window_counts(rr, W, A)
        cover_r = float((cr >= 1).mean())
        cov_mask = cr >= 1
        mult_r = float(cr[cov_mask].mean())
        dbl_r_frac = float((cr >= 2).sum() / max(cov_mask.sum(), 1))
        # z-score for extremal dbl fraction vs random-window distribution of per-window dbl fraction
        dblw = (cr >= 2).mean(axis=1)
        mu, sd = float(dblw.mean()), float(dblw.std())
        z = (dbl_e - mu) / sd if sd > 0 else float("nan")
        log(f"  {A:>3} {W:>4} | {1.0:>16.3f} {mult_e:>6.3f} {dbl_e:>7.3f} | "
            f"{cover_r:>19.3f} {mult_r:>8.3f} {dbl_r_frac:>8.3f} {z:>7.1f}")
        # per-clock redundancy in extremal windows
        per = []
        for q in wing_primes(A):
            a = inv6(q)
            tot_s, tot_d = 0, 0
            for r in starts:
                offs = clock_pattern(r, G, q)
                tot_s += len(offs)
                cnt = window_counts([r], W, A)[0]
                tot_d += sum(1 for o in offs if cnt[o - 1] >= 2)
            per.append(f"q{q}:{tot_d}/{tot_s}")
        log(f"        per-clock redundant/strikes over all extremal windows: {'  '.join(per)}")
    return info


# ================================================================= main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parts", default="1,2,3")
    ap.add_argument("--budget", type=int, default=900, help="per-decision solver budget (s)")
    ap.add_argument("--log", default="tools/gap_extremal_run1.log")
    args = ap.parse_args()
    sys.stdout = Tee(args.log)
    parts = set(args.parts.split(","))
    log("GAP EXTREMAL HARNESS -- SG0-B gate (extremal gap geometry of the twin-Jacobsthal wall)")
    log(f"date: 2026-07-10   numpy {np.__version__}   parts: {sorted(parts)}")
    log(f"known exact G(A): {KNOWN_G} (short_survivor_run1.log)")
    scan29_starts = None
    if "1" in parts:
        task1()
    if "2" in parts:
        _, scan29_starts = task2(args.budget)
    if "3" in parts:
        task3(scan29_starts=scan29_starts)
    log(f"\n{stamp()} done.")


if __name__ == "__main__":
    main()
