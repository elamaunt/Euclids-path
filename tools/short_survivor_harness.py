# short_survivor_harness.py -- Line C recon: the exact shape of the scale wall.
#
# Lean-proved kernel (ShortSurvivor): Clean(A, m) with 6m+1 <= A^2 forces m to
# be a twin center -- any composite wing would carry a factor <= sqrt(6m+1) <= A.
# The wall of Line C: prove a short survivor EXISTS above every horizon.
# This harness quantifies the wall's true shape:
#   (1) N_short(M0) = #{m in (M0, (A^2-1)/6] : Clean(A, m)} for A = A(M0) the
#       smallest prime with A^2 > 6(M0+1), over a log grid M0 <= 10^7; compared
#       against the Hardy-Littlewood-type density prod_{5<=q<=A}(1 - 2/q) and a
#       fitted c * |window| / log^2 A.  Is N_short ever 0?
#   (2) Largest clean-gaps: (a) empirical largest gap between consecutive
#       Clean(A, .) centers m <= 10^7 for A in {13, 31, 101, 331}; (b) EXACT
#       largest cyclic gap G(A) between clean residues mod P_A = prod_{5<=q<=A} q
#       by scanning one full period, for A in {5,...,23} (P_23 ~ 3.7e7).
#       Verdict table: does G(A) <= A^2/6 hold?  (If yes: any window of length
#       G(A) contains a clean center; combined with 6m+1 <= A^2 this yields
#       twins only BELOW A^2/6 -- a finite range per A.  The escalation in A is
#       where the wall lives; exact G(A) calibrates the escalation.)
#       Growth fits: G(A) vs c*(log P_A)^2 and vs k*(e^gamma * log A)^2.
#   (3) Primorial-anchor honesty: log(P_A) / log(A^2) for A up to 331 -- the
#       shortfall factor showing why primorial-height clean anchors (~P_A)
#       cannot feed the short-window lemma (needs height <= A^2/6).
#
# Output: fixed-width console tables. Feeds tools/LAWS_ordered_exponent.md.

import numpy as np
import math
import time

M_GAP = 10**7                       # empirical gap scan range
A_GAP = [13, 31, 101, 331]          # scales for empirical gap scan
A_EXACT = [5, 7, 11, 13, 17, 19, 23]  # scales for the exact full-period scan
GRID_EXPONENTS = [k / 6 for k in range(12, 43)]  # 10^2 .. 10^7, step 10^(1/6)
EULER_GAMMA = 0.5772156649015329


def prime_sieve(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


PRIMES_10K = [int(p) for p in np.flatnonzero(prime_sieve(10**4))]


def next_prime_sq_above(x):
    """Smallest prime A with A^2 > x."""
    for p in PRIMES_10K:
        if p * p > x:
            return p
    raise ValueError("prime table too small")


def wing_primes(A):
    return [q for q in PRIMES_10K if 5 <= q <= A]


def clean_mask_window(lo, hi, A):
    """Boolean mask over m in [lo, hi]: Clean(A, m)."""
    W = hi - lo + 1
    mask = np.ones(W, dtype=bool)
    for q in wing_primes(A):
        aL = pow(6, -1, q)
        for a in (aL, (q - aL) % q):
            first = (a - lo) % q
            mask[first::q] = False
    return mask


def crt_density(A):
    d = 1.0
    for q in wing_primes(A):
        d *= (q - 2) / q
    return d


def is_prime_mr(n):
    """Deterministic Miller-Rabin for n < 3.3e24 (bases 2..37)."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# ---------- part 1: N_short over a log grid ----------

def part1():
    print("-" * 78)
    print("PART 1 -- short-window survivor counts N_short(M0) over a log grid")
    print("-" * 78)
    print("A(M0) = smallest prime with A^2 > 6(M0+1); window (M0, (A^2-1)/6];")
    print("dens = prod_{5<=q<=A}(1-2/q); pred = |W| * dens; c_i = N * ln^2(A)/|W|\n")
    hdr = (f"{'M0':>10}{'A':>7}{'|W|':>9}{'N_short':>9}{'pred':>10}"
           f"{'N/pred':>8}{'dens*ln^2A':>12}{'c_i':>8}")
    print(hdr)
    rows = []
    zero_rows = []
    for e in GRID_EXPONENTS:
        M0 = round(10**e)
        A = next_prime_sq_above(6 * (M0 + 1))
        lo, hi = M0 + 1, (A * A - 1) // 6
        mask = clean_mask_window(lo, hi, A)
        N = int(mask.sum())
        W = hi - lo + 1
        dens = crt_density(A)
        pred = W * dens
        lnA2 = math.log(A) ** 2
        c_i = N * lnA2 / W
        rows.append((M0, A, W, N, pred, dens * lnA2, c_i))
        if N == 0:
            zero_rows.append((M0, A, hi))
        print(f"{M0:>10}{A:>7}{W:>9}{N:>9}{pred:>10.2f}"
              f"{N/pred if pred > 0 else float('nan'):>8.3f}"
              f"{dens*lnA2:>12.4f}{c_i:>8.4f}")
    zeros = len(zero_rows)
    Ws = np.array([r[2] for r in rows], dtype=np.float64)
    Ns = np.array([r[3] for r in rows], dtype=np.float64)
    lnA2s = np.array([math.log(r[1]) ** 2 for r in rows])
    x = Ws / lnA2s
    c_fit = float((Ns * x).sum() / (x * x).sum())  # least squares N ~ c * W/ln^2 A
    print(f"\nleast-squares fit N_short ~ c * |W| / ln^2(A):  c = {c_fit:.4f}")
    print(f"grid points with N_short = 0: {zeros} / {len(rows)}"
          + ("   (never zero -- the truth is plentiful, the wall is proof)"
             if zeros == 0 else "   <-- ZERO WINDOWS EXIST, detail below"))
    for M0, A, hi in zero_rows:
        mt = M0 + 1
        while not (is_prime_mr(6 * mt - 1) and is_prime_mr(6 * mt + 1)):
            mt += 1
        A_need = next_prime_sq_above(6 * mt)  # smallest prime A' with A'^2 > 6*mt,
        # then (A'^2-1)/6 >= mt and the window (M0, .] reaches the twin
        esc = len([q for q in PRIMES_10K if A < q <= A_need])
        print(f"  zero window at M0={M0} (A={A}, hi={hi}): first twin above M0 "
              f"is m={mt} (pair {6*mt-1},{6*mt+1}), missed by {mt - hi} centers; "
              f"needed A'={A_need} ({esc} primes up the escalation)")
    return rows


# ---------- part 2: clean gaps ----------

def part2a():
    print("\n" + "-" * 78)
    print(f"PART 2a -- largest empirical clean-gap, centers m <= {M_GAP:.0e}")
    print("-" * 78)
    print(f"{'A':>5}{'#clean':>10}{'density':>10}{'CRT dens':>10}"
          f"{'max gap':>9}{'at m':>10}{'A^2/6':>10}{'P_A (period)':>16}")
    out = {}
    for A in A_GAP:
        t0 = time.time()
        mask = clean_mask_window(1, M_GAP, A)
        pos = np.flatnonzero(mask) + 1
        gaps = np.diff(pos)
        gi = int(np.argmax(gaps))
        G = int(gaps[gi])
        P_A = 1
        for q in wing_primes(A):
            P_A *= q
        out[A] = G
        print(f"{A:>5}{pos.size:>10}{pos.size/M_GAP:>10.5f}{crt_density(A):>10.5f}"
              f"{G:>9}{pos[gi]:>10}{A*A/6:>10.1f}{P_A:>16.3e}"
              f"   [{time.time()-t0:.1f}s]")
    print("note: for A = 101, 331 the period P_A >> 10^7, so these gaps are")
    print("LOWER bounds on the true worst case G(A); for A = 13 the scan covers")
    print("~2000 full periods, so it must reproduce the exact G(13) below.")
    return out


def exact_gap(A):
    """Exact largest cyclic gap between clean residues mod P_A (full period)."""
    P = 1
    for q in wing_primes(A):
        P *= q
    mask = np.ones(P, dtype=bool)
    for q in wing_primes(A):
        aL = pow(6, -1, q)
        mask[aL::q] = False
        mask[(q - aL) % q::q] = False
    pos = np.flatnonzero(mask)
    gaps = np.diff(pos)
    gi = int(np.argmax(gaps))
    G_lin = int(gaps[gi])
    wrap = int(P - pos[-1] + pos[0])
    if wrap > G_lin:
        G, loc = wrap, int(pos[-1])
    else:
        G, loc = G_lin, int(pos[gi])
    return P, G, loc, pos.size


def part2b(empirical):
    print("\n" + "-" * 78)
    print("PART 2b -- EXACT worst-case clean gap G(A) over one full period P_A")
    print("-" * 78)
    print(f"{'A':>4}{'P_A':>12}{'#clean/P':>10}{'G(A)':>7}{'gap at':>10}"
          f"{'A^2/6':>9}{'G<=A^2/6':>10}{'G/(A^2/6)':>11}"
          f"{'c=G/ln^2 P':>12}{'k=G/(e^g lnA)^2':>17}")
    verdict_all = True
    results = []
    for A in A_EXACT:
        t0 = time.time()
        P, G, loc, ncl = exact_gap(A)
        bound = A * A / 6
        ok = G <= bound
        verdict_all &= ok
        c = G / math.log(P) ** 2
        k = G / (math.exp(EULER_GAMMA) * math.log(A)) ** 2
        results.append((A, P, G, bound, ok))
        print(f"{A:>4}{P:>12}{ncl/P:>10.5f}{G:>7}{loc:>10}{bound:>9.2f}"
              f"{'YES' if ok else 'NO':>10}{G/bound:>11.3f}{c:>12.4f}{k:>17.3f}"
              f"   [{time.time()-t0:.1f}s]")
    if 13 in empirical:
        _, _, G13, _, _ = [r for r in results if r[0] == 13][0]
        tag = "MATCH" if empirical[13] == G13 else "MISMATCH!"
        print(f"\ncross-check: empirical max gap at A=13 over 10^7 = "
              f"{empirical[13]}, exact G(13) = {G13} -> {tag}")
    print()
    if verdict_all:
        print("*** EXACT-CANDIDATE: G(A) <= A^2/6 holds for EVERY tested A in "
              f"{A_EXACT} ***")
        print("*** i.e. every window of A^2/6 consecutive centers contains a "
              "Clean(A,.) center -- a kernel-checkable exact law per fixed A. ***")
        print("*** CAVEAT (scale wall): fixed-A version + ShortSurvivor only "
              "yields twins below A^2/6, a finite range; the escalation in A is "
              "the actual wall. ***")
    else:
        bad = [(A, G, b) for A, P, G, b, ok in results if not ok]
        print(f"G(A) <= A^2/6 FAILS at: {bad}")
    return results


# ---------- part 3: primorial-anchor honesty ----------

def part3():
    print("\n" + "-" * 78)
    print("PART 3 -- primorial-anchor honesty: log(P_A) vs log(A^2)")
    print("-" * 78)
    show = [5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 53, 71, 101, 131, 173, 229,
            283, 331]
    print(f"{'A':>5}{'log P_A':>10}{'log A^2':>10}{'ratio':>8}"
          f"{'P_A / (A^2/6)':>16}")
    logP = 0.0
    for q in wing_primes(331):
        logP += math.log(q)
        if q in show:
            r = logP / math.log(q * q)
            excess = logP - math.log(q * q / 6)
            print(f"{q:>5}{logP:>10.3f}{math.log(q*q):>10.3f}{r:>8.2f}"
                  f"{'10^%.1f' % (excess / math.log(10)):>16}")
    print("\nhonest sentence: the primorial clean anchor lives at height ~P_A,")
    print("exponentially (factor ~10^(theta(A)/ln 10)) above the A^2/6 ceiling that")
    print("the short-window lemma needs -- the anchor can never feed Line C directly.")


def main():
    print("=" * 78)
    print("SHORT SURVIVOR HARNESS -- Line C recon (the exact shape of the scale wall)")
    print("=" * 78)
    t0 = time.time()
    part1()
    emp = part2a()
    part2b(emp)
    part3()
    print(f"\ndone in {time.time()-t0:.1f}s.")


if __name__ == "__main__":
    main()
