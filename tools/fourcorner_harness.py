import numpy as np
from fractions import Fraction as F

def primes_upto(n):
    s = np.ones(n+1, dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def inv6(p):  # 6^{-1} mod p
    return pow(6, -1, p)

def block(k, oldfree=False):
    N = 1<<k
    X = 12*N
    A = int(round(X**0.25))
    P = primes_upto(A*A)
    layer = [int(p) for p in P if A < p <= A*A]
    small = [int(p) for p in P if 5 <= p <= A]   # old clocks p<=A (exclude 2,3 which never divide 6m±1)
    Nlen = N  # m in [N, 2N)
    rminus = np.zeros(Nlen, dtype=np.int16)
    rplus  = np.zeros(Nlen, dtype=np.int16)
    base = N
    def mark(plist, arr, sign):
        for p in plist:
            i6 = inv6(p)
            r = (sign*i6) % p            # m ≡ sign*6^{-1} mod p
            m0 = base + ((r - base) % p) # smallest m>=N with m≡r
            arr[m0-base::p] += 1
    mark(layer, rminus, +1)   # p | 6m-1  <=> m ≡ 6^{-1}
    mark(layer, rplus,  -1)   # p | 6m+1  <=> m ≡ -6^{-1}
    mask = np.ones(Nlen, dtype=bool)
    if oldfree:
        om = np.zeros(Nlen, dtype=np.int16); op = np.zeros(Nlen, dtype=np.int16)
        mark(small, om, +1); mark(small, op, -1)
        mask = (om==0) & (op==0)
    rm = rminus[mask]; rp = rplus[mask]
    def cnt(i,j): return int(np.sum((rm==i)&(rp==j)))
    N00=cnt(0,0); N03=cnt(0,3); N30=cnt(3,0); N33=cnt(3,3)
    return dict(k=k,A=A,N00=N00,N03=N03,N30=N30,N33=N33,total=int(mask.sum()))

print("=== ALL m in [N,2N) (no old-free restriction) ===")
print(f"{'k':>3}{'A':>6}{'N00':>12}{'N03':>10}{'N30':>10}{'N33':>9}{'R_fc':>10}{'fc<1':>6}")
for k in range(21,27):
    r=block(k,oldfree=False)
    Rfc=F(r['N00']*r['N33'], r['N03']*r['N30']) if r['N03']*r['N30']>0 else F(0)
    print(f"{k:>3}{r['A']:>6}{r['N00']:>12}{r['N03']:>10}{r['N30']:>10}{r['N33']:>9}{float(Rfc):>10.5f}{str(r['N00']*r['N33']<r['N03']*r['N30']):>6}")

print()
print("=== OLD-FREE carrier (no prime p<=A divides either side) ===")
print(f"{'k':>3}{'A':>6}{'N00':>12}{'N03':>10}{'N30':>10}{'N33':>9}{'R_fc':>10}{'fc<1':>6}")
for k in range(21,27):
    r=block(k,oldfree=True)
    Rfc=F(r['N00']*r['N33'], r['N03']*r['N30']) if r['N03']*r['N30']>0 else F(0)
    print(f"{k:>3}{r['A']:>6}{r['N00']:>12}{r['N03']:>10}{r['N30']:>10}{r['N33']:>9}{float(Rfc):>10.5f}{str(r['N00']*r['N33']<r['N03']*r['N30']):>6}")
