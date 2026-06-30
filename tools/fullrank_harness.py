import numpy as np
from fractions import Fraction as F

def primes_upto(n):
    s = np.ones(n+1, dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def full_matrix(k, RMAX=6, oldfree=True):
    N=1<<k; X=12*N; A=int(round(X**0.25)); P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]
    base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16)
    def mark(plist,arr,sign):
        for p in plist:
            i6=pow(6,-1,p); r=(sign*i6)%p; m0=base+((r-base)%p); arr[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1)
    if oldfree:
        om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
        mark(small,om,1); mark(small,op,-1); mask=(om==0)&(op==0)
        rm=rm[mask]; rp=rp[mask]
    M=np.zeros((RMAX,RMAX),dtype=np.int64)
    rmc=np.clip(rm,0,RMAX-1); rpc=np.clip(rp,0,RMAX-1)
    idx=rmc.astype(np.int64)*RMAX+rpc.astype(np.int64)
    flat=np.bincount(idx,minlength=RMAX*RMAX)
    return A, flat.reshape(RMAX,RMAX)

for k in [20,22,24,26]:
    A,Mx=full_matrix(k)
    print(f"\n===== k={k}, A={A}  (rows r-, cols r+) =====")
    for i in range(5):
        print("  "+" ".join(f"{Mx[i][j]:>9d}" for j in range(5)))
    # log-submodularity: all adjacent 2x2 minors  D_ij = N_ij*N_{i+1,j+1} - N_{i,j+1}*N_{i+1,j}
    print("  2x2 minors  N_ij*N_{i+1,j+1} - N_{i,j+1}*N_{i+1,j}  (want <=0 = neg.assoc / four-corner):")
    allneg=True
    for i in range(4):
        line=[]
        for j in range(4):
            D=int(Mx[i][j])*int(Mx[i+1][j+1]) - int(Mx[i][j+1])*int(Mx[i+1][j])
            line.append(D); 
            if D>0: allneg=False
        print("    "+" ".join(f"{d:>12d}" for d in line))
    print(f"  ALL minors <= 0 (full log-submodular / negative association)? {allneg}")
    # marginals vs independence: is N_ij ~ R_i*C_j/T ?
    T=int(Mx[:5,:5].sum()); Ri=Mx[:5,:5].sum(axis=1); Cj=Mx[:5,:5].sum(axis=0)
    print(f"  total T={T}; row sums r-={list(Ri)}; col sums r+={list(Cj)}")
    # correlation sign overall: sum_ij i*j*N - (sum i)(sum j)/T
    ii=np.arange(5)
    EX=float((ii*Ri).sum())/T; EY=float((ii*Cj).sum())/T
    EXY=float(sum(i*j*int(Mx[i][j]) for i in range(5) for j in range(5)))/T
    print(f"  E[r-]={EX:.5f} E[r+]={EY:.5f} E[r-r+]={EXY:.5f}  Cov={EXY-EX*EY:+.6f}  (neg => four-corner direction)")
