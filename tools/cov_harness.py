import numpy as np
def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
def run(k,kappa):
    N=1<<k; X=12*N; A=int(round(X**(1.0/kappa))); P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]; base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16); om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
    def mark(pl,a,s):
        for p in pl:
            i6=pow(6,-1,p); r=(s*i6)%p; m0=base+((r-base)%p); a[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1)
    if small: mark(small,om,1); mark(small,op,-1)
    mask=(om==0)&(op==0); a=rm[mask].astype(np.float64); b=rp[mask].astype(np.float64); T=a.size
    cov=float((a*b).mean()-a.mean()*b.mean())
    # four-corner sign via corner counts
    def c(i,j): return int(np.sum((rm[mask]==i)&(rp[mask]==j)))
    n00,n03,n30,n33=c(0,0),c(0,3),c(3,0),c(3,3)
    D = n00*n33-n03*n30
    return A,T,cov,(D),(n00*n33/(n03*n30) if n03*n30 else None)
print(f"{'kappa':>6}{'k':>4}{'A':>6}{'Cov(r-,r+)':>12}{'fourcornerD':>14}{'D<0?':>6}{'R_fc':>9}")
res=[]
for kappa in [3.6,4.0,4.4,4.8]:
    for k in [22,24,26]:
        A,T,cov,D,Rfc=run(k,kappa)
        ok = (D<0)
        print(f"{kappa:>6.1f}{k:>4}{A:>6}{cov:>12.6f}{D:>14d}{str(ok):>6}{(Rfc if Rfc else 0):>9.5f}")
        res.append((kappa,k,A,cov,D,Rfc))
allneg_cov=all(r[3]<0 for r in res)
allneg_D=all(r[4]<0 for r in res)
print(f"\nCov(r-,r+) < 0 on ALL (k,kappa)? {allneg_cov}")
print(f"four-corner D < 0 on ALL (k,kappa)? {allneg_D}")
