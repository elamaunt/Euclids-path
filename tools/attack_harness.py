import numpy as np, math
def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
def run(k,kappa):
    N=1<<k; X=12*N; A=int(round(X**(1.0/kappa))); P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]; base=N
    rm=np.zeros(N,dtype=np.int8); rp=np.zeros(N,dtype=np.int8); om=np.zeros(N,dtype=np.int8); op=np.zeros(N,dtype=np.int8)
    sm={}; sp={}
    def mark(pl,a,s,store):
        for p in pl:
            i6=pow(6,-1,p); r=(s*i6)%p; st=(r-base)%p; a[st::p]+=1
            if store is not None: store[p]=st
    mark(layer,rm,1,sm); mark(layer,rp,-1,sp)
    if small: mark(small,om,1,None); mark(small,op,-1,None)
    mask=(om==0)&(op==0); T=int(mask.sum())
    a=rm[mask].astype(np.float64); b=rp[mask].astype(np.float64)
    Cov=float((a*b).mean()-a.mean()*b.mean())
    DIAG=0.0
    for p in layer:
        cm=int(mask[sm[p]::p].sum()); cp=int(mask[sp[p]::p].sum()); DIAG+=(cm/T)*(cp/T)
    CROSS=Cov+DIAG
    def c(i,j): return int(np.sum((rm[mask]==i)&(rp[mask]==j)))
    n00,n03,n30,n33=c(0,0),c(0,3),c(3,0),c(3,3)
    D=n00*n33-n03*n30
    return A,T,Cov,DIAG,CROSS,D,(n00*n33/(n03*n30) if n03*n30 else None)
print(f"{'kappa':>6}{'k':>4}{'A':>6}{'DIAG':>11}{'CROSS':>12}{'C/D':>8}{'cornerD<0':>10}{'R_fc':>9}{'DIAG*AlnA':>10}")
for kappa in [4.0,4.4]:
    for k in [25,26,27,28]:
        A,T,Cov,DIAG,CROSS,D,Rfc=run(k,kappa)
        print(f"{kappa:>6.1f}{k:>4}{A:>6}{DIAG:>11.6f}{CROSS:>+12.6f}{abs(CROSS)/DIAG:>8.3f}{str(D<0):>10}{(Rfc if Rfc else 0):>9.5f}{DIAG*A*math.log(A):>10.4f}")
    print()
