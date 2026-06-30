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
    starts_minus={}; starts_plus={}
    def mark(pl,a,s,store):
        for p in pl:
            i6=pow(6,-1,p); r=(s*i6)%p; st=(r-base)%p
            a[st::p]+=1
            if store is not None: store[p]=st
    mark(layer,rm,1,starts_minus); mark(layer,rp,-1,starts_plus)
    if small: mark(small,om,1,None); mark(small,op,-1,None)
    mask=(om==0)&(op==0); T=int(mask.sum())
    a=rm[mask].astype(np.float64); b=rp[mask].astype(np.float64)
    Cov=float((a*b).mean()-a.mean()*b.mean())
    # DIAG = sum_p P_p^- P_p^+   (the 'removed heat' from exclusivity)
    DIAG=0.0
    for p in layer:
        cm = int(mask[starts_minus[p]::p].sum())   # old-free m with p|6m-1
        cp = int(mask[starts_plus[p]::p].sum())     # old-free m with p|6m+1
        DIAG += (cm/T)*(cp/T)
    CROSS = Cov + DIAG   # since Cov = CROSS - DIAG
    # mutual information of (r-,r+) over old-free pop
    Rm=int(a.max())+1; Rp=int(b.max())+1
    H=np.zeros((Rm,Rp))
    ai=a.astype(int); bi=b.astype(int)
    for i in range(Rm):
        for j in range(Rp):
            H[i,j]=np.sum((ai==i)&(bi==j))
    Pj=H/T; Pa=Pj.sum(1); Pb=Pj.sum(0)
    def ent(p):
        p=p[p>0]; return float(-(p*np.log(p)).sum())
    MI = ent(Pa)+ent(Pb)-ent(Pj.flatten())
    return A,T,Cov,DIAG,CROSS,MI
print(f"{'kappa':>6}{'k':>4}{'A':>6}{'Cov':>11}{'DIAG':>11}{'CROSS':>11}{'|CROSS|/DIAG':>13}{'MI(r-,r+)':>11}{'sign by':>10}")
for kappa in [4.0,4.4]:
    for k in [20,22,24]:
        A,T,Cov,DIAG,CROSS,MI=run(k,kappa)
        dom = 'DIAG(excl)' if abs(CROSS)<DIAG else 'CROSS(bnd)'
        print(f"{kappa:>6.1f}{k:>4}{A:>6}{Cov:>11.6f}{DIAG:>11.6f}{CROSS:>+11.6f}{abs(CROSS)/DIAG:>13.4f}{MI:>11.6f}{dom:>10}")
