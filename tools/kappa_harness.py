import numpy as np
from math import comb

def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def esym(ws,K=6):
    e=[1.0]+[0.0]*K
    for w in ws:
        for k in range(K,0,-1): e[k]+=w*e[k-1]
    return e

def run(k, kappa):
    N=1<<k; X=12*N; A=int(round(X**(1.0/kappa)))
    if A<5: return None
    P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]
    base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16)
    om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
    def mark(pl,a,s):
        for p in pl:
            i6=pow(6,-1,p); r=(s*i6)%p; m0=base+((r-base)%p); a[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1)
    if small: mark(small,om,1); mark(small,op,-1)
    mask=(om==0)&(op==0); rmf=rm[mask]; rpf=rp[mask]; T=int(mask.sum())
    def c(i,j): return int(np.sum((rmf==i)&(rpf==j)))
    n00,n03,n30,n33=c(0,0),c(0,3),c(3,0),c(3,3)
    if n03*n30==0: return (A,len(layer),T,n00,n03,n30,n33,None,None)
    Rr=n00*n33/(n03*n30)
    ws=[1.0/(q-2) for q in layer]; e=esym(ws,6)
    Rm=20*e[6]/(e[3]**2) if e[3]>0 else None
    return (A,len(layer),T,n00,n03,n30,n33,Rr,Rm)

print("Vary kappa (block scale X=A^kappa), k=22:")
print(f"{'kappa':>6}{'A':>6}{'#layer':>8}{'N00':>10}{'N03':>8}{'N33':>8}{'R_fc_real':>11}{'R_fc_model':>11}{'fc<1':>6}")
for kappa in [3.0,3.3,3.6,4.0,4.4,4.8]:
    r=run(22,kappa)
    if r is None: continue
    A,nl,T,n00,n03,n30,n33,Rr,Rm=r
    fc = (n00*n33 < n03*n30)
    print(f"{kappa:>6.1f}{A:>6}{nl:>8}{n00:>10}{n03:>8}{n33:>8}{(Rr if Rr else 0):>11.5f}{(Rm if Rm else 0):>11.5f}{str(fc):>6}")

# matrix anti-diagonal (Hankel) check at k=24, kappa=4
print("\nMatrix anti-diagonal structure N_ij/C(i+j,i) (k=24, kappa=4): is it constant along i+j?")
N=1<<24; X=12*N; A=int(round(X**0.25)); P=primes_upto(A*A)
layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]; base=N
rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16); om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
def mark(pl,a,s):
    for p in pl:
        i6=pow(6,-1,p); r=(s*i6)%p; m0=base+((r-base)%p); a[m0-base::p]+=1
mark(layer,rm,1); mark(layer,rp,-1); mark(small,om,1); mark(small,op,-1)
mask=(om==0)&(op==0); rmf=rm[mask]; rpf=rp[mask]
M=np.array([[int(np.sum((rmf==i)&(rpf==j))) for j in range(4)] for i in range(4)])
print("  N_ij:"); 
for i in range(4): print("   ",M[i])
print("  N_ij / C(i+j,i)  (anti-diagonals i+j=const should be equal if Hankel):")
for i in range(4):
    print("   ",[round(M[i][j]/comb(i+j,i),1) for j in range(4)])
# singular values of M (rank structure)
sv=np.linalg.svd(M.astype(float),compute_uv=False)
print(f"  singular values of N (4x4): {[round(s,1) for s in sv]}  (ratio sv2/sv1={sv[1]/sv[0]:.4f})")
