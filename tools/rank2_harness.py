import numpy as np

def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def matrix(k,kappa,R=5):
    N=1<<k; X=12*N; A=int(round(X**(1.0/kappa))); P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]; base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16); om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
    def mark(pl,a,s):
        for p in pl:
            i6=pow(6,-1,p); r=(s*i6)%p; m0=base+((r-base)%p); a[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1)
    if small: mark(small,om,1); mark(small,op,-1)
    mask=(om==0)&(op==0); rmf=rm[mask]; rpf=rp[mask]
    M=np.array([[int(np.sum((rmf==i)&(rpf==j))) for j in range(R)] for i in range(R)],dtype=float)
    return A,M

print("Trend of four-corner margin (R_fc-1) and rank-2 strength (sv2/sv1):")
print(f"{'kappa':>6}{'k':>4}{'A':>6}{'R_fc':>9}{'R_fc-1':>10}{'sv2/sv1':>10}{'cornerDet sign':>15}")
for kappa in [3.6,4.0,4.4]:
    prev=None
    for k in [20,22,24,26]:
        A,M=matrix(k,kappa)
        n00,n03,n30,n33=M[0,0],M[0,3],M[3,0],M[3,3]
        if n03*n30==0: continue
        Rfc=n00*n33/(n03*n30)
        sv=np.linalg.svd(M,compute_uv=False)
        D=n00*n33-n03*n30
        print(f"{kappa:>6.1f}{k:>4}{A:>6}{Rfc:>9.5f}{Rfc-1:>+10.5f}{sv[1]/sv[0]:>10.5f}{('neg(ok)' if D<0 else 'POS(fail)'):>15}")
    print()

# Show the rank-2 perturbation structure at k=24, kappa=4
A,M=matrix(24,4.0)
U,s,Vt=np.linalg.svd(M)
print(f"k=24 kappa=4: singular values {[round(x,1) for x in s]}")
print(f"  rank-1 captures {s[0]**2/ (s**2).sum()*100:.4f}% of energy")
# rank-1 approx and residual
M1=s[0]*np.outer(U[:,0],Vt[0])
resid=M-M1
print("  residual (M - rank1) at integer ranks 0..3 (rows r-, cols r+):")
for i in range(4):
    print("    "+" ".join(f"{resid[i,j]:>+9.1f}" for j in range(4)))
print("  2nd singular vectors u2, v2 (sign pattern across ranks 0..4):")
print("    u2:", [round(x,3) for x in U[:,1]])
print("    v2:", [round(x,3) for x in Vt[1]])
print(f"  corner det of residual N00*N33-N03*N30 in residual? full D = {M[0,0]*M[3,3]-M[0,3]*M[3,0]:+.3e}")
