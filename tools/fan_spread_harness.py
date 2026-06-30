import numpy as np
from collections import Counter

def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def analyze(k):
    N=1<<k; X=12*N; A=int(round(X**0.25)); P=primes_upto(A*A)
    layerset=set(int(p) for p in P if A<p<=A*A)
    layer=sorted(layerset); small=[int(p) for p in P if 5<=p<=A]
    base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16)
    om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
    def mark(plist,arr,sign):
        for p in plist:
            i6=pow(6,-1,p); r=(sign*i6)%p; m0=base+((r-base)%p); arr[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1); mark(small,om,1); mark(small,op,-1)
    sel=np.nonzero((om==0)&(op==0)&(rm==3)&(rp==3))[0]   # rank-(3,3) old-free centers
    def layerfacs(n):
        f=[]
        for p in layer:
            if p*p>n: break
            while n%p==0: f.append(p); n//=p
        if n in layerset: f.append(n)
        return f
    rays=Counter()    # (v,s) -> count   (max-terminal pair)
    n33=0
    for mi in sel:
        m=base+int(mi)
        minus=m*6-1; plus=m*6+1
        fa=layerfacs(minus); fb=layerfacs(plus)
        if len(fa)>=3 and len(fb)>=3:
            n33+=1
            v=max(fa); s=max(fb)
            rays[(v,s)]+=1
    mult=Counter(rays.values())  # R* distribution
    O=len(rays); Rmax=max(rays.values()) if rays else 0
    CRE=n33-O
    print(f"k={k} A={A}: N33(verified by factoring)={n33}, occupied rays O={O}, CRE=N33-O={CRE} ({100*CRE/max(n33,1):.2f}%), max R*={Rmax}")
    print(f"   R* multiplicity distribution (how many rays have multiplicity r): {dict(sorted(mult.items()))}")
    print(f"   #distinct products vs N33/A^s heuristics: O={O}, N33={n33}, A={A}")
    return

for k in [20,22,24]:
    analyze(k)
