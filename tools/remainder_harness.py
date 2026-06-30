import numpy as np

def primes_upto(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

def esym(ws, K=6):
    # elementary symmetric e_0..e_K via poly product prod(1+w t) truncated
    e=[1.0]+[0.0]*K
    for w in ws:
        for k in range(K,0,-1):
            e[k]+=w*e[k-1]
    return e

def analyze(k):
    N=1<<k; X=12*N; A=int(round(X**0.25)); P=primes_upto(A*A)
    layer=[int(p) for p in P if A<p<=A*A]; small=[int(p) for p in P if 5<=p<=A]
    base=N
    rm=np.zeros(N,dtype=np.int16); rp=np.zeros(N,dtype=np.int16)
    om=np.zeros(N,dtype=np.int16); op=np.zeros(N,dtype=np.int16)
    def mark(plist,arr,sign):
        for p in plist:
            i6=pow(6,-1,p); r=(sign*i6)%p; m0=base+((r-base)%p); arr[m0-base::p]+=1
    mark(layer,rm,1); mark(layer,rp,-1); mark(small,om,1); mark(small,op,-1)
    mask=(om==0)&(op==0); rmf=rm[mask]; rpf=rp[mask]; T=int(mask.sum())
    def cnt(i,j): return int(np.sum((rmf==i)&(rpf==j)))
    n00,n03,n30,n33=cnt(0,0),cnt(0,3),cnt(3,0),cnt(3,3)
    # model
    ws=[1.0/(q-2) for q in layer]
    logprodc=sum(np.log1p(-2.0/q) for q in layer); prodc=np.exp(logprodc)
    e=esym(ws,6)
    base_m=T*prodc
    m00=base_m*1.0
    m03=base_m*e[3]; m30=base_m*e[3]
    m33=base_m*20*e[6]
    Rfc_real=n00*n33/(n03*n30)
    Rfc_model=20*e[6]/(e[3]**2)
    print(f"\n=== k={k}, A={A}, layer primes={len(layer)}, T(old-free)={T} ===")
    print(f"  prod c_q = {prodc:.6e},  e1={e[1]:.4f} e3={e[3]:.5f} e6={e[6]:.6e}")
    print(f"  corner | real        | model        | e=real-model | e/model")
    for nm,nr,mr in [("N00",n00,m00),("N03",n03,m03),("N30",n30,m30),("N33",n33,m33)]:
        print(f"   {nm}  | {nr:>11d} | {mr:>12.1f} | {nr-mr:>+12.1f} | {(nr-mr)/mr:>+7.3f}")
    print(f"  R_fc REAL  = {Rfc_real:.5f}")
    print(f"  R_fc MODEL = {Rfc_model:.5f}   (=20 e6/e3^2, the Maclaurin bound)")
    margin_model = m03*m30 - m00*m33
    ndiff = n00*n33 - n03*n30
    mdiff = m00*m33 - m03*m30
    R = ndiff - mdiff   # cross-term remainder (from decomp identity)
    print(f"  model four-corner diff m00*m33-m03*m30 = {mdiff:>.3e}  (<0 ok)")
    print(f"  real  four-corner diff n00*n33-n03*n30 = {ndiff:>.3e}  (<0 ok)")
    print(f"  margin(model)= -mdiff = {-mdiff:>.3e};  remainder cross R = ndiff-mdiff = {R:>.3e}")
    print(f"  hrem (R <= margin)? {R <= -mdiff}   <=> real four-corner holds? {ndiff<=0}")
    print(f"  KEY: R_fc_real vs R_fc_model -> {'REAL has MORE excess (remainder AGAINST)' if Rfc_real>Rfc_model else 'real has less excess (remainder helps)'}")

for k in [20,22,24]:
    analyze(k)
