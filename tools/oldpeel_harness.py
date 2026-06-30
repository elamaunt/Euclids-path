def primes_upto(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return [i for i in range(n+1) if s[i]]
A=200
P=primes_upto(A*A*4); small=[p for p in P if 3<p<=A]; isprime=set(P)
cnt=sign_ok=drop_ok=regen=0
for n in range(A*A//6, A*A*3):
    for eps in (1,-1):
        a=6*n+eps
        if a<=A or a not in isprime: continue
        other=6*n-eps
        if other<2: continue
        p=next((q for q in small if other%q==0), None)
        if p is None: continue
        co=other//p; delta=1 if co%6==1 else (-1 if co%6==5 else 0)
        if delta==0: continue
        t=(co-delta)//6; cnt+=1; pi=1 if p%6==1 else -1
        if delta==-pi*eps: sign_ok+=1
        if t<n/5+1: drop_ok+=1
        if t>0: regen+=1
    if cnt>=3000: break
print(f"catches={cnt} sign={sign_ok/cnt:.4f} drop={drop_ok/cnt:.4f} regen={regen/cnt:.4f}")
