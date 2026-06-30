import math
def primes_upto(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return [i for i in range(n+1) if s[i]]
# (3) fraction of primes a in (A,A^2] whose neighbour a±2 has a small divisor <= A
for A in [50,200,1000]:
    P=primes_upto(A*A); small=set(p for p in P if 3<p<=A); big=[p for p in P if A<p<=A*A]
    caught=lambda x: any(x%q==0 for q in small)
    n=len(big)
    print(f"A={A}: a-2 caught {sum(caught(a-2) for a in big)/n:.4f}, a+2 caught {sum(caught(a+2) for a in big)/n:.4f}")
