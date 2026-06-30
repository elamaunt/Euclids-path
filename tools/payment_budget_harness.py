import math
def primes_upto(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return [i for i in range(n+1) if s[i]]
# Budget 20.2: frac of a<=Z=A^kappa with gcd(a-theta, P_<p(>3)) >= D  (theta=+1)
for (A,p,kappa) in [(70,29,4.5),(130,31,4.5),(240,37,4.5)]:
    Z=int(A**kappa); qs=[q for q in primes_upto(p-1) if q>3]
    for D in [p*p,1000,100]:
        N=2_000_000; step=max(1,Z//N); cnt=0; tot=0
        for a in range(1,Z+1,step):
            tot+=1; g=1; x=a-1
            for q in qs:
                if x%q==0: g*=q
            if g>=D: cnt+=1
        print(f"A={A} p={p} Z~{Z:.2e} D={D}: frac(gcd>=D)={cnt/tot:.5e}")
