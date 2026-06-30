from fractions import Fraction as F

rows = {}
for fn in ["twin_stats_21_27.csv", "twin_stats_28_detail.csv"]:
    for line in open(fn, encoding="utf-8"):
        if line.startswith("GLOBAL,"):
            p = line.strip().split(",")
            k = int(p[1]); N = int(p[2]); A = float(p[3])
            N00=int(p[4]); N30=int(p[5]); N31=int(p[6]); N32=int(p[7]); N33=int(p[8]); N03=int(p[9])
            M=int(p[10]); Gamma=int(p[11])
            rows[k] = dict(N=N,A=A,N00=N00,N30=N30,N31=N31,N32=N32,N33=N33,N03=N03,M=M,Gamma=Gamma)

print(f"{'k':>3} {'R_fc=N00N33/N03N30':>20} {'R_sc=N03N30/N00^2':>20} {'N33/N00':>10} {'N03/N30':>10} {'N00N33<N03N30?':>15} {'Gamma=N30+4N33?':>16}")
for k in sorted(rows):
    r = rows[k]
    N00,N03,N30,N33 = r['N00'],r['N03'],r['N30'],r['N33']
    R_fc = F(N00*N33, N03*N30)
    R_sc = F(N03*N30, N00*N00)
    r3300 = F(N33, N00)
    sym = F(N03, N30)
    fc_holds = N00*N33 < N03*N30
    gamma_ok = (r['N30'] + 4*r['N33'] == r['Gamma'])
    print(f"{k:>3} {float(R_fc):>20.6f} {float(R_sc):>20.6f} {float(r3300):>10.6f} {float(sym):>10.6f} {str(fc_holds):>15} {str(gamma_ok):>16}")

print()
print("=== deviation from independence: corr := 1 - R_fc  (positive => negative association, four-corner strict) ===")
for k in sorted(rows):
    r = rows[k]
    N00,N03,N30,N33 = r['N00'],r['N03'],r['N30'],r['N33']
    R_fc = F(N00*N33, N03*N30)
    print(f"k={k}: 1 - R_fc = {float(1-R_fc):+.6f}   D = N00*N33 - N03*N30 = {N00*N33 - N03*N30}")

print()
print("=== test combined: does (four-corner)+(side-corner) chain give N33<N00, and with how much margin? ===")
for k in sorted(rows):
    r = rows[k]
    N00,N03,N30,N33 = r['N00'],r['N03'],r['N30'],r['N33']
    lhs = F(N03*N30, N00)   # N03*N30/N00  (product-corner upper proxy)
    print(f"k={k}: N33={N33}  N03*N30/N00={float(lhs):.1f}  N00={N00}   N33 < N03N30/N00 ? {N33*N00 < N03*N30}   N03N30/N00 < N00 ? {N03*N30 < N00*N00}")
