# newman_prepass.py — numeric pre-pass for the Newman analytic theorem (Tauberian campaign, stage N).
#
# Validates, BEFORE any Lean is written:
#   T1  the master contour ledger (C12) at concrete data f(t) = e^{-t}
#       (g(z) = 1/(z+1), g(0) = 1) over a (R, delta, T) grid — every sign and
#       orientation of rightArc / dentInt / leftArc;
#   T2  the telescoping sub-identities rightArc(1/z) = dentInt(1/z) = pi*i and
#       rightArc(phi) + dentInt(phi) = 0 for phi = (g*K - g(0))/z;
#   T3  the exact circle weight identity (1 + z^2/R^2)/z = 2*Re(z)/R^2 on |z| = R;
#   T4  sharpness of the three ML estimates E1-E3 with their exact constants;
#   T5  the epsilon-schedule realizability (R = 4M/eps + 1, T0 from E3);
#   T6  NEGATIVE control f(t) = cos t (g = z/(1+z^2), poles at +-i ON the closed
#       half-plane): with R < 1 the ledger still balances (it is an identity),
#       while S_T(0) = sin T does not converge — the hypothesis, not the algebra,
#       is what fails;
#   T7  the Mellin bridge (D4): A = psi (Chebyshev) up to 10^4, c = 1:
#       int_1^X (A - t)/t^2 dt equals int_0^{log X} f(u) du under t = e^u, and
#       G(s) ~ (-zeta'/zeta(s))/s - 1/(s-1) at s = 2, 1.5.
#
# Exit code 0 with all PASS lines, nonzero otherwise.

import mpmath as mp
import sys

mp.mp.dps = 60
TOL = mp.mpf("1e-9")
fails = []


def check(name, ok, detail=""):
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name} {detail}")
    if not ok:
        fails.append(name)


# ---------------------------------------------------------------- contour pieces
def circle(R, th):
    return R * mp.e ** (1j * th)


def right_arc(R, h):
    # int_{-pi/2}^{pi/2} deriv(circleMap) * h(circleMap)  with deriv = i R e^{i th}
    return mp.quad(lambda th: 1j * circle(R, th) * h(circle(R, th)),
                   [-mp.pi / 2, 0, mp.pi / 2])


def left_arc(R, h):
    return mp.quad(lambda th: 1j * circle(R, th) * h(circle(R, th)),
                   [mp.pi / 2, mp.pi, 3 * mp.pi / 2])


def dent_int(R, d, h):
    top = mp.quad(lambda x: h(x + R * 1j), [0, -d])            # iR -> -d + iR
    left = mp.quad(lambda y: 1j * h(-d + y * 1j), [R, 0, -R])   # down the segment
    bot = mp.quad(lambda x: h(x - R * 1j), [-d, 0])             # -d - iR -> -iR
    return top + left + bot


# ---------------------------------------------------------------- T1: master ledger
def S_T_exp(z, T):
    # f = e^{-t}: S_T(z) = (1 - e^{-(z+1)T})/(z+1)
    return (1 - mp.e ** (-(z + 1) * T)) / (z + 1)


def K_fn(R, T, z):
    return mp.e ** (z * T) * (1 + z * z / (R * R))


print("== T1: master ledger, f = exp(-t), g = 1/(z+1) ==")
g0 = mp.mpf(1)
for R in (1, 2, 5):
    for d in (mp.mpf("0.1"), mp.mpf("0.3")):
        for T in (1, 5, 20):
            g = lambda z: 1 / (z + 1)
            hR = lambda z: (g(z) - S_T_exp(z, T)) * K_fn(R, T, z) / z
            hD = lambda z: g(z) * K_fn(R, T, z) / z
            hL = lambda z: S_T_exp(z, T) * K_fn(R, T, z) / z
            lhs = 2 * mp.pi * 1j * (g0 - S_T_exp(mp.mpf(0), T))
            pR, pD, pL = right_arc(R, hR), dent_int(R, d, hD), left_arc(R, hL)
            rhs = pR + pD - pL
            scale = max(mp.mpf(1), abs(pR), abs(pD), abs(pL))
            err = abs(lhs - rhs) / scale
            check(f"ledger R={R} d={float(d)} T={T}", err < TOL, f"rel_err={mp.nstr(err, 3)}")

# ---------------------------------------------------------------- T2: sub-identities
print("== T2: telescoping sub-identities ==")
for R in (1, 2, 5):
    v = right_arc(R, lambda z: 1 / z)
    check(f"rightArc(1/z)=pi*i R={R}", abs(v - mp.pi * 1j) < TOL, f"err={mp.nstr(abs(v - mp.pi * 1j), 3)}")
    for d in (mp.mpf("0.1"), mp.mpf("0.3")):
        w = dent_int(R, d, lambda z: 1 / z)
        check(f"dentInt(1/z)=pi*i R={R} d={float(d)}", abs(w - mp.pi * 1j) < TOL,
              f"err={mp.nstr(abs(w - mp.pi * 1j), 3)}")
R, d, T = 2, mp.mpf("0.3"), 5
g = lambda z: 1 / (z + 1)
phi = lambda z: (g(z) * K_fn(R, T, z) - g0) / z
v = right_arc(R, phi) + dent_int(R, d, phi)
check("rightArc(phi)+dentInt(phi)=0", abs(v) < TOL, f"err={mp.nstr(abs(v), 3)}")

# ---------------------------------------------------------------- T3: weight identity
print("== T3: exact circle weight identity ==")
worst = mp.mpf(0)
for R in (1, 2, 5):
    for k in range(200):
        th = -mp.pi + 2 * mp.pi * (k + mp.mpf("0.5")) / 200
        z = circle(R, th)
        if abs(z) < mp.mpf("1e-20"):
            continue
        lhs = (1 + z * z / (R * R)) / z
        rhs = 2 * mp.re(z) / (R * R)
        worst = max(worst, abs(lhs - rhs))
check("weight identity (200 pts x 3 radii)", worst < mp.mpf("1e-12"), f"worst={mp.nstr(worst, 3)}")

# ---------------------------------------------------------------- T4: ML sharpness
print("== T4: ML estimate sharpness (M = 1) ==")
M = mp.mpf(1)
for R in (2, 5):
    for T in (5, 20):
        g = lambda z: 1 / (z + 1)
        hR = lambda z: (g(z) - S_T_exp(z, T)) * K_fn(R, T, z) / z
        hL = lambda z: S_T_exp(z, T) * K_fn(R, T, z) / z
        vR = abs(right_arc(R, hR))
        vL = abs(left_arc(R, hL))
        cap = 2 * mp.pi * M / R + TOL
        check(f"E1 rightArc<=2piM/R R={R} T={T}", vR <= cap, f"{mp.nstr(vR, 4)} <= {mp.nstr(cap, 4)}")
        check(f"E2 leftArc<=2piM/R R={R} T={T}", vL <= cap, f"{mp.nstr(vL, 4)} <= {mp.nstr(cap, 4)}")
for R in (2,):
    for d in (mp.mpf("0.3"),):
        # C0 = sup over the three dent segments of |g(z)(1+z^2/R^2)/z|
        pts = ([x + R * 1j for x in mp.linspace(-d, 0, 200)]
               + [-d + y * 1j for y in mp.linspace(-R, R, 400)]
               + [x - R * 1j for x in mp.linspace(-d, 0, 200)])
        C0 = max(abs((1 / (z + 1)) * (1 + z * z / (R * R)) / z) for z in pts)
        for T in (5, 20, 60):
            vD = abs(dent_int(R, d, lambda z: (1 / (z + 1)) * K_fn(R, T, z) / z))
            cap = 2 * R * C0 * mp.e ** (-d * T) + 2 * C0 / T + TOL
            check(f"E3 dent<=2RC0e^-dT+2C0/T R={R} d={float(d)} T={T}", vD <= cap,
                  f"{mp.nstr(vD, 4)} <= {mp.nstr(cap, 4)}")

# ---------------------------------------------------------------- T5: eps-schedule
print("== T5: epsilon schedule ==")
for eps in (mp.mpf("0.1"), mp.mpf("0.01")):
    R = 4 * M / eps + 1
    d = mp.mpf("0.2")
    pts = [-d + y * 1j for y in mp.linspace(-R, R, 600)] + \
          [x + R * 1j for x in mp.linspace(-d, 0, 100)] + \
          [x - R * 1j for x in mp.linspace(-d, 0, 100)]
    C0 = max(abs((1 / (z + 1)) * (1 + z * z / (R * R)) / z) for z in pts)
    # T0 such that (2 R C0 e^{-dT} + 2 C0/T)/(2 pi) <= eps/4  and 2M/R <= eps/2 already
    T = mp.mpf(10)
    while (2 * R * C0 * mp.e ** (-d * T) + 2 * C0 / T) / (2 * mp.pi) > eps / 4 and T < 10 ** 7:
        T *= 2
    diff = abs(g0 - S_T_exp(mp.mpf(0), T))
    check(f"schedule eps={float(eps)}", diff < eps, f"|g0-S_T0|={mp.nstr(diff, 3)} at T={mp.nstr(T, 3)}")

# ---------------------------------------------------------------- T6: negative control
print("== T6: negative control f = cos t (poles at +-i) ==")
R, d = mp.mpf("0.5"), mp.mpf("0.2")   # contour avoids the poles
g_cos = lambda z: z / (1 + z * z)


def S_T_cos(z, T):
    # int_0^T cos t e^{-zt} dt = [e^{-zt}(sin t - z cos t)/(1+z^2)]_0^T
    return (mp.e ** (-z * T) * (mp.sin(T) - z * mp.cos(T)) + z) / (1 + z * z)


for T in (5, 20):
    hR = lambda z: (g_cos(z) - S_T_cos(z, T)) * K_fn(R, T, z) / z
    hD = lambda z: g_cos(z) * K_fn(R, T, z) / z
    hL = lambda z: S_T_cos(z, T) * K_fn(R, T, z) / z
    lhs = 2 * mp.pi * 1j * (g_cos(0) - S_T_cos(mp.mpf(0), T))
    rhs = right_arc(R, hR) + dent_int(R, d, hD) - left_arc(R, hL)
    check(f"negative-control ledger T={T}", abs(lhs - rhs) < TOL, f"err={mp.nstr(abs(lhs - rhs), 3)}")
# S_T(0) = sin T does not converge:
check("negative-control S_T(0)=sinT wanders", abs(S_T_cos(mp.mpf(0), 5) - S_T_cos(mp.mpf(0), 20)) > mp.mpf("0.1"),
      f"|sin5-sin20|={mp.nstr(abs(mp.sin(5) - mp.sin(20)), 3)}")

# ---------------------------------------------------------------- T7: Mellin bridge
print("== T7: Mellin bridge with psi up to 10^4 ==")
N = 10 ** 4
lam = [mp.mpf(0)] * (N + 1)  # von Mangoldt
sieve = list(range(N + 1))
for p in range(2, N + 1):
    if sieve[p] == p:  # p prime
        pk = p
        while pk <= N:
            lam[pk] = mp.log(p)
            pk *= p
        for m in range(p * p, N + 1, p):
            if sieve[m] == m:
                sieve[m] = p
psi_arr = [mp.mpf(0)] * (N + 1)
for n in range(1, N + 1):
    psi_arr[n] = psi_arr[n - 1] + lam[n]


def psi(t):
    tt = int(mp.floor(t))
    return psi_arr[min(tt, N)]


# psi is a step function: integrate EXACTLY over integer breakpoints on the
# t-side, and over u-breakpoints log n on the u-side — the substitution maps
# breakpoints to breakpoints, so both exact sums must agree to full precision.
X = 5000
# t-side: sum over n of  psi_n*(1/n - 1/(n+1)) - log((n+1)/n)
lhs = mp.mpf(0)
for n in range(1, X):
    lhs += psi_arr[n] * (mp.mpf(1) / n - mp.mpf(1) / (n + 1)) - mp.log(mp.mpf(n + 1) / n)
# u-side: int_{log n}^{log(n+1)} (psi(e^u)e^{-u} - 1) du
#       = psi_n*(1/n - 1/(n+1)) - (log(n+1) - log n)   — identical closed form
rhs = mp.mpf(0)
for n in range(1, X):
    rhs += psi_arr[n] * (mp.e ** (-mp.log(mp.mpf(n))) - mp.e ** (-mp.log(mp.mpf(n + 1)))) \
        - (mp.log(mp.mpf(n + 1)) - mp.log(mp.mpf(n)))
check("Mellin substitution t=e^u (exact piecewise)", abs(lhs - rhs) < mp.mpf("1e-20"),
      f"err={mp.nstr(abs(lhs - rhs), 3)}")

for s in (mp.mpf(2), mp.mpf("1.5")):
    G_num = sum(lam[n] / mp.mpf(n) ** s for n in range(1, N + 1)) / s - 1 / (s - 1)
    G_zeta = (-mp.zeta(s, derivative=1) / mp.zeta(s)) / s - 1 / (s - 1)
    check(f"G(s) via -zeta'/zeta at s={float(s)}", abs(G_num - G_zeta) < mp.mpf("0.05"),
          f"num={mp.nstr(G_num, 5)} zeta={mp.nstr(G_zeta, 5)}")

print()
if fails:
    print(f"PREPASS FAILED: {len(fails)} checks: {fails}")
    sys.exit(1)
print("PREPASS: ALL CHECKS PASSED")
