"""Numeric pre-pass for stage L-M3 (GeometricTypeIIWingSign) — THE BUDGET CHAIN.

Verifies, with high-precision arithmetic (mpmath, 60 dps) and exact
rationals where the design constants are rational:

  1. The slice grid a_i = (14+i)/40, i = 0..6, covers the rung range
     (X^{7/20}, X^{1/2}] for every theta in [7/20, 9/20]  (symbolic).
  2. The Riemann upper sum U6 = sum_i log(a_{i+1}/a_i) / (1 - a_{i+1})
     and the Chebyshev-inflated margin log 4 * U6 < 1.
  3. THE BUDGET: with interface slack eps = 1/200 and registered
     constant c = 1/40,
        (1/2 + eps) * log4 * U6 + c + SLOP < 1/2 - eps
     with slop budget 0.02 (covers the 1/log X boundary terms, the
     nat-division log-2 slop and the apCount(z) subtraction, all of
     which vanish eventually).
  4. The K = 8 fallback grid (a_i = (14+i)/40 refined to 80ths on the
     first slice) also fits (coarser check: log4 * U8 < log4 * U6).

Design reference: the landing plan (campaign session), section 4.
Measured grounding at X = 10^7 (recorded in the design, not re-run
here): Sigma lambda = -172058 / -238841 / -299193 at theta = .35/.40/.45.
"""

from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60

failures = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"[{status}] {name} {detail}")
    if not cond:
        failures.append(name)


# ---------------------------------------------------------------- 1. slices
# Rungs satisfy z < p and p^2 <= X with X^7 <= z^20 <= X^9, i.e.
# p in (X^{theta}, X^{1/2}] with theta = (log z / log X) in [7/20, 9/20].
# The slice grid starts at 14/40 = 7/20 and ends at 20/40 = 1/2.
a = [Fraction(14 + i, 40) for i in range(7)]
check("slice grid endpoints", a[0] == Fraction(7, 20) and a[-1] == Fraction(1, 2),
      f"a = {[str(x) for x in a]}")
# monotone cover
check("slice grid monotone", all(a[i] < a[i + 1] for i in range(6)))

# ---------------------------------------------------------------- 2. U6
log4 = mp.log(4)
U6 = mp.mpf(0)
for i in range(6):
    ratio = mp.mpf(a[i + 1].numerator) / a[i + 1].denominator
    lo = mp.mpf(a[i].numerator) / a[i].denominator
    U6 += mp.log(ratio / lo) / (1 - ratio)
print(f"U6            = {mp.nstr(U6, 10)}")
print(f"log4 * U6     = {mp.nstr(log4 * U6, 10)}")
check("U6 approx 0.6329", abs(U6 - mp.mpf("0.6329")) < mp.mpf("0.001"))
check("log4*U6 < 0.878", log4 * U6 < mp.mpf("0.878"))
check("log4*U6 < 1 (margin exists at all)", log4 * U6 < 1)

# ---------------------------------------------------------------- 3. budget
eps = Fraction(1, 200)
c_target = Fraction(1, 40)
slop = Fraction(2, 100)
lhs = (Fraction(1, 2) + eps) * Fraction(str(mp.nstr(log4 * U6, 30))) \
    if False else None
# exact-side: use a certified UPPER bound for log4*U6
log4U6_upper = mp.mpf("0.8776")
check("certified upper: log4*U6 <= 0.8776", log4 * U6 <= log4U6_upper)
budget_lhs = (mp.mpf(1) / 2 + mp.mpf(1) / 200) * log4U6_upper \
    + mp.mpf(1) / 40 + mp.mpf(2) / 100
budget_rhs = mp.mpf(1) / 2 - mp.mpf(1) / 200
print(f"budget lhs    = {mp.nstr(budget_lhs, 10)} (incl. slop 0.02)")
print(f"budget rhs    = {mp.nstr(budget_rhs, 10)}")
check("BUDGET: (1/2+eps)*0.8776 + 1/40 + 0.02 < 1/2 - eps",
      budget_lhs < budget_rhs,
      f"margin = {mp.nstr(budget_rhs - budget_lhs, 6)}")

# ---------------------------------------------------------------- 4. K = 8
a8 = [Fraction(28 + i, 80) for i in range(13)]  # 80ths from 28/80 to 40/80
U8 = mp.mpf(0)
for i in range(12):
    hi = mp.mpf(a8[i + 1].numerator) / a8[i + 1].denominator
    lo = mp.mpf(a8[i].numerator) / a8[i].denominator
    U8 += mp.log(hi / lo) / (1 - hi)
print(f"U8 (80ths)    = {mp.nstr(U8, 10)}, log4*U8 = {mp.nstr(log4 * U8, 10)}")
check("fallback U8 <= U6", U8 <= U6 + mp.mpf("1e-30"))

# ---------------------------------------------------------------- summary
print()
if failures:
    print(f"FAILURES: {failures}")
    raise SystemExit(1)
print("ALL CHECKS PASSED — the M3 budget chain is sound "
      "(eps = 1/200, c = 1/40, slop 0.02, K = 6 slices at 40ths).")
