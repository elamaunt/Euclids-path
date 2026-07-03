import math
# Accelerated Collatz map T: even -> n/2, odd -> (3n+1)/2 (forced halving folded in)
# Engine view: even step = DESCENT (x2 down); odd step = FUEL injection (+1) then partial descent.

def trajectory_stats(n):
    """Return (steps, max_excursion_ratio, halvings, triplings, log_drift_sum)."""
    start = n
    steps = 0; halv = 0; trip = 0; mx = n; logdrift = 0.0
    while n != 1:
        prev = n
        if n % 2 == 0:
            n //= 2; halv += 1
        else:
            n = (3*n + 1)//2; trip += 1; halv += 1   # 3n+1 always even -> one forced halving
        steps += 1
        logdrift += math.log(n/prev)
        if n > mx: mx = n
        if steps > 100000: return None  # divergence guard (never triggers in range)
    return steps, mx/start, halv, trip, logdrift

LIMIT = 200000
tot_steps=0; max_exc=0.0; max_exc_n=0; tot_halv=0; tot_trip=0; tot_logdrift=0.0; nsteps_total=0
worst_steps=0; worst_n=0
all_reach_1 = True
for n in range(2, LIMIT+1):
    r = trajectory_stats(n)
    if r is None:
        all_reach_1 = False; print("DIVERGENT/long:", n); continue
    s, exc, h, t, ld = r
    tot_steps += s
    if exc > max_exc: max_exc = exc; max_exc_n = n
    if s > worst_steps: worst_steps = s; worst_n = n
    tot_halv += h; tot_trip += t; tot_logdrift += ld; nsteps_total += s

print(f"=== Collatz as Euclid-engine: n in [2,{LIMIT}] ===")
print(f"all reach 1 (no perpetual engine / no foreign cycle in range): {all_reach_1}")
print(f"avg stopping time (steps):           {tot_steps/(LIMIT-1):.2f}")
print(f"worst stopping time:                 {worst_steps} steps at n={worst_n}")
print(f"max excursion ratio (peak/start):    {max_exc:.1f} at n={max_exc_n}  <-- height NOT monotone (>1)")
print(f"total halvings (descent steps):      {tot_halv}")
print(f"total triplings (fuel +1 steps):     {tot_trip}")
print(f"halvings / triplings:                {tot_halv/tot_trip:.4f}")
print(f"  (threshold for descent = log2(3) = {math.log(3)/math.log(2):.4f}; need ratio > this)")
print(f"geometric-mean per-step drift exp(<log ratio>): {math.exp(tot_logdrift/nsteps_total):.4f}  (<1 = fuel net-consumed)")
print(f"  theoretical accel-map drift sqrt(1/2 * 3/2) = {math.sqrt(0.75):.4f}")
