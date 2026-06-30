#!/usr/bin/env python3
"""
twin_certify — детерминированный сертификатор пар простых-близнецов из доказанных законов.

Опирается на МАШИННО ДОКАЗАННУЮ лемму (EuclidsPath/Engine/Residuals.lean):
  `oldfree_below_sq_prime` / `sink_is_twin`:
    если ни один простой p с 5 ≤ p ≤ A делит 6m-1 или 6m+1,  И  6m+1 < A² ,
    то 6m-1 и 6m+1 ОБА простые  (ДОКАЗАТЕЛЬСТВО, не вероятность).
Плюс channel-law колесо (EuclidsPath/Engine/PaymentLedger.lean): центр-близнец избегает
  m ≡ ±6⁻¹ (mod q) для малых q — быстрый предфильтр.

См. tools/README_twin_certify.md — ниша, границы, бенчмарк.
"""
import sys, time, math, random

def sieve_primes(n):
    if n < 2: return []
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

def wheel_forbidden(wheel_qs):
    forb = {}
    for q in wheel_qs:
        i6 = pow(6, -1, q); forb[q] = {i6 % q, (-i6) % q}
    return forb

def wheel_pass(m, forb):
    return all(m % q not in bad for q, bad in forb.items())

def size_guard(hi):
    A = math.isqrt(6 * hi + 1) + 1
    npr = int(A / math.log(A)) if A > 2 else 1
    return A, npr, (A <= 2 * 10**8)

def certify_window(lo, hi, use_wheel=True, wheel_bound=50):
    A, _, feasible = size_guard(hi)
    if not feasible:
        raise ValueError(f"hi={hi} вне ниши: нужно сито до A={A} (>2e8). "
                         f"Лемма упирается в √(6m+1), как trial-division.")
    sp = [p for p in sieve_primes(A) if p >= 5]
    forb = wheel_forbidden([p for p in sp if p <= wheel_bound]) if use_wheel else {}
    out = []
    for m in range(max(lo, 1), hi + 1):
        a, b = 6*m - 1, 6*m + 1
        if a < 5:
            sb = set(sieve_primes(b))
            if a in sb and b in sb: out.append(m)
            continue
        if use_wheel and not wheel_pass(m, forb): continue
        of = True
        for p in sp:
            if p * p > b: break
            if a % p == 0 or b % p == 0: of = False; break
        if of: out.append(m)
    return out, A

def certify_one(m):
    a, b = 6*m - 1, 6*m + 1
    if a < 2: return False, "нет пары"
    A = math.isqrt(b) + 1
    for p in sieve_primes(A):
        if p < 5: continue
        if p * p > b: break
        if a % p == 0 or b % p == 0: return False, f"делитель {p} (не близнец)"
    return True, f"СЕРТИФИЦИРОВАНО: ({a}, {b}); сито до A={A}"

def is_prime_mr(n, k=20):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for _ in range(k):
        a = random.randrange(2, n-1); x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def bench(hi):
    random.seed(7)
    print(f"=== БЕНЧМАРК: окно центров до hi={hi}, числа до {6*hi+1} ===\n")
    A, npr, feasible = size_guard(hi)
    print(f"граница ниши: сито до A=√(6·hi+1)={A} (~{npr} простых), practical={feasible}\n")
    K = min(20000, hi)
    cands = sorted(random.sample(range(1, hi+1), K))
    sp = [p for p in sieve_primes(A) if p >= 5]
    t = time.time(); cert = []
    for m in cands:
        a, b = 6*m-1, 6*m+1
        if a < 5: continue
        of = True
        for p in sp:
            if p*p > b: break
            if a % p == 0 or b % p == 0: of = False; break
        if of: cert.append(m)
    t_lemma = time.time() - t
    t = time.time(); mr = [m for m in cands if is_prime_mr(6*m-1) and is_prime_mr(6*m+1)]
    t_mr = time.time() - t
    print(f"[НИША: разреженные кандидаты + детерминированный сертификат]")
    print(f"  лемма (ДОКАЗАТЕЛЬСТВО): {len(cert)} близнецов, {t_lemma:.3f}s")
    print(f"  Miller-Rabin x2 (вероятн.): {len(mr)} близнецов, {t_mr:.3f}s")
    print(f"  идентично: {cert==mr};  ускорение лемма/MR: {t_mr/max(t_lemma,1e-9):.2f}x\n")
    N = 6*hi+1; t = time.time()
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    allt = [m for m in range(1,hi+1) if s[6*m-1] and s[6*m+1]]
    t_seg = time.time()-t
    print(f"[НЕ ниша: все близнецы подряд] полное сито: {len(allt)}, {t_seg:.3f}s (сито выигрывает)")

def main():
    if len(sys.argv) < 2: print(__doc__); return
    cmd = sys.argv[1]
    if cmd == "certify":
        ok, msg = certify_one(int(sys.argv[2])); print(("OK " if ok else "NO ") + msg)
    elif cmd == "window":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        try:
            res, A = certify_window(lo, hi)
            print(f"{len(res)} сертифицированных центров в [{lo},{hi}] (сито до A={A}); первые: {res[:12]}")
        except ValueError as e: print("ОТКАЗ:", e)
    elif cmd == "list":
        for m in (int(x) for x in sys.argv[2:]):
            ok, msg = certify_one(m); print(f"m={m}: " + ("OK " if ok else "NO ") + msg)
    elif cmd == "bench":
        bench(int(sys.argv[2]))
    else: print(__doc__)

if __name__ == "__main__":
    main()
