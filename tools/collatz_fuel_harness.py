import math, random
def T(n): return n//2 if n%2==0 else (3*n+1)//2
def next_odd(n):
    m=3*n+1; k=0
    while m%2==0: m//=2; k+=1
    return m,k
# топливо ограничено вдоль траектории
mx=0
for s in range(2,100000):
    n=s; trip=halv=0; em=0
    while n!=1:
        if n%2==0: n//=2; halv+=1
        else: n=(3*n+1)//2; trip+=1; halv+=1
        em=max(em, trip*math.log2(3)-halv)
    mx=max(mx,em)
print(f"макс незакрытое топливо: {mx:.2f}")
# odd->odd монотонность
down=up=0
for n in range(3,2000000,2):
    m,k=next_odd(n);
    if math.log2(m)<math.log2(n): down+=1
    else: up+=1
print(f"odd->odd: падает {100*down/(down+up):.1f}%, растёт {100*up/(down+up):.1f}% (нет монотонности)")
