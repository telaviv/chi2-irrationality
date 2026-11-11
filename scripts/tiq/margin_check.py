"""Margins of Theorem T with the Lean constants (TiQ/Defs.lean), mpmath 30 digits, every q in [6, 20000):
alphaCoreT q + c2 + beta < 0, c2 = log2/4 (odd q), (c(e) - e/3) log 2 (even q), beta = PhiT6 (q = 6) or
PhiT6 - log(q/6)/2 (q >= 7), PhiT6 = -2.5671 (certified PhiQ = -2.5671799991 at q = 6, L = 800)."""
from mpmath import mp, log, mpf
mp.dps = 30
def vp2(n):
    e = 0
    while n % 2 == 0: n //= 2; e += 1
    return e
def odd(n): return n // 2 ** vp2(n)
Phi = mpf(-25671) / 10000
worst = None
for q in range(6, 20000):
    a = mpf(133) / 60 + log(odd(q * q + 1)) / 4 - log(odd(q)) / 3
    if q % 2: c2 = log(2) / 4
    else:
        e = vp2(q); c2 = (mpf(6 - 4 * e) / (3 * (3 * e + 8)) - mpf(e) / 3) * log(2)
    m = a + c2 + Phi - (log(mpf(q) / 6) / 2 if q > 6 else 0)
    if q < 16 or q % 5000 == 0: print(q, mp.nstr(m, 10))
    assert m < 0, q
    if worst is None or m > worst[1]: worst = (q, m)
print("all negative; worst", worst[0], mp.nstr(worst[1], 10))
