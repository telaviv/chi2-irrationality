"""Numerical check of the margin bounds in Chi2Irrational/Q/Margin.lean (mpmath, 50 digits)."""
from mpmath import mp, log, mpf
mp.dps = 50
l2, l3 = log(2), log(3)
def v2(n):
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    return v
def odd(n): return n >> v2(n)
def margin(q):
    a = mpf(133)/60 + log(odd(q*q-1))/4 - log(odd(q))/3
    if q % 2: return a + (v2(q*q-1)-2)*l2/4 - mpf(2078)/1000 - log(mpf(q)/3)/2
    return a + (mpf(1)/2 - mpf(v2(q))/3)*l2 - mpf(303)/100 - log(mpf(q)/14)/2
print("odd worst q=3:", margin(3), " max over odd 3..9999:", max(margin(q) for q in range(3, 10000, 2)))
print("even worst q=14:", margin(14), " max over even 14..10000:", max(margin(q) for q in range(14, 10001, 2)))
print("odd crude constant 133/60-2.078-(7/30)log2 (uses 3^5<2^8):", mpf(133)/60 - mpf(2078)/1000 - mpf(7)/30*l2)
print("even crude constant 133/60-3.03+(7/6)log2 (uses 14<16):", mpf(133)/60 - mpf(303)/100 + mpf(7)/6*l2)
