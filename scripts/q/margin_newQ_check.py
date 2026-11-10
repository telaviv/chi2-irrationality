"""Numerical check of the Theorem Q4 margins alphaCore q + c2EvenSharp q + PhiT q at q = 6, 8, 10, 12,
and of the rational upper bounds used in Chi2Irrational/Q/Even/Margin.lean (Arb balls, python-flint)."""
from flint import arb, ctx, fmpq
ctx.prec = 200
def v2(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k
def odd(n): return n >> v2(n)
def cE(e): return fmpq(6 - 4*e, 3*(3*e + 8))
PhiT = {6: fmpq(-256,100), 8: fmpq(-272,100), 10: fmpq(-285,100), 12: fmpq(-295,100)}
L2 = arb(2).log()
for q in (6, 8, 10, 12):
    e = v2(q)
    a = arb(133)/60 + arb(odd(q*q-1)).log()/4 - arb(odd(q)).log()/3
    c2 = (arb(cE(e)) - arb(e)/3) * L2
    print(q, "e =", e, "oddPart(q^2-1) =", odd(q*q-1), "oddPart q =", odd(q), "cE =", cE(e),
          "margin =", (a + c2 + arb(PhiT[q])).str(10))
# bounds used in the Lean proof (log 2 < 0.6931471808)
l2 = arb(fmpq(6931471808, 10**10))
# q=6: log35 <= 2log2 + 2log3 - 1/36, 2log3 <= 3log2 + 1/8
b6 = arb(133)/60 + (2*l2 + 3*l2 + arb(1)/8 - arb(1)/36)/4 - (3*l2 + arb(1)/8)/6 + (arb(cE(1)) - arb(1)/3)*l2 + arb(PhiT[6])
print("q=6 bound", b6.str(10))
# q=8: log63 <= 6log2
print("q=8 bound", (arb(133)/60 + 6*l2/4 + (arb(cE(3)) - 1)*l2 + arb(PhiT[8])).str(10))
# q=10: log99 <= 2log2 + 2log5, log5 <= 2log2 + 1/4
l5 = 2*l2 + arb(1)/4
print("q=10 bound", (arb(133)/60 + (2*l2 + 2*l5)/4 - l5/3 + (arb(cE(1)) - arb(1)/3)*l2 + arb(PhiT[10])).str(10))
# q=12: log143 <= 4log2 + 2log3, log3 <= 2log2
l3 = 2*l2
print("q=12 bound", (arb(133)/60 + (4*l2 + 2*l3)/4 - l3/3 + (arb(cE(2)) - arb(2)/3)*l2 + arb(PhiT[12])).str(10))
