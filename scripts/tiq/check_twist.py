"""Check the coefficient twist used in TiQ/Free.lean (exact, sympy):
DeltaF_h in Q[q,E][X] (Arith/Free.lean: Omega_0 = E, Omega_b = q^2 E^{b+1}); twist each monomial q^n E^m X^j by
tw(j; n, m) = (-1)^(m + j + (n+j)/2) (parity: n + j is even on the support); then substituting q = q0,
E = 1/(q0^2+1) gives DeltaT q0 h (TiQ/Machine.lean, replicated in check_defs.py)."""
import sympy as sp
from fractions import Fraction as Fr
from math import comb
from check_defs import AfunT, BfunT, pole, omega, Dpoly, divmonic, peval
q, E, X = sp.symbols('q E X')
def dCoef(n, b): return sum((-1) ** (b - k) * comb(b, k) * k ** n for k in range(b + 1))
def OmegaF(b): return E if b == 0 else q ** 2 * E ** (b + 1)
def muMonoF(d): return sum(sp.Rational(d * dCoef(d - 1, b)) * OmegaF(b) for b in range(d))
def SpartF(k): return sum(q ** (2 * (k - j)) * sp.Rational(1, (2 * j + 1) ** 2) for j in range(k + 1))
def R(x): return sp.Rational(x.numerator, x.denominator)
def AfunF(K, m):
    g = [Fr(0)] * m + [Fr(1)]
    Qp = divmonic([Fr(0)] + g, Dpoly(K))
    return sum(R(c) * muMonoF(d) for d, c in enumerate(Qp)) + 4 * sum(R(peval(g, pole(k)) * omega(K, k)) * SpartF(k) for k in range(K))
def BfunF(K, m):
    g = [Fr(0)] * m + [Fr(1)]
    return -4 * sum(R(peval(g, pole(k)) * omega(K, k)) * q ** (2 * k + 1) for k in range(K))
ok = True
for h in [1, 2, 3, 4]:
    M = sp.Matrix(h, h, lambda i, j: AfunF(h, i + j) + X * BfunF(h, i + j))
    DF = sp.Poly(sp.expand(M.det()), q, E, X)
    parity = all((n + j) % 2 == 0 for (n, m, j) in DF.monoms())
    DFT = sum(c * (-1) ** (m + j + (n + j) // 2) * q ** n * E ** m * X ** j for (n, m, j), c in zip(DF.monoms(), DF.coeffs()))
    for q0 in [2, 3, 6, 7]:
        memo = {}
        MT = sp.Matrix(h, h, lambda i, j: R(AfunT(q0, h, [Fr(0)] * (i + j) + [Fr(1)], memo)) + X * R(BfunT(q0, h, [Fr(0)] * (i + j) + [Fr(1)])))
        DT = sp.expand(MT.det())
        ev = sp.expand(DFT.subs({q: q0, E: sp.Rational(1, q0 ** 2 + 1)}))
        e = sp.simplify(DT - ev) == 0
        ok &= e and parity
        print(f"h={h} q0={q0}: parity {parity}, twisted DeltaF at (q0, 1/(q0^2+1)) = DeltaT: {e}")
print("ALL OK" if ok else "MISMATCH")
