"""Check the Lean definitions of TiQ/Machine.lean (replicated literally, exact Fractions) against the pilot's
Ti machine (pilot_ti2q/ti_machine.py, build_AB with sign -1) and against the identity Delta^Ti = P_h(-q^2, qX)
(pilot_ti2q/verify_identity.py, build_Q).  Also: ti2(1/q) vs A + theta B against the defining series (Lemma 1)."""
import sys
from fractions import Fraction as Fr
from math import comb
sys.path.insert(0, r"C:\Users\Shawn Krisman\math\handoff\log2log3\pilot_ti2q")
from flint import fmpq, fmpq_poly
from ti_machine import build_AB, delta_poly
from verify_identity import build_Q

def pole(k): return -(Fr(k) + Fr(1, 2))
def dPrime(K, k):
    p = Fr(1)
    for m in range(K):
        if m != k: p *= pole(k) - pole(m)
    return p
def omega(K, k): return pole(k) / dPrime(K, k)
def powSum(w, n, memo):
    if n in memo: return memo[n]
    if n == 0: r = w / (1 - w)
    else: r = sum(comb(n, j) * (-1) ** (n - 1 - j) * powSum(w, j, memo) for j in range(n)) / (1 - w)
    memo[n] = r; return r
def muMono(w, d, memo): return Fr(0) if d == 0 else d * powSum(w, d - 1, memo)
def wT(q): return Fr(-1, q * q)
def SpartT(q, k): return sum(Fr((-1) ** (k - j) * q ** (2 * (k - j)), (2 * j + 1) ** 2) for j in range(k + 1))
def poleW(q, k): return (-1) ** k * Fr(q) ** (2 * k + 1)
# polynomials as lists of Fractions (low degree first)
def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def Dpoly(K):
    p = [Fr(1)]
    for k in range(K): p = pmul(p, [-pole(k), Fr(1)])
    return p
def divmonic(a, d):  # quotient of a by monic d
    a = a[:]; n = len(d) - 1; qq = [Fr(0)] * max(len(a) - n, 1)
    for i in range(len(a) - 1, n - 1, -1):
        c = a[i]; qq[i - n] = c
        for j in range(n + 1): a[i - n + j] -= c * d[j]
    return qq
def peval(a, x): return sum(c * x ** i for i, c in enumerate(a))
def AfunT(q, K, g, memo):
    gx = [Fr(0)] + g
    Qp = divmonic(gx, Dpoly(K))
    mu = sum(c * muMono(wT(q), d, memo) for d, c in enumerate(Qp))
    return mu + 4 * sum(peval(g, pole(k)) * omega(K, k) * SpartT(q, k) for k in range(K))
def BfunT(q, K, g):
    return -4 * sum(peval(g, pole(k)) * omega(K, k) * poleW(q, k) for k in range(K))
ok = True
for q in [2, 3, 5, 6, 7, 8]:
    for h in [1, 2, 3, 5, 8]:
        memo = {}
        A = [AfunT(q, h, [Fr(0)] * m + [Fr(1)], memo) for m in range(2 * h - 1)]
        B = [BfunT(q, h, [Fr(0)] * m + [Fr(1)]) for m in range(2 * h - 1)]
        Ap, Bp = build_AB(q, h, -1)
        e1 = all(fmpq(A[i].numerator, A[i].denominator) == Ap[i] and fmpq(B[i].numerator, B[i].denominator) == Bp[i]
                 for i in range(2 * h - 1))
        A2, B2 = build_Q(fmpq(-q * q), h)
        e2 = all(fmpq(A[i].numerator, A[i].denominator) == A2[i] and fmpq(B[i].numerator, B[i].denominator) == q * B2[i]
                 for i in range(2 * h - 1))
        ok &= e1 and e2
        print(f"q={q} h={h}: Lean defs = pilot Ti machine: {e1};  = P_h(-q^2, qX) entries: {e2}")
# Lemma 1 for Ti: A(g) + Ti2(1/q) B(g) = sum_t w^t (g u/D)'(t), floats via mpmath
from mpmath import mp, mpf, nsum, inf, diff
mp.dps = 40
for q in [3, 6, 7]:
    z = mpf(1) / q
    ti2 = nsum(lambda n: (-1) ** int(n) * z ** (2 * n + 1) / (2 * n + 1) ** 2, [0, inf])
    for h in [2, 3]:
        memo = {}
        for m in range(2 * h - 1):
            g = [Fr(0)] * m + [Fr(1)]
            a = AfunT(q, h, g, memo); b = BfunT(q, h, g)
            D = Dpoly(h)
            f = lambda u: u ** m * u / sum(float(c) * u ** i if False else mpf(c.numerator) / c.denominator * u ** i for i, c in enumerate(D))
            w = mpf(-1) / q ** 2
            ser = nsum(lambda t: w ** t * diff(f, t), [1, inf])
            lhs = mpf(a.numerator) / a.denominator + ti2 * mpf(b.numerator) / b.denominator
            err = abs(lhs - ser)
            ok &= err < mpf(10) ** -25
            print(f"Lemma 1 q={q} h={h} m={m}: |A + Ti2 B - series| = {mp.nstr(err, 3)}")
print("ALL OK" if ok else "MISMATCH")
