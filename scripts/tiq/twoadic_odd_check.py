"""Exact checks for TiQ/TwoAdicEntries.lean, TiQ/TwoAdicNu1.lean (twoAdic_odd_t, Lemma 10_1 at odd q, nu = 1).
Checks the intermediate statements proved in Lean, at odd q:
 (1) v2(OmQ(wT q, b)) = -(b+1)                                   (V2_OmQT)
 (2) v2(Delta^m T(0)) >= m - 1 for T(l) = SpartT(q, i+l), poleW(q, i+l)   (V2_fd_seq1)
 (3) (U) entries (4/N!) Delta^N[pole(i+l) T(i+l)](0): v2 >= 0     (V2_U1)
 (4) anchored entries: (L) v2 >= -pi - 1 - floor(log2 pi), B = 0; (U) v2 >= 0   (V2_entryT)
 (5) n2(h) = -min_k v2([X^k] DeltaT) <= betaP(h) + h (floor(log2 h) + 2)          (twoAdic_DeltaT)
Usage: python twoadic_odd_check.py   (writes nothing; output committed as twoadic_odd_check.txt)
"""
import sys
from fractions import Fraction as Fr
from math import comb, factorial
sys.path.insert(0, r"C:\Users\Shawn Krisman\math\handoff\log2log3\pilot_ti2q")
from flint import fmpq, fmpq_poly
from ti_machine import build_AB, delta_poly


def v2(x):
    x = Fr(x)
    if x == 0: return 10**9
    n, d, v = x.numerator, x.denominator, 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v


def v2f(c):
    return v2(Fr(int(c.p), int(c.q)))


def log2f(n): return n.bit_length() - 1 if n > 0 else 0


def pole(k): return -(Fr(k) + Fr(1, 2))
def wT(q): return Fr(-1, q * q)
def SpartT(q, k): return sum(Fr((-1) ** (k - j) * q ** (2 * (k - j)), (2 * j + 1) ** 2) for j in range(k + 1))
def poleW(q, k): return (-1) ** k * Fr(q) ** (2 * k + 1)
def OmQ(w, b): return w / (1 - w) if b == 0 else w ** b / (1 - w) ** (b + 1)
def fd(f, m, y=0): return sum((-1) ** (m - l) * comb(m, l) * f(y + l) for l in range(m + 1))
def rPot(h, a): return max(0, a + 1 - (h + 1) // 2)
def cPot(h, b): return max(0, b - h // 2)
def betaP(h): return sum(rPot(h, a) for a in range(h)) + sum(cPot(h, b) for b in range(h))


bad = 0
for q in [3, 5, 7, 9, 15, 17]:
    # (1)
    for b in range(30):
        if v2(OmQ(wT(q), b)) != -(b + 1): bad += 1; print("OmQ fail", q, b)
    # (2), (3)
    mn2, mn3 = 10**9, 10**9
    for i in range(8):
        for T in (lambda l: SpartT(q, i + l), lambda l: poleW(q, i + l)):
            for m in range(16):
                s = v2(fd(T, m)) - (m - 1); mn2 = min(mn2, s)
                if s < 0: bad += 1; print("fd_seq fail", q, i, m)
                e = Fr(4, factorial(m)) * fd(lambda l: pole(i + l) * T(l), m)
                mn3 = min(mn3, v2(e))
                if v2(e) < 0: bad += 1; print("U fail", q, i, m)
    print(f"q={q}: (1) ok; (2) min slack v2(Delta^m T(0)) - (m-1) = {mn2}; (3) min v2 of U-entry = {mn3}")
    # (4), (5)
    for h in [2, 3, 4, 5, 6, 8, 10, 12]:
        K = h
        A, B = build_AB(q, h, -1)
        u = fmpq_poly([0, 1])
        a = [fmpq_poly([1])]; bb = [fmpq_poly([1])]
        for i in range(1, h):
            a.append(a[-1] * (u + (i - 1) + fmpq(1, 2))); bb.append(bb[-1] * (u + (K - i) + fmpq(1, 2)))
        slackL, minU = 10**9, 10**9
        for i in range(h):
            for j in range(h):
                g = a[i] * bb[j]
                GA = sum((g[n] * A[n] for n in range(g.degree() + 1)), fmpq(0))
                GB = sum((g[n] * B[n] for n in range(g.degree() + 1)), fmpq(0))
                pi = i + j + 1 - K
                if pi >= 1:
                    if GB != 0: bad += 1; print("B_L nonzero", q, h, i, j)
                    s = v2f(GA) + pi + 1 + log2f(pi); slackL = min(slackL, s)
                    if s < 0: bad += 1; print("L fail", q, h, i, j)
                else:
                    v = min(v2f(GA), v2f(GB)); minU = min(minU, v)
                    if v < 0: bad += 1; print("U entry fail", q, h, i, j)
        D = delta_poly(A, B, h)
        n2 = -min(v2f(D[k]) for k in range(D.degree() + 1))
        bound = betaP(h) + h * (log2f(h) + 2)
        if n2 > bound: bad += 1; print("n2 fail", q, h)
        print(f"  h={h}: (4) min (L) slack {slackL}, min v2 (U) {minU}; (5) n2={n2} <= betaP+h(log2 h+2)={bound}"
              f" (floor(h^2/4)={h*h//4})")
print("violations:", bad)
