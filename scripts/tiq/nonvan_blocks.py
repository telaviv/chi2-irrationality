"""Lemma P for the Ti machine (TiQ/NonVan/*): check the block formulas of TiQ/NonVan/BlockMat.lean against exact data,
and derive the block determinants as rational functions of q.

1. For K = 3l, E0_ij = nu_ij * AfunT(f_i f_j) (Lean definitions of TiQ/Machine.lean replicated literally, exact
   Fractions).  Checked mod l:
   * every E0_ij is l-integral;
   * red E0_ij = 0 when class i != class j and class j != kappa;
   * for gamma != kappa: red E0(gamma+l r, gamma+l s) = xbar_gamma qbar^{2 gamma} (-1)^{kappa+gamma} red M(S or L)_rs;
   * red E0(kappa+l r, kappa+l s) = red M(D)_rs,
   with the Ti block matrices (TqT_n = sum_{u<n} (-1)^u z^{2u+1}/(2u+1)^2, z = 1/q, w = -1/q^2):
     M(S)_rs = c_r/(1-w) + [r=s] 4 (-1)^r q^{2r+1} TqT_r,
     M(L)_rs = w c_r/(1-w) + [r=s] 4 (-1)^r q^{2r+1} TqT_{r+1},
     M(D)_rs = w (c_r e_rs/(1-w) + 2 c_r w/(1-w)^2) + [r=s] (-4)(r+1/2) (-1)^r q^{2r+1} TqT_{r+1}.
2. det M(S), det M(L), det M(D) as rational functions of q (sympy), compared with the chi_2 ones at q^2 -> -q^2,
   and an exact Fraction check of the closed forms used in TiQ/NonVan/NonVanT.lean at q = 2..15.
"""
from fractions import Fraction as Fr
from math import comb
import sympy as sp


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


def pmul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r


def Dpoly(K):
    p = [Fr(1)]
    for k in range(K): p = pmul(p, [-pole(k), Fr(1)])
    return p


def divmonic(a, d):
    a = a[:]; n = len(d) - 1; qq = [Fr(0)] * max(len(a) - n, 1)
    for i in range(len(a) - 1, n - 1, -1):
        c = a[i]; qq[i - n] = c
        for j in range(n + 1): a[i - n + j] -= c * d[j]
    return qq


def peval(a, x): return sum(c * x ** i for i, c in enumerate(a))


def AfunT(q, K, g, memo, D):
    gx = [Fr(0)] + g
    Qp = divmonic(gx, D)
    mu = sum(c * muMono(wT(q), d, memo) for d, c in enumerate(Qp))
    return mu + 4 * sum(peval(g, pole(k)) * omega(K, k) * SpartT(q, k) for k in range(K))


def fpoly(K, i):
    p = [Fr(1)]
    for m in range(K):
        if m != i: p = pmul(p, [-pole(m), Fr(1)])
    return p


def red(x, l):
    assert x.denominator % l != 0, ("not l-integral", x)
    return x.numerator * pow(x.denominator, -1, l) % l


def crr(r): return Fr(-1) if r == 1 else Fr(1, 2)
def eD(r, s): return Fr(11, 2) - 2 * r if r == s else Fr(3 - r - s) + Fr(5, 2)
def TqT(q, n): return sum(Fr((-1) ** u) * Fr(1, q) ** (2 * u + 1) / (2 * u + 1) ** 2 for u in range(n))


def MS(q, r, s):
    w = wT(q)
    return crr(r) / (1 - w) + (4 * (-1) ** r * Fr(q) ** (2 * r + 1) * TqT(q, r) if r == s else 0)


def ML(q, r, s):
    w = wT(q)
    return w * crr(r) / (1 - w) + (4 * (-1) ** r * Fr(q) ** (2 * r + 1) * TqT(q, r + 1) if r == s else 0)


def MD(q, r, s):
    w = wT(q)
    return (w * (crr(r) * eD(r, s) / (1 - w) + crr(r) * 2 * w / (1 - w) ** 2)
            + (-4 * (r + Fr(1, 2)) * (-1) ** r * Fr(q) ** (2 * r + 1) * TqT(q, r + 1) if r == s else 0))


def check(q, l):
    K = 3 * l; kap = l // 2
    D = Dpoly(K); memo = {}
    f = [fpoly(K, i) for i in range(K)]
    E = [[None] * K for _ in range(K)]
    for i in range(K):
        for j in range(K):
            nu = (Fr(l) if j % l == kap else Fr(l * l)) / dPrime(K, i)
            E[i][j] = nu * AfunT(q, K, pmul(f[i], f[j]), memo, D)
    bad = 0
    for i in range(K):
        for j in range(K):
            e = red(E[i][j], l)
            if i % l != j % l and j % l != kap and e != 0: bad += 1
    for g in range(l):
        for r in range(3):
            for s in range(3):
                e = red(E[g + l * r][g + l * s], l)
                if g == kap:
                    want = red(MD(q, r, s), l)
                else:
                    M = MS if g < kap else ML
                    want = red(pole(g), l) * pow(q, 2 * g, l) * (-1) ** (kap + g) * red(M(q, r, s), l) % l
                if e != want: bad += 1
    return bad


# 1. exact data
for q in [3, 4, 6, 7]:
    for l in [7, 11]:
        if q % l == 0 or (q * q + 1) % l == 0: continue
        print(f"q={q} l={l}: block-formula mismatches = {check(q, l)}", flush=True)

# 2. symbolic determinants
x = sp.symbols('q', positive=True)
w = -1 / x**2
Ts = lambda n: sum(sp.Integer((-1) ** u) * (1 / x) ** (2 * u + 1) / sp.Integer(2 * u + 1) ** 2 for u in range(n))
cr = lambda r: sp.Integer(-1) if r == 1 else sp.Rational(1, 2)
ed = lambda r, s: sp.Rational(11, 2) - 2 * r if r == s else sp.Integer(3 - r - s) + sp.Rational(5, 2)
S = sp.Matrix(3, 3, lambda r, s: cr(r) / (1 - w) + (4 * (-1) ** r * x ** (2 * r + 1) * Ts(r) if r == s else 0))
L = sp.Matrix(3, 3, lambda r, s: w * cr(r) / (1 - w) + (4 * (-1) ** r * x ** (2 * r + 1) * Ts(r + 1) if r == s else 0))
Dm = sp.Matrix(3, 3, lambda r, s: w * (cr(r) * ed(r, s) / (1 - w) + cr(r) * 2 * w / (1 - w) ** 2)
               + (-4 * (r + sp.Rational(1, 2)) * (-1) ** r * x ** (2 * r + 1) * Ts(r + 1) if r == s else 0))
chi = {'S': 8 * x**6 * (9 * x**2 + 1) / (9 * (x**2 - 1)),
       'L': 8 * x**2 * (16200 * x**6 - 10575 * x**4 - 6352 * x**2 + 905) / (2025 * (x**2 - 1)),
       'D': -x**4 * (16200 * x**6 - 51075 * x**4 + 28523 * x**2 + 420) / (135 * (x**2 - 1)**2)}
y = sp.symbols('y')
for name, M in [('S', S), ('L', L), ('D', Dm)]:
    d = sp.factor(sp.cancel(M.det()))
    n, den = sp.fraction(sp.cancel(M.det()))
    print(name, 'det =', d)
    print('   num', sp.expand(n), ' den', sp.factor(den))
    # compare with chi_2 at q^2 -> -q^2:  chi(q) is a function of q^2 times a power of q
    c = sp.cancel(chi[name])

    ratio = sp.simplify(d / c.subs(x, sp.I * x))
    print('   det_Ti / det_chi(i q) =', ratio)

# 3. Fraction check of the closed forms used in Lean (filled in after step 2)
def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


ok = True
for qq in range(2, 16):
    dS = det3([[MS(qq, r, s) for s in range(3)] for r in range(3)])
    dL = det3([[ML(qq, r, s) for s in range(3)] for r in range(3)])
    dD = det3([[MD(qq, r, s) for s in range(3)] for r in range(3)])
    cS = Fr(-72 * qq**8 + 8 * qq**6, 9 * (qq * qq + 1))
    cL = Fr(-129600 * qq**8 - 84600 * qq**6 + 50816 * qq**4 + 7240 * qq**2, 2025 * (qq * qq + 1))
    cD = Fr(16200 * qq**10 + 51075 * qq**8 + 28523 * qq**6 - 420 * qq**4, 135 * (qq * qq + 1)**2)
    if (dS, dL, dD) != (cS, cL, cD):
        ok = False
        print('  mismatch at q =', qq, (dS, dL, dD), (cS, cL, cD))
print('Fraction check of the Lean closed forms, q = 2..15:', ok)
