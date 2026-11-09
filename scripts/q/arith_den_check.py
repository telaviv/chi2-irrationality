"""Check the general-q denominator of Chi2Irrational/Q/Arith.lean on exact Delta_h (Machine.lean definitions).

den h = 2^{n2 h} * prod_{odd p <= 2h+q^2} p^{eN q h p} / oddPart(q)^{aQ h}, with
  eN = 2h*lev(h,p) + v_p(q^2-1)*betaP(h)   if p | q(q^2-1),
  eN = eGen(h,p)                            otherwise,
and n2 h = -min_k v_2(coeff_k) (the honest 2-adic exponent).  Verify den*coeff in Z for every coefficient.
Exact arithmetic (python-flint fmpq).  Run from this folder: python arith_den_check.py
"""
from flint import fmpq, fmpq_poly, fmpq_mat, fmpz
from math import comb
import sys

def pole(k): return fmpq(-(2 * k + 1), 2)

def Delta(q, h):
    K = h
    D = fmpq_poly([1])
    for k in range(K):
        D *= fmpq_poly([-pole(k), 1])
    def dPrime(k):
        r = fmpq(1)
        for m in range(K):
            if m != k: r *= pole(k) - pole(m)
        return r
    omega = [pole(k) / dPrime(k) for k in range(K)]
    S = [sum((fmpq(q) ** (2 * (k - j)) / fmpq((2 * j + 1) ** 2) for j in range(k + 1)), fmpq(0)) for k in range(K)]
    w = fmpq(1, q * q)
    ps = []
    def powSum(n):
        while len(ps) <= n:
            m = len(ps)
            if m == 0: ps.append(w / (1 - w))
            else:
                nn = m - 1
                ps.append(sum((fmpq(comb(nn + 1, j)) * (-1) ** (nn - j) * ps[j] for j in range(nn + 1)), fmpq(0)) / (1 - w))
        return ps[n]
    def muMono(d): return fmpq(0) if d == 0 else d * powSum(d - 1)
    def mu(R): return sum((R[d] * muMono(d) for d in range(R.degree() + 1)), fmpq(0))
    def A(n):
        g = fmpq_poly([0] * n + [1])
        R = (g * fmpq_poly([0, 1])) // D
        return mu(R) + 4 * sum((pole(k) ** n * omega[k] * S[k] for k in range(K)), fmpq(0))
    def B(n):
        return -4 * sum((pole(k) ** n * omega[k] * fmpq(q) ** (2 * k + 1) for k in range(K)), fmpq(0))
    As = [A(n) for n in range(2 * h - 1)]; Bs = [B(n) for n in range(2 * h - 1)]
    Am = fmpq_mat(h, h, [As[i + j] for i in range(h) for j in range(h)])
    Bm = fmpq_mat(h, h, [Bs[i + j] for i in range(h) for j in range(h)])
    xs = list(range(h + 1))
    ys = [(Am + Bm * fmpq(x)).det() for x in xs]
    coef = list(ys)
    for j in range(1, h + 1):
        for i in range(h, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) / fmpq(xs[i] - xs[i - j])
    poly = fmpq_poly([coef[-1]])
    for i in range(h - 1, -1, -1):
        poly = poly * fmpq_poly([-xs[i], 1]) + fmpq_poly([coef[i]])
    return [poly[k] for k in range(h + 1)]

def isprime(n): return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))
def vp(n, p):
    v = 0
    while n % p == 0: n //= p; v += 1
    return v
def vpq(x, p):
    return vp(int(x.p), p) - vp(int(x.q), p)
def oddPart(n): return n >> vp(n, 2)
def lev(h, p): return sum(1 for e in range(1, 2 * h + 1) if p ** e <= 2 * h - 1)
def betaP(h):
    return sum(max(a + 1 - (h + 1) // 2, 0) for a in range(h)) + sum(max(b - h // 2, 0) for b in range(h))
def aQ(h): return max(h * (h - 1) - 6 * h, 0) // 3
def wAtom(d, k): return max((2 if d <= 2 * k + 1 else 0) - (1 if (2 * k + 1) % d == 0 else 0), 0)
def clSize(K, d, m): return max(K - 1 - m % d, 0) // d + 1
def wMax(d, m): return max(wAtom(d, m % d + j * d) for j in range(m // d + 1))
def classBd(K, d): return sum(max(2 * (m // d) + 1 + wMax(d, m) - clSize(K, d, m), 0) for m in range(K))
def eGen(h, p): return classBd(h, p) if (2 * h < p * p and 2 * h <= 5 * p) else 2 * h * lev(h, p)
def eN(q, h, p):
    if (q * (q * q - 1)) % p == 0: return 2 * h * lev(h, p) + vp(q * q - 1, p) * betaP(h)
    return eGen(h, p)

def check(q, h):
    cs = Delta(q, h)
    nz = [c for c in cs if c != 0]
    n2 = -min(vpq(c, 2) for c in nz)
    num = fmpz(1)
    for p in range(3, 2 * h + q * q + 1):
        if isprime(p): num *= fmpz(p) ** eN(q, h, p)
    den = fmpq(num, oddPart(q) ** aQ(h)) * (fmpq(2) ** n2 if n2 >= 0 else fmpq(1, 2 ** (-n2)))
    bad = [k for k, c in enumerate(cs) if (den * c).q != 1]
    # slack at the special odd primes: min over k of v_p(den*coeff)
    slack = {}
    for p in range(3, q * q + 1):
        if isprime(p) and (q * (q * q - 1)) % p == 0:
            slack[p] = min(vpq(den * c, p) for c in nz)
    return n2, bad, slack

if __name__ == "__main__":
    qs = [3, 5, 7, 9, 15, 21, 45, 4, 6, 12, 14, 18]
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    allok = True
    for q in qs:
        for h in range(1, H + 1):
            n2, bad, slack = check(q, h)
            ok = not bad
            allok &= ok
            print(f"q={q:3d} h={h:2d} n2={n2:4d} int={'OK' if ok else 'FAIL ' + str(bad)} slack(special odd p)={slack}", flush=True)
    print("ALL OK" if allok else "FAILURES")
