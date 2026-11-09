"""Numerical checks for Lemma 10_0 (twoAdic_even), exact arithmetic (python-flint).

Built directly from the Lean definitions (Machine.lean, Arith/Free.lean, Arith/TwoAdicEntries.lean).

Part 1 (specialised q): for even q, n2(h) := max_k -v2([X^k] Delta_q h) satisfies
    n2(h) <= E(h) - v2(q) * aQ(h),  E(h) = 2*f*(f+1), f = floor(h/2),  aQ(h) = (h(h-1)-6h) div 3
  (the Lean bound) and also the sharper RESULT form n2 <= floor(h^2/2) - h - aQ*v2(q) (reported).
Part 2 (free ring Q[q,E]): the anchored-basis entries A(a_i b_j), B(a_i b_j) have Gauss
    v2 >= -|i+j+1-h|   and the Gauss v2 of DeltaF h is >= -E(h)   (small h).
"""
import sys
from fractions import Fraction as Fr
from flint import fmpq, fmpq_poly, fmpq_mpoly_ctx

def v2q(x):
    x = Fr(x)
    if x == 0:
        return 10**9
    n, d = x.numerator, x.denominator
    v = 0
    while n % 2 == 0:
        n //= 2; v += 1
    while d % 2 == 0:
        d //= 2; v -= 1
    return v

def pole(k): return Fr(-(2 * k + 1), 2)

def omega(K, k):
    d = Fr(1)
    for m in range(K):
        if m != k:
            d *= pole(k) - pole(m)
    return pole(k) / d

def aQ(h): return max(h * (h - 1) - 6 * h, 0) // 3
def Eb(h):
    f = h // 2
    return 2 * f * (f + 1)

# ---------- Part 1: specialised q ----------
def powsums(w, n):
    s = [w / (1 - w)]
    from math import comb
    for m in range(n):
        s.append(sum(comb(m + 1, j) * (-1) ** (m - j) * s[j] for j in range(m + 1)) / (1 - w))
    return s

def delta_q(q, h):
    w = Fr(1, q * q)
    ps = powsums(w, 2 * h + 2)
    muMono = [Fr(0)] + [(d + 1) * ps[d] for d in range(2 * h + 1)]
    D = fmpq_poly([1])
    for k in range(h):
        D *= fmpq_poly([fmpq(-pole(k).numerator, pole(k).denominator) * -1 * -1, 1]) if False else fmpq_poly([fmpq((2*k+1), 2), 1])
    S = [sum(Fr(q) ** (2 * (k - j)) / Fr(2 * j + 1) ** 2 for j in range(k + 1)) for k in range(h)]
    om = [omega(h, k) for k in range(h)]
    A = {}; B = {}
    for n in range(2 * h - 1):
        g = fmpq_poly([0] * (n + 1) + [1])  # X^(n+1) = g*X
        quo = g // D
        mu = sum(Fr(int(quo[d].p), int(quo[d].q)) * muMono[d] for d in range(quo.degree() + 1)) if quo.degree() >= 0 else Fr(0)
        A[n] = mu + 4 * sum(pole(k) ** n * om[k] * S[k] for k in range(h))
        B[n] = -4 * sum(pole(k) ** n * om[k] * Fr(q) ** (2 * k + 1) for k in range(h))
    # det(A + X B) via evaluation/interpolation at h+1 points
    from flint import fmpq_mat
    pts = list(range(h + 1))
    vals = []
    for x in pts:
        M = fmpq_mat(h, h, [fmpq((A[i + j] + x * B[i + j]).numerator, (A[i + j] + x * B[i + j]).denominator)
                            for i in range(h) for j in range(h)])
        vals.append(M.det())
    P = fmpq_poly.interpolate([fmpq(x) for x in pts], vals) if hasattr(fmpq_poly, 'interpolate') else None
    if P is None:
        # Lagrange
        P = fmpq_poly([0])
        for a, ya in zip(pts, vals):
            L = fmpq_poly([1])
            for b in pts:
                if b != a:
                    L *= fmpq_poly([-b, 1]) * fmpq(1, a - b)
            P += L * ya
    return [Fr(int(P[k].p), int(P[k].q)) for k in range(h + 1)]

def part1(qs, hs):
    ok = True
    for q in qs:
        v = v2q(q)
        for h in hs:
            co = delta_q(q, h)
            n2 = max(-v2q(c) for c in co if c != 0)
            lean = Eb(h) - v * aQ(h)
            res = h * h // 2 - h - v * aQ(h)
            good = n2 <= lean
            ok &= good
            print(f"q={q:3d} v2={v} h={h:3d} n2={n2:6d}  RESULT bound={res:6d} (holds={n2 <= res})  "
                  f"Lean bound E-v*aQ={lean:6d} holds={good}  (n2+v*aQ)/h^2={(n2 + v * aQ(h)) / h**2:+.4f}")
    return ok

# ---------- Part 2: free ring ----------
def part2(hs):
    from math import comb
    R = fmpq_mpoly_ctx.get(('q', 'E', 'X'), 'lex')
    qg, Eg, Xg = R.gens()
    def dCoef(n, b):
        return sum((-1) ** (b - k) * comb(b, k) * k ** n for k in range(b + 1))
    def Om(b): return Eg if b == 0 else qg ** 2 * Eg ** (b + 1)
    def muMonoF(d):
        r = qg - qg
        for b in range(d):
            r += fmpq(d * dCoef(d - 1, b)) * Om(b)
        return r
    def gauss_v2(f):
        if f == 0: return 10**9
        return min(v2q(Fr(int(c.p), int(c.q))) for c in f.coeffs())
    ok = True
    for h in hs:
        D = fmpq_poly([1])
        for k in range(h):
            D *= fmpq_poly([fmpq(2 * k + 1, 2), 1])
        SF = [sum(qg ** (2 * (k - j)) * fmpq(1, (2 * j + 1) ** 2) for j in range(k + 1)) for k in range(h)]
        om = [omega(h, k) for k in range(h)]
        def lin(m): return fmpq_poly([fmpq(2 * m + 1, 2), 1])
        def aB(i):
            p = fmpq_poly([1])
            for m in range(i): p *= lin(m)
            return p
        def bB(j):
            p = fmpq_poly([1])
            for m in range(h - j, h): p *= lin(m)
            return p
        def LamF(g):
            quo = (g * fmpq_poly([0, 1])) // D
            mu = (qg-qg)
            for d in range(quo.degree() + 1):
                mu += quo[d] * muMonoF(d)
            s = (qg-qg); t = (qg-qg)
            for k in range(h):
                ck = g(fmpq(pole(k).numerator, pole(k).denominator)) * fmpq(om[k].numerator, om[k].denominator)
                s += ck * SF[k]
                t += ck * qg ** (2 * k + 1)
            return mu + 4 * s, -4 * t
        G = [[None] * h for _ in range(h)]
        for i in range(h):
            for j in range(h):
                a, b = LamF(aB(i) * bB(j))
                e = -abs(i + j + 1 - h)
                va, vb = gauss_v2(a), gauss_v2(b)
                if va < e or vb < e:
                    ok = False
                    print(f"  entry violation h={h} i={i} j={j}: v2(A)={va} v2(B)={vb} bound {e}")
                G[i][j] = a + Xg * b
        # Bareiss determinant
        M = [row[:] for row in G]
        prev = (qg-qg+1); sign = 1
        n = h
        for k in range(n - 1):
            if M[k][k] == 0:
                sw = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
                if sw is None:
                    M = None; break
                M[k], M[sw] = M[sw], M[k]; sign = -sign
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
            prev = M[k][k]
        det = (qg-qg) if M is None else sign * M[n - 1][n - 1]
        vd = gauss_v2(det)
        good = vd >= -Eb(h)
        ok &= good
        print(f"free ring h={h}: Gauss v2(DeltaF)={vd}, -E(h)={-Eb(h)}, RESULT -(floor(h^2/2)-h)={-(h*h//2-h)}, holds={good}")
    return ok

if __name__ == "__main__":
    ok1 = part1([6, 14, 16, 4, 12], list(range(1, 17)))
    ok2 = part2(list(range(1, 8)))
    print("ALL OK" if ok1 and ok2 else "FAILURE")
