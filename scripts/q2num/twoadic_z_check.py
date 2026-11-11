"""Lemma 10'' (QZ/TwoAdic*.lean): exact check of the entry bounds, the potentials and n2(h) at zeta = q/2, q odd.

Follows the Lean definitions (QZ/Machine.lean): K = h, poles x_k = -(k + 1/2), omega_k = x_k / D'(x_k),
A(g) = mu((g X) div D) + 4 sum_k g(x_k) omega_k S_k(zeta),  B(g) = -4 sum_k g(x_k) omega_k zeta^(2k+1),
mu(u^d) = sum_{b<d} d dCoef(d-1, b) Omega_b,  Omega_0 = E, Omega_b = zeta^2 E^(b+1),  E = 1/(zeta^2 - 1).
Anchored basis a_i = prod_{m<i}(X - x_m), b_j = prod_{h-j<=m<h}(X - x_m).

Checked (exact, fractions):
  (L) i+j >= h, pi = i+j+1-h:   v2(A), v2(B) >= -pi          (B = 0)
  (U) i+j <  h, N = h-1-i-j:    v2(A), v2(B) >= -2i - 3N
  potentials (a = floor((4h+2)/3)):  U_i = -i (3i < 2h), i - a (else);  V_j = 3h - 3j (3j < 2h), j + 1 - h + a (else)
  c(i,j) <= U_i + V_j with c = pi on (L), 2i + 3N on (U)
  n2(h) = sum U + sum V = 4hm - 3m^2 + 2m, m = floor((2h+2)/3);  3 n2(h) <= 4h^2 + 4h + 4
  -v2(coeff_k Delta_h) <= n2(h) for every k (Delta_h = det(A + X B), by interpolation)
Usage: python twoadic_z_check.py   (writes twoadic_z_check.txt next to it)
"""
from fractions import Fraction as F
from math import comb
import os, sys


def v2(x):
    x = F(x)
    if x == 0:
        return 10 ** 9
    n, d, v = x.numerator, x.denominator, 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v


def pmul(p, r):
    out = [F(0)] * (len(p) + len(r) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(r):
            out[i + j] += a * b
    return out


def peval(p, x):
    s = F(0)
    for c in reversed(p): s = s * x + c
    return s


def pdivmonic(p, d):
    p = p[:]; n = len(d) - 1
    if len(p) - 1 < n: return [F(0)]
    q = [F(0)] * (len(p) - n)
    for k in range(len(p) - 1, n - 1, -1):
        c = p[k]; q[k - n] = c
        for t in range(n + 1): p[k - n + t] -= c * d[t]
    return q


def dcoef(n, b):
    return sum((-1) ** (b - k) * comb(b, k) * k ** n for k in range(b + 1))


def det(M):
    M = [r[:] for r in M]; n = len(M); s = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return F(0)
        if p != c: M[c], M[p] = M[p], M[c]; s = -s
        s *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f: M[r] = [M[r][t] - f * M[c][t] for t in range(n)]
    return s


def interp(ts, ys):
    n = len(ts); coeffs = [F(0)] * n
    for i in range(n):
        basis = [F(1)]; den = F(1)
        for j in range(n):
            if j != i: basis = pmul(basis, [F(-ts[j]), F(1)]); den *= ts[i] - ts[j]
        for k in range(n): coeffs[k] += ys[i] * basis[k] / den
    return coeffs


def run(q, h, out):
    z = F(q, 2); E = 1 / (z * z - 1)
    Om = lambda b: E if b == 0 else z * z * E ** (b + 1)
    mu_mono = lambda d: sum(d * dcoef(d - 1, b) * Om(b) for b in range(d))
    K = h; xs = [-(k + F(1, 2)) for k in range(K)]
    D = [F(1)]
    for x in xs: D = pmul(D, [-x, F(1)])
    S = [sum(z ** (2 * (k - j)) / F((2 * j + 1) ** 2) for j in range(k + 1)) for k in range(K)]
    om = []
    for k in range(K):
        dp = F(1)
        for m in range(K):
            if m != k: dp *= xs[k] - xs[m]
        om.append(xs[k] / dp)

    def AB(g):
        Q = pdivmonic(pmul(g, [F(0), F(1)]), D)
        A = sum(c * mu_mono(d) for d, c in enumerate(Q)) + 4 * sum(peval(g, xs[k]) * om[k] * S[k] for k in range(K))
        B = -4 * sum(peval(g, xs[k]) * om[k] * z ** (2 * k + 1) for k in range(K))
        return A, B

    aB = [[F(1)]]
    for i in range(1, h): aB.append(pmul(aB[-1], [-xs[i - 1], F(1)]))
    bB = [[F(1)]]
    for j in range(1, h): bB.append(pmul(bB[-1], [-xs[K - j], F(1)]))
    a = (4 * h + 2) // 3
    U = [-i if 3 * i < 2 * h else i - a for i in range(h)]
    V = [3 * h - 3 * j if 3 * j < 2 * h else j + 1 - h + a for j in range(h)]
    GA = [[None] * h for _ in range(h)]; GB = [[None] * h for _ in range(h)]
    viol = 0; pviol = 0; smin = {'L': 10 ** 9, 'U': 10 ** 9}
    for i in range(h):
        for j in range(h):
            A, B = AB(pmul(aB[i], bB[j])); GA[i][j] = A; GB[i][j] = B
            if i + j >= h:
                bd = -(i + j + 1 - h); c = i + j + 1 - h; t = 'L'
                if B != 0: viol += 1
            else:
                N = h - 1 - i - j; bd = -2 * i - 3 * N; c = 2 * i + 3 * N; t = 'U'
            v = min(v2(A), v2(B))
            if v < bd: viol += 1
            smin[t] = min(smin[t], v - bd)
            if c > U[i] + V[j]: pviol += 1
    n2 = sum(U) + sum(V)
    m = (2 * h + 2) // 3
    closed = 4 * h * m - 3 * m * m + 2 * m
    ts = list(range(h + 1))
    ys = [det([[GA[i][j] + t * GB[i][j] for j in range(h)] for i in range(h)]) for t in ts]
    co = interp(ts, ys)
    # cross-check against the monomial Hankel determinant at t = 1 (unitriangular change of basis)
    H = [[sum(AB([F(0)] * (r + s) + [F(1)])) for s in range(h)] for r in range(h)]
    same = det(H) == ys[1]
    ex = max(-v2(c) for c in co if c != 0)
    line = (f"q={q} h={h}: entry viol={viol} min slack L={smin['L']} U={smin['U']}  potential viol={pviol}  "
            f"n2={n2} closed={closed} 3n2<=4h^2+4h+4:{3 * n2 <= 4 * h * h + 4 * h + 4}  "
            f"exact max -v2(coeff)={ex} <= n2:{ex <= n2}  anchored=monomial:{same}")
    print(line, flush=True); out.write(line + "\n")
    return viol == 0 and pviol == 0 and n2 == closed and ex <= n2 and same and 3 * n2 <= 4 * h * h + 4 * h + 4


if __name__ == '__main__':
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'twoadic_z_check.txt')
    ok = True
    with open(path, 'w') as out:
        for q in (3, 5, 7, 9, 15, 177):
            for h in range(1, 13):
                ok &= run(q, h, out)
        # potentials and closed form alone, larger h
        for h in range(1, 400):
            a = (4 * h + 2) // 3
            U = [-i if 3 * i < 2 * h else i - a for i in range(h)]
            V = [3 * h - 3 * j if 3 * j < 2 * h else j + 1 - h + a for j in range(h)]
            bad = sum(1 for i in range(h) for j in range(h)
                      if (i + j + 1 - h if i + j >= h else 2 * i + 3 * (h - 1 - i - j)) > U[i] + V[j])
            m = (2 * h + 2) // 3; n2 = sum(U) + sum(V)
            if bad or n2 != 4 * h * m - 3 * m * m + 2 * m or 3 * n2 > 4 * h * h + 4 * h + 4:
                ok = False; out.write(f"potential check FAILED at h={h}\n")
        out.write(f"potentials + closed form + 3 n2 <= 4h^2+4h+4 checked for h < 400\nALL OK: {ok}\n")
    print("ALL OK:", ok)
