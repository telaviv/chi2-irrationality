"""Numerical checks for TiQ/PoleExpansion.lean and TiQ/Analytic.lean (mpmath, 50 digits).
* aeval_ti2_DeltaT + LamMatT_hasSum: det(A_h + Ti2(1/q) B_h) = lim_T det(HTT q h T), HTT built from nodeTermT
  (W = wT q = -1/q^2, phi(u) = u/D(u), phi'(u) = phi(u)(1/u - sum_k 1/(u - x_k)));
* abs_cNT_le: |cNT| <= bN q h s = Wr^s h phi(s), Wr = 1/q^2, on all triples with s <= 60."""
from fractions import Fraction as Fr
from mpmath import mp, mpf, nsum, inf, matrix, det
from check_defs import AfunT, BfunT
mp.dps = 50
def F(x): return mpf(x.numerator) / x.denominator
ok = True
for q in [2, 3, 6, 7]:
    z = mpf(1) / q
    ti2 = nsum(lambda n: (-1) ** int(n) * z ** (2 * n + 1) / (2 * n + 1) ** 2, [0, inf])
    W = mpf(-1) / q ** 2; Wr = abs(W)
    for h in [2, 3, 4, 5]:
        memo = {}
        mom = [F(AfunT(q, h, [Fr(0)] * m + [Fr(1)], memo)) + ti2 * F(BfunT(q, h, [Fr(0)] * m + [Fr(1)]))
               for m in range(2 * h - 1)]
        dlam = det(matrix([[mom[i + j] for j in range(h)] for i in range(h)]))
        xs = [-(k + mpf(1) / 2) for k in range(h)]
        def phi(u):
            u = mpf(u)
            p = mpf(1)
            for x in xs: p *= u - x
            return u / p
        def dphi(u):
            u = mpf(u)
            return phi(u) * (1 / u - sum(1 / (u - x) for x in xs))
        T = 400
        node = lambda n, t: W ** (t + 1) * (n * (t + 1) ** max(n - 1, 0) * phi(t + 1) * (1 if n > 0 else 0)
                                            + (t + 1) ** n * dphi(t + 1))
        HT = matrix([[sum(node(i + j, t) for t in range(T)) for j in range(h)] for i in range(h)])
        dT = det(HT)
        err = abs(dlam - dT) / max(abs(dlam), mpf(10) ** -40)
        good = err < mpf(10) ** -30
        # |cNT| <= bN
        for s in range(1, 61):
            for c in (W ** s * dphi(s), W ** s * phi(s)):
                good &= abs(c) <= Wr ** s * h * phi(s) * (1 + mpf(10) ** -40)
        ok &= good
        print(f"q={q} h={h}: det(A+Ti2 B) = {mp.nstr(dlam, 12)}, det HTT(T={T}) rel.err = {mp.nstr(err, 3)}, "
              f"|cNT| <= bN: {good}")
print("ALL OK" if ok else "MISMATCH")
