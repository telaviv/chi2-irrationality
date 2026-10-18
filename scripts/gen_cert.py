"""Generate a kernel-checkable dual certificate for Theorem B (`Chi2Irrational/Cert/DataQ*.lean`).

Usage: python gen_cert.py q L s K X N out.lean name
  q = 3: python scripts/gen_cert.py 3 100 5 30 3 2 Chi2Irrational/Cert/DataQ3.lean Q3
  q = 5: python scripts/gen_cert.py 5 40 2 23 2 2 Chi2Irrational/Cert/DataQ5.lean Q5
Requires numpy, scipy, mpmath.

1. Optimise a step density mu (heights c_j on cells [j s/L, (j+1) s/L], j < K) for the dual functional (float, scipy).
2. Rationalise: c_j dyadic (2^-16), exact mass sum(c) * s = L, 0 <= c_j <= 2.
3. Replicate EXACTLY (python Fractions) the Lean interval arithmetic of Cert/Core.lean and Interval/{Basic,Log}.lean:
   the log table (entryOK), termIV/sum0/sum1 per grid cell, EIV. The cell bounds S_k are the exact interval upper
   endpoints rounded up to 10^-12; E_lo the exact lower endpoint rounded down. So every kernel check passes.
4. Choose lambda (optimal: an order statistic of the S_k), report Phi = -E_lo + lam + (2/L) sum (S_k - lam)_+.
Nothing here is trusted: Lean re-checks every number.
"""
import sys
from fractions import Fraction as Fr
from math import floor, ceil
import numpy as np
from scipy.optimize import minimize
import mpmath

q, L, s, K, X, N = (int(a) for a in sys.argv[1:7])
out, name = sys.argv[7], sys.argv[8]
mpmath.mp.dps = 60
PB = 40

# ---------------------------------------------------------------- 1. optimise mu (float)
w = 1.0 / q ** 2; lw = np.log(w)
a = np.arange(K + 1) * s / L


def Psi_f(u):
    u = np.asarray(u, float); o = np.zeros_like(u); nz = u != 0
    o[nz] = u[nz] ** 2 * np.log(np.abs(u[nz])) / 2 - 3 * u[nz] ** 2 / 4
    return o


def V_f(x):
    x = np.asarray(x, float)
    return x * lw - (x + 1) * np.log(x + 1) + np.where(x > 0, x * np.log(np.where(x > 0, x, 1)), 0) + 1


G = -(Psi_f(a[1:, None] - a[None, 1:]) - Psi_f(a[1:, None] - a[None, :-1]) - Psi_f(a[:-1, None] - a[None, 1:])
      + Psi_f(a[:-1, None] - a[None, :-1]))
d = s / L
vc = (V_f(a[:-1]) + 4 * V_f((a[:-1] + a[1:]) / 2) + V_f(a[1:])) / 6 * d
cons = [{'type': 'eq', 'fun': lambda r: r.sum() * d - 1}]
cons += [{'type': 'ineq', 'fun': (lambda r, i=i: r[i] - r[i + 1])} for i in range(K - 1)]
T = K * s / L
res = minimize(lambda r: -(r @ G @ r + vc @ r), np.full(K, 1 / T), jac=lambda r: -(2 * G @ r + vc),
               bounds=[(0, 2)] * K, constraints=cons, method='SLSQP', options={'maxiter': 5000, 'ftol': 1e-15})
cf = np.clip(res.x, 0, 2)

# ---------------------------------------------------------------- 2. rationalise
D16 = 2 ** 16
cs = [Fr(int(round(v * D16)), D16) for v in cf]
cs = [min(max(v, Fr(0)), Fr(2)) for v in cs]
target = Fr(L, s)
deficit = target - sum(cs)
# spread the deficit over the cells with room, in units of 2^-16
i = 0
while deficit != 0:
    step = Fr(1, D16) if deficit > 0 else -Fr(1, D16)
    if 0 <= cs[i] + step <= 2:
        cs[i] += step; deficit -= step
    i = (i + 1) % K
assert sum(cs) * s == L and all(0 <= v <= 2 for v in cs)

# ---------------------------------------------------------------- 3. exact replica of the Lean interval code
LOG2_LO = Fr(878668439483319573618263538048, 2 ** 100)
LOG2_HI = Fr(878668439483319573618263538049, 2 ** 100)
TOP = None


def iv(lo, hi): return (Fr(lo), Fr(hi))
def ofRat(x): return (x, x)
def add(I, J): return TOP if I is TOP or J is TOP else (I[0] + J[0], I[1] + J[1])
def neg(I): return TOP if I is TOP else (-I[1], -I[0])
def sub(I, J): return add(I, neg(J))


def smul(qq, I):
    if I is TOP: return TOP
    return (qq * I[0], qq * I[1]) if qq >= 0 else (qq * I[1], qq * I[0])


def lser(x, n):
    acc = Fr(0)
    for i in range(n):
        acc = acc + x ** (i + 1) / (i + 1)
    return acc


def logOneSub(x, n):
    if abs(x) < 1:
        S = lser(x, n); t = abs(x) ** (n + 1) / (1 - abs(x))
        return (-S - t, -S + t)
    return TOP


def nat_log2(m):  # Nat.log2
    return m.bit_length() - 1 if m > 0 else 0


def kOf(x):
    k0 = nat_log2(abs(x.numerator)) - nat_log2(x.denominator)
    r = x / Fr(2) ** k0
    if Fr(4, 3) < r: return k0 + 1
    if r < Fr(2, 3): return k0 - 1
    return k0


def logPt(n, x):
    if x > 0:
        k = kOf(x)
        return add(smul(Fr(k), (LOG2_LO, LOG2_HI)), logOneSub(1 - x / Fr(2) ** k, n))
    return TOP


NMAX = 2 * L * (X + 1) + 4
tab = []
for n in range(1, NMAX + 1):
    v = mpmath.log(n) * 2 ** PB
    t = int(mpmath.floor(v - mpmath.mpf('0.5')))
    enc = logPt(30, Fr(n))
    assert enc[0] >= Fr(t, 2 ** PB) and enc[1] <= Fr(t + 2, 2 ** PB), n
    tab.append(t)


def tabIV(n):
    assert 0 < n <= len(tab), ("table too small", n)
    if n == 0 or n - 1 >= len(tab): return TOP
    t = tab[n - 1]
    return (Fr(t, 2 ** PB), Fr(t + 2, 2 ** PB))


def logQ(num, den): return sub(tabIV(abs(num)), tabIV(den))


def psiQ(num, den):
    if num == 0: return ofRat(Fr(0))
    u = Fr(num, den)
    return sub(smul(u, logQ(num, den)), ofRat(u))


def PsiQ(num, den):
    if num == 0: return ofRat(Fr(0))
    u = Fr(num, den)
    return sub(smul(u ** 2 / 2, logQ(num, den)), ofRat(3 * u ** 2 / 4))


def tanPt(u0):
    if u0 == 0: return 2
    if u0 + 1 == 0: return -2
    return 2 * u0 + 1


def termIV(k, D, al):
    u0 = k - al
    if (D >= 0 and u0 >= 0) or (D <= 0 and u0 + 1 <= 0):
        return smul(D, psiQ(u0, L)), smul(D, psiQ(u0 + 1, L))
    pn = tanPt(u0)
    P = psiQ(pn, 2 * L); lg = logQ(pn, 2 * L)
    return (smul(D, add(P, smul(Fr(2 * u0 - pn, 2 * L), lg))),
            smul(D, add(P, smul(Fr(2 * (u0 + 1) - pn, 2 * L), lg))))


def cfun(j): return cs[j] if j < K else Fr(0)


def Dfun(j):
    if j <= K: return 2 * (cfun(j) - (Fr(0) if j == 0 else cfun(j - 1)))
    if j == K + 1: return Fr(1)
    return Fr(-1)


def afun(j):
    if j <= K: return j * s
    if j == K + 1: return 0
    return -L


nT = K + 3
LW = smul(Fr(-2), tabIV(q))


def sums(k):
    S0 = smul(Fr(k, L), LW); S1 = smul(Fr(k + 1, L), LW)
    for j in range(nT):
        t0, t1 = termIV(k, Dfun(j), afun(j))
        S0 = add(t0, S0); S1 = add(t1, S1)
    return S0, S1


SCALE = 10 ** 12
Sks = []
for k in range(X * L):
    S0, S1 = sums(k)
    assert S0 is not TOP and S1 is not TOP
    m = max(S0[1], S1[1])
    Sks.append(Fr(ceil(m * SCALE), SCALE))


def GQ(dd):
    return sub(add(PsiQ((dd + 1) * s, L), PsiQ((dd - 1) * s, L)), smul(Fr(2), PsiQ(dd * s, L)))


Gd = {dd: GQ(dd) for dd in range(-K, K + 1)}
E = ofRat(Fr(0))
for j in range(K):
    for jp in range(K):
        E = add(smul(cs[j] * cs[jp], Gd[j - jp]), E)
Elo = Fr(floor(E[0] * SCALE), SCALE)

# ---------------------------------------------------------------- 4. lambda and Phi
srt = sorted(Sks, reverse=True)


def Phi(lam): return -Elo + lam + Fr(2, L) * sum(max(v - lam, Fr(0)) for v in Sks)


best = min(srt, key=Phi)
lam = Fr(int(floor(best * 10 ** 9)), 10 ** 9)
PhiV = Phi(lam)
# tail checks (replica)
t1 = add(LW, ofRat(Fr(1, X)))
t2 = add(tabIV(X), smul(Fr(X), LW))
assert t1[1] < 0, "tail1"
assert t2[1] < lam, "tail2"
print(f"q={q} L={L} s={s} K={K} X={X} N={N}: -E_lo={float(-Elo):.9f} lam={float(lam):.9f} "
      f"2int={float(Fr(2, L) * sum(max(v - lam, 0) for v in Sks)):.9f} PHI={float(PhiV):.9f}  tab={len(tab)}")


def ql(x):  # Lean rational literal
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


with open(out, 'w', encoding='utf-8', newline=chr(10)) as f:
    f.write(f"/-\n# Certificate data for q = {q} (generated by `scripts/gen_cert.py {' '.join(sys.argv[1:7])}`)\n\n"
            f"Untrusted data: every number is re-checked by the kernel in `Cert/{name}.lean`.\n"
            f"Φ = {float(PhiV):.10f} (exact value `{name}.data.PhiQ`).\n-/\n")
    f.write("import Chi2Irrational.Cert.Instance\n\nnamespace Chi2Irr.Cert." + name + "\n\n")
    f.write("/-- The log table: entry `i` encloses `log (i+1)` in `[t, t+2]·2^{-40}`. -/\n")
    f.write("def tab : List ℤ := [" + ", ".join(str(t) for t in tab) + "]\n\n")
    f.write("/-- Heights of the step density (multiples of `2^{-16}`). -/\n")
    f.write("def cs : List ℚ := [" + ", ".join(ql(v) for v in cs) + "]\n\n")
    f.write("/-- Cell bounds `S_k` (upper endpoints, rounded up to `10^{-12}`). -/\n")
    f.write("def Sks : List ℚ := [" + ", ".join(ql(v) for v in Sks) + "]\n\n")
    f.write(f"/-- The certificate. -/\ndef data : CData where\n  q := {q}\n  L := {L}\n  s := {s}\n  K := {K}\n"
            f"  X := {X}\n  N := {N}\n  tab := tab\n  cs := cs\n  lam := {ql(lam)}\n  Sks := Sks\n  Elo := {ql(Elo)}\n\n")
    f.write(f"end Chi2Irr.Cert.{name}\n")
print("PhiQ exact =", PhiV)
