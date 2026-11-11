"""Check the Lean definition `QZ.DeltaZ (q/2) h` (QZ/Machine.lean) against the pilot's machine (pilot_chi2_2q/q4_twoadic.py).

Lean replica: muMono via the `powSum` recurrence of Machine.lean, `SpartZ`, `AfunZ`, `BfunZ` on monomials u^{i+j};
Delta = det(A + X B). Pilot: anchored-basis entries GA, GB (unitriangular change of basis, so the determinants agree).
Exact arithmetic (python-flint). Usage: python defs_check.py
"""
import sys, os
PILOT = r"C:\Users\Shawn Krisman\math\handoff\log2log3\pilot_chi2_2q"
sys.path.insert(0, PILOT); sys.path.insert(0, os.path.dirname(PILOT))
cwd = os.getcwd(); os.chdir(os.path.dirname(PILOT))
from q4_twoadic import entries
os.chdir(cwd)
from flint import fmpq, fmpq_poly, fmpq_mat
from math import comb

def powSum(w, N):
    s = [w / (1 - w)]
    for n in range(N):
        acc = fmpq(0)
        for j in range(n + 1):
            acc += comb(n + 1, j) * (-1) ** (n - j) * s[j]
        s.append(acc / (1 - w))
    return s

def lean_delta(zeta, h):
    w = 1 / (zeta * zeta)
    ps = powSum(w, 3 * h + 2)
    muMono = lambda d: 0 if d == 0 else d * ps[d - 1]
    pole = [-(fmpq(k) + fmpq(1, 2)) for k in range(h)]
    D = fmpq_poly([1])
    for x in pole: D *= fmpq_poly([-x, 1])
    def dPrime(k):
        p = fmpq(1)
        for m in range(h):
            if m != k: p *= pole[k] - pole[m]
        return p
    omega = [pole[k] / dPrime(k) for k in range(h)]
    Sp = [sum((zeta ** (2 * (k - j)) / fmpq((2 * j + 1) ** 2) for j in range(k + 1)), fmpq(0)) for k in range(h)]
    X = fmpq_poly([0, 1])
    def A(n):
        g = X ** n
        Q = (g * X) // D   # divByMonic
        mu = sum((Q[d] * muMono(d) for d in range(Q.degree() + 1)), fmpq(0))
        return mu + 4 * sum((g(pole[k]) * omega[k] * Sp[k] for k in range(h)), fmpq(0))
    def B(n):
        g = X ** n
        return -4 * sum((g(pole[k]) * omega[k] * zeta ** (2 * k + 1) for k in range(h)), fmpq(0))
    Am = [[A(i + j) for j in range(h)] for i in range(h)]
    Bm = [[B(i + j) for j in range(h)] for i in range(h)]
    return Am, Bm

def det_poly(Am, Bm, h):
    # det(A + X B) by interpolation at h+1 points
    pts = list(range(h + 1)); vals = []
    for t in pts:
        M = fmpq_mat(h, h, [Am[i][j] + t * Bm[i][j] for i in range(h) for j in range(h)])
        vals.append(M.det())
    # Lagrange
    P = fmpq_poly([0])
    for i, t in enumerate(pts):
        L = fmpq_poly([1])
        for j, s in enumerate(pts):
            if j != i: L *= fmpq_poly([-s, 1]) / (t - s)
        P += vals[i] * L
    return P

ok = True
for q in (5, 7, 9, 41):
    for h in (3, 5, 8):
        zeta = fmpq(q, 2)
        Am, Bm = lean_delta(zeta, h)
        PL = det_poly(Am, Bm, h)
        GA, GB = entries(fmpq(2, q), h)
        PP = det_poly(GA, GB, h)
        same = (PL == PP)
        ok &= same
        print(f"q={q} h={h}: Lean replica == pilot: {same}; deg {PL.degree()}, lead v2 = "
              f"{fmpq(PL[h]).p}/{fmpq(PL[h]).q}"[:120])
print("ALL OK" if ok else "MISMATCH")
