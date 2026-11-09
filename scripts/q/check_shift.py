"""Exact check of the discretised shift lemma (Q/Shift.lean) on the q = 14 certificate data.

Reads Sks, lam, L, X from Chi2Irrational/Cert/DataQ14.lean; with ell a rational stand-in for 2 log(q/q0) and
refinement r, builds S'_{k'} = S_{k' // 2r} - ell k'/L', lam' = lam - ell/2, L' = 2rL, and checks
  (2/L') sum (S'_k' - lam')_+  - ell/2  <=  (2/L) sum (S_k - lam)_+  - ell/4 + ell/(4 r L)   (exact Fractions).
"""
import re
from fractions import Fraction as Fr

src = open("Chi2Irrational/Cert/DataQ14.lean", encoding="utf-8").read()
def rat(t):
    t = t.strip().strip("()").replace(": ℚ", "").strip()
    if "/" in t:
        a, b = t.split("/"); return Fr(int(a), int(b))
    return Fr(int(t))
Sks = [rat(t) for t in re.findall(r"\((-?\d+(?: / \d+)? : ℚ)\)", src.split("def Sks")[1].split("]")[0])]
lam = rat(re.search(r"lam := (\(.*?\))", src).group(1))
L, X = 200, 2
assert len(Sks) == X * L
pos = lambda v: max(v, Fr(0))
base = Fr(2, L) * sum(pos(s - lam) for s in Sks)
for ell in [Fr(0), Fr(267, 1000), Fr(1), Fr(5)]:      # 2 log(16/14) ~ 0.267
    for r in [1, 2, 5]:
        Lp = 2 * r * L
        new = Fr(2, Lp) * sum(pos(Sks[k // (2 * r)] - ell * k / Lp - (lam - ell / 2)) for k in range(X * Lp)) - ell / 2
        bound = base - ell / 4 + ell / (4 * r * L)
        print(f"ell={float(ell):.3f} r={r}: Phi'-Phi = {float(new - base):+.6f}  bound {float(bound - base):+.6f}  ok={new <= bound}")
        assert new <= bound
