"""Fidelity referee (Theorem Q4): independent interval recomputation of the four new Lean margins.

Shares no code with scripts/q/margin_newQ_check.py. Transcribes the Lean definitions literally:
  alphaCore q   = 133/60 + log(oddPart(q^2-1))/4 - log(oddPart q)/3          (Q/Defs.lean l. 34-35)
  cE e          = (6 - 4e) / (3(3e + 8))                                     (Q/Even/Defs.lean l. 25)
  c2EvenSharp q = (cE(v2 q) - v2(q)/3) * log 2                               (Q/Even/Defs.lean l. 28-29)
  PhiT          = 6 -> -256/100, 8 -> -272/100, 10 -> -285/100, 12 -> -295/100 (Q/Even/Defs.lean l. 32-37)
Also: the paper's alpha_e(q) = 133/60 + log(q^2-1)/4 - log(q)/3 + c(e) log 2 (RESULT §0 l. 25) for comparison,
the paper margins with RESULT's pilot Phi, and PhiQ = -Elo + lam + (2/L) sum max(S_k - lam, 0) recomputed exactly
(Fractions) from Cert/DataQ{6,8,10,12}.lean (Cert/Instance.lean l. 78-81).
Run from lean_chi2/: python scripts/q/referee_q4/margin_q4_referee.py
"""
import re
from fractions import Fraction as F
from mpmath import iv, mpf
iv.prec = 256

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k
def oddpart(n): return n >> v2(n)
L2 = iv.log(2)
def lg(x): return iv.log(iv.mpf(x))
def cE(e): return F(6 - 4 * e, 3 * (3 * e + 8))
def fr(x): return iv.mpf(x.numerator) / x.denominator

def alphaCore(q): return iv.mpf(133) / 60 + lg(oddpart(q * q - 1)) / 4 - lg(oddpart(q)) / 3
def c2EvenSharp(q): return (fr(cE(v2(q))) - iv.mpf(v2(q)) / 3) * L2
PhiT = {6: F(-256, 100), 8: F(-272, 100), 10: F(-285, 100), 12: F(-295, 100)}
def paper_alpha_e(q): return iv.mpf(133) / 60 + lg(q * q - 1) / 4 - lg(q) / 3 + fr(cE(v2(q))) * L2
pilotPhi = {4: '-2.3088114', 6: '-2.5704376', 8: '-2.7418293', 10: '-2.8694177', 12: '-2.9710242'}

print("c(e) e=1..3:", cE(1), cE(2), cE(3))
for q in (6, 8, 10, 12):
    m = alphaCore(q) + c2EvenSharp(q) + fr(PhiT[q])
    d = alphaCore(q) + c2EvenSharp(q) - paper_alpha_e(q)
    print("q=%2d e=%d oddPart(q^2-1)=%d oddPart(q)=%d cE=%s | Lean margin in [%s, %s]  (neg: %s) | "
          "|Lean alpha - paper alpha_e| <= %.1e | paper margin (pilot Phi) <= %s" % (
              q, v2(q), oddpart(q * q - 1), oddpart(q), cE(v2(q)), mpf(m.a), mpf(m.b), m.b < 0,
              max(abs(float(d.a)), abs(float(d.b))), mpf((paper_alpha_e(q) + iv.mpf(pilotPhi[q])).b)))
    # room: largest Phi target that would still give a negative margin
    print("       PhiT must be < %s for a negative margin" % mpf((-(alphaCore(q) + c2EvenSharp(q))).a))
q = 4
print("q= 4 (excluded): paper margin with pilot Phi <= %s" % mpf((paper_alpha_e(4) + iv.mpf(pilotPhi[4])).b))

def phiQ(path):
    s = open(path, encoding='utf8').read()
    def rat(t): return F(t.replace(' ', '').replace(':ℚ', ''))
    Sks = [rat(x) for x in re.findall(r'\(([-0-9 /]+) : ℚ\)',
                                      re.search(r'def Sks : List ℚ := \[(.*?)\]', s, re.S).group(1))]
    lam = rat(re.search(r'lam := \(([-0-9 /]+) : ℚ\)', s).group(1))
    Elo = rat(re.search(r'Elo := \(([-0-9 /]+) : ℚ\)', s).group(1))
    L = int(re.search(r'\n  L := (\d+)', s).group(1))
    qq = int(re.search(r'\n  q := (\d+)', s).group(1))
    sig = sum((max(v - lam, F(0)) for v in Sks), F(0))
    return qq, L, len(Sks), -Elo + lam + F(2, L) * sig
for q in (6, 8, 10, 12):
    qq, L, n, P = phiQ('Chi2Irrational/Cert/DataQ%d.lean' % q)
    print("DataQ%d: q=%d L=%d #Sks=%d PhiQ=%.10f  PhiQ <= PhiT: %s  slack %.6f" % (
        q, qq, L, n, float(P), P <= PhiT[q], float(PhiT[q] - P)))
