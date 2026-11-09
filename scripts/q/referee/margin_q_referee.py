"""Fidelity referee (Theorem Q): independent interval recomputation of the Lean margins.

Shares no code with scripts/q/margin_check.py. Transcribes Chi2Irrational/Q/Defs.lean literally:
  alphaCore q = 133/60 + log(oddPart(q^2-1))/4 - log(oddPart q)/3
  c2Odd q     = (v2(q^2-1) - 2)/4 * log 2
  c2Even q    = (1/2 - v2(q)/3) * log 2
  betaOdd q   = -2078/1000 - log(q/3)/2
  betaEven q  = -303/100  - log(q/14)/2
and the paper's formulas (RESULT §2, §4.2): alpha(q) = 133/60 - log2/2 + log(q^2-1)/4 - log(q)/3 (odd),
alpha_even(q) = 133/60 + log2/2 + log(q^2-1)/4 - log(q)/3, Phi_3 = -2.0987404387, Phi_14 = -3.0444073501.
Also recomputes PhiQ = -Elo + lam + (2/L) sum max(S_k - lam, 0) exactly from Cert/DataQ{3,14}.lean.
Run from lean_chi2/: python scripts/q/referee/margin_q_referee.py
"""
import re
from fractions import Fraction as F
from mpmath import iv, mpf
iv.prec = 200

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k
def oddpart(n): return n >> v2(n)
L2 = iv.log(2)
def lg(x): return iv.log(iv.mpf(x))

def alphaCore(q): return iv.mpf(133)/60 + lg(oddpart(q*q-1))/4 - lg(oddpart(q))/3
def c2Odd(q): return (iv.mpf(v2(q*q-1)) - 2)/4 * L2
def c2Even(q): return (iv.mpf(1)/2 - iv.mpf(v2(q))/3) * L2
def betaOdd(q): return iv.mpf(-2078)/1000 - iv.log(iv.mpf(q)/3)/2
def betaEven(q): return iv.mpf(-303)/100 - iv.log(iv.mpf(q)/14)/2

def paper_alpha_odd(q): return iv.mpf(133)/60 - L2/2 + lg(q*q-1)/4 - lg(q)/3
def paper_alpha_even(q): return iv.mpf(133)/60 + L2/2 + lg(q*q-1)/4 - lg(q)/3

worst_odd = None; bad = []; maxdiff = 0
for q in range(3, 5002, 2):
    m = alphaCore(q) + c2Odd(q) + betaOdd(q)
    if not (m.b < 0): bad.append(('odd', q, m))
    if worst_odd is None or m.b > worst_odd[1].b: worst_odd = (q, m)
    d = (alphaCore(q) + c2Odd(q)) - paper_alpha_odd(q)
    maxdiff = max(maxdiff, float(abs(d.a)), float(abs(d.b)))
worst_even = None
for q in range(14, 5001, 2):
    m = alphaCore(q) + c2Even(q) + betaEven(q)
    if not (m.b < 0): bad.append(('even', q, m))
    if worst_even is None or m.b > worst_even[1].b: worst_even = (q, m)
    d = (alphaCore(q) + c2Even(q)) - paper_alpha_even(q)
    maxdiff = max(maxdiff, float(abs(d.a)), float(abs(d.b)))
print("odd q in [3,5001]: count", len(range(3,5002,2)), "worst q =", worst_odd[0], "margin upper =", mpf(worst_odd[1].b))
print("even q in [14,5000]: count", len(range(14,5001,2)), "worst q =", worst_even[0], "margin upper =", mpf(worst_even[1].b))
print("non-negative margins:", bad)
print("max |Lean alpha+c2 - paper alpha| over both ranges:", maxdiff)
for q in (3, 5, 7, 9, 11, 15, 21, 51, 101, 199):
    print(" odd q=%d  Lean margin <= %s   paper alpha=%s  paper margin(Phi3 shift)=%s" % (q,
          mpf((alphaCore(q)+c2Odd(q)+betaOdd(q)).b), mpf(paper_alpha_odd(q).b),
          mpf((paper_alpha_odd(q) - iv.mpf('2.0987404387') - iv.log(iv.mpf(q)/3)/2).b)))
for q in (12, 14, 16, 20, 100):
    print(" even q=%d Lean margin(betaEven) <= %s   paper alpha_even=%s" % (q,
          mpf((alphaCore(q)+c2Even(q)+betaEven(q)).b), mpf(paper_alpha_even(q).b)))
# What the even formula would give at excluded q (sanity: q=12 must fail with Phi_14 shift reversed -> not applicable)
# closed forms of Margin.lean
print("odd closed-form constant 133/60-2.078-log2/2+log3/6 =", mpf((iv.mpf(133)/60-iv.mpf(2078)/1000-L2/2+lg(3)/6).b))
print("even closed-form constant 133/60-3.03+7/6 log2 =", mpf((iv.mpf(133)/60-iv.mpf(303)/100+7*L2/6).b))
print("paper closed-form 133/60-log2/2+log3/2-2.0987404387 =", mpf((iv.mpf(133)/60-L2/2+lg(3)/2-iv.mpf('2.0987404387')).b))
print("Lean closed-form 133/60-log2/2+log3/2-2.078 =", mpf((iv.mpf(133)/60-L2/2+lg(3)/2-iv.mpf('2.078')).b))

def phiQ(path):
    s = open(path, encoding='utf8').read()
    def rat(t):
        t = t.strip().strip('()').replace(': ℚ', '').strip()
        return F(t.replace(' ', ''))
    Sks = [rat(x) for x in re.findall(r'\(([-0-9 /]+) : ℚ\)', re.search(r'def Sks : List ℚ := \[(.*?)\]', s, re.S).group(1))]
    lam = rat(re.search(r'lam := \(([-0-9 /]+) : ℚ\)', s).group(1))
    Elo = rat(re.search(r'Elo := \(([-0-9 /]+) : ℚ\)', s).group(1))
    L = int(re.search(r'\n  L := (\d+)', s).group(1))
    q = int(re.search(r'\n  q := (\d+)', s).group(1))
    sig = sum(max(v - lam, F(0)) for v in Sks)
    return q, L, len(Sks), -Elo + lam + F(2, L) * sig
for p in ('Chi2Irrational/Cert/DataQ3.lean', 'Chi2Irrational/Cert/DataQ14.lean'):
    q, L, n, P = phiQ(p)
    print(p, "q =", q, "L =", L, "#Sks =", n, "PhiQ =", float(P), "PhiQ <= -2.078:", P <= F(-2078,1000), "PhiQ <= -3.03:", P <= F(-303,100))
