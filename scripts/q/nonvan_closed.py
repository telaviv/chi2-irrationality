# Closed forms of det MS, ML, MD (Lean definitions in NonVan/BlockMat.lean) as rational functions of q.
import sympy as sp
from fractions import Fraction as F
q=sp.symbols('q')
def crr(r): return sp.Integer(-1) if r==1 else sp.Rational(1,2)
def wt(): return 1/q**2
def Tq(n): return sum((1/q)**(2*u+1)/sp.Integer(2*u+1)**2 for u in range(n))
def eD(r,s): return sp.Rational(11,2)-2*r if r==s else sp.Integer(max(3-r-s,0))+sp.Rational(5,2)
def MS(): return sp.Matrix(3,3,lambda r,s: crr(r)/(1-wt()) + (4*q**(2*r+1)*Tq(r) if r==s else 0))
def ML(): return sp.Matrix(3,3,lambda r,s: wt()*crr(r)/(1-wt()) + (4*q**(2*r+1)*Tq(r+1) if r==s else 0))
def MD(): return sp.Matrix(3,3,lambda r,s: wt()*(crr(r)*eD(r,s)/(1-wt())+crr(r)*2*wt()/(1-wt())**2) + (-4*(r+sp.Rational(1,2))*q**(2*r+1)*Tq(r+1) if r==s else 0))
for name,M in [('S',MS()),('L',ML()),('D',MD())]:
    d=sp.factor(sp.cancel(M.det()))
    n,den=sp.fraction(sp.cancel(M.det()))
    print(name, d)
    print('  num', sp.expand(n)); print('  den', sp.factor(den))
    for qq in range(3,16): print('   q=%d'%qq, d.subs(q,qq))
    P=sp.Poly(n,q); print('  real roots', [sp.N(r,6) for r in sp.real_roots(P)])

# Independent check: exact Fraction evaluation of the Lean entries at q = 3..15 vs the closed forms used in Q/NonVan.lean.
def det3(M):
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
def ent(qq):
    c=lambda r: F(-1) if r==1 else F(1,2)
    w=F(1,qq*qq)
    T=lambda n: sum(F(1,qq)**(2*u+1)/(2*u+1)**2 for u in range(n))
    e=lambda r,s: F(11,2)-2*r if r==s else F(max(3-r-s,0))+F(5,2)
    S=[[c(r)/(1-w)+(4*F(qq)**(2*r+1)*T(r) if r==s else 0) for s in range(3)] for r in range(3)]
    L=[[w*c(r)/(1-w)+(4*F(qq)**(2*r+1)*T(r+1) if r==s else 0) for s in range(3)] for r in range(3)]
    D=[[w*(c(r)*e(r,s)/(1-w)+c(r)*2*w/(1-w)**2)+(-4*(r+F(1,2))*F(qq)**(2*r+1)*T(r+1) if r==s else 0) for s in range(3)] for r in range(3)]
    return det3(S),det3(L),det3(D)
ok=True
for qq in range(3,16):
    S,L,D=ent(qq)
    cS=F(72*qq**8+8*qq**6, 9*(qq*qq-1))
    cL=F(129600*qq**8-84600*qq**6-50816*qq**4+7240*qq**2, 2025*(qq*qq-1))
    cD=F(-16200*qq**10+51075*qq**8-28523*qq**6-420*qq**4, 135*(qq*qq-1)**2)
    ok &= (S,L,D)==(cS,cL,cD)
print('Fraction check q=3..15:', ok, '; q=3:', ent(3), '; q=5:', ent(5))
