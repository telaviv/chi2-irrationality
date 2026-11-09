"""Exact check of the general-nu Lemma 10 bounds proved in Chi2Irrational/Q/TwoAdicEntries.lean and Q/TwoAdic.lean.

Uses the gate referee's independent machine (pilot_q/referee/rmachine.py, exact python-flint fmpq).
For odd q, nu = v2(q^2 - 1), anchored basis G_ij = A_ij + X B_ij (i, j < h = K):
  (L) pi = i+j+1-h >= 1 : v2(A) >= -(nu-1) pi - 2 - floor(log2 pi), B = 0          (Q.V2_A_L, Q.Bfun_L)
  (U) N = h-1-i-j >= 0  : v2(A), v2(B) >= N - 1 - floor(log2 N)                      (Q.V2_A_U, Q.V2_B_U)
  all                   : v2 >= eTA = h-(i+j+1) - (nu-2) pi_+ - floor(log2 h) - 6      (Q.V2_entry)
  determinant           : n2 = -min_k v2([X^k] Delta_h) <= (nu-2) betaP(h) + h (floor(log2 h) + 6)   (Q.twoAdic_Delta)
betaP is the Lean definition (Arith/PoleOrder.lean): sum_a (a+1-(h+1)//2)_+ + sum_b (b - h//2)_+.
Usage: python twoadic_odd_check.py   (writes twoadic_odd_check.txt next to this file)
"""
import os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, r"C:\Users\Shawn Krisman\math\handoff\log2log3\pilot_q\referee")
from rmachine import Machine, det_poly, vp_fmpq  # noqa: E402


def log2f(n):
    return n.bit_length() - 1 if n > 0 else 0  # Nat.log 2 (Nat.log 2 0 = 0)


def betaP(h):
    return sum(max(a + 1 - (h + 1) // 2, 0) for a in range(h)) + sum(max(b - h // 2, 0) for b in range(h))


def v2nat(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def run(q, h):
    nu = v2nat(q * q - 1)
    M = Machine(q, h)
    GA, GB = M.anchored()
    viol = []
    slack = {'L': None, 'U': None, 'eTA': None}

    def upd(k, s):
        slack[k] = s if slack[k] is None else min(slack[k], s)

    for i in range(h):
        for j in range(h):
            a, b = GA[i][j], GB[i][j]
            va = vp_fmpq(a, 2) if a != 0 else None
            vb = vp_fmpq(b, 2) if b != 0 else None
            pi = i + j + 1 - h
            eTA = h - (i + j + 1) - (nu - 2) * max(pi, 0) - log2f(h) - 6
            if pi >= 1:
                if b != 0:
                    viol.append(('B_L nonzero', i, j))
                bd = -(nu - 1) * pi - 2 - log2f(pi)
                if va is not None:
                    upd('L', va - bd)
                    if va < bd:
                        viol.append(('L', i, j, va, bd))
            else:
                N = h - 1 - i - j
                bd = N - 1 - log2f(N)
                for v in (va, vb):
                    if v is not None:
                        upd('U', v - bd)
                        if v < bd:
                            viol.append(('U', i, j, v, bd))
            for v in (va, vb):
                if v is not None:
                    upd('eTA', v - eTA)
                    if v < eTA:
                        viol.append(('eTA', i, j, v, eTA))
    A, B = M.hankel()
    cs = det_poly(A, B)
    n2 = -min(vp_fmpq(c, 2) for c in cs if c != 0)
    bd2 = (nu - 2) * betaP(h) + h * (log2f(h) + 6)
    if n2 > bd2:
        viol.append(('det', n2, bd2))
    return nu, n2, bd2, slack, viol


if __name__ == '__main__':
    out = open(os.path.join(HERE, 'twoadic_odd_check.txt'), 'w')
    total = 0
    for q in (3, 5, 7, 9, 15, 17, 31, 33, 63):
        for h in (8, 12, 16):
            t = time.time()
            nu, n2, bd2, slack, viol = run(q, h)
            total += len(viol)
            line = (f"q={q:3d} nu={nu} h={h:3d} n2={n2:5d} bound={bd2:5d} entry_minslack={slack} "
                    f"violations={len(viol)} {viol[:3]} ({time.time() - t:.1f}s)")
            print(line, flush=True)
            out.write(line + '\n')
    line = f"TOTAL violations {total}"
    print(line)
    out.write(line + '\n')
    out.close()
