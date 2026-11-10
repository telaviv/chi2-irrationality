"""Exact checks of every inequality used in the Lean proof of Lemma 10_e (scripts/q/l10e_plan.md).

Run:  python l10e_check.py > l10e_check.txt
Exact arithmetic throughout (fractions / python-flint fmpq).  Nothing here feeds Lean; it only tests the
statement chain before formalisation.
"""
import random, itertools, json, math
from fractions import Fraction as Fr
import flint

random.seed(20261109)

def v2(x):
    x = Fr(x)
    if x == 0: return 10**9
    n, d = x.numerator, x.denominator
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v

def nlog2(n):  # Nat.log 2 n (0 for n = 0)
    return n.bit_length() - 1 if n >= 1 else 0

def pole(k): return -(Fr(k) + Fr(1, 2))
def D(h, t):
    r = Fr(1)
    for k in range(h): r *= (t - pole(k))
    return r
def Dd(h, t):
    s = Fr(0)
    for k in range(h):
        r = Fr(1)
        for j in range(h):
            if j != k: r *= (t - pole(j))
        s += r
    return s
def phd(h, m):
    t = Fr(-m); return (D(h, t) - t * Dd(h, t)) / D(h, t) ** 2
def phv(h, m):
    t = Fr(-m); return t / D(h, t)
def omega(h, k):
    dp = Fr(1)
    for m in range(h):
        if m != k: dp *= (pole(k) - pole(m))
    return pole(k) / dp

out = {}

# ---- 1. factor bounds: v2(phd) >= h, v2(phv) >= h, v2(4 omega) >= -(h-2) >= -h ----
bad = 0
for h in range(1, 31):
    for m in range(0, 120):
        if v2(phd(h, m)) < h: bad += 1
        if v2(phv(h, m)) < h: bad += 1
    for k in range(h):
        if v2(4 * omega(h, k)) < -(h - 2): bad += 1
print("1. factor bounds (h<=30, m<120): violations =", bad)
out["factor_violations"] = bad

# ---- 2. CoreDet: |det R| <= prod_{i<j, z_i != z_j} |z_j - z_i| * 2^{Lam * #U} ----
def det_exact(rows):
    n = len(rows)
    if n == 0: return Fr(1)
    M = flint.fmpq_mat(n, n, [flint.fmpq(x.numerator, x.denominator) for r in rows for x in r])
    d = M.det()
    return Fr(int(d.p), int(d.q))

def rowvec(z, der, h):
    if der: return [Fr(j) * z ** (j - 1) if j >= 1 else Fr(0) for j in range(h)]
    return [z ** j for j in range(h)]

def coredet_check(z, U):
    h = len(z)
    d = det_exact([rowvec(z[i], i in U, h) for i in range(h)])
    rhs = 0  # valuation of the bound
    for i in range(h):
        for j in range(i + 1, h):
            if z[i] != z[j]: rhs += v2(z[j] - z[i])
    # Lam: max(0, max_{i in U, z_j != z_i} v2(z_i - z_j))
    lam = 0
    for i in U:
        for j in range(h):
            if z[j] != z[i]: lam = max(lam, v2(z[i] - z[j]))
    return v2(d) >= rhs - lam * len(U), (v2(d), rhs, lam, len(U))

bad = 0; ntest = 0; minslack = 10**9
for trial in range(3000):
    h = random.randint(1, 9)
    pts = []
    for i in range(h):
        if random.random() < 0.5: pts.append(Fr(-random.randint(0, 12)))
        else: pts.append(pole(random.randint(0, 12)))
    U = set(i for i in range(h) if random.random() < 0.4)
    ok, data = coredet_check(pts, U)
    ntest += 1
    if not ok: bad += 1
    elif data[0] < 10**8: minslack = min(minslack, data[0] - (data[1] - data[2] * data[3]))
print("2. CoreDet random tests:", ntest, "violations =", bad, " min slack (nonzero dets) =", minslack)
out["coredet_violations"] = bad

# ---- 3. term level: exact weighted valuation of each Andreief term vs nu(f) vs R(h) ----
def Rh(h, e):
    t = nlog2(h)
    me = Fr(e) - Fr(2 * (e + 1) ** 2, 3 * e + 8)
    return me * h * h - h * (Fr(3 * e, 2) + 4 * t + 4)

def cnt(n, L):
    return sum(1 for l in range(L) if n % (2 ** (l + 1)) == 0)

def term_data(f, h, e):
    """f: list of slots ('n', m, tau) or ('p', k). Returns (exact valuation or None if zero, nu)."""
    # x-key / y-key injectivity
    xk = [(s[1], s[2] == 1) if s[0] == 'n' else ('p', s[1]) for s in f]
    yk = [(s[1], s[2] == 2) if s[0] == 'n' else ('p', s[1]) for s in f]
    valid = len(set(xk)) == h and len(set(yk)) == h
    z = [Fr(-s[1]) if s[0] == 'n' else pole(s[1]) for s in f]
    dx = [s[0] == 'n' and s[2] == 1 for s in f]
    dy = [s[0] == 'n' and s[2] == 2 for s in f]
    w = Fr(1); price = 0
    for s in f:
        if s[0] == 'n':
            w *= -(phd(h, s[1]) if s[2] == 0 else phv(h, s[1])); price += 2 * s[1]
        else:
            w *= -4 * omega(h, s[1]); price += 2 * s[1] + 1
    dX = det_exact([rowvec(z[i], dx[i], h) for i in range(h)])
    dY = det_exact([rowvec(z[i], dy[i], h) for i in range(h)])
    val = None if (w * dX * dY == 0) else v2(w * dX * dY) + e * price
    if not valid:
        return val, None, valid
    t = nlog2(h); L = t + 1
    nodes = [s[1] for s in f if s[0] == 'n']; I = len(nodes); P = h - I
    Mx = max(nodes) if nodes else 0; Lam = nlog2(Mx); nder = sum(dx) + sum(dy)
    om = sum(h if s[0] == 'n' else -h for s in f)
    csum = 0
    for i in range(h):
        for j in range(h):
            a, b = f[i], f[j]
            if a[0] == 'n' and b[0] == 'n':
                if a[1] != b[1]: csum += cnt(abs(a[1] - b[1]), L)
            elif a[0] == 'p' and b[0] == 'p':
                if a[1] != b[1]: csum += cnt(abs(a[1] - b[1]), L)
            else:
                csum -= 1
    nu = om + e * price + csum - Lam * nder
    # the intermediate inequalities (I2)-(I5)
    nodeprice = sum(2 * m for m in nodes); poleprice = sum(2 * s[1] + 1 for s in f if s[0] == 'p')
    assert 2 * nodeprice >= I * (I - 1) - 2 * I + 2 * max(0, 2 * Mx - h), ("I2n", f)
    assert poleprice >= P * P, ("I2p", f)
    assert csum >= I * I * (1 - Fr(1, 2 ** L)) - 2 * L * I + P * P * (1 - Fr(1, 2 ** L)) - L * P - 2 * I * P, ("I3", f)
    assert e * max(0, 2 * Mx - h) - Lam * nder >= -h * (2 * t + 1), ("I4", f)
    me = Fr(e) - Fr(2 * (e + 1) ** 2, 3 * e + 8)
    assert e * (Fr(I * I, 2) + P * P) + h * (I - P) + (I - P) ** 2 >= me * h * h, ("I5", f)
    return val, nu, valid

def all_slots(M, h):
    return [('n', m, tau) for m in range(M) for tau in range(3)] + [('p', k) for k in range(h)]

stats = {}
for (h, M) in [(1, 6), (2, 6), (3, 5), (4, 3)]:
    S = all_slots(M, h)
    for e in (1, 2, 3):
        R = Rh(h, e); nviol = 0; nzero_invalid = 0; nterms = 0; minslack_val = 10**9; minslack_R = 10**9
        for f in itertools.product(S, repeat=h):
            val, nu, valid = term_data(list(f), h, e)
            nterms += 1
            if not valid:
                if val is not None: nviol += 1  # invalid terms must vanish
                continue
            if val is not None:
                if val < nu: nviol += 1
                minslack_val = min(minslack_val, val - nu)
            if nu < R: nviol += 1
            minslack_R = min(minslack_R, nu - R)
        stats[f"h={h},M={M},e={e}"] = dict(terms=nterms, violations=nviol, min_val_minus_nu=minslack_val,
                                           min_nu_minus_R=float(minslack_R))
        print(f"3. h={h} M={M} e={e}: terms={nterms} violations={nviol} min(val-nu)={minslack_val} "
              f"min(nu-R)={float(minslack_R):.2f}")

# random valid configurations at larger h, including large nodes
bad = 0; ntest = 0
for trial in range(400):
    h = random.randint(5, 14); e = random.randint(1, 4)
    I = random.randint(0, h); P = h - I
    poles = random.sample(range(h), P)
    # nodes: choose distinct x-keys/y-keys: each node either single (tau random) or doubled (tau 1,2)
    f = []; used = set()
    big = random.random() < 0.3
    while len(f) < I:
        m = random.randint(0, (h * h * 4) if big else 3 * h)
        if m in used: continue
        used.add(m)
        if len(f) + 2 <= I and random.random() < 0.4: f += [('n', m, 1), ('n', m, 2)]
        else: f.append(('n', m, random.randint(0, 2)))
    f += [('p', k) for k in poles]
    random.shuffle(f)
    val, nu, valid = term_data(f, h, e)
    ntest += 1
    assert valid
    if (val is not None and val < nu) or nu < Rh(h, e): bad += 1
print("3b. random valid terms (h 5..14, big nodes):", ntest, "violations =", bad)
out["term_stats"] = stats; out["random_term_violations"] = bad

# ---- 4. the final bound vs the exact n2 (pilot / referee data) ----
def n2bound(h, e):
    return h - math.ceil(Rh(h, e))
exact = {}
for line in open(r"C:\Users\Shawn Krisman\math\handoff\log2log3\pilot_qeven\runs_n2.txt"):
    p = line.split()
    if not p or not p[0].startswith("q="): continue
    try:
        e = int(p[2].split("=")[1]); h = int(p[4]); n2 = int(p[5].split("=")[1]) if "=" in p[5] and p[5] != "n2=" else int(p[6])
    except Exception:
        continue
    exact[(e, h)] = n2
bad = 0
for (e, h), n2 in sorted(exact.items()):
    b = n2bound(h, e)
    if n2 > b: bad += 1
    if h in (48, 96, 160):
        print(f"4. e={e} h={h}: exact n2={n2}  Lean bound n2(h)={b}  (n2bound/h^2={b/h/h:+.4f}, "
              f"limit {-(e - 2*(e+1)**2/(3*e+8)):+.4f})")
print("4. exact n2 <= Lean bound: violations =", bad, "of", len(exact))
out["final_violations"] = bad
# asymptotics of the Lean bound
for e in (1, 2, 3):
    print(f"   e={e}: n2bound(h)/h^2 at h=10^3,10^5,10^7:",
          [round(n2bound(h, e) / h / h, 4) for h in (10**3, 10**5, 10**7)],
          " limit -m_e =", round(-(e - 2 * (e + 1) ** 2 / (3 * e + 8)), 4),
          " = c(e) - e/3 =", round((6 - 4 * e) / (3 * (3 * e + 8)) - e / 3, 4))

json.dump(out, open("l10e_check.json", "w"), indent=1, default=str)
