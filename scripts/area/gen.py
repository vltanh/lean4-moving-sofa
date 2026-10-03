"""Generator for the numerical part of MovingSofaOptimality/Gerver/AreaBounds.lean.

Produces Lean text for
  * the coefficient structures `ga_K_*` of the antiderivatives on each phase,
  * the interval-arithmetic chains `ga_num_*` (each step checked by norm_num),
  * the enclosures of the derived quantities (c₂, d₁, d₂, the endpoints).
All intervals are computed with exact rationals and rounded outward on a decimal grid.
"""
import sympy as sp
from fractions import Fraction as Fr
import math, sys

DIG = 12  # decimal places of the grid

def rdown(x, d=DIG):
    q = Fr(10) ** d
    return Fr(math.floor(x * q)) / q

def rup(x, d=DIG):
    q = Fr(10) ** d
    return Fr(math.ceil(x * q)) / q

def dec(x):
    """Lean decimal literal of a rational with a terminating decimal expansion."""
    x = Fr(x)
    neg = x < 0
    x = abs(x)
    ip = x.numerator // x.denominator
    fp = x - ip
    digs = ''
    k = 0
    while fp != 0:
        fp *= 10
        d = fp.numerator // fp.denominator
        digs += str(d)
        fp -= d
        k += 1
        assert k < 60, x
    s = str(ip) + ('.' + digs if digs else '')
    return '(-' + s + ')' if neg else s

def lit(x):
    """Lean term for an interval endpoint (type ℝ inferred from context)."""
    d = dec(x)
    if d.startswith('(-'):
        d = d[1:-1]
    return '(' + d + ' : ℝ)'

# ---------------------------------------------------------------- expression trees

class E:
    pass

class Var(E):
    def __init__(s, name): s.name = name
    def key(s): return ('v', s.name)
class Const(E):
    def __init__(s, v): s.v = Fr(v)
    def key(s): return ('c', s.v)
class Bin(E):
    def __init__(s, op, a, b): s.op, s.a, s.b = op, a, b
    def key(s): return (s.op, s.a.key(), s.b.key())
class Neg(E):
    def __init__(s, a): s.a = a
    def key(s): return ('neg', s.a.key())
class Div(E):
    def __init__(s, a, k): s.a, s.k = a, int(k)
    def key(s): return ('div', s.a.key(), s.k)

def add(a, b): return Bin('+', a, b)
def sub(a, b): return Bin('-', a, b)
def mul(a, b): return Bin('*', a, b)

def const_text(v):
    v = Fr(v)
    if v.denominator == 1:
        return str(v.numerator) if v >= 0 else '(-' + str(-v.numerator) + ')'
    p, q = abs(v.numerator), v.denominator
    s = '(%d / %d)' % (p, q)
    return s if v > 0 else '(-' + s + ')'

def pr(e):
    if isinstance(e, Var): return e.name
    if isinstance(e, Const): return const_text(e.v)
    if isinstance(e, Bin): return '(' + pr(e.a) + ' ' + e.op + ' ' + pr(e.b) + ')'
    if isinstance(e, Neg): return '(-' + pr(e.a) + ')'
    if isinstance(e, Div): return '(' + pr(e.a) + ' / ' + str(e.k) + ')'
    raise TypeError(e)

def strip(s):
    # drop one pair of outer parentheses for readability (only if they enclose everything)
    if s.startswith('(') and s.endswith(')'):
        depth = 0
        for i, ch in enumerate(s):
            if ch == '(': depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    return s
        return s[1:-1]
    return s

def from_sympy(x):
    x = sp.sympify(x)
    if x.is_Symbol:
        return Var(str(x))
    if x.is_Rational:
        return Const(Fr(int(x.p), int(x.q)))
    if x.is_Add:
        terms = list(x.args)
        # put positive terms first
        def negc(t):
            c, _ = t.as_coeff_Mul()
            return bool(c < 0)
        terms.sort(key=lambda t: (bool(negc(t)), str(t)))
        acc = from_sympy(terms[0])
        for t in terms[1:]:
            if negc(t):
                acc = sub(acc, from_sympy(-t))
            else:
                acc = add(acc, from_sympy(t))
        return acc
    if x.is_Mul:
        c, rest = x.as_coeff_Mul()
        c = Fr(int(sp.Rational(c).p), int(sp.Rational(c).q))
        factors = sp.Mul.make_args(rest)
        tr = None
        for f in factors:
            ft = from_sympy(f)
            tr = ft if tr is None else mul(tr, ft)
        if tr is None:
            return Const(c)
        p, q = abs(c.numerator), c.denominator
        if p != 1:
            tr = mul(Const(p), tr)
        if q != 1:
            tr = Div(tr, q)
        if c < 0:
            tr = Neg(tr)
        return tr
    if x.is_Pow:
        b, n = x.args
        assert n.is_Integer and n > 0
        bt = from_sympy(b)
        tr = bt
        for _ in range(int(n) - 1):
            tr = mul(tr, bt)
        return tr
    raise TypeError(x)

# ---------------------------------------------------------------- interval chain

class Chain:
    def __init__(s, env):
        """env: name -> (lean hypothesis name, lo, hi)"""
        s.env = dict(env)
        s.lines = []
        s.memo = {}
        s.n = 0
    def fresh(s):
        s.n += 1
        return 'h%d' % s.n
    def step(s, lemma, args, L, U, cond):
        h = s.fresh()
        s.lines.append('  have %s := %s %s\n    (L := %s) (U := %s) (by norm_num)' %
                       (h, lemma, ' '.join(args), lit(L), lit(U)))
        return h
    def ev(s, e):
        """returns (term, lo, hi) where term proves `pr(e) ∈ Icc lo hi`"""
        k = e.key()
        if k in s.memo:
            return s.memo[k]
        r = s._ev(e)
        s.memo[k] = r
        return r
    def _ev(s, e):
        if isinstance(e, Var):
            h, lo, hi = s.env[e.name]
            return (h, Fr(lo), Fr(hi))
        if isinstance(e, Const):
            return ('(ga_iv_const %s)' % ('(' + strip(const_text(e.v)) + ' : ℝ)'), e.v, e.v)
        if isinstance(e, Neg):
            h, a, b = s.ev(e.a)
            L, U = rdown(-b), rup(-a)
            return (s.step('ga_iv_neg', [h], L, U, None), L, U)
        if isinstance(e, Div):
            h, a, b = s.ev(e.a)
            L, U = rdown(a / e.k), rup(b / e.k)
            hh = s.fresh()
            s.lines.append('  have %s := ga_iv_div %s (k := %d)\n    (L := %s) (U := %s) (by norm_num)' %
                           (hh, h, e.k, lit(L), lit(U)))
            return (hh, L, U)
        if isinstance(e, Bin):
            h1, a, b = s.ev(e.a)
            h2, c, d = s.ev(e.b)
            if e.op == '+':
                L, U = rdown(a + c), rup(b + d)
                return (s.step('ga_iv_add', [h1, h2], L, U, None), L, U)
            if e.op == '-':
                L, U = rdown(a - d), rup(b - c)
                return (s.step('ga_iv_sub', [h1, h2], L, U, None), L, U)
            if e.op == '*':
                if a >= 0 and c >= 0:
                    lem, lo, hi = 'ga_iv_mul_pp', a * c, b * d
                elif a >= 0 and d <= 0:
                    lem, lo, hi = 'ga_iv_mul_pn', b * c, a * d
                elif b <= 0 and c >= 0:
                    lem, lo, hi = 'ga_iv_mul_np', a * d, b * c
                elif b <= 0 and d <= 0:
                    lem, lo, hi = 'ga_iv_mul_nn', b * d, a * c
                else:
                    lem = 'ga_iv_mul'
                    ps = [a * c, a * d, b * c, b * d]
                    lo, hi = min(ps), max(ps)
                L, U = rdown(lo), rup(hi)
                return (s.step(lem, [h1, h2], L, U, None), L, U)
        raise TypeError(e)

# ---------------------------------------------------------------- the trigonometric polynomial F

def Fexpr(K, t, c, s):
    """the tree of `ga_TP.F K t c s` (K: dict field -> tree)"""
    P = mul(t, add(K['p1'], mul(t, add(K['p2'], mul(t, add(K['p3'], mul(t, add(K['p4'], mul(t, K['p5'])))))))))
    Q = add(K['q0'], mul(t, add(K['q1'], mul(t, K['q2']))))
    R = add(K['r0'], mul(t, add(K['r1'], mul(t, K['r2']))))
    return add(add(P, mul(Q, c)), mul(R, s))

FIELDS = ['p1', 'p2', 'p3', 'p4', 'p5', 'q0', 'q1', 'q2', 'r0', 'r1', 'r2']

# ---------------------------------------------------------------- the phases (sympy)

t, c, s = sp.symbols('t c s')
a1, b1, b2, c1, c2, d1, d2 = sp.symbols('a1 b1 b2 c1 c2 d1 d2')
k1, k2 = sp.symbols('k1 k2')
Rt = sp.Rational
PH = {}
# phase index (Lean, 0-based) -> w1, w2, w1', w2', w1'', w2'', kappa   (a₂ = -1/4, e₁ = a₁, e₂ = 1/4,
# κ₁ = (1 - a₁, 1/4) substituted)
a2 = Rt(-1, 4); e1 = a1; e2 = Rt(1, 4)
PH[0] = dict(w1=a1*c+a2*s-1, w2=-a2*c+a1*s-Rt(1,2), w1p=-a1*s+a2*c, w2p=a2*s+a1*c, w1pp=-a1*c-a2*s,
             w2pp=a2*c-a1*s, k=(1-a1, Rt(1,4)))
PH[1] = dict(w1=-t**2/4+b1*t+b2, w2=t/2-b1-1, w1p=-t/2+b1, w2p=Rt(1,2), w1pp=Rt(-1,2), w2pp=0, k=(k1,k2))
PH[2] = dict(w1=c1-t, w2=c2+t, w1p=-1, w2p=1, w1pp=0, w2pp=0, k=(k1,k2))
PH[3] = dict(w1=-t/2+d1-1, w2=-t**2/4+d1*t+d2, w1p=Rt(-1,2), w2p=-t/2+d1, w1pp=0, w2pp=Rt(-1,2), k=(k1,k2))
PH[4] = dict(w1=e1*c+e2*s-Rt(1,2), w2=-e2*c+e1*s-1, w1p=-e1*s+e2*c, w2p=e2*s+e1*c, w1pp=-e1*c-e2*s,
             w2pp=e2*c-e1*s, k=(k1,k2))

def integrand(i, curve):
    p = PH[i]; w1, w2 = p['w1'], p['w2']; K1, K2 = p['k']
    rA = p['w1pp'] + w1 + 1; rC = p['w2pp'] + w2 + 1; al = p['w1p'] - w2; be = p['w2p'] + w1
    if curve == 'A': return rA * (w1 + 1 + K1*c + K2*s)
    if curve == 'C': return rC * (w2 + 1 - K1*s + K2*c)
    if curve == 'X': return w1*be - w2*al + al*(K1*s - K2*c) + be*(K1*c + K2*s)
    if curve == 'B': return (rA - 1) * (w1 + K1*c + K2*s)
    if curve == 'D': return (1 - rC) * (-w2 + K1*s - K2*c)

def split(f):
    f = sp.expand(f)
    d = sp.Poly(f, c, s).as_dict()
    for k in d: assert sum(k) <= 1
    return sp.expand(d.get((0, 0), 0)), sp.expand(d.get((1, 0), 0)), sp.expand(d.get((0, 1), 0))

def SC(p):
    S = 0; C = 0; k = 0
    while True:
        u, v = sp.diff(p, t, 2*k), sp.diff(p, t, 2*k+1)
        if u == 0 and v == 0: break
        S += (-1)**k * u; C += (-1)**k * v; k += 1
    return sp.expand(S), sp.expand(C)

def coeffs(i, curve):
    f = integrand(i, curve)
    p0, p1, p2 = split(f)
    Pp = sp.integrate(p0, t)
    S1, C1 = SC(p1); S2, C2 = SC(p2)
    Q = sp.expand(C1 - S2); R = sp.expand(S1 + C2)
    dF = sp.diff(Pp, t) + (sp.diff(Q, t) + R)*c + (sp.diff(R, t) - Q)*s
    assert sp.expand(dF - sp.expand(f)) == 0
    pc = [sp.expand(Pp).coeff(t, k) for k in range(6)]
    assert pc[0] == 0 and sp.degree(Pp, t) <= 5
    qc = [Q.coeff(t, k) for k in range(3)]; rc = [R.coeff(t, k) for k in range(3)]
    assert sp.degree(Q, t) <= 2 and sp.degree(R, t) <= 2
    K = dict(p1=pc[1], p2=pc[2], p3=pc[3], p4=pc[4], p5=pc[5], q0=qc[0], q1=qc[1], q2=qc[2],
             r0=rc[0], r1=rc[1], r2=rc[2])
    return {k: sp.factor(v) for k, v in K.items()}

# ---------------------------------------------------------------- atoms and their intervals

def D(x): return Fr(x)
ATOM = {
    'phi': (D('0.039177264'), D('0.039177465')),
    'th': (D('0.681301409'), D('0.68130161')),
    'a1': (D('1.210322322'), D('1.210322523')),
    'b1': (D('-0.527624699'), D('-0.527624498')),
    'b2': (D('0.920258285'), D('0.920258486')),
    'c1': (D('0.626045422'), D('0.626045623')),
    'k21': (D('-0.919179393'), D('-0.919179192')),
    'k22': (D('0.472406519'), D('0.47240672')),
    'k31': (D('-0.61376333'), D('-0.613763129')),
    'k32': (D('0.889626379'), D('0.88962658')),
    'k41': (D('-0.308347267'), D('-0.308347066')),
    'k42': (D('0.472406519'), D('0.47240672')),
    'k51': (D('-1.017204137'), D('-1.017203936')),
    'k52': (D('0.2499999'), D('0.2500001')),
    'pv': (D('3.14159265358'), D('3.14159265359')),
}

# ---------------------------------------------------------------- derived atoms

def chain_for(tree, env):
    ch = Chain(env)
    h, lo, hi = ch.ev(tree)
    return ch, h, lo, hi

DER = {}   # name -> (tree over atoms, Lean expression text, lo, hi, chain)
def derive(name, tree):
    env = {k: ('h' + k, v[0], v[1]) for k, v in ATOM.items()}
    ch, h, lo, hi = chain_for(tree, env)
    DER[name] = (tree, lo, hi, ch, h)
    ATOM[name] = (lo, hi)

V = Var
derive('c2', sub(V('c1'), Div(V('pv'), 2)))
derive('d1', sub(Div(V('pv'), 4), V('b1')))
derive('d2', add(V('b2'), mul(Div(V('pv'), 4), sub(mul(Const(2), V('b1')), Div(V('pv'), 4)))))
derive('pth', sub(Div(V('pv'), 2), V('th')))
derive('pphi', sub(Div(V('pv'), 2), V('phi')))
derive('p2', Div(V('pv'), 2))

# Taylor bounds for cos and sin (alternating series), k = 3
def cos_sum(y, n): return sum((-1)**i * y**(2*i) / math.factorial(2*i) for i in range(n))
def sin_sum(y, n): return sum((-1)**i * y**(2*i+1) / math.factorial(2*i+1) for i in range(n))
TK = 3
TRIG = {}
def trig(name, kind, ang):
    lo_x, hi_x = ATOM[ang]
    if kind == 'cos':
        lo = rdown(cos_sum(hi_x, 2*TK)); hi = rup(cos_sum(lo_x, 2*TK+1))
    else:
        lo = rdown(sin_sum(lo_x, 2*TK)); hi = rup(sin_sum(hi_x, 2*TK+1))
    ATOM[name] = (lo, hi)
    TRIG[name] = (kind, ang, lo, hi)
trig('cphi', 'cos', 'phi'); trig('sphi', 'sin', 'phi')
trig('cth', 'cos', 'th'); trig('sth', 'sin', 'th')

ENDP = {
    'zero': (('0', Fr(0), Fr(0)), ('1', Fr(1), Fr(1)), ('0', Fr(0), Fr(0))),
    'phi': ('phi', 'cphi', 'sphi'),
    'th': ('th', 'cth', 'sth'),
    'pth': ('pth', 'sth', 'cth'),
    'pphi': ('pphi', 'sphi', 'cphi'),
    'p2': ('p2', ('0', Fr(0), Fr(0)), ('1', Fr(1), Fr(1))),
}
def endp_ivs(kind):
    out = []
    for x in ENDP[kind]:
        if isinstance(x, tuple): out.append((x[1], x[2]))
        else: out.append(ATOM[x])
    return out

# ---------------------------------------------------------------- the phase integrals
# name, curve, Lean phase index, interval kinds, map K-variable -> atom
JOBS = [
    ('A2', 'A', 1, 'phi', 'th', dict(b1='b1', b2='b2', k1='k21', k2='k22')),
    ('A3', 'A', 2, 'th', 'pth', dict(c1='c1', k1='k31', k2='k32')),
    ('A4', 'A', 3, 'pth', 'pphi', dict(d1='d1', k1='k41', k2='k42')),
    ('A5', 'A', 4, 'pphi', 'p2', dict(a1='a1', k1='k51', k2='k52')),
    ('C1', 'C', 0, 'zero', 'phi', dict(a1='a1')),
    ('C2', 'C', 1, 'phi', 'th', dict(b1='b1', k1='k21', k2='k22')),
    ('C3', 'C', 2, 'th', 'pth', dict(c2='c2', k1='k31', k2='k32')),
    ('C4', 'C', 3, 'pth', 'pphi', dict(d1='d1', d2='d2', k1='k41', k2='k42')),
    ('X2', 'X', 1, 'phi', 'th', dict(b1='b1', b2='b2', k1='k21', k2='k22')),
    ('X3', 'X', 2, 'th', 'pth', dict(c1='c1', c2='c2', k1='k31', k2='k32')),
    ('X4', 'X', 3, 'pth', 'pphi', dict(d1='d1', d2='d2', k1='k41', k2='k42')),
    ('B4', 'B', 3, 'pth', 'pphi', dict(d1='d1', k1='k41', k2='k42')),
    ('B5', 'B', 4, 'pphi', 'p2', dict(a1='a1', k1='k51', k2='k52')),
    ('D1', 'D', 0, 'zero', 'phi', dict(a1='a1')),
    ('D2', 'D', 1, 'phi', 'th', dict(b1='b1', k1='k21', k2='k22')),
]
ORDER = ['a1', 'b1', 'b2', 'c1', 'c2', 'd1', 'd2', 'k1', 'k2']

RES = {}
for (nm, cv, i, ea, eb, vmap) in JOBS:
    Ks = coeffs(i, cv)
    free = set()
    for v in Ks.values(): free |= {str(x) for x in v.free_symbols}
    assert free <= set(vmap), (nm, free, vmap)
    vars_ = [v for v in ORDER if v in vmap]
    Kt = {f: from_sympy(Ks[f]) for f in FIELDS}
    env = {v: ('h' + v, ATOM[vmap[v]][0], ATOM[vmap[v]][1]) for v in vars_}
    (lta, lca, lsa), (ltb, lcb, lsb) = endp_ivs(ea), endp_ivs(eb)
    env['tA'] = ('htA',) + lta; env['cA'] = ('hcA',) + lca; env['sA'] = ('hsA',) + lsa
    env['tB'] = ('htB',) + ltb; env['cB'] = ('hcB',) + lcb; env['sB'] = ('hsB',) + lsb
    tree = mul(Const(Fr(1, 2)), sub(Fexpr(Kt, V('tB'), V('cB'), V('sB')), Fexpr(Kt, V('tA'), V('cA'), V('sA'))))
    ch, h, lo, hi = chain_for(tree, env)
    RES[nm] = dict(cv=cv, i=i, ea=ea, eb=eb, vmap=vmap, vars=vars_, Kt=Kt, Ks=Ks, env=env, ch=ch, h=h,
                   lo=lo, hi=hi)

if __name__ == '__main__' and 'sim' in sys.argv:
    for nm, r in RES.items():
        print(nm, float(r['lo']), float(r['hi']), 'width %.2e' % float(r['hi'] - r['lo']), 'steps', len(r['ch'].lines))
    for cv in 'ACXBD':
        lo = sum(r['lo'] for r in RES.values() if r['cv'] == cv)
        hi = sum(r['hi'] for r in RES.values() if r['cv'] == cv)
        print(cv, float(lo), float(hi), 'width %.2e' % float(hi - lo))
    for k, v in ATOM.items(): print(k, float(v[0]), float(v[1]))

# ---------------------------------------------------------------- Lean emission

LEANARG = {  # atom -> (Lean term for the parameter, Lean proof of its enclosure)
    'a1': ('P.a₁', 'hB.a₁_mem'), 'b1': ('P.b₁', 'hB.b₁_mem'), 'b2': ('P.b₂', 'hB.b₂_mem'),
    'c1': ('P.c₁', 'hB.c₁_mem'), 'c2': ('P.c₂', '(ga_c₂_mem hP hB)'),
    'd1': ('P.d₁', '(ga_d₁_mem hP hB)'), 'd2': ('P.d₂', '(ga_d₂_mem hP hB)'),
    'k21': ('P.κ₂.1', 'hB.κ₂₁_mem'), 'k22': ('P.κ₂.2', 'hB.κ₂₂_mem'),
    'k31': ('P.κ₃.1', 'hB.κ₃₁_mem'), 'k32': ('P.κ₃.2', 'hB.κ₃₂_mem'),
    'k41': ('P.κ₄.1', 'hB.κ₄₁_mem'), 'k42': ('P.κ₄.2', 'hB.κ₄₂_mem'),
    'k51': ('P.κ₅.1', 'hB.κ₅₁_mem'), 'k52': ('P.κ₅.2', 'hB.κ₅₂_mem'),
}
ENDLEAN = {  # endpoint kind -> (Lean endpoint, hyps for t, c, s)
    'zero': ('0', '(ga_iv_const 0)', '(by rw [cos_zero]; exact ga_iv_const 1)',
             '(by rw [sin_zero]; exact ga_iv_const 0)'),
    'phi': ('P.φ', 'hB.φ_mem', '(ga_cos_φ_mem hB)', '(ga_sin_φ_mem hB)'),
    'th': ('P.θ', 'hB.θ_mem', '(ga_cos_θ_mem hB)', '(ga_sin_θ_mem hB)'),
    'pth': ('(π / 2 - P.θ)', '(ga_pth_mem hB)', '(by rw [cos_pi_div_two_sub]; exact ga_sin_θ_mem hB)',
            '(by rw [sin_pi_div_two_sub]; exact ga_cos_θ_mem hB)'),
    'pphi': ('(π / 2 - P.φ)', '(ga_pphi_mem hB)', '(by rw [cos_pi_div_two_sub]; exact ga_sin_φ_mem hB)',
             '(by rw [sin_pi_div_two_sub]; exact ga_cos_φ_mem hB)'),
    'p2': ('(π / 2)', 'ga_p2_mem', '(by rw [cos_pi_div_two]; exact ga_iv_const 0)',
           '(by rw [sin_pi_div_two]; exact ga_iv_const 1)'),
}
PHASEINFO = {  # Lean phase index -> (lower kind, upper kind, hab proof, piece proof, gs_ph, extra simp)
    0: ('zero', 'phi', 'hO.φ_pos', 'fun t ht => gs_piece₀ ht.2', 'gs_ph1',
        ', gs_a₂ hP, gs_κ₁₁ hP, gs_κ₁₂ hP'),
    1: ('phi', 'th', 'hO.φ_lt_θ', 'fun t ht => gs_piece₁ ht.1 ht.2', 'gs_ph2', ''),
    2: ('th', 'pth', 'hO.θ_lt', 'fun t ht => gs_piece₂ ht.1 ht.2', 'gs_ph3', ''),
    3: ('pth', 'pphi', 'hO.lt_φ\'', 'fun t ht => gs_piece₃ ht.1 ht.2', 'gs_ph4', ''),
    4: ('pphi', 'p2', '(by linarith [hO.φ_pos])', 'fun t ht => gs_piece₄ ht.1', 'gs_ph5',
        ', gs_e₁ hP, gs_e₂ hP, gs_a₂ hP'),
}
CURVE = {  # curve -> (Lean curve, phase lemma, cross lemma, simp of the frame quantities, continuity)
    'A': ('contactA P.path', 'ga_phase_A', 'ga_cross_A', 'gs_Phase.ρA', 'ga_continuous_ρA%s'),
    'B': ('contactB P.path', 'ga_phase_B', 'ga_cross_B', 'gs_Phase.ρA', 'ga_continuous_ρA%s'),
    'C': ('contactC P.path', 'ga_phase_C', 'ga_cross_C', 'gs_Phase.ρC', 'ga_continuous_ρC%s'),
    'D': ('contactD P.path', 'ga_phase_D', 'ga_cross_D', 'gs_Phase.ρC', 'ga_continuous_ρC%s'),
    'X': ('P.path', 'ga_phase_X', 'ga_cross_X', 'gs_Phase.α, gs_Phase.β', None),
}
SUB = '₀₁₂₃₄'
CURVENAME = {'A': '𝐀', 'B': '𝐁', 'C': '𝐂', 'D': '𝐃', 'X': '𝐱'}
PHNAME = {0: '`[0, φ]`', 1: '`[φ, θ]`', 2: '`[θ, π/2 - θ]`', 3: '`[π/2 - θ, π/2 - φ]`',
          4: '`[π/2 - φ, π/2]`'}

def hyp(name, lo, hi):
    return '(h%s : %s ∈ Icc %s %s)' % (name, name, lit(lo), lit(hi))

def wrap_args(prefix, items, indent='    ', width=100):
    lines = []
    cur = prefix
    for it in items:
        if len(cur) + 1 + len(it) > width:
            lines.append(cur)
            cur = indent + it
        else:
            cur = cur + (' ' if cur.strip() else '') + it if cur.strip() else indent + it
    lines.append(cur)
    return '\n'.join(lines)

def emit_chain_lemma(name, vars_, env, ch, h, concl):
    out = []
    head = 'theorem %s {%s : ℝ}' % (name, ' '.join(vars_))
    hyps = [hyp(v, env[v][1], env[v][2]) for v in vars_ if not env[v][0].startswith('(')]
    out.append(wrap_args(head, hyps))
    out[-1] += ' :'
    out.append('    ' + concl + ' := by')
    out.extend(ch.lines)
    out.append('  exact ' + h)
    return '\n'.join(out)

def emit_K(nm):
    r = RES[nm]
    lines = ['/-- Coefficients of an antiderivative of `%s × %s\'` on phase %s. -/' %
             (CURVENAME[r['cv']], CURVENAME[r['cv']], PHNAME[r['i']])]
    lines.append('noncomputable def ga_K_%s (%s : ℝ) : ga_TP where' % (nm, ' '.join(r['vars'])))
    for f in FIELDS:
        lines.append('  %s := %s' % (f, strip(pr(r['Kt'][f]))))
    return '\n'.join(lines)

def emit_num(nm):
    r = RES[nm]
    vs = r['vars'] + ['tA', 'cA', 'sA', 'tB', 'cB', 'sB']
    K = '(ga_K_%s %s)' % (nm, ' '.join(r['vars']))
    concl = '1 / 2 * (%s.F tB cB sB - %s.F tA cA sA) ∈\n      Icc %s %s' % (K, K, lit(r['lo']), lit(r['hi']))
    return emit_chain_lemma('ga_num_' + nm, vs, r['env'], r['ch'], r['h'], concl)

def emit_phase(nm):
    r = RES[nm]
    i = r['i']
    lo_k, hi_k, hab, pc, gph, extra = PHASEINFO[i]
    cl, plem, xlem, fq, cont = CURVE[r['cv']]
    Kargs = ' '.join(LEANARG[r['vmap'][v]][0] for v in r['vars'])
    K = '(ga_K_%s %s)' % (nm, Kargs)
    a = ENDLEAN[lo_k][0]; b = ENDLEAN[hi_k][0]
    out = []
    out.append('lemma ga_%s (hP : P.IsSolution) :' % nm)
    cls = '(%s)' % cl if ' ' in cl else cl
    out.append('    curveArea %s %s %s = 1 / 2 *' % (cls, a, b))
    l1 = '      (%s.F %s (cos %s) (sin %s) -' % (K, b, b, b)
    l2 = '        %s.F %s (cos %s) (sin %s)) := by' % (K, a, a, a)
    if len(l1) > 100:
        l1 = '      (%s.F %s\n        (cos %s) (sin %s) -' % (K, b, b, b)
    if len(l2) > 100:
        l2 = '        %s.F %s\n          (cos %s) (sin %s)) := by' % (K, a, a, a)
    out.append(l1)
    out.append(l2)
    out.append('  have hO := gs_ord hP')
    if cont:
        line = '  refine %s hP %s %s (%s) _ fun t => ?_' % (plem, hab, cont % SUB[i], pc)
        if len(line) > 100:
            line = '  refine %s hP %s %s (%s) _\n    fun t => ?_' % (plem, hab, cont % SUB[i], pc)
    else:
        line = '  refine %s hP %s (%s) _ fun t => ?_' % (plem, hab, pc)
        if len(line) > 100:
            line = '  refine %s hP %s (%s) _\n    fun t => ?_' % (plem, hab, pc)
    out.append(line)
    out.append('  rw [%s]' % xlem)
    out.append('  simp only [gs_phase, %s, %s, ga_TP.dF, ga_K_%s%s]' % (gph, fq, nm, extra))
    out.append('  ring')
    return '\n'.join(out)

def emit_mem(nm):
    r = RES[nm]
    i = r['i']
    lo_k, hi_k = PHASEINFO[i][0], PHASEINFO[i][1]
    cl = CURVE[r['cv']][0]
    a = ENDLEAN[lo_k][0]; b = ENDLEAN[hi_k][0]
    args = [LEANARG[r['vmap'][v]][1] for v in r['vars']]
    args += list(ENDLEAN[lo_k][1:]) + list(ENDLEAN[hi_k][1:])
    out = ['lemma ga_%s_mem (hP : P.IsSolution) (hB : P.Bounds) :' % nm]
    cls = '(%s)' % cl if ' ' in cl else cl
    line = '    curveArea %s %s %s ∈ Icc %s %s := by' % (cls, a, b, lit(r['lo']), lit(r['hi']))
    if len(line) > 100:
        out.append('    curveArea %s %s %s ∈' % (cls, a, b))
        out.append('      Icc %s %s := by' % (lit(r['lo']), lit(r['hi'])))
    else:
        out.append(line)
    out.append('  rw [ga_%s hP]' % nm)
    out.append(wrap_args('  exact ga_num_%s' % nm, args, indent='    '))
    return '\n'.join(out)

def emit_derived(name, lname, vars_):
    tree, lo, hi, ch, h = DER[name]
    env = {k: ('h' + k, ATOM[k][0], ATOM[k][1]) for k in vars_}
    concl = '%s ∈ Icc %s %s' % (strip(pr(tree)), lit(lo), lit(hi))
    if len(concl) > 85:
        concl = '%s ∈\n      Icc %s %s' % (strip(pr(tree)), lit(lo), lit(hi))
    return emit_chain_lemma(lname, vars_, env, ch, h, concl)

def emit_seg():
    tree = Div(sub(add(V('a1'), V('k51')), mul(add(Const(Fr(3, 4)), V('k52')),
                                                  sub(Const(1), mul(Const(2), V('a1'))))), 2)
    env = {k: ('h' + k, ATOM[k][0], ATOM[k][1]) for k in ['a1', 'k51', 'k52']}
    ch, h, lo, hi = chain_for(tree, env)
    concl = '%s ∈\n      Icc %s %s' % (strip(pr(tree)), lit(lo), lit(hi))
    return emit_chain_lemma('ga_num_seg', ['a1', 'k51', 'k52'], env, ch, h, concl), lo, hi, tree

def trig_lemma(name):
    kind, ang, lo, hi = TRIG[name]
    alo, ahi = ATOM[ang]
    lname = {'cphi': 'ga_cos_φ_mem', 'sphi': 'ga_sin_φ_mem', 'cth': 'ga_cos_θ_mem',
             'sth': 'ga_sin_θ_mem'}[name]
    pv = {'phi': 'P.φ', 'th': 'P.θ'}[ang]
    mem = {'phi': 'hB.φ_mem', 'th': 'hB.θ_mem'}[ang]
    fn = kind
    out = ['lemma %s (hB : P.Bounds) : %s %s ∈ Icc %s %s := by' % (lname, fn, pv, lit(lo), lit(hi))]
    out.append('  have hx := %s' % mem)
    out.append('  have hpi := pi_gt_three')
    if kind == 'cos':
        out.append('  have h1 : %s ≤ cos %s := by' % (lit(lo), lit(ahi)))
        out.append('    refine le_trans ?_ (ga_cos_ge (by norm_num) (by norm_num) %d)' % TK)
        out.append('    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]')
        out.append('    norm_num')
        out.append('  have h2 : cos %s ≤ %s := by' % (lit(alo), lit(hi)))
        out.append('    refine (ga_cos_le (by norm_num) (by norm_num) %d).trans ?_' % TK)
        out.append('    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]')
        out.append('    norm_num')
        out.append('  exact ⟨h1.trans (cos_le_cos_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith) hx.2),')
        out.append('    (cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [hx.2]) hx.1).trans h2⟩')
    else:
        out.append('  have h1 : %s ≤ sin %s := by' % (lit(lo), lit(alo)))
        out.append('    refine le_trans ?_ (ga_sin_ge (by norm_num) (by norm_num) %d)' % TK)
        out.append('    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]')
        out.append('    norm_num')
        out.append('  have h2 : sin %s ≤ %s := by' % (lit(ahi), lit(hi)))
        out.append('    refine (ga_sin_le (by norm_num) (by norm_num) %d).trans ?_' % TK)
        out.append('    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]')
        out.append('    norm_num')
        out.append('  exact ⟨h1.trans (sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hx.2]) hx.1),')
        out.append('    (sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith) hx.2).trans h2⟩')
    return '\n'.join(out)


def r4(x, up):
    q = Fr(10) ** 4
    return (Fr(math.ceil(x * q)) if up else Fr(math.floor(x * q))) / q

DERIVED_USE = [
    # name, chain lemma, vars, use-site lemma text template
    ('c2', 'ga_num_c2', ['c1', 'pv'],
     'lemma ga_c₂_mem (hP : P.IsSolution) (hB : P.Bounds) :\n    P.c₂ ∈ Icc %s %s := by\n'
     '  rw [gs_c₂ hP]; exact ga_num_c2 hB.c₁_mem ga_pi_mem'),
    ('d1', 'ga_num_d1', ['pv', 'b1'],
     'lemma ga_d₁_mem (hP : P.IsSolution) (hB : P.Bounds) :\n    P.d₁ ∈ Icc %s %s := by\n'
     '  rw [gs_d₁ hP]; exact ga_num_d1 ga_pi_mem hB.b₁_mem'),
    ('d2', 'ga_num_d2', ['pv', 'b1', 'b2'],
     'lemma ga_d₂_mem (hP : P.IsSolution) (hB : P.Bounds) :\n    P.d₂ ∈ Icc %s %s := by\n'
     '  rw [gs_d₂ hP]; exact ga_num_d2 ga_pi_mem hB.b₁_mem hB.b₂_mem'),
    ('pth', 'ga_num_pth', ['pv', 'th'],
     'lemma ga_pth_mem (hB : P.Bounds) : π / 2 - P.θ ∈ Icc %s %s :=\n'
     '  ga_num_pth ga_pi_mem hB.θ_mem'),
    ('pphi', 'ga_num_pphi', ['pv', 'phi'],
     'lemma ga_pphi_mem (hB : P.Bounds) : π / 2 - P.φ ∈ Icc %s %s :=\n'
     '  ga_num_pphi ga_pi_mem hB.φ_mem'),
    ('p2', 'ga_num_p2', ['pv'],
     'lemma ga_p2_mem : π / 2 ∈ Icc %s %s :=\n'
     '  ga_num_p2 ga_pi_mem'),
]

def emit_params():
    out = ['/-! ### Enclosures of the parameters, of the phase endpoints, and of `cos`, `sin` at `φ`, `θ` -/',
           '']
    for (nm, lname, vars_, use) in DERIVED_USE:
        out.append(emit_derived(nm, lname, vars_))
        out.append('')
        lo, hi = ATOM[nm]
        out.append(use % (lit(lo), lit(hi)))
        out.append('')
    for nm in ['cphi', 'sphi', 'cth', 'sth']:
        out.append(trig_lemma(nm))
        out.append('')
    return '\n'.join(out)

CURVE_ORDER = [('A', ['A2', 'A3', 'A4', 'A5']), ('C', ['C1', 'C2', 'C3', 'C4']),
               ('X', ['X2', 'X3', 'X4']), ('B', ['B4', 'B5']), ('D', ['D1', 'D2'])]
TITLE = {'A': '𝒥(𝐀|[0, π/2])', 'C': '𝒥(𝐂|[0, π/2])', 'X': '𝒥(𝐱|[t₁, t₄])', 'B': '𝒥(𝐁|[t₃, π/2])',
         'D': '𝒥(𝐃|[0, t₂])'}

def emit_phases():
    out = []
    for cv, nms in CURVE_ORDER:
        out.append('/-! ### %s on each phase -/' % TITLE[cv])
        out.append('')
        for nm in nms:
            out.append(emit_K(nm)); out.append('')
            out.append(emit_num(nm)); out.append('')
            out.append(emit_phase(nm)); out.append('')
            out.append(emit_mem(nm)); out.append('')
    return '\n'.join(out)

def tot(cv):
    lo = sum(r['lo'] for r in RES.values() if r['cv'] == cv)
    hi = sum(r['hi'] for r in RES.values() if r['cv'] == cv)
    return lo, hi

def hyps_list(nms):
    hs = []
    for k, nm in enumerate(nms):
        hs += ['h%d.1' % k, 'h%d.2' % k]
    return ', '.join(hs)

def emit_tail(seg):
    seg_text, slo, shi, _ = seg
    out = ['/-! ### The six curve areas -/', '']
    bounds = {}
    for cv, nms in CURVE_ORDER:
        lo, hi = tot(cv)
        bounds[cv] = (r4(lo, False), r4(hi, True))
    bounds['S'] = (r4(slo, False), r4(shi, True))
    def stmt(name, lhs, b, doc):
        return ['/-- %s -/' % doc, 'theorem %s (hP : P.IsSolution) (hB : P.Bounds) :' % name,
                '    %s ∈ Icc %s %s := by' % (lhs, lit(b[0]), lit(b[1]))]
    def haves(nms):
        return ['  have h%d := ga_%s_mem hP hB' % (k, nm) for k, nm in enumerate(nms)]
    # A
    out += stmt('ga_curveArea_A_mem', 'curveArea (contactA P.path) 0 (π / 2)', bounds['A'],
                'The curve area `𝒥(𝐀|[0, π/2]) = 0.72016…`.')
    out += ['  have hO := gs_ord hP',
            '  rw [ga_split_five hO.φ_pos.le hO.φ_lt_θ.le hO.θ_lt.le hO.lt_φ\'.le (by linarith [hO.φ_pos])',
            '    (ga_isCBV_A hP), ga_A1 hP]']
    out += haves(['A2', 'A3', 'A4', 'A5'])
    out += ['  constructor <;> linarith [%s]' % hyps_list(['A2', 'A3', 'A4', 'A5']), '']
    # C
    out += stmt('ga_curveArea_C_mem', 'curveArea (contactC P.path) 0 (π / 2)', bounds['C'],
                'The curve area `𝒥(𝐂|[0, π/2]) = 1.33392…`.')
    out += ['  have hO := gs_ord hP',
            '  rw [ga_split_five hO.φ_pos.le hO.φ_lt_θ.le hO.θ_lt.le hO.lt_φ\'.le (by linarith [hO.φ_pos])',
            '    (ga_isCBV_C hP), ga_C5 hP]']
    out += haves(['C1', 'C2', 'C3', 'C4'])
    out += ['  constructor <;> linarith [%s]' % hyps_list(['C1', 'C2', 'C3', 'C4']), '']
    # segment
    out += [seg_text, '']
    out += stmt('ga_segArea_mem', 'segArea (contactA P.path (π / 2)) (contactC P.path 0)', bounds['S'],
                'The curve area of the segment from `𝐀(π/2)` to `𝐂(0)`, `0.80688…`.')
    out += ['  rw [ga_segArea_eq hP]',
            '  have h := ga_num_seg hB.a₁_mem hB.κ₅₁_mem hB.κ₅₂_mem',
            '  exact ⟨by linarith [h.1], by linarith [h.2]⟩', '']
    # X
    out += stmt('ga_curveArea_x_mem', 'curveArea P.path P.φ (π / 2 - P.φ)', bounds['X'],
                'The curve area `𝒥(𝐱|[t₁, t₄]) = 0.60139…` of the rotation path.')
    out += ['  have hO := gs_ord hP',
            '  rw [ga_split_three hO.φ_lt_θ.le hO.θ_lt.le hO.lt_φ\'.le (ga_isCBV_X hP)]']
    out += haves(['X2', 'X3', 'X4'])
    out += ['  constructor <;> linarith [%s]' % hyps_list(['X2', 'X3', 'X4']), '']
    # B
    out += stmt('ga_curveArea_B_mem', 'curveArea (contactB P.path) (π / 2 - P.θ) (π / 2)', bounds['B'],
                'The curve area `𝒥(𝐁|[t₃, π/2]) = -0.00308…`.')
    out += ['  have hO := gs_ord hP',
            '  rw [proposition7_2_6 hO.lt_φ\'.le (by linarith [hO.φ_pos]) (ga_isCBV_B hP)]']
    out += haves(['B4', 'B5'])
    out += ['  constructor <;> linarith [%s]' % hyps_list(['B4', 'B5']), '']
    # D
    out += stmt('ga_curveArea_D_mem', 'curveArea (contactD P.path) 0 P.θ', bounds['D'],
                'The curve area `𝒥(𝐃|[0, t₂]) = -0.03695…`.')
    out += ['  have hO := gs_ord hP',
            '  rw [proposition7_2_6 hO.φ_pos.le hO.φ_lt_θ.le (ga_isCBV_D hP)]']
    out += haves(['D1', 'D2'])
    out += ['  constructor <;> linarith [%s]' % hyps_list(['D1', 'D2']), '']
    s = (bounds['A'][0] + bounds['C'][0] + bounds['S'][0] - bounds['X'][1] + bounds['B'][0]
         + bounds['D'][0])
    assert s >= Fr(22, 10), s
    for k, b in bounds.items():
        assert b[1] - b[0] <= Fr(2, 1000), (k, b)
    out += ['/-- **Lower bound for the area of Gerver\'s sofa.** The area of the cap,',
            '`𝒥(𝐀) + 𝒥(𝐀(π/2), 𝐂(0)) + 𝒥(𝐂)`, minus the area of the niche,',
            '`𝒥(𝐱|[t₁, t₄]) - 𝒥(𝐁|[t₃, π/2]) - 𝒥(𝐃|[0, t₂])`, is at least `2.2` (its value is',
            '`2.21953…`). -/',
            'theorem ga_area_lower (hP : P.IsSolution) (hB : P.Bounds) :',
            '    2.2 ≤ curveArea (contactA P.path) 0 (π / 2) + curveArea (contactC P.path) 0 (π / 2)',
            '      + segArea (contactA P.path (π / 2)) (contactC P.path 0)',
            '      - curveArea P.path P.φ (π / 2 - P.φ)',
            '      + curveArea (contactB P.path) (π / 2 - P.θ) (π / 2)',
            '      + curveArea (contactD P.path) 0 P.θ := by',
            '  have h1 := ga_curveArea_A_mem hP hB',
            '  have h2 := ga_curveArea_C_mem hP hB',
            '  have h3 := ga_segArea_mem hP hB',
            '  have h4 := ga_curveArea_x_mem hP hB',
            '  have h5 := ga_curveArea_B_mem hP hB',
            '  have h6 := ga_curveArea_D_mem hP hB',
            '  linarith [h1.1, h2.1, h3.1, h4.2, h5.1, h6.1]', '',
            'end MovingSofaOptimality.GerverParams', '']
    return '\n'.join(out), bounds, s

if __name__ == '__main__' and 'emit' in sys.argv:
    out = sys.argv[sys.argv.index('emit') + 1]
    parts = [open('tpl_head.lean.in').read(), open('iv.lean.in').read(), open('tpl_generic.lean.in').read(),
             open('tpl_phase.lean.in').read(), emit_params(), emit_phases()]
    tail, bounds, s = emit_tail(emit_seg())
    parts.append(tail)
    import re
    text = re.sub(r'\n{3,}', '\n\n', '\n'.join(parts))
    open(out, 'w').write(text)
    for k, b in bounds.items(): print(k, dec(b[0]), dec(b[1]))
    print('lower bound sum', float(s))
