"""Generator for the interval-arithmetic and derivative proofs of MovingSofa/External/Romik*.lean."""
from fractions import Fraction as Fr
import math, itertools
import sympy as sp
import mpmath as mp

mp.mp.dps = 60

ATOMS = ['φ', 'θ', 'c', 's', 'C', 'S', 'p']

# ---------------------------------------------------------------- expressions
class E:
    def __add__(a, b): return Bin('+', a, wrap(b))
    def __radd__(a, b): return Bin('+', wrap(b), a)
    def __sub__(a, b): return Bin('-', a, wrap(b))
    def __rsub__(a, b): return Bin('-', wrap(b), a)
    def __mul__(a, b): return Bin('*', a, wrap(b))
    def __rmul__(a, b): return Bin('*', wrap(b), a)
    def __truediv__(a, b): return Bin('/', a, wrap(b))
    def __neg__(a): return Neg(a)

def wrap(x):
    if isinstance(x, E): return x
    if isinstance(x, int): return Num(str(x), Fr(x))
    raise TypeError(x)

class Var(E):
    def __init__(self, name): self.name = name
    def lean(self): return self.name
    def atoms(self): return {self.name}
    def refs(self): return set()

class Num(E):
    def __init__(self, s, val): self.s = s; self.val = Fr(val)
    def lean(self): return self.s
    def atoms(self): return set()
    def refs(self): return set()

def dec(s):  # decimal literal
    return Num(s, Fr(s))

class Ref(E):
    def __init__(self, name): self.name = name
    def lean(self): return '(' + DEFS[self.name].call() + ')'
    def atoms(self): return set(DEFS[self.name].atoms)
    def refs(self): return {self.name}

class Bin(E):
    def __init__(self, op, a, b): self.op = op; self.a = a; self.b = b
    def lean(self): return '(' + self.a.lean() + ' ' + self.op + ' ' + self.b.lean() + ')'
    def atoms(self): return self.a.atoms() | self.b.atoms()
    def refs(self): return self.a.refs() | self.b.refs()

class Neg(E):
    def __init__(self, a): self.a = a
    def lean(self): return '(-' + self.a.lean() + ')'
    def atoms(self): return self.a.atoms()
    def refs(self): return self.a.refs()

φ, θ, c, s, C, S, p = [Var(n) for n in ATOMS]

class Def:
    def __init__(self, name, expr, doc):
        self.name = name; self.expr = expr; self.doc = doc
        self.atoms = [a for a in ATOMS if a in expr.atoms()]
    def call(self, args=None):
        if args is None: args = self.atoms
        else: args = [args[a] for a in self.atoms]
        return ' '.join([self.name] + args)

DEFS = {}
ORDER = []
def define(name, expr, doc):
    DEFS[name] = Def(name, expr, doc); ORDER.append(name)
    return Ref(name)

H = lambda n: Fr(1, n)
half = Num('1 / 2', Fr(1, 2)); threehalf = Num('3 / 2', Fr(3, 2)); quarter = Num('1 / 4', Fr(1, 4))

K = define('rom_K', p / 2 - threehalf - θ + θ * θ / 4, 'the quantity `K = π/2 - 3/2 - θ + θ²/4`')
Kθ = define('rom_Kθ', θ / 2 - 1, '`∂K/∂θ`')
D = define('rom_D', 2 * c - (2 + θ - φ) * s, 'the coefficient `D = 2 cos φ - (2 + θ - φ) sin φ` of `a₁`')
Nb = define('rom_Nb', c * (φ - half - c / 2) - s * (s / 2 - φ * φ / 4 + K + threehalf),
            'the numerator `N_b` of `b₁ = N_b / D`')
U1 = define('rom_U1', -(c * (K - φ * φ / 4)) + s * (φ / 2 - 1) + 3 * C / 2 + S * (3 * θ / 2 - 3),
            'the first component of `U`')
V1 = define('rom_V1', c * (2 + θ - φ) - s - 3 * S, 'the first component of `V`')
U2 = define('rom_U2', -(s * (K - φ * φ / 4)) - c * (φ / 2 - 1) - S / 2 + C * (θ / 2 - 1),
            'the second component of `U`')
V2 = define('rom_V2', s * (2 + θ - φ) + c - C, 'the second component of `V`')
H1 = define('rom_H1', D * U1 + Nb * V1, 'the first component of `H = D U + N_b V`')
H2 = define('rom_H2', D * U2 + Nb * V2, 'the second component of `H = D U + N_b V`')
# partial derivatives
Dφ = define('rom_Dφ', c * (φ - θ - 2) - s, '`∂D/∂φ`')
Dθ = define('rom_Dθ', -s, '`∂D/∂θ`')
Nbφ = define('rom_Nbφ', c * (φ * φ / 4 - K - half) + s * (1 - φ) / 2, '`∂N_b/∂φ`')
Nbθ = define('rom_Nbθ', s * (1 - θ / 2), '`∂N_b/∂θ`')
U1φ = define('rom_U1φ', s * (K - φ * φ / 4 + half) + c * (φ - 1), '`∂U₁/∂φ`')
U1θ = define('rom_U1θ', -(c * (θ / 2 - 1)) + C * (3 * θ / 2 - 3), '`∂U₁/∂θ`')
V1φ = define('rom_V1φ', -(s * (2 + θ - φ)) - 2 * c, '`∂V₁/∂φ`')
V1θ = define('rom_V1θ', c - 3 * C, '`∂V₁/∂θ`')
U2φ = define('rom_U2φ', -(c * (K - φ * φ / 4 + half)) + s * (φ - 1), '`∂U₂/∂φ`')
U2θ = define('rom_U2θ', (s + S) * (1 - θ / 2), '`∂U₂/∂θ`')
V2φ = define('rom_V2φ', c * (2 + θ - φ) - 2 * s, '`∂V₂/∂φ`')
V2θ = define('rom_V2θ', s + S, '`∂V₂/∂θ`')
H1φ = define('rom_H1φ', Dφ * U1 + D * U1φ + Nbφ * V1 + Nb * V1φ, '`∂H₁/∂φ`')
H1θ = define('rom_H1θ', Dθ * U1 + D * U1θ + Nbθ * V1 + Nb * V1θ, '`∂H₁/∂θ`')
H2φ = define('rom_H2φ', Dφ * U2 + D * U2φ + Nbφ * V2 + Nb * V2φ, '`∂H₂/∂φ`')
H2θ = define('rom_H2θ', Dθ * U2 + D * U2θ + Nbθ * V2 + Nb * V2θ, '`∂H₂/∂θ`')
M11, M12, M21, M22 = dec('0.1481'), dec('0.2886'), dec('2.7218'), dec('0.6267')
G1 = define('rom_G1', φ + (M11 * H1 + M12 * H2), 'the first component of the Newton map')
G2 = define('rom_G2', θ + (M21 * H1 - M22 * H2), 'the second component of the Newton map')
G1φ = define('rom_G1φ', 1 + (M11 * H1φ + M12 * H2φ), '`∂G₁/∂φ`')
G1θ = define('rom_G1θ', M11 * H1θ + M12 * H2θ, '`∂G₁/∂θ`')
G2φ = define('rom_G2φ', M21 * H1φ - M22 * H2φ, '`∂G₂/∂φ`')
G2θ = define('rom_G2θ', 1 + (M21 * H1θ - M22 * H2θ), '`∂G₂/∂θ`')
MH1 = define('rom_MH1', M11 * H1 + M12 * H2, 'the first component of `M H`')
MH2 = define('rom_MH2', M21 * H1 - M22 * H2, 'the second component of `M H`')
# parameters
beta0 = define('rom_β₀', (φ - half - c / 2) / 2, 'the constant term `β₀` of `b₁ = β₀ - a₁ sin φ`')
Nn = define('rom_N', s / 2 - φ * φ / 4 + K + threehalf - (2 + θ - φ) * beta0, 'the numerator of `a₁ = N / D`')
A1 = define('rom_a₁', Nn / D, 'the parameter `a₁`')
B1 = define('rom_b₁', beta0 - s * A1, 'the parameter `b₁`')
B2 = define('rom_b₂', K - (2 + θ) * B1, 'the parameter `b₂`')
C1 = define('rom_c₁', p / 2 - 2 - 2 * B1, 'the parameter `c₁`')
Δ1 = define('rom_Δ₁', A1 * c - s / 4 - 1 - (-(φ * φ / 4) + B1 * φ + B2), 'first coordinate of `w₁(φ) - w₂(φ)`')
Δ2 = define('rom_Δ₂', c / 4 + A1 * s - half - (φ / 2 - B1 - 1), 'second coordinate of `w₁(φ) - w₂(φ)`')
K21 = define('rom_κ₂₁', c * Δ1 - s * Δ2 + (1 - A1), 'the first coordinate of `κ₂`')
K22 = define('rom_κ₂₂', s * Δ1 + c * Δ2 + quarter, 'the second coordinate of `κ₂`')
K31 = define('rom_κ₃₁', C / 2 - S * (1 + B1 - θ / 2) + K21, 'the first coordinate of `κ₃`')
K32 = define('rom_κ₃₂', S / 2 + C * (1 + B1 - θ / 2) + K22, 'the second coordinate of `κ₃`')
K41 = define('rom_κ₄₁', 2 * K31 - K21, 'the first coordinate of `κ₄`')
K51 = define('rom_κ₅₁', 2 * K31 - 1 + A1, 'the first coordinate of `κ₅`')

# ---------------------------------------------------------------- sympy check of the partials
def to_sympy(e, env):
    if isinstance(e, Var): return env[e.name]
    if isinstance(e, Num): return sp.Rational(e.val.numerator, e.val.denominator)
    if isinstance(e, Ref): return to_sympy(DEFS[e.name].expr, env)
    if isinstance(e, Neg): return -to_sympy(e.a, env)
    a, b = to_sympy(e.a, env), to_sympy(e.b, env)
    return {'+': a + b, '-': a - b, '*': a * b, '/': a / b}[e.op]

def check_partials():
    x, y, pp = sp.symbols('x y p')
    env = {'φ': x, 'θ': y, 'c': sp.cos(x), 's': sp.sin(x), 'C': sp.cos(y), 'S': sp.sin(y), 'p': pp}
    for base in ['rom_D', 'rom_Nb', 'rom_U1', 'rom_V1', 'rom_U2', 'rom_V2', 'rom_H1', 'rom_H2', 'rom_G1', 'rom_G2']:
        f = to_sympy(DEFS[base].expr, env)
        for v, sym in [('φ', x), ('θ', y)]:
            g = to_sympy(DEFS[base + v].expr, env)
            d = sp.simplify(sp.expand(sp.diff(f, sym) - g))
            assert d == 0, (base, v, d)
    print('partials ok')

# ---------------------------------------------------------------- interval arithmetic
def rnd_down(x, k):
    q = Fr(10) ** k
    return Fr(math.floor(x * q)) / q
def rnd_up(x, k):
    q = Fr(10) ** k
    return Fr(math.ceil(x * q)) / q

def fmt(x):
    """exact decimal string of a Fraction whose denominator divides a power of 10"""
    neg = x < 0; x = abs(x)
    k = 0
    while (x * Fr(10) ** k).denominator != 1:
        k += 1
        if k > 100: raise ValueError(x)
    n = int(x * Fr(10) ** k)
    s = str(n)
    if k > 0:
        s = s.rjust(k + 1, '0'); s = s[:-k] + '.' + s[-k:]
    return ('-' if neg else '') + s

def lean_num(x):
    s = fmt(x)
    return '(' + s + ' : ℝ)'

class Emitter:
    def __init__(self, digits):
        self.digits = digits; self.lines = []; self.cnt = 0; self.ivs = {}
    def fresh(self):
        self.cnt += 1; return 'h%d' % self.cnt
    def rnd(self, lo, hi):
        return rnd_down(lo, self.digits), rnd_up(hi, self.digits)
    def ev(self, e, env):
        """returns (hyp name, (lo, hi)) and emits lines"""
        if isinstance(e, Var):
            return env[e.name]
        if isinstance(e, Num):
            return ('(rom_iv_self (' + e.s + ' : ℝ))', (e.val, e.val))
        if isinstance(e, Ref):
            return env[e.name]
        if isinstance(e, Neg):
            ha, (a, b) = self.ev(e.a, env)
            lo, hi = -b, -a
            h = self.fresh()
            self.lines.append('have %s := rom_iv_neg (L := %s) (U := %s) %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha))
            return (h, (lo, hi))
        ha, (a, b) = self.ev(e.a, env)
        if e.op == '/' and isinstance(e.b, Num):
            k = e.b.val
            assert k > 0
            lo, hi = self.rnd(a / k, b / k)
            h = self.fresh()
            self.lines.append('have %s := rom_iv_div (L := %s) (U := %s) %s (k := %s) (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, e.b.s))
            return (h, (lo, hi))
        hb, (cc, d) = self.ev(e.b, env)
        h = self.fresh()
        if e.op == '+':
            lo, hi = self.rnd(a + cc, b + d)
            self.lines.append('have %s := rom_iv_add (L := %s) (U := %s) %s %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, hb))
        elif e.op == '-':
            lo, hi = self.rnd(a - d, b - cc)
            self.lines.append('have %s := rom_iv_sub (L := %s) (U := %s) %s %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, hb))
        elif e.op == '*':
            if a >= 0 and cc >= 0:
                lo, hi = self.rnd(a * cc, b * d)
                self.lines.append('have %s := rom_iv_mul_nn (L := %s) (U := %s) %s %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, hb))
            else:
                prods = [a * cc, a * d, b * cc, b * d]
                lo, hi = self.rnd(min(prods), max(prods))
                self.lines.append('have %s := rom_iv_mul (L := %s) (U := %s) %s %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, hb))
        elif e.op == '/':
            assert a >= 0 and cc > 0
            lo, hi = self.rnd(a / d, b / cc)
            self.lines.append('have %s := rom_iv_div2 (L := %s) (U := %s) %s %s (by norm_num)' % (h, lean_num(lo), lean_num(hi), ha, hb))
        else:
            raise ValueError(e.op)
        return (h, (lo, hi))

HYP = {'φ': 'hφ', 'θ': 'hθ', 'c': 'hc', 's': 'hs', 'C': 'hC', 'S': 'hS', 'p': 'hp'}

def gen_regime(regime, names, atom_iv, digits, out_iv=None):
    """Emit interval lemmas `name_regime` for each def in `names` (in order).
    atom_iv: dict atom -> (lo, hi) Fractions. Returns dict name -> (lo, hi) and lean text."""
    results = {}
    text = []
    for name in names:
        d = DEFS[name]
        em = Emitter(digits)
        env = {}
        for a in d.atoms:
            env[a] = (HYP[a], atom_iv[a])
        # refs used directly
        for r in sorted(d.expr.refs()):
            rd = DEFS[r]
            hn = em.fresh()
            em.lines.append('have %s := %s_%s %s' % (hn, r, regime, ' '.join(HYP[a] for a in rd.atoms)))
            env[r] = (hn, results[r])
        h, (lo, hi) = em.ev(d.expr, env)
        results[name] = (lo, hi)
        hyps = '\n'.join('    (%s : %s ∈ Icc %s %s)' % (HYP[a], a, lean_num(atom_iv[a][0]), lean_num(atom_iv[a][1])) for a in d.atoms)
        text.append('theorem %s_%s {%s : ℝ}\n%s :\n    %s ∈ Icc %s %s := by' % (name, regime, ' '.join(d.atoms), hyps, d.call(), lean_num(lo), lean_num(hi)))
        for l in em.lines:
            text.append('  ' + l)
        text.append('  exact %s' % h)
        text.append('')
    return results, '\n'.join(text)

# ---------------------------------------------------------------- definitions text
def gen_defs(names):
    out = []
    for n in names:
        d = DEFS[n]
        out.append('/-- %s -/' % (d.doc[0].upper() + d.doc[1:] + '.'))
        out.append('noncomputable def %s (%s : ℝ) : ℝ :=\n  %s' % (n, ' '.join(d.atoms), d.expr.lean()))
        out.append('')
    return '\n'.join(out)

# ---------------------------------------------------------------- derivative proofs
def deriv_term(e, v):
    """Lean term proving HasDerivAt (fun t => e) e' t, moving variable v in {'φ','θ'};
    the moving variable is called `t` in the lambda and the other one is fixed."""
    if v == 'φ':
        mov = {'φ': 'hasDerivAt_id\' x', 'c': 'Real.hasDerivAt_cos x', 's': 'Real.hasDerivAt_sin x'}
        val = {'φ': 'x', 'θ': 'y', 'c': '(cos x)', 's': '(sin x)', 'C': '(cos y)', 'S': '(sin y)', 'p': 'π'}
        pt = 'x'
    else:
        mov = {'θ': 'hasDerivAt_id\' y', 'C': 'Real.hasDerivAt_cos y', 'S': 'Real.hasDerivAt_sin y'}
        val = {'φ': 'x', 'θ': 'y', 'c': '(cos x)', 's': '(sin x)', 'C': '(cos y)', 'S': '(sin y)', 'p': 'π'}
        pt = 'y'
    def go(e):
        if isinstance(e, Var):
            if e.name in mov: return '(' + mov[e.name] + ')'
            return '(hasDerivAt_const %s %s)' % (pt, val[e.name])
        if isinstance(e, Num):
            return '(hasDerivAt_const %s (%s : ℝ))' % (pt, e.s)
        if isinstance(e, Ref):
            d = DEFS[e.name]
            movatoms = {'φ': {'φ', 'c', 's'}, 'θ': {'θ', 'C', 'S'}}[v]
            if not (set(d.atoms) & movatoms):
                return '(hasDerivAt_const %s (%s))' % (pt, d.call(val))
            return '(%s_hasDerivAt_%s x y)' % (e.name, v)
        if isinstance(e, Neg):
            return '(%s.fun_neg)' % go(e.a)
        if e.op == '/' and isinstance(e.b, Num):
            return '(%s.div_const (%s : ℝ))' % (go(e.a), e.b.s)
        op = {'+': 'fun_add', '-': 'fun_sub', '*': 'fun_mul'}[e.op]
        return '(%s.%s %s)' % (go(e.a), op, go(e.b))
    return go(e)

def gen_deriv(names):
    out = []
    val = {'φ': 'x', 'θ': 'y', 'c': '(cos x)', 's': '(sin x)', 'C': '(cos y)', 'S': '(sin y)', 'p': 'π'}
    for n in names:
        d = DEFS[n]
        for v in ['φ', 'θ']:
            movatoms = {'φ': {'φ', 'c', 's'}, 'θ': {'θ', 'C', 'S'}}[v]
            if not (set(d.atoms) & movatoms):
                continue
            dd = DEFS[n + v]
            pt = 'x' if v == 'φ' else 'y'
            valt = dict(val)
            if v == 'φ':
                valt.update({'φ': 't', 'c': '(cos t)', 's': '(sin t)'})
            else:
                valt.update({'θ': 't', 'C': '(cos t)', 'S': '(sin t)'})
            stmt = 'HasDerivAt (fun t => %s) (%s) %s' % (d.call(valt), dd.call(val), pt)
            import re
            xs = 'x' if re.search(r'\bx\b', stmt) else '_x'
            ys = 'y' if re.search(r'\by\b', stmt) else '_y'
            out.append('theorem %s_hasDerivAt_%s (%s %s : ℝ) :\n    %s := by' % (n, v, xs, ys, stmt))
            out.append('  refine HasDerivAt.congr_deriv %s ?_' % deriv_term(d.expr, v))
            extra = ', rom_Kθ' if (v == 'θ' and 'rom_K' in d.expr.refs()) else ''
            out.append('  simp only [%s%s]' % (n + v, extra))
            out.append('  ring')
            out.append('')
    return '\n'.join(out)

if __name__ == '__main__':
    check_partials()

def wrap_line(line, width=100):
    if len(line) <= width:
        return [line]
    import re
    indent = len(line) - len(line.lstrip(' '))
    body = line.strip(' ')
    # protect the spaces inside short parenthesised groups such as `(2 : ℝ)` or `(cos x)`
    body = re.sub(r'\([^()]{0,26}\)', lambda m: m.group(0).replace(' ', '\x00'), body)
    body = body.replace(' :=', '\x00:=')
    words = body.split(' ')
    out = []
    cur = ' ' * indent + words[0]
    cont = ' ' * (indent + 4)
    for w in words[1:]:
        if len(cur) + 1 + len(w) <= width:
            cur += ' ' + w
        else:
            out.append(cur)
            cur = cont + w
    out.append(cur)
    return [l.replace('\x00', ' ') for l in out]

def wrap_text(text, width=100):
    res = []
    for l in text.split('\n'):
        res.extend(wrap_line(l, width))
    return '\n'.join(res)
