"""High-precision exact interval evaluation for deep rational-angle exclusion.

This is a standalone 192-bit version of the contact-model scalar checker.
It uses exact integers/Fractions, Machin bounds for pi, Taylor enclosures,
and interval Newton for the contact parameter. No floating-point arithmetic,
optimizer, NumPy, or polygon library enters the proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt
import json

BITS = 192
SCALE = 1 << BITS


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @classmethod
    def rational(cls, value):
        q = Fraction(value)
        return cls(q.numerator*SCALE//q.denominator,
                   ceil_div(q.numerator*SCALE, q.denominator))

    @staticmethod
    def coerce(value):
        if isinstance(value, Interval):
            return value
        if isinstance(value, (int, Fraction)):
            return Interval.rational(value)
        raise TypeError(type(value))

    def __add__(self, other):
        b = self.coerce(other)
        return Interval(self.lo+b.lo, self.hi+b.hi)
    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        b = self.coerce(other)
        p = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Interval(min(p)//SCALE, ceil_div(max(p), SCALE))
    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.coerce(other)
        if b.lo <= 0 <= b.hi:
            raise ZeroDivisionError
        nums = (self.lo*SCALE, self.hi*SCALE)
        floor = [n//d for n in nums for d in (b.lo, b.hi)]
        ceil = [ceil_div(n, d) for n in nums for d in (b.lo, b.hi)]
        return Interval(min(floor), max(ceil))

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        high = max(self.lo*self.lo, self.hi*self.hi)
        return Interval(low//SCALE, ceil_div(high, SCALE))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("negative square-root interval")
        lo = isqrt(self.lo*SCALE)
        hi = isqrt(self.hi*SCALE)
        if hi*hi < self.hi*SCALE:
            hi += 1
        return Interval(lo, hi)


def atan_reciprocal_bounds(n: int, terms: int = 200):
    total = sum((Fraction((-1)**j, (2*j+1)*n**(2*j+1)) for j in range(terms)), Fraction(0))
    nxt = Fraction((-1)**terms, (2*terms+1)*n**(2*terms+1))
    return min(total, total+nxt), max(total, total+nxt)


def pi_interval():
    a0, a1 = atan_reciprocal_bounds(5)
    b0, b1 = atan_reciprocal_bounds(239)
    lo, hi = 16*a0-4*b1, 16*a1-4*b0
    return Interval(Interval.rational(lo).lo, Interval.rational(hi).hi)


def _sin_cos_small(x: Interval):
    # All callers reduce to |x|<=1. Degree 141/140 leaves remainder <2^-192.
    n = 70
    if Fraction(1, factorial(2*n+2)) >= Fraction(1, SCALE):
        raise ArithmeticError("Taylor remainder too large")
    xx = x.square()
    ps = Interval.rational(Fraction((-1)**n, factorial(2*n+1)))
    pc = Interval.rational(Fraction((-1)**n, factorial(2*n)))
    for j in range(n-1, -1, -1):
        ps = ps*xx + Interval.rational(Fraction((-1)**j, factorial(2*j+1)))
        pc = pc*xx + Interval.rational(Fraction((-1)**j, factorial(2*j)))
    return x*ps + Interval(-1, 1), pc + Interval(-1, 1)


def sin_cos(x: Interval):
    if max(abs(x.lo), abs(x.hi)) > 4*SCALE:
        raise ValueError("trig argument outside [-4,4]")
    s, c = _sin_cos_small(x/4)
    for _ in range(2):
        s, c = 2*s*c, c.square()-s.square()
    return s, c


def sinh_cosh(x: Interval):
    # Relevant arguments have absolute value below one.
    if max(abs(x.lo), abs(x.hi)) > SCALE:
        raise ValueError("hyperbolic argument outside [-1,1]")
    n = 70
    xx = x.square()
    ps = Interval.rational(Fraction(1, factorial(2*n+1)))
    pc = Interval.rational(Fraction(1, factorial(2*n)))
    for j in range(n-1, -1, -1):
        ps = ps*xx + Interval.rational(Fraction(1, factorial(2*j+1)))
        pc = pc*xx + Interval.rational(Fraction(1, factorial(2*j)))
    return x*ps + Interval(-1, 1), pc + Interval(-1, 1)


ZERO = Interval.rational(0)


@dataclass(frozen=True)
class Jet:
    v: Interval
    db: Interval = ZERO
    dt: Interval = ZERO

    @staticmethod
    def cast(value):
        if isinstance(value, Jet):
            return value
        if isinstance(value, Interval):
            return Jet(value)
        return Jet(Interval.rational(value))

    def __add__(self, other):
        b = self.cast(other)
        return Jet(self.v+b.v, self.db+b.db, self.dt+b.dt)
    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.db, -self.dt)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) + (-self)

    def __mul__(self, other):
        b = self.cast(other)
        return Jet(self.v*b.v,
                   self.db*b.v+self.v*b.db,
                   self.dt*b.v+self.v*b.dt)
    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.cast(other)
        den = b.v.square()
        return Jet(self.v/b.v,
                   (self.db*b.v-self.v*b.db)/den,
                   (self.dt*b.v-self.v*b.dt)/den)

    def __rtruediv__(self, other):
        return self.cast(other)/self

    def square(self):
        return Jet(self.v.square(), 2*self.v*self.db, 2*self.v*self.dt)

    def sqrt(self):
        r = self.v.sqrt()
        return Jet(r, self.db/(2*r), self.dt/(2*r))


def trig(x: Jet):
    s, c = sin_cos(x.v)
    return Jet(s, c*x.db, c*x.dt), Jet(c, -s*x.db, -s*x.dt)


def hyper(x: Jet):
    s, c = sinh_cosh(x.v)
    return Jet(s, c*x.db, c*x.dt), Jet(c, s*x.db, s*x.dt)


def model(beta: Jet, T: Jet, pi: Interval):
    q, d = trig(beta)
    s, c = trig(beta/2)
    st, ct = trig(T)
    mu = (3/(4*q.square())-1).sqrt()
    eta = ((-1-2*d)/(1-2*d)).sqrt()
    sh, ch = hyper(mu*T)
    r = (1-2*d)/(2*(1+d)*mu)
    z0 = -2*c/(1+2*d)
    B = -2*c/(3*mu*(ch+eta*sh))
    A = Jet.cast(Fraction(1, 3))
    residual = eta*(3*s*st-c*ct-1) + (sh/ch)*(s*st-3*c*ct-eta.square())

    zx, zy = A*st+B*sh, A*ct+r*B*ch+z0
    dx, dy = A*ct+mu*B*ch, -A*st+r*mu*B*sh
    alpha = beta/2-T
    sa, ca = trig(alpha)
    p = (s*zx+c*zy+(1-ca)/2)/sa
    g, gp = p*sa+ca/2, p*ca-sa/2
    f, fp = -s*zx+c*zy, -s*dx+c*dy
    W = (alpha/2-2*g*gp+p+2*T
         +2*c*(A*st+r*B*sh/mu+z0*T)
         -2*((1-d)*zx*dx+(1+d)*zy*dy)
         +2*(f+Fraction(1,2))*fp)

    e = Jet.cast(pi)-beta
    qr, dr = trig(e)
    mr = 2-dr
    etar = (mr/(2+dr)).sqrt()
    Kr = e*(1+3/qr.square()).sqrt()/2
    skr, ckr = trig(Kr)
    R = etar*skr/(ckr+etar*skr)
    V = e/mr+(1+2*dr)/(4*qr)+3*dr.square()*R/(2*qr*mr.square())
    return residual, W-V


def interval(lo, hi):
    return Interval(Interval.rational(lo).lo, Interval.rational(hi).hi)


def at(beta, T, pi):
    return model(Jet(beta, Interval.rational(1), ZERO),
                 Jet(T, ZERO, Interval.rational(1)), pi)


def isolate_T(beta: Interval, pi: Interval):
    lo, hi = Fraction(65,100), Fraction(75,100)
    for _ in range(300):
        mid = (lo+hi)/2
        value = at(beta, Interval.rational(mid), pi)[0].v
        if value.hi < 0:
            lo = mid
            continue
        if value.lo > 0:
            hi = mid
            continue
        derivative = at(beta, interval(lo, hi), pi)[0].dt
        if derivative.lo <= 0:
            raise ArithmeticError("interval Newton derivative not positive")
        newton = Interval.rational(mid)-value/derivative
        new_lo = max(lo, Fraction(newton.lo, SCALE))
        new_hi = min(hi, Fraction(newton.hi, SCALE))
        if not new_lo < new_hi:
            raise ArithmeticError("empty interval-Newton enclosure")
        if new_hi-new_lo >= Fraction(99,100)*(hi-lo):
            break
        lo, hi = new_lo, new_hi
        if hi-lo < Fraction(1, 1 << 170):
            break
    return interval(lo, hi)


def gap_at_ratio(ratio: Fraction):
    pi = pi_interval()
    beta = pi*Interval.rational(ratio)
    T = isolate_T(beta, pi)
    gap = at(beta, T, pi)[1].v
    return Fraction(gap.lo, SCALE), Fraction(gap.hi, SCALE)


LOWER = Fraction(504644407557908571, 664626775090067219)
UPPER = Fraction(1920149641230808118, 2528875470784124371)


def prove():
    gl0, gl1 = gap_at_ratio(LOWER)
    gu0, gu1 = gap_at_ratio(UPPER)
    if gl0 <= 0 or gu1 >= 0:
        raise ArithmeticError("signs do not bracket the unique crossing")
    determinant = UPPER.numerator*LOWER.denominator - LOWER.numerator*UPPER.denominator
    if determinant != 1:
        raise ArithmeticError("fractions are not Farey neighbours")
    return {
        "format": "deep-rational-exclusion-v1",
        "precision_bits": BITS,
        "lower": str(LOWER),
        "upper": str(UPPER),
        "lower_gap": [str(gl0), str(gl1)],
        "upper_gap": [str(gu0), str(gu1)],
        "farey_determinant": determinant,
        "minimum_denominator": LOWER.denominator+UPPER.denominator,
        "conclusion": "if beta_model/pi=p/q in lowest terms then q>=3193502245874191590",
        "scope": "contact-model crossing only; not the unrestricted global transition",
    }


if __name__ == "__main__":
    print(json.dumps(prove(), indent=2))
