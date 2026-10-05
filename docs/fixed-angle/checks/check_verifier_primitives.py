"""Exact-rational regression checks; not a substitute for certificate replay."""
from fractions import Fraction as F
from itertools import product
from interval_contact import I, PI, HALF_PI
from jet_contact import Jet
from contact_core import step


def contains(interval, number):
    number = F(number)
    if not (F.from_float(interval.lo) <= number <= F.from_float(interval.hi)):
        raise ArithmeticError(("Failed exact inclusion", interval, number))


def main():
    cases = [(-2., -1.), (-1., 0.), (-.25, .5), (0., 0.), (0., 1.), (.5, 1.5), (1., 2.)]
    tests = 0
    for (a,b),(c,d) in product(cases, repeat=2):
        xx, yy = I(a,b), I(c,d)
        contains(xx+yy, F(a)+F(c)); contains(xx+yy, F(b)+F(d))
        for x,y in product((a,b),(c,d)):
            contains(xx*yy, F(x)*F(y))
        if not c <= 0 <= d:
            for x,y in product((a,b),(c,d)):
                contains(xx/yy, F(x)/F(y))
        tests += 1
    for n in range(-20,21):
        for d in range(1,41):
            contains(I.exact_rational(n,d), F(n,d))
    contains(I(0).sin(),0); contains(I(0).cos(),1)
    contains(HALF_PI.sin(),1); contains(HALF_PI.cos(),0)
    if not F.from_float(PI.hi) < F(3927,1250):
        raise ArithmeticError('The endpoint rational pi bound was not verified')

    # This catches accidental loss of the second-derivative class when
    # an interval is the left operand of division by a Jet.
    x=Jet(I(2),[1,0,0,0]); z=I(1)/x
    if not isinstance(z,Jet):
        raise ArithmeticError('Mixed reciprocal discarded the Hessian')
    contains(z.val,F(1,2)); contains(z.grad[0],F(-1,4)); contains(z.hess[0][0],F(1,4))

    # All eight coefficient pieces must match the ODE through second order
    # at their initial time. The paper derives their full elementary flows.
    f,g,p,v=F(5,4),F(7,4),F(3,2),F(-1,4)
    t=Jet(I(0),[1,0,0,0])
    for C,B,D in product((0,1),repeat=3):
        state=tuple(Jet(I.exact_rational(z.numerator,z.denominator)) for z in (f,g,p,v))
        result=step(state,t,(C,B,D))
        rp=(C*(g-1)+B)/(1+B); rk=(C*(f-1)+D)/(1+D)
        df,dg=g-rp,rk-f
        first=(df,dg,v,rp-p)
        second=((1-F(C,1+B))*dg,(-1+F(C,1+D))*df,rp-p,F(C,1+B)*dg-v)
        for actual,initial,d1,d2 in zip(result,(f,g,p,v),first,second):
            contains(actual.val,initial);contains(actual.grad[0],d1);contains(actual.hess[0][0],d2)
    print(f'Passed {tests} interval-pair cases, 1640 rational conversions, mixed Hessian division, and all eight flow pieces.')


if __name__=='__main__':
    main()
