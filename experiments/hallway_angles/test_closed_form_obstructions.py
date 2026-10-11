"""Checks of symbolic identities and numerical recognition, not transcendence proofs.

Gelfond-Schneider/Lindemann-Weierstrass are invoked mathematically in
CONTACT_TRANSCENDENCE.md; passing these tests does not formalize them.
"""
from __future__ import annotations
import unittest
import mpmath as mp
import sympy as sp
from closed_form_search import equations, solve, run


class SymbolicChecks(unittest.TestCase):
    def setUp(self):
        self.z,self.w,self.s,self.c,self.h=sp.symbols('z w s c h')
        z,s,c,h=self.z,self.s,self.c,self.h
        self.a=(-3*sp.I*s-c)*z**2-2*z+(3*sp.I*s-c)
        self.b=(-sp.I*s-3*c)*z**2-2*h*h*z+(sp.I*s-3*c)
        self.P=sp.expand(h*self.a+self.b)
        self.Q=sp.expand(h*self.a-self.b)

    def test_exponential_normal_form_identically(self):
        z,w,s,c,h=self.z,self.w,self.s,self.c,self.h
        st=(z-1/z)/(2*sp.I);ct=(z+1/z)/2
        f=h*(3*s*st-c*ct-1)+(w-1)/(w+1)*(s*st-3*c*ct-h*h)
        self.assertEqual(sp.cancel(2*z*(w+1)*f-self.P*w-self.Q),0)

    def test_common_root_contradiction_symbolically(self):
        c=self.c
        E=(1-4*c*c)/(3-4*c*c)
        # Solve for X=s*sin(T), Y=c*cos(T) without radicals.
        X=(3-E)/8;Y=(1-3*E)/8
        self.assertEqual(sp.cancel(X-(1-c*c)/(3-4*c*c)),0)
        self.assertEqual(sp.cancel(Y-c*c/(3-4*c*c)),0)
        norm=X*X/(1-c*c)+Y*Y/(c*c)
        self.assertEqual(sp.cancel(norm-1/(3-4*c*c)**2),0)

    def test_exact_nonzero_resultant(self):
        z,s,c,h=self.z,self.s,self.c,self.h
        result=sp.resultant(self.P,self.Q,z)
        # The resultant is even in s and h: replace their squares exactly.
        result=sp.Poly(result,s).rem(sp.Poly(s*s+c*c-1,s)).as_expr()
        E=(1-4*c*c)/(3-4*c*c)
        result=sp.Poly(result,h).rem(sp.Poly(h*h-E,h)).as_expr()
        target=8192*c*c*(c*c-1)**2*(4*c*c-1)*(2*c*c-1)/(4*c*c-3)**3
        self.assertEqual(sp.cancel(result-target),0)
        for cv in (sp.Rational(1,4),sp.Rational(1,3),sp.Rational(2,5)):
            self.assertNotEqual(sp.cancel(result.subs(c,cv)),0)

    def test_six_exponential_coefficients_are_not_all_zero(self):
        z=self.z;h=self.h
        self.assertEqual(sp.expand(sp.Poly(self.P,z).coeff_monomial(z)+2*h*(h+1)),0)
        self.assertEqual(sp.expand(sp.Poly(self.Q,z).coeff_monomial(z)-2*h*(h-1)),0)
        self.assertEqual(sp.Poly(self.P,z).degree(),2)
        self.assertEqual(sp.Poly(self.Q,z).degree(),2)

    def test_monodromy_factor(self):
        mu,L=sp.symbols('mu L')
        difference=sp.expand((-2*sp.I*mu)*(L+2*sp.pi*sp.I)-(-2*sp.I*mu)*L)
        self.assertEqual(difference,4*sp.pi*mu)


class NumericalChecks(unittest.TestCase):
    def test_independent_precision_root_check(self):
        p=solve(100);q=solve(160)
        with mp.workdps(90):
            self.assertLess(max(abs(a-b) for a,b in zip(p,q)),mp.mpf('1e-85'))
            self.assertLess(max(abs(x) for x in equations(*q)),mp.mpf('1e-85'))

    def test_exponential_relation_off_and_on_branch(self):
        with mp.workdps(90):
            for deg in (135,137,140):
                beta=mp.mpf(deg)*mp.pi/180
                s,c=mp.sin(beta/2),mp.cos(beta/2)
                eta=mp.sqrt((1-4*c*c)/(3-4*c*c));mu=mp.sqrt(3/(4*mp.sin(beta)**2)-1)
                for T in (mp.mpf('.66'),mp.mpf('.70'),mp.mpf('.74')):
                    z=mp.exp(1j*T);w=mp.exp(2*mu*T)
                    a=(-3j*s-c)*z*z-2*z+(3j*s-c)
                    b=(-1j*s-3*c)*z*z-2*eta*eta*z+(1j*s-3*c)
                    f=eta*(3*s*mp.sin(T)-c*mp.cos(T)-1)+mp.tanh(mu*T)*(s*mp.sin(T)-3*c*mp.cos(T)-eta*eta)
                    self.assertLess(abs((eta*a+b)*w+(eta*a-b)-2*z*(w+1)*f),mp.mpf('1e-80'))

    def test_no_denominator_cancellation_at_contact_root(self):
        with mp.workdps(90):
            beta=3*mp.pi/4
            alpha=mp.findroot(lambda a:equations(beta,a)[0],mp.mpf('.49'))
            T=beta/2-alpha
            self.assertTrue(mp.mpf('.65')<T<mp.mpf('.75'))
            self.assertLess(abs(equations(beta,alpha)[0]),mp.mpf('1e-80'))
            s,c=mp.sin(beta/2),mp.cos(beta/2)
            eta=mp.sqrt((1-4*c*c)/(3-4*c*c));mu=mp.sqrt(3/(4*mp.sin(beta)**2)-1)
            z=mp.exp(1j*T)
            a=(-3j*s-c)*z*z-2*z+(3j*s-c)
            b=(-1j*s-3*c)*z*z-2*eta*eta*z+(1j*s-3*c)
            P=eta*a+b;Q=eta*a-b
            self.assertGreater(abs(P),mp.mpf('.01'))
            self.assertLess(abs(-Q/P-mp.exp(2*mu*T)),mp.mpf('1e-80'))
            # beta has a closed form despite the conditional transcendence
            # theorem for its switching data. Never infer the converse.
            self.assertEqual(beta/mp.pi,mp.mpf(3)/4)

    def test_known_polynomial_recognized(self):
        with mp.workdps(100):
            x=mp.sqrt(2)
            r=mp.pslq(mp.matrix([1,x,x*x]),tol=mp.mpf('1e-80'),maxcoeff=100,maxsteps=1000)
            self.assertIsNotNone(r)
            self.assertEqual(r[1],0)
            self.assertEqual(r[0]+2*r[2],0)

    def test_known_elementary_linear_combination_recognized(self):
        with mp.workdps(100):
            x=mp.pi/2+mp.sqrt(2)-mp.log(2)
            vals=mp.matrix([x,mp.pi,mp.sqrt(2),mp.log(2)])
            r=mp.pslq(vals,tol=mp.mpf('1e-80'),maxcoeff=100,maxsteps=1000)
            self.assertIsNotNone(r)
            self.assertNotEqual(r[0],0)
            self.assertLess(abs(sum(a*b for a,b in zip(r,vals))),mp.mpf('1e-80'))

    def test_search_input_validation(self):
        for kwargs in ({'precision':70},{'degree':0},{'degree':17},{'height':1},{'maxsteps':0}):
            with self.assertRaises(ValueError):run(**kwargs)


if __name__=='__main__':unittest.main(verbosity=2)
