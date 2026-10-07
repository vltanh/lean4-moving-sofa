"""Regression checks for EXACT_CONTACT_CROSSING.md, not a global sofa proof.

Requires the mpmath version in requirements-round6.txt. The long reference
expression is independently transcribed from FORWARD_CONTACT_MODEL.md.
The reduced area agrees with it on the matching locus, not off that locus.
No root-isolation or geometric-optimality claim is inferred from these tests.
"""
from fractions import Fraction as Q
import unittest
import mpmath as mp


def original(beta, T):
    d, s, c = mp.cos(beta), mp.sin(beta/2), mp.cos(beta/2)
    mu = mp.sqrt(3/(4*mp.sin(beta)**2)-1)
    eta = mp.sqrt((-1-2*d)/(1-2*d))
    r = (1-2*d)/(2*(1+d)*mu)
    z0 = -2*c/(1+2*d)
    A = mp.mpf(1)/3
    B = -2*c/(3*mu*(mp.cosh(mu*T)+eta*mp.sinh(mu*T)))
    F = (eta*(3*s*mp.sin(T)-c*mp.cos(T)-1)
         +mp.tanh(mu*T)*(s*mp.sin(T)-3*c*mp.cos(T)-eta**2))
    zx = A*mp.sin(T)+B*mp.sinh(mu*T)
    zy = A*mp.cos(T)+r*B*mp.cosh(mu*T)+z0
    dx = A*mp.cos(T)+mu*B*mp.cosh(mu*T)
    dy = -A*mp.sin(T)+r*mu*B*mp.sinh(mu*T)
    alpha = beta/2-T
    p = (s*zx+c*zy+(1-mp.cos(alpha))/2)/mp.sin(alpha)
    g = p*mp.sin(alpha)+mp.cos(alpha)/2
    gp = p*mp.cos(alpha)-mp.sin(alpha)/2
    f, fp = -s*zx+c*zy, -s*dx+c*dy
    W = (alpha/2-2*g*gp+p+2*T
         +2*c*(A*mp.sin(T)+r*B*mp.sinh(mu*T)/mu+z0*T)
         -2*((1-d)*zx*dx+(1+d)*zy*dy)+2*(f+mp.mpf('0.5'))*fp)
    return F, W


def reduced_contact(beta, alpha):
    d = mp.cos(beta)
    mu = mp.sqrt(3/(4*mp.sin(beta)**2)-1)
    eta = mp.sqrt((-1-2*d)/(1-2*d))
    return ((mp.cos(alpha)+2*mp.cos(beta-alpha)+eta**2)
            *mp.tanh(mu*(beta/2-alpha))
            -eta*(mp.cos(alpha)-2*mp.cos(beta-alpha)-1))


def reduced_area(beta, alpha):
    d = mp.cos(beta)
    return (d*beta+(1-2*d)*alpha/2-mp.sin(beta)
            +((1-4*d)*mp.cos(alpha)-(1+2*d*d))/(3*mp.sin(alpha)))/(1+2*d)


class ExactContactReductionTests(unittest.TestCase):
    def test_contact_equation_is_negative_of_original(self):
        with mp.workdps(80):
            for degree in (135, 137, 140):
                beta = mp.mpf(degree)*mp.pi/180
                for T in (mp.mpf('.65'), mp.mpf('.70'), mp.mpf('.75')):
                    F, _ = original(beta, T)
                    self.assertLess(abs(F+reduced_contact(beta, beta/2-T)), mp.mpf('1e-70'))

    def test_area_identity_on_matching_branch(self):
        with mp.workdps(80):
            for j in range(11):
                beta = (mp.mpf(135)+mp.mpf(j)/2)*mp.pi/180
                T = mp.findroot(lambda t: original(beta, t)[0], (mp.mpf('.65'), mp.mpf('.75')))
                F, W = original(beta, T)
                self.assertLess(abs(F), mp.mpf('1e-70'))
                self.assertLess(abs(W-reduced_area(beta, beta/2-T)), mp.mpf('1e-65'))

    def test_off_branch_replacement_is_invalid(self):
        with mp.workdps(80):
            beta, T = mp.mpf(137)*mp.pi/180, mp.mpf('.7')
            F, W = original(beta, T)
            self.assertGreater(abs(F), mp.mpf('.01'))
            self.assertGreater(abs(W-reduced_area(beta, beta/2-T)), mp.mpf('.03'))

    def test_eliminated_rational_identity_exactly(self):
        # Rational half-angle substitution gives exact sine/cosine values.
        # These exact cases supplement, not replace, the analytic identity.
        for v in (Q(2,3), Q(7,10), Q(3,4), Q(4,5)):
            s, c = 2*v/(1+v*v), (1-v*v)/(1+v*v)
            E2 = (1-4*c*c)/(3-4*c*c)
            d = 2*c*c-1
            for u in (Q(1,3), Q(7,20), Q(2,5)):
                a, b = 2*u/(1+u*u), (1-u*u)/(1+u*u)
                sa, ca = s*b-c*a, c*b+s*a
                H = -(3*s*a-c*b-1)/(s*a-3*c*b-E2)
                p = (sa/6+2*s*c*(1+H)/(3*(1+E2*H)))/ca
                N = p-4*s*c*H/((3-4*c*c)*(1-4*c*c)*(1+E2*H))
                compact = (((1-4*d)*ca-(1+2*d*d))/(3*sa)-2*s*c)/(1+2*d)
                self.assertEqual(N, compact)

    def test_linear_angle_terms_reduce_exactly(self):
        for d in (Q(-7,10), Q(-3,4), Q(-4,5)):
            eta2 = (-1-2*d)/(1-2*d)
            for beta, alpha in ((Q(12,5),Q(1,2)), (Q(7,3),Q(3,5))):
                T = beta/2-alpha
                self.assertEqual(beta/4+T/(2*eta2),
                                 (d*beta+(1-2*d)*alpha/2)/(1+2*d))


if __name__ == '__main__':
    unittest.main(verbosity=2)
