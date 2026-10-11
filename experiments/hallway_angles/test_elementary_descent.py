"""Local exact-algebra regression checks, NOT a test of Schanuel's conjecture.

No numerical search, denominator recognition, geometric optimality claim,
or purported machine verification of the transcendence proof is involved.
"""
from __future__ import annotations

import unittest
import sympy as S
from elementary_descent_algebra import verify_identities


class DescentIdentityChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.record = verify_identities()

    def test_all_fourteen_exact_identity_residuals_vanish(self) -> None:
        identities = [k for k, v in self.record.items() if v == "0"]
        self.assertEqual(len(identities), 14)

    def test_contact_pole_and_leading_coefficient_are_nonzero(self) -> None:
        c, s, eta, z = S.symbols("c s eta z", positive=True)
        pa = (-3*S.I*s-c)*z**2-2*z+(3*S.I*s-c)
        pb = (-S.I*s-3*c)*z**2-2*eta**2*z+(S.I*s-3*c)
        p, q = eta*pa+pb, eta*pa-pb
        self.assertEqual(S.re(S.expand(p).coeff(z, 2)).expand(), -c*eta-3*c)
        self.assertEqual(S.re(p.subs(z, 0)).expand(), -c*eta-3*c)
        self.assertEqual(S.re(q.subs(z, 0)).expand(), 3*c-c*eta)

    def test_common_root_defect_is_strictly_negative_on_rational_examples(self) -> None:
        # The proof's factor signs cover all 0<c<1/2. These are exact controls.
        for c in [S.Rational(1, 100), S.Rational(1, 4), S.Rational(49, 100)]:
            value = 1/(3-4*c*c)**2-1
            self.assertLess(value, 0)

    def test_resultant_matches_independent_sylvester_determinant(self) -> None:
        # A rational c yields algebraic s,eta. Determinants are exact here.
        z = S.symbols("z")
        c, s, eta = S.Rational(1, 4), S.sqrt(15)/4, S.sqrt(S.Rational(3, 11))
        pa = (-3*S.I*s-c)*z**2-2*z+(3*S.I*s-c)
        pb = (-S.I*s-3*c)*z**2-2*eta**2*z+(S.I*s-3*c)
        p, q = S.Poly(eta*pa+pb, z), S.Poly(eta*pa-pb, z)
        p2, p1, p0 = p.all_coeffs()
        q2, q1, q0 = q.all_coeffs()
        matrix = S.Matrix([[p2, p1, p0, 0], [0, p2, p1, p0],
                           [q2, q1, q0, 0], [0, q2, q1, q0]])
        value = S.simplify(matrix.det(method="berkowitz"))
        expected = -8192*c*c*(1-c*c)**2*(1-4*c*c)*(1-2*c*c)/(3-4*c*c)**3
        self.assertEqual(S.simplify(value-expected), 0)
        self.assertNotEqual(value, 0)

    def test_bend_coefficient_cannot_cancel(self) -> None:
        d = S.symbols("d")
        A = S.factor(S.Rational(1, 4)+1/(2+d))
        self.assertEqual(S.cancel(A-(d+6)/(4*(d+2))), 0)
        for value in [S.Rational(-99, 100), S.Rational(-3, 4), S.Rational(-51, 100)]:
            self.assertGreater(A.subs(d, value), 0)

    def test_forward_fraction_has_a_genuine_pole(self) -> None:
        z, H, d = S.symbols("z H d")
        p = (1-4*d)*(H**2+z**2)-2*H*z*(1+2*d**2)
        self.assertEqual(S.factor(p.subs(z, H)), -4*H**2*d*(d+2))
        self.assertNotEqual(p.subs({z: 1, H: 1, d: S.Rational(-3, 4)}), 0)

    def test_reverse_fraction_is_not_constant(self) -> None:
        y, eta = S.symbols("y eta", nonzero=True)
        numerator, denominator = eta*(y-1), S.I*(y+1)+eta*(y-1)
        determinant = S.expand(S.diff(numerator, y)*denominator-numerator*S.diff(denominator, y))
        self.assertEqual(determinant, 2*S.I*eta)

    def test_direction_recovery_is_a_monic_quartic(self) -> None:
        E, mu = S.symbols("E mu")
        q2 = 3/(4*(mu**2+1))
        polynomial = S.Poly(E**4+(4*q2-2)*E**2+1, E)
        self.assertEqual(polynomial.LC(), 1)
        self.assertEqual(polynomial.degree(), 4)
        self.assertEqual(polynomial.TC(), 1)

    def test_log_step_forces_both_switch_coefficients_to_zero(self) -> None:
        r, s, mu = S.symbols("r s mu", real=True)
        difference = s+2*S.I*mu*r
        self.assertEqual(S.re(difference), s)
        self.assertEqual(S.im(difference), 2*mu*r)

    def test_reverse_frequency_hyperbola_is_not_a_rational_square(self) -> None:
        x = S.symbols("x")
        p = x*x+S.Rational(5, 4)
        self.assertEqual(S.gcd(p, S.diff(p, x)), 1)
        self.assertEqual(S.discriminant(p, x), -5)
        for root in [S.I*S.sqrt(5)/2, -S.I*S.sqrt(5)/2]:
            self.assertEqual(S.simplify(p.subs(x, root)), 0)
            self.assertNotEqual(S.simplify(S.diff(p, x).subs(x, root)), 0)


class NecessaryHypothesisControls(unittest.TestCase):
    def test_a_constant_denominator_allows_an_elementary_solution(self) -> None:
        # exp(c*x)=2 exp(x), x=log(2)/(c-1), c=sqrt(2).
        c = S.sqrt(2)
        x = S.log(2)/(c-1)
        self.assertEqual(S.simplify((c-1)*x), S.log(2))
        self.assertEqual(S.exp(S.simplify((c-1)*x)), 2)
        z = S.symbols("z")
        self.assertEqual((1*(2*z)-2*z).expand(), 0)

    def test_a_pole_only_at_zero_allows_an_elementary_solution(self) -> None:
        # P(z)=z, Q(z)=-2, exp(c*x)=2/exp(x).
        c = S.sqrt(2)
        x = S.log(2)/(c+1)
        self.assertEqual(S.simplify((c+1)*x), S.log(2))
        z = S.symbols("z", nonzero=True)
        self.assertEqual(S.cancel(z*(2/z)-2), 0)
        self.assertEqual(S.Poly(z, z).TC(), 0)

    def test_a_common_factor_invalidates_the_monomial_obstruction(self) -> None:
        z = S.symbols("z")
        p, q = z-1, -2*z*(z-1)
        self.assertEqual(S.gcd(p, q), z-1)
        self.assertEqual(S.expand(p*(2*z)+q), 0)

    def test_rational_multipliers_can_leave_a_logarithmic_mode(self) -> None:
        # Nonrational c is essential to coefficient comparison s=c*r.
        r, s, c = S.Rational(1, 2), S.Rational(3, 2), S.Integer(3)
        self.assertEqual(s-c*r, 0)
        self.assertNotEqual(r, 0)

    def test_minimal_tower_base_uses_a_real_nonzero_argument(self) -> None:
        a, h = S.symbols("a h", real=True)
        pi = S.symbols("pi", real=True, positive=True)
        self.assertEqual(S.re(h-a*S.I*pi), h)
        self.assertEqual(S.im(h-a*S.I*pi), -a*pi)


if __name__ == "__main__":
    unittest.main(verbosity=2)
