"""Exact symbolic checks for SCHANUEL_NON_ELEMENTARITY.md.

This verifies rational identities and records nonzero factors used by the
proof. It does not verify Schanuel's conjecture, the field-theoretic argument,
or any geometric interpretation of the contact model. No root search is used.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sympy as S


def verify_identities() -> dict[str, str]:
    """Raise on an algebraic mismatch; return the exact checked expressions."""
    z, w, s, c, eta = S.symbols("z w s c eta")
    st, ct = (z-1/z)/(2*S.I), (z+1/z)/2
    pa = (-3*S.I*s-c)*z**2-2*z+(3*S.I*s-c)
    pb = (-S.I*s-3*c)*z**2-2*eta**2*z+(S.I*s-3*c)
    P, Q = eta*pa+pb, eta*pa-pb
    f = eta*(3*s*st-c*ct-1)+(w-1)/(w+1)*(s*st-3*c*ct-eta**2)
    checks = {"contact_normal_form": S.cancel(2*z*(w+1)*f-P*w-Q)}

    X, Y = S.symbols("X Y")
    solution = S.solve([3*X-Y-1, X-3*Y-eta**2], [X, Y])
    eta2 = (1-4*c**2)/(3-4*c**2)
    v = S.factor((solution[X]/s).subs(eta**2, eta2))
    u = S.factor((solution[Y]/c).subs(eta**2, eta2))
    checks["common_root_sine"] = S.factor(
        S.factor((v-s/(3-4*c**2))*s).subs(s**2, 1-c**2))
    checks["common_root_cosine"] = S.factor(u-c/(3-4*c**2))
    defect = 1/(3-4*c**2)**2-1
    defect_factor = -8*(1-c**2)*(1-2*c**2)/(3-4*c**2)**2
    checks["common_root_defect_factorization"] = S.factor(defect-defect_factor)
    resultant = S.factor(S.resultant(P, Q, z)).subs(s**2, 1-c**2)
    resultant = S.factor(resultant).subs(eta**2, eta2)
    expected_resultant = (-8192*c**2*(1-c**2)**2*(1-4*c**2)
                          *(1-2*c**2)/(3-4*c**2)**3)
    checks["resultant_factorization"] = S.factor(resultant-expected_resultant)

    d, b, t, pi = S.symbols("d b t pi")
    a = -(1-2*d)/(2*(1+2*d))
    A, B = S.Rational(1, 4)+1/(2+d), -1/(2+d)
    linear = (d*b+(1-2*d)*(b/2-t)/2)/(1+2*d)-(pi-b)/(2+d)
    checks["area_linear_coefficients"] = S.factor(linear-a*t-A*b-B*pi)
    checks["bend_coefficient_factorization"] = S.factor(A-(d+6)/(4*(d+2)))

    q2, E = S.symbols("q2 E")
    mu2 = S.Rational(3, 4)/q2-1
    k2 = (1+3/q2)/4
    sine2 = (2-E**2-E**(-2))/4
    checks["mu_recovers_sine_square"] = S.factor(S.Rational(3, 4)/(mu2+1)-q2)
    checks["direction_reconstruction"] = S.cancel(E**4+(4*sine2-2)*E**2+1)
    checks["frequency_hyperbola"] = S.factor(k2-mu2-S.Rational(5, 4))

    H, q, u, eta_r, R = S.symbols("H q u eta_r R", nonzero=True)
    sin_alpha, cos_alpha = (H/z-z/H)/(2*S.I), (H/z+z/H)/2
    original_C = (-q+((1-4*d)*cos_alpha-(1+2*d**2))/(3*sin_alpha))/(1+2*d)
    numerator = (1-4*d)*(H**2+z**2)-2*H*z*(1+2*d**2)
    rational_C = (-q+S.I*numerator/(3*(H**2-z**2)))/(1+2*d)
    checks["forward_rational_form"] = S.cancel(original_C-rational_C)
    checks["nonzero_forward_pole_factorization"] = S.factor(
        numerator.subs(z, H)+4*H**2*d*(d+2))

    rn = eta_r*(u**2-1)
    rd = S.I*(u**2+1)+eta_r*(u**2-1)
    inverse = ((S.I+eta_r)*R-eta_r)*u**2+((S.I-eta_r)*R+eta_r)
    checks["reverse_mobius_inverse"] = S.expand(R*rd-rn-inverse)
    checks["reverse_mobius_determinant"] = S.expand(
        eta_r*(S.I-eta_r)+eta_r*(S.I+eta_r)-2*S.I*eta_r)

    for name, residual in checks.items():
        if residual != 0:
            raise ArithmeticError(f"Symbolic identity failed: {name}: {residual}")
    result = {name: str(residual) for name, residual in checks.items()}
    result.update({
        "common_root_defect": str(defect_factor),
        "contact_resultant": str(expected_resultant),
        "bend_coefficient": str(S.factor(A)),
        "forward_pole_numerator": str(-4*H**2*d*(d+2)),
        "reverse_mobius_determinant_value": str(2*S.I*eta_r),
        "frequency_square_difference": "5/4",
    })
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(verify_identities(), indent=2)+"\n"
    if args.output is None:
        print(text, end="")
    else:
        args.output.write_text(text, encoding="utf-8")
