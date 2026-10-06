"""Exact finite-algebra checks for GH1 (arbitrary unequal wing heights with
arbitrary cut slack).

Requires SymPy.  Reconstructs the minimized finite remainder from the same
pre-minimization expression SQ.6 used by check_two_wing_slack.py and
check_two_wing_height.py, but with three independent vertical trace
deficits (A, B0, C0) as in WS.7, then verifies

  * the height / cut / mixed split, with the general mixed term GH.3;
  * the absorption identity GH.5 used in the written sign argument;
  * regressions: B0=C0=T0 gives NH.8, A=B0=C0=0 gives SQ.9, zero slack gives
    WS.10;
  * three deliberate mutations are rejected.

It checks rational identities in the indeterminate y=tan(beta) only.  It does
not check geometric admission, terminal angles or unrestricted optimality.
"""
from __future__ import annotations
import hashlib
import json
import platform
from pathlib import Path
import sympy as sp


def build():
    y = sp.symbols('y', positive=True)
    X, Z, U, V, F, G, z0 = sp.symbols('X Z U V F G z0', real=True)
    rp, rm, dp, dm = sp.symbols('rp rm dp dm', real=True)
    A, B0, C0 = sp.symbols('A B0 C0', nonnegative=True, real=True)
    sr, sd, er, ed = sp.symbols('sr sd er ed', real=True)
    C, S, T = 2*y/(1+y*y), (1-y*y)/(1+y*y), (1+y)/(1-y)
    f0 = X+Z
    F0, G0 = F-C*f0-S*G, S*f0-C*G
    aa, bb = (T*F0-G0)/2, (F0+T*G0)/2
    core = (aa*(F-f0)-bb*G)/2

    def gap0(xx, zz):
        return (zz**2/y-y*xx**2)/2-y*xx*zz

    def gappi(xx, zz):
        return (zz**2/y-y*xx**2)/2+y*xx*zz

    XR, ZR = X+(rp+rm)/2, Z+(rp-rm)/2
    XD, ZD = -(dp+dm)/2, (dm-dp)/2
    tail = ((F*F-2*F*U+U*U)/y+y*(-X+Z-rm)**2
            - 2*U*(-X+Z-rm)+y*dp*dp+2*V*dp
            + (V*V+G*G-2*V*G)/y)/2
    cut = ((y*XR-ZR/y)*f0+(f0+rp)*G+dm*F)/2
    E = sp.expand(core+tail+gap0(X, Z)+gappi(XR, ZR)+gap0(XD, ZD)+cut)

    H2 = sp.simplify(sp.hessian(E, (F, G))/2)
    l2 = sp.Matrix([sp.diff(E, w).subs({F: 0, G: 0}) for w in (F, G)])
    Ered = sp.factor(E.subs({F: 0, G: 0})-(l2.T*H2.inv()*l2)[0]/4)
    lower = Ered.subs({U: -z0, V: -A-z0}, simultaneous=True)
    upper = Ered.subs({Z: -Z, U: -B0+z0, V: -C0+z0,
                       rp: rm, rm: rp, dp: dm, dm: dp}, simultaneous=True)
    total = sp.expand(lower+upper)
    H3 = sp.simplify(sp.hessian(total, (X, Z, z0))/2)
    l3 = sp.Matrix([sp.diff(total, w).subs({X: 0, Z: 0, z0: 0})
                    for w in (X, Z, z0)])
    opt = sp.simplify(-H3.inv()*l3/2)
    minimum = sp.expand(total.subs(dict(zip((X, Z, z0), opt)), simultaneous=True))
    minimum = sp.expand(minimum.subs({rp: sr+er, rm: sr-er,
                                      dp: sd+ed, dm: sd-ed}, simultaneous=True))
    syms = dict(y=y, A=A, B0=B0, C0=C0, sr=sr, sd=sd, er=er, ed=ed,
                X=X, Z=Z, z0=z0, H2=H2, H3=H3, opt=opt, upper=upper, Ered=Ered)
    return minimum, syms


def run():
    checked, controls = [], []

    def zero(name, e):
        es = list(e) if isinstance(e, sp.MatrixBase) else [e]
        if any(sp.cancel(sp.together(x)) != 0 for x in es):
            raise AssertionError(name)
        checked.append(name)

    def nonzero(name, e):
        es = list(e) if isinstance(e, sp.MatrixBase) else [e]
        if all(sp.cancel(sp.together(x)) == 0 for x in es):
            raise AssertionError("mutation not detected: "+name)
        controls.append(name)

    minimum, s = build()
    y, A, B0, C0 = s["y"], s["A"], s["B0"], s["C0"]
    sr, sd, er, ed = s["sr"], s["sd"], s["er"], s["ed"]
    X, Z, z0 = s["X"], s["Z"], s["z0"]
    k = 2*y/(1+y*y)
    half = sp.Rational(1, 2)
    quarter = sp.Rational(1, 4)

    # WS.10 height polynomial, SQ.9 cut polynomial
    Pk = ((A-B0)**2+C0**2)/8+(k-quarter)*A*C0+(k-3*quarter)*B0*C0
    Pcut = ((y*y+2*y+3/y)*(er+ed)**2+(1+3/y)*(er-ed)**2)/8 \
        - y*(sr**2+sd**2+2*y*sr*sd)/4
    # GH.3 general mixed term
    alphaR = (1-y)/2*A+B0+(1-y)/2*C0
    alphaD = A+(1-y)/2*B0+C0
    gamma = (1-y)/4*(A+B0-C0)
    mixed = -alphaR*sr-alphaD*sd-gamma*(er+ed)

    # the 3x3 minimisation is the WS one: same Hessian as WS/SQ
    d0 = y*y-y+1
    H3ws = sp.Matrix([[(1+y*y)/(2*d0), 0, 0],
                      [0, (1+y*y)*(2*y*y-y+2)/(2*y*d0), (1+y*y)/d0],
                      [0, (1+y*y)/d0, 2*y/d0]])
    zero("3x3 Hessian equals WS/SQ matrix", s["H3"]-H3ws)
    d = (y*y-y+2)/(4*y*(1-y))
    zero("2x2 Hessian equals WS.6 matrix",
         s["H2"]-sp.Matrix([[d, -quarter], [-quarter, d]]))

    zero("general height-cut-mixed decomposition", minimum-Pk-Pcut-mixed)
    zero("zero-slack regression (WS.10)",
         minimum.subs({sr: 0, sd: 0, er: 0, ed: 0})-Pk)
    zero("zero-height regression (SQ.9)",
         minimum.subs({A: 0, B0: 0, C0: 0})-Pcut)
    T0 = sp.symbols('T0', nonnegative=True)
    nh8 = (A*(y-1)*(er+ed+2*sr)-4*A*sd+2*T0*(y-3)*(sr+sd))/4
    zero("shared-bottom regression (NH.8)",
         mixed.subs({B0: T0, C0: T0}, simultaneous=True)-nh8)

    # GH.5 absorption identity
    a = (y*y+2*y+3/y)/8
    b = (1+3/y)/8
    Eg = er+ed
    Dg = er-ed
    resid = y*(sr*(1-sr)+sd*(1-sd)+y*(sr*(1-sd)+sd*(1-sr)))/4
    lin = y*(3-y)/4
    lhs = y*(sr+sd)+Pcut+mixed+Pk
    rhs = (lin-alphaR)*sr+(lin-alphaD)*sd+(a*Eg**2-gamma*Eg)+b*Dg**2+Pk+resid
    zero("GH.5 absorption identity", lhs-rhs)

    # WS.11 copositive factorisation of the height polynomial (general)
    ws11 = (B0-A+(4*k-3)*C0)**2/8+(1-(4*k-3)**2)/8*C0**2+(2*k-1)*A*C0
    zero("WS.11 copositive factorisation", Pk-ws11)

    # mutations
    nonzero("mixed term with A and C0 roles exchanged rejected",
            minimum-Pk-Pcut-mixed.subs({A: C0, C0: A}, simultaneous=True))
    nonzero("lost reflected bottom trace rejected",
            s["upper"]-s["Ered"].subs({Z: -Z, sp.Symbol('U', real=True): z0,
                                       sp.Symbol('V', real=True): z0},
                                      simultaneous=True))
    nonzero("sign of gamma flipped rejected",
            lhs-((lin-alphaR)*sr+(lin-alphaD)*sd+(a*Eg**2+gamma*Eg)+b*Dg**2+Pk+resid))

    return {
        "status": "exact_identities_passed",
        "identity_count": len(checked),
        "identities": checked,
        "negative_controls_rejected": controls,
        "mixed_term": str(sp.simplify(mixed)),
        "analytic_domain": "0<y<1; A,B0,C0>=0; 0<=s_R,s_D<=1; |e_R|<=s_R, |e_D|<=s_D",
        "geometric_admission_verified": False,
        "unrestricted_optimality_proved": False,
        "arithmetic": "SymPy exact rational functions; no floating-point decisions",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "lean_or_ci_used": False,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
