"""Exact finite-algebra checks for CS2 and SQ1.

Requires SymPy; performs no numerical optimization or floating-point decisions.
This checks displayed rational identities, not geometric admission, the reference
candidate, or the entire historical proof. It is not a Lean or CI invocation.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import platform
import sympy as sp


def run_checks() -> dict:
    checked: list[str] = []
    controls: list[str] = []
    def zero(name: str, expr) -> None:
        entries = list(expr) if isinstance(expr, sp.MatrixBase) else [expr]
        if any(sp.cancel(e) != 0 for e in entries):
            raise AssertionError('Identity failed: ' + name)
        checked.append(name)
    def nonzero(name: str, expr) -> None:
        entries = list(expr) if isinstance(expr, sp.MatrixBase) else [expr]
        if all(sp.cancel(e) == 0 for e in entries):
            raise AssertionError('Negative control was not detected: ' + name)
        controls.append(name)

    y = sp.symbols('y', positive=True)
    X,Z,U,V,F,G,z0 = sp.symbols('X Z U V F G z0', real=True)
    rp,rm,dp,dm = sp.symbols('rp rm dp dm', real=True)
    sr,sd,er,ed = sp.symbols('sr sd er ed', real=True)
    C,S,T = 2*y/(1+y*y),(1-y*y)/(1+y*y),(1+y)/(1-y)
    f0 = X+Z
    F0,G0 = F-C*f0-S*G, S*f0-C*G
    aa,bb = (T*F0-G0)/2,(F0+T*G0)/2
    # Integrate f'=g+aa, g'=-f+bb explicitly over the core angle.
    zero('core terminal f', C*f0+S*G+aa*S+bb*(1-C)-F)
    zero('core terminal g', -S*f0+C*G-aa*(1-C)+bb*S)
    core = (aa*(F-f0)-bb*G)/2

    def gap0(xx,zz):
        return (zz**2/y-y*xx**2)/2-y*xx*zz
    def gappi(xx,zz):
        return (zz**2/y-y*xx**2)/2+y*xx*zz
    # Harmonic energy = [h h']/2, independently evaluated at gap endpoints.
    zero('outward half-gap boundary formula',
         ((X+Z)*(-y*X+Z/y)-X*Z*(1+y*y)/y)/2-gap0(X,Z))
    zero('inward half-gap boundary formula',
         (X*Z*(1+y*y)/y-(-X+Z)*(-y*X-Z/y))/2-gappi(X,Z))

    XR,ZR = X+(rp+rm)/2, Z+(rp-rm)/2
    XD,ZD = -(dp+dm)/2,(dm-dp)/2
    tail = ((F*F-2*F*U+U*U)/y+y*(-X+Z-rm)**2
            -2*U*(-X+Z-rm)+y*dp*dp+2*V*dp
            +(V*V+G*G-2*V*G)/y)/2
    cut = ((y*XR-ZR/y)*f0+(f0+rp)*G+dm*F)/2
    E = sp.expand(core+tail+gap0(X,Z)+gappi(XR,ZR)+gap0(XD,ZD)+cut)
    H2 = sp.simplify(sp.hessian(E,(F,G))/2)
    d = (y*y-y+2)/(4*y*(1-y))
    expectedH2 = sp.Matrix([[d,-sp.Rational(1,4)],[-sp.Rational(1,4),d]])
    zero('H2 coefficients', H2-expectedH2)
    zero('H2 second LDL pivot',
         H2[1,1]-H2[1,0]**2/H2[0,0]-(y*y-y+1)/(y*(1-y)*(y*y-y+2)))
    l2 = sp.Matrix([sp.diff(E,w).subs({F:0,G:0}) for w in (F,G)])
    fgmin = sp.simplify(-H2.inv()*l2/2)
    Ered = sp.factor(E.subs({F:0,G:0})-(l2.T*H2.inv()*l2)[0]/4)
    vf = sp.Matrix([F,G])-fgmin
    zero('H2 completed-square identity', E-Ered-(vf.T*H2*vf)[0])

    lower = Ered.subs({U:-z0,V:-z0}, simultaneous=True)
    upper = Ered.subs({Z:-Z,U:z0,V:z0,rp:rm,rm:rp,dp:dm,dm:dp}, simultaneous=True)
    total = sp.expand(lower+upper)
    vars3=(X,Z,z0)
    H3 = sp.simplify(sp.hessian(total,vars3)/2)
    d0=y*y-y+1
    expectedH3=sp.Matrix([
        [(1+y*y)/(2*d0),0,0],
        [0,(1+y*y)*(2*y*y-y+2)/(2*y*d0),(1+y*y)/d0],
        [0,(1+y*y)/d0,2*y/d0]])
    zero('H3 coefficients', H3-expectedH3)
    zero('H3 final LDL pivot',
         H3[2,2]-H3[2,1]**2/H3[1,1]-2*y/(2*y*y-y+2))
    opt=sp.Matrix([
        -y*(rp+rm+dp+dm)/4,
        -(rp-rm+dp-dm)/4,
        ((1-y)*(rp-rm)+(3*y-1+2/y)*(dp-dm))/8])
    subsopt=dict(zip(vars3,opt))
    zero('finite minimizer stationarity',
         sp.Matrix([sp.diff(total,w) for w in vars3]).subs(subsopt,simultaneous=True))
    minimum=sp.factor(total.subs(subsopt,simultaneous=True))
    vv=sp.Matrix(vars3)-opt
    zero('H3 completed-square identity',total-minimum-(vv.T*H3*vv)[0])
    mean_subs={rp:sr+er,rm:sr-er,dp:sd+ed,dm:sd-ed}
    expectedP=((y*y+2*y+3/y)*(er+ed)**2+(1+3/y)*(er-ed)**2)/8 \
              -y*(sr*sr+sd*sd+2*y*sr*sd)/4
    zero('slack remainder factorization',
         minimum.subs(mean_subs,simultaneous=True)-expectedP)
    zero('zero-slack regression',minimum.subs({rp:0,rm:0,dp:0,dm:0}))
    zero('symmetric negative quadratic control value',
         expectedP.subs({er:0,ed:0,sd:sr})+y*(1+y)*sr*sr/2)
    remainder=(y*(sr+sd)-y*(sr*sr+sd*sd+2*y*sr*sd)/4
               -y*(3-y)*(sr+sd)/4)
    positive=y*(sr*(1-sr)+sd*(1-sd)
                +y*(sr*(1-sd)+sd*(1-sr)))/4
    zero('linear slack absorption identity',remainder-positive)

    # Independently sum right endpoint variation with the two reference atoms.
    op,om,ip,im=sp.symbols('op om ip im',real=True)
    endpoint=y*(op+om-ip-im)/2
    atoms=y*(ip+im)
    zero('right first-variation width coefficient',
         endpoint+atoms-y*(op+om+ip+im)/2)
    nonzero('incorrect fixed-cut coefficient detected',
            endpoint+atoms-y*(op+om+ip+im))
    # Audit mutations which preserve dimensions but break real signs/trigonometry.
    nonzero('wrong inward-cut sign detected', (E-dm*F)-E)
    badF0,badG0=F-S*f0-C*G,C*f0-S*G
    badcore=(((T*badF0-badG0)/2)*(F-f0)-((badF0+T*badG0)/2)*G)/2
    nonzero('interchanged sine/cosine in core detected',
            sp.hessian(badcore-core,(F,G)))
    # Positivity is justified by the displayed formulas on 0<y<1, not by samples.
    return {
        'status':'exact_identities_passed',
        'identity_count':len(checked),
        'identities':checked,
        'negative_controls_rejected':controls,
        'arithmetic':'SymPy exact rational functions in indeterminates; no floats',
        'sympy_version':sp.__version__,
        'python_version':platform.python_version(),
        'analytic_domain':'0 < y < 1; each cut slack in [0,1]; both wings span [0,1]',
        'geometric_admission_verified':False,
        'unrestricted_optimality_proved':False,
        'lean_or_ci_used':False,
        'scope':'Finite identities in CS2/SQ1, not the complete geometric proof',
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    text=json.dumps(run_checks(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
