"""Exact finite-algebra checks for NH1.

Requires SymPy.  This reconstructs the minimized finite remainder from the
same pre-minimization expression used by SQ1 and verifies the height/cut/mixed
split.  It does not check geometric admission or unrestricted optimality.
"""
from __future__ import annotations
import hashlib, json, platform
from pathlib import Path
import sympy as sp

def run():
    checked=[]
    controls=[]
    def zero(name,e):
        es=list(e) if isinstance(e,sp.MatrixBase) else [e]
        if any(sp.cancel(x)!=0 for x in es):
            raise AssertionError(name)
        checked.append(name)
    def nonzero(name,e):
        es=list(e) if isinstance(e,sp.MatrixBase) else [e]
        if all(sp.cancel(x)==0 for x in es):
            raise AssertionError("mutation not detected: "+name)
        controls.append(name)

    y=sp.symbols('y', positive=True)
    X,Z,U,V,F,G,z0=sp.symbols('X Z U V F G z0', real=True)
    rp,rm,dp,dm=sp.symbols('rp rm dp dm', real=True)
    A,T0=sp.symbols('A T0', nonnegative=True, real=True)
    sr,sd,er,ed=sp.symbols('sr sd er ed', real=True)
    C,S,T=2*y/(1+y*y),(1-y*y)/(1+y*y),(1+y)/(1-y)
    f0=X+Z
    F0,G0=F-C*f0-S*G,S*f0-C*G
    aa,bb=(T*F0-G0)/2,(F0+T*G0)/2
    core=(aa*(F-f0)-bb*G)/2
    def gap0(xx,zz):
        return (zz**2/y-y*xx**2)/2-y*xx*zz
    def gappi(xx,zz):
        return (zz**2/y-y*xx**2)/2+y*xx*zz
    XR,ZR=X+(rp+rm)/2,Z+(rp-rm)/2
    XD,ZD=-(dp+dm)/2,(dm-dp)/2
    tail=((F*F-2*F*U+U*U)/y+y*(-X+Z-rm)**2
          -2*U*(-X+Z-rm)+y*dp*dp+2*V*dp
          +(V*V+G*G-2*V*G)/y)/2
    cut=((y*XR-ZR/y)*f0+(f0+rp)*G+dm*F)/2
    E=sp.expand(core+tail+gap0(X,Z)+gappi(XR,ZR)+gap0(XD,ZD)+cut)

    H2=sp.simplify(sp.hessian(E,(F,G))/2)
    l2=sp.Matrix([sp.diff(E,w).subs({F:0,G:0}) for w in (F,G)])
    Ered=sp.factor(E.subs({F:0,G:0})-(l2.T*H2.inv()*l2)[0]/4)
    lower=Ered.subs({U:-z0,V:-A-z0}, simultaneous=True)
    upper=Ered.subs({Z:-Z,U:-T0+z0,V:-T0+z0,
                     rp:rm,rm:rp,dp:dm,dm:dp}, simultaneous=True)
    total=sp.expand(lower+upper)
    H3=sp.simplify(sp.hessian(total,(X,Z,z0))/2)
    l3=sp.Matrix([sp.diff(total,w).subs({X:0,Z:0,z0:0})
                  for w in (X,Z,z0)])
    opt=sp.simplify(-H3.inv()*l3/2)
    minimum=sp.factor(total.subs(dict(zip((X,Z,z0),opt)),simultaneous=True))
    minimum=sp.factor(minimum.subs({rp:sr+er,rm:sr-er,
                                    dp:sd+ed,dm:sd-ed},simultaneous=True))

    k=2*y/(1+y*y)
    pheight=((A-T0)**2+T0**2)/8+(k-sp.Rational(1,4))*A*T0 \
            +(k-sp.Rational(3,4))*T0**2
    pcut=((y*y+2*y+3/y)*(er+ed)**2
          +(1+3/y)*(er-ed)**2)/8 \
         -y*(sr**2+sd**2+2*y*sr*sd)/4
    mixed=(A*(y-1)*(er+ed+2*sr)-4*A*sd
           +2*T0*(y-3)*(sr+sd))/4
    zero("height-cut-mixed decomposition",minimum-pheight-pcut-mixed)
    zero("zero-height regression",
         minimum.subs({A:0,T0:0})-pcut)
    zero("zero-cut regression",
         minimum.subs({sr:0,sd:0,er:0,ed:0})-pheight)

    # The purely algebraic absorption identities used in the written proof.
    linear_remainder=(y*(sr+sd)-y*(sr**2+sd**2+2*y*sr*sd)/4
                      -y*(3-y)*(sr+sd)/4)
    positive=y*(sr*(1-sr)+sd*(1-sd)
                +y*(sr*(1-sd)+sd*(1-sr)))/4
    zero("SQ linear-slack absorption",linear_remainder-positive)

    # Coefficient comparisons after A+T0 <= y/2.
    zero("sD coefficient difference",
         (3-y)/2-(5-y)/4-(1-y)/4)
    zero("sR coefficient difference",
         (3-y)/2-3*(1-y)/4-(3+y)/4)

    # Exact WS factorization of the height term at B0=C0=T0.
    ws=((T0-A+(4*k-3)*T0)**2
        +(1-(4*k-3)**2)*T0**2)/8+(2*k-1)*A*T0
    zero("height copositive factorization",pheight-ws)

    nonzero("wrong half endpoint coefficient rejected",
            minimum-(pheight+pcut+2*mixed))
    nonzero("lost reflected bottom trace rejected",
            upper-Ered.subs({Z:-Z,U:z0,V:z0,
                             rp:rm,rm:rp,dp:dm,dm:dp},simultaneous=True))

    return {
      "status":"exact_identities_passed",
      "identity_count":len(checked),
      "identities":checked,
      "negative_controls_rejected":controls,
      "analytic_domain":"0<y<1, A,T0>=0, A+T0<=y/2, cut slacks nonnegative",
      "geometric_admission_verified":False,
      "unrestricted_optimality_proved":False,
      "arithmetic":"SymPy exact rational functions; no floating-point decisions",
      "python_version":platform.python_version(),
      "sympy_version":sp.__version__,
      "lean_or_ci_used":False,
      "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    }

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
