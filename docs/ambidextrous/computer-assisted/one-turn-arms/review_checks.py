"""Exact local-algebra checks and optional replay audit for AR/TS/SP.

The rational checks are not global sofa certificates. The optional imported
run is floating-point output, and its geometric assumptions remain unverified.
No CI, Lean/Lake, dependency installation, or network call occurs here.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import itertools
import json
import math
from pathlib import Path
import platform
import sympy as sp


def merge_length(intervals):
    intervals = sorted((a,b) for a,b in intervals if a < b)
    if not intervals:
        return Q(0)
    total=Q(0); lo,hi=intervals[0]
    for a,b in intervals[1:]:
        if a > hi:
            total += hi-lo; lo,hi=a,b
        else:
            hi=max(hi,b)
    return total+hi-lo


def checks():
    identities=[]
    def zero(name, expression):
        if sp.cancel(expression) != 0:
            raise AssertionError(name)
        identities.append(name)
    t=sp.symbols('T', positive=True)
    f,g,fm,fp,gm,gp=sp.symbols('f g fm fp gm gp',real=True)
    c=(1-t*t)/(1+t*t); s=2*t/(1+t*t); tangent=s/c
    dfp=(fp-c*f)/s; dfm=(c*f-fm)/s
    dgp=(gp-c*g)/s; dgm=(c*g-gm)/s
    pp,pm=dfp-g+1,dfm-g+1
    qp,qm=f+dgp-1,f+dgm-1
    v0=g-1
    v_next_first=(fp-1-c*(f-1))/s
    v_next_companion=(gp-1+s*(f-1))/c
    up1=(fp-1-s*(g-1))/c
    up2=(c*(g-1)-gp+1)/s
    um2=(gm-1-c*(g-1))/s
    um1=(fm-1+s*(g-1))/c
    zero('unit rational rotation',c*c+s*s-1)
    zero('next first-wall threshold',v_next_first-(dfp-t))
    zero('first-ray next-wall gap',v_next_first-v0-(pp-t))
    zero('companion threshold sign',v_next_companion-v0-tangent*(qp-t))
    zero('companion-ray next first wall',up1-(f-1)-tangent*(pp-t))
    zero('companion-ray next second wall',up2-(t-dgp))
    zero('companion-ray previous second wall',um2-(-dgm-t))
    zero('companion-ray previous first wall',um1-(f-1)+tangent*(pm+t))
    zero('previous-ray coverage margin',um1-um2-(qm+t-tangent*(pm+t)))
    zero('remaining interval length',up2-um2-(2*t-(dgp-dgm)))
    x=sp.symbols('x',real=True)
    zero('initial propagation integral',sp.integrate(sp.Rational(1,4)-3*x/4,(x,0,sp.Rational(1,3)))-sp.Rational(1,24))
    zero('reentered propagation integral',sp.integrate(1-3*x/4,(x,0,sp.Rational(4,3)))-sp.Rational(2,3))
    zero('same-sign propagation integral',sp.integrate(sp.Rational(1,2)-x,(x,0,sp.Rational(1,2)))-sp.Rational(1,8))
    sc,cc=sp.Rational(3,5),sp.Rational(4,5)
    zero('TS rational support constant',sc*sc/2+cc*cc-sc-cc+sp.Rational(29,50))
    zero('TS endpoint arm bound',(sp.Rational(1,2)+sp.Rational(29,50))/(sc*cc)-sp.Rational(9,4))
    wrong_sign=sp.cancel(v_next_companion-v0+tangent*(qp-t))
    if wrong_sign == 0:
        raise AssertionError('Sign mutation was not rejected')
    # The known false strengthening to arm bound 2 does not follow from this direction.
    if not Q(9,4) > 2:
        raise AssertionError('The endpoint witness must exceed two')
    if Q(12,25)*Q(9,4)-Q(29,50) != Q(1,2):
        raise AssertionError('Exact endpoint witness failed')

    # Exact derivative identities in SP1. Positivity is established in the note
    # on the stated ranges; testing a derivative identity is not a sign proof.
    d=sp.symbols('d', positive=True)
    v=sp.symbols('v', nonnegative=True)
    u=sp.symbols('u', positive=True)
    low=2*sp.atan(d)+sp.pi/4-sp.atan(2*d)
    zero('SP low passage derivative',sp.diff(low,d)-6*d*d/((1+d*d)*(1+4*d*d)))
    beta2=2*sp.atan(1/(2*(1+v)))
    zero('SP outer-segment derivative',sp.diff(beta2,v)+4/(1+4*(1+v)**2))
    Bsmall=4*sp.atan(1+v)-sp.pi
    zero('SP small standard duration derivative',sp.diff(Bsmall,v)-4/(1+(1+v)**2))
    Bmiddle=2*(u-1)+sp.pi-4*sp.atan(u/2)
    zero('SP middle standard duration derivative',sp.diff(Bmiddle,u)*2/u-4*u/(u*u+4))
    zero('SP middle lower derivative margin',
         4*u/(u*u+4)-sp.Rational(4,5)-4*(u-1)*(4-u)/(5*(u*u+4)))
    zero('SP middle total derivative margin',
         sp.Rational(4,5)-sp.Rational(4,17)-sp.Rational(48,85))
    zero('SP upper standard duration derivative',sp.diff(v+sp.Rational(1,4),v)-1)
    # The two middle/upper formulas agree at u=2, v=7/4 exactly.
    zero('SP upper joining value',sp.simplify(Bmiddle.subs(u,2))-2)

    cases=0
    levels=[Q(-3,4),Q(0),Q(1,4),Q(3,4),Q(3,2)]
    for T, pm0,pp0,qm0,qp0 in itertools.product([Q(1,10),Q(1,5)],levels,levels,levels,levels):
        if pm0 > pp0 or qm0 > qp0:
            continue
        ct=(1-T*T)/(1+T*T); st=2*T/(1+T*T); tan=st/ct
        # f=g=1. Local offsets, not asserted to be supports of a genuine cap.
        # On the companion ray u<=0, compute the removed intervals independently.
        # The arbitrary finite lower cutoff may only enlarge surviving exposure.
        lo=Q(-20); hi=Q(0)
        covered=[]
        # Next quadrant requires u<tan*(pp-T) and u>T-qp.
        covered.append((max(lo,T-qp0),min(hi,tan*(pp0-T))))
        # Previous quadrant requires u<-qm-T and u<-tan*(pm+T).
        covered.append((lo,min(hi,-qm0-T,-tan*(pm0+T))))
        if pp0 > T and qm0+T >= tan*(pm0+T):
            exposed=hi-lo-merge_length(covered)
            if exposed > max(2*T-(qp0-qm0),Q(0)):
                raise AssertionError('AR7 companion exposure failed')
            cases+=1
    if cases == 0:
        raise AssertionError('No tested AR7 hypotheses')
    growth=0
    points=[Q(-2),Q(-1),Q(0),Q(1),Q(2)]
    intervals=list(itertools.combinations(points,2))
    for pair in itertools.product(intervals,repeat=2):
        for eps in [Q(1,3),Q(2)]:
            base=merge_length(pair)
            grown=merge_length([(a,b+eps) for a,b in pair])
            if grown < base+eps:
                raise AssertionError('One-dimensional growth failed')
            growth+=1
    return dict(status='exact_checks_passed',identity_count=len(identities),identities=identities,
                rational_local_exposure_cases=cases,interval_growth_cases=growth,
                rejected_controls=['companion threshold sign','replacing 9/4 by 2'],
                rational_cases_are_cap_realizations=False,
                arithmetic='SymPy rational identities and Fraction arithmetic',
                endpoint_arm_EA2_proved=False,unrestricted_optimality_proved=False,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                python=platform.python_version(),sympy=sp.__version__,ci_or_lean_used=False)


def passage(q0):
    """SP1's closed formula, evaluated in float only for replay comparison."""
    if q0 < 0:
        raise ValueError('The derived passage formula assumes q0 >= 0')
    if q0 <= math.sqrt(5)/2-1:
        d=math.sqrt((1+q0)**2-1)
        return 2*math.atan(d)+math.pi/4-math.atan(2*d)
    v=math.sqrt((1+q0)**2-0.25)-1
    beta=math.atan(1/(2*(1+v)))
    if v <= 1:
        middle=4*math.atan(1+v)-math.pi
    elif v <= 1.75:
        u=math.sqrt(4*v-3)
        middle=2*(u-1)+math.pi-4*math.atan(u/2)
    else:
        middle=v+0.25
    return 2*beta+middle


def audit_replay(path):
    data=json.loads(path.read_text())
    expected='03ba9e809a5ecf4dc06fc3223ebb4bae793c3b7964ba3cc4d584231369e105b7'
    if data['script_sha256'] != expected:
        raise AssertionError('Unexpected imported source')
    a=data['A_candidate']
    if abs(a['eval_Psi_minus_Mhalf'])>1e-7 or abs(a['eval_A_minus_F'])>1e-7:
        raise AssertionError('Candidate numerical regression')
    for v in data['B_arm_propagation_samples'].values():
        if v['kept']<=0 or v['worst']>1e-6:
            raise AssertionError('Sampled propagation regression')
    fold=data['C_negative_examples']
    if any(v['A_minus_F_refined']<=0 or abs(v['A_minus_F_refined']-v['eval_A_minus_F'])>1e-8 for v in fold):
        raise AssertionError('Fold diagnostics regression')
    e=data['E_saturated_balance_diagnostic']
    if not e['strictly_increasing'] or abs(e['root_minus_q0_star'])>1e-7:
        raise AssertionError('Assumed ODE diagnostic regression')
    qgrid=e['q0_grid']; times=e['hit_time']
    if len(qgrid)!=len(times) or not qgrid:
        raise AssertionError('Missing or mismatched passage samples')
    discrepancy=max(abs(passage(q)-t) for q,t in zip(qgrid,times))
    if discrepancy>1e-6:
        raise AssertionError('Closed passage formula and ODE samples disagree')
    candidate_passage_error=passage(a['q0_star'])-math.pi/2
    return dict(status='floating_point_replay_passed',is_proof_certificate=False,
                original_script_sha256=expected,output_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                python=data['python'],numpy=data['numpy'],scipy=data['scipy'],
                candidate_Psi=a['eval_Psi'],candidate_Psi_minus_M_half=a['eval_Psi_minus_Mhalf'],
                propagation_samples=data['B_arm_propagation_samples'],
                fold_fine_differences=[v['A_minus_F_refined'] for v in fold],
                assumed_ODE_root=e['root_q0'],
                passage_formula_samples=len(qgrid),
                max_passage_formula_discrepancy=discrepancy,
                candidate_passage_formula_error=candidate_passage_error,
                geometry_and_error_sign_certified=False,all_original_parts_completed=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--imported-run',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    out={'exact':checks(),'is_global_proof_certificate':False}
    if args.imported_run:
        out['replay']=audit_replay(args.imported_run)
    text=json.dumps(out,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
