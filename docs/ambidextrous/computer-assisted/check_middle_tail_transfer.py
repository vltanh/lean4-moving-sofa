"""Short exact MT/ME/CT/HC regressions; not a global optimality certificate.

The proofs supply geometric admission, monotone substitution and the continuum
claims. Local rational samples do not assert actual cap realizability.
Run with an external five-second timeout. Standard library only; no search.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
from time import perf_counter


def scalar_remainder(x: Q, e: Q, positive: bool) -> Q:
    part = lambda z: max(z, Q(0)) if positive else min(z, Q(0))
    return part(x+e)**2-part(x)**2-2*part(x)*e


def integrand(f: Q, g: Q, fp: Q, gp: Q) -> Q:
    p, q = fp-g+1, gp+f-1
    return (f*f+g*g-fp*fp-gp*gp+(f-1)**2+(g-1)**2
            +(f-1)*gp-(g-1)*fp-min(p, Q(0))**2-max(q, Q(0))**2)/2


def gradient(f: Q, g: Q, fp: Q, gp: Q) -> tuple[Q, Q, Q, Q]:
    pm, qp = min(fp-g+1, Q(0)), max(gp+f-1, Q(0))
    return (2*f-1+gp/2-qp, 2*g-1-fp/2+pm,
            -fp-(g-1)/2-pm, -gp+(f-1)/2-qp)


def direction(r: Q) -> tuple[Q, Q]:
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)


def run() -> dict:
    start = perf_counter()
    named = []
    def check(name: str, ok: bool) -> None:
        if not ok:
            raise AssertionError(name)
        named.append(name)

    c0, s0 = direction(Q(9, 11))
    check('cut direction is complementary to eta', (c0, s0) == (Q(20, 101), Q(99, 101)))
    check('late p strict upper bound', 1-Q(3, 2)*s0 == -Q(95, 202))
    check('late q strict upper bound', 2*c0-Q(1, 2) == -Q(21, 202))
    check('companion clearance floor', (Q(3, 2)*s0-1)/c0 == Q(19, 8))
    check('allowed upward wall displacement', (1-s0)/(2*s0) == Q(1, 99) < Q(19, 8))
    check('changed-corner height bound', c0+c0*c0/2 == Q(2220, 10201) < Q(1, 2))
    check('background perturbation height bound', Q(13, 30)+Q(1, 50) == Q(34, 75) < Q(1, 2))
    check('ordinary derivative coercivity constant', Q(7, 32)*Q(4, 5)**2 == Q(7, 50))
    check('HC background niche is below half height', Q(7, 5)**2 < 2 and Q(31, 20)-Q(3, 4)*Q(7, 5) == Q(1, 2))

    remainder_cases = 0
    for positive in (False, True):
        for i in range(-8, 9):
            for j in range(-8, 9):
                if scalar_remainder(Q(i, 4), Q(j, 4), positive) < 0:
                    raise AssertionError('Negative convex scalar remainder')
                remainder_cases += 1
    check('positive/negative-part remainders', remainder_cases == 578)

    quadratic_cases = 0
    values = (Q(-2, 3), Q(0), Q(1, 5), Q(7, 4))
    for v in values:
        for w in values:
            for vp in values:
                for wp in values:
                    b0 = (vp*vp+wp*wp-2*(v*v+w*w)-(v*wp-w*vp))/2
                    gauge = ((vp+w/2)**2+(wp-v/2)**2)/2-Q(9, 8)*(v*v+w*w)
                    if b0 != gauge:
                        raise AssertionError('Incorrect gauge-completion sign')
                    for f,g,fp,gp in ((Q(1),Q(1),Q(0),Q(0)),
                                     (Q(3,2),Q(4,3),Q(-2,5),Q(1,4)),
                                     (Q(1,2),Q(3,4),Q(2),Q(-1))):
                        grad = gradient(f,g,fp,gp)
                        lhs = integrand(f,g,fp,gp)-integrand(f+v,g+w,fp+vp,gp+wp)
                        lhs += sum(a*b for a,b in zip(grad,(v,w,vp,wp)))
                        rhs = b0+(scalar_remainder(fp-g+1,vp-w,False)
                                  +scalar_remainder(gp+f-1,wp+v,True))/2
                        if lhs != rhs:
                            raise AssertionError('Wrong adaptive deficit expansion')
                        quadratic_cases += 1
    check('pointwise quadratic and contact-remainder expansion', quadratic_cases == 768)

    pruning_cases = pairing_cases = 0
    for m in (Q(1), Q(7,6), Q(6,5), Q(4,3)):
        b = m/2
        def walls(c: Q, s: Q, x: Q) -> tuple[Q, Q]:
            f, g = Q(1,2)+b*c+s/2, m*s+c/2
            return ((f-1-x*c)/s, (g-1+x*s)/c)
        for rr in (Q(9,11), Q(5,6), Q(9,10), Q(19,20), Q(39,40)):
            c,s = direction(rr)
            for k in range(21):
                x = -m+(b-Q(10,101)+m)*Q(k,20)
                if min(walls(c,s,x)) > min(walls(c0,s0,x)):
                    raise AssertionError('False end-angle pruning inequality')
                pruning_cases += 1
            xin,xout = b-c/2,b+c/2
            nbase,abase = (1-s)/2,(1+s)/2
            f,g = Q(1,2)+b*c+s/2,m*s+c/2
            for scale in (Q(-1), Q(-1,2), Q(0), Q(1), Q(4)):
                e = scale*(1-s)/2
                rnew = (f-e-1-xin*c)/s
                lold = (g-1+xin*s)/c
                outer_test = (f-e-xout*c)/s
                if lold < rnew or nbase-max(Q(0),rnew) > e/s or abase-outer_test != e/s:
                    raise AssertionError('Signed tail test or companion clearance failed')
                pairing_cases += 1
    check('end-angle two-case pruning samples', pruning_cases == 420)
    check('signed inner/outer supporting-line pairings', pairing_cases == 100)

    jacobian_cases = 0
    for rho in (Q(1,2),Q(3,5),Q(2,3),Q(3,4),Q(1)):
        for e in (Q(0),Q(1,100),Q(1,7),Q(1,2),Q(2)):
            if e*rho-e*(1-rho) != e*(2*rho-1) or e*(2*rho-1) < 0:
                raise AssertionError('Wrong tail Jacobian surplus')
            jacobian_cases += 1
    check('nonnegative inward Jacobian surplus', jacobian_cases == 25)

    gains = 0
    for aa in (Q(1,10),Q(1),Q(3,2)):
        for bb in (Q(1),Q(2),Q(10)):
            eps=aa/(4*bb)
            if eps*aa/2-eps**2*bb != aa**2/(16*bb) or aa**2/(16*bb) <= 0:
                raise AssertionError('HC small-change gain has wrong sign')
            gains += 1
    check('HC positive finite quadratic gain', gains == 9)

    # Deliberate stronger statements that the actual hypotheses do not allow.
    controls = []
    check('below-half threshold has negative surplus', Q(1,4)-(1-Q(1,4)) < 0)
    controls.append('unit curvature alone does not pay inward tail loss')
    check('outward sign can reverse CT surplus', -Q(1,10)*(2*Q(3,4)-1) < 0)
    controls.append('CT cannot silently admit outward defects')
    check('coercivity constant is not seven thirty-seconds for raw derivatives',
          Q(7,32)*Q(4,5)**2 != Q(7,32))
    controls.append('gauge-to-raw derivative factor retained')

    return dict(status='exact_regressions_passed', named_checks=len(named), checks=named,
                remainder_cases=remainder_cases, deficit_identity_cases=quadratic_cases,
                pruning_cases=pruning_cases, signed_pairing_cases=pairing_cases,
                jacobian_cases=jacobian_cases, finite_gain_cases=gains,
                negative_controls=controls, arithmetic='unbounded integers and Fraction',
                python_version=platform.python_version(), internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                geometric_admission_verified=False, continuum_proof_verified=False,
                local_samples_are_cap_realizations=False, unrestricted_optimality_proved=False,
                ci_or_lean_used=False)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
