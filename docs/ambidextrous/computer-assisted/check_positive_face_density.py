"""Short exact regressions for RR/PD, not a global optimality certificate.

Only unbounded integers and Fraction are used. The compactness, connectedness,
semiconvexity and limit arguments are the hand proofs in the companion notes.
Run under an external five-second limit. No CI, Lean, network or search solver.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
from time import perf_counter


def dot(p, n):
    return p[0]*n[0]+p[1]*n[1]


def clip(poly, n, bound):
    """Exact half-plane clipping of a convex rational polygon."""
    out = []
    for p, q in zip(poly, poly[1:]+poly[:1]):
        a, b = dot(p, n)-bound, dot(q, n)-bound
        if a <= 0:
            out.append(p)
        if (a < 0 < b) or (b < 0 < a):
            t = a/(a-b)
            out.append(tuple(p[i]+t*(q[i]-p[i]) for i in range(2)))
    # Remove duplicates without imposing an unverified cyclic reordering.
    clean = []
    for p in out:
        if not clean or p != clean[-1]:
            clean.append(p)
    if len(clean) > 1 and clean[0] == clean[-1]:
        clean.pop()
    return clean


def direction(r):
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)


def width(poly, n):
    vals = [dot(p, n) for p in poly]
    return max(vals)-min(vals)


def run():
    start = perf_counter()
    tests = []
    def check(name, ok):
        if not ok:
            raise AssertionError(name)
        tests.append(name)

    depth_count = 0
    for lam in (Q(1,2), Q(3,4), Q(9,10), Q(99,100)):
        r = (1-lam)/2
        check('rounding budget '+str(lam), lam+2*r == 1)
        for depth in (Q(0), Q(1,3), Q(2,3), Q(1)):
            for z in (Q(-1), Q(-3,5), Q(0), Q(4,5), Q(1)):
                if lam*depth+r*(1-z) > 1:
                    raise AssertionError('Canonical depth bound failed')
                depth_count += 1
        for old_width in (Q(1,2), Q(1), Q(3,2), Q(3)):
            new_width = lam*old_width+2*r
            check('safe-strip level '+str((lam,old_width)),
                  (new_width <= 1) == (old_width <= 1))
        for ratio in (Q(1,10), Q(1,4), Q(1,2)):
            eps = ratio*r
            check('centers and positive chord '+str((lam,ratio)),
                  r-eps > 0 and 2*r*eps-eps*eps > 0)
            # A support whose center has depth at least r moves inside the
            # shaved plane under the stated centered homothety.
            for slack in (r, 2*r, 3*r):
                check('inner homothety '+str((lam,ratio,slack)),
                      (eps/r)*slack >= eps)

    for c in (Q(1,8),Q(1,4),Q(1,2),Q(1)):
        for D in (Q(1),Q(2),Q(4),Q(8)):
            sigma = Q(1,4)
            h = min(sigma/8,c/(8*D))
            err = c*h/16
            check('semiconvex lower derivative '+str((c,D)),
                  h < sigma/4 and c-2*err/h-D*h/2 > c/2)

    # A rational rectangle tests only the convex clipping/width lemma.
    # These samples are not the proof of the general interval statement.
    rect = [(Q(-3,4),Q(-1,4)),(Q(3,4),Q(-1,4)),
            (Q(3,4),Q(1,4)),(Q(-3,4),Q(1,4))]
    c,s = direction(Q(1,5)); n=(-s,c); tangent=(c,s)
    cap = max(dot(p,n) for p in rect); eps=Q(1,1000)
    shaved = clip(clip(rect,n,cap-eps),(-n[0],-n[1]),cap-eps)
    d = 2*(cap-eps)
    check('cut width attained', width(shaved,n)==d and d>1)
    top = [dot(p,tangent) for p in shaved if dot(p,n)==cap-eps]
    bottom = [dot(p,tangent) for p in shaved if dot(p,n)==-cap+eps]
    check('both actual polygon faces positive', len(top)>=2 and len(bottom)>=2
          and max(top)>min(top) and max(bottom)>min(bottom))
    gap = min(bottom)-max(top)
    check('strict face order',gap>0)
    sampled_widths=[]
    for k in range(101):
        cc,ss=direction(Q(k,500))
        value=width(shaved,(-ss,cc))
        if value>d:
            raise AssertionError('Rational clipped width sample exceeded endpoint')
        sampled_widths.append(value)
    check('sampled increasing clipped widths',
          all(a<b for a,b in zip(sampled_widths,sampled_widths[1:])))

    # Negative controls: premises that must not be silently omitted.
    check('oversized rounding rejected', Q(3,4)+2*Q(1,4)>1)
    check('shaving past disk centers rejected',Q(1,10)-Q(1,9)<0)
    # Finite regularization need not be area-nonincreasing. A radius-1/4
    # disk rounds to radius 3/8 at lambda=1/2; the limit, not monotonicity,
    # is the valid general assertion.
    check('finite area-monotonicity claim rejected',Q(1,2)*Q(1,4)+Q(1,4)>Q(1,4))
    # Three safe strip normals do not certify their intervening interval.
    hexagon=[(Q(25,14),Q(0)),(Q(1,14),Q(1,2)),(-Q(1,14),Q(1,2)),
             (-Q(25,14),Q(0)),(-Q(1,14),-Q(1,2)),(Q(1,14),-Q(1,2))]
    check('isolated safe strips',all(width(hexagon,n)==1 for n in
          [(Q(7,25),Q(24,25)),(Q(0),Q(1)),(-Q(7,25),Q(24,25))]))
    check('missing safe-strip bridge rejected',
          width(hexagon,(Q(9,41),Q(40,41)))==Q(289,287)>1)

    return dict(status='exact_regressions_passed',named_checks=len(tests),
                depth_cases=depth_count,convex_strip_samples=len(sampled_widths),
                rectangle_shaved_width=str(d),rectangle_face_gap=str(gap),
                arithmetic='Python unbounded integers and Fraction',
                negative_controls=['oversized rounding','shaving excludes centers',
                    'finite area monotonicity','isolated strips are not a bridge'],
                continuum_density_verified_by_script=False,
                arbitrary_sofa_feasibility_verified_by_script=False,
                unrestricted_optimality_proved=False,
                python_version=platform.python_version(),
                internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                ci_or_lean_used=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
