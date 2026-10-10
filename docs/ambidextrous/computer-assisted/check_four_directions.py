"""Bounded, reproducible first attempts for four ambidextrous proof directions.

D1--D3 use Fraction arithmetic. D4's numerical quadrature is diagnostic only;
its continuum theorem is proved separately. No optimizer or Lean invocation.
Run: timeout 5s python four_direction_checks.py --output results.json
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from hashlib import sha256, sha1
from pathlib import Path
from time import perf_counter
import math
import json
import platform

Point = tuple[F, F]
HalfPlane = tuple[F, F, F]


def clip(poly: list[Point], hp: HalfPlane) -> list[Point]:
    a, b, c = hp
    if not poly:
        return []
    out = []
    for p, q in zip(poly, poly[1:] + poly[:1]):
        vp = a*p[0]+b*p[1]-c
        vq = a*q[0]+b*q[1]-c
        pin, qin = vp <= 0, vq <= 0
        if pin:
            out.append(p)
        if pin != qin:
            t = vp/(vp-vq)
            out.append((p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1])))
    clean = []
    for p in out:
        if not clean or p != clean[-1]:
            clean.append(p)
    if len(clean) > 1 and clean[0] == clean[-1]:
        clean.pop()
    return clean


def area(poly: list[Point]) -> F:
    if len(poly) < 3:
        return F(0)
    return abs(sum(p[0]*q[1]-p[1]*q[0]
                   for p,q in zip(poly,poly[1:]+poly[:1])))/2


def box(w: F, h: F = F(1)) -> list[Point]:
    return [(F(0), F(0)), (w, F(0)), (w, h), (F(0), h)]


def support(poly: list[Point], n: Point) -> F:
    return max(n[0]*x+n[1]*y for x,y in poly)


def lower_quad(poly: list[Point], n: Point) -> list[HalfPlane]:
    assert n[0]**2+n[1]**2 == 1
    v = (-n[1], n[0])
    return [(n[0], n[1], support(poly,n)-1),
            (v[0], v[1], support(poly,v)-1)]


def reflect_y(q: list[HalfPlane]) -> list[HalfPlane]:
    return [(a,-b,c-b) for a,b,c in q]


def quads_for_box(w: F) -> list[list[HalfPlane]]:
    B = box(w)
    lower = [lower_quad(B,(F(3,5),F(4,5))),
             lower_quad(B,(F(4,5),F(3,5)))]
    return lower + [reflect_y(q) for q in lower]


def intersection(B: list[Point], qs: list[list[HalfPlane]]) -> list[Point]:
    p = list(B)
    for q in qs:
        for hp in q:
            p = clip(p,hp)
    return p


def removed(B: list[Point], qs: list[list[HalfPlane]]) -> F:
    total = F(0)
    for k in range(1,len(qs)+1):
        for inds in combinations(range(len(qs)),k):
            value = area(intersection(B,[qs[i] for i in inds]))
            total += value if k%2 else -value
    return total


def remaining(B: list[Point], qs: list[list[HalfPlane]]) -> F:
    return area(B)-removed(B,qs)


def vertical_area(width: F, qs: list[list[HalfPlane]]) -> tuple[F,list[dict]]:
    """Independent area evaluator: order all wall crossings, integrate fibers.

    Only for lower/downward or upper/upward quadrants, in [0,width] x [0,1].
    Uses no polygon clipping or inclusion-exclusion.
    """
    lines = [(F(0),F(0)),(F(0),F(1))]
    walls = []
    for q in qs:
        assert len(q) == 2 and q[0][1]*q[1][1] > 0
        ids = []
        for a,b,c in q:
            ids.append(len(lines))
            lines.append((-a/b,c/b))
        walls.append((q[0][1] > 0, ids))
    breaks = {F(0),width}
    for (m,b),(n,c) in combinations(lines,2):
        if m != n:
            x = (c-b)/(m-n)
            if 0 < x < width:
                breaks.add(x)
    xs = sorted(breaks)
    ans = F(0)
    cert = []
    for a,b in zip(xs,xs[1:]):
        mid = (a+b)/2
        vals = [m*mid+c for m,c in lines]
        lo,hi = 0,1
        for is_lower,ids in walls:
            if is_lower:
                i = min(ids,key=lambda i: vals[i])
                if vals[i] > vals[lo]: lo=i
            else:
                i = max(ids,key=lambda i: vals[i])
                if vals[i] < vals[hi]: hi=i
        if vals[hi] <= vals[lo]:
            v = F(0)
        else:
            m = lines[hi][0]-lines[lo][0]
            c = lines[hi][1]-lines[lo][1]
            v = (b-a)*(m*(a+b)/2+c)
            assert v >= 0
        ans += v
        cert.append({'left':str(a),'right':str(b),'lower_line':lo,
                     'upper_line':hi,'area':str(v)})
    return ans,cert


def quadratic_candidates(H, g, c, lo=F(0), hi=F(1)):
    """Exhaust all faces of a 2D rational box per Theorem D1.1."""
    def value(x):
        return c+sum(g[i]*x[i] for i in range(2))+sum(
            x[i]*H[i][j]*x[j] for i in range(2) for j in range(2))/2
    pts = list(product((lo,hi),repeat=2))
    for fixed in range(2):
        free = 1-fixed
        if H[free][free] < 0:
            for z in (lo,hi):
                y = -(g[free]+H[free][fixed]*z)/H[free][free]
                if lo <= y <= hi:
                    x=[F(0),F(0)];x[fixed]=z;x[free]=y;pts.append(tuple(x))
    det=H[0][0]*H[1][1]-H[0][1]*H[1][0]
    if H[0][0] < 0 and det > 0:
        x=(-g[0]*H[1][1]+H[0][1]*g[1])/det
        y=(-H[0][0]*g[1]+H[1][0]*g[0])/det
        if lo<=x<=hi and lo<=y<=hi:pts.append((x,y))
    best=max(value(x) for x in pts)
    return best,[x for x in pts if value(x)==best]


def direction1():
    d=F(5,7)
    val,pts=quadratic_candidates(((F(0),F(-2)),(F(-2),F(0))),
                                 (d,d),F(0),d/4,3*d/4)
    assert val==F(125,392)
    assert set(pts)=={(d/4,3*d/4),(3*d/4,d/4)}
    t=d/8
    base=d*d/2
    improved=d*((d/2+t)+(d/2-t))-2*(d/2+t)*(d/2-t)
    assert improved-base==2*t*t>0
    fixtures=[
        (((F(-2),F(0)),(F(0),F(-4))),(F(2,3),F(8,3)),F(0),F(1)),
        (((F(-2),F(-2)),(F(-2),F(-2))),(F(2),F(2)),F(0),F(1)),
        (((F(2),F(0)),(F(0),F(2))),(F(0),F(0)),F(0),F(2)),
        (((F(0),F(0)),(F(0),F(0))),(F(1),F(1)),F(0),F(2)),
    ]
    # First fixture's maximum is 1 (1/9+8/9) without its constant shift.
    for H,g,c,expected in fixtures:
        best,_=quadratic_candidates(H,g,c)
        assert best==expected
    return {'stationary_saddle_area':str(base),'exact_box_maximum':str(val),
            'maximizers':[[str(q) for q in p] for p in pts],
            'additional_face_tests':len(fixtures),
            'continuum_curvature_theorem_proved':False}


def direction2():
    B=box(F(3,2));qs=quads_for_box(F(3,2))
    singles=[area(intersection(B,[q])) for q in qs]
    assert singles==[F(8,75)]*4
    overlap=area(intersection(B,qs[:2]))
    assert overlap==F(37,448)
    # Lower and upper roofs are separated by a midline neighborhood.
    for lo in range(2):
        for up in range(2,4):
            assert area(intersection(B,[qs[lo],qs[up]]))==0
    exact=remaining(B,qs)
    exact2,_=vertical_area(F(3,2),qs)
    assert exact==exact2==F(20807,16800)
    unsafe=area(B)-sum(singles)
    assert unsafe==F(161,150)<exact
    dual=area(B)-F(16,75)
    assert dual==F(193,150)>exact
    # Every outer vertex survives, so this is its actual finite hull.
    for p in B:
        for q in qs:
            assert not all(a*p[0]+b*p[1]<c for a,b,c in q)
    return {'single_forbidden_area':str(singles[0]),'same_turn_overlap':str(overlap),
            'true_finite_envelope_area':str(exact),
            'invalid_unweighted_upper_claim':str(unsafe),
            'optimal_constant_weight_dual_upper':str(dual),
            'constant_weight_gap':str(dual-exact),
            'four_angle_only_not_full_motion':True,
            'independent_area_algorithms_agree':True}


def direction3():
    center=F(12,5);rad=F(1,20);width=center+rad
    original=quads_for_box(center)
    robust=[[(a,b,c-rad) for a,b,c in q] for q in original]
    bound=remaining(box(width),robust)
    second,cert=vertical_area(width,robust)
    assert bound==second==F(709,480)<F(8,5)
    wing=F(5,12)+F(1,4)+F(3,64)
    assert 2*wing+rad==bound
    # A wider offset box loses this exclusion; record instead of asserting it.
    bigrad=F(1,10)
    larger=[[(a,b,c-bigrad) for a,b,c in q] for q in original]
    not_excluded=remaining(box(center+bigrad),larger)
    assert not_excluded==F(117,70)>F(8,5)
    return {'center_width':str(center),'offset_radius':str(rad),
            'containing_box_width':str(width),'independent_offset_count':8,
            'certified_all_box_area_upper':str(bound),
            'margin_below_8_over_5':str(F(8,5)-bound),
            'larger_radius_nonexclusion':str(not_excluded),
            'independent_area_algorithms_agree':True,
            'vertical_certificate':cert,
            'global_parameter_covering_complete':False}


def allowance(p,q,e):
    a=math.acos(p);b=math.acos(q)
    if e<=a+b:return 0.0
    return .5*((2*p*q-math.cos(e)*(p*p+q*q))/math.sin(e)
               -p*math.sqrt(max(0.,1-p*p))-q*math.sqrt(max(0.,1-q*q))-e+a+b)


def simpson(f,a,b,n=1024):
    h=(b-a)/n
    return h/3*(f(a)+f(b)+4*sum(f(a+i*h) for i in range(1,n,2))
                +2*sum(f(a+i*h) for i in range(2,n,2)))


def direction4():
    params=[(1.,1.,.2),(1.,1.,.5),(.98,1.,.3),(.98,.98,.3),
            (.98,.98,.5),(.95,.99,.6),(.96,1.,2*math.atan(.2)),
            (.8,.8,math.atan2(24,7)),(.8,1.,.5)]
    rows=[]
    for p,q,e in params:
        value=allowance(p,q,e)
        a=math.acos(p);b=math.acos(q)
        if e<=a+b:
            quadrature=0.
        else:
            t=math.atan2(q-p*math.cos(e),p*math.sin(e))
            quadrature=.5*(simpson(lambda x:p*p/math.cos(x)**2-1,a,t)
                           +simpson(lambda x:q*q/math.cos(e-x)**2-1,t,e-b))
        unit=math.tan(e/2)-e/2
        assert abs(value-quadrature)<2e-11
        assert -2e-14<=value<=unit+2e-14
        rows.append({'p':p,'q':q,'missing_angle':e,'new_allowance':value,
                     'unit_strip_allowance':unit,'quadrature':quadrature})
    assert allowance(.98,.98,.3)==0
    return {'prescribed_cases':rows,'quadrature_certified':False,
            'formula_proof_in_note_not_numerical':True}


def run():
    start=perf_counter()
    result={'D1':direction1(),'D2':direction2(),'D3':direction3(),'D4':direction4()}
    result.update(status='all_prescribed_checks_passed',
                  internal_seconds=perf_counter()-start,python=platform.python_version(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  used_ci_or_lean=False,global_optimality_proved=False)
    # Git blob identity can be reconstructed without executing git.
    raw=Path(__file__).read_bytes()
    result['source_git_blob_sha']=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ns=ap.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if ns.output:ns.output.write_text(text,encoding='utf-8')
    print(text,end='')
