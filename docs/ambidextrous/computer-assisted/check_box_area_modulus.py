"""Finite exact-rational regression of BH1 (not a proof of its all-offset statement).

The hand proof is in box-area-lipschitz-hand-certificate.md.
No huge certificate, dependencies, optimization or compilation.
"""
from fractions import Fraction as Q
from hashlib import sha256, sha1
from pathlib import Path
from time import perf_counter
import json

COORDS = [
    ((0, 4, 3), (0, -3, 4)),
    ((0, 3, 4), (0, -4, 3)),
    ((3, 4, -3), (4, -3, -4)),
    ((4, 3, -4), (3, -4, -3)),
]
# All affine coordinate triples have common denominator 5.
ROOT = [(Q(-1), Q(18, 5)), (Q(-1), Q(-1, 5)),
        (Q(-1), Q(14, 5)), (Q(-1), Q(-2, 5)),
        (Q(-2, 5), Q(18, 5)), (Q(-1), Q(-1, 5)),
        (Q(-1, 5), Q(14, 5)), (Q(-1), Q(-2, 5))]
COEFF = [Q(19,5), Q(23,5), Q(23,5), Q(19,5),
         Q(19,5), Q(23,5), Q(23,5), Q(19,5)]


def val(fn, p):
    return (fn[0] + fn[1]*p[0] + fn[2]*p[1]) / 5


def clip(poly, fn, limit, sign):
    if not poly:
        return []
    s = [sign * (val(fn, p) - limit) for p in poly]
    out = []
    for i, p in enumerate(poly):
        j = (i+1)%len(poly)
        q = poly[j]
        if s[i] >= 0:
            out.append(p)
        if s[i] * s[j] < 0:
            t = s[i] / (s[i]-s[j])
            out.append((p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1])))
    clean=[]
    for p in out:
        if not clean or clean[-1]!=p:
            clean.append(p)
    if len(clean)>1 and clean[-1]==clean[0]:
        clean.pop()
    return clean


def area(poly):
    if len(poly)<3:
        return Q(0)
    twice = sum(p[0]*q[1]-p[1]*q[0]
                for p,q in zip(poly, poly[1:]+poly[:1]))
    return abs(twice)/2


def envelope_area(box):
    cur = [[(Q(0),Q(0)), (Q(5),Q(0)), (Q(5),Q(1)),(Q(0),Q(1))]]
    for j, (f,g) in enumerate(COORDS):
        (a,b),(c,d) = box[2*j],box[2*j+1]
        new=[]
        for poly in cur:
            poly = clip(clip(poly, f, b+1, -1),g,d+1,-1)
            if not poly:
                continue
            first = clip(poly,f,a,+1)
            if first:
                new.append(first)
            second = clip(clip(poly,f,a,-1),g,c,+1)
            if second:
                new.append(second)
        cur = new
        if not cur:
            break
    return sum(map(area, cur)), len(cur)


def run():
    start=perf_counter()
    checks=0
    strict=0
    largest_ratio=Q(0)
    values=[]
    # Generate 32 distinct rational centers and boxes inside the canonical root.
    for seed in range(32):
        box=[]
        for j,(lo,hi) in enumerate(ROOT):
            w=hi-lo
            center=lo+w*Q((7*seed+5*j+3)%31 + 1, 33)
            half=min(w/Q(30+(seed%5)*6),center-lo,hi-center)
            box.append((center-half,center+half))
        mid=[((a+b)/2,(a+b)/2) for a,b in box]
        expanded,pieces=envelope_area(box)
        central,_=envelope_area(mid)
        penalty=sum(c*(hi-lo) for c,(lo,hi) in zip(COEFF,box))
        max_w=max(hi-lo for lo,hi in box)
        assert central <= expanded <= central+penalty
        assert penalty <= Q(168,5)*max_w
        assert 0 <= expanded <= Q(5)
        checks+=3
        if expanded>central:
            strict+=1
        ratio=(expanded-central)/penalty if penalty>0 else Q(0)
        largest_ratio=max(largest_ratio,ratio)
        if seed in (0,7,16,31):
            values.append(dict(seed=seed,center_area=str(central),
                               enlarged_area=str(expanded),
                               exact_penalty=str(penalty),
                               pieces=pieces,area_over_penalty=float(ratio)))
    # Published rational four-hallway near-extremizer, translated by +3 in x.
    witness_center=[Q(1263,500),Q(-543,400),Q(9661,5000),Q(-18603,10000)]*2
    witness_point=[(a,a) for a in witness_center]
    witness_area,witness_pieces=envelope_area(witness_point)
    assert witness_pieces==7
    assert witness_area==Q(29092957301,16800000000)
    delta=Q(1,2000)
    witness_box=[(a-delta/2,a+delta/2) for a in witness_center]
    witness_enlarged,_=envelope_area(witness_box)
    hand_upper=witness_area+Q(168,5)*delta
    assert witness_area<=witness_enlarged<=hand_upper<Q(7,4)
    checks+=3
    raw=Path(__file__).read_bytes()
    return dict(result='exact_rational_regression_passed',cases=32,checks=checks,
                strict_enlargements=strict,largest_realized_penalty_fraction=float(largest_ratio),
                sample=values,witness=dict(center_area=str(witness_area),exact_enlarged_area=str(witness_enlarged),hand_upper=str(hand_upper),strict_below=str(Q(7,4)-hand_upper)),execution_seconds=round(perf_counter()-start,6),
                source_sha256=sha256(raw).hexdigest(),
                source_git_blob_sha=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
                hand_proof_verified_by_finite_tests=False,global_area_M_proved=False)

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
