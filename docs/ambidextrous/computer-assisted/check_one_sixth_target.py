"""Exact checks for SX (six fixed positions) and JT (terminal-strip transfer).

The continuum motion and gap-compression proofs are in the companion notes.
The finite tests do not establish A_F <= 33/20 or the requested 1/6 bound.
Run with an external five-second limit; only the standard library is needed.
"""
from fractions import Fraction as Q
from hashlib import sha256, sha1
from itertools import combinations
from pathlib import Path
from time import perf_counter
import json

BREAKS = [Q(0), Q(3,35), Q(3,25), Q(3,10), Q(3,5),
          Q(16,15), Q(10,7), Q(7,4)]
PROFILE = [(Q(1),Q(1,10)),(Q(-3,4),Q(1,4)),(Q(4,3),Q(0)),
           (Q(1),Q(1,10)),(Q(0),Q(7,10)),(Q(-3,4),Q(3,2)),
           (Q(-4,3),Q(7,3))]
# Lines underlying the exact min/max profile in SX, as (slope, intercept).
LINES = [(Q(0),Q(7,10)),(Q(-1),Q(19,10)),(Q(1),Q(1,10)),
         (Q(-4,3),Q(7,3)),(Q(-3,4),Q(3,2)),(Q(4,3),Q(0)),
         (Q(-3,4),Q(1,4)),(Q(3,4),Q(1,4))]


def line(ab, z):
    return ab[0]*z+ab[1]


def envelope_profile(z):
    vals=[line(ab,z) for ab in LINES]
    return min(vals[:5]+[max(vals[5],vals[6]),vals[7]])


def table_profile(z):
    for a,b,ab in zip(BREAKS,BREAKS[1:],PROFILE):
        if a <= z <= b:
            return line(ab,z)
    raise ValueError('z outside table')


def arctan_cost_upper(u):
    return u**3/3-u**5/5+u**7/7


def run():
    start=perf_counter(); count=0
    def require(p, message):
        nonlocal count
        if not p:
            raise AssertionError(message)
        count+=1

    # Every line ordering is constant between these exact crossing points.
    events=set(BREAKS)
    for (a,b),(c,d) in combinations(LINES,2):
        if a != c:
            crossing=(d-b)/(a-c)
            if 0 <= crossing <= BREAKS[-1]:
                events.add(crossing)
    events=sorted(events)
    for z in events:
        require(table_profile(z)==envelope_profile(z), 'profile at boundary')
    for a,b in zip(events,events[1:]):
        require(table_profile((a+b)/2)==envelope_profile((a+b)/2),
                'profile on fixed-order affine cell')
    for i,(a,b,ab) in enumerate(zip(BREAKS,BREAKS[1:],PROFILE)):
        require(line(ab,a)>=0 and line(ab,b)>=0, 'nonnegative profile')
        require(line(ab,(a+b)/2)>0, 'positive interior fiber')
        if i+1<len(PROFILE):
            require(line(ab,b)==line(PROFILE[i+1],b), 'continuous profile')
    ar=2*sum(a*(v*v-u*u)/2+b*(v-u)
             for u,v,(a,b) in zip(BREAKS,BREAKS[1:],PROFILE))
    require(ar==Q(5,3), 'exact six-frame witness area')
    require(Q(7,5)**2<2, 'incoming height less than one')
    require(7**2<50, 'extra hallway widths less than one')
    require(Q(17,6)**2>8, '5/3 exceeds requested target')

    # The existing feasible-reference area has a rational lower bound >49/30.
    y=Q(59,200)
    require(4*y**3+3*y-1<0, 'lower cubic-root endpoint')
    require(4*Q(3,10)**3+3*Q(3,10)-1>0, 'upper cubic-root endpoint')
    reference_lower=1+4*y*y+y-y**3/3
    require(reference_lower==Q(39229021,24000000)>Q(49,30),
            'feasible reference lower bound')

    # Unconditional additive gap JT.2, given the hand geometric transfer.
    u=Q(171,500)
    require(Q(49,30)-(u+1/u)/2==Q(59,171000)>0,
            'uniform half-angle bound')
    gap=arctan_cost_upper(u)
    require(gap<Q(1,80), 'uniform completion gap')

    # Conditional 1/6 target JT.3: no assertion of the unproved full-turn premise.
    a0=Q(41543,25000); u0=Q(1673,5000); full_target=Q(33,20)
    require(a0-(u0+1/u0)/2==Q(8233,83650000)>0,
            'target half-angle upper bound')
    cost=arctan_cost_upper(u0)
    margin=a0-full_target-cost
    require(margin==Q(1117653653116181013187,234375000000000000000000000)>0,
            'conditional completion budget strictly paid')
    target_margin=8-(a0+Q(7,6))**2
    require(target_margin==Q(1287359,5625000000)>0,
            'conditional rational bound below 1/6 target')
    raw=Path(__file__).read_bytes()
    return {
        'status':'exact_rational_checks_passed','checks':count,
        'profile_affine_cells':len(events)-1,
        'six_frame_witness_area':str(ar),
        'uniform_transfer_gap_upper':str(gap),
        'conditional_full_turn_premise':str(full_target),
        'conditional_general_upper':str(a0),
        'conditional_budget_margin':str(margin),
        'seconds':perf_counter()-start,
        'source_sha256':sha256(raw).hexdigest(),
        'source_git_blob_sha':sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        'full_turn_33_20_proved':False,
        'unconditional_one_sixth_bound_proved':False,
        'continuum_proofs_verified_by_finite_checks':False,
        'ci_or_lean_used':False,
    }

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
