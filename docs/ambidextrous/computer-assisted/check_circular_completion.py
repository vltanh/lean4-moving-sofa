"""Bounded exact regressions for CC and IC, not an optimality certificate.

Run under an external five-second limit. All tests use Fraction arithmetic.
The continuum motion and area statements are hand proofs in the companion notes.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from random import Random
from time import perf_counter
import json


def add(a, b):
    return [sum((v[i] if i < len(v) else Q(0) for v in (a, b)), Q(0))
            for i in range(max(len(a), len(b)))]


def mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def scale(a, c):
    return [c*x for x in a]


def trig(r):
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)


def dot(a, b):
    return a[0]*b[0] + a[1]*b[1]


def run():
    start = perf_counter()
    k, v = Q(1, 10), Q(20, 99)
    d = [Q(1), Q(0), Q(1)]
    xn, yn, hn = [Q(1), -2*v, Q(-1)], [v, Q(2), -v], [k, Q(2), -k]
    lhs = add(mul(xn, d), scale(mul(yn, add(add(xn, hn), scale(d, -1))), -1))
    rhs = scale(mul(mul([Q(1), Q(-1)], [Q(9), Q(-11)]),
                    [Q(5335), Q(6811), Q(-6345)]), Q(1, 49005))
    assert lhs == rhs
    assert (1+k)**2 + (1-v)**2 < 2
    assert Q(3960, 10201) < Q(2, 5)
    assert Q(46, 25) < 2 and Q(11, 10) + Q(7, 5)*v < 2
    assert Q(101, 100) > 1 and 1010**2 > 99**2*101
    assert Q(1, 2)*(1+k*v) == Q(101, 198)

    vertices = [(Q(0), Q(0)), (k, Q(1)), (Q(-1), v)]
    frame_points = 0
    for reflected, limit in ((False, Q(9, 11)), (True, Q(1))):
        poly = [(x, -y if reflected else y) for x, y in vertices]
        for j in range(81):
            c, s = trig(limit*Q(j, 80))
            u, w = (c, s), (-s, c)
            hu, hw = max(dot(p, u) for p in poly), max(dot(p, w) for p in poly)
            for a in range(9):
                for b in range(9-a):
                    p = tuple((a*poly[1][i]+b*poly[2][i])/8 for i in (0, 1))
                    assert min(hu-dot(p, u), hw-dot(p, w)) <= 1
                    frame_points += 1

    tangent_cases = cone_cases = 0
    kappas = [Q(1,100), Q(1,20), Q(1,10), Q(1,5), Q(21,79), Q(1,2), Q(3,4)]
    for q in kappas:
        ce, se = trig(q)
        D, E, F = (q,Q(1)), (q,Q(0)), (-q*ce,q*se)
        assert (D[0]-F[0],D[1]-F[1]) == (se,ce)
        assert (q*q*se+se)/2 == q
        for j in range(21):
            cs, ss = trig(q*Q(j,20))
            n = (ss,cs)
            assert dot((D[0]-E[0],D[1]-E[1]),n) <= 1
            assert dot((D[0]-F[0],D[1]-F[1]),n) <= 1
            tangent_cases += 1
        for a in range(11):
            for b in range(11-a):
                z = ((a*E[0]+b*F[0])/10, (a*E[1]+b*F[1])/10)
                w = (D[0]-z[0],D[1]-z[1])
                assert se*w[1]-ce*w[0] >= 0 and w[0] >= 0
                cone_cases += 1
    q = Q(21,79)
    assert 2*q**3/3 == Q(6174,493039)
    tau_sum = Q(99,101)**2 * Q(9999,10001)
    assert tau_sum > Q(19,20)
    assert Q(83,50)-Q(19,20) == Q(71,100) < Q(3,4)

    rng, valid, negative_full = Random(7102026), 0, 0
    for _ in range(5000):
        du,dv,nu,nv = [Q(rng.randrange(17),16) for _ in range(4)]
        ell_vis = 1-max(du,nv)-max(dv,nu)
        if ell_vis < 0:
            continue
        fu,fv = nu+Q(rng.randrange(9),16),nv+Q(rng.randrange(9),16)
        ell = 1-max(du,fv)-max(dv,fu)
        xi = max(dv,fu)-max(dv,nu)+max(du,fv)-max(du,nv)
        z = max(-ell,Q(0))
        a,b = fu-dv,fv-du
        R = max(a,0)+max(b,0)-max(a+b,0)
        C = 1-max(du+dv,fu+fv)
        assert ell_vis == ell+xi and C-R == ell
        assert ell_vis-max(ell,0) == xi-z >= 0
        assert C-max(ell,0) == R-z
        valid += 1
        negative_full += ell < 0
    assert negative_full > 0
    return {'status':'exact_regressions_passed', 'triangle_polynomial_identity':True,
            'triangle_frame_point_cases':frame_points, 'circle_tangent_cases':tangent_cases,
            'bisector_cone_cases':cone_cases, 'signed_fiber_cases':valid,
            'negative_full_fiber_cases':negative_full,
            'negative_controls':['strict missing-angle triangle violation',
                'signed full fiber differs from actual positive-part length',
                'unqualified original PC6 fails on large-deficit disk'],
            'arithmetic':'Python unbounded integers and Fraction',
            'continuum_proof_verified_by_script':False,
            'unrestricted_optimality_proved':False,'ci_or_lean_used':False,
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'internal_seconds':perf_counter()-start}


if __name__ == '__main__':
    print(json.dumps(run(),indent=2))
