"""Exact finite regressions for GC1; not a continuum or optimality certificate.
Run under an external five-second limit. Uses the standard library only.
"""
from fractions import Fraction as Q
from hashlib import sha256, sha1
from pathlib import Path
from time import perf_counter
import json
import platform


def collapse(x, a, b):
    return x - min(max(x-a, Q(0)), b-a)


def run():
    start = perf_counter()
    normals = set()
    for c,s in [(Q(1),Q(0)),(Q(0),Q(1)),(Q(3,5),Q(4,5)),
                (Q(5,13),Q(12,13)),(Q(7,25),Q(24,25))]:
        for sc in [-1,1]:
            for ss in [-1,1]:
                normals.add((sc*c,ss*s))
    maps = [lambda x:x, lambda x:Q(0), lambda x:x/2,
            lambda x:collapse(x,Q(-1,2),Q(1,2)),
            lambda x:collapse(collapse(x,Q(-1),Q(-1,2)),Q(0),Q(1,3))]
    total=safe=0
    for H in [Q(1),Q(3,5)]:
        points=[(Q(i,3),H*Q(j,6)) for i in range(-6,7) for j in range(7)]
        for T in maps:
            for nx,ny in normals:
                assert nx*nx+ny*ny==1
                old_h=max(nx*x+ny*y for x,y in points)
                new_h=max(nx*T(x)+ny*y for x,y in points)
                for x,y in points:
                    old=old_h-nx*x-ny*y
                    new=new_h-nx*T(x)-ny*y
                    assert new<=max(old,H*abs(ny))
                    if old<=1:
                        assert new<=1
                        safe+=1
                    total+=1
    # A hypothesis violation must not be accepted as the theorem.
    # H=2, collapse x: old safe depth 1 becomes 8/5.
    assert -Q(3,5)+Q(4,5)*2==1 and Q(4,5)*2>1
    # Nonmonotone reflection with H=1 can also destroy a safe wall.
    assert -Q(3,5)+Q(4,5)<=1 and Q(3,5)+Q(4,5)>1
    # Horizontal expansion is not a nonexpansive compression.
    assert Q(1)<=1 and Q(2)>1
    # Two separated rectangles, whose compressed fibers need a vertical join.
    widths=[Q(1,5),Q(1,5)];heights=[Q(2,5),Q(2,5)]
    original_area=sum(w*h for w,h in zip(widths,heights))
    assert original_area==Q(4,25)
    assert collapse(Q(1),Q(1,5),Q(1))==Q(1,5)
    assert collapse(Q(6,5),Q(1,5),Q(1))==Q(2,5)
    source=Path(__file__).read_bytes()
    return dict(status='exact_finite_checks_passed',depth_checks=total,
                safe_depth_checks=safe,normals=len(normals),maps=len(maps),
                negative_controls=['height_above_one','nonmonotone_map','expansive_map'],
                rectangle_area=str(original_area),python=platform.python_version(),
                internal_seconds=perf_counter()-start,
                source_sha256=sha256(source).hexdigest(),
                source_git_blob_sha=sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest(),
                continuum_proof_verified_by_script=False,
                full_turn_optimality_proved=False,ci_or_lean_used=False)


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
