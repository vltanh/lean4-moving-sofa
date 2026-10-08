"""Exact finite regressions of the analytic midpoint-strip proof.
No finite tests establish the universal bound; that is proved in the note.
All polygon areas below use Fraction; d is rational and sqrt(2) is not rounded.
"""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256, sha1
from pathlib import Path
from time import perf_counter
import json

def clip(poly,A,B,C):
    if not poly:return []
    ans=[]
    p=poly[-1]; fp=A*p[0]+B*p[1]-C
    for z in poly:
        fz=A*z[0]+B*z[1]-C
        if (fp<=0)!=(fz<=0):
            t=fp/(fp-fz)
            ans.append((p[0]+t*(z[0]-p[0]),p[1]+t*(z[1]-p[1])))
        if fz<=0:ans.append(z)
        p,fp=z,fz
    return ans

def rect_band(x0,x1,y0,y1,k,d):
    if x1<=x0 or y1<=y0:return Q(0)
    p=[(x0,y0),(x1,y0),(x1,y1),(x0,y1)]
    p=clip(clip(p,Q(1),Q(1),k+d),Q(-1),Q(-1),-k)
    if not p:return Q(0)
    return abs(sum(p[i][0]*p[(i+1)%len(p)][1]-p[(i+1)%len(p)][0]*p[i][1] for i in range(len(p))))/2

def envelope(P,R,k,d):
    # Outer rectangle minus two opposed forbidden rectangles; overlap restored.
    a=rect_band(Q(0),P,Q(0),R,k,d)
    a-=rect_band(Q(0),max(Q(0),P-1),Q(0),max(Q(0),R-1),k,d)
    a-=rect_band(Q(1),P,Q(1),R,k,d)
    a+=rect_band(Q(1),P-1,Q(1),R-1,k,d)
    return a

def run():
    st=perf_counter(); n=0;eq=0;tail=0
    values=list(map(Q,['1/2','1','3/2','2','5/2','4']))
    for P,R,d in product(values,values,[Q(1,2),Q(3,4),Q(1),Q(7,5),Q(3,2),Q(2)]):
        for k in [Q(-1),Q(0),(P+R-d)/2,P-R,P,R]:
            a=envelope(P,R,k,d)
            assert 0<=a<=2*d-d*d/2,(P,R,k,d,a)
            n+=1
    for d in [Q(1,2),Q(3,4),Q(1),Q(7,5),Q(3,2),Q(2)]:
        a=envelope(Q(2),Q(2),2-d/2,d)
        assert a==2*d-d*d/2
        eq+=1
        for q in [Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)]:
            # Optimal central strip on a 1 by q corner rectangle.
            z=rect_band(Q(0),Q(1),Q(0),q,(1+q-d)/2,d)
            expected=q*d if d<=1-q else q-max(Q(0),1+q-d)**2/4
            assert z==expected
            F=d*(1-q)+2*expected
            assert F<=2*d-d*d/2
            tail+=1
    # The un-subtracted outer rectangle is not bounded by the theorem.
    assert rect_band(Q(0),Q(4),Q(0),Q(4),Q(13,4),Q(3,2))>Q(15,8)
    src=Path(__file__).read_bytes()
    return dict(status='exact_regressions_passed',offset_band_cases=n,
                sharp_equalities=eq,corner_concentration_checks=tail,
                negative_controls=['forgetting_forbidden_rectangles_rejected'],
                internal_seconds=perf_counter()-st,source_sha256=sha256(src).hexdigest(),
                source_git_blob_sha=sha1(b'blob '+str(len(src)).encode()+b'\0'+src).hexdigest(),
                continuum_verified_by_code=False,sharp_romik_bound_proved=False)
if __name__=='__main__':print(json.dumps(run(),indent=2))
