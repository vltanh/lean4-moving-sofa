"""Short exact full-turn checks for CGA and AS; not an optimality certificate.

All comparisons use Python Fraction. A finite angular grid does not establish
motion feasibility; the accompanying pen-and-paper proof gives the continuum
inequalities. Run under a five-second wall-clock limit. No solver, CI or Lean.
"""
from fractions import Fraction as F
from random import Random
from hashlib import sha256
from pathlib import Path
from time import perf_counter
import json,platform, argparse

def pos(x):
    return max(x,F(0))

def run():
    start=perf_counter()
    W=F(12,5); eps=F(1,20)
    assert W*W+1==F(169,25)
    assert W+eps==F(49,20)
    assert F(19,20)**2-F(169,200)==F(23,400)>0
    assert 2*2<F(9,2)  # sqrt(2)<3/2 by squaring
    frames=0
    for k in range(81):
        r=F(k,80)
        c=(1-r*r)/(1+r*r); s=2*r/(1+r*r)
        assert c>=0 and s>=0 and c*c+s*s==1
        for i in range(9):
            lam=F(i,8)
            for j in range(9):
                z=F(j,8)
                x=W*lam+eps*z
                y=1-lam
                hu=max(s,W*c)+eps*c; hv=c
                du=hu-(x*c+y*s); dv=hv-(-x*s+y*c)
                assert du>=0 and dv>=0
                assert min(du,dv)<=1,('lower',r,lam,z,du,dv)
                yy=lam
                hu2=W*c+s+eps*c;hv2=max(F(0),c-W*s)
                du2=hu2-(x*c+yy*s); dv2=hv2-(-x*s+yy*c)
                assert du2>=0 and dv2>=0
                assert min(du2,dv2)<=1,('upper',r,lam,z,du2,dv2)
                frames+=1
    # Incorrectly thickening the same diagonal by one unit fails.
    r=F(1,5); c=(1-r*r)/(1+r*r); s=2*r/(1+r*r)
    lam=z=F(1,2); wide=F(1)
    x=W*lam+wide*z;y=1-lam
    bad_u=max(s,W*c)+wide*c-(x*c+y*s)
    bad_v=c-(-x*s+y*c)
    assert bad_u>1 and bad_v>1

    rng=Random(1317); mismatch_cases=0; strict_mismatch=False
    for i in range(10000):
        du=F(rng.randrange(100),30);dv=F(rng.randrange(100),30)
        nu=F(rng.randrange(100),30);nv=F(rng.randrange(100),30)
        a=nu-dv;b=nv-du
        gap=pos(a)+pos(b)-pos(a+b)
        assert gap==min(pos(a),pos(-b))+min(pos(b),pos(-a))
        assert max(du,nv)+max(dv,nu)-max(du+dv,nu+nv)==gap
        assert gap>=0
        strict_mismatch |= gap>0
        mismatch_cases+=1
    assert strict_mismatch
    return {
        'status':'exact_regressions_passed',
        'quarter_frame_cases':frames,
        'both_turns_checked':True,
        'switching_identity_cases':mismatch_cases,
        'negative_controls':['overwide diagonal thickening rejected',
                             'mixed-cross-deficit strict mismatch detected'],
        'width':'49/20','area':'1/20',
        'scope':'finite rational regressions, not continuum full-turn verification',
        'unrestricted_full_turn_optimality_proved':False,
        'python':platform.python_version(),
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'internal_seconds':perf_counter()-start,
        'ci_or_lean_used':False}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    print(text,end='')
