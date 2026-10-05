"""Independent geometry checks and negative controls for the width certificate."""
import hashlib,json,random,sys,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from exact_width import (DIRECTIONS,template_certificate,exact_area_bound,
                         verify_template_box,next_axis)
from fast_exact import area_bound_int,template_box_int,axis_int
from verify_width_complete import replay_python,replay_accelerated


def clip(poly, nx, ny, height):
    """Independent rational Sutherland-Hodgman clipping against n.p <= height."""
    if not poly:return []
    out=[];prev=poly[-1];vp=nx*prev[0]+ny*prev[1]-height
    for curr in poly:
        vc=nx*curr[0]+ny*curr[1]-height
        if (vp<=0)!=(vc<=0):
            lam=vp/(vp-vc)
            out.append((prev[0]+lam*(curr[0]-prev[0]),prev[1]+lam*(curr[1]-prev[1])))
        if vc<=0:out.append(curr)
        prev=curr;vp=vc
    return out


def polygon_area(poly):
    if len(poly)<3:return F(0)
    return abs(sum(p[0]*q[1]-p[1]*q[0] for p,q in zip(poly,poly[1:]+poly[:1])))/2


def direct_area(low, high):
    """Exact disjoint polygon splitting, independent of vertical-grid integration."""
    polygons=[[(F(0),F(0)),(F(2),F(0)),(F(2),F(1)),(F(0),F(1))]]
    for hand in range(2):
        for j,(cn,sn,dn) in enumerate(DIRECTIONS):
            c,s=F(cn,dn),F(sn,dn);i=4*hand+2*j
            ah,bh=high[i:i+2];al,bl=low[i:i+2]
            if hand==0:n=(c,s);m=(-s,c);shift_n=shift_m=F(0)
            else:n=(c,-s);m=(-s,-c);shift_n=s;shift_m=c
            new=[]
            for poly in polygons:
                poly=clip(clip(poly,*n,ah-shift_n),*m,bh-shift_m)
                # Keep first inner half-plane, then the disjoint remainder
                # satisfying the second. Shared boundaries have zero area.
                p1=clip(poly,-n[0],-n[1],-(al-1-shift_n))
                rest=clip(poly,*n,al-1-shift_n)
                p2=clip(rest,-m[0],-m[1],-(bl-1-shift_m))
                if p1:new.append(p1)
                if p2:new.append(p2)
            polygons=new
    return sum(map(polygon_area,polygons),F(0))


def offsets(ids,depths):
    lo=[];hi=[]
    for hand in range(2):
        for j,(cn,sn,dn) in enumerate(DIRECTIONS):
            for q in range(2):
                i=4*hand+2*j+q;left=F(ids[i],1<<depths[i]);right=F(ids[i]+1,1<<depths[i])
                base=F(sn,dn) if q==0 else F(0);scale=F(2*cn,dn) if q==0 else F(cn,dn)
                lo.append(base+scale*left);hi.append(base+scale*right)
    return lo,hi


def main():
    rng=random.Random(20261005);start=time.time()
    rows,maximum,pivots,opt=template_certificate();rarray=np.array(rows,np.int64)
    checked=0;geometry_cases=0
    for case in range(1200):
        depths=[rng.randrange(14) for _ in range(8)]
        ids=[rng.randrange(1<<d) for d in depths]
        if case<400:
            depths=[rng.randrange(4,10) for _ in range(8)]
            ids=[max(0,min((1<<d)-1,int(opt[i]*(1<<d))+rng.randrange(-3,4))) for i,d in enumerate(depths)]
        ii,dd=np.array(ids,np.int64),np.array(depths,np.int64)
        n,d=exact_area_bound(ids,depths)
        if area_bound_int(ii,dd)!=(n,d):raise AssertionError('accelerator differs from big integers')
        if verify_template_box(ids,depths,rows)!=template_box_int(ii,dd,rarray):raise AssertionError('template accelerator mismatch')
        if next_axis(depths)!=axis_int(dd):raise AssertionError('bisection mismatch')
        if case<500:
            lo,hi=offsets(ids,depths);area=direct_area(lo,hi)
            if area>F(n,d):raise AssertionError('grid upper bound below independently clipped area')
            if F(n,d)-area>F(1,100000):raise AssertionError('unexpectedly large fencing error')
            geometry_cases+=1
        checked+=1
    physical=[]
    for hand in range(2):
        for j,(cn,sn,dn) in enumerate(DIRECTIONS):
            physical += [F(sn,dn)+F(2*cn,dn)*opt[4*hand+2*j],F(cn,dn)*opt[4*hand+2*j+1]]
    if direct_area(physical,physical)!=maximum:raise AssertionError('exact finite-position witness mismatch')
    bad=[b'',b'\x01',b'\x02',b'\x03',b'\xff',b'\x00',b'\x00\x01']
    rejected=0
    for data in bad:
        for checker in (replay_python,replay_accelerated):
            try:checker(data,rows)
            except ValueError:rejected+=1
            else:raise AssertionError('malformed/false tree accepted')
    r=F(149,500);candidate_lower=1+4*r*r+r-r**3/3+r**5/5-r**7/7
    if not (4*r**3+3*r-1<0 and candidate_lower>F(411,250)):raise AssertionError('candidate comparison')
    out={'integer_cross_checks':checked,'independent_polygon_checks':geometry_cases,
         'negative_controls_rejected':rejected,'exact_finite_position_witness_area':str(maximum),
         'candidate_area_rational_lower':str(candidate_lower),'target':'411/250',
         'seconds':time.time()-start,'all_passed':True,'python':sys.version,
         'inputs_are_not_continuous_motion_witnesses':True}
    Path('checks.json').write_text(json.dumps(out,indent=2)+'\n')
    Path('finite_witness.json').write_text(json.dumps({'normalized_coordinates':list(map(str,opt)),
                                                    'physical_support_offsets':list(map(str,physical)),
                                                    'exact_area':str(maximum),
                                                    'scope':'four-position relaxation only'},indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
