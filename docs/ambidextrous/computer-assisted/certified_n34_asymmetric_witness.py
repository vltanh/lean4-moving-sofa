"""Exact 1.65 finite-mesh witness with ALL independent handed offsets.

Reads finite-mesh-n34-witness.json, 136 rational support offsets at scale
10^12 (34 frames on each hand, including exact pi/4), then computes a
CONSERVATIVE LOWER area bound for one CONNECTED component of their exact
finite hallway intersection, with a verified full midline connector.

This DOES NOT show continuous-turn feasibility or global optimality.
All mathematical decisions use directed integer arithmetic. NumPy int64
overflow is guarded, and only the final large product uses Python integers.

Run: python certified_n34_asymmetric_witness.py
"""
from pathlib import Path
from math import isqrt
from fractions import Fraction as F
import json, sys, time
import numpy as np
P = 10**12

def verify(filename=None,cells=1000000):
    start=time.perf_counter()
    if filename is None:
        filename=Path(__file__).with_name("finite-mesh-n34-witness.json")
    data=json.loads(Path(filename).read_text())
    n=data["n"]
    assert n==34 and data["scale"]==P
    p=data["offsets_scaled"]
    k=n
    assert len(p)==4*k and all(isinstance(v,int) and 0<v<3*P for v in p)
    xhalf=1300000000000
    assert cells>0 and (2*xhalf)%cells==0
    dx=2*xhalf//cells
    XL=-xhalf+dx*np.arange(cells,dtype=np.int64)
    XR=XL+dx
    root2lo=isqrt(2*P*P)
    root2hi=root2lo+1
    assert root2lo*root2lo<=2*P*P<root2hi*root2hi
    def mul_root2_scaled(v, upper):
        b=root2hi if ((v>=0)==upper) else root2lo
        num=v*b
        return -((-num)//P) if upper else num//P
    j=range(1,n)
    def cap(offset):
        ff=p[offset:offset+k];gg=p[offset+k:offset+2*k]
        U=np.full(cells,P,dtype=np.int64)
        N=np.zeros(cells,dtype=np.int64)
        for i in j:
            C=n*n-i*i;T=2*n*i;D=n*n+i*i
            f,g=ff[i-1],gg[i-1]
            assert max(abs(f),abs(g),P)*D+max(C,T)*xhalf<2**62
            # For every x in [XL,XR] an exact LOWER outer roof:
            aa=np.floor_divide(f*D-C*XR,T)
            bb=np.floor_divide(g*D+T*XL,C)
            U=np.minimum(U,np.minimum(aa,bb))
            # For every x an exact UPPER forbidden-niche roof:
            aa=np.floor_divide((f-P)*D-C*XL+T-1,T)
            bb=np.floor_divide((g-P)*D+T*XR+C-1,C)
            N=np.maximum(N,np.minimum(aa,bb))
        f,g=ff[-1],gg[-1]  # exact 45 degrees, not a rationalized normal
        f_out=mul_root2_scaled(f,False)
        g_out=mul_root2_scaled(g,False)
        f_in=mul_root2_scaled(f-P,True)
        g_in=mul_root2_scaled(g-P,True)
        U=np.minimum(U,np.minimum(f_out-XR,g_out+XL))
        N=np.maximum(N,np.minimum(f_in-XL,g_in+XR))
        return U,N
    lower_roof,lower_niche=cap(0)
    reflected_roof,reflected_niche=cap(2*k)
    top_lower=np.minimum(lower_roof,P-reflected_niche)
    bottom_upper=np.maximum(lower_niche,P-reflected_roof)
    length=np.maximum(0,top_lower-bottom_upper)
    # A cell is certified to contain (x,1/2) FOR ALL x in its interval.
    connectors=(top_lower>=P//2)&(bottom_upper<=P//2)
    indices=np.flatnonzero(connectors)
    assert len(indices)>0
    cuts=np.flatnonzero(np.diff(indices)>1)+1
    runs=np.split(indices,cuts)
    best=max(runs,key=lambda part:int(length[part].sum(dtype=np.int64)))
    lo=int(best[0]);hi=int(best[-1])+1
    # Each actual vertical fiber is a connected interval and contains 1/2.
    # Restricting to [XL[lo],XR[hi-1]] yields a connected compact witness.
    subtotal=int(length[best].sum(dtype=np.int64))
    assert 0<=subtotal<2**62
    area=F(subtotal*dx,P*P)
    target=F(33,20)
    assert area>target
    return dict(status="exact_connected_finite_witness_above_33_20",
        n=n,frames_each_hand=k,offsets=4*k,independent_handed_offsets=True,
        pi4_normals_exact_radical=True,scale=P,spatial_cells=cells,
        x_range=[str(F(-xhalf+lo*dx,P)),str(F(-xhalf+hi*dx,P))],
        midline_connected_cells=len(best),midline_component_slice_sum=subtotal,
        cell_width_scaled=dx,lower_area_fraction=str(area),
        lower_area_decimal=float(area),margin_over_33_20=str(area-target),
        proven_connected=True,fully_turning_motion_proved=False,
        global_A_F_le_165_proved=False,elapsed_seconds=time.perf_counter()-start)
if __name__=="__main__":
    count=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
    print(json.dumps(verify(cells=count),indent=2))
