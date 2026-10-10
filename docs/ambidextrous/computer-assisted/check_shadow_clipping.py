"""Independent local diagnostics for repair-shadow-clipping-obstruction.md.

The tests compare ordinary slice areas, a support-functional deficit and the
clipping correction. They are NOT a global proof or an interval certificate.
Only the Python standard library is used; no CI or Lean is invoked.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Callable


def integral(f: Callable[[float], float], a: float, b: float,
             tolerance: float = 1e-20, depth: int = 28) -> float:
    if not a < b:
        return 0.0
    def rec(l, r, fl, fm, fr, whole, eps, remaining):
        m=(l+r)/2
        flm,frm=f((l+m)/2),f((m+r)/2)
        left=(m-l)*(fl+4*flm+fm)/6
        right=(r-m)*(fm+4*frm+fr)/6
        error=left+right-whole
        if abs(error)<=15*eps:
            return left+right+error/15
        if remaining==0:
            raise RuntimeError('Quadrature did not meet diagnostic tolerance')
        return rec(l,m,fl,flm,fm,left,eps/2,remaining-1)+rec(m,r,fm,frm,fr,right,eps/2,remaining-1)
    fa,fm,fb=f(a),f((a+b)/2),f(b)
    return rec(a,b,fa,fm,fb,(b-a)*(fa+4*fm+fb)/6,tolerance,depth)


def circle_floor(x: float) -> float:
    return 2*x*x/(1+math.sqrt(1-4*x*x))


def unit_floor(x: float) -> float:
    return x*x/(1+math.sqrt(1-x*x))


def one_scale(z: float) -> dict:
    if not 0<z<=0.04:
        raise ValueError('Diagnostic restricted to 0 < z <= 0.04')
    s=math.sin(z)
    Y=math.cos(z/2)**2
    D=math.sin(z/2)*math.sqrt(1+Y)
    a=z/2
    b=s/2-D
    d1=math.atan2(D,Y)
    # Find the intersection of the two actual upper-boundary circles.
    lo,hi=b,0.0
    for _ in range(80):
        x=(lo+hi)/2
        if unit_floor(x-b)<circle_floor(x):lo=x
        else:hi=x
    xi=(lo+hi)/2
    clipping=integral(lambda x:unit_floor(x-b),b,xi)+integral(circle_floor,xi,0.0)
    top_loss=integral(lambda x:unit_floor(x-b)-circle_floor(x),xi,s/2)
    def lower_new(x):
        w=s/2-x
        return (w*w-D*D)/(Y+math.sqrt(1-w*w))
    lower_gain=(integral(lambda x:circle_floor(x)-lower_new(x),-s/2,b)
                +integral(circle_floor,b,0.0))
    ordinary_deficit=top_loss-lower_gain
    def energy1(d):
        v=b*math.sin(d)+math.sin(d/2)**2
        vp=-b*math.cos(d)-.5*math.sin(d)
        return vp*vp-v*v
    def energy2(d):
        v=-math.sin(z/2)**2+.5*s*math.sin(d)-2*(Y-.5)*math.sin(d/2)**2
        vp=-.5*s*math.cos(d)+(Y-.5)*math.sin(d)
        return vp*vp-v*v
    functional_deficit=integral(energy1,0.0,d1)+integral(energy2,d1,z)
    error=functional_deficit-ordinary_deficit-clipping
    if abs(error)>1e-13*max(a**3,1e-8):
        raise AssertionError('Independent ordinary and functional area calculations disagree')
    if not 0<ordinary_deficit<functional_deficit or clipping<=0:
        raise AssertionError('Counterexample sign failed at a diagnostic scale')
    return dict(z=z,ordinary_deficit=ordinary_deficit,functional_deficit=functional_deficit,
                clipping_error=clipping,identity_discrepancy=error,
                scaled_ordinary_deficit=ordinary_deficit/a**3,
                scaled_functional_deficit=functional_deficit/a**3,
                scaled_clipping=clipping/a**3)


def check() -> dict:
    observations=[one_scale(z) for z in (.04,.02,.01,.005,.0025)]
    limits=dict(ordinary=(37-26*math.sqrt(2))/3,
                functional=math.sqrt(2)-4/3,
                clipping=(29*math.sqrt(2)-41)/3)
    for key,value in limits.items():
        field={'ordinary':'scaled_ordinary_deficit','functional':'scaled_functional_deficit','clipping':'scaled_clipping'}[key]
        if abs(observations[-1][field]-value)>=abs(observations[0][field]-value):
            raise AssertionError('Diagnostic ratios fail the convergence check')
    negative_controls=0
    for z in (0,-.01,.05):
        try:one_scale(z)
        except ValueError:negative_controls+=1
        else:raise AssertionError('Invalid scale was accepted')
    return dict(status='diagnostics_passed',is_proof_certificate=False,
                ordinary_area_enclosure=False,unrestricted_optimality_proved=False,
                observations=observations,expected_limits=limits,
                invalid_scales_rejected=negative_controls,python=platform.python_version(),
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                ci_or_lean_used=False)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
    args=p.parse_args();text=json.dumps(check(),indent=2)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    print(text,end='')
