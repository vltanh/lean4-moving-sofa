"""Non-certifying diagnostics for saturated-axis-cut-area.md.

Standard-library only. Closed cap formulas are compared with direct vertical
slice integration. Floating-point observations are not a proof of a continuum
statement. No Lean, Lake, CI, or network access is used.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Callable


def integrate(f: Callable[[float], float], a: float, b: float,
              tol: float = 2e-15, depth: int = 24) -> float:
    """Adaptive Simpson quadrature, used only as a diagnostic."""
    if b <= a:
        return 0.0
    def rec(l: float, r: float, fl: float, fm: float, fr: float,
            whole: float, eps: float, remaining: int) -> float:
        m = (l + r) / 2
        lm, rm = (l + m) / 2, (m + r) / 2
        flm, frm = f(lm), f(rm)
        left = (m-l) * (fl + 4*flm + fm) / 6
        right = (r-m) * (fm + 4*frm + fr) / 6
        error = left + right - whole
        if abs(error) <= 15*eps:
            return left + right + error/15
        if remaining == 0:
            raise RuntimeError('Diagnostic quadrature did not meet tolerance')
        return (rec(l,m,fl,flm,fm,left,eps/2,remaining-1) +
                rec(m,r,fm,frm,fr,right,eps/2,remaining-1))
    fa, fm, fb = f(a), f((a+b)/2), f(b)
    whole = (b-a)*(fa+4*fm+fb)/6
    return rec(a,b,fa,fm,fb,whole,tol,depth)


def root_and_face_length() -> tuple[float, float]:
    lo, hi = 0.0, 1.0
    for _ in range(70):
        y = (lo+hi)/2
        if 4*y*y*y+3*y < 1:
            lo = y
        else:
            hi = y
    y = (lo+hi)/2
    return y, math.sqrt(1+y*y)/(3*y)


def circle_floor(d: float) -> float:
    """1/2-sqrt(1/4-d^2), rationalized to avoid cancellation."""
    return 2*d*d/(1+math.sqrt(max(0.0,1-4*d*d)))


def check() -> dict:
    y,m = root_and_face_length()
    limit = (1+2*math.sqrt(2))*m**1.5/3
    rows = []
    for z in (0.04,0.02,0.01,0.005,0.0025):
        sz,cz = math.sin(z), math.cos(z)
        tau = 2*math.sin(z/2)**2/(2*m+sz)
        delta = math.atan(tau)
        yp = math.cos(z/2)**2
        D = math.sqrt(1-yp*yp)
        cap = lambda v: (v-math.sin(v)*math.cos(v))/4
        top_closed = cap(delta)+cap(z-delta)
        old_closed = (2*sz-sz*cz-z)/8
        new_closed = yp*(sz-D)-(sz*cz+z-D*yp-math.acos(yp))/2
        gain_closed = old_closed-new_closed
        # The upper loss is two integrals of the actual cut-minus-circle roof.
        right = integrate(lambda d: tau*(m+d)-circle_floor(d),
                          math.sin(2*delta-z)/2, sz/2)
        left = integrate(lambda x: tau*x-circle_floor(x),
                         0.0,tau/(1+tau*tau))
        top_slice = left+right
        # For the lower gain, x denotes displacement from the old right tip.
        xb, xz, xp = -sz/2, sz/2-D, sz/2
        def new_floor(x: float) -> float:
            w = xp-x
            sq = math.sqrt(max(0.0,1-w*w))
            return (w*w-D*D)/(yp+sq)
        gain_slice = (integrate(lambda x: circle_floor(x)-new_floor(x),xb,xz)
                      + integrate(circle_floor,xz,0.0))
        gap = top_slice-gain_slice
        discrepancies = [abs(top_slice-top_closed),abs(gain_slice-gain_closed)]
        if max(discrepancies)>1e-11:
            raise AssertionError('Closed form and independent slice integral disagree')
        if gap <= 0 or gain_slice <= 0:
            raise AssertionError('Unexpected sign in diagnostic sample')
        rows.append(dict(z=z,tau=tau,upper_loss=top_slice,lower_gain=gain_slice,
                         deficit=gap,scaled_deficit=gap/tau**1.5,
                         absolute_formula_discrepancies=discrepancies))
    if abs(rows[-1]['scaled_deficit']-limit) >= abs(rows[0]['scaled_deficit']-limit):
        raise AssertionError('Sampled ratios do not approach the proposed limit')
    return dict(status='diagnostics_passed',is_proof_certificate=False,
                scope='Specified axis-cut family only; no global optimality inference',
                python=platform.python_version(),candidate_root=y,face_length=m,
                predicted_limit=limit,observations=rows,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                ci_or_lean_used=False)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(check(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
