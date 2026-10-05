"""Post-solve contact discovery without a Gerver reference or phase ansatz.

For each point, continuous-angle forbidden-wedge penetration is minimized
cell by cell using sinusoidal stationary points and wall-switch candidates.
Results use floating point, not interval arithmetic. Contact thresholds and
hinge fits are diagnostics, not certified phase boundaries.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, least_squares

from q_experiment import PI, QProblem, unit


def periodic_candidates(angle: float, a: float, b: float) -> list[float]:
    first = int(np.ceil((a-angle)/PI))
    last = int(np.floor((b-angle)/PI))
    return [angle+k*PI for k in range(first, last+1)]


class ContactProbe:
    def __init__(self, problem: QProblem, x: np.ndarray):
        self.p = problem
        x = np.asarray(x, dtype=float)
        if x.shape != (problem.size,) or not np.all(np.isfinite(x)):
            raise ValueError('expected a finite full solution vector')
        self.z = np.r_[x, 1.]
        self.vertices = problem.vertices @ self.z

    def wedge_penetration(self, point: np.ndarray, exclude: tuple[float,float] | None = None
                          ) -> tuple[float, float]:
        """min_s max(1+<point-A_i,u_s>,1+<point-C_i,v_s>).

A negative value means that point lies strictly inside some forbidden wedge.
With exclude, the closed complement of that angular interval is searched;
this removes the point's own corner contact when looking for a second contact.
"""
        p = self.p
        best, angle = np.inf, np.nan
        for i in range(p.m):
            lo, hi = p.angles[i:i+2]
            intervals = [(lo, hi)]
            if exclude is not None:
                a, b = exclude
                intervals = [(lo, min(hi,a)), (max(lo,b),hi)]
            av = point-self.vertices[0,i]
            w = point-self.vertices[0,i+p.m]
            bv = np.array([w[1],-w[0]])
            difference = av-bv
            for a, b in intervals:
                if b < a:
                    continue
                candidates = [a,b]
                for vector in (av,bv):
                    candidates += periodic_candidates(float(np.arctan2(vector[1],vector[0])),a,b)
                if np.linalg.norm(difference)>1e-14:
                    candidates += periodic_candidates(
                        float(np.arctan2(difference[1],difference[0])+PI/2),a,b)
                for s in candidates:
                    value = 1+max(float(av@unit(s)),float(bv@unit(s)))
                    if value<best:
                        best,angle=value,s
        return best,angle

    def corner_exposure(self, exclusion: float = .2, subdivisions: int = 64) -> list[dict]:
        if not 0<exclusion<PI/4 or subdivisions<8:
            raise ValueError('require 0<exclusion<pi/4 and subdivisions>=8')
        def value(t: float) -> float:
            point=self.p.corner_rows(t)@self.z
            return self.wedge_penetration(point,(t-exclusion,t+exclusion))[0]
        ts=np.linspace(0,PI/2,subdivisions+1)
        ys=np.array([value(t) for t in ts])
        roots=[]
        for i in range(subdivisions):
            if ys[i]*ys[i+1]>=0:
                continue
            t=float(brentq(value,ts[i],ts[i+1],xtol=1e-12))
            point=self.p.corner_rows(t)@self.z
            penetration,other=self.wedge_penetration(point,(t-exclusion,t+exclusion))
            cap_slack=min(float(point[1]),float(np.min(
                self.p.support[0]@self.z-np.array([unit(a)@point for a in self.p.angles]))))
            roots.append({'angle':t,'other_contact_angle':other,
                          'direction':'enter' if ys[i]<0 else 'leave',
                          'nonlocal_residual':penetration,'cap_membership_slack':cap_slack})
        return roots

    def wall_slacks(self, body: int) -> list[dict]:
        """Minimum slack over each entire cell, not just the imposed wall samples."""
        if body not in (1,2):
            raise ValueError('body must be 1 (B) or 2 (D)')
        p=self.p
        lo,hi=(p.phi,PI/2) if body==1 else (0,PI/2-p.phi)
        rows=[]
        for i in range(p.m):
            a,b=max(lo,p.angles[i]),min(hi,p.angles[i+1])
            if b<=a:
                continue
            if body==1:
                coefficient=self.vertices[0,i]-self.vertices[1,i+2*p.m]
            else:
                v=self.vertices[0,i+p.m]-self.vertices[2,i+3*p.m]
                coefficient=np.array([v[1],-v[0]])
            candidates=[a,b]+periodic_candidates(
                float(np.arctan2(coefficient[1],coefficient[0])),a,b)
            values=[1-float(coefficient@unit(t)) for t in candidates]
            k=int(np.argmin(values))
            rows.append({'lo':a,'hi':b,'angle':float(candidates[k]),'slack':float(values[k])})
        return rows

    def tail_transition(self, body: int, power: int = 2, tolerance_factor: float = 2) -> dict:
        """Fit departure from the longest resolved near-zero wall-slack plateau.

The B curve is reversed so both fits are active-to-inactive. No known theta
or number of phases is used. A threshold locates a window, then an offset
plus a one-sided power fits the data. Model dependence is retained in output.
"""
        if power not in (2,3) or tolerance_factor<=0:
            raise ValueError('require power 2 or 3 and a positive tolerance factor')
        raw=self.wall_slacks(body)
        ts=np.array([r['angle'] for r in raw]);ys=np.array([r['slack'] for r in raw])
        if body==1:
            ts=PI/2-ts
        order=np.argsort(ts);ts,ys=ts[order],ys[order]
        tolerance=max(1e-7,tolerance_factor*max(0.,float(-ys.min())))
        active=ys<=tolerance
        transitions=np.flatnonzero(np.diff(np.r_[False,active,False]))
        plateaus=[(int(a),int(b)) for a,b in transitions.reshape(-1,2)
                  if b-a>=3 and b<len(ts)]
        if not plateaus:
            return {'body':body,'identified':False,'reason':'no resolved active plateau'}
        start,k=max(plateaus,key=lambda ab:ts[ab[1]-1]-ts[ab[0]])
        initial=(ts[k-1]+ts[k])/2
        width=max(.15,4*float(np.median(np.diff(ts))))
        use=(ts>=initial-width)&(ts<=initial+width)
        if np.count_nonzero(use)<6:
            return {'body':body,'identified':False,'reason':'too few cells for transition fit'}
        xx,yy=ts[use],ys[use]
        scale=max(float(np.max(abs(yy))),1e-6)
        amplitude=scale/max(width,1e-3)**power
        def residual(parameters):
            cutoff,log_a,offset=parameters
            prediction=offset+np.exp(log_a)*np.maximum(xx-cutoff,0.)**power
            return (prediction-yy)/scale
        result=least_squares(residual,[initial,np.log(amplitude),0.],
            bounds=([float(xx.min()),-30,-scale],[float(xx.max()),30,scale]),
            ftol=1e-12,xtol=1e-12,gtol=1e-12,max_nfev=1000)
        cutoff,log_a,offset=result.x
        fit_identified=bool(result.success and np.exp(log_a)>1e-5
            and ts[k-1]<=cutoff<=ts[k])
        return {'body':body,'identified':fit_identified,'fit_success':bool(result.success),
                'power':power,'plateau_interval':[float(ts[start]),float(ts[k-1])],
                'resolved_plateaus':len(plateaus),
                'tolerance_factor':tolerance_factor,'tolerance':tolerance,
                'threshold_bracket':([float(ts[k-1]),float(ts[k])] if body==2
                    else [float(PI/2-ts[k]),float(PI/2-ts[k-1])]),
                'search_coordinate_bracket':[float(ts[k-1]),float(ts[k])],
                'angle':float(cutoff if body==2 else PI/2-cutoff),
                'fit_rms':float(np.sqrt(np.mean((residual(result.x)*scale)**2))),
                'offset':float(offset),'amplitude':float(np.exp(log_a)),
                'fit_cells':len(xx)}

    def report(self) -> dict:
        return {'intervals':self.p.intervals,'phi_input':self.p.phi,
                'corner_exposure':{str(g):self.corner_exposure(g) for g in (.1,.2,.3)},
                'tail_transitions':[self.tail_transition(b,power,factor)
                    for b in (2,1) for power in (2,3) for factor in (1,2,4)],
                'wall_slacks':{str(b):self.wall_slacks(b) for b in (1,2)},
                'arithmetic_certified':False}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results',type=Path,nargs='+')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    reports=[]
    for source in args.results:
        for r in json.loads(source.read_text())['runs']:
            if 'shared_cuts' in r:
                from cut_search import shared_problem
                p=shared_problem(r['intervals'],r['phi'],r['shared_cuts'])
            else:
                p=QProblem(r['intervals'],r['phi'],r['quadrature'],r['wall_samples'])
            report=ContactProbe(p,np.array(r['all_variables'])).report()
            report['source']=str(source);report['seed']=r['seed']
            reports.append(report)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps({'runs':reports},indent=2)+'\n')
            print(json.dumps({k:v for k,v in report.items() if k!='wall_slacks'}),flush=True)


if __name__=='__main__':
    main()
