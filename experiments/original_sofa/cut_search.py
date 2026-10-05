"""Min-max cut experiments on a common polygon normal fan.

Every tested cut is inserted into every problem, so changing the cut does not
change the support-function approximation space. This controls one mesh bias,
not all of them. Only [0.039,0.04] has the source's geometric reduction here.
No reference shape, exact Gerver angle, or reference area enters these solves.
"""
from __future__ import annotations

import argparse
import copy
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

from q_experiment import PI, QProblem, tangent, unit


def shared_problem(intervals: int, phi: float, cuts: list[float]) -> QProblem:
    """Construct the same linear polygon model on the union of all cut normals.

This repeats only QProblem's fan-to-vertex linear algebra. Its constraints and
objective are assembled by the existing methods, not a second Q formula.
"""
    if not cuts or any(not 0<c<PI/4 for c in cuts) or phi not in cuts:
        raise ValueError('cuts must lie in (0,pi/4) and include phi')
    p=QProblem(intervals,phi)
    quarter=np.unique(np.r_[np.linspace(0,PI/2,intervals+1),cuts,PI/2-np.array(cuts)])
    if np.min(np.diff(quarter))<1e-8:
        raise ValueError('common fan has nearly coincident normals')
    p.angles=np.concatenate([quarter[:-1]+k*PI/2 for k in range(4)])
    p.m=len(quarter)-1
    n=len(p.angles);nk=2*p.m+1;p.size=10*p.m+1;d=p.size+1
    p.support=np.zeros((3,n,d));p.support[0,:nk,:nk]=np.eye(nk)
    for i in range(nk,n):
        c=np.cos(p.angles[i]);p.support[0,i,0 if c>0 else 2*p.m]=abs(c)
    p.support[1,:,nk:nk+n]=np.eye(n)
    p.support[2,:,nk+n:nk+2*n]=np.eye(n)
    p.vertices=np.empty((3,n,2,d))
    for i,a in enumerate(p.angles):
        j=(i+1)%n;b=p.angles[j] if j else 2*PI
        inverse=np.linalg.inv(np.stack([unit(a),unit(b)]))
        p.vertices[:,i]=np.einsum('ab,kbd->kad',inverse,p.support[:,[i,j]])
    p.edges=np.empty((3,n,d))
    for i,a in enumerate(p.angles):
        p.edges[:,i]=np.einsum('a,kad->kd',tangent(a),p.vertices[:,i]-p.vertices[:,i-1])
    p._assemble_constraints();p._assemble_objective()
    return p


def recut(p:QProblem,phi:float)->QProblem:
    """Retain all fan arrays; change only the cut-dependent constraints and Q."""
    if not 0<phi<PI/4:
        raise ValueError('invalid cut')
    p.index(phi);p.index(PI/2-phi)
    q=copy.copy(p);q.phi=phi
    q._assemble_constraints();q._assemble_objective()
    return q


def solve_probe(p:QProblem,previous:np.ndarray|None=None,seed:int=0)->tuple[np.ndarray,dict]:
    start=time.perf_counter()
    constraints=p.ge@p.transform
    a,b=constraints[:,:-1],constraints[:,-1]
    norms=np.linalg.norm(a,axis=1);keep=norms>1e-10
    if np.any(b[~keep]<-1e-9):
        raise RuntimeError('inconsistent constant constraint')
    a,b=a[keep]/norms[keep,None],b[keep]/norms[keep]
    if previous is None:
        lp=linprog(np.random.default_rng(seed).normal(size=a.shape[1]),
            A_ub=-a,b_ub=b,bounds=[(-10,10)]*a.shape[1],method='highs')
        if not lp.success:
            raise RuntimeError(lp.message)
        y0=lp.x;initialization='random_LP'
    else:
        if previous.shape!=(p.size,) or not np.all(np.isfinite(previous)):
            raise ValueError('incorrect previous solution')
        y0=p.basis.T@(previous-p.particular);initialization='previous_common_fan_solution'
    h=p.reduced[:-1,:-1];c=p.reduced[:-1,-1];constant=p.reduced[-1,-1]
    fun=lambda y:-float(y@h@y+2*c@y+constant)
    jac=lambda y:-2*(h@y+c)
    result=minimize(fun,y0,jac=jac,method='SLSQP',constraints=[
        {'type':'ineq','fun':lambda y:a@y+b,'jac':lambda y:a}],
        options={'ftol':1e-12,'maxiter':900})
    x=p.particular+p.basis@result.x
    # An independent first-order gap LP. Numerical, not a certified bound.
    gradient=jac(result.x)
    check=linprog(gradient,A_ub=-a,b_ub=b,bounds=[(None,None)]*len(result.x),method='highs')
    first_order_gap=float(gradient@result.x-check.fun) if check.success else None
    row={'intervals':p.intervals,'phi':p.phi,'seed':seed,'variables':p.size,
         'wall_samples':p.wall_samples,'quadrature':p.quadrature,
         'q':p.objective(x),'success':bool(result.success),'message':str(result.message),
         'iterations':int(result.nit),'initialization':initialization,
         'initial_scaled_feasibility':float(np.min(a@y0+b)),
         'first_order_gap_lp_success':bool(check.success),
         'first_order_gap':first_order_gap,'first_order_gap_message':str(check.message),
         'elapsed_seconds':time.perf_counter()-start,**p.constraint_residuals(x)}
    return x,row


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--intervals',type=int,nargs='+',default=[16,32])
    parser.add_argument('--cuts',type=float,nargs='+',default=[.02,.03,.035,.039,.04,.045,.05,.06])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();rows=[]
    cuts=sorted(set(args.cuts))
    for n in args.intervals:
        common=shared_problem(n,cuts[0],cuts);previous=None
        for phi in cuts:
            p=recut(common,phi)
            x,row=solve_probe(p,previous)
            if row['success'] and row['inequality_min']>=-1e-7:
                previous=x
            row['shared_cuts']=cuts;row['source_reduction_range']=.039<=phi<=.04
            row['all_variables']=x.tolist();rows.append(row)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps({'outer_objective':'minimize','runs':rows},indent=2)+'\n')
            print(json.dumps({k:v for k,v in row.items() if k!='all_variables'}),flush=True)


if __name__=='__main__':
    main()
