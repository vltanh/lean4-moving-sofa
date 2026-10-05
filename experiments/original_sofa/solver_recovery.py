"""Explicit feasibility-repair experiments; original failures remain unchanged.

An L1-distance LP projects an approximate support vector onto the finite
constraints in equality-reduced coordinates. The same SLSQP quadratic solver
is then restarted. This is a numerical recovery tactic, not certification.
"""
from __future__ import annotations
import argparse
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import bmat, csr_matrix, eye
from contacts import ContactProbe
from cut_feedback import interpolate_variables
from cut_search import solve_probe
from q_experiment import PI, QProblem


def project_feasible(p:QProblem,x:np.ndarray)->tuple[np.ndarray,dict]:
    if x.shape!=(p.size,) or not np.all(np.isfinite(x)):
        raise ValueError('expected a finite full solution vector')
    start=time.perf_counter()
    y0=p.basis.T@(x-p.particular)
    rows=p.ge@p.transform;a,b=rows[:,:-1],rows[:,-1]
    norms=np.linalg.norm(a,axis=1);keep=norms>1e-10
    if np.any(b[~keep]<-1e-9):
        raise RuntimeError('inconsistent constant constraint')
    a,b=a[keep]/norms[keep,None],b[keep]/norms[keep]
    dim=len(y0);identity=eye(dim,format='csr')
    constraints=bmat([[-csr_matrix(a),csr_matrix((len(b),dim))],
                      [identity,-identity],[-identity,-identity]],format='csr')
    result=linprog(np.r_[np.zeros(dim),np.ones(dim)],A_ub=constraints,
        b_ub=np.r_[b,y0,-y0],bounds=[(None,None)]*dim+[(0,None)]*dim,
        method='highs',options={'primal_feasibility_tolerance':1e-9,
                               'dual_feasibility_tolerance':1e-9})
    if not result.success:
        raise RuntimeError('L1 feasibility repair failed: '+result.message)
    projected=p.particular+p.basis@result.x[:dim]
    return projected,{'method':'L1_feasibility_projection','distance_l1_reduced':float(result.fun),
        'support_change_l2':float(np.linalg.norm(projected-x)),
        'elapsed_seconds':time.perf_counter()-start,**p.constraint_residuals(projected)}


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs',type=Path,nargs='+')
    parser.add_argument('--steps',type=int,default=2)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.steps<1:parser.error('--steps must be positive')
    results=[]
    for source in args.inputs:
        for failed in json.loads(source.read_text())['runs']:
            if failed['success']:continue
            p=QProblem(failed['intervals'],failed['phi'],failed['quadrature'],failed['wall_samples'])
            x=np.array(failed['all_variables'])
            for step in range(args.steps):
                projected,repair=project_feasible(p,x)
                x,row=solve_probe(p,projected)
                row.update({'source':str(source),'source_failure_message':failed['message'],
                    'source_failure_phi':failed['phi'],'source_start_cut':failed.get('start_cut'),
                    'source_failure_inequality_min':failed['inequality_min'],
                    'recovery_step':step,'projection':repair,'arithmetic_certified':False,
                    'source_reduction_range':.039<=p.phi<=.04})
                target=None
                if row['success'] and row['inequality_min']>=-1e-7:
                    events=ContactProbe(p,x).corner_exposure()
                    row['corner_events']=events
                    enter=[e for e in events if e['direction']=='enter']
                    leave=[e for e in events if e['direction']=='leave']
                    if len(enter)==1 and len(leave)==1 and all(e['cap_membership_slack']>=-1e-7 for e in events):
                        target=(enter[0]['angle']+PI/2-leave[0]['angle'])/2
                        row['inferred_cut']=target
                row['all_variables']=x.tolist();results.append(row)
                args.output.parent.mkdir(parents=True,exist_ok=True)
                args.output.write_text(json.dumps({'runs':results},indent=2)+'\n')
                print(json.dumps({k:v for k,v in row.items() if k!='all_variables'}),flush=True)
                if target is None:break
                new=QProblem(p.intervals,target,p.quadrature,p.wall_samples)
                x=interpolate_variables(p,x,new);p=new


if __name__=='__main__':
    main()
