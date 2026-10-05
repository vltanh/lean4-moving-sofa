"""Exploratory cut feedback from a solved cap's corner-exposure events.

The next symmetric cut is the mean of the inferred left exposure angle and
pi/2 minus the right one. This is a fixed-point experiment, NOT a replacement
for the continuous min-max theorem and NOT a convergence proof. The normal
fan changes with the cut. No analytic Gerver reference is imported.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from contacts import ContactProbe
from cut_search import solve_probe
from q_experiment import PI, QProblem


def interpolate_variables(old:QProblem,x:np.ndarray,new:QProblem)->np.ndarray:
    z=np.r_[x,1.]
    values=[old.support_row(body,t)@z for body in range(3)
            for t in (new.angles[:2*new.m+1] if body==0 else new.angles)]
    return np.array(values)


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--intervals',type=int,nargs='+',default=[16,32])
    parser.add_argument('--starts',type=float,nargs='+',default=[.02,.06])
    parser.add_argument('--steps',type=int,default=4)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.steps<1:
        parser.error('--steps must be positive')
    rows=[]
    for n in args.intervals:
        for start in args.starts:
            phi=start;old=None;x=None
            for step in range(args.steps):
                p=QProblem(n,phi)
                warm=None if old is None else interpolate_variables(old,x,p)
                x,row=solve_probe(p,warm)
                row.update({'start_cut':start,'feedback_step':step,
                    'initialization':'random_LP' if old is None else 'interpolated_previous_cut',
                    'source_reduction_range':.039<=phi<=.04})
                if not row['success'] or row['inequality_min']<-1e-7:
                    row['feedback_status']='solver_failure'
                else:
                    events=ContactProbe(p,x).corner_exposure()
                    enter=[e for e in events if e['direction']=='enter']
                    leave=[e for e in events if e['direction']=='leave']
                    row['corner_events']=events
                    if len(enter)!=1 or len(leave)!=1 or any(e['cap_membership_slack']<-1e-7 for e in events):
                        row['feedback_status']='unresolved_events'
                    else:
                        target=(enter[0]['angle']+PI/2-leave[0]['angle'])/2
                        row['inferred_cut']=target
                        row['cut_update']=target-phi
                        row['feedback_status']='converged' if abs(target-phi)<1e-7 else 'continue'
                row['all_variables']=x.tolist();rows.append(row)
                args.output.parent.mkdir(parents=True,exist_ok=True)
                args.output.write_text(json.dumps({'method':'exposure_fixed_point','runs':rows},indent=2)+'\n')
                print(json.dumps({k:v for k,v in row.items() if k!='all_variables'}),flush=True)
                if row['feedback_status']!='continue':
                    break
                old=p;phi=row['inferred_cut']


if __name__=='__main__':
    main()
