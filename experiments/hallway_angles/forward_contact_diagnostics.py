"""Finite-pose diagnostics of the forward CONTACT MODEL, not certificates.

This intentionally reports positive outside-polygon area instead of hiding it
with a tolerance or polygon repair. Neither finite-pose containment nor a
signed-area formula establishes continuous feasibility or optimality.
"""
from __future__ import annotations
import argparse
import json
import math
import numpy as np
from shapely.geometry import Polygon
from shapely.ops import unary_union
from forward_contact_equations import ForwardContactModel


def clip(vertices, normal, rhs):
    if len(vertices)==0:return np.empty((0,2))
    out=[];p=vertices[-1];dp=float(p@normal-rhs)
    for c in vertices:
        dc=float(c@normal-rhs)
        if (dp<=0)!=(dc<=0):out.append(p+(c-p)*(dp/(dp-dc)))
        if dc<=0:out.append(c)
        p,dp=c,dc
    return np.asarray(out,dtype=float).reshape(-1,2)


def sampled_intersection(model,poses):
    if isinstance(poses,bool) or not isinstance(poses,int) or poses<3 or poses%2!=1:
        raise ValueError('poses must be an odd integer at least three')
    beta=model.beta
    t=np.unique(np.r_[np.linspace(0,beta,poses),model.alpha,beta-model.alpha])
    corners=model.corner(t)
    ns=np.stack([np.column_stack([-np.sin(t),np.cos(t)]),
                 np.column_stack([np.sin(beta-t),np.cos(beta-t)])],axis=1)
    middle=model.corner([beta/2])[0]
    s,c=math.sin(beta/2),math.cos(beta/2)
    radius=(1+c*max(abs(middle[1]),abs(1-middle[1])))/s+1
    lo,hi=middle[0]-radius,middle[0]+radius
    base=np.array([[lo,0],[hi,0],[hi,1],[lo,1]],dtype=float)
    offsets=np.einsum('nij,nj->ni',ns,corners)
    cap=base.copy();cuts=[]
    for pair,offset in zip(ns,offsets):
        for n,o in zip(pair,offset):cap=clip(cap,n,float(o+1))
        cut=clip(clip(base,pair[0],float(offset[0])),pair[1],float(offset[1]))
        if len(cut)>=3:cuts.append(Polygon(cut))
    if len(cap)<3:return Polygon(),len(t)
    result=Polygon(cap).difference(unary_union(cuts))
    if not result.is_valid:raise ArithmeticError('invalid sampled intersection; not repaired')
    return result,len(t)


def diagnose(degrees,points=1025,poses=1025):
    model=ForwardContactModel.solve(math.radians(degrees))
    p=Polygon(model.boundary_polygon(points))
    intersection,actual_poses=sampled_intersection(model,poses)
    if not p.is_valid:raise ArithmeticError('invalid candidate polygon; not repaired')
    return dict(bend_degrees=degrees,T=model.T,alpha_degrees=math.degrees(model.alpha),
                signed_area=model.signed_area(),boundary_polygon_area=p.area,
                sampled_intersection_area=intersection.area,
                boundary_polygon_outside_sampled_intersection=p.difference(intersection).area,
                points_per_boundary_interval=points,poses=actual_poses,
                status='Floating-point diagnostic only; neither a lower nor a global upper certificate')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--angles',type=float,nargs='+',default=[135,136.672184698,137,140])
    p.add_argument('--points',type=int,default=1025)
    p.add_argument('--poses',type=int,default=1025)
    p.add_argument('--output')
    args=p.parse_args()
    text=json.dumps([diagnose(b,args.points,args.poses) for b in args.angles],indent=2)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:print(text,end='')
