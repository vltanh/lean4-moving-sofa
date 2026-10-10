#!/usr/bin/env python3
"""Replay transfer of PR #7's reverse/forward shapes into the two-90-degree problem.

Requires separate checkout of PR #7's research branch and packages numpy, scipy, numba.
This is numerical exploration only, NOT a rigorous feasible-area certificate.
"""
from __future__ import annotations
import argparse,math,sys
from pathlib import Path
import numpy as np
from scipy.spatial import ConvexHull
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from all_angle_polygon_pair import M,M_HALF,romik_cap_polygon,pair_area

def hull(p):
    p=np.asarray(p,dtype=float)
    return p[ConvexHull(p).vertices]

def build(pr7_dir,source,beta,W,T,points):
    sys.path.insert(0,str(pr7_dir))
    if source=='reverse':
        from reverse_exact import ReverseSofa
        s=ReverseSofa(math.radians(180-beta))
        vertices=s.polygon(points)
        # This is NOT a rigid-motion-preserving coordinate change.
        original_area=s.area()
    else:
        from forward_contact_equations import ForwardContactModel
        f=(ForwardContactModel.solve(math.radians(beta)) if T is None
           else ForwardContactModel(math.radians(beta),T))
        vertices=f.boundary_polygon(points)
        # The forward model is a signed boundary ansatz, NOT a certified sofa.
        original_area=f.signed_area()
    p=hull(vertices)
    xmin,xmax=np.min(p[:,0]),np.max(p[:,0]);ymin,ymax=np.min(p[:,1]),np.max(p[:,1])
    p[:,0]=(p[:,0]-(xmin+xmax)/2)*W/(xmax-xmin)
    p[:,1]=(p[:,1]-ymin)/(ymax-ymin)
    p=hull(np.vstack([p,[[-W/2,0],[W/2,0]]]))
    return p,original_area

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--pr7-dir',required=True,type=Path,
                   help='Directory containing reverse_exact.py and forward_contact_equations.py in PR #7 worktree')
    a.add_argument('--shape',choices=['reverse','forward'],default='reverse')
    a.add_argument('--beta',type=float,default=173.)
    a.add_argument('--T',type=float,default=None,help='Free central contact half-length for forward model')
    a.add_argument('--width',type=float,default=2*M_HALF)
    a.add_argument('--points',type=int,default=140)
    a.add_argument('--nx',type=int,default=3501)
    args=a.parse_args()
    p,old=build(args.pr7_dir,args.shape,args.beta,args.width,args.T,args.points)
    ref=romik_cap_polygon(args.points)
    area,parts=pair_area(p,p,nx=args.nx,details=True)
    print(f'PR7 source bend {args.beta} deg ({args.shape}), source area/signed value {old:.9f}')
    print(f'90-degree reprocessed cap width {args.width:.9f}, polygon vertices {len(p)}')
    print(f'Full-angle numeric candidate={area:.10f}, components={parts}, exact Romik={M:.10f}')
    print(f'Difference candidate-Romik={area-M:+.10f}')
    if abs(args.width-2*M_HALF)<1e-10:
        mr,_=pair_area(p,ref,nx=args.nx,details=True)
        rr,_=pair_area(ref,ref,nx=args.nx,details=True)
        print(f'Mixed with reference={mr:.10f}; sampled reference={rr:.10f}')
    print('NOT A CERTIFICATE: floating algebraic roots and spatial quadrature; connectedness and continuous feasible motion must be justified separately.')

if __name__=='__main__':main()
