"""Conservative continuous-angle construction with explicitly non-rigorous arithmetic.

For K inside a radius-R disk about the origin, each inner-wall slack
p.u(t)-h_K(t)+1 (and its quarter-turn counterpart) is 2R-Lipschitz.
On a uniform mesh of step d, excluding wedges enlarged by R*d therefore
ensures the exact-arithmetic continuous hallway constraints. Floating-point
polygon clipping here is not interval-verified, so output is NOT a certified bound.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from shapely.geometry import MultiPoint, Polygon, box
from shapely.ops import unary_union
from q_experiment import PI, QProblem


def conservative_shape(p:QProblem,x:np.ndarray,subdivisions:int=4096):
    if subdivisions < 4:
        raise ValueError('subdivisions must be at least 4')
    residual=p.constraint_residuals(x)
    if residual['inequality_min'] < -1e-6 or residual['equality_max_abs'] > 1e-6:
        raise ValueError('refusing substantially infeasible input')
    cap=MultiPoint(p.vertices[0]@np.r_[x,1.]).convex_hull
    xmin,_,xmax,_=cap.bounds
    cap=cap.intersection(box(xmin,0.,xmax,1.))
    if cap.is_empty or cap.geom_type!='Polygon':
        raise ValueError('cap has no positive-area polygon in the unit strip')
    vertices=np.asarray(cap.exterior.coords)[:-1]
    radius=float(np.max(np.linalg.norm(vertices,axis=1)))
    step=PI/(2*subdivisions)
    margin=radius*step+1e-10
    xmin,ymin,xmax,ymax=cap.bounds
    triangles=[]
    for t in np.linspace(0,PI/2,subdivisions+1):
        c,s=np.cos(t),np.sin(t)
        h=float(np.max(vertices[:,0]*c+vertices[:,1]*s))
        k=float(np.max(-vertices[:,0]*s+vertices[:,1]*c))
        a,b=h-1+margin,k-1+margin
        if t==0:
            right,top=min(xmax,a),min(ymax,b)
            if right>xmin and top>ymin:
                triangles.append(box(xmin,ymin,right,top))
        elif t==PI/2:
            left,top=max(xmin,-b),min(ymax,a)
            if left<xmax and top>ymin:
                triangles.append(box(left,ymin,xmax,top))
        else:
            corner=np.array([a*c-b*s,a*s+b*c])
            if corner[1]>0:
                triangles.append(Polygon([corner,[a/c,0],[-b/s,0]]))
    result=cap.difference(unary_union(triangles))
    parts=[result] if result.geom_type=='Polygon' else [g for g in result.geoms if g.area>1e-10]
    return result, {'motion_subdivisions':subdivisions,'radius':radius,'inner_wall_margin':margin,
        'conservative_constructed_area':float(result.area),'positive_area_components':len(parts),
        'polygon_valid':bool(result.is_valid),'arithmetic_certified':False,
        'interpretation':'continuous-angle margin argument; floating-point geometry, not a certified lower bound'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results',type=Path)
    parser.add_argument('--subdivisions',type=int,nargs='+',default=[4096,16384])
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    results=[]
    for run in json.loads(args.results.read_text())['runs']:
        p=QProblem(run['intervals'],run['phi'],run['quadrature'],run['wall_samples'])
        for n in args.subdivisions:
            _,row=conservative_shape(p,np.asarray(run['all_variables']),n)
            row.update(intervals=p.intervals,phi=p.phi,seed=run['seed'])
            results.append(row)
            print(json.dumps(row),flush=True)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps({'runs':results},indent=2)+'\n')

if __name__=='__main__':
    main()
