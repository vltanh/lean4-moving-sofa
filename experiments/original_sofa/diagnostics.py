"""Independent formula, shape-reference, and discretization diagnostics.

Gerver's analytic path is imported only here, after optimization, never in QProblem.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import numpy as np
from numpy.polynomial.legendre import leggauss
from q_experiment import PI, QProblem, tangent, unit


def square_matrix(p: QProblem, quadrature: int = 64) -> np.ndarray:
    """The six Mamikon squares, independently assembled from tangent displacements."""
    rows = []
    terms = [(0,0,p.phi,PI/2), (0,p.phi,PI/2-p.phi,None),
             (0,PI/2-p.phi,PI/2,PI-p.phi), (0,PI/2,PI,PI),
             (1,PI+p.phi,3*PI/2,3*PI/2), (2,3*PI/2,2*PI-p.phi,2*PI-p.phi)]
    nodes, weights = leggauss(quadrature)
    for body, start, end, target in terms:
        lo,hi = p.index(start),p.index(end)
        for i in range(lo,hi):
            a,b = p.angles[i:i+2]
            for t,w in zip((a+b)/2+(b-a)*nodes/2,weights*(b-a)/2):
                hp=p.support_row(body,t,True)
                if target is None:
                    rho=p.support_row(body,t+PI/2)-hp
                else:
                    rho=(p.support_row(body,target)-np.cos(target-t)*p.support_row(body,t))/np.sin(target-t)-hp
                rows.append(np.sqrt(.5*w)*rho)
    matrix=np.stack(rows)
    return matrix.T@matrix


def audit(p:QProblem) -> dict:
    sq=square_matrix(p)
    t=p.transform[:,:-1]
    residual=t.T@(sq+p.matrix)@t
    return {'square_decomposition_max_abs':float(np.max(abs(residual))),
            'square_decomposition_frobenius':float(np.linalg.norm(residual))}


def reference_support(angles:np.ndarray) -> np.ndarray:
    path=Path(__file__).resolve().parents[2]/'scripts'/'figures'/'gerver.py'
    spec=importlib.util.spec_from_file_location('gerver_reference_only',path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'cannot load Gerver reference: {path}')
    gerver=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gerver)
    values=[]
    for a in angles:
        t=a if a<=PI/2 else a-PI/2
        v=unit(t) if a<=PI/2 else tangent(t)
        values.append(1+np.asarray(gerver.path(t))@v)
    left=1+np.asarray(gerver.path(PI/2))@tangent(PI/2)
    right=1+np.asarray(gerver.path(0.))@unit(0.)
    center=(right-left)/2
    return np.asarray(values)-center*np.cos(angles)


def compare_reference(p:QProblem,x:np.ndarray,samples:int=4096) -> dict:
    angles=np.linspace(0,PI,samples+1)
    calculated=np.array([p.support_row(0,t)@np.r_[x,1.] for t in angles])
    error=calculated-reference_support(angles)
    return {'reference_support_samples':samples,
            'gerver_support_max_abs':float(np.max(abs(error))),
            'gerver_support_rms':float(np.sqrt(np.mean(error**2)))}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--dense-samples',type=int,nargs='+',default=[1024,4096,16384])
    args=parser.parse_args()
    results=[]
    for run in json.loads(args.results.read_text())['runs']:
        p=QProblem(run['intervals'],run['phi'],run['quadrature'],run['wall_samples'])
        x=np.asarray(run['all_variables'])
        row={'intervals':p.intervals,'phi':p.phi,'seed':run['seed'],**audit(p),**compare_reference(p,x)}
        row['dense_validation']=[p.validate(x,n) for n in args.dense_samples]
        results.append(row)
        print(json.dumps(row),flush=True)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps({'runs':results},indent=2)+'\n')

if __name__=='__main__':
    main()
