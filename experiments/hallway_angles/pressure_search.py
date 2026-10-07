"""Multilevel direct area maximization using exposed-wall gradients.

The exported path is piecewise linear even when a cubic basis helps the search.
No global optimality, symmetry, or monotonicity reduction is assumed.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import platform
import time
import numpy as np
import scipy
from scipy.interpolate import CubicSpline
from scipy.optimize import minimize
import shapely
from geometry import Motion
from pressure import area_gradient


def interpolation_matrix(knots: int, samples: int, basis: str) -> np.ndarray:
    if knots < 3 or knots % 2 != 1 or samples < knots or samples % 2 != 1:
        raise ValueError("require odd samples >= odd knots >= 3")
    if (samples-1) % (knots-1):
        raise ValueError("samples must subdivide all control intervals equally")
    old, new = np.linspace(0.,1.,knots), np.linspace(0.,1.,samples)
    eye = np.eye(knots)
    if basis == "linear":
        return np.column_stack([np.interp(new,old,v) for v in eye])
    if basis == "cubic":
        return CubicSpline(old,eye,axis=0)(new)
    raise ValueError("basis must be linear or cubic")


def default_seed(beta: float, mode: str, knots: int) -> Motion:
    u = np.linspace(0.,1.,knots)
    if mode == "forward":
        # Starting curve only: all free coordinates are subsequently released.
        x = .65*math.cos(beta/2)/math.sin(beta/2)*np.cos(math.pi*u)
        y = .67*np.sin(math.pi*u)
        y[[0,-1]] = 0.
    elif mode == "reverse":
        x = .20*math.sin(beta/2)/math.cos(beta/2)*(2*u-1)**2
        y = u-.06*np.sin(2*math.pi*u)
        y[[0,-1]] = [0.,1.]
    else:
        raise ValueError("invalid mode")
    x[knots//2] = 0.
    return Motion(beta,mode,np.column_stack((x,y)))


def optimize_pressure(initial: Motion, knots: int, subdivisions: int = 4,
                      basis: str = "linear", maxiter: int = 400,
                      perturb: float = 0.0, seed: int = 0):
    if subdivisions < 1 or maxiter < 1 or perturb < 0 or not math.isfinite(perturb):
        raise ValueError("invalid optimizer settings")
    samples = (knots-1)*subdivisions+1
    matrix = interpolation_matrix(knots,samples,basis)
    old,new = np.linspace(0.,1.,len(initial.corners)),np.linspace(0.,1.,knots)
    c = np.column_stack([np.interp(new,old,initial.corners[:,j]) for j in range(2)])
    c[:,0] -= c[knots//2,0]
    template = c.ravel().copy()
    fixed = (1, 2*(knots-1)+1, 2*(knots//2))
    free = np.array([i for i in range(2*knots) if i not in fixed])
    x = template[free].copy()
    if perturb:
        x += np.random.default_rng(seed).normal(0.,perturb,len(x))
    limit = 4./min(math.sin(initial.beta/2),math.cos(initial.beta/2))
    bounds = [(-limit,limit) if i%2 == 0 else (-2.,3.) for i in free]
    x = np.clip(x,[b[0] for b in bounds],[b[1] for b in bounds])
    history=[]
    best_area=-1.
    best_c=c.copy()
    calls=0
    max_unassigned=max_tied=0.
    def decode(v):
        c=template.copy()
        c[free]=v
        return c.reshape(-1,2)
    def objective(v):
        nonlocal calls,best_area,best_c,max_unassigned,max_tied
        c=decode(v)
        dense=matrix@c
        dense[0,1],dense[-1,1]=initial.corners[0,1],initial.corners[-1,1]
        dense[samples//2,0]=0.
        m=Motion(initial.beta,initial.mode,dense)
        a,g,info=area_gradient(m)
        calls+=1
        max_unassigned=max(max_unassigned,info["unassigned_length"])
        max_tied=max(max_tied,info["tied_length"])
        if info["unassigned_length"] > 1e-6:
            raise ArithmeticError("unassigned exposed edge in area gradient")
        if a > best_area:
            best_area,best_c=a,c.copy()
            history.append([calls,a])
        return -a,-(matrix.T@g).ravel()[free]
    start=time.monotonic()
    initial_area=objective(x)[0]*-1
    result=minimize(objective,x,jac=True,method="L-BFGS-B",bounds=bounds,
        options={"maxiter":maxiter,"maxls":40,"maxcor":20,"ftol":1e-13,"gtol":2e-7})
    # Save the best evaluated controls even if the final line search fails.
    dense=matrix@best_c
    dense[0,1],dense[-1,1]=initial.corners[0,1],initial.corners[-1,1]
    dense[samples//2,0]=0.
    motion=Motion(initial.beta,initial.mode,dense)
    record={"knots":knots,"samples":samples,"basis":basis,"subdivisions":subdivisions,
        "initial_sampled_area":initial_area,"best_sampled_area":best_area,
        "returned_sampled_area":float(-result.fun),"success":bool(result.success),
        "status":int(result.status),"message":str(result.message),
        "iterations":int(result.nit),"evaluations":calls,"maxiter":maxiter,
        "elapsed_seconds":time.monotonic()-start,"seed":seed,"perturb":perturb,
        "controls":best_c.tolist(),"max_unassigned_length":max_unassigned,
        "max_tied_length":max_tied,"accepted_improvements":history,
        "returned_gradient_inf_norm":float(np.max(np.abs(result.jac)))}
    return motion,record


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--angles",type=float,nargs="+",default=[90.])
    p.add_argument("--modes",nargs="+",choices=["forward","reverse"],default=["forward","reverse"])
    p.add_argument("--levels",type=int,nargs="+",default=[17,33,65])
    p.add_argument("--subdivisions",type=int,default=4)
    p.add_argument("--basis",choices=["linear","cubic"],default="linear")
    p.add_argument("--maxiter",type=int,default=400)
    p.add_argument("--seed",type=int,default=0)
    p.add_argument("--perturb",type=float,default=0.)
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    rows=[]
    for degrees in a.angles:
        for mode in a.modes:
            motion=default_seed(math.radians(degrees),mode,a.levels[0])
            for knots in a.levels:
                motion,record=optimize_pressure(motion,knots,a.subdivisions,a.basis,
                    a.maxiter,a.perturb,a.seed)
                rows.append({"bend_degrees":degrees,"mode":mode,"corners":motion.corners.tolist(),"optimization":record})
                a.output.parent.mkdir(parents=True,exist_ok=True)
                a.output.write_text(json.dumps({"status":"local sampled optima, not continuous-motion certificates",
                    "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__,"shapely":shapely.__version__},
                    "results":rows},indent=2)+"\n")
                print(degrees,mode,knots,record["best_sampled_area"],record["evaluations"],record["success"],flush=True)
if __name__=="__main__":
    main()
