"""Non-certifying search that suggests a rational certificate template.

The solver's success flag is not an upper-bound certificate. Proof replay uses
neither this file nor SciPy, floating-point positions, or optimizer tolerances.
"""
import argparse,json
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution
from exact_width import rational_lines

_lines=rational_lines()
_slope=np.array([float(a) for a,b in _lines])
_intercept=np.array([[float(c) for c in b] for a,b in _lines])
_i,_j=np.triu_indices(len(_lines),1)
_keep=abs(_slope[_i]-_slope[_j])>1e-14
_i,_j=_i[_keep],_j[_keep]
_den=_slope[_i]-_slope[_j]

def floating_area(t):
    b=_intercept@np.r_[1.,t]
    crossing=(b[_j]-b[_i])/_den
    knots=np.sort(np.r_[0.,crossing[(crossing>0)&(crossing<2)],2.])
    mid=(knots[1:]+knots[:-1])/2
    v=_slope[:,None]*mid+b[:,None]
    top=np.minimum.reduce([v[1],v[2],v[3],v[10],v[11],np.maximum(v[8],v[9]),np.maximum(v[16],v[17])])
    bot=np.maximum.reduce([v[0],v[6],v[7],v[14],v[15],np.minimum(v[4],v[5]),np.minimum(v[12],v[13])])
    return float(np.dot(np.maximum(top-bot,0),np.diff(knots)))

def discover(seeds):
    results=[]
    for seed in seeds:
        r=differential_evolution(lambda t:-floating_area(t),[(0.,1.)]*8,
                                 seed=seed,maxiter=250,popsize=8,tol=1e-9,polish=True)
        results.append({'seed':seed,'area_float':float(-r.fun),'coordinates':r.x.tolist(),
                        'solver_success':bool(r.success),'evaluations':int(r.nfev),
                        'certified_upper_bound':False,'continuous_motion_verified':False})
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seeds',default='0,1,2,20261005');p.add_argument('--output',type=Path,default=Path('discovery.json'));a=p.parse_args()
    result=discover([int(x) for x in a.seeds.split(',')]);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
