#!/usr/bin/env python3
"""Explore non-Romik ambidextrous sofas by varying the two corner MOTIONS.

Each parent angle goes from 0 to alpha, with alpha <= pi/2.
A supplied continuous path of the inner corner defines actual hallway
placements. At the terminal angle the extra outgoing straight strip
is imposed. At the initial angle, the common incoming unit strip is used.

Numerical angular and spatial grids are ONLY explorations; they omit
intermediate constraints and are NOT a rigorous feasible-area certificate.
Disconnected unions cannot be scored as one sofa.

Requires numpy, scipy and numba. No Lean formalization.
"""
import argparse
import numpy as np
from scipy.optimize import differential_evolution
from numba import njit
from all_angle_polygon_pair import Y,BETA,M,M_HALF

R0=np.cos(BETA)/np.sin(1.5*BETA+np.pi/8)
D=8  # per handedness: 3 horizontal, 4 vertical, 1 terminal-angle parameter

def reference_corner(t):
    """Romik's true inner corner from its analytic support functions."""
    c=np.cos(t);s=np.sin(t);m=M_HALF;b=m/2
    f=np.where(t<=BETA,m*c+s/2,np.where(t>=np.pi/2-BETA,
               b*c+s/2+.5,R0*np.cos(t/2+np.pi/8)+s/2))
    g=np.where(t<=BETA,b*s+c/2+.5,np.where(t>=np.pi/2-BETA,
               m*s+c/2,R0*np.sin(t/2+np.pi/8)+c/2))
    return (f-1)*c-(g-1)*s,(f-1)*s+(g-1)*c

def route(p,n):
    """Continuous cosine/sine corner-path interpolation, possibly partial turn."""
    alpha=np.pi/2-p[7]
    u=np.linspace(0,1,n)
    ts=alpha*u
    x,y=reference_corner(u*np.pi/2)
    x=x+p[0]+p[1]*np.cos(np.pi*u)+p[2]*np.cos(2*np.pi*u)
    y=y+p[3]*np.sin(np.pi*u)+p[4]*np.sin(2*np.pi*u)
    y=y+p[5]*np.sin(3*np.pi*u)+p[6]*u
    # Incoming inner corner has vertical coordinate 0, hence incoming strip [0,1].
    return ts,x,y

@njit(cache=True)
def _intersection(xs,t1,x1,y1,t2,x2,y2):
    height=np.empty(len(xs))
    for i in range(len(xs)):
        x=xs[i]
        high1=1.;high2=1.;low1=0.;low2=0.
        for k in range(2):
            if k==0:t=t1;px=x1;py=y1
            else:t=t2;px=x2;py=y2
            # Incoming arm at t=0: x <= inner_corner_x(0)+1.
            high=1. if x<=px[0]+1 else -1e4
            low=0.
            for j in range(1,len(t)):
                c=np.cos(t[j]);s=np.sin(t[j]);xc=px[j];yc=py[j]
                f=1+xc*c+yc*s;g=1-xc*s+yc*c
                # Both outer walls, and the safe alternative to the inner quadrant.
                if s>1e-12:
                    high=min(high,(f-x*c)/s)
                elif x*c>f: high=-1e4
                if c>1e-12:
                    high=min(high,(g+x*s)/c)
                elif -x*s>g: high=-1e4
                if s>1e-12 and c>1e-12:
                    low=max(low,min((f-1-x*c)/s,(g-1+x*s)/c))
            # The final straight outbound strip, normal u_alpha.
            c=np.cos(t[-1]);s=np.sin(t[-1])
            low=max(low,(px[-1]*c+py[-1]*s-x*c)/s)
            if k==0:high1=high;low1=low
            else:high2=high;low2=low
        height[i]=max(0,min(high1,1-low2)-max(low1,1-high2))
    return height

def score(z,nx=301,nt=301,details=False):
    t1,x1,y1=route(z[:D],nt);t2,x2,y2=route(z[D:],nt)
    xs=np.linspace(-2.3,2.3,nx)
    h=_intersection(xs,t1,x1,y1,t2,x2,y2)
    active=h>1e-8
    edges=np.diff(np.r_[False,active,False].astype(int))
    parts=[]
    for start,end in zip(np.where(edges==1)[0],np.where(edges==-1)[0]):
        a=max(0,start-1);b=min(nx,end+1)
        parts.append(float(np.trapezoid(h[a:b],xs[a:b])))
    if details:return float(np.trapezoid(h,xs)),parts,(np.pi/2-z[7],np.pi/2-z[15])
    # Select a single connected component. Combining disjoint areas is invalid.
    return max(parts,default=0)

def search(iters=60,seed=707,nx=251,nt=251):
    bounds=[]
    for j in range(D):
        if j==7:bounds.append((0,.55))
        elif j in (0,1,2):bounds.append((-.45,.45))
        else:bounds.append((-.45,.45))
    bounds=bounds*2
    zero=np.zeros(2*D)
    print('Reference sampled area',score(zero,nx,nt),
          'exact reference area',M)
    calls=0
    def objective(p):
        nonlocal calls
        calls+=1
        return -score(p,nx,nt)
    res=differential_evolution(objective,bounds,popsize=6,
                                maxiter=iters,tol=1e-7,seed=seed,
                                init='sobol',polish=False)
    print('evaluations',calls,'best sampled score',-res.fun,
          'terminal angles',np.pi/2-res.x[[7,15]])
    for n in (501,1201,3201):
        print('refinement',n,'candidate',score(res.x,n,n,True),
              'reference',score(zero,n,n,True))
    return res

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--iterations',type=int,default=60)
    p.add_argument('--seed',type=int,default=707)
    opt=p.parse_args()
    search(iters=opt.iterations,seed=opt.seed)
