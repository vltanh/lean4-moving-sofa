#!/usr/bin/env python3
"""Exploratory all-angle one-turn polygon-pair evaluator.

Mathematical reduction: at a given x, the maximum over EVERY angle
is attained at a polygon support-switch angle, an extremum of one
wall, or an intersection of the two walls. Support-switch sectors
are subdivided at algebraic zeros of the corner-x derivative.

Important: quartic roots and area integration use floating point.
This is NOT a rigorous interval certificate. A disconnected union
cannot be treated as one connected sofa.

Requires numpy, scipy and numba; no Lean formalization.
"""
import numpy as np
from scipy.optimize import brentq
from scipy.spatial import ConvexHull
from numba import njit

Y=brentq(lambda y:4*y**3+3*y-1,0,.5,xtol=1e-15)
BETA=np.arctan(Y)
M=1+4*Y**2+BETA
M_HALF=1/(3*np.sin(BETA))

def romik_cap_polygon(n=100):
    """Polygon whose vertices sample Romik's exact one-turn convex cap."""
    a=M_HALF;b=a/2;R=np.cos(BETA)/np.sin(1.5*BETA+np.pi/8)
    t=np.unique(np.r_[np.linspace(0,BETA,max(5,n//4)),
                        np.linspace(BETA,np.pi/2-BETA,n),
                        np.linspace(np.pi/2-BETA,np.pi/2,max(5,n//4))])
    c=np.cos(t);s=np.sin(t)
    f=np.where(t<=BETA,a*c+s/2,np.where(t>=np.pi/2-BETA,
           b*c+s/2+.5,R*np.cos(t/2+np.pi/8)+s/2))
    g=np.where(t<=BETA,b*s+c/2+.5,np.where(t>=np.pi/2-BETA,
           a*s+c/2,R*np.sin(t/2+np.pi/8)+c/2))
    fp=np.where(t<=BETA,-a*s+c/2,np.where(t>=np.pi/2-BETA,
            -b*s+c/2,-R*np.sin(t/2+np.pi/8)/2+c/2))
    gp=np.where(t<=BETA,b*c-s/2,np.where(t>=np.pi/2-BETA,
            a*c-s/2,R*np.cos(t/2+np.pi/8)/2-s/2))
    p=np.r_[np.c_[f*c-fp*s,f*s+fp*c],
            np.c_[-g*s-gp*c,g*c-gp*s],
            [[-a,0],[a,0]]]
    return p[ConvexHull(p).vertices]

def _xcorner(t,xf,yf,xg,yg):
    c=np.cos(t);s=np.sin(t)
    return xf*c*c+xg*s*s+(yf-yg)*s*c-c+s

def sectors(poly):
    """Partition [0,pi/2] into fixed-support, monotone-corner sectors.

    Derivative of xcorner is a quartic in z=tan(t/2).
    Quartic roots are evaluated numerically (not interval-certified).
    """
    p=np.asarray(poly)[ConvexHull(poly).vertices]
    edges=np.roll(p,-1,axis=0)-p
    a=np.mod(np.arctan2(-edges[:,0],edges[:,1]),2*np.pi)
    cuts=[0.,np.pi/2]
    for theta in a:
        if 1e-10<theta<np.pi/2-1e-10:cuts.append(theta)
        if np.pi/2+1e-10<theta<np.pi-1e-10:cuts.append(theta-np.pi/2)
    cuts=np.unique(cuts)
    out=[]
    for lo,hi in zip(cuts[:-1],cuts[1:]):
        t=(lo+hi)/2;c=np.cos(t);s=np.sin(t)
        xf,yf=p[np.argmax(p[:,0]*c+p[:,1]*s)]
        xg,yg=p[np.argmax(-p[:,0]*s+p[:,1]*c)]
        dx=xg-xf;dy=yf-yg
        coeff=[dy-1,2-4*dx,-6*dy,2+4*dx,dy+1]
        segments=[lo,hi]
        for root in np.roots(coeff):
            if abs(root.imag)<1e-8 and root.real>=0:
                tt=2*np.arctan(root.real)
                if lo+1e-9<tt<hi-1e-9:segments.append(float(tt))
        segments=sorted(set(segments))
        for l,r in zip(segments[:-1],segments[1:]):
            out.append([l,r,xf,yf,xg,yg,
                        _xcorner(l,xf,yf,xg,yg),
                        _xcorner(r,xf,yf,xg,yg)])
    return np.array(out)

@njit(cache=True)
def _walls(theta,x,xf,yf,xg,yg):
    c=np.cos(theta);s=np.sin(theta)
    # Subtraction of 1 occurs BEFORE dividing by sin/cos.
    return min(((xf-x)*c+yf*s-1)/s,
               ((x-xg)*s+yg*c-1)/c)

@njit(cache=True)
def niche(sec,xs):
    """Maximize forbidden inner-wall height over the complete angle continuum."""
    n=np.zeros(len(xs))
    for i in range(len(xs)):
        x=xs[i];best=0.
        for k in range(len(sec)):
            lo,hi,xf,yf,xg,yg,xa,xb=sec[k]
            # Polygon support switches and xcorner monotonicity endpoints.
            for tt in (lo,hi):
                if 1e-9<tt<np.pi/2-1e-9:
                    z=_walls(tt,x,xf,yf,xg,yg)
                    if z>best:best=z
            # Extrema of either one-wall roof.
            q=xf-x
            if -1<q<1:
                t=np.arccos(q)
                if lo<t<hi:
                    z=_walls(t,x,xf,yf,xg,yg)
                    if z>best:best=z
            q=x-xg
            if -1<q<1:
                t=np.arcsin(q)
                if lo<t<hi:
                    z=_walls(t,x,xf,yf,xg,yg)
                    if z>best:best=z
            # Crossing of the two walls where xcorner(t)=x.
            if min(xa,xb)<=x<=max(xa,xb) and abs(xa-xb)>1e-14:
                l=lo;r=hi
                for j in range(32):
                    t=(l+r)/2;c=np.cos(t);s=np.sin(t)
                    mid=xf*c*c+xg*s*s+(yf-yg)*s*c-c+s
                    if (mid-x)*(xa-x)>0:l=t
                    else:r=t
                t=(l+r)/2
                if 1e-9<t<np.pi/2-1e-9:
                    z=_walls(t,x,xf,yf,xg,yg)
                    if z>best:best=z
        n[i]=best
    return n

def upper_roof(poly,xs):
    hull=np.asarray(poly)[ConvexHull(poly).vertices]
    hull=hull[np.argsort(hull[:,0])]
    xx,idx=np.unique(np.round(hull[:,0],12),return_index=True)
    yy=np.maximum.reduceat(hull[:,1],idx)
    return np.interp(xs,xx,yy)

def pair_area(p,q,nx=3001,details=False):
    """Full-turn pair area (spatial quadrature). Check components separately."""
    xmin=max(np.min(p[:,0]),np.min(q[:,0]))
    xmax=min(np.max(p[:,0]),np.max(q[:,0]))
    if xmin>=xmax:return (0,[]) if details else 0
    xs=np.linspace(xmin,xmax,nx)
    lo=np.maximum(niche(sectors(p),xs),1-upper_roof(q,xs))
    hi=np.minimum(upper_roof(p,xs),1-niche(sectors(q),xs))
    height=np.maximum(0,hi-lo)
    total=float(np.trapezoid(height,xs))
    if not details:return total
    active=height>1e-8
    d=np.diff(np.r_[False,active,False].astype(int))
    comps=[]
    for i,j in zip(np.where(d==1)[0],np.where(d==-1)[0]):
        a=max(0,i-1);b=min(nx,j+1)
        comps.append(float(np.trapezoid(height[a:b],xs[a:b])))
    return total,comps

if __name__=='__main__':
    print('Exact Romik reference area:',M)
    for n in (60,160):
        p=romik_cap_polygon(n)
        for nx in (601,2401,9601):
            print('Polygon vertices',len(p),'x samples',nx,
                  'all-angle pair quadrature',pair_area(p,p,nx))
