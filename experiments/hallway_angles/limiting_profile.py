"""Explicit limiting rescaled near-reversal sofa; floating diagnostics only.

The scaling is (x,y)->(epsilon*x,y), not a claimed preservation of rigid
motions under an affine map. The proof is in UNIVERSAL_LIMIT_SHAPE.md.
"""
from __future__ import annotations
import math
import numpy as np

K=math.sqrt(3)
A=K/2
D=math.cos(A)+math.sin(A)/K
T=math.tan(A)/K


def area_constant() -> float:
    return 3*(1+3*T)/(4*(1+T))


def left_boundary(u):
    u=np.asarray(u,dtype=float)
    if not np.isfinite(u).all() or np.any(np.abs(u)>.5):
        raise ValueError("left-boundary parameter must be in [-1/2,1/2]")
    x=(math.cos(A)-np.cos(K*u))/D
    y=(u*np.cos(K*u)+np.sin(K*u)/(2*K))/D
    return x,y


def upper_boundary(v):
    v=np.asarray(v,dtype=float)
    if not np.isfinite(v).all() or np.any(v<0) or np.any(v>1):
        raise ValueError("upper-boundary parameter must be in [0,1]")
    u=v-.5
    h=1+(math.cos(A)/D)*v-(np.cos(K*u)-np.sin(K*u)/K)/(2*D)
    dh=(math.cos(A)+np.cos(K*u)/2+K*np.sin(K*u)/2)/D
    return dh,h-v*dh


def profile_polygon(points_per_arc: int=513):
    """An inscribed diagnostic polygon, not an arithmetic certificate."""
    if not isinstance(points_per_arc,int) or isinstance(points_per_arc,bool) or points_per_arc<3:
        raise ValueError("at least three points per arc are required")
    v=np.linspace(0,1,points_per_arc)
    x,y=upper_boundary(v)
    lower=np.column_stack((x,-y))
    upper=np.column_stack((x[::-1],y[::-1]))
    lx,ly=left_boundary(v-.5)
    left=np.column_stack((lx[::-1],ly[::-1]))
    return np.vstack((lower,upper[1:],left))
