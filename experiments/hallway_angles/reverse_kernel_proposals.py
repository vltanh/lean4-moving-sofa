"""Numerical proposals for exact reverse-kernel dual certificates.

This module alone uses NumPy/SciPy. Its outputs are not accepted as proofs;
reverse_kernel_dual.py independently checks their continuum inequalities.
"""
from fractions import Fraction as F
from math import cos
import numpy as np
from scipy.optimize import linprog


def matrix(e,knots,ts):
    l=np.asarray(knots[:-1],float)[None,:];h=np.asarray(knots[1:],float)[None,:]
    t=np.asarray(ts,float)[:,None];D=h-l
    U=np.minimum(t,h);z=np.maximum(0,U-l)
    Itot=np.cos(e*(t-U))-np.cos(e*(t-l))
    Iright=(z*np.cos(e*(t-U))+(np.sin(e*(t-U))-np.sin(e*(t-l)))/e)/D
    Ileft=Itot-Iright
    selfm=np.stack([np.where(U>l,Ileft,0),np.where(U>l,Iright,0)],axis=2).reshape(len(ts),-1)
    L=np.maximum(l,1-t);z=L-l
    Jtot=np.cos(e*(t+L))-np.cos(e*(t+h))
    Jright=(-D*np.cos(e*(t+h))+z*np.cos(e*(t+L))+(np.sin(e*(t+h))-np.sin(e*(t+L)))/e)/D
    Jleft=Jtot-Jright
    cross=np.stack([np.where(h>L,Jleft,0),np.where(h>L,Jright,0)],axis=2).reshape(len(ts),-1)
    return selfm,cross


def make(e,u=None,N=24,checks=4,target=.86):
    if not 0<e<1.571 or N<2 or checks<1:
        raise ValueError('invalid proposal parameters')
    if u is not None and not 0<=u<=F(1,2):
        raise ValueError('u must lie in the first half')
    knots=sorted(set([F(j,N) for j in range(N+1)]+([] if u is None else [F(u),1-F(u)])))
    qq=[];cell=[];weight=[]
    for j,(l,h) in enumerate(zip(knots[:-1],knots[1:])):
        for k in range(checks+1):qq.append(l+(h-l)*F(k,checks));cell.append(j);weight.append(k/checks)
    ts=np.array(list(map(float,qq)));n=len(knots)-1
    si,cr=matrix(e,knots,ts)
    ident=np.zeros((len(ts),2*n));ident[np.arange(len(ts)),2*np.array(cell)]=1-np.array(weight)
    ident[np.arange(len(ts)),2*np.array(cell)+1]=weight
    R=1/(1-cos(e));c=R/2
    M=np.block([[ident+c*si,c*cr],[c*cr,ident+c*si]])
    mom=e*np.sin(e*ts);mom=np.r_[mom,mom]
    f=np.zeros(2*len(ts))
    if u is None:f[:len(ts)]=e*np.sin(e*ts)
    else:
        uu=float(u)
        for j,(l,h) in enumerate(zip(knots[:-1],knots[1:])):
            mask=np.array(cell)==j
            if (l+h)/2>=u:f[:len(ts)][mask]=e*np.sin(e*(ts[mask]+1-uu))
            if (l+h)/2>=1-u:f[len(ts):][mask]=e*np.sin(e*(ts[mask]-(1-uu)))
    full=np.c_[M,mom,-mom]
    cost=R*np.repeat(np.diff(list(map(float,knots)))/2,2)
    obj=np.r_[cost,cost,1.,-.983]
    res=linprog(obj,A_ub=-full,b_ub=-f,bounds=(0,None),method='highs')
    if not res.success:raise RuntimeError(res.message)
    return dict(e=e,u=None if u is None else str(u),knots=list(map(str,knots)),
                lam=res.x[:4*n].tolist(),eta=float(res.x[-2]-res.x[-1]),
                cost=res.fun,target=target if u is None else 1+cos(e),
                nominal_margin=(target if u is None else 1+cos(e))-res.fun)
