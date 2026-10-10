"""Numerical diagnostic, NOT a certificate: compare sampled P_J with exact local quadratic formula.

The two middle-arc support perturbations are smooth, compactly supported, and small.
This script approximates the true niche by sampling hallway angles: its P_J values
are upper approximations only modulo numerical integration error, not rigorous bounds.

Requires numpy; no global optimization, no Lean, no claim about arbitrary cap pairs.
"""
import json
import math
import numpy as np

L = math.pi / 2
lo, hi = 7/25, 3/10
for _ in range(80):
    mid=(lo+hi)/2
    if 4*mid**3+3*mid-1<0:lo=mid
    else:hi=mid
Y=(lo+hi)/2
beta=math.atan(Y)
m=math.sqrt(1+Y*Y)/(3*Y)
R=math.cos(beta)/math.sin(3*beta/2+math.pi/8)


def supports(t):
    s,c=np.sin(t),np.cos(t)
    z=t/2+math.pi/8
    f=np.where(t<beta,m*c+s/2,np.where(t>L-beta,m*c/2+s/2+.5,R*np.cos(z)+s/2))
    g=np.where(t<beta,m*s/2+c/2+.5,np.where(t>L-beta,m*s+c/2,R*np.sin(z)+c/2))
    return f,g


def bump(t, a, b):
    theta=np.pi*(t-a)/(b-a)
    inside=(t>=a)&(t<=b)
    return np.where(inside,np.sin(theta)**4,0.),np.where(inside,4*np.sin(theta)**3*np.cos(theta)*np.pi/(b-a),0.)


def pj_sampled(eps, sign, nx=650, nt=1700, nc=22000):
    t=np.linspace(1e-6,L-1e-6,nt)
    c,s=np.cos(t),np.sin(t)
    ph,_=bump(t,.55,.95)
    ps,_=bump(t,.60,1.)
    ff,gg=supports(t)
    ff=ff+eps*ph
    gg=gg+eps*sign*ps
    T=np.linspace(beta,L,nc)
    C,S=np.cos(T),np.sin(T)
    f,_=supports(T)
    fp=np.where(T<L-beta,-R/2*np.sin(T/2+math.pi/8)+C/2,-m*S/2+C/2)
    bh,bhp=bump(T,.55,.95)
    f+=eps*bh
    fp+=eps*bhp
    xo=f*C-fp*S
    yo=f*S+fp*C
    T=np.linspace(0,L-beta,nc)
    C,S=np.cos(T),np.sin(T)
    _,g=supports(T)
    gp=np.where(T<beta,m*C/2-S/2,R/2*np.cos(T/2+math.pi/8)-S/2)
    bh,bhp=bump(T,.60,1.)
    g+=eps*sign*bh
    gp+=eps*sign*bhp
    xg=-g*S-gp*C
    yg=g*C-gp*S
    xl=np.linspace(-m,-m/2,nx)
    xj=np.linspace(-m/2,m/2,2*nx)
    xr=np.linspace(m/2,m,nx)
    x=np.concatenate((xl,xj,xr))
    roof=np.trapezoid(np.interp(xl,xg[::-1],yg[::-1]),xl)+np.trapezoid(np.interp(xr,xo[::-1],yo[::-1]),xr)
    first=(ff[None,:]-1-x[:,None]*c[None,:])/s[None,:]
    second=(gg[None,:]-1+x[:,None]*s[None,:])/c[None,:]
    niche=np.maximum(0,np.max(np.minimum(first,second),axis=1))
    return float(roof-np.trapezoid(niche[nx:3*nx],xj))


def quadratic(sign):
    t=np.linspace(.55,1.0,16001)
    ph,php=bump(t,.55,.95)
    ps,psp=bump(t,.60,1.)
    ps,psp=sign*ps,sign*psp
    return float(np.trapezoid(.5*(ph*ph+ps*ps)-php*php-psp*psp-ph*psp,t))


def main():
    base=pj_sampled(0,0)
    cases=[]
    for sign,label in [(0,'one_arc'),(1,'two_arcs_same'),(-1,'two_arcs_opposite')]:
        q=quadratic(sign)
        for eps in (.0005,.001):
            sampled=pj_sampled(eps,sign)
            predicted=eps*eps*q
            observed=sampled-base
            residual=observed-predicted
            cases.append({'case':label,'epsilon':eps,'predicted_change':predicted,'sampled_change':observed,'absolute_residual':abs(residual)})
            assert abs(residual)<7e-7, (label,eps,residual)
    print(json.dumps({'status':'sampled_diagnostics_passed','certified':False,'angle_count':1700,'horizontal_points':2600,'base_sampled_value':base,'cases':cases},indent=2))


if __name__=='__main__':main()
