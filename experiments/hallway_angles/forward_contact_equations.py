"""An analytic three-phase forward contact model near the numerical crossing.

These are necessary-contact/stationary equations under a specified boundary
pattern, not a theorem of forward-class or unrestricted optimality. The signed
boundary area is not by itself a feasibility certificate.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import numpy as np


@dataclass(frozen=True)
class ForwardContactModel:
    beta: float
    T: float

    def __post_init__(self):
        if not math.isfinite(self.beta) or not math.radians(130)<=self.beta<=math.radians(145):
            raise ValueError('this contact-model implementation is restricted to bends 130..145 degrees')
        if not math.isfinite(self.T) or not 0<self.T<self.beta/2:
            raise ValueError('central half interval T must lie in (0,beta/2)')

    @property
    def constants(self):
        beta=self.beta;L=beta/2;d=math.cos(beta);s,c=math.sin(L),math.cos(L)
        mu=math.sqrt(3/(4*math.sin(beta)**2)-1)
        eta=math.sqrt((-1-2*d)/(1-2*d))
        r=(1-2*d)/(2*(1+d)*mu);z0=-2*c/(1+2*d)
        B=-2*c/(3*mu*(math.cosh(mu*self.T)+eta*math.sinh(mu*self.T)))
        return dict(L=L,d=d,s=s,c=c,mu=mu,eta=eta,r=r,z0=z0,B=B,A=1/3)

    @property
    def alpha(self):return self.beta/2-self.T

    def residual(self):
        z=self.constants;T=self.T
        return (z['eta']*(3*z['s']*math.sin(T)-z['c']*math.cos(T)-1)
                +math.tanh(z['mu']*T)*(z['s']*math.sin(T)-3*z['c']*math.cos(T)-z['eta']**2))

    @classmethod
    def solve(cls,beta:float):
        lo,hi=.65,.75
        fl,fh=cls(beta,lo).residual(),cls(beta,hi).residual()
        if not fl<0<fh:raise ValueError('no bracket for this analytic branch')
        for _ in range(60):
            mid=(lo+hi)/2
            if cls(beta,mid).residual()<0:lo=mid
            else:hi=mid
        return cls(beta,(lo+hi)/2)

    def central(self,t):
        t=np.asarray(t,dtype=float);z=self.constants
        A,B,r,z0,mu=(z[k] for k in ['A','B','r','z0','mu'])
        st,ct=np.sin(t),np.cos(t);sh,ch=np.sinh(mu*t),np.cosh(mu*t)
        x=-z0*st+B*(sh*ct-r*ch*st)
        y=A+z0*ct+B*(sh*st+r*ch*ct)
        U,W=mu-r,1+r*mu
        dx=-z0*ct+B*(U*ch*ct-W*sh*st)
        dy=-z0*st+B*(U*ch*st+W*sh*ct)
        return x,y,dx,dy

    def circle_and_vertex(self):
        x,y,_,_=self.central(-self.T);a=self.alpha
        f=-math.sin(a)*x+math.cos(a)*y
        p=float((f+(1-math.cos(a))/2)/math.sin(a))
        return p,float(x+math.sin(self.beta-a))

    def corner(self,theta):
        theta=np.atleast_1d(theta).astype(float)
        if np.any(theta<0) or np.any(theta>self.beta):raise ValueError('pose angle outside [0,beta]')
        p,xR=self.circle_and_vertex()
        flip=theta>self.beta/2;u=np.where(flip,self.beta-theta,theta)
        early=u<self.alpha;out=np.empty((len(theta),2))
        out[~early]=np.column_stack(self.central(u[~early]-self.beta/2)[:2])
        if early.any():
            t=u[early]
            f1=p*np.sin(t)+.5*np.cos(t)-.5
            f2=xR*np.sin(self.beta-t)-1
            mat=np.stack([np.column_stack([-np.sin(t),np.cos(t)]),
                          np.column_stack([np.sin(self.beta-t),np.cos(self.beta-t)])],axis=1)
            out[early]=np.linalg.solve(mat,np.column_stack([f1,f2])[...,None])[...,0]
        out[flip,0]*=-1
        return out

    def support_pair(self,theta):
        theta=np.asarray(theta,dtype=float);p,_=self.circle_and_vertex()
        f=p*np.sin(theta)+.5*np.cos(theta)-.5
        df=p*np.cos(theta)-.5*np.sin(theta)
        x,y,dx,dy=self.central(theta-self.beta/2)
        st,ct=np.sin(theta),np.cos(theta)
        central_f=-st*x+ct*y
        central_df=-ct*x-st*y-st*dx+ct*dy
        return np.where(theta<=self.alpha,f,central_f),np.where(theta<=self.alpha,df,central_df)

    def signed_area(self):
        z=self.constants;T=self.T;a=self.alpha
        A,B,r,mu,d,c,s,z0=(z[k] for k in ['A','B','r','mu','d','c','s','z0'])
        sn,cs=math.sin(T),math.cos(T);sh,ch=math.sinh(mu*T),math.cosh(mu*T)
        zx=A*sn+B*sh;zy=A*cs+r*B*ch+z0
        dx=A*cs+mu*B*ch;dy=-A*sn+r*mu*B*sh
        p,_=self.circle_and_vertex();g=p*math.sin(a)+.5*math.cos(a)
        gp=p*math.cos(a)-.5*math.sin(a)
        f=-s*zx+c*zy;fp=-s*dx+c*dy
        early=a/2-2*g*gp+p
        central=2*T+2*c*(A*sn+r*B*sh/mu+z0*T)-2*((1-d)*zx*dx+(1+d)*zy*dy)
        return early+central+2*(f+.5)*fp

    def boundary_polygon(self,points:int=1025):
        """Sample the hypothesized oriented boundary, not an inner certificate."""
        if isinstance(points,bool) or not isinstance(points,int) or points<3:raise ValueError('at least 3 points per interval')
        b=self.beta-self.alpha
        theta=np.concatenate([np.linspace(0,self.alpha,points),np.linspace(self.alpha,b,points)[1:]])
        f,df=self.support_pair(theta)
        n=np.column_stack([-np.sin(theta),np.cos(theta)]);jn=np.column_stack([-np.cos(theta),-np.sin(theta)])
        inner=f[:,None]*n+df[:,None]*jn;outer=inner+n
        reflected=lambda p: p[::-1]*np.array([-1,1])
        corner=np.column_stack(self.central(np.linspace(self.T,-self.T,points))[:2])
        return np.vstack([reflected(outer),outer,inner,corner,reflected(inner)])
