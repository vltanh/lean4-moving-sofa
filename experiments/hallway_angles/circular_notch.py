"""All-angle circular-notch construction; floating-point diagnostics only.

The exact argument and motion are in CIRCULAR_NOTCH_CONSTRUCTION.md.
Floating membership and quadrature tests are not interval certificates.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import numpy as np


@dataclass(frozen=True)
class CircularNotchSofa:
    beta: float
    radius: float | None = None

    def __post_init__(self) -> None:
        if not math.isfinite(self.beta) or not 0<self.beta<math.pi:
            raise ValueError("bend must lie strictly between zero and pi")
        q,c=math.sin(self.beta),math.cos(self.beta)
        denominator=self.beta-q*c
        if denominator<=0:
            raise ArithmeticError("angle too small for this floating evaluator")
        r=q*q/denominator if self.radius is None else self.radius
        if not math.isfinite(r) or not 0<r<1/math.tan(self.beta/2):
            raise ValueError("radius must be positive and leave a connecting top region")
        object.__setattr__(self,"radius",float(r))

    @property
    def disk_radius(self) -> float:
        return self.radius/math.sin(self.beta)

    @property
    def disk_center_height(self) -> float:
        return -self.radius/math.tan(self.beta)

    @property
    def top_height(self) -> float:
        return self.radius*math.tan(self.beta/2)

    def area(self) -> float:
        q,c=math.sin(self.beta),math.cos(self.beta)
        return math.pi/2+2*self.radius-(self.beta-q*c)*self.radius**2/q**2

    def corner(self,theta):
        theta=np.asarray(theta,dtype=float)
        if not np.isfinite(theta).all() or np.any(theta<0) or np.any(theta>self.beta):
            raise ValueError("orientation must lie in [0,beta]")
        scale=self.radius/math.sin(self.beta)
        return np.stack((scale*np.sin(self.beta-2*theta),
                         scale*(np.cos(self.beta-2*theta)-math.cos(self.beta))),axis=-1)

    def contains(self,points):
        p=np.asarray(points,dtype=float)
        if p.ndim<1 or p.shape[-1]!=2 or not np.isfinite(p).all():
            raise ValueError("points must have finite final coordinate dimension two")
        x,y=p[...,0],p[...,1]
        dx=np.maximum(np.abs(x)-self.radius,0)
        in_stadium=(y>=0)&(y<=1)&(dx*dx+y*y<=1)
        out_of_disk=x*x+(y-self.disk_center_height)**2>=self.disk_radius**2
        return in_stadium&out_of_disk
