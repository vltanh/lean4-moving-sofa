"""Explicit reverse-turn sofa and its area (floating-point evaluation only).

The analytic formulas are in REVERSE_QUADRATIC_THEOREM.md and the theorem's
scope is in REVERSE_MAIN_THEOREM.md. These routines are not the interval
certificate checker; they provide reproducible diagnostics and polygons.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import numpy as np


@dataclass(frozen=True)
class ReverseSofa:
    epsilon: float

    def __post_init__(self) -> None:
        e = self.epsilon
        if not math.isfinite(e) or not 0 < e < math.pi/2:
            raise ValueError("epsilon=pi-beta must be strictly between 0 and pi/2")

    @property
    def constants(self) -> dict[str, float]:
        e = self.epsilon
        s, c = math.sin(e/2), math.cos(e/2)
        d, q = math.cos(e), math.sin(e)
        m = 2-d
        k = math.sqrt(1+3/q**2)
        K = k*e/2
        eta = math.sqrt(m/(2+d))
        r = s*eta/c
        denominator = math.cos(K)+eta*math.sin(K)
        z0 = -2*s/m
        B = -d/(2*m*s*denominator)
        A = (c/2+r*B*math.sin(K))/s
        return dict(s=s, c=c, d=d, q=q, m=m, a=1-d, b=1+d, k=k, K=K,
                    eta=eta, r=r, denominator=denominator, z0=z0, B=B, A=A)

    def corner(self, t) -> tuple[np.ndarray, ...]:
        """x,y,x',y',x'',y'' for -epsilon/2 <= t <= epsilon/2."""
        t = np.asarray(t, dtype=float)
        if not np.isfinite(t).all() or np.any(np.abs(t) > self.epsilon/2+1e-14):
            raise ValueError("corner parameter outside the rotation interval")
        z = self.constants
        k, r, z0, B, A = (z[n] for n in ("k", "r", "z0", "B", "A"))
        ct, st, ck, sk = np.cos(t), np.sin(t), np.cos(k*t), np.sin(k*t)
        x = A+z0*ct+B*(ck*ct-r*sk*st)
        y = -z0*st-B*(ck*st+r*sk*ct)
        xd = -z0*st-B*((k+r)*sk*ct+(1+r*k)*ck*st)
        yd = -z0*ct-B*((1+r*k)*ck*ct-(k+r)*sk*st)
        xdd = -z0*ct-B*((k*k+1+2*r*k)*ck*ct-(2*k+r*(k*k+1))*sk*st)
        ydd = z0*st+B*((2*k+r*(k*k+1))*sk*ct+(k*k+1+2*r*k)*ck*st)
        return x, y, xd, yd, xdd, ydd

    def support(self, phi) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        """Upper support h, its derivative, and curvature radius h+h''."""
        phi = np.asarray(phi, dtype=float)
        if not np.isfinite(phi).all() or np.any(phi < 0) or np.any(phi > self.epsilon):
            raise ValueError("support angle outside [0,epsilon]")
        z = self.constants
        t = phi-self.epsilon/2
        k, eta, A, m = (z[n] for n in ("k", "eta", "A", "m"))
        coef = z["d"]/(2*m*z["denominator"])
        ck, sk = np.cos(k*t), np.sin(k*t)
        h = 1/m+A*np.sin(phi)-coef*(ck-eta*sk)
        dh = A*np.cos(phi)+coef*k*(sk+eta*ck)
        rho = 1/m+coef*(k*k-1)*(ck-eta*sk)
        return h, dh, rho

    def area(self) -> float:
        """Stable elementary formula V(epsilon), not a rounded lower bound."""
        z = self.constants
        ratio = z["eta"]*math.sin(z["K"])/z["denominator"]
        return (self.epsilon/z["m"]+(1+2*z["d"])/(4*z["q"])
                +3*z["d"]**2*ratio/(2*z["q"]*z["m"]**2))

    def polygon(self, points_per_arc: int = 257) -> np.ndarray:
        """Counterclockwise inscribed polygon for diagnostics, not a certificate."""
        if not isinstance(points_per_arc, int) or points_per_arc < 3:
            raise ValueError("at least three samples per arc are required")
        phi = np.linspace(0, self.epsilon, points_per_arc)
        h, dh, _ = self.support(phi)
        xx = h*np.sin(phi)+dh*np.cos(phi)
        yy = h*np.cos(phi)-dh*np.sin(phi)
        lower = np.column_stack((xx, -yy))
        upper = np.column_stack((xx[::-1], yy[::-1]))
        x, y, *_ = self.corner(phi-self.epsilon/2)
        left = np.column_stack((x[::-1], y[::-1]))
        return np.vstack((lower, upper[1:], left))


def width_majorant(epsilon: float, width: float) -> float:
    if not math.isfinite(width) or not 0 <= width <= 1:
        raise ValueError("actual width must be in [0,1]")
    z = ReverseSofa(epsilon).constants
    T = z["eta"]*math.tan(z["K"])
    d, m, q = z["d"], z["m"], z["q"]
    c0 = -(T*d*d-4*T*d-2*T+d*d-4*d+4)/((1+T)*m*m)
    c1 = -2*(T*d+T+d-2)/((1+T)*m)
    c2 = (2*T*d+3*T+2*d-3)/(4*(1+T))
    return epsilon/m+(c0+c1*width+c2*width*width)/q


def asymptotic_constant() -> float:
    T0 = math.tan(math.sqrt(3)/2)/math.sqrt(3)
    return 3*(1+3*T0)/(4*(1+T0))
