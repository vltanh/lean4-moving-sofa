"""Numerical polygon discretization of Baek's Q, not a proof or a CI target.

Q follows MovingSofaOptimality/Optimality/UpperBound.lean, definition upperQ.
The unknowns are support values of three bodies K,B,D, not a Gerver ansatz.
Only finite constraints are imposed; between-node defects are reported separately.
"""
from __future__ import annotations

import argparse
import json
import platform
import time
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import scipy
from numpy.polynomial.legendre import leggauss
from scipy.linalg import null_space
from scipy.optimize import linprog, minimize

PI = np.pi


def unit(t: float) -> np.ndarray:
    return np.array([np.cos(t), np.sin(t)])


def tangent(t: float) -> np.ndarray:
    return np.array([-np.sin(t), np.cos(t)])


@dataclass
class QProblem:
    """All arrays include a final constant coordinate for affine expressions."""
    intervals: int
    phi: float = 0.04
    quadrature: int = 8
    wall_samples: int = 3

    def __post_init__(self) -> None:
        if self.intervals < 4 or self.intervals % 2:
            raise ValueError('intervals must be even and at least 4')
        if not 0 < self.phi < PI / 4:
            raise ValueError('phi must lie strictly between 0 and pi/4')
        if self.quadrature < 2 or self.wall_samples < 1:
            raise ValueError('quadrature >= 2 and wall_samples >= 1 required')
        quarter = np.unique(np.r_[np.linspace(0, PI / 2, self.intervals + 1),
                                   self.phi, PI / 2 - self.phi])
        self.angles = np.concatenate([quarter[:-1] + k * PI / 2 for k in range(4)])
        self.m = len(quarter) - 1
        n = len(self.angles)
        self.size = 10 * self.m + 1
        d = self.size + 1
        self.support = np.zeros((3, n, d))
        nk = 2 * self.m + 1
        self.support[0, :nk, :nk] = np.eye(nk)
        for i in range(nk, n):
            c = np.cos(self.angles[i])
            self.support[0, i, 0 if c > 0 else 2 * self.m] = abs(c)
        self.support[1, :, nk:nk+n] = np.eye(n)
        self.support[2, :, nk+n:nk+2*n] = np.eye(n)
        self.vertices = np.empty((3, n, 2, d))
        for i, a in enumerate(self.angles):
            j = (i + 1) % n
            b = self.angles[j] if j else 2 * PI
            inverse = np.linalg.inv(np.stack([unit(a), unit(b)]))
            self.vertices[:, i] = np.einsum('ab,kbd->kad', inverse,
                self.support[:, [i, j]])
        self.edges = np.empty((3, n, d))
        for i, a in enumerate(self.angles):
            self.edges[:, i] = np.einsum('a,kad->kd', tangent(a),
                self.vertices[:, i] - self.vertices[:, i-1])
        self._assemble_constraints()
        self._assemble_objective()

    def index(self, t: float) -> int:
        distance = abs((self.angles - t + PI) % (2 * PI) - PI)
        i = int(np.argmin(distance))
        if distance[i] > 1e-10:
            raise ValueError('requested angle is not a fan normal')
        return i

    def support_row(self, body: int, t: float, derivative: bool = False) -> np.ndarray:
        t = float(t % (2 * PI))
        i = int(np.searchsorted(self.angles, t, side='right') - 1)
        return (tangent(t) if derivative else unit(t)) @ self.vertices[body, i]

    def corner_rows(self, t: float, derivative: bool = False) -> np.ndarray:
        h = self.support_row(0, t).copy()
        k = self.support_row(0, t + PI / 2).copy()
        h[-1] -= 1
        k[-1] -= 1
        if derivative:
            hp = self.support_row(0, t, True)
            kp = self.support_row(0, t + PI / 2, True)
            return np.outer(unit(t), hp-k) + np.outer(tangent(t), h+kp)
        return np.outer(unit(t), h) + np.outer(tangent(t), k)

    def _assemble_constraints(self) -> None:
        s = self.support
        eq, ge = [], []
        def equal(row: np.ndarray, rhs: float = 0) -> None:
            row = row.copy(); row[-1] -= rhs; eq.append(row)
        def lower(row: np.ndarray, rhs: float = 0) -> None:
            row = row.copy(); row[-1] -= rhs; ge.append(row)
        equal(s[0, self.m], 1)
        equal(s[0, 0] - s[0, 2*self.m])
        for body in range(3):
            for row in self.edges[body]:
                if np.linalg.norm(row) > 1e-10:
                    lower(row)
        for body in (1, 2):
            for row in s[0] - s[body]:
                lower(row)
        a = self.index(self.phi)
        b = self.index(PI / 2 - self.phi)
        for body, lo, hi, shift in [(1,a,self.m,2*self.m), (2,self.m,self.m+b,2*self.m)]:
            equal(s[0,lo] + s[body,(lo+shift) % len(self.angles)], 1)
            equal(s[0,hi] + s[body,(hi+shift) % len(self.angles)], 1)
            for i in range(lo, hi):
                for t in np.linspace(self.angles[i], self.angles[i+1], self.wall_samples+1):
                    lower(-self.support_row(0,t)-self.support_row(body,t+PI), -1)
        # Polygonal analogue of f,g >= 1, checked at both ends of each cell.
        # f,g are sinusoidal inside a cell; endpoint bounds imply interval bounds.
        for i in range(self.m):
            difference = self.vertices[0,i+self.m] - self.vertices[0,i]
            for t in (self.angles[i],self.angles[i+1]):
                lower(tangent(t) @ difference, 1)
                lower(-unit(t) @ difference, 1)
        self.eq = np.array(eq)
        self.ge = np.array(ge)
        _, indices = np.unique(np.round(self.ge,12), axis=0, return_index=True)
        self.ge = self.ge[np.sort(indices)]
        self.particular = np.linalg.lstsq(self.eq[:,:-1], -self.eq[:,-1], rcond=None)[0]
        self.basis = null_space(self.eq[:,:-1])
        self.transform = np.zeros((self.size+1,self.basis.shape[1]+1))
        self.transform[:-1,:-1] = self.basis
        self.transform[:-1,-1] = self.particular
        self.transform[-1,-1] = 1

    @staticmethod
    def cross_matrix(a: np.ndarray, b: np.ndarray) -> np.ndarray:
        return .5 * (np.outer(a[0],b[1]) - np.outer(a[1],b[0]))

    def _assemble_objective(self) -> None:
        s = self.support
        mat = .5 * np.einsum('ij,ik->jk',s[0],self.edges[0])
        self.area_matrix = (mat + mat.T) / 2
        for body,lo,hi in [(1,self.index(PI+self.phi),3*self.m),
                           (2,3*self.m,self.index(2*PI-self.phi))]:
            mat += .5 * np.einsum('ij,ik->jk',s[body,lo+1:hi],self.edges[body,lo+1:hi])
        mat += self.cross_matrix(self.vertices[2,self.index(2*PI-self.phi)-1],
                                 self.corner_rows(PI/2-self.phi))
        mat += self.cross_matrix(self.corner_rows(self.phi),
                                 self.vertices[1,self.index(PI+self.phi)])
        nodes,weights = leggauss(self.quadrature)
        for i in range(self.index(self.phi),self.index(PI/2-self.phi)):
            a,b = self.angles[i:i+2]
            for t,w in zip((a+b)/2+(b-a)*nodes/2,weights*(b-a)/2):
                mat -= w*self.cross_matrix(self.corner_rows(t), self.corner_rows(t,True))
        self.matrix = (mat + mat.T) / 2
        self.reduced = self.transform.T @ self.matrix @ self.transform
        self.reduced = (self.reduced+self.reduced.T)/2

    def objective(self, x: np.ndarray) -> float:
        z = np.r_[x,1.]
        return float(z @ self.matrix @ z)

    def constraint_residuals(self, x: np.ndarray) -> dict:
        z = np.r_[x,1.]
        return {'equality_max_abs':float(np.max(abs(self.eq@z))),
                'inequality_min':float(np.min(self.ge@z))}

    def solve(self, seed: int = 0, maxiter: int = 600) -> tuple[np.ndarray,dict]:
        start = time.perf_counter()
        constraint = self.ge @ self.transform
        a,b = constraint[:,:-1],constraint[:,-1]
        norms = np.linalg.norm(a,axis=1)
        keep = norms > 1e-10
        if np.any(b[~keep] < -1e-9):
            raise RuntimeError('inconsistent constant constraint')
        a,b = a[keep]/norms[keep,None],b[keep]/norms[keep]
        rng = np.random.default_rng(seed)
        # A genuine LP feasible point; no Gerver data or area enters the solve.
        lp = linprog(rng.normal(size=a.shape[1]), A_ub=-a,b_ub=b,
                     bounds=[(-10,10)]*a.shape[1],method='highs')
        if not lp.success:
            raise RuntimeError(f'feasible-start LP failed: {lp.message}')
        h = self.reduced[:-1,:-1]
        c = self.reduced[:-1,-1]
        constant = self.reduced[-1,-1]
        def fun(y):
            return -float(y@h@y+2*c@y+constant)
        def jac(y):
            return -2*(h@y+c)
        result = minimize(fun,lp.x,jac=jac,method='SLSQP',constraints=[
            {'type':'ineq','fun':lambda y:a@y+b,'jac':lambda y:a}],
            options={'ftol':1e-11,'maxiter':maxiter})
        x = self.particular+self.basis@result.x
        eigenvalues = np.linalg.eigvalsh(2*h)
        out = {'intervals':self.intervals,'phi':self.phi,'wall_samples':self.wall_samples,
               'quadrature':self.quadrature,'seed':seed,'variables':self.size,
               'reduced_variables':len(result.x),'success':bool(result.success),
               'message':str(result.message),'iterations':int(result.nit),'q':self.objective(x),
               'cap_area':float(np.r_[x,1.]@self.area_matrix@np.r_[x,1.]),
               'hessian_max_eigenvalue':float(eigenvalues[-1]),
               'hessian_min_eigenvalue':float(eigenvalues[0]),
               'hessian_near_zero_count':int(np.count_nonzero(abs(eigenvalues)<1e-8)),
               'elapsed_seconds':time.perf_counter()-start,**self.constraint_residuals(x)}
        return x,out

    def validate(self,x:np.ndarray,samples:int=1024) -> dict:
        from shapely.geometry import Polygon, MultiPoint
        from shapely.ops import unary_union
        z = np.r_[x,1.]
        vertices = self.vertices @ z
        cap = MultiPoint(vertices[0]).convex_hull
        if self.constraint_residuals(x)['inequality_min'] < -1e-6:
            return {'validation_error':'solver output is substantially infeasible'}
        wall_defect = 0.
        for body,lo,hi in [(1,self.index(self.phi),self.m),
                           (2,self.m,self.index(PI-self.phi))]:
            for i in range(lo,hi):
                v = vertices[0,i] - vertices[body,(i+2*self.m)%len(self.angles)]
                a,b = self.angles[i:i+2]
                candidates = [a,b]
                radial = np.arctan2(v[1],v[0]) % (2*PI)
                if a <= radial <= b:
                    candidates.append(radial)
                wall_defect = max(wall_defect,max(float(v@unit(t)-1) for t in candidates))
        wedges = []
        for t in np.linspace(0,PI/2,samples+1)[1:-1]:
            corner = self.corner_rows(t) @ z
            if corner[1] > 0:
                h = self.support_row(0,t)@z
                k = self.support_row(0,t+PI/2)@z
                wedges.append(Polygon([corner,[(h-1)/np.cos(t),0],[(1-k)/np.sin(t),0]]))
        niche = unary_union(wedges)
        sofa = cap.difference(niche)
        parts = [sofa] if sofa.geom_type == 'Polygon' else [g for g in sofa.geoms if g.area>1e-10]
        mirror = MultiPoint(vertices[0]*[-1,1]).convex_hull
        return {'validation_samples':samples, 'between_node_wall_violation':wall_defect,
                'cap_hull_area_discrepancy':float(abs(cap.area-z@self.area_matrix@z)),
                'sampled_sofa_area':float(sofa.area),
                'sampled_sofa_functional':float(cap.area-niche.area),
                'sampled_niche_outside_cap_area':float(niche.difference(cap).area),
                'positive_area_components':len(parts), 'polygon_valid':bool(sofa.is_valid),
                'reflection_hausdorff':float(cap.hausdorff_distance(mirror))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--intervals',type=int,nargs='+',default=[4,8,16])
    parser.add_argument('--phi',type=float,default=.04)
    parser.add_argument('--seeds',type=int,nargs='+',default=[0])
    parser.add_argument('--wall-samples',type=int,default=3)
    parser.add_argument('--validation-samples',type=int,default=1024)
    parser.add_argument('--output',type=Path,default=Path('results.json'))
    args = parser.parse_args()
    results=[]
    for n in args.intervals:
        problem=QProblem(n,args.phi,wall_samples=args.wall_samples)
        for seed in args.seeds:
            x,row=problem.solve(seed)
            row.update(problem.validate(x,args.validation_samples))
            row['cap_normal_angles']=problem.angles[:2*problem.m+1].tolist()
            row['cap_support']=x[:2*problem.m+1].tolist()
            row['all_variables']=x.tolist()
            results.append(row)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps({'environment':{'python':platform.python_version(),
                'numpy':np.__version__,'scipy':scipy.__version__},'runs':results},indent=2)+'\n')
            print(json.dumps({k:v for k,v in row.items() if not isinstance(v,list)}),flush=True)


if __name__ == '__main__':
    main()
