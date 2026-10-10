#!/usr/bin/env python3
"""Independent numerical negative control for the all-angle polygon niche solver.

30,001 sampled angles cannot exceed the continuous-angle candidate list.
Upper roofs are crosschecked against an independent supporting-facet formula.
This test is numerical validation, NOT an interval proof or an area certificate.

Run from this folder: python test_all_angle_polygon_pair.py
Requires numpy, scipy and numba.
"""
import numpy as np
from scipy.spatial import ConvexHull
from all_angle_polygon_pair import romik_cap_polygon,sectors,niche,upper_roof

def coarse_niche(poly,xs,nt=30001):
    t=np.linspace(1e-8,np.pi/2-1e-8,nt)
    c=np.cos(t);s=np.sin(t)
    f=np.max(poly[:,0,None]*c+poly[:,1,None]*s,axis=0)
    g=np.max(-poly[:,0,None]*s+poly[:,1,None]*c,axis=0)
    return np.array([max(0,float(np.max(np.minimum(
        (f-1-x*c)/s,(g-1+x*s)/c)))) for x in xs])

def test():
    base=romik_cap_polygon(70)
    rng=np.random.default_rng(15)
    for i in range(9):
        v=base.copy()
        if i:
            x,y=v[:,0],v[:,1]
            scale=np.exp(rng.uniform(-.08,.08))
            shear=rng.uniform(-.10,.10)
            yshift=rng.uniform(-.15,.15)
            v[:,0]=scale*x+shear*y
            v[:,1]=np.clip(y+y*(1-y)*yshift*np.cos(3*x),0,1)
            left,right=v[:,0].min(),v[:,0].max()
            v=np.vstack([v,[left,0],[right,0]])
        v=v[ConvexHull(v).vertices]
        xs=np.linspace(v[:,0].min()+.004,v[:,0].max()-.004,31)
        exact=niche(sectors(v),xs)
        sampled=coarse_niche(v,xs)
        facets=ConvexHull(v).equations
        upper=facets[facets[:,1]>1e-8]
        truth=np.min(-(upper[:,0,None]*xs+upper[:,2,None])/upper[:,1,None],axis=0)
        assert np.min(exact-sampled)>-1e-8
        assert np.max(np.abs(truth-upper_roof(v,xs)))<1e-8
        print('test',i,'min analytic-minus-grid',np.min(exact-sampled),
              'max roof-facet error',np.max(np.abs(truth-upper_roof(v,xs))))
    print('PASS: 9 polygon caps, 31 x values each, 30,001 sampled angles per point')

if __name__=='__main__':test()
