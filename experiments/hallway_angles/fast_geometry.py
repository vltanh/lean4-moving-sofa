"""Equivalent polygon operations with bounded-size wedge cuts.

Every cut is intersected with the bounding rectangle rather than the evolving
cap: C minus (W intersect B) = C minus W whenever C is a subset of B. The enclosure
is still floating-point geometry, NOT a machine-certified decimal bound.
"""
from __future__ import annotations
import math
import numpy as np
from shapely.geometry import Polygon, MultiPoint
from shapely.ops import unary_union
from geometry import Motion, normals, polygons, largest_component
from pressure import clip, cap_polygon
from swept import offset_convex_intersection


def fast_intersection(motion: Motion, subdivisions: int = 1):
    angles,corners=motion.sample(subdivisions)
    ns=normals(motion.beta,angles).reshape(-1,2)
    offsets=np.sum(ns*np.repeat(corners,2,axis=0),axis=1)
    base=motion.bounding_rectangle()
    cap=cap_polygon(base,ns,offsets)
    if len(cap)<3: return Polygon()
    cuts=[]
    for i in range(len(corners)):
        w=clip(clip(base,ns[2*i],offsets[2*i]),ns[2*i+1],offsets[2*i+1])
        if len(w)>=3: cuts.append(Polygon(w))
    out=Polygon(cap).difference(unary_union(cuts)) if cuts else Polygon(cap)
    if not out.is_valid: raise ArithmeticError('invalid GEOS intersection')
    return out


def enclose_fast(motion: Motion, subdivisions: int = 32, audit: bool = False):
    raw=fast_intersection(motion,subdivisions)
    parts=list(polygons(raw))
    record={'method':'swept_hull_second_order_rectangular_cuts',
        'samples':(len(motion.corners)-1)*subdivisions+1,
        'sampled_area':float(largest_component(raw).area),'sampled_total_area':float(raw.area),
        'sampled_components':len(parts),'inner_area':0.,'inner_components':0.,
        'audit_outside_area':0. if audit else None}
    if not parts: return record,Polygon()
    verts=np.concatenate([np.asarray(p.exterior.coords) for p in parts])
    radius=max(float(np.linalg.norm(verts-c,axis=1).max()) for c in motion.corners)
    angles,corners=motion.sample(subdivisions)
    ns=normals(motion.beta,angles)
    delta=abs(motion.turn)/(len(angles)-1)
    d=float(np.linalg.norm(np.diff(motion.corners,axis=0),axis=1).max())/subdivisions
    guard=1e-10*max(1.,radius)
    outer_margin=(radius+2*d/delta)*delta**2/8+guard
    sweep_margin=radius*delta**2/8+guard
    record.update(radius_bound=radius,outer_margin=outer_margin,sweep_margin=sweep_margin)
    base=motion.bounding_rectangle()
    cap=base.copy()
    for pair,c in zip(ns,corners,strict=True):
        for n in pair: cap=clip(cap,n,float(n@c+1.-outer_margin))
        if len(cap)<3: return record,Polygon()
    padding=2*radius*math.sin(delta/2)+d+1.
    lo=base.min(axis=0)-padding;hi=base.max(axis=0)+padding
    expanded=np.array([[lo[0],lo[1]],[hi[0],lo[1]],[hi[0],hi[1]],[lo[0],hi[1]]])
    cuts=[];previous=None
    for pair,c in zip(ns,corners,strict=True):
        w=clip(clip(expanded,pair[0],float(pair[0]@c)),pair[1],float(pair[1]@c))
        if previous is not None:
            pts=np.vstack((previous,w))
            if len(pts):
                hull=MultiPoint(pts).convex_hull
                if hull.geom_type=='Polygon':
                    # Same set inside cap; this avoids quadratic-size GEOS cuts.
                    cut=offset_convex_intersection(base,hull,sweep_margin)
                    if cut.area>0: cuts.append(cut)
                elif not hull.is_empty and hull.distance(Polygon(cap))<=sweep_margin:
                    raise ArithmeticError('degenerate swept hull meets cap')
        previous=w
    out=Polygon(cap).difference(unary_union(cuts)) if cuts else Polygon(cap)
    if not out.is_valid: raise ArithmeticError('invalid GEOS swept enclosure')
    inner=largest_component(out)
    record.update(inner_area=float(inner.area),inner_components=len(list(polygons(out))))
    if audit:
        denser=fast_intersection(motion,subdivisions*2)
        record['audit_outside_area']=float(inner.difference(denser).area)
    return record,inner
