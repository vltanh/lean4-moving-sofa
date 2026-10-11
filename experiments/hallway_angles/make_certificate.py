"""Propose dyadic boxes from a floating polygon; interval_verify checks them."""
from __future__ import annotations
import math
import numpy as np
from geometry import Motion,largest_component
from fast_geometry import fast_intersection
from interval_verify import GRID

def intersect_intervals(a,b):
    return [(max(x0,y0),min(x1,y1)) for x0,x1 in a for y0,y1 in b if max(x0,y0)<min(x1,y1)]

def propose(motion: Motion,rows: int=2048,inset: float=0.0001,subdivisions: int=8, degrees: str | None=None):
    if rows<2 or GRID%rows or not math.isfinite(inset) or inset<=0:
        raise ValueError('rows must divide 2^30; inset must be positive')
    shape=largest_component(fast_intersection(motion,subdivisions)).buffer(-inset,join_style=2)
    if shape.is_empty:raise ValueError('empty proposal')
    shape=shape.simplify(inset/8.,preserve_topology=True)
    rings=[]
    parts=[shape] if shape.geom_type=="Polygon" else list(shape.geoms)
    for part in parts:
        rings.extend(np.asarray(r.coords) for r in [part.exterior,*part.interiors])
    aa=np.concatenate([r[:-1] for r in rings]);bb=np.concatenate([r[1:] for r in rings])
    def section(y):
        crossed=(aa[:,1]<=y)!=(bb[:,1]<=y)
        a,b=aa[crossed],bb[crossed]
        xs=np.sort(a[:,0]+(y-a[:,1])*(b[:,0]-a[:,0])/(b[:,1]-a[:,1]))
        if len(xs)%2:raise ArithmeticError("odd number of slice crossings")
        return list(zip(xs[::2],xs[1::2]))
    bounds=shape.bounds
    ylo=max(1,math.ceil(bounds[1]*GRID)+1)
    yhi=min(GRID-1,math.floor(bounds[3]*GRID)-1)
    step=GRID//rows
    boxes=[]
    for row in range(rows):
        lo=max(ylo,row*step);hi=min(yhi,(row+1)*step)
        if lo>=hi:continue
        intervals=section(lo/GRID)
        for y in ((lo+hi)/(2*GRID),hi/GRID):
            intervals=intersect_intervals(intervals,section(y))
        for a,b in intervals:
            xa,xb=math.ceil(a*GRID)+1,math.floor(b*GRID)-1
            if xa<xb:boxes.append([xa,xb,lo,hi])
    return {'format':'hallway-dyadic-rectangles-v1',
        'bend_degrees':str(math.degrees(motion.beta)) if degrees is None else degrees, 'mode':motion.mode,
        'corner_hex':[[v.hex() for v in row] for row in motion.corners.tolist()],
        'grid_denominator':GRID,'boxes':boxes,
        'proposal':{'rows':rows,'inset':inset,'subdivisions':subdivisions,
                    'polygon_area_untrusted':float(shape.area)}}
