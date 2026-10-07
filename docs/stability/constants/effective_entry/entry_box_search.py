"""Exact rational OUTER bound from finitely many supporting hallways.

This searches terminal-angle boxes, not the full local shape neighborhood.
Every reported upper bound is from all retained frontier boxes. Stopping early
returns inconclusive, never a fabricated positive separation gap.
"""
from __future__ import annotations
from fractions import Fraction as Q
from dataclasses import dataclass
from heapq import heappop,heappush
import json,time,argparse

P=tuple[Q,Q]
def normal(r:Q)->P:return (1-r*r)/(1+r*r),2*r/(1+r*r)
def dot(p:P,n:P)->Q:return p[0]*n[0]+p[1]*n[1]
def clip(poly:list[P],n:P,h:Q)->list[P]:
    if not poly:return []
    out=[];a=poly[-1];da=dot(a,n)-h
    for b in poly:
        db=dot(b,n)-h
        if (da<=0)!=(db<=0):
            t=da/(da-db);out.append((a[0]+t*(b[0]-a[0]),a[1]+t*(b[1]-a[1])))
        if db<=0:out.append(b)
        a,da=b,db
    return out


def area(poly:list[P])->Q:
    if len(poly)<3:return Q(0)
    return abs(sum((a[0]*b[1]-a[1]*b[0] for a,b in zip(poly,poly[1:]+poly[:1])),Q(0)))/2


def hallway(polys,n,box):
    (ul,uu),(vl,vu)=box;v=(-n[1],n[0]);out=[]
    for p in polys:
        p=clip(clip(p,n,uu),v,vu)
        if not p:continue
        # Disjoint interiors; the shared cutting line has zero area.
        p1=clip(p,(-n[0],-n[1]),1-ul)
        p2=clip(clip(p,n,ul-1),(-v[0],-v[1]),1-vl)
        if len(p1)>=3:out.append(p1)
        if len(p2)>=3:out.append(p2)
    return out


@dataclass
class Search:
    terminal_lo:Q
    terminal_hi:Q
    intermediate:tuple[Q,...]=(Q(1,10),Q(1,4),Q(2,5),Q(3,5))
    radius:Q=Q(3)
    def __post_init__(self):
        assert Q(0)<self.terminal_lo<=self.terminal_hi<=1
        assert all(Q(0)<r<=self.terminal_lo for r in self.intermediate)
        self.normals=[normal(r) for r in self.intermediate]
        self.n=normal(self.terminal_lo);n1=normal(self.terminal_hi)
        # |x|<=3 and 0<=y<=1; both coordinate changes are monotone.
        error=self.radius*(self.n[0]-n1[0])+(n1[1]-self.n[1])
        self.terminal_width=1+2*error
        # Area>=2.2 implies span>=2.2 and centered extreme x coordinates ±r, r>=1.1.
        self.root=[]
        for c,s in self.normals:
            self.root.extend([(Q(11,10)*c,self.radius*c+s),(Q(11,10)*s,self.radius*s+c)])
        self.root.append((Q(11,10)*self.n[0],self.radius*self.n[0]+self.n[1]))
        self.root=tuple(self.root)
    def polygons(self,box):
        R=self.radius
        polys=[[(-R,Q(0)),(R,Q(0)),(R,Q(1)),(-R,Q(1))]]
        lo,hi=box[-1]
        p=clip(clip(polys[0],self.n,hi),(-self.n[0],-self.n[1]),self.terminal_width-lo)
        polys=[p] if p else []
        for j,n in enumerate(self.normals):
            polys=hallway(polys,n,box[2*j:2*j+2])
            if not polys:break
        return polys
    def bound(self,box):return sum(map(area,self.polygons(box)),Q(0))
    def split(self,box):
        widths=[b-a for a,b in box]
        j=max(range(len(box)),key=lambda j:widths[j])
        a,b=box[j];m=(a+b)/2
        lo=list(box);hi=list(box);lo[j]=(a,m);hi[j]=(m,b)
        return tuple(lo),tuple(hi),j
    def run(self,max_nodes=1000,target=Q(2219,1000)):
        start=time.time();serial=0;ub=self.bound(self.root)
        heap=[(-ub,serial,self.root)];pruned=0;visits=0;max_pruned=Q(0)
        trajectory=[]
        while heap and visits<max_nodes:
            best=-heap[0][0]
            if best<target:break
            neg,_,box=heappop(heap);visits+=1
            for child in self.split(box)[:2]:
                value=self.bound(child)
                # Parent is also a valid upper bound, so take the smaller.
                value=min(value,-neg)
                if value<target:
                    pruned+=1;max_pruned=max(max_pruned,value)
                else:
                    serial+=1;heappush(heap,(-value,serial,child))
            if visits%100==0:
                bound=max(max_pruned,-heap[0][0] if heap else Q(0))
                trajectory.append([visits,str(bound)])
                print('entry',visits,float(bound),len(heap),flush=True)
        ub=max(max_pruned,-heap[0][0] if heap else Q(0))
        # Include the small-area class omitted by the initial geometric bounds.
        ub=max(Q(11,5),ub)
        return {'status':'separated' if ub<target else 'inconclusive',
            'terminal_half_angle_tangent_interval':[str(self.terminal_lo),str(self.terminal_hi)],
            'intermediate_half_angle_tangents':list(map(str,self.intermediate)),
            'upper_area_bound':str(ub),'upper_area_display':float(ub),'target':str(target),
            'visited':visits,'frontier_boxes':len(heap),'pruned':pruned,'seconds':time.time()-start,
            'history':trajectory,'scope':'only the stated terminal-angle slab; no shape-neighborhood exclusion',
            'not_claimed':['global epsilon0','all terminal angles covered','connected-component sharp bound']}
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--lo',default='37/50');a.add_argument('--hi',default='3/4');a.add_argument('--nodes',type=int,default=1000);a.add_argument('--out',default='entry-angle-search.json');args=a.parse_args()
    report=Search(Q(args.lo),Q(args.hi)).run(args.nodes)
    with open(args.out,'w') as f:json.dump(report,f,indent=2);f.write('\n')
    print(json.dumps(report,indent=2))
