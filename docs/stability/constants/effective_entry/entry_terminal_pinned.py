"""Improved exact outer search: fix terminal-strip translation, propagate support quantiles.

All geometric and pruning arithmetic is rational. The 32-bit support grid
rounds lower bounds DOWN and upper bounds UP; it is not a numerical tolerance.
The only floats in the report are display values and elapsed time.
"""
from entry_box_search import *


@dataclass
class TerminalPinnedSearch(Search):
    grid_bits:int=32
    def down(self,x):return Q((x*(1<<self.grid_bits)).numerator//(x*(1<<self.grid_bits)).denominator,1<<self.grid_bits)
    def up(self,x):return -self.down(-x)
    def __post_init__(self):
        assert Q(0)<self.terminal_lo<=self.terminal_hi<1
        assert all(Q(0)<r<=self.terminal_lo for r in self.intermediate)
        self.normals=[normal(r) for r in self.intermediate]
        na=normal(self.terminal_lo);nb=normal(self.terminal_hi)
        xmin=-nb[1]/nb[0];xmax=1/nb[0]
        base=[(xmin,Q(0)),(xmax,Q(0)),(xmax,Q(1)),(xmin,Q(1))]
        base=clip(base,(-nb[0],-nb[1]),Q(0))
        a=clip(base,na,Q(1));b=clip(clip(base,nb,Q(1)),(-na[0],-na[1]),Q(-1))
        self.base=[p for p in [a,b] if area(p)>0]
        root=[]
        for c,s in self.normals:
            for n in [(c,s),(-s,c)]:
                vals=[dot(v,n) for p in self.base for v in p]
                root.append((min(vals),max(vals)))
        self.root=tuple((self.down(a),self.up(b)) for a,b in root)
    def polygons(self,box):
        polys=self.base
        for j,n in enumerate(self.normals):
            polys=hallway(polys,n,box[2*j:2*j+2])
            if not polys:break
        return polys
    def contract(self,box,target,passes=1):
        box=list(box)
        for _ in range(passes):
            polys=self.polygons(box)
            if sum(map(area,polys),Q(0))<target:return None
            for j,n0 in enumerate(self.normals):
                for k,n in enumerate([n0,(-n0[1],n0[0])]):
                    idx=2*j+k;lo,hi=box[idx]
                    hi=min(hi,self.up(max(dot(v,n) for p in polys for v in p)))
                    if hi<lo:return None
                    # Safe support lower bound for ANY subset of area at least target.
                    for _ in range(2):
                        mid=(lo+hi)/2
                        caparea=sum((area(clip(p,n,mid)) for p in polys),Q(0))
                        if caparea<target:lo=max(lo,self.down(mid))
                        else:break
                    box[idx]=(lo,hi)
        return tuple(box)
    def run(self,max_nodes=1000,target=Q(2219,1000)):
        start=time.time();serial=0;root=self.contract(self.root,target,passes=3)
        if root is None:return {'status':'separated','upper_area_bound':str(target),'visited':0,
            'terminal_half_angle_tangent_interval':[str(self.terminal_lo),str(self.terminal_hi)],
            'frontier_boxes':0,'pruned':1,'grid_bits':self.grid_bits,'seconds':time.time()-start}
        heap=[(-self.bound(root),serial,root)];pruned=0;visits=0;history=[]
        while heap and visits<max_nodes:
            neg,_,box=heappop(heap)
            if -neg<target:pruned+=1;continue
            visits+=1
            for child in self.split(box)[:2]:
                child=self.contract(child,target)
                if child is None:pruned+=1;continue
                value=min(self.bound(child),-neg)
                if value<target:pruned+=1
                else:
                    serial+=1;heappush(heap,(-value,serial,child))
            if visits%100==0:
                upper=max(target,-heap[0][0] if heap else Q(0));history.append([visits,str(upper)])
                print('terminal pinned',visits,float(upper),len(heap),flush=True)
        upper=max(target,-heap[0][0] if heap else Q(0))
        return {'status':'separated' if not heap else 'inconclusive',
            'terminal_half_angle_tangent_interval':[str(self.terminal_lo),str(self.terminal_hi)],
            'intermediate_half_angle_tangents':list(map(str,self.intermediate)),
            'upper_area_bound':str(upper),'upper_area_display':float(upper),'target':str(target),
            'grid_bits':self.grid_bits,'visited':visits,'frontier_boxes':len(heap),'pruned':pruned,'seconds':time.time()-start,
            'history':history,'scope':'only stated terminal-angle slab, area-based support contraction',
            'not_claimed':['global epsilon0','all terminal angles covered','shape-neighborhood entry']}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--lo',default='37/50');a.add_argument('--hi',default='3/4');a.add_argument('--nodes',type=int,default=1000);a.add_argument('--out',default='entry-terminal-search.json');args=a.parse_args()
 r=TerminalPinnedSearch(Q(args.lo),Q(args.hi)).run(args.nodes)
 with open(args.out,'w') as f:json.dump(r,f,indent=2);f.write('\n')
 print(json.dumps(r,indent=2))
