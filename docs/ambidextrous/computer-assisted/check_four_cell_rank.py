"""Exact certificate of a four-cell rank-two conflict for two conventional full turns.
Each box is an actual positive-area square in [0,5/2] x [0,1].
If three distinct boxes contain a point of an actual two-turn sofa,
one of four rational-angle hallway placements becomes impossible.
"""
from fractions import Fraction as Q
from itertools import combinations
from json import dumps

E = Q(1,12)
anchors = [(Q(0),Q(0)),(Q(5,6),Q(1)),(Q(5,3),Q(0)),(Q(5,2),Q(1))]
# Every axis-aligned cell is a square of side E ending at its
# horizontal anchor; lower boxes start at y=0 and upper end at y=1.
cells = [ (x if x==0 else x-E, E if x==0 else x,
           Q(0) if y==0 else 1-E, E if y==0 else Q(1))
          for x,y in anchors ]
# (triple, point p, point q, point r, c, s, handedness)
checks = [
 ((0,1,2),1,2,0,Q(21,29),Q(20,29),-1),
 ((0,1,3),1,3,0,Q(12,13),Q(5,13),-1),
 ((0,2,3),2,3,0,Q(5,13),Q(12,13),1),
 ((1,2,3),2,3,1,Q(21,29),Q(20,29),1),
]

def dot_min_difference(p, q, vec):
    a,b = vec
    low = (q[0]-p[1]) if a>=0 else (q[1]-p[0])
    high = (q[2]-p[3]) if b>=0 else (q[3]-p[2])
    return a*low+b*high

def run():
    assert [v[0] for v in checks]==list(combinations(range(4),3))
    assert all(x0<x1 and y0<y1 for x0,x1,y0,y1 in cells)
    assert all(Q(0)<=x0<x1<=Q(5,2) and Q(0)<=y0<y1<=Q(1)
               for x0,x1,y0,y1 in cells)
    margins=[]
    for tri,p,q,r,c,s,hand in checks:
        assert set((p,q,r))==set(tri)
        assert c*c+s*s==1 and c>0 and s>0
        u=(c,hand*s)
        v=(-s,hand*c)
        du=dot_min_difference(cells[p],cells[q],u)
        dv=dot_min_difference(cells[p],cells[r],v)
        assert du>1 and dv>1, (tri,du,dv)
        margins.append((str(du-1),str(dv-1)))
    assert min(Q(t) for row in margins for t in row)==Q(1,39)
    print(dumps({'status':'PASS_exact_four_cell_rank_two',
          'interval_width':str(E), 'cells':[[str(v) for v in b] for b in cells],
          'triples_certified':len(checks), 'exact_margins':margins,
          'min_margin':str(min(Q(t) for row in margins for t in row)), 'rank_upper':2,
          'constant_two_thirds_sum':'8/3',
          'excludes_uniform_two_thirds':Q(8,3)>2},indent=2))
if __name__=='__main__':run()
