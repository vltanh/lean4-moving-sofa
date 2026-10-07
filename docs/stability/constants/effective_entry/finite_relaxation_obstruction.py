"""Exact counterexample to a finite-hallway relaxation, NOT a moving sofa.

All validation is rational. Reference-center choices are merely discovery data.
The witness tests the four intermediate normals used in the coarse entry search.
"""
from __future__ import annotations
from fractions import Fraction as Q
import json,hashlib
from pathlib import Path

P=tuple[Q,Q]
def normal(r:Q)->P:return (1-r*r)/(1+r*r),2*r/(1+r*r)
def dot(p,n):return p[0]*n[0]+p[1]*n[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def clip(poly,n,h):
    if not poly:return []
    out=[];a=poly[-1];da=dot(a,n)-h
    for b in poly:
        db=dot(b,n)-h
        if (da<=0)!=(db<=0):
            t=da/(da-db);out.append((a[0]+t*(b[0]-a[0]),a[1]+t*(b[1]-a[1])))
        if db<=0:out.append(b)
        a,da=b,db
    return out

def area(poly):
    return abs(sum((cross(a,b) for a,b in zip(poly,poly[1:]+poly[:1])),Q(0)))/2 if len(poly)>2 else Q(0)

def hallway(polys,n,U,V):
    v=(-n[1],n[0]);out=[]
    for p in polys:
        p=clip(clip(p,n,U),v,V)
        a=clip(p,(-n[0],-n[1]),1-U)
        b=clip(clip(p,n,U-1),(-v[0],-v[1]),1-V)
        out.extend(q for q in [a,b] if q and area(q)>0)
    return out

def intersection(a,b):
    # b is counterclockwise; lower dimensional intersections are retained.
    for x,y in zip(b,b[1:]+b[:1]):
        n=(y[1]-x[1],x[0]-y[0]);a=clip(a,n,dot(n,x))
    return a

def build(data):
    polygons=[[(Q(-3),Q(0)),(Q(2),Q(0)),(Q(2),Q(1)),(Q(-3),Q(1))]]
    for r,U,V in data:
        polygons=hallway(polygons,normal(Q(r)),Q(U),Q(V))
    return polygons

def main():
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'critical_cone'))
    from dyadic_interval import iv, Interval as I, atan_small_bounds
    data=[['1/10','997717/1000000','1272361/1000000'],
          ['1/4','1012999/1000000','405497/250000'],
          ['2/5','1034119/1000000','1883759/1000000'],
          ['3/5','130541/125000','209611/100000']]
    polygons=build(data)
    A=sum(map(area,polygons),Q(0))
    assert A>Q(22199,10000)
    # All sampled coordinates are the OWN supports, not unattained assignments.
    for r,U,V in data:
        n=normal(Q(r));v=(-n[1],n[0])
        assert max(dot(p,n) for poly in polygons for p in poly)==Q(U)
        assert max(dot(p,v) for poly in polygons for p in poly)==Q(V)
        # Convex pieces individually satisfy one entire branch of each hallway.
        for poly in polygons:
            assert all(dot(p,n)<=Q(U) and dot(p,v)<=Q(V) for p in poly)
            assert all(dot(p,n)>=Q(U)-1 for p in poly) or all(dot(p,v)>=Q(V)-1 for p in poly)
    edges=[]
    for i,a in enumerate(polygons):
        for j,b in enumerate(polygons[:i]):
            it=intersection(a,b)
            assert area(it)==0  # no positive-area double counting
            if it:edges.append((i,j))
    reached={0}
    while True:
        larger=reached | {j for i,j in edges if i in reached} | {i for i,j in edges if j in reached}
        if larger==reached:break
        reached=larger
    assert len(reached)==len(polygons)
    witness=(Q(-28,25),Q(23,100))
    def inside(p,poly):
        return all(dot(p,(b[1]-a[1],a[0]-b[0]))<=dot(a,(b[1]-a[1],a[0]-b[0]))
                   for a,b in zip(poly,poly[1:]+poly[:1]))
    assert any(inside(witness,poly) for poly in polygons)
    # Bound the fixed reference's inner corner at tan(t/2)=4/5 using only
    # Gerver.Bounds intervals, reflection, and the second Romik phase formula.
    r=Q(4,5);t=2*atan_small_bounds(r,200);s=iv.pi/2-t
    assert s>I('0.039177465') and s<I('0.681301409')
    b1=I('-0.527624699','-0.527624498');b2=I('0.920258285','0.920258486')
    k2x=I('-0.919179393','-0.919179192');k2y=I('0.472406519','0.472406720')
    k3x=I('-0.613763330','-0.613763129')
    ct,st=normal(r);cs,ss=I(st),I(ct)
    Fx=-s*s/4+b1*s+b2;Fy=s/2-b1-1
    X=cs*Fx-ss*Fy+k2x;Y=ss*Fx+cs*Fy+k2y
    x=(2*k3x-X,Y);n=normal(r);v=(-n[1],n[0])
    U=x[0]*n[0]+x[1]*n[1];V=x[0]*v[0]+x[1]*v[1]
    base_gaps=[U-I(dot(witness,n)),V-I(dot(witness,v))]
    assert all(g>I(Q(1,20)) for g in base_gaps)
    # A 99/100 homothety makes every sampled inner inequality strict and also
    # fits every terminal strip with half-angle tangent in [999/1000,1].
    lam=Q(99,100)
    scaled_witness=(lam*witness[0],lam*witness[1]+1-lam)
    scaled_gaps=[U-I(dot(scaled_witness,n)),V-I(dot(scaled_witness,v))]
    assert all(g>I(Q(1,25)) for g in scaled_gaps)
    terminal_width=lam*(1+5*normal(Q(999,1000))[0])
    assert terminal_width<1 and lam*lam*A>Q(22199,10000)
    report={'status':'passed','result':'obstruction to the fixed four-hallway relaxation, NOT a moving sofa',
        'support_data':data,'polygon_pieces':len(polygons),'connected_intersection_edges':edges,
        'all_own_supports_attained':True,'piece_interiors_pairwise_disjoint':True,
        'area_exact':str(A),'area_display':float(A),'gerver_area_upper':'22199/10000',
        'far_reference_point':list(map(str,witness)),
        'reference_inner_normal_half_tangent':'4/5','reference_gap_intervals':[g.exact() for g in base_gaps],
        'directed_distance_lower':'1/20',
        'scaled_near_right_angle_family':{'scale':'99/100','area_exact':str(lam*lam*A),
            'area_display':float(lam*lam*A),'terminal_half_tangent_interval':['999/1000','1'],
            'uniform_terminal_width_upper':str(terminal_width),
            'sampled_inner_wall_slack_lower':'1/100','far_point':list(map(str,scaled_witness)),
            'reference_gap_intervals':[g.exact() for g in scaled_gaps],
            'directed_distance_lower':'1/25'},
        'polygons':[[list(map(str,p)) for p in poly] for poly in polygons],
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'interval_backend_sha256':hashlib.sha256((Path(__file__).resolve().parents[1]/'critical_cone'/'dyadic_interval.py').read_bytes()).hexdigest(),
        'not_claimed':['valid continuous motion','counterexample to Gerver','effective global entry']}
    Path(__file__).with_name('finite-relaxation-obstruction.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='polygons'},indent=2))

if __name__=='__main__':main()
