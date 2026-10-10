"""Independent exact affine-in-width rank-two certificate for four spatial cells.
No floating arithmetic or optimization. Each min-dot product is affine in W.
All slopes are positive; exact endpoint checks prove the theorem for all W above the threshold.
"""
from fractions import Fraction as F
from itertools import combinations
from json import dumps

alpha=(F(0),F(1,3),F(2,3),F(1))
ybase=(0,1,0,1)
witnesses=[
    ((0,1,2),1,2,0,F(21,29),F(20,29),-1),
    ((0,1,3),1,3,0,F(4,5),F(3,5),-1),
    ((0,2,3),2,3,0,F(3,5),F(4,5),1),
    ((1,2,3),2,3,1,F(21,29),F(20,29),1),
]

def geom(e):
    # Each x bound is (coefficient of W, constant).
    out=[]
    for i in range(4):
        lo=(alpha[i], -e if i else F(0))
        hi=(alpha[i], F(0) if i else e)
        yl,yh=(F(0),e) if ybase[i]==0 else (1-e,F(1))
        out.append((lo,hi,yl,yh))
    return out

def affine_min(B,C,n):
    a,b=n
    pb=B[1] if a>=0 else B[0]
    qc=C[0] if a>=0 else C[1]
    py=B[3] if b>=0 else B[2]
    qy=C[2] if b>=0 else C[3]
    return a*(qc[0]-pb[0]),a*(qc[1]-pb[1])+b*(qy-py)

def verify(w,e):
    G=geom(e)
    assert w>=2 and e>0 and e<F(1,6)
    assert [t[0] for t in witnesses]==list(combinations(range(4),3))
    assert all(G[i+1][0][0]>G[i][1][0] and
               G[i][1][0]*w+G[i][1][1] < G[i+1][0][0]*w+G[i+1][0][1]
               for i in range(3))
    margins=[]
    for tri,p,q,r,c,s,h in witnesses:
        assert set((p,q,r))==set(tri)
        assert c*c+s*s==1 and h in (-1,1)
        # Normal-u and normal-v exact minima for all p,q,r in cells.
        for vec,src in [((c,h*s),q),((-s,h*c),r)]:
            slope,inter=affine_min(G[p],G[src],vec)
            margin=slope*w+inter-1
            assert slope>0 and margin>0,(tri,src,margin)
            margins.append((str(slope),str(inter),str(margin)))
    print(dumps({'status':'PASS_parametric_rank_two',
                 'width_at_least':str(w),'square_side':str(e),
                 'conditions':len(margins),
                 'least_endpoint_margin':str(min(F(row[2]) for row in margins)),
                 'affine_checks':margins,
                 'valid_for_all_larger_widths':True},indent=2))

if __name__=='__main__':
    verify(F(2),F(1,64))
    verify(F(23,10),F(1,12))
