"""Exact rational checks for the wide-hull curvature-repair counterexample.

No sampled trigonometric values or floating-point proof decisions are used.
Angles are specified by z=tan(t/2); all knot sines/cosines are rational.
Polynomial nonnegativity is certified by Bernstein coefficients on a finite
rational subdivision. The geometric proof is in global-repair-counterexample.md.
"""
from fractions import Fraction as F
from math import comb
import hashlib
import json
from pathlib import Path

A = F(63, 50)
J = (F(3, 25), F(1, 8))


def sine(z):
    return 2*z/(1+z*z)


def cosine(z):
    return (1-z*z)/(1+z*z)


UP = ((F(1, 10), F(7, 16), F(1)), (F(4, 5), F(1), F(1)))
MOMENT = sum(r*(cosine(a)-cosine(b)) for a,b,r in UP)
LAMBDA = MOMENT/(cosine(F(4,15))-cosine(F(7,10)))
DOWN = ((F(4,15), F(7,10), LAMBDA),)


def add(*polys):
    out = [F(0)]*max(map(len,polys))
    for p in polys:
        for i,c in enumerate(p): out[i] += c
    return out


def scale(p, c):
    return [c*x for x in p]


def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):out[i+j]+=x*y
    return out


DEN=[F(1),F(0),F(1)]
COS=[F(1),F(0),F(-1)]
SIN=[F(0),F(2)]
DEN2=mul(DEN,DEN)


def pieces(parts):
    """(left z,right z,rho,cos coefficient,sin coefficient) for f."""
    knots=sorted({F(0),F(1)}|{x for a,b,_ in parts for x in (a,b)})
    B=1-sum(r*(sine(b)-sine(a)) for a,b,r in parts)
    AA=A
    prev=F(0)
    out=[]
    for a,b in zip(knots,knots[1:]):
        mid=(a+b)/2
        rho=sum(r for lo,hi,r in parts if lo<mid<hi)
        AA+=(prev-rho)*cosine(a)
        B+=(prev-rho)*sine(a)
        out.append((a,b,rho,AA,B));prev=rho
    # Exact endpoint data, including the final trace at t=pi/2.
    assert out[0][2]+out[0][3] == A
    assert out[-1][2]+out[-1][4] == 1
    return out


def at(pl,z):
    for a,b,r,c,s in pl:
        if a<=z<=b: return r,c,s
    raise ValueError('outside quarter')


def reflected(z):
    return (1-z)/(1+z)


def polynomials(pl,z):
    r,ac,bs=at(pl,z)
    rg,ag,bg=at(pl,reflected(z))
    cy=add(scale(mul(SIN,DEN),r-1),scale(mul(COS,DEN),rg-1),
           scale(mul(SIN,COS),ac+ag),scale(mul(SIN,SIN),bs),
           scale(mul(COS,COS),bg))
    p=add(scale(DEN,1-rg),scale(COS,bs-bg),scale(SIN,-ac-ag))
    q=add(scale(DEN,r-1),scale(COS,ac+ag),scale(SIN,bs-bg))
    return cy,p,q


def bernstein(poly,lo,hi):
    """Coefficients of P(lo+(hi-lo)x) in the degree-n Bernstein basis."""
    n=len(poly)-1
    mon=[sum(poly[k]*comb(k,i)*lo**(k-i)*(hi-lo)**i
             for k in range(i,n+1)) for i in range(n+1)]
    return [sum(mon[i]*F(comb(j,i),comb(n,i)) for i in range(j+1))
            for j in range(n+1)]


def certify(poly,lo,hi,depth=0):
    b=bernstein(poly,lo,hi)
    if min(b)>0:
        return [(lo,hi,depth,min(b))]
    if depth>=20:
        raise AssertionError('Unresolved polynomial: no certificate claimed')
    mid=(lo+hi)/2
    return certify(poly,lo,mid,depth+1)+certify(poly,mid,hi,depth+1)


def main():
    assert 0<LAMBDA<1
    cosmoment=sum(r*(sine(b)-sine(a)) for a,b,r in UP+DOWN)
    axis_atom=1-cosmoment
    assert axis_atom>0
    assert A-MOMENT>F(1,2)
    assert 2*A>2
    pl_up,pl_down=pieces(UP),pieces(DOWN)
    certs={}
    for name,pl,H in [('lower',pl_up,F(53,100)),('upper_reflected',pl_down,F(23,50))]:
        knots=sorted({F(0),F(1)}|{x for a,b,*_ in pl for x in (a,b)}|
                     {reflected(x) for a,b,*_ in pl for x in (a,b)})
        leaves=[]
        for lo,hi in zip(knots,knots[1:]):
            cy,_,_=polynomials(pl,(lo+hi)/2)
            leaves+=certify(add(scale(DEN2,H),scale(cy,-1)),lo,hi)
        certs[name]={'ceiling':str(H),'leaves':len(leaves),
                     'max_depth':max(x[2] for x in leaves),
                     'min_positive_bernstein_coefficient':str(min(x[3] for x in leaves))}
    cy,p,q=polynomials(pl_up,sum(J)/2)
    assert all(at(pl_up,z)[0]==1 for z in J)
    assert not any(J[0]<x<J[1] for a,b,*_ in pl_up for x in (a,b,reflected(a),reflected(b)))
    pc=certify(add(scale(p,-1),scale(DEN,F(-1,250))),*J)
    qc=certify(add(q,scale(DEN,F(-101,100))),*J)
    cc=certify(add(cy,scale(DEN2,F(-1,10))),*J)
    certs['source_window']={'tan_half_endpoints':list(map(str,J)),
       'p_strict_upper':'-1/250','q_strict_lower':'101/100',
       'corner_height_strict_lower':'1/10',
       'leaves':len(pc)+len(qc)+len(cc),
       'max_depth':max(x[2] for x in pc+qc+cc)}
    # Checks cannot accept a reversed sign or a deliberately false ceiling.
    for bad in ([F(-1)],add(scale(DEN2,F(-1)),scale(cy,-1))):
        assert min(bernstein(bad,*J))<0
    report={'status':'exact scalar checks passed; see geometric proof',
       'half_width':str(A),'width':str(2*A),'lambda':str(LAMBDA),
       'sine_moment':str(MOMENT),'axis_atom':str(axis_atom),
       'half_face_length':str(A-MOMENT),'certificates':certs,
       'arithmetic':'Python standard-library Fraction; no floating-point arithmetic',
       'ci_used':False,'lean_or_lake_used':False,
       'unrestricted_optimality_proved':False,
       'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
