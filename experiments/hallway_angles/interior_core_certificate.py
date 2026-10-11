"""Whole-interval integer certificates for larger interior contact cores.

No binary64 arithmetic, optimizer, or polygon library is used here. The
analytic interpretation is documented in INTERIOR_CORE_GLOBAL_CUTOFF.md.
This is a mathematical proof draft with computational scalar assistance,
not a Lean proof. Reuses the pinned integer interval implementation.
"""
from __future__ import annotations
from fractions import Fraction as F
import argparse
import json
from parameter_certificate import Interval as I, SCALE, BITS, sin_cos
from width_certificate import sinc

EMAX = F(1,8)


def span(lo: F, hi: F) -> I:
    return I(I.rational(lo).lo,I.rational(hi).hi)


def constants(e: I) -> dict:
    if e.lo<0 or e.hi>I.rational(EMAX).hi: raise ValueError('epsilon outside [0,1/8]')
    e2=e.square(); sc=sinc(e); _,d=sin_cos(e)
    se=sinc(e/2)/2; _,c=sin_cos(e/2)
    m=2-d; eta=((2-d)/(2+d)).sqrt()
    kap=(e2+3/sc.square()).sqrt(); sk,ck=sin_cos(kap/2)
    D=ck+eta*sk; rc=se*eta/c
    for v in [sc,se,c,d,m,sk,ck,D]:
        if v.lo<=0: raise ArithmeticError('inconclusive positive denominator')
    eb=-d/(2*m*se*D)
    ea=(c/2+rc*eb*sk)/se
    return dict(e=e,e2=e2,sc=sc,d=d,se=se,c=c,m=m,eta=eta,kap=kap,
                sk=sk,ck=ck,D=D,rc=rc,eb=eb,ea=ea)


def scalars(z: dict) -> dict[str,I]:
    e,e2,sc,d,se,c,m,eta,kap,sk,ck,D,rc,eb,ea=(z[k] for k in
      ['e','e2','sc','d','se','c','m','eta','kap','sk','ck','D','rc','eb','ea'])
    T=eta*sk/ck
    c1=-2*(T*d+T+d-2)/((1+T)*m)
    c2=(2*T*d+3*T+2*d-3)/(4*(1+T))
    eV=e2/m+(1+2*d)/(4*sc)+3*d.square()*eta*sk/(2*sc*m.square()*D)
    dj=c*sk+e2*rc*se*ck
    return dict(eV=eV,ell=ea+d*kap*(-sk+eta*ck)/(2*m*D),
      endpoint=-(sc/d)*((2*d-1)*sk-eta*(2*d+1)*ck)/((1+d)*sk+eta*(1-d)*ck),
      width_slope=(c1+2*c2)/sc,
      width_half_slope=(c1+I.rational(3,2)*c2)/sc,
      width_near_slope=(c1+I.rational(97,50)*c2)/sc,
      narrow_gap=eV-1/sinc(e/2),
      jacobi_y=(se*(sk-eta*ck)+rc)/dj,
      width_x=-c/(2*se)+(1+eta*sk/c)/(2*se*D),
      jacobi_x_monotone=(kap+e2*rc)*ck*c-(1+rc*kap)*sk*e2*se,
      width_y_monotone=(1+rc*kap)*ck*c-(kap+e2*rc)*sk*se,
      curvature_upper=e2/m+3*d*(1+eta.square()).sqrt()/(2*m*D*sc.square()))

SCALAR_BOUNDS={
 'eV':(F(27,20),F(34,25)), 'ell':(F(143,500),F(1,3)),
 'endpoint':(F(59,250),F(1,4)),
 'width_slope':(F(1,4),F(1)), 'width_half_slope':(F(1,10),F(1)),
 'width_near_slope':(F(1,4),F(1)), 'narrow_gap':(F(1,3),F(1,2)),
 'jacobi_y':(F(0),F(16,25)), 'width_x':(F(0),F(7,20)),
 'jacobi_x_monotone':(F(0),F(2)), 'width_y_monotone':(F(0),F(1)), 'curvature_upper':(F(1),F(8,5))}


def corner_point(z:dict, u:F)->tuple[I,I]:
    """Rescaled corner at time t=e*u, including the removable endpoint e=0."""
    if u==F(1,2): return I.rational(0),I.rational(1,2)
    uu=I.rational(u); e=z['e']; e2=z['e2']
    st,ct=sin_cos(e*uu); sk,ck=sin_cos(z['kap']*uu)
    st_over_e=uu*sinc(e*uu)
    X=z['ea']-2*e2*z['se']*ct/z['m']+z['eb']*(ck*ct-z['rc']*e2*sk*st_over_e)
    Y=2*e2*z['se']*st_over_e/z['m']-z['eb']*(ck*st_over_e+z['rc']*sk*ct)
    if u==0:Y=I.rational(0)
    return X,Y


def outer_point(z:dict,u:F)->tuple[I,I]:
    """Rescaled upper support contact at phi=e*u; no division by e."""
    uu=I.rational(u); e=z['e']; sc=sinc(e*uu)
    _,ce=sin_cos(e*uu); sk,ck=sin_cos(z['kap']*(uu-I.rational(1,2)))
    coef=z['d']/(2*z['m']*z['D'])
    h=1/z['m']+z['ea']*uu*sc-coef*(ck-z['eta']*sk)
    dh=z['ea']*ce+coef*z['kap']*(sk+z['eta']*ck)
    X=z['e2']*h*uu*sc+dh*ce
    Y=I.rational(1,2) if u==0 else (1/z['m']-coef*(ck-z['eta']*sk))*ce-coef*z['kap']*(sk+z['eta']*ck)*uu*sc
    return X,Y


def prove_foundation(cells:int=128, points:int=128)->dict:
    for n in [cells,points]:
        if isinstance(n,bool) or not isinstance(n,int) or n<1:
            raise ValueError('cells and points must be positive integers')
    outer_u=[F(j,points) for j in range(points)]
    inner_u=[F(j,2*points) for j in range(points+1)]
    outer_bounds=[[None,None] for _ in outer_u]
    inner_bounds=[[None,None] for _ in inner_u]
    extrema={k:[None,None] for k in SCALAR_BOUNDS}
    for j in range(cells):
        z=constants(span(EMAX*j/cells,EMAX*(j+1)/cells))
        for name,v in scalars(z).items():
            lo,hi=SCALAR_BOUNDS[name]
            if F(v.lo,SCALE)<=lo or F(v.hi,SCALE)>=hi:
                raise ArithmeticError(f'inconclusive scalar cell {j}: {name}')
            a,b=extrema[name]
            extrema[name]=[v.lo if a is None else min(a,v.lo),v.hi if b is None else max(b,v.hi)]
        for k,u in enumerate(outer_u):
            x,y=outer_point(z,u)
            # The verified rho_scaled <= 8/5 and the contact-point derivative
            # give an endpoint-tight lower bound by integration, not sampling.
            yl=max(y.lo,I.rational(F(1,2)-F(4,5)*u*u).lo)
            if yl>y.hi:raise ArithmeticError('inconsistent curvature bound')
            y=I(yl,y.hi)
            a,b=outer_bounds[k]
            outer_bounds[k]=[x.lo if a is None else min(a,x.lo),y.lo if b is None else min(b,y.lo)]
        for k,u in enumerate(inner_u):
            x,y=corner_point(z,u)
            a,b=inner_bounds[k]
            inner_bounds[k]=[x.hi if a is None else max(a,x.hi),y.lo if b is None else min(b,y.lo)]
    # Every rectangle is in all candidate bodies over the whole e interval.
    # Endpoint-coordinate enclosures and convexity suffice; geometry sampling
    # does not enter the containment proof.
    if any(x>0 or y<0 or 2*y>SCALE for x,y in inner_bounds):
        raise ArithmeticError('inner witness outside the certified half strip')
    heights=sorted(set([v[1] for v in outer_bounds]+[v[1] for v in inner_bounds]),reverse=True)
    rectangles=[]; best_width=-1
    for y in heights:
        if y<=0: continue
        right=[(v[0],k) for k,v in enumerate(outer_bounds) if v[1]>=y]
        left=[(v[0],k) for k,v in enumerate(inner_bounds) if v[1]>=y]
        if not right or not left: continue
        R,oi=max(right); L,ii=min(left)
        # Chords of known points inside the convex candidate give further
        # inside points, without assuming interval boxes themselves are inside.
        for k in range(len(inner_bounds)-1):
            x0,y0=inner_bounds[k];x1,y1=inner_bounds[k+1]
            if y0<=y<=y1 and y0<y1 and max(x0,x1)<=0:
                numer=x0*(y1-y)+x1*(y-y0)
                chord=-((-numer)//(y1-y0))
                if chord<L:L,ii=chord,k
        W=R-L
        if W<=max(0,best_width): continue
        best_width=W
        rectangles.append(dict(left=L,right=R,half_height=y,width=W,height=2*y,
                               outer_parameter=str(outer_u[oi]),inner_parameter=str(inner_u[ii])))
    return dict(format='interior-core-foundation-v1',epsilon_interval=['0',str(EMAX)],
                denominator=SCALE,bits=BITS,cells=cells,points=points,
                scalar_bounds={k:[str(a),str(b)] for k,(a,b) in SCALAR_BOUNDS.items()},
                scalar_enclosures=extrema,rectangles=rectangles)


def path_constants()->dict:
    e=EMAX; A=F(39,100);B=F(197,100);r=F(8,25)
    det=A*B-r*r; h=e*e/2
    tx=(B+2*r*h+A*h*h)/(2*det)
    ty=(B/4+r+A)/(2*det)
    slacks={
      'poincare_A':F(1,2)-e*e/24-(1+e*e/2)*F(64,625)-A,
      'poincare_B':2-e*e/2-3*e*e*F(64,625)-B,
      'matrix_determinant':det,
      'trace_x':F(12,5)**2-tx-F(250,59),
      'trace_y':F(41,25)**2-ty-F(16,25)**2*F(250,59),
      'mismatch':F(3,4)*(1-(3*e/4)**2/6)-F(20,27),
      'sinc_reciprocal':F(501,500)*(1-(3*e/4)**2/6)-1,
      'cos_mismatch':1-(3*e/4)**2/2-F(99,100),
      'reverse_not_forward':F(27,40)/e-3,
      'coarse_width_97':F(3,100)-10*F(17,50)*(3*e/4)**2,
      'sqrt_deficit':F(7,12)**2-F(17,50),
    }
    if min(slacks.values())<=0: raise ArithmeticError('path constant propagation failed')
    return dict(matrix=[[str(A),str(-r)],[str(-r),str(B)]],
                trace_squared=[str(tx),str(ty)],
                path_errors=['(12/5)sqrt(d)+(7/5)d','(41/25)sqrt(d)+2d'],
                slacks={k:str(v) for k,v in slacks.items()})


def prove_directions(foundation:dict,cells:int=512,cutoff:F=EMAX)->dict:
    """Cover sqrt(sin(nu)/e) by exact rational intervals, including zero."""
    if isinstance(cells,bool) or not isinstance(cells,int) or cells<1: raise ValueError('positive cells required')
    cutoff=F(cutoff)
    if not 0<cutoff<=EMAX: raise ValueError('cutoff outside the foundation interval')
    if foundation.get('epsilon_interval')!=['0',str(EMAX)] or foundation.get('denominator')!=SCALE:
        raise ValueError('unexpected foundation record')
    # This function consumes a freshly verified foundation in the CLI. A
    # caller supplying a record must separately establish its rectangle bounds.
    recs=[(F(r['width'],SCALE),F(r['height'],SCALE)) for r in foundation['rectangles']]
    z=F(501,500)*cutoff
    records=[]; minimum=None
    for j in range(cells):
        t0=F(7*j,8*cells);t1=F(7*(j+1),8*cells)
        a=t1*t1;n=z*a;d=F(17,50)*n*n
        ex=F(7,5)*n+F(119,250)*n*n
        ey=F(287,300)*n+F(17,25)*n*n
        chosen=None
        for k,(W0,H0) in enumerate(recs):
            if t0==0 and H0!=1:continue
            height_cost=0 if H0==1 else (1-H0)/(t0*t0)
            margin=(W0-height_cost-2*ex-F(287,150)*z-F(34,25)*z*z*a
                    -z*z*a*H0/2-F(7,6)*z*t1)
            W=W0-2*ex;H=H0-2*ey
            # Divide the horizontal triangular condition by a>0; this
            # removes the apparent singularity at the first interval.
            hc=W*W/2-F(17,50)*z*z*a
            vc=F(99,200)*H*H-a*d
            if min(margin,W,H,hc,vc)<=0:continue
            score=margin
            if chosen is None or score>chosen[0]:chosen=(score,k,[W,H,hc,vc])
        if chosen is None:
            raise ArithmeticError(f'no certified core for direction cell {j}: t in [{t0},{t1}]')
        v,k,slacks=chosen
        minimum=v if minimum is None else min(minimum,v)
        records.append(dict(t_interval=[str(t0),str(t1)],rectangle=k,
                            normalized_width_margin=str(v),other_slacks=[str(q) for q in slacks]))
    return dict(format='interior-core-direction-v1',status='all direction cells excluded',
                epsilon_cutoff=str(cutoff),sqrt_direction_interval=['0','7/8'],cells=cells,
                minimum_normalized_margin=str(minimum),cell_records=records)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--parameter-cells',type=int,default=128)
    p.add_argument('--points',type=int,default=128)
    p.add_argument('--direction-cells',type=int,default=512)
    p.add_argument('--cutoff',default=str(EMAX))
    p.add_argument('--output')
    args=p.parse_args()
    f=prove_foundation(args.parameter_cells,args.points)
    result=dict(foundation=f,path=path_constants(),directions=prove_directions(f,args.direction_cells,F(args.cutoff)))
    s=json.dumps(result,indent=2)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(s)
    else:print(s,end='')
