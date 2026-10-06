#!/usr/bin/env python3
"""Reference interval inequalities and exact cutoff bookkeeping, not a Lean audit.

Run from the repository: python docs/stability/constants/effective_entry/check_cutoff_radii.py
The dependency is the committed critical_cone/dyadic_interval.py backend.
No floating-point value is used for acceptance. The enormous deficit is handled
as an exact Fraction, not rounded to the 90-bit reference interval grid.
"""
from __future__ import annotations
import hashlib
import json
import platform
import sys
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

HERE=Path(__file__).resolve().parent
BACKEND=HERE.parent/'critical_cone'
if BACKEND.is_dir(): sys.path.insert(0,str(BACKEND))
from dyadic_interval import Interval as I, SCALE, sin, cos, tan, pi
import dyadic_interval

COUNTS=Counter()
REFERENCE={}
MARGINS={}

def require(group, condition, label):
    COUNTS[group]+=1
    if not condition: raise AssertionError(group+': '+label)

def qmargin(label, value):
    require('rational_local_and_cutoff',value>0,label)
    MARGINS[label]=str(value)

def hull(vals):
    return I.raw(min(v.lo for v in vals),max(v.hi for v in vals))

def record(label, value): REFERENCE[label]=value.exact()

p=I('0.039177264','0.039177465')
th=I('0.681301409','0.681301610')
a1=I('1.210322322','1.210322523')
b1=I('-0.527624699','-0.527624498')
b2=I('0.920258285','0.920258486')
c1=I('0.626045422','0.626045623')
k3x=I('-0.613763330','-0.613763129')
k3y=I('0.889626379','0.889626580')
v=pi/2

def frame(phase,t):
    if phase==1:
        a=2*a1*sin(t)+(cos(t)-1)/2
        b=2*a1*cos(t)-sin(t)/2-1
        ap=2*a1*cos(t)-sin(t)/2
        bp=-2*a1*sin(t)-cos(t)/2
    elif phase==2:
        a=t-2*b1-1
        b=-t**2/4+b1*t+b2+I('0.5')
        ap=I(1);bp=b1-t/2
    elif phase==3:
        a=1+c1-v+t;b=1+c1-t;ap=I(1);bp=I(-1)
    else: raise ValueError('phase')
    return a,b,ap,bp

def first_position(t):
    F0=a1*cos(t)-sin(t)/4-1
    F1=cos(t)/4+a1*sin(t)-I('0.5')
    return cos(t)*F0-sin(t)*F1+1-a1, sin(t)*F0+cos(t)*F1+I('0.25')

def reference_checks():
    require('reference_scalars',pi>I('3.14159'),'pi lower')
    require('reference_scalars',p>I('.039'),'phi lower')
    require('reference_scalars',p<I('.04'),'phi upper')
    require('reference_scalars',th<pi/4,'theta before midpoint')
    l=2*k3x-1;r=I(1);a=1-2*a1;b=2*k3x-a;D=a-l
    record('wing_width',D);record('roof_floor_width',b-a)
    require('reference_scalars',D>I(Q(403,500)),'wing width lower')
    require('reference_scalars',D<I(1),'wing width upper')
    require('reference_scalars',b-a>I(1),'central roof width')
    require('reference_scalars',r-l<I(Q(13,4)),'cap width')
    require('reference_scalars',k3x>I(-1) and k3x<I(Q(-3,5)),'reference midpoint')
    xp,yp=first_position(p);record('core_endpoint_height',yp)
    require('reference_scalars',yp>I(Q(1,20)),'core minimum height')
    left_corner=2*k3x-xp
    gaps=[left_corner-l,xp-left_corner,r-xp]
    record('corner_abscissa_gaps',hull(gaps))
    require('reference_scalars',all(x>I(Q(1,10)) for x in gaps),'corner spacing')
    require('reference_scalars',left_corner-a>I(Q(1,10)) and b-xp>I(Q(1,10)),
            'roof corners inside central rectangle')
    core_a,core_b,_,_=frame(2,p)
    X=core_a*cos(p)+core_b*sin(p);Y=-core_a*sin(p)+core_b*cos(p)
    require('reference_scalars',Y>X and X>I(0),'roof joins convex with acute normal gap')
    require('reference_scalars',cos(p)/sin(p)<I(32),'upper graph slope')
    require('reference_scalars',v-p>I(Q(153,100)+Q(1,2000)),'sector angular reserve')
    require('reference_scalars',I(1)/cos(p)<I(Q(1001,1000)),'centered cap coefficient')
    # The analytic height bound from note08 uses this rational expression.
    require('reference_scalars',Q(1882251,2830000)<Q(2,3),'roof height upper')
    min_arm=[];max_speed=[];max_accel=[];max_slope=[];dens=[];tail=[]
    N=256
    for phase,lo,hi in [(1,I(0),p),(2,p,th),(3,th,v/2)]:
        for j in range(N):
            lam=I(Q(j,N),Q(j+1,N));t=lo+(hi-lo)*lam
            aa,bb,ap,bp=frame(phase,t)
            speed=aa**2+bb**2;accel=(-ap-bb)**2+(bp-aa)**2
            require('reference_phase_cover',speed<I(100),'reference speed squared <100')
            require('reference_phase_cover',accel<I(10000),'reference acceleration squared <10000')
            max_speed.append(speed);max_accel.append(accel)
            if phase>=2:
                require('reference_phase_cover',aa>I(Q(1,16)) and bb>I(Q(1,16)),'core speed/arm lower')
                require('reference_phase_cover',aa+bb>I(1),'normal lambda denominator')
                XX=aa*cos(t)+bb*sin(t);YY=-aa*sin(t)+bb*cos(t)
                require('reference_phase_cover',abs(YY)<I(Q(189,20))*XX,'roof slope bound')
                max_slope.append(abs(YY)/XX)
                require('reference_phase_cover',bb>I(Q(1,2)) and bb<I(16),'outer density phases2/3')
                dens.append(bb)
            if phase<=2:
                tail_density=I(Q(1,2)) if phase==1 else 1+b1-t/2
                require('reference_phase_cover',tail_density>I(Q(1,8)),'tail speed lower')
                require('reference_phase_cover',bb>I(Q(9,10)),'tail inactive wall slack')
                tail.append(tail_density)
            if phase==2:
                require('reference_phase_cover',-aa*sin(t)+bb*cos(t)>I(0),'phase2 height monotonicity')
                density4=t/2-b1
                require('reference_phase_cover',density4>I(Q(1,2)) and density4<I(16),'reflected contact density')
                dens.append(density4)
    # Phase1 away from zero; reflection gives the final small-angle interval.
    for j in range(N):
        t=p/2+(p/2)*I(Q(j,N),Q(j+1,N));aa,bb,_,_=frame(1,t)
        require('reference_arms_extended',aa>I(Q(1,32)) and bb>I(Q(1,32)),'extended core arm margin')
        min_arm += [aa,bb]
    record('extended_arm_range',hull(min_arm))
    record('speed_squared_range',hull(max_speed));record('acceleration_squared_range',hull(max_accel))
    record('core_abs_slope_range',hull(max_slope));record('curved_outer_density_range',hull(dens))
    record('tail_speed_range',hull(tail))
    require('reference_scalars',Q(100)*16**2<2**20,'core curvature bound')


def radius_checks():
    delta=Q(1,10**40);alpha=Q(1,10**20);w=Q(1,100000);t=w/16
    for eta in [w,Q(1,10**8)]:
        s=eta/512;rho=eta*eta/2**20
        qmargin('support_tolerance_'+str(eta),eta**3/2**24-delta)
        qmargin('top_face_error_'+str(eta),eta/2-(20*rho/s+4*delta/s+128*s))
        qmargin('far_foot_error_'+str(eta),eta/8-2*delta/rho)
    qmargin('arm_error',Q(1,64)-128*Q(1,10**20))
    qmargin('cut_reference_gap',Q(1,2)-Q(1,25)-Q(32,100))
    qmargin('far_cut_perturbation',Q(1,100)-3*delta)
    qmargin('niche_height',Q(7,10)-Q(2,3)-2*delta)
    qmargin('niche_containment',Q(1,20)-w-delta)
    qmargin('visited_angle',t-alpha)
    qmargin('interior_floor_slack',w*w/128-delta-12*alpha)
    qmargin('early_first_wall',Q(1,10)-Q(4,5)*t*t-12*alpha*t-delta)
    qmargin('omitted_wedge_area',Q(1,1000)-48*w)
    D=Q(403,500);eta=D/1000;zeta=Q(1,10**8)
    qmargin('floor_top_margin',eta/4-Q(1,10000))
    qmargin('trapezoid_height',Q(1,2000)-alpha)
    qmargin('trapezoid_niche_separation',eta-w)
    qmargin('terminal_top_point',eta/4000-zeta)
    qmargin('terminal_angle_remainder',eta/4000-alpha/2-alpha**2/6)
    qmargin('terminal_loss',Q(999,1000)*Q(499,1000)*D**2-Q(1,1000)-Q(10,31))
    R=Q(1,10**20);ell=10**6*R;normal=Q(1,10**8)
    qmargin('cone_angular_reserve',Q('3.14159')/2-Q('.04')-Q('1.53')-Q(1,2000))
    qmargin('cone_tangent_variation',Q(1,10000)-2**20*1024*ell)
    qmargin('cone_corner_separation',Q(1,1000)-8*ell)
    qmargin('cone_other_graph_separation',ell/33-1000*R)
    qmargin('roof_opposite_boundary',Q(1,3)-32*8*ell-8*ell)
    qmargin('normal_angle_range',Q('.039')/2-2*normal)
    qmargin('normal_derivative_error',Q(1,100)-1024*normal)
    qmargin('deep_point_exclusion',Q(5,51)*normal-Q(1,10**10))
    qmargin('tail_inactive_slack',Q(9,10)-normal-normal*Q(49,100))


def cutoff_checks():
    # Exact powers: epsilon=10^-600, root12=10^-50, root6=10^-100, sqrt=10^-300.
    eps=Q(1,10**600);root12=Q(1,10**50);root6=Q(1,10**100);root2=Q(1,10**300)
    require('exact_roots',root12**12==eps,'twelfth root')
    require('exact_roots',root6**6==eps,'sixth root')
    require('exact_roots',root2**2==eps,'square root')
    qmargin('entry_theorem_range',Q(1,10**144)-eps)
    qmargin('angle_theorem_range',Q(1,10**30)-eps)
    qmargin('entry_cap_radius',Q(1,10**40)-3000000*root12)
    qmargin('entry_terminal_radius',Q(1,10**20)-500*root6)
    k=Q(1001,1000);CH=Q(23,10);CA=Q(50);F=Q(100,49)
    qmargin('refined_full_angle_slack',Q(1,10**10)-k*root2-Q(248,5)*eps)
    qmargin('sector_recovery_radius',Q(1,10**20)-(CH+Q(3,2)*k)*root2)
    qmargin('forward_coefficient',CH-F*k-F*Q(248,5)*root2)
    qmargin('area_coefficient',CA-Q(62307,1250)*k-(3+8*k*k)*root2)
    qmargin('area_remainder_scale',Q(1,200)-root2)
    # Independently recheck the existing exact sector-budget inequality.
    h=Q(153,200);slo=h-h**3/6+h**5/120-h**7/5040
    chi=1-h*h/2+h**4/24-h**6/720+h**8/40320
    tlo=slo/chi;lam=Q(10031,10000);q=lam/(2*k*k)
    z=q*tlo*tlo/(1+q*tlo+tlo*tlo)
    Llo=z-z**3/3+z**5/5-z**7/7
    qmargin('sector_all_splits',CH*CH*Llo-lam)
    qmargin('sector_nonempty',CH*CH*slo*slo-2*k*k)
    # Negative controls: a weakened core height and a large input deficit must be rejected.
    require('negative_controls',not (first_position(p)[1]>I(Q(3,50))),'reject core height 0.06')
    require('negative_controls',not (3000000*Q(1,10**12)<Q(1,10**40)),
            '10^-144 is not sufficient for this local cap radius')
    return {'epsilon':'1/10^600','entry_support_upper':'3/10^44','entry_angle_upper':'5/10^98',
            'local_cap_support_radius':'1/10^40','local_terminal_angle_radius':'1/10^20',
            'normal_depth':'1/10^8','normal_error_threshold':'1/10^10','sector_radius':'1/10^20'}


def main():
    reference_checks();radius_checks();values=cutoff_checks()
    source=Path(__file__).read_bytes();backend=Path(dyadic_interval.__file__).read_bytes()
    report={'status':'passed','groups':dict(COUNTS),'checks':sum(COUNTS.values()),
            'proposed_cutoff':values,'reference_enclosures':REFERENCE,'exact_positive_margins':MARGINS,
            'arithmetic':'90-bit outward dyadic reference intervals; Fraction-only local/cutoff budgets',
            'scope':'numerical reference formulas and scalar implications of the analytic radius lemmas',
            'not_verified':['penalized polygon-limit arguments in notes26-27','contact classification',
                            'arbitrary-set local area comparison','uniform epigraph proof','Lean or CI'],
            'source_sha256':hashlib.sha256(source).hexdigest(),
            'source_git_blob':hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest(),
            'backend_sha256':hashlib.sha256(backend).hexdigest(),'python':platform.python_version()}
    out=HERE/'cutoff-radius-checks.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'checks':report['checks'],'groups':report['groups'],
                      'source_sha256':report['source_sha256'],'backend_sha256':report['backend_sha256']},indent=2))

if __name__=='__main__': main()
