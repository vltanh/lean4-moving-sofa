#!/usr/bin/env python3
"""Exact arithmetic and numerical diagnostics for the global-constant notes.

No Lean, Lake, CI, network, or external solver is invoked. A passing report is
not a proof of the global theorem or its uncomputed entry threshold.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import platform
import random
from fractions import Fraction as Q
import mpmath as mp

mp.mp.dps = 60
COUNTS: dict[str, int] = {}
DIAGNOSTICS: dict[str, str] = {}


def check(group: str, predicate: bool, detail: str) -> None:
    COUNTS[group] = COUNTS.get(group, 0) + 1
    if not predicate:
        raise AssertionError(f"{group}: {detail}")


def exact_checks() -> None:
    a, b, s, c = Q(59,625), Q(7,5), Q(39,1000), Q(127,128)
    L, h, c0, cr, k = Q(189,20), Q(951,100), Q(10,101), Q(5,51), Q(1001,500)
    kap = Q(100,1051)
    checks = {
        'small phase slope margin': a*(L*c+s)+b*(L*s-1) == Q(190489,40000000),
        'small phase transversality margin': a*(c-c0)+b*(s-c0) == Q(2441,8080000),
        'positive margins': a*(L*c+s)+b*(L*s-1)>0 and a*(c-c0)+b*(s-c0)>0,
        'Euclidean cone margin': h*h-(L*L+1)==Q(86,625),
        'ball ratio': kap*(h+1)==1 and kap<Q(1,10),
        'wing distance': 2*Q(3,4)**2<Q(9,8)**2,
        'large phase sine': Q(1,8)-Q(1,8)**3/6>Q(1,9)>1/L,
        'sine at phi': Q('0.039177264')-Q('0.04')**3/6>Q(39,1000),
        'second phase lower b': Q(1,2)-Q('.69')**2/4-Q('.528')*Q('.69')+Q('.9202')>Q(93,100),
        'second phase increasing height': Q(93,100)*(1-Q('.69')**2/2)-Q(3,4)*Q('.69')>0,
        'adaptive margin': c0-cr==Q(5,5151) and Q(122,200000)<c0-cr,
        'clipping threshold': cr/Q(200000)==Q(1,2040000),
        'reverse 31': 2*k*k+Q(2,3)<Q(737,250)**2 and Q(737,250)<kap*31,
        'reverse 30.5': 2*k*k+Q(10031,30000)<Q(29,10)**2 and Q(29,10)<kap*Q(61,2),
        'monotone 30': Q(283,200)*k<kap*30 and Q(283,200)**2>2,
        'forward': Q(51,5)*(k+Q(1,2))==Q(63801,2500)<Q(61,2),
        'angle coefficient': Q(999,1000)*Q(499,1000)*Q(403,500)**2-Q(1,1000)>Q(10,31),
        'reference height': Q(8897,10000)-Q(1589,5000)*Q(200,283)==Q(1882251,2830000)<Q(2,3),
        'outer margin': Q(3,4)**2+Q(3,5)**2<1,
    }
    for name, result in checks.items():
        check('rational_reference_and_budgets', result, name)
    A = 2*(Q(323,100)+1)+Q(51,5)*Q(807,500)
    check('rational_reference_and_budgets', A==Q(62307,2500), 'excess area factor')
    check('rational_reference_and_budgets', 2*A*k==Q(62369307,625000), 'area leading coefficient')
    check('rational_reference_and_budgets', 2*A*k+Q(827,25)/200<100, 'area final coefficient')
    z=Q(1,10**7)
    for name, result in {
        'clipped slack': k*z+Q(248,5)*z*z<Q(1,2040000),
        'outer margin': k*z<Q(1,5),
        'interior ball scale': Q(61,2)*z<Q(1,24),
        'linear remainder': Q(248,5)*z<Q(1,2),
        'area threshold': z<Q(1,200),
    }.items():
        check('conditional_downstream_threshold',result,name)
    alo, ahi=Q('1.210322322'),Q('1.210322523')
    klo, khi=Q('-0.613763330'),Q('-0.613763129')
    check('rational_reference_and_budgets',2-2*ahi-2*khi>Q(403,500),'minimum wing width')
    check('rational_reference_and_budgets',2-2*klo<Q(323,100),'maximum cap width')
    check('rational_reference_and_budgets',2*khi+4*ahi-2<Q(807,500),'maximum niche width')


def rot(t, v):
    return (mp.cos(t)*v[0]-mp.sin(t)*v[1], mp.sin(t)*v[0]+mp.cos(t)*v[1])


def add(v,w): return (v[0]+w[0],v[1]+w[1])
def dot(v,w): return v[0]*w[0]+v[1]*w[1]
def norm(v): return mp.sqrt(dot(v,v))


class Reference:
    # Post-solve high-precision candidate, used for diagnostics only.
    A=mp.mpf('0.09442656084365289018422549398878262792535')
    B=mp.mpf('1.399203727333547214607829644295640682365')
    phi=mp.mpf('0.03917736479008364186321787524244653474158')
    theta=mp.mpf('0.6813015093827248944738557570830649252656')

    def __init__(self):
        A,B,p,t=self.A,self.B,self.phi,self.theta
        self.a1=((A+mp.mpf('.5'))*mp.sin(p)+(B+1)*mp.cos(p))/2
        self.b1=(p-1-A)/2
        self.b2=B-mp.mpf('.5')-self.b1*p+p*p/4
        self.c1=mp.pi/2+A-p-1
        self.c2=A-p-1
        self.k1=(1-self.a1,mp.mpf('.25'))
        self.k2=add(self.k1,rot(p,(-B/2,mp.mpf('.25'))))
        self.k3=add(self.k2,rot(t,(mp.mpf('.5'),(1-A-(t-p))/2)))

    def triple(self,t):
        # Return x,x',x'' from the relevant phase, with explicit derivatives.
        v=mp.pi/2
        if t>v/2:
            x,dx,ddx=self.triple(v-t)
            return ((2*self.k3[0]-x[0],x[1]),(dx[0],-dx[1]),(-ddx[0],ddx[1]))
        if t<self.phi:
            a=self.a1
            f=(a*mp.cos(t)-mp.sin(t)/4-1,mp.cos(t)/4+a*mp.sin(t)-mp.mpf('.5'))
            f1=(-a*mp.sin(t)-mp.cos(t)/4,-mp.sin(t)/4+a*mp.cos(t))
            f2=(-a*mp.cos(t)+mp.sin(t)/4,-mp.cos(t)/4-a*mp.sin(t))
            shift=self.k1
        elif t<self.theta:
            f=(-t*t/4+self.b1*t+self.b2,t/2-self.b1-1)
            f1=(-t/2+self.b1,mp.mpf('.5'));f2=(-mp.mpf('.5'),mp.mpf(0));shift=self.k2
        else:
            f=(self.c1-t,self.c2+t);f1=(-mp.mpf(1),mp.mpf(1));f2=(mp.mpf(0),mp.mpf(0));shift=self.k3
        dx=rot(t,(f1[0]-f[1],f1[1]+f[0]))
        ddx=rot(t,(f2[0]-2*f1[1]-f[0],f2[1]+2*f1[0]-f[1]))
        return add(rot(t,f),shift),dx,ddx


def reference_checks() -> None:
    ref=Reference();v=mp.pi/2;tol=mp.mpf('1e-32')
    slopes=[];trans=[];speeds=[];accels=[];worst_slack=mp.mpf(0)
    nodes=[ref.phi,ref.theta,v/2,v-ref.theta,v-ref.phi]
    ts=[]
    for lo,hi in zip(nodes,nodes[1:]):
        ts += [lo+(hi-lo)*j/40 for j in range(41)]
    for t in ts:
        x,dx,ddx=ref.triple(t);u=(mp.cos(t),mp.sin(t));vn=(-mp.sin(t),mp.cos(t))
        a=-dot(dx,u);b=dot(dx,vn);X=-dx[0];Y=dx[1]
        lam=(mp.sin(t)-mp.cos(t))/(a+b)
        rate=X/(a+b)
        slopes.append(abs(Y)/X);trans.append(rate)
        check('sampled_phase_reference',a+b>=1,'positive frame speed')
        check('sampled_phase_reference',abs(Y)<=mp.mpf('9.45')*X,'slope')
        check('sampled_phase_reference',rate>=mp.mpf(10)/101,'transversality')
        for d in map(mp.mpf,['1e-9','1e-7','0.000005']):
            s=t+lam*d;xs,vs,_=ref.triple(s)
            displacement=(x[0]-xs[0],x[1]-d-xs[1])
            normals=[(mp.cos(s),mp.sin(s)),(-mp.sin(s),mp.cos(s))]
            for n in normals:
                slack=dot(displacement,n)
                worst_slack=max(worst_slack,slack+mp.mpf(5)/51*d)
                check('sampled_adaptive_slack',slack<=-mp.mpf(5)/51*d+tol,'uniform sampled slack')
        r1=-mp.sin(t)+a*lam;r2=-mp.cos(t)-b*lam
        check('balanced_first_variation',abs(r1+rate)<tol and abs(r2+rate)<tol,'balanced rates')
    for j in range(401):
        x,dx,ddx=ref.triple(v*j/400)
        speeds.append(norm(dx));accels.append(norm(ddx))
        check('sampled_reference_scales',norm(dx)<10 and norm(ddx)<100,'velocity/acceleration')
        check('sampled_reference_scales',x[1]<mp.mpf(2)/3,'height')
    DIAGNOSTICS.update({
        'largest_sampled_core_slope':mp.nstr(max(slopes),18),
        'smallest_sampled_transversality':mp.nstr(min(trans),18),
        'largest_sampled_speed':mp.nstr(max(speeds),18),
        'largest_sampled_acceleration':mp.nstr(max(accels),18),
        'reference_peak_height':mp.nstr(ref.triple(v/2)[0][1],18),
        'positive_slack_violation_allowance':mp.nstr(worst_slack,12),
    })


def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])


def hull(points):
    p=sorted(set(points))
    if len(p)<3: return p
    lower=[];upper=[]
    for x in p:
        while len(lower)>=2 and cross(lower[-2],lower[-1],x)<=0: lower.pop()
        lower.append(x)
    for x in reversed(p):
        while len(upper)>=2 and cross(upper[-2],upper[-1],x)<=0: upper.pop()
        upper.append(x)
    return lower[:-1]+upper[:-1]


def area(p): return abs(sum(x[0]*y[1]-x[1]*y[0] for x,y in zip(p,p[1:]+p[:1])))/2


def polygon_checks() -> None:
    rng=random.Random(734813)
    polys=[hull([(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))]),
           hull([(Q(0),Q(0)),(Q(3),Q(0)),(Q(3),Q(1)),(Q(0),Q(1))])]
    for _ in range(30):
        polys.append(hull([(Q(rng.randint(-100,100),37),Q(rng.randint(-100,100),41)) for _ in range(15)]))
    for p in polys:
        W=max(x[0] for x in p)-min(x[0] for x in p)
        H=max(x[1] for x in p)-min(x[1] for x in p)
        for h in [Q(0),Q(1,100),Q(1,8),Q(2,3)]:
            new=hull([(x+sx*h,y+sy*h) for x,y in p for sx,sy in [(-1,-1),(-1,1),(1,-1),(1,1)]])
            check('exact_polygon_square_dilation',area(new)-area(p)==2*(W+H)*h+4*h*h,'Cavalieri layer identity')


def budget_checks() -> None:
    k=mp.mpf('2.002');kap=mp.mpf(100)/1051;gamma=mp.mpf(10031)/10000
    A=mp.mpf(62307)/2500
    weights=[mp.mpf(j)/100 for j in range(101)]
    weights.append((2*k*k)/(2*k*k+gamma/mp.pi))
    for eps in map(mp.mpf,['1e-14','1e-10','0.000025']):
        for q in weights:
            e=q*eps
            reverse=mp.sqrt(2)*k*mp.sqrt(e)+mp.sqrt(gamma/mp.pi)*mp.sqrt(eps-e)
            check('split_deficit_stress',reverse<kap*mp.mpf('30.5')*mp.sqrt(eps),'reverse radius')
            check('split_deficit_stress',3*eps-2*e+2*A*k*mp.sqrt(e)+8*k*k*e<=100*mp.sqrt(eps),'area')
    DIAGNOSTICS['reverse_reference_formula']=mp.nstr(mp.sqrt(2*k*k+gamma/mp.pi)/kap,18)
    DIAGNOSTICS['puncture_lower_bound']=mp.nstr(1/mp.sqrt(mp.pi),18)


def main() -> None:
    exact_checks();reference_checks();polygon_checks();budget_checks()
    content=Path(__file__).read_bytes()
    report={
        'status':'passed','groups':COUNTS,'assertions':sum(COUNTS.values()),
        'diagnostics_not_certificates':DIAGNOSTICS,
        'scope':'exact rational/polygon arithmetic and sampled high-precision diagnostics only',
        'not_checked':['Lean elaboration','kernel axioms','global compactness separation gap',
                       'effective global epsilon0','uniform C1 proof by numerical sampling'],
        'python':platform.python_version(),'mpmath':mp.__version__,'decimal_digits':mp.mp.dps,
        'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest(),
    }
    output=Path(__file__).with_name('global-constant-checks.json')
    output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
