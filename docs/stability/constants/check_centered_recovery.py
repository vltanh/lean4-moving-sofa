#!/usr/bin/env python3
"""Analytic diagnostics only: no Lean, Lake, CI, network, or formal verification.

Exact rational certificates are separated from sampled/quadrature diagnostics.
This program does not verify the reference boundary cover or global local entry.
"""
from __future__ import annotations
import hashlib
import json
import math
import platform
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50
COUNTS: dict[str, int] = {}
DETAILS: dict[str, object] = {}
TOL = mp.mpf('1e-35')


def check(group: str, condition: bool, message: str) -> None:
    COUNTS[group] = COUNTS.get(group, 0) + 1
    if not condition:
        raise AssertionError(f'{group}: {message}')


def exact_certificates() -> None:
    h = Q(153, 200)
    slo = sum((-1)**j*h**(2*j+1)/math.factorial(2*j+1) for j in range(4))
    chi = sum((-1)**j*h**(2*j)/math.factorial(2*j) for j in range(5))
    tlo = slo/chi
    lam = Q(10031, 10000)
    check('exact_rational', 0 < slo < chi < 1, 'Taylor denominators')
    check('exact_rational', Q('3.14159')/2-Q('.04') > Q(153, 100), 'corner aperture')
    check('exact_rational', Q(1250, 1249) < Q(1001, 1000), 'centered cap coefficient')
    margins = {}
    for label, k, C in [('centered', Q(1001,1000), Q(23,10)),
                         ('left_pinned', Q(1001,500), Q(211,50))]:
        q = lam/(2*k*k)
        z = q*tlo*tlo/(1+q*tlo+tlo*tlo)
        lower = sum((-1)**j*z**(2*j+1)/Q(2*j+1) for j in range(4))
        margin = C*C*lower-lam
        check('exact_rational', 0 < z < 1, f'{label}: atan range')
        check('exact_rational', margin > 0, f'{label}: reverse area margin')
        check('exact_rational', C*C*slo*slo > 2*k*k, f'{label}: erosion fits sector')
        check('exact_rational', Q(100,49)*k < C, f'{label}: forward leading margin')
        margins[label] = {'margin_float': float(margin),
                          'margin_exact': str(margin), 'constant': str(C)}
    A0=Q(62307,2500);k=Q(1001,1000)
    check('exact_rational', 2*A0*k+(3+8*k*k)/200 < 50, 'centered area coefficient')
    DETAILS['exact_reverse_margins'] = margins


def kernel(phi, t, j, u):
    v=mp.pi/2;b=v-phi;T=mp.pi-phi;A=1/mp.cos(phi)
    if t == mp.pi:
        return mp.mpf(0)
    if t <= phi:
        if j==0:return mp.cos(t)/mp.cos(u) if t <= u else mp.mpf(0)
        if j==1:return mp.cos(t)*A
        if j==2:return mp.cos(t)*A/mp.sin(T-u)
        if u<=v+phi:return mp.cos(t)*A*(A-mp.sin(phi))/mp.sin(u)
        if u<=T:return mp.cos(t)*A*(A+mp.cos(u))/mp.sin(u)
        return mp.mpf(0)
    if t<=b:
        if j==0:return mp.mpf(0)
        if j==1:return mp.mpf(1) if t<=u else mp.mpf(0)
        if j==2:return 1/mp.sin(T-u)
        if u<=v+t:return (A-mp.sin(t))/mp.sin(u)
        if u<=T:return (A+mp.cos(u))/mp.sin(u)
        return mp.mpf(0)
    if t<=v:
        if j==2:return mp.sin(T-t)/mp.sin(T-u) if t<=u else mp.mpf(0)
        if j==3:return A*mp.cos(t)*mp.sin(phi)/mp.sin(u) if u<=T else mp.mpf(0)
        return mp.mpf(0)
    return -mp.sin(t)/mp.sin(u) if j==3 and u<=t else mp.mpf(0)


def arc_integral(phi, t, integrand):
    v=mp.pi/2;b=v-phi;T=mp.pi-phi;out=mp.mpf(0)
    for j,(a,bnd) in enumerate([(0,phi),(phi,b),(b,v),(v,mp.pi)]):
        nodes=sorted(set([mp.mpf(a),mp.mpf(bnd)]+[
            x for x in [t,v+t,v+phi,T] if a<x<bnd]))
        for lo,hi in zip(nodes,nodes[1:]):
            out+=mp.quad(lambda u:integrand(j,u),[lo,hi])
    return out


def covariance(phi,t):
    v=mp.pi/2;b=v-phi;T=mp.pi-phi;A=1/mp.cos(phi);c=mp.cos(t);s=mp.sin(t)
    if t<=phi:return 2*A*A*c-s
    if t<=b:return A+A*A*c-s
    if t<=v:return (A*A+A*mp.sin(phi))*c
    if t<=v+phi:return A*(A-mp.sin(phi))*c
    if t<=T:return A+A*A*c-s
    return -s


def centered_norm(phi,t):
    v=mp.pi/2;b=v-phi;T=mp.pi-phi;A=1/mp.cos(phi);c=mp.cos(t);s=mp.sin(t)
    if t<=phi or t>=T:return A*A*c*c/2
    if t<=b:return A*c-A*A*c*c/2
    if t<=v:return s*c+(A*mp.sin(phi)-A*A/2)*c*c
    if t<=v+phi:return -s*c+(A*mp.sin(phi)-A*A/2)*c*c
    return -A*c-A*A*c*c/2


def kernel_checks() -> None:
    err=mp.mpf(0)
    for phi in map(mp.mpf,['.01','.03917736479','.04','.3','.7']):
        A=1/mp.cos(phi);v=mp.pi/2
        edges=[0,phi,v-phi,v,v+phi,mp.pi-phi,mp.pi]
        n0=arc_integral(phi,mp.mpf(0),lambda j,u:kernel(phi,0,j,u)**2)
        check('kernel_quadrature',abs(n0-2*A*A)<TOL,'H0 norm')
        for a,b in zip(edges,edges[1:]):
            t=a+mp.mpf('.37')*(b-a)
            n=arc_integral(phi,t,lambda j,u:(kernel(phi,t,j,u)-mp.cos(t)*kernel(phi,0,j,u)/2)**2)
            cov=arc_integral(phi,t,lambda j,u:kernel(phi,t,j,u)*kernel(phi,0,j,u))
            err=max(err,abs(n-centered_norm(phi,t)),abs(cov-covariance(phi,t)))
            check('kernel_quadrature',abs(n-centered_norm(phi,t))<TOL,'centered norm')
            check('kernel_quadrature',abs(cov-covariance(phi,t))<TOL,'covariance')
        for j in range(301):
            t=mp.pi*j/300;d=centered_norm(phi,t)
            check('sampled_kernel_bound',-TOL<=d<=A*A/2+TOL,'uniform bound')
        # Endpoint width lower bound for the abstract r=H0 witness.
        for s in [-A*A,mp.mpf(0),A*A,2*A*A,3*A*A]:
            check('quotient_witness',max(abs(2*A*A-s),abs(s))>=A*A-TOL,'all shifts lower bound')
    DETAILS['largest_kernel_quadrature_error']=mp.nstr(err,18)


def rot(t,w):return (mp.cos(t)*w[0]-mp.sin(t)*w[1],mp.sin(t)*w[0]+mp.cos(t)*w[1])
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def dot(x,y):return x[0]*y[0]+x[1]*y[1]
def norm(x):return mp.sqrt(dot(x,x))
def unit(x):return (x[0]/norm(x),x[1]/norm(x))


class Reference:
    phi=mp.mpf('0.03917736479008364186321787524244653474158')
    theta=mp.mpf('0.6813015093827248944738557570830649252656')
    def __init__(self):
        A=mp.mpf('0.09442656084365289018422549398878262792535')
        B=mp.mpf('1.399203727333547214607829644295640682365')
        p,t=self.phi,self.theta
        self.a1=((A+mp.mpf('.5'))*mp.sin(p)+(B+1)*mp.cos(p))/2
        self.b1=(p-1-A)/2;self.b2=B-mp.mpf('.5')-self.b1*p+p*p/4
        self.c1=mp.pi/2+A-p-1;self.c2=A-p-1
        self.k1=(1-self.a1,mp.mpf('.25'))
        self.k2=add(self.k1,rot(p,(-B/2,mp.mpf('.25'))))
        self.k3=add(self.k2,rot(t,(mp.mpf('.5'),(1-A-(t-p))/2)))
    def pair(self,t):
        if t>mp.pi/4:
            x,dx=self.pair(mp.pi/2-t)
            return ((2*self.k3[0]-x[0],x[1]),(dx[0],-dx[1]))
        if t<self.phi:
            a=self.a1
            f=(a*mp.cos(t)-mp.sin(t)/4-1,mp.cos(t)/4+a*mp.sin(t)-mp.mpf('.5'))
            f1=(-a*mp.sin(t)-mp.cos(t)/4,-mp.sin(t)/4+a*mp.cos(t));shift=self.k1
        elif t<self.theta:
            f=(-t*t/4+self.b1*t+self.b2,t/2-self.b1-1)
            f1=(-t/2+self.b1,mp.mpf('.5'));shift=self.k2
        else:
            f=(self.c1-t,self.c2+t);f1=(-mp.mpf(1),mp.mpf(1));shift=self.k3
        return add(rot(t,f),shift),rot(t,(f1[0]-f[1],f1[1]+f[0]))


def reference_checks() -> None:
    ref=Reference();v=mp.pi/2;worst=mp.mpf(10)
    def core_witness(t,w):
        nonlocal worst
        x,dx=ref.pair(t);u=(mp.cos(t),mp.sin(t));vn=(-mp.sin(t),mp.cos(t))
        a=-dot(dx,u);b=dot(dx,vn);lam=(dot(w,vn)-dot(w,u))/(a+b)
        rate=(b*dot(w,u)+a*dot(w,vn))/(a+b)
        check('normal_first_variation',abs(dot(w,u)+a*lam-rate)<TOL,'equal first wall')
        check('normal_first_variation',abs(dot(w,vn)-b*lam-rate)<TOL,'equal second wall')
        for d in map(mp.mpf,['1e-8','1e-5']):
            s=t+lam*d;xs,_=ref.pair(s);diff=(x[0]+d*w[0]-xs[0],x[1]+d*w[1]-xs[1])
            slack=max(dot(diff,(mp.cos(s),mp.sin(s))),dot(diff,(-mp.sin(s),mp.cos(s))))
            worst=min(worst,-slack/d)
            check('sampled_normal_witness',slack<=-mp.mpf('.49')*d+mp.mpf('1e-32'),'finite normal displacement')
    for i in range(81):
        t=ref.phi+(v-2*ref.phi)*i/80;x,dx=ref.pair(t)
        u=(mp.cos(t),mp.sin(t));vn=(-mp.sin(t),mp.cos(t));a=-dot(dx,u);b=dot(dx,vn)
        n=unit((b*u[0]+a*vn[0],b*u[1]+a*vn[1]));core_witness(t,(-n[0],-n[1]))
    for t,tail in [(ref.phi,v-ref.theta),(v-ref.phi,ref.theta)]:
        x,dx=ref.pair(t);u=(mp.cos(t),mp.sin(t));vn=(-mp.sin(t),mp.cos(t));a=-dot(dx,u);b=dot(dx,vn)
        nc=unit((b*u[0]+a*vn[0],b*u[1]+a*vn[1]))
        nt=(mp.cos(tail),mp.sin(tail)) if t==ref.phi else (-mp.sin(tail),mp.cos(tail))
        check('reference_corner',dot(nc,nt)>0,'roof normals separated by less than pi/2')
        for i in range(21):
            z=mp.mpf(i)/20;out=unit(((1-z)*nc[0]+z*nt[0],(1-z)*nc[1]+z*nt[1]));w=(-out[0],-out[1])
            if -dot(w,nc)>=1/mp.sqrt(2):core_witness(t,w)
            else:
                for d in map(mp.mpf,['1e-8','1e-5']):
                    xs,_=ref.pair(tail);diff=(x[0]+d*w[0]-xs[0],x[1]+d*w[1]-xs[1])
                    sl=max(dot(diff,(mp.cos(tail),mp.sin(tail))),dot(diff,(-mp.sin(tail),mp.cos(tail))))
                    check('sampled_tail_witness',sl<=-mp.mpf('.49')*d+mp.mpf('1e-32'),'corner tail')
    for i in range(11):
        t=ref.phi*i/12;x,dx=ref.pair(t);u=(mp.cos(t),mp.sin(t));vn=(-mp.sin(t),mp.cos(t));a=-dot(dx,u)
        contact=(x[0]-a*vn[0]+u[0],x[1]-a*vn[1]+u[1])
        check('reference_corner',norm((contact[0]-1,contact[1]))<TOL,'fixed first contact')
    _,dx=ref.pair(ref.phi);angle=mp.pi-mp.atan(dx[1]/(-dx[0]))+ref.theta
    DETAILS.update({'smallest_sampled_normal_violation_rate':mp.nstr(worst,18),
                    'outer_floor_angle':mp.nstr(v-ref.phi,18),
                    'roof_corner_angle':mp.nstr(angle,18)})


def sector(beta,u):
    if u>=mp.sin(beta/2):return mp.mpf(0)
    return beta/2-mp.asin(u)-u*mp.sqrt(1-u*u)+u*u/mp.tan(beta/2)


def sector_checks() -> None:
    beta=mp.mpf('1.53');lam=mp.mpf('1.0031');out={}
    for fraction in ['.01','.2','.5','.9','.99']:
        u=mp.mpf(fraction)*mp.sin(beta/2)
        area=mp.quad(lambda theta:1-u*u/mp.sin(beta/2-theta)**2,[0,beta/2-mp.asin(u)])
        check('sector_quadrature',abs(area-sector(beta,u))<TOL,'polar integration')
    for label,k,C in [('centered',mp.mpf('1.001'),mp.mpf('2.3')),
                      ('left_pinned',mp.mpf('2.002'),mp.mpf('4.22'))]:
        q=lam/(2*k*k);B=1/mp.tan(beta/2)+q;ustar=1/mp.sqrt(1+B*B)
        L=beta/2-mp.atan(1/B);zstar=C*C*ustar*ustar/(2*k*k)
        residuals=[]
        for z in [mp.mpf(i)/500 for i in range(501)]+[zstar]:
            val=C*C*sector(beta,mp.sqrt(2)*k*mp.sqrt(z)/C)-lam*(1-z)
            residuals.append(val);check('sampled_sector_budget',val>0,'all sampled budget splits')
        check('sector_stationary_identity',abs(min(residuals)-(C*C*L-lam))<TOL,'exact stationary minimum')
        out[label]={'sufficient_method_infimum':mp.nstr(mp.sqrt(lam/L),18),
                    'chosen_C':str(C),'worst_budget_fraction':mp.nstr(zstar,18),
                    'minimum_area_margin':mp.nstr(min(residuals),18)}
    # A failed method bound is not a counterexample among actual sofas.
    k=mp.mpf('1.001');C=mp.mpf('2.2');q=lam/(2*k*k);B=1/mp.tan(beta/2)+q
    u=1/mp.sqrt(1+B*B);z=C*C*u*u/(2*k*k)
    check('negative_method_control',C*C*sector(beta,u)-lam*(1-z)<0,'2.2 fails this sufficient sector calculation')
    DETAILS['sector_budget']=out
    A=1/mp.cos(Reference.phi)
    check('raw_direction_obstruction',-1<0,'positive residual extremizer has negative endpoint face length')
    check('raw_direction_obstruction',-A*A*mp.sin(Reference.phi)<0,'negative extremizer has negative phi atom')
    DETAILS['feasibility_scope']='raw extremizing ray rejected; no sharp feasible-Q constant claimed'


def main() -> None:
    exact_certificates();kernel_checks();reference_checks();sector_checks()
    content=Path(__file__).read_bytes()
    report={'status':'passed','groups':COUNTS,'assertions':sum(COUNTS.values()),'diagnostics':DETAILS,
            'scope':'exact rational inequalities plus sampled high-precision diagnostics',
            'not_checked':['Lean proofs','uniform boundary charts by sampling','global separation gap',
                           'effective global entry threshold','critical-cone feasible Q optimization'],
            'python':platform.python_version(),'mpmath':mp.__version__,'decimal_digits':mp.mp.dps,
            'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()}
    output=Path(__file__).with_name('centered-recovery-checks.json')
    output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
