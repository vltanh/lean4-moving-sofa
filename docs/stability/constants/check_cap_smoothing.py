#!/usr/bin/env python3
"""Diagnostics for the actual-cap residual witness, not a feasible-Q certificate."""
from __future__ import annotations
import hashlib, json, platform
from pathlib import Path
import mpmath as mp
from check_centered_recovery import Reference, covariance
mp.mp.dps=50

def dc(phi,t):
    A=1/mp.cos(phi);v=mp.pi/2;b=v-phi;T=mp.pi-phi;c=mp.cos(t);s=mp.sin(t)
    if t<=phi:return -2*A*A*s-c
    if t<=b:return -A*A*s-c
    if t<=v:return -(A*A+A*mp.sin(phi))*s
    if t<=v+phi:return -A*(A-mp.sin(phi))*s
    if t<=T:return -A*A*s-c
    return -c

class SmoothWitness:
    def __init__(self,phi,eta):
        self.phi=phi;self.eta=eta;self.T=mp.pi-phi;self.A=1/mp.cos(phi)
        self.pieces=[]
        # Only the positive-curvature side of each normal gap is changed.
        for lo,hi,dlo,dhi in [(phi,phi+eta,dc(phi,phi),dc(phi,phi+eta)),
                              (self.T-eta,self.T,dc(phi,self.T-eta),mp.cos(phi))]:
            y0=covariance(phi,lo);y1=covariance(phi,hi);h=hi-lo
            a=y0;b=h*dlo;c=3*(y1-y0)-h*(2*dlo+dhi);d=2*(y0-y1)+h*(dlo+dhi)
            self.pieces.append((lo,hi,(a,b,c,d)))
        self.curvature_bound=max([self.A]+[
            sum(abs(x) for x in coeff)+(2*abs(coeff[2])+6*abs(coeff[3]))/(hi-lo)**2
            for lo,hi,coeff in self.pieces])
    def pair(self,t):
        for lo,hi,(a,b,c,d) in self.pieces:
            if lo<=t<=hi:
                z=(t-lo)/(hi-lo)
                return a+b*z+c*z*z+d*z**3,(b+2*c*z+3*d*z*z)/(hi-lo)
        return covariance(self.phi,t),dc(self.phi,t)
    def energy(self):
        p=self.phi;v=mp.pi/2;b=v-p;T=self.T
        FT=self.pair(T)[0]
        def residual(j,t):
            if j==0:return 1/mp.cos(t)
            if j==3 and t>=T:return mp.mpf(0)
            f,df=self.pair(t)
            if j==1:return self.pair(t+v)[0]-df
            if j==2:return (FT-f*mp.cos(T-t))/mp.sin(T-t)-df
            return mp.cos(t)/mp.sin(t)*f-df
        energy=mp.mpf(0)
        specials=[p,p+self.eta,v-p-self.eta,b,v,v+p,T-self.eta,T]
        for j,(lo,hi) in enumerate([(0,p),(p,b),(b,v),(v,mp.pi)]):
            nodes=sorted(set([mp.mpf(lo),mp.mpf(hi)]+[x for x in specials if lo<x<hi]))
            for a,z in zip(nodes,nodes[1:]):
                energy+=mp.quad(lambda t:residual(j,t)**2,[a,z])/2
        return energy

def main():
    phi=Reference.phi;A=1/mp.cos(phi);runs=[]
    for eta in map(mp.mpf,['.01','.003','.001','.0003','.0001']):
        w=SmoothWitness(phi,eta);E=w.energy();ratio=A*A/mp.sqrt(E)
        tau=1/(8*(1+w.curvature_bound+A*A+mp.tan(phi)))
        assert E>=A*A-mp.mpf('1e-35')
        assert tau*w.curvature_bound<mp.mpf('.25')
        assert abs(w.pair(0)[0]-2*A*A)<mp.mpf('1e-35')
        assert abs(w.pair(mp.pi/2)[0])<mp.mpf('1e-35')
        for lo,hi,coeff in w.pieces:
            a,b,c,d=coeff
            assert abs(w.pair(lo)[0]-covariance(phi,lo))<mp.mpf('1e-35')
            assert abs(w.pair(hi)[0]-covariance(phi,hi))<mp.mpf('1e-35')
        runs.append({'smoothing_width':str(eta),'residual_energy':mp.nstr(E,20),
                     'endpoint_quotient_lower_ratio':mp.nstr(ratio,20),
                     'safe_perturbation_amplitude':mp.nstr(tau,12),
                     'energy_excess':mp.nstr(E-A*A,15)})
    assert all(mp.mpf(x['endpoint_quotient_lower_ratio'])<mp.mpf(y['endpoint_quotient_lower_ratio'])
               for x,y in zip(runs,runs[1:]))
    source=Path(__file__).read_bytes()
    report={'status':'passed','runs':runs,'abstract_optimal_coefficient':mp.nstr(A,20),
            'scope':'smoothed actual-cap support witness using the reference curvature lower bound',
            'not_claimed':['feasible auxiliary bodies with negligible deficit','sharp Q coefficient',
                           'sharp area-deficit coefficient','Lean or interval verification'],
            'python':platform.python_version(),'mpmath':mp.__version__,'decimal_digits':mp.mp.dps,
            'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()}
    Path(__file__).with_name('cap-smoothing-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
