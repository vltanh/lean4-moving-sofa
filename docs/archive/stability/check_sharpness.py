#!/usr/bin/env python3
"""Independent numerical/algebraic checks, never a Lean or CI invocation.

The tests evaluate the analytic formulas, not the Lean proof terms. They do not
certify topology, integrability at every endpoint, or any formal declaration.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import platform
import mpmath as mp

mp.mp.dps = 60
TOL = mp.mpf('1e-45')
checks: dict[str, dict[str, str | int]] = {}


def check(name: str, pairs: list[tuple[mp.mpf, mp.mpf]]) -> None:
    errors = [abs(a - b) / (1 + abs(b)) for a, b in pairs]
    worst = max(errors, default=mp.mpf(0))
    if worst > TOL:
        raise AssertionError(f'{name}: relative error {worst} > {TOL}')
    checks[name] = {'cases': len(pairs), 'max_scaled_error': mp.nstr(worst, 12)}


def kernel_norm(phi: mp.mpf, t: mp.mpf) -> mp.mpf:
    v, b, T = mp.pi / 2, mp.pi / 2 - phi, mp.pi - phi
    A = 1 / mp.cos(phi)
    if t <= phi:
        middle_phi = (b-phi + mp.quad(lambda u: 1/mp.sin(T-u)**2, [b,v])
                      + (A-mp.sin(phi))**2 * mp.quad(lambda u: 1/mp.sin(u)**2, [v,v+phi])
                      + mp.quad(lambda u: ((A+mp.cos(u))/mp.sin(u))**2, [v+phi,T]))
        return mp.cos(t)**2 * (A*A*middle_phi + mp.quad(lambda u: 1/mp.cos(u)**2, [t, phi]))
    if t <= b:
        return (b-t + mp.quad(lambda u: 1/mp.sin(T-u)**2, [b,v])
                + (A-mp.sin(t))**2 * mp.quad(lambda u: 1/mp.sin(u)**2, [v,v+t])
                + mp.quad(lambda u: ((A+mp.cos(u))/mp.sin(u))**2, [v+t,T]))
    if t <= v:
        return ((mp.cos(t)/mp.cos(phi))**2 * (-mp.sin(T)*mp.cos(T))
                + mp.sin(T-t)**2 * mp.quad(lambda u: 1/mp.sin(T-u)**2, [t,v]))
    if t == mp.pi:
        return mp.mpf(0)
    return mp.sin(t)**2 * mp.quad(lambda u: 1/mp.sin(u)**2, [v,t])


def formula(phi: mp.mpf, t: mp.mpf) -> mp.mpf:
    A = 1/mp.cos(phi)
    if t <= phi:
        return mp.cos(t)**2 * (2*A*A-mp.tan(t))
    if t <= mp.pi/2-phi:
        return mp.cos(t)*(2*A-mp.sin(t))
    if t <= mp.pi/2:
        return mp.sin(t)*mp.cos(t)+2*mp.tan(phi)*mp.cos(t)**2
    return -mp.sin(t)*mp.cos(t)


def main() -> None:
    phis = [mp.mpf(s) for s in ['0.01','0.03917736479','0.04','0.3','0.7']]
    pairs = []
    for phi in phis:
        nodes = [mp.mpf(0), phi, mp.pi/2-phi, mp.pi/2, mp.pi]
        for a,b in zip(nodes,nodes[1:]):
            for q in [mp.mpf('0.17'),mp.mpf('0.51'),mp.mpf('0.89')]:
                t = a+q*(b-a)
                pairs.append((kernel_norm(phi,t),formula(phi,t)))
    check('actual_kernel_square_integrals',pairs)
    pairs = []
    for phi in phis:
        A=1/mp.cos(phi)
        for t in [mp.mpf('0.01'),mp.mpf('0.8'),mp.mpf('2.9')]:
            F=lambda u: -(A*A+1)*mp.cos(u)/mp.sin(u)-2*A/mp.sin(u)-u
            pairs.append((mp.diff(F,t),((A+mp.cos(t))/mp.sin(t))**2))
    check('tail_primitive_derivative',pairs)
    pairs=[]
    funcs=[lambda t: mp.sin(2*t),lambda t: mp.sin(t)*(t-mp.pi/2),
           lambda t:(t-mp.pi/2)*(t-mp.pi)]
    for phi in phis:
        v,b,T=mp.pi/2,mp.pi/2-phi,mp.pi-phi
        A=1/mp.cos(phi)
        for f in funcs:
            df=lambda t: mp.diff(f,t)
            r1=lambda t:-mp.tan(t)*f(t)-df(t)
            r2=lambda t:f(t+v)-df(t)
            r3=lambda t:f(T)/mp.sin(T-t)-mp.cos(T-t)/mp.sin(T-t)*f(t)-df(t)
            r4=lambda t:mp.cos(t)/mp.sin(t)*f(t)-df(t)
            t=(phi+b)/2
            val=(mp.quad(r2,[t,b])+mp.quad(lambda u:r3(u)/mp.sin(T-u),[b,v])
                 +(A-mp.sin(t))*mp.quad(lambda u:r4(u)/mp.sin(u),[v,v+t])
                 +mp.quad(lambda u:(A+mp.cos(u))/mp.sin(u)*r4(u),[v+t,T]))
            pairs.append((val,f(t)))
            t=phi/2
            pairs.append((mp.cos(t)*(A*f(phi)+mp.quad(lambda u:r1(u)/mp.cos(u),[t,phi])),f(t)))
            t=(b+v)/2
            pairs.append((-(mp.cos(t)/mp.cos(phi))*f(T)
                          +mp.sin(T-t)*mp.quad(lambda u:r3(u)/mp.sin(T-u),[t,v]),f(t)))
            t=(v+T)/2
            pairs.append((-mp.sin(t)*mp.quad(lambda u:r4(u)/mp.sin(u),[v,t]),f(t)))
            B=lambda u:(A+mp.cos(u))/mp.sin(u)
            pairs.append((mp.diff(lambda u:B(u)*f(u),t),-f(t)-B(t)*r4(t)))
    check('reconstruction_and_product_identity',pairs)
    pairs=[]
    for phi in phis:
        b,v,A=mp.pi/2-phi,mp.pi/2,1/mp.cos(phi)
        pairs += [(mp.cos(phi)**2*(2*A*A-mp.tan(phi)),mp.cos(phi)*(2*A-mp.sin(phi))),
                  (mp.cos(b)*(2*A-mp.sin(b)),mp.sin(b)*mp.cos(b)+2*mp.tan(phi)*mp.cos(b)**2)]
        assert all(-TOL <= formula(phi,mp.pi*i/300) <= 2*A*A+TOL for i in range(301))
    check('junctions_and_sampled_uniform_bound',pairs)
    check('rational_constant',[(mp.mpf(2)/(1-mp.mpf('0.04')**2/2),mp.mpf(2500)/1249)])
    assert mp.mpf(2500)/1249 < mp.mpf(1001)/500
    pairs=[]
    for a in [mp.mpf('0.6'),mp.mpf('1'),mp.mpf('1.7')]:
        for r in [mp.mpf('0.001'),mp.mpf('0.03')]:
            for C in [mp.mpf('-3'),mp.mpf('0'),mp.mpf('20')]:
                pairs.append((C*(mp.pi*r*r)**a,C*mp.pi**a*r**(2*a-1)*r))
    check('puncture_power_identity',pairs)
    source=Path(__file__).read_bytes()
    report={'status':'passed','scope':'numerical analytic formulas only; no Lean or CI',
            'not_checked':['Lean elaboration','proof dependencies','topology','rigid-orbit compactness'],
            'python':platform.python_version(),'mpmath':mp.__version__,'decimal_precision':mp.mp.dps,
            'tolerance':str(TOL),'groups':checks,
            'cases':sum(int(c['cases']) for c in checks.values()),
            'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()}
    output=Path(__file__).with_name('sharpness-checks.json')
    output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
