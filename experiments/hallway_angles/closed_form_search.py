"""Bounded numerical recognition of the analytic contact-model root.

A negative PSLQ search is NOT an impossibility theorem. Source equations:
EXACT_CONTACT_CROSSING.md at 267ba93548d58c23f10e6b8793b952099acdc5b2.
The model root is not known to be the unrestricted phase transition.
"""
from __future__ import annotations
import argparse
import json
import mpmath as mp


def equations(beta, alpha):
    d, q = mp.cos(beta), mp.sin(beta)
    mu = mp.sqrt(3/(4*q*q)-1)
    eta = mp.sqrt((-1-2*d)/(1-2*d))
    T = beta/2-alpha
    contact = ((mp.cos(alpha)+2*mp.cos(beta-alpha)+eta*eta)*mp.tanh(mu*T)
               -eta*(mp.cos(alpha)-2*mp.cos(beta-alpha)-1))
    forward = (d*beta+(1-2*d)*alpha/2-q
               +((1-4*d)*mp.cos(alpha)-(1+2*d*d))/(3*mp.sin(alpha)))/(1+2*d)
    er = mp.sqrt((2+d)/(2-d))
    K = (mp.pi-beta)*mp.sqrt(1+3/q**2)/2
    ratio = er*mp.sin(K)/(mp.cos(K)+er*mp.sin(K))
    reverse = (mp.pi-beta)/(2+d)+(1-2*d)/(4*q)+3*d*d*ratio/(2*q*(2+d)**2)
    return contact, forward-reverse


def solve(precision: int):
    with mp.workdps(precision):
        return tuple(mp.findroot(equations, (mp.mpf('2.385379'),mp.mpf('0.49795')),
                                 tol=mp.mpf(10)**(-precision+20),maxsteps=100))


def run(precision=180, degree=8, height=10**6, maxsteps=3000):
    if precision<80 or not 1<=degree<=16 or height<2 or maxsteps<1:
        raise ValueError('require precision>=80, 1<=degree<=16, height>=2, maxsteps>=1')
    low = solve(precision)
    high = solve(precision+80)
    with mp.workdps(precision):
        beta,alpha=high
        residual=max(abs(v) for v in equations(beta,alpha))
        agreement=max(abs(x-y) for x,y in zip(low,high))
        if residual>mp.mpf(10)**(-precision+30) or agreement>mp.mpf(10)**(-precision+30):
            raise ArithmeticError('high precision numerical root did not agree')
        vals={'beta':beta,'beta_over_pi':beta/mp.pi,'cos_beta':mp.cos(beta),
              'tan_beta_half':mp.tan(beta/2),'alpha_over_pi':alpha/mp.pi,
              'cos_alpha':mp.cos(alpha),'T':beta/2-alpha,'T_over_beta':(beta/2-alpha)/beta}
        tol=mp.mpf(10)**(-precision+40)
        records=[]
        for name,value in vals.items():
            for n in range(1,degree+1):
                relation=mp.pslq(mp.matrix([value**k for k in range(n+1)]),
                                  tol=tol,maxcoeff=height,maxsteps=maxsteps)
                records.append({'target':name,'polynomial_degree':n,'relation':relation,
                                'outcome':'candidate_relation_REQUIRES_EXACT_PROOF' if relation
                                           else 'no_relation_returned_NOT_AN_EXCLUSION_CERTIFICATE'})
        bases={
            'quadratic_constants':['1','pi','sqrt2','sqrt3','sqrt5','sqrt6','sqrt7'],
            'elementary_constants':['1','pi','sqrt2','sqrt3','sqrt5','log2','log3','log5'],
            'pi_products':['1','pi','pi2','pi_sqrt2','pi_sqrt3','pi_sqrt5'],
        }
        constants={'1':mp.mpf(1),'pi':mp.pi,'pi2':mp.pi**2,
                   **{f'sqrt{k}':mp.sqrt(k) for k in (2,3,5,6,7)},
                   **{f'log{k}':mp.log(k) for k in (2,3,5)},
                   **{f'pi_sqrt{k}':mp.pi*mp.sqrt(k) for k in (2,3,5)}}
        for name,names in bases.items():
            relation=mp.pslq(mp.matrix([beta]+[constants[n] for n in names]),
                              tol=tol,maxcoeff=height,maxsteps=maxsteps)
            records.append({'target':'beta','basis':name,'terms':['beta']+names,'relation':relation,
                            'outcome':'candidate_relation_REQUIRES_EXACT_PROOF' if relation
                                     else 'no_relation_returned_NOT_AN_EXCLUSION_CERTIFICATE'})
        return {'format':'contact-closed-form-recognition-v1',
                'meaning':'bounded heuristic recognition; not proof of transcendence or absence of elementary closed form',
                'precision_decimal_digits':precision,'crosscheck_digits':precision+80,
                'pslq_tolerance':mp.nstr(tol,8),'height':height,'maxsteps':maxsteps,
                'equations_source_commit':'267ba93548d58c23f10e6b8793b952099acdc5b2',
                'root_beta_radians':mp.nstr(beta,80),'root_alpha_radians':mp.nstr(alpha,80),
                'residual':mp.nstr(residual,8),'precision_agreement':mp.nstr(agreement,8),
                'records':records,'mpmath_version':mp.__version__}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--precision',type=int,default=180)
    p.add_argument('--degree',type=int,default=8)
    p.add_argument('--height',type=int,default=10**6)
    p.add_argument('--maxsteps',type=int,default=3000)
    p.add_argument('--output')
    a=p.parse_args();text=json.dumps(run(a.precision,a.degree,a.height,a.maxsteps),indent=2)+'\n'
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(text)
    else:print(text,end='')
