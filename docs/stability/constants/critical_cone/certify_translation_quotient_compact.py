"""Exact dyadic all-pairs upper bound for the critical translation quotient.

Imports the existing rank-two continuum model. No floats decide acceptance.
The analytic two-point quotient identity is an input, not tested by the program.
"""
from __future__ import annotations
from functools import lru_cache
from fractions import Fraction
from pathlib import Path
import argparse,hashlib,json,time
from certify_critical_rank2 import iv,Z,ONE,imin,imax,positive_part_bound
from compact_rank2 import CompactModel as Model
from dyadic_interval import SCALE

def certificate(coefficient='0.93',max_visits=250000,max_depth=32):
    m=Model(iv.mpf(['0.039177264','0.039177465']),iv.mpf(['0.681301409','0.681301610']))
    ranges=m.ranges();limit=iv.mpf(coefficient)**2
    @lru_cache(maxsize=20000)
    def pack(region,i,den):
        kind,a,b=ranges[region]
        t=a+iv.mpf([iv.mpf(i)/den,iv.mpf(i+1)/den])*(b-a)
        pk='last' if region>=3 else kind
        P=m.pieces(pk,t);co=iv.cos(t)
        c0=m.inner(P,m.P0)
        w1=m.inner(P,m.VB)-co*m.w01/2;w2=m.inner(P,m.VD)-co*m.w02/2
        inv1=(m.S22*w1-m.S12*w2)/m.det
        inv2=(m.S11*w2-m.S12*w1)/m.det
        D=m.centered_norm(kind,t)-positive_part_bound(w1*inv1+w2*inv2)
        return t,P,co,c0,w1,w2,inv1,inv2,D
    def bound(cell):
        rt,i,nt,ru,j,nu,depth=cell
        t,Pt,ct,c0t,w1t,w2t,a1t,a2t,Dt=pack(rt,i,nt)
        u,Pu,cu,c0u,w1u,w2u,a1u,a2u,Du=pack(ru,j,nu)
        if 2*max(Dt.b,Du.b)<limit.a:
            return 2*max(Dt.b,Du.b),'centered_triangle'
        den=abs(ct)+abs(cu)
        if den.a<=0:raise ZeroDivisionError('unresolved cosine denominator')
        if rt>=3 and ru>=3:K=-iv.sin(imax(t,u))*iv.cos(imin(t,u))
        else:K=m.inner(Pt,Pu)
        Kc=K-cu*c0t/2-ct*c0u/2+ct*cu*m.A**2/2
        Kq=Kc-w1t*a1u-w2t*a2u
        norm=2*(cu**2*Dt+ct**2*Du-2*ct*cu*Kq)/(den**2)
        return norm.b,'pair'
    stack=[(r,0,1,s,0,1,0) for r in range(6) for s in range(r,6)]
    records=[];failed=[];visits=0;worst=Z;start=time.time()
    while stack and visits<max_visits:
        cell=stack.pop();visits+=1
        try:b,method=bound(cell)
        except ZeroDivisionError:b=iv.mpf(1000);method='singular_enclosure'
        if b<limit.a:
            worst=max(worst,b);records.append({'cell':list(cell[:6]),'squared_upper':b.exact(),'method':method})
        elif cell[-1]>=max_depth:failed.append({'cell':list(cell),'bound':str(b),'method':method})
        else:
            rt,i,nt,ru,j,nu,depth=cell
            wt=(ranges[rt][2]-ranges[rt][1]).b/nt
            wu=(ranges[ru][2]-ranges[ru][1]).b/nu
            if wt>=wu:stack.extend([(rt,2*i,2*nt,ru,j,nu,depth+1),(rt,2*i+1,2*nt,ru,j,nu,depth+1)])
            else:stack.extend([(rt,i,nt,ru,2*j,2*nu,depth+1),(rt,i,nt,ru,2*j+1,2*nu,depth+1)])
        if visits%2000==0:print('pairs',visits,len(records),len(stack),len(failed),round(time.time()-start,1),flush=True)
    return {'status':'passed' if not stack and not failed else 'inconclusive','coefficient':str(Fraction(coefficient)),
        'parameter_box':{'phi':['0.039177264','0.039177465'],'theta':['0.681301409','0.681301610']},
        'normalization':'infimum over horizontal translations, not fixed midpoint',
        'arithmetic':'90-bit exact dyadic outward rounding; rational comparisons',
        'visited':visits,'leaves':len(records),'failed':failed,'frontier':len(stack),'worst_squared_upper':worst.exact(),
        'seconds':time.time()-start,'leaf_certificate':records,
        'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in ['certify_translation_quotient_compact.py','compact_rank2.py','certify_critical_rank2.py','dyadic_interval.py']},
        'scope':'continuum two-point rank-two relaxation; analytic identities are inputs',
        'not_claimed':['feasible lower bound','global original-sofa entry','Lean verification']}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--coefficient',default='0.93');ap.add_argument('--visits',type=int,default=250000);ap.add_argument('--depth',type=int,default=32);ap.add_argument('--output',default='translation-quotient-certificate.json');a=ap.parse_args()
    result=certificate(a.coefficient,a.visits,a.depth)
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='leaf_certificate'},indent=2))
