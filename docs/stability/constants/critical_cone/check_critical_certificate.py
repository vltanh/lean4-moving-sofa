"""Reproduce exact interval checks, validate coverage, and test arithmetic invariants."""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,random,platform
from dyadic_interval import Interval as I,iv,SCALE
from certify_critical_rank2 import certify,Model
counts={}
def check(g,p,msg):
    counts[g]=counts.get(g,0)+1
    if not p:raise AssertionError(msg)
def contains(x,q):return F(x.lo,SCALE)<=q<=F(x.hi,SCALE)
def main():
    rng=random.Random(62026)
    for _ in range(300):
        a,b=sorted([F(rng.randint(-50,50),rng.randint(1,31)) for _ in range(2)])
        c,d=sorted([F(rng.randint(-50,50),rng.randint(1,31)) for _ in range(2)])
        X=I(a,b);Y=I(c,d);x=(a+b)/2;y=(c+d)/2
        for z,q in [(X+Y,x+y),(X-Y,x-y),(X*Y,x*y),(X**2,x*x),(abs(X),abs(x))]:
            check('exact_arithmetic',contains(z,q),'arithmetic enclosure')
        if not c<=0<=d:check('exact_arithmetic',contains(X/Y,x/y),'division enclosure')
    try:I(-1,1).reciprocal();check('zero_division',False,'division through zero accepted')
    except ZeroDivisionError:check('zero_division',True,'expected rejection')
    p=iv.mpf(['0.039177264','0.039177465']);th=iv.mpf(['0.681301409','0.681301610'])
    m=Model(p,th);w=I(F(1,8))
    side=[(1+I('-0.527624699')-th/2>I(F(1,8)),'density'),
          (m.c+w<m.b,'B interval within middle cap'),
          (m.d-w>m.v,'D interval within last cap'),
          (iv.tan(m.c+w)<2,'B tangent bound'),
          (m.DD<1,'D energy weight'),
          (iv.sin(I.raw((m.T-m.d).lo,(m.T-m.d+w).hi))>I('0.7'),'D sine bound'),
          (abs(iv.cos(I.raw((m.d-w).lo,m.d.hi))/iv.sin(I.raw((m.d-w).lo,m.d.hi)))<1,'last cotangent bound'),
          (1/iv.cos(p)<I('1.001'),'secant cap constant')]
    for passed,name in side:check('exact_reference_bounds',passed,name)
    check('exact_scalar_bounds',F(1001,500)*F(1001,1000)+2<5,'B support')
    check('exact_scalar_bounds',F(1001,500)*F(1001,1000)+F(3,2)<4,'D support')
    check('exact_scalar_bounds',(F(1001,500)+4)/F(7,10)<9,'D derivative')
    check('exact_scalar_bounds',(10+F(1001,500))*F(3,8)+3<8,'B slack derivative')
    check('exact_scalar_bounds',(9+F(1001,500))*F(3,8)+3<8,'D slack derivative')
    check('exact_scalar_bounds',F(1,10**18)<=F(1,512),'Q threshold range')
    check('exact_scalar_bounds',F(49,50)+F(8,1000)<F(99,100),'final coefficient')
    result=certify();check('certificate',result['status']=='passed','continuum certificate failed')
    for region,_,_ in m.ranges():
        cells=sorted((F(x['i'],x['denominator']),F(x['i']+1,x['denominator']))
                     for x in result['leaf_certificate'] if x['region']==region)
        check('coverage',cells[0][0]==0 and cells[-1][1]==1,'missing region endpoints')
        for a,b in zip(cells,cells[1:]):check('coverage',a[1]==b[0],'gap or overlap')
    for cell in result['leaf_certificate']:
        b=cell['squared_bound'];s=cell['slack_sensitivity_bound']
        check('leaf_bounds',F(b['upper_numerator'],b['denominator'])<F(49,50)**2,'squared norm')
        check('leaf_bounds',F(s['upper_numerator'],s['denominator'])<F(1,2),'sensitivity')
    neg=certify('0.90',max_depth=4)
    check('negative_control',neg['status']=='inconclusive' and len(neg['failed'])>0,'invalid target accepted')
    Path('critical_rank2_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    summary={k:v for k,v in result.items() if k!='leaf_certificate'}
    summary.update({'test_status':'passed','test_counts':counts,'tests':sum(counts.values()),
                    'negative_control_failed_cells':len(neg['failed']),'python':platform.python_version(),
                    'certificate_sha256':hashlib.sha256(Path('critical_rank2_certificate.json').read_bytes()).hexdigest()})
    Path('critical-certificate-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
