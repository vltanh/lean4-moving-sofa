"""Second-order centered interval enclosures for the contact residual."""
import math
from interval_contact import I,AD,all_orders,down,up
from contact_core import events,shooting,step,flags_between

class Jet(AD):
    __slots__=('hess',)
    def __init__(self,val,grad=None,hess=None):
        if isinstance(val,Jet):
            self.val,self.grad,self.hess=val.val,val.grad,val.hess; return
        self.val=I(val)
        self.grad=tuple(I(0) for _ in range(4)) if grad is None else tuple(I(g) for g in grad)
        self.hess=tuple(tuple(I(0) for _ in range(4)) for _ in range(4)) if hess is None else tuple(tuple(I(h) for h in row) for row in hess)
    def __add__(a,b):
        b=Jet(b)
        return Jet(a.val+b.val,[x+y for x,y in zip(a.grad,b.grad)],[[a.hess[i][j]+b.hess[i][j] for j in range(4)] for i in range(4)])
    __radd__=__add__
    def __neg__(a):return Jet(-a.val,[-g for g in a.grad],[[-h for h in row] for row in a.hess])
    def __sub__(a,b):return a+-Jet(b)
    def __rsub__(a,b):return Jet(b)+-a
    def __mul__(a,b):
        b=Jet(b)
        return Jet(a.val*b.val,[a.grad[i]*b.val+a.val*b.grad[i] for i in range(4)],[[a.hess[i][j]*b.val+a.val*b.hess[i][j]+a.grad[i]*b.grad[j]+b.grad[i]*a.grad[j] for j in range(4)] for i in range(4)])
    __rmul__=__mul__
    def recip(a):
        iv=1/a.val; iv2=iv*iv; iv3=iv2*iv
        return Jet(iv,[-g*iv2 for g in a.grad],[[2*a.grad[i]*a.grad[j]*iv3-a.hess[i][j]*iv2 for j in range(4)] for i in range(4)])
    def __truediv__(a,b):return a*Jet(b).recip()
    def __rtruediv__(a,b):return Jet(b)*a.recip()
    def sin(a):
        s,c=a.val.sin(),a.val.cos()
        return Jet(s,[c*g for g in a.grad],[[c*a.hess[i][j]-s*a.grad[i]*a.grad[j] for j in range(4)] for i in range(4)])
    def cos(a):
        s,c=a.val.sin(),a.val.cos()
        return Jet(c,[-s*g for g in a.grad], [[-s*a.hess[i][j]-c*a.grad[i]*a.grad[j] for j in range(4)] for i in range(4)])

def evaluate(W,X,order,cls=Jet):
    xx=[cls(v,[int(i==j) for i in range(4)]) for j,v in enumerate(X)]
    ww=cls(W,[0,0,0,1])
    return shooting(ww,*xx,order)

def dot(a,b):return sum((I(x)*y for x,y in zip(a,b)),I(0))
def hull(a,b):return a.hull(b)

def certificate(wlo,whi,center,radii,Y,geometry=True):
    W=I(wlo,whi); wm=(wlo+whi)/2
    X=[I(down(c-r),up(c+r)) for c,r in zip(center,radii)]
    if not(0<X[0].lo and X[0].hi<=I.exact_rational(1,12).lo and X[0].hi<X[1].lo and X[1].hi<X[2].lo and X[2].hi<W.lo and X[1].hi<(I(W.lo)-I(X[0].hi)).lo):
        return {'ok':False,'reason':'ordering-box'}
    orders=all_orders(W,X)
    Delta=[X[j]-I(center[j]) for j in range(3)]+[W-I(wm)]
    errors=[]; corrections=[]; data=[]; bases=[]
    for order in orders:
        full=evaluate(W,X,order); data.append(full)
        base=evaluate(I(wm),[I(c) for c in center],order,AD)
        bases.append(base)
        f=full[0]; f0=base[0]
        err=[[None]*3 for _ in range(3)]; cor=[]
        for i in range(3):
            hww=dot(Y[i],[z.hess[3][3] for z in f])
            val=-dot(Y[i],[z.val for z in f0])-dot(Y[i],[z.grad[3] for z in f0])*Delta[3]-hww*Delta[3]*Delta[3]/2
            cor.append(val)
            for j in range(3):
                v=I(int(i==j))-dot(Y[i],[z.grad[j] for z in f0])
                for r in range(4):v-=dot(Y[i],[z.hess[j][r] for z in f])*Delta[r]
                err[i][j]=v
        errors.append(err);corrections.append(cor)
    E=[[errors[0][i][j] for j in range(3)] for i in range(3)]
    corr=corrections[0]
    for e,c in zip(errors[1:],corrections[1:]):
        E=[[E[i][j].hull(e[i][j]) for j in range(3)] for i in range(3)]
        corr=[corr[i].hull(c[i]) for i in range(3)]
    good=True;ratios=[]
    for i in range(3):
        ki=corr[i]+sum((E[i][j]*Delta[j] for j in range(3)),I(0))
        left=(I(center[i])-I(X[i].lo)).lo;right=(I(X[i].hi)-I(center[i])).lo
        good=good and ki.lo>-left and ki.hi<right
        ratios.append(max(-ki.lo/left,ki.hi/right))
    cn=[]
    for i in range(3):
        cn.append(sum((I(E[i][j].mag())*I(radii[j])/I(radii[i]) for j in range(3)),I(0)).hi)
    good=good and max(cn)<1
    ans={'ok':bool(good),'ratio':max(ratios),'contraction':max(cn),'orders':len(orders)}
    if not good or not geometry:return ans
    maxsecond=-math.inf; maxp0=-math.inf; maxd=-math.inf
    def centered(z,z0):
        return z0.val+sum((z.grad[i]*Delta[i] for i in range(4)),I(0))
    for order,full,base in zip(orders,data,bases):
        pp0=centered(full[1],base[1]); gg0=centered(full[2],base[2]); dd=gg0-pp0
        maxp0=max(maxp0,pp0.hi);maxd=max(maxd,dd.hi)
        if not(pp0.lo>1 and pp0.hi<I.exact_rational(5,3).lo and dd.lo>0 and dd.hi<1):
            return dict(ans,ok=False,reason='endpoint-admissibility',p0=repr(pp0),d=repr(dd))
        ev=events(W,*X); states={key:tuple(centered(z,z0) for z,z0 in zip(st,base[3][key])) for key,st in full[3].items()}
        for j,(lo,hi) in enumerate(zip(order,order[1:])):
            flags=flags_between(order,j);C,B,D=flags; length=ev[hi]-ev[lo]
            for m in range(16):
                h=length*I(m/16,(m+1)/16)
                f,g,p,dp=step(states[lo],h,flags);t=ev[lo]+h
                truep=p+pp0*t.cos();rp=(C*(g-1)+B)/(1+B)
                maxsecond=max(maxsecond,(rp-truep).hi)
    ans.update(max_p_second=maxsecond,max_p0=maxp0,max_d=maxd)
    ans['ok']=maxsecond<0
    if not ans['ok']:ans['reason']='curvature-admissibility'
    return ans
