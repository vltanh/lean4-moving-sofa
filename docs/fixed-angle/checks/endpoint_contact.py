"""Regular endpoint certificate with h=w-c as the external parameter."""
import math
from interval_contact import I,AD,down,up
from jet_contact import Jet,dot
from contact_core import events,shooting,step,flags_between,sn,cs
ORDER=['0','dc','a','db','m','b','za','c','w']

def endpoint_events(w,phi,b,h):
    ev=events(w,phi,b,w-h);ev['dc']=h;return ev

def endpoint_shoot(h,z,cls=None):
    if cls is not None:
        xx=[cls(v,[int(i==j) for i in range(4)]) for j,v in enumerate(z)]
        hh=cls(h,[0,0,0,1])
    else:xx=z;hh=h
    phi,b,w=xx
    data=shooting(w,phi,b,w-hh,ORDER,endpoint_events(w,phi,b,hh))
    f,p0,g0,states=data
    # On [c,w] both C and B vanish. Use the exact harmonic floor formula.
    floor=2*cs(w-hh/2)*sn(hh/2)+(p0-g0)*cs(w)
    return [f[0],f[1],floor],p0,g0,states

def endpoint_residual(z,h):return endpoint_shoot(h,z)[0]

def endpoint_certificate(hlo,hhi,center,radii,Y,geometry=True):
    H=I(hlo,hhi);hm=(hlo+hhi)/2
    X=[I(down(c-r),up(c+r)) for c,r in zip(center,radii)]
    phi,b,W=X
    if not(0<=H.lo and H.hi<=I.exact_rational(1,32).lo and H.hi<phi.lo and 0<phi.lo and phi.hi<=I.exact_rational(1,12).lo and W.lo>1.5 and W.hi<I.exact_rational(8,5).lo and b.lo>W.hi/2 and b.hi<(I(W.lo)-I(phi.hi)).lo):
        return {'ok':False,'reason':'ordering'}
    Delta=[X[j]-I(center[j]) for j in range(3)]+[H-I(hm)]
    full=endpoint_shoot(H,X,Jet);base=endpoint_shoot(I(hm),[I(c) for c in center],AD)
    f,f0=full[0],base[0]
    E=[[None]*3 for _ in range(3)];corr=[]
    for i in range(3):
        corr.append(-dot(Y[i],[z.val for z in f0])-dot(Y[i],[z.grad[3] for z in f0])*Delta[3]-dot(Y[i],[z.hess[3][3] for z in f])*Delta[3]*Delta[3]/2)
        for j in range(3):
            v=I(int(i==j))-dot(Y[i],[z.grad[j] for z in f0])
            for r in range(4):v-=dot(Y[i],[z.hess[j][r] for z in f])*Delta[r]
            E[i][j]=v
    good=True;ratios=[];cn=[]
    for i in range(3):
        ki=corr[i]+sum((E[i][j]*Delta[j] for j in range(3)),I(0))
        left=(I(center[i])-I(X[i].lo)).lo;right=(I(X[i].hi)-I(center[i])).lo
        good=good and ki.lo>-left and ki.hi<right
        ratios.append(max(-ki.lo/left,ki.hi/right))
        cn.append(sum((I(E[i][j].mag())*I(radii[j])/I(radii[i]) for j in range(3)),I(0)).hi)
    good=good and max(cn)<1
    ans={'ok':bool(good),'ratio':max(ratios),'contraction':max(cn)}
    if not good or not geometry:return ans
    def centered(z,z0):return z0.val+sum((z.grad[i]*Delta[i] for i in range(4)),I(0))
    p0=centered(full[1],base[1]);g0=centered(full[2],base[2]);d=g0-p0
    if not(p0.lo>1 and p0.hi<I.exact_rational(5,3).lo and d.lo>.5 and d.hi<1):
        return dict(ans,ok=False,reason='endpoints',p0=repr(p0),d=repr(d))
    ev=endpoint_events(W,phi,b,H)
    states={key:tuple(centered(z,z0) for z,z0 in zip(st,base[3][key])) for key,st in full[3].items()}
    maxsecond=-math.inf
    for j,(lo,hi) in enumerate(zip(ORDER,ORDER[1:])):
        flags=flags_between(ORDER,j);C,B,D=flags;length=ev[hi]-ev[lo]
        for m in range(20):
            hh=length*I(m/20,(m+1)/20)
            ff,gg,pp,dd=step(states[lo],hh,flags);t=ev[lo]+hh
            truep=pp+p0*t.cos();rp=(C*(gg-1)+B)/(1+B)
            maxsecond=max(maxsecond,(rp-truep).hi)
    ans.update(max_p_second=maxsecond,max_p0=p0.hi,max_d=d.hi)
    ans['ok']=maxsecond<0
    if not ans['ok']:ans['reason']='curvature'
    return ans
