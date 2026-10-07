"""Verify a supplied nonnegative piecewise-affine kernel dual exactly.

No optimizer is used by this verifier. Its mathematical scope is the stated
positive-kernel relaxation, not an unproved geometric premise.
"""
from fractions import Fraction as F
from bisect import bisect_right
from reverse_kernel_interval import I,trig,S


def rationalize(proposal,places=12):
    """Candidate conversion only; verify_box decides mathematical acceptance."""
    return dict(e=str(F(str(proposal['e']))),u=proposal['u'],knots=proposal['knots'],
                lam=[str(max(F(0),F(round(x*10**places),10**places))) for x in proposal['lam']],
                eta=str(F(round(proposal['eta']*10**places),10**places)))


class Family:
    def __init__(self,e,knots,values):
        self.e=e;self.knots=knots;self.values=values
        self.slopes=[(values[2*j+1]-values[2*j])/(h-l) for j,(l,h) in enumerate(zip(knots[:-1],knots[1:]))]
        self.C=[I.cast(0)];self.D=[I.cast(0)]
        self.trig=[trig(e*t) for t in knots]
        for j in range(len(knots)-1):
            c,d=self.increment(j,knots[j+1]);self.C.append(self.C[-1]+c);self.D.append(self.D[-1]+d)
    def val(self,j,t):return self.values[2*j]+self.slopes[j]*(t-self.knots[j])
    def increment(self,j,t):
        l=self.knots[j];v=self.val(j,t);vl=self.values[2*j];slope=self.slopes[j]
        st,ct=trig(self.e*t);sl,cl=self.trig[j]
        return v*st-vl*sl+(slope/self.e)*(ct-cl),-v*ct+vl*cl+(slope/self.e)*(st-sl)
    def integrals(self,t):
        if t==1:return self.C[-1],self.D[-1]
        j=bisect_right(self.knots,t)-1
        c,d=self.increment(j,t)
        return self.C[j]+c,self.D[j]+d


def verify_point(record,subdivisions=8):
    e=F(record['e']);u=None if record['u'] is None else F(record['u'])
    knots=list(map(F,record['knots']));lam=list(map(F,record['lam']));eta=F(record['eta'])
    if not F(57,50)<=e<=F(15708,10000):raise ValueError('point e outside certificate domain')
    if u is not None and not 0<=u<=F(1,2):raise ValueError('target u outside first half')
    if isinstance(subdivisions,bool) or not isinstance(subdivisions,int) or subdivisions<1:raise ValueError('positive subdivisions required')
    if len(knots)<2 or knots[0]!=0 or knots[-1]!=1 or any(a>=b for a,b in zip(knots[:-1],knots[1:])):raise ValueError('invalid partition')
    if knots!=[1-x for x in reversed(knots)]:raise ValueError('partition must be symmetric')
    if u is not None and (u not in knots or 1-u not in knots):raise ValueError('target breakpoints missing')
    n=len(knots)-1
    if len(lam)!=4*n or min(lam)<0:raise ValueError('invalid nonnegative affine weights')
    p=Family(e,knots,lam[:2*n]);m=Family(e,knots,lam[2*n:]);families=[p,m]
    _,d=trig(e)
    if d.lo<0:raise ValueError('point must have nonnegative cosine')
    R=1/(1-d);c=R/2;cb=c.upper();db=d.upper()
    mass=sum((knots[j+1]-knots[j])*(lam[2*j]+lam[2*j+1]+lam[2*n+2*j]+lam[2*n+2*j+1])/2 for j in range(n))
    eps=F(0)
    for side in range(2):
        own,other=families[side],families[1-side]
        for j,(l,h) in enumerate(zip(knots[:-1],knots[1:])):
            jo=n-1-j
            mx=max(own.values[2*j:2*j+2]);mo=max(other.values[2*jo:2*jo+2])
            M=e**3*(1+abs(eta)+cb*mass)+cb*e*e*(mx+2*db*mo)+cb*e*abs(other.slopes[jo])
            delta=(h-l)/subdivisions
            max_endpoint=None
            for k in range(subdivisions+1):
                t=l+(h-l)*F(k,subdivisions);si,co=trig(e*t)
                C,D=own.integrals(t);Cc,Dc=other.integrals(1-t)
                kernel=si*C-co*D+si*(other.C[-1]-Cc)+co*(other.D[-1]-Dc)
                f=I.cast(0)
                if u is None:
                    if side==0:f=e*si
                elif side==0 and (l+h)/2>=u:
                    f=e*trig(e*(t+1-u))[0]
                elif side==1 and (l+h)/2>=1-u:
                    f=e*trig(e*(t-1+u))[0]
                res=f-own.val(j,t)-c*kernel-eta*e*si
                max_endpoint=res.upper() if max_endpoint is None else max(max_endpoint,res.upper())
            eps=max(eps,max_endpoint+M*delta*delta/8)
    cost=R.upper()*(mass+2*eps)+(eta if eta>=0 else F(983,1000)*eta)
    return dict(e=e,u=u,mass=mass,eta=eta,epsilon=eps,cost=cost)


def verify_box(record,elo,ehi,ulo=None,uhi=None,subdivisions=8):
    elo,ehi=F(elo),F(ehi)
    p=verify_point(record,subdivisions)
    if not F(57,50)<=elo<=p['e']<=ehi<=F(15708,10000):raise ValueError('invalid e box')
    if p['u'] is None:
        if ulo is not None or uhi is not None:raise ValueError('moment box has no u')
        du=F(0);target=F(86,100)
    else:
        ulo,uhi=F(ulo),F(uhi)
        if not 0<=ulo<=p['u']<=uhi<=F(1,2):raise ValueError('invalid target box')
        du=max(p['u']-ulo,uhi-p['u'])
        # The theorem restricts the last rational enclosure to e<=pi/2.
        # Thus cos(e)>=0 even if ehi exceeds pi/2 by a tiny amount.
        target=1+max(F(0),trig(ehi)[1].lower())
    de=max(p['e']-elo,ehi-p['e']);E=ehi
    Rmax=1/(1-trig(elo)[1].upper());cmax=Rmax/2
    kerlip=cmax*(1+2*E)+E*Rmax*Rmax/2
    L=1+2*E+kerlip*p['mass']+abs(p['eta'])*(1+E)
    eps=p['epsilon']+L*de
    cost=Rmax*(p['mass']+2*eps)+(p['eta'] if p['eta']>=0 else F(983,1000)*p['eta'])+Rmax*E*(1+2*E)*du
    margin=target-cost
    return dict(e=[str(elo),str(ehi)],u=None if p['u'] is None else [str(ulo),str(uhi)],
                margin=str(margin),point_epsilon=str(p['epsilon']),mass=str(p['mass']),
                point_cost=str(p['cost']),lipschitz_e=str(L),accepted=margin>0)
