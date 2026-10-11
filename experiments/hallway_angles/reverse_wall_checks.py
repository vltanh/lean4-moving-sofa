"""Exact algebra checks for two neighboring reverse-wall wedges.

These test line identities and ray lengths, not existence of maximizing-cap
variations, the limit passage, or global optimality. Standard library only.
"""
from fractions import Fraction as F
import random
import unittest


def trig_half(t):
    return 2*t/(1+t*t), (1-t*t)/(1+t*t)


def pos(x): return max(F(0), x)


def exposed_length(A, B, U, V):
    """Length of [0,max(0,A,B)] outside the open interval (V,U)."""
    T=max(F(0), A, B)
    removed=max(F(0), min(T,U)-max(F(0),V))
    return T-removed


def thresholds(e_half, delta_half, aminus, sigma, bminus, bplus):
    q,d=trig_half(e_half); sd,cd=trig_half(delta_half)
    if not (q*cd-d*sd>0 and q*cd+d*sd>0):
        raise ValueError('neighboring denominators must be positive')
    aplus=aminus+sigma
    A=delta_half-aplus
    B=(1-cd+bminus*sd)/(q*cd-d*sd)
    U=-delta_half-aminus
    V=(1-cd-bplus*sd)/(q*cd+d*sd)
    return A,B,U,V


class ReverseWallChecks(unittest.TestCase):
    def test_two_neighbor_enclosure(self):
        rng=random.Random(62026)
        for _ in range(2500):
            u=F(rng.randrange(1,30),100)
            sigma=F(rng.randrange(0,101),100)
            aminus=F(rng.randrange(-200,201),100)
            B=F(rng.randrange(-200,201),100)
            V=F(rng.randrange(-200,201),100)
            U=-u-aminus; A=u-aminus-sigma
            E=exposed_length(A,B,U,V)
            self.assertLessEqual(E,pos(B)+pos(V)+pos(2*u-sigma))
            if V<=0:
                self.assertLessEqual(E,max(pos(B),pos(2*u-sigma)))
            self.assertEqual(A-U,2*u-sigma)

    def test_stationarity_scalar_solve(self):
        for H in [F(0),F(1,10),F(1,2),F(1),F(2)]:
            for L in [F(1,10),F(1),F(3)]:
                for eps in [F(0),F(1,100)]:
                    bound=max(H+eps,(H+eps+L)/2)
                    for j in range(101):
                        sigma=F(j,20)
                        if sigma <= H+pos(L-sigma)+eps:
                            self.assertLessEqual(sigma,bound)
                        if sigma <= max(H,pos(L-sigma))+eps:
                            self.assertLessEqual(sigma,max(H+eps,(L+eps)/2))

    def test_neighbor_line_identities(self):
        eh=F(2,3); ph=F(1,5); dh=F(1,100)
        q,d=trig_half(eh); sp,cp=trig_half(ph); sd,cd=trig_half(dh)
        ss=q*cp-d*sp; cs=d*cp+q*sp
        n=(sp,cp);t=(cp,-sp);m=(ss,-cs);s=(cs,ss)
        C=(F(3,7),F(-2,11));am,ap=F(-3,10),F(1,5);bm,bp=F(2,5),F(3,5)
        add=lambda x,y:tuple(a+b for a,b in zip(x,y))
        scale=lambda k,x:tuple(k*a for a in x)
        dot=lambda x,y:sum(a*b for a,b in zip(x,y))
        Pm=add(add(C,n),scale(am,t));Pp=add(add(C,n),scale(ap,t))
        Qm=add(add(C,m),scale(bm,s));Qp=add(add(C,m),scale(bp,s))
        np=add(scale(cd,n),scale(sd,t));nm=add(scale(cd,n),scale(-sd,t))
        mp=add(scale(cd,m),scale(-sd,s));mm=add(scale(cd,m),scale(sd,s))
        for r in [F(0),F(1,20),F(1,3),F(2)]:
            point=add(C,scale(-r,t))
            self.assertEqual(dot(np,point)-(dot(np,Pp)-1),sd*(dh-ap-r))
            self.assertEqual(dot(nm,point)-(dot(nm,Pm)-1),sd*(dh+am+r))
            self.assertEqual(dot(mp,point)-(dot(mp,Qm)-1),1-cd+bm*sd-r*(q*cd-d*sd))
            self.assertEqual(dot(mm,point)-(dot(mm,Qp)-1),1-cd-bp*sd-r*(q*cd+d*sd))

    def test_geometric_arm_constraint(self):
        for eh,ph in [(F(1,2),F(1,10)),(F(2,3),F(1,5)),(F(3,4),F(1,4))]:
            q,d=trig_half(eh);sp,cp=trig_half(ph)
            ss,cs=q*cp-d*sp,d*cp+q*sp
            for a,b in [(F(-1,4),F(1)),(F(1,2),F(3,4)),(F(1),F(-1,3))]:
                upper_lower_height=cp+cs-a*sp-b*ss
                bigA=1+d;fgap=bigA-q*a;ggap=bigA-q*b
                self.assertEqual(sp*fgap+ss*ggap,q*upper_lower_height)

    def test_negative_excursion_endpoints_exact(self):
        q,d=F(99,101),F(20,101); A0=F(37,33)
        sl,cl=trig_half(F(33,148))
        self.assertEqual(q*q+d*d,1)
        self.assertEqual(A0,(2+d)/(2*q))
        self.assertEqual((sl,cl),(F(9768,22993),F(20815,22993)))
        self.assertEqual(A0*(1-cl)-sl/4,0)
        self.assertEqual(A0*sl-cl/4,F(1,4))
        self.assertEqual(1+d-q*q/4,F(39083,40804))
        self.assertLess(1+d-q*q/4,1)
        self.assertGreater(1+d-q*q/4-(1-cl)/2,0)
        self.assertLess(F(33,148),q/(1+d))

    def test_negative_excursion_differential_identities_exact(self):
        q,d=F(99,101),F(20,101); A0=F(37,33)
        for j in range(101):
            half=F(33,148)*j/100; st,ct=trig_half(half)
            a=A0*(1-ct)-st/4; da=A0*st-ct/4; dda=A0*ct+st/4
            b=q*(da+F(1,2))+d*a; db=q*dda+d*da
            self.assertEqual(da,F(1,2)-1-d*a/q+b/q)
            self.assertEqual(db,1-a/q+d*b/q)
            self.assertGreater(b,0)
            if 0<j<100:self.assertLess(a,0)
            self.assertLessEqual(a,(1+d)/q)
            self.assertLessEqual(b,(1+d)/q)

    def test_tangent_strip_identity(self):
        for eh,ph in [(F(3,4),F(1,5)),(F(3,4),F(1,2))]:
            q,d=trig_half(eh);sp,cp=trig_half(ph)
            ss,cs=q*cp-d*sp,d*cp+q*sp
            sin_two_phi_minus_e=2*sp*cp*d-(cp*cp-sp*sp)*q
            self.assertEqual(sp*sp-ss*ss,q*sin_two_phi_minus_e)

    def test_affine_majorant_when_lower_arm_bound_holds(self):
        for eh in [F(3,5),F(2,3),F(3,4),F(9,10)]:
            q,d=trig_half(eh); A=1+d
            low=-q/A;high=A/q
            for j in range(501):
                b=low+(high-low)*j/500
                rho=F(0) if b<=0 else max(F(1,2),b/q)
                self.assertLessEqual(rho,F(1,2)+A*b/(2*q))


if __name__=='__main__':
    unittest.main(verbosity=2)
