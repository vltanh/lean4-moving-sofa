"""Local regression tests; analytic and interval proofs are separate."""
import math
import unittest
import numpy as np
from numpy.polynomial.legendre import leggauss
from reverse_exact import ReverseSofa, width_majorant, asymptotic_constant


def functional(e, t, weights, C, Cp, endpoints):
    phi = t+e/2
    n1 = np.column_stack((np.sin(phi), np.cos(phi)))
    n2 = np.column_stack((np.sin(e-phi), -np.cos(e-phi)))
    dn1 = np.column_stack((np.cos(phi), -np.sin(phi)))
    dn2 = np.column_stack((-np.cos(e-phi), -np.sin(e-phi)))
    hp = 1+np.einsum('ij,ij->i', n1, C)
    hm = 1+np.einsum('ij,ij->i', n2, C)
    dp = np.einsum('ij,ij->i', dn1, C)+np.einsum('ij,ij->i', n1, Cp)
    dm = np.einsum('ij,ij->i', dn2, C)+np.einsum('ij,ij->i', n2, Cp)
    start, end = endpoints
    Hplus = 1+math.sin(e)*end[0]+math.cos(e)*end[1]
    Hminus = 1+math.sin(e)*start[0]-math.cos(e)*start[1]
    cap = .5*np.dot(weights, hp*hp-dp*dp+hm*hm-dm*dm)
    cap += (Hplus*Hminus+.5*math.cos(2*e)*(Hplus*Hplus+Hminus*Hminus))/math.sin(2*e)
    return cap-np.dot(weights, C[:,0]*Cp[:,1])


def clip(poly, normal, rhs):
    result = []
    if not len(poly):
        return np.empty((0,2))
    old = poly[-1]
    d0 = old@normal-rhs
    for new in poly:
        d1 = new@normal-rhs
        if (d0<=0) != (d1<=0):
            result.append(old+(new-old)*d0/(d0-d1))
        if d1<=0:
            result.append(new)
        old, d0 = new, d1
    return np.asarray(result).reshape(-1,2)


def polygon_area(poly):
    if len(poly)<3:
        return 0.
    return abs(np.dot(poly[:,0],np.roll(poly[:,1],-1))-np.dot(poly[:,1],np.roll(poly[:,0],-1)))/2


class ReverseExactTests(unittest.TestCase):
    def test_endpoints_and_symmetry(self):
        for deg in (1,10,30,43,45,60,80,89):
            sofa = ReverseSofa(math.radians(deg))
            x,y,*_ = sofa.corner(np.linspace(-sofa.epsilon/2,sofa.epsilon/2,101))
            np.testing.assert_allclose(x,x[::-1],atol=1e-12)
            np.testing.assert_allclose(y,-y[::-1],atol=1e-12)
            np.testing.assert_allclose([x[0],x[-1],y[0],y[-1]],[0,0,-.5,.5],atol=2e-12)

    def test_support_and_terminal_contact(self):
        for deg in (1,30,43,60,80,89):
            e=math.radians(deg);sofa=ReverseSofa(e)
            p=np.linspace(0,e,101);x,y,xd,yd,*_=sofa.corner(p-e/2)
            h,dh,rho=sofa.support(p)
            np.testing.assert_allclose(h,1+x*np.sin(p)+y*np.cos(p),atol=2e-12)
            self.assertAlmostEqual(h[0],.5,places=12)
            self.assertAlmostEqual(h[-1]*math.cos(e)-dh[-1]*math.sin(e),0,places=11)
            self.assertAlmostEqual(yd[-1],math.sin(e)*rho[-1],places=10)

    def test_shape_inequality_diagnostics(self):
        for deg in (1,10,30,43,45,60,80,89):
            e=math.radians(deg);sofa=ReverseSofa(e)
            p=np.linspace(0,e,301);x,y,xd,yd,xdd,ydd=sofa.corner(p-e/2)
            self.assertGreater(np.min(yd),0)
            self.assertGreater(np.min(xdd*yd-xd*ydd),0)
            self.assertGreater(np.min(sofa.support(p)[2]),0)
            self.assertGreater(np.min(xd*np.sin(p)+yd*np.cos(p)),0)
            self.assertLess(np.max(xd*np.sin(e-p)-yd*np.cos(e-p)),0)

    def test_value_against_independent_quadrature(self):
        ts,ws=leggauss(180)
        for deg in (1,10,30,43,60,80):
            e=math.radians(deg);sofa=ReverseSofa(e);t=ts*e/2;w=ws*e/2
            x,y,xd,yd,*_=sofa.corner(t)
            q=functional(e,t,w,np.c_[x,y],np.c_[xd,yd],((0,-.5),(0,.5)))
            self.assertAlmostEqual(q,sofa.area(),delta=3e-10)

    def test_asymmetric_and_endpoint_variations(self):
        ts,ws=leggauss(140)
        rng=np.random.default_rng(813)
        for deg in (10,30,45,60,80):
            e=math.radians(deg);sofa=ReverseSofa(e);t=ts*e/2;w=ws*e/2
            x,y,xd,yd,*_=sofa.corner(t);C=np.c_[x,y];Cp=np.c_[xd,yd]
            for _ in range(8):
                a,b,c,d=rng.normal(size=4)
                # Includes a freely varying antisymmetric endpoint abscissa.
                v=np.c_[a*ts+b*(1-ts*ts),c*(1-ts*ts)+d*ts*(1-ts*ts)]
                vp=np.c_[a-2*b*ts,-2*c*ts+d*(1-3*ts*ts)]*2/e
                delta=.01
                qp=functional(e,t,w,C+delta*v,Cp+delta*vp,((-delta*a,-.5),(delta*a,.5)))
                qm=functional(e,t,w,C-delta*v,Cp-delta*vp,((delta*a,-.5),(-delta*a,.5)))
                self.assertLess(max(qp,qm),sofa.area())
                self.assertAlmostEqual(qp,qm,delta=1e-10)

    def test_width_majorant_endpoints(self):
        for deg in (1,10,30,43,60):
            e=math.radians(deg);value=ReverseSofa(e).area()
            self.assertAlmostEqual(width_majorant(e,1),value,delta=2e-11)
            for width in np.linspace(0,1,81):
                bound=min(width_majorant(e,width),width/math.sin(e/2))
                self.assertLessEqual(bound,value+2e-11)

    def test_whole_polygon_collision_audit(self):
        for deg in (10,30,43,60,80):
            e=math.radians(deg);sofa=ReverseSofa(e);poly=sofa.polygon(129)
            for p in np.linspace(0,e,65):
                x,y,*_=sofa.corner(p-e/2);corner=np.array([x,y])
                n1=np.array([math.sin(p),math.cos(p)])
                n2=np.array([math.sin(e-p),-math.cos(e-p)])
                self.assertLessEqual(np.max((poly-corner)@n1),1+2e-12)
                self.assertLessEqual(np.max((poly-corner)@n2),1+2e-12)
                wedge=clip(clip(poly,n1,n1@corner),n2,n2@corner)
                self.assertLess(polygon_area(wedge),2e-12)
            self.assertLess(polygon_area(poly),sofa.area())

    def test_corner_derivatives_against_finite_differences(self):
        for deg in (10,30,60,80):
            e=math.radians(deg);sofa=ReverseSofa(e)
            t=np.linspace(-e*.4,e*.4,25);dt=1e-6
            base=sofa.corner(t);plus=sofa.corner(t+dt);minus=sofa.corner(t-dt)
            for original,derivative in ((0,2),(1,3),(2,4),(3,5)):
                np.testing.assert_allclose((plus[original]-minus[original])/(2*dt),
                                           base[derivative],rtol=2e-7,atol=2e-8)

    def test_variable_width_against_independent_quadrature(self):
        ts,ww=leggauss(140)
        for deg in (10,30,43,60):
            e=math.radians(deg);z=ReverseSofa(e).constants
            s,c,k,K,r,z0=[z[n] for n in ('s','c','k','K','r','z0')]
            t=ts*e/2;weights=ww*e/2
            for width in (.1,.5,.9):
                l=1-width/2
                B=-(l-z['a']/z['m'])/(s*z['denominator'])
                A=(l*c+r*B*math.sin(K))/s
                zx=z0+A*np.cos(t)+B*np.cos(k*t)
                zy=A*np.sin(t)-r*B*np.sin(k*t)
                zxp=-A*np.sin(t)-B*k*np.sin(k*t)
                zyp=A*np.cos(t)-r*B*k*np.cos(k*t)
                C=np.c_[np.cos(t)*zx+np.sin(t)*zy,-np.sin(t)*zx+np.cos(t)*zy]
                Cp=np.c_[np.cos(t)*(zxp+zy)+np.sin(t)*(zyp-zx),
                         -np.sin(t)*(zxp+zy)+np.cos(t)*(zyp-zx)]
                value=functional(e,t,weights,C,Cp,((0,-l),(0,l)))+(1-width)**2/math.tan(e)
                self.assertAlmostEqual(value,width_majorant(e,width),delta=2e-10)

    def test_free_endpoint_jacobi_coefficient(self):
        ts,ww=leggauss(140)
        for deg in (10,30,43,60,80):
            e=math.radians(deg);sofa=ReverseSofa(e);z=sofa.constants
            s,c,k,K,r,d=[z[n] for n in ('s','c','k','K','r','d')]
            t=ts*e/2;weights=ww*e/2
            den=c*math.sin(K)+r*s*math.cos(K)
            T=-1/den;P=s*(math.sin(K)-z['eta']*math.cos(K))/den
            vx=P*np.sin(t)+T*np.sin(k*t);vy=-P*np.cos(t)+r*T*np.cos(k*t)
            vxp=P*np.cos(t)+T*k*np.cos(k*t);vyp=P*np.sin(t)-r*T*k*np.sin(k*t)
            v=np.c_[np.cos(t)*vx+np.sin(t)*vy,-np.sin(t)*vx+np.cos(t)*vy]
            vp=np.c_[np.cos(t)*(vxp+vy)+np.sin(t)*(vyp-vx),
                     -np.sin(t)*(vxp+vy)+np.cos(t)*(vyp-vx)]
            x,y,xd,yd,*_=sofa.corner(t)
            value=functional(e,t,weights,np.c_[x,y]+v,np.c_[xd,yd]+vp,((1,-.5),(-1,.5)))
            E=math.sin(e)/d*((2*d-1)*math.sin(K)-z['eta']*(2*d+1)*math.cos(K))
            E/=((1+d)*math.sin(K)+z['eta']*(1-d)*math.cos(K))
            self.assertLess(E,0)
            self.assertAlmostEqual(value-sofa.area(),E,delta=1e-10)

    def test_asymptotic_constant(self):
        constant=asymptotic_constant()
        self.assertAlmostEqual(constant,1.3565337324523,places=12)
        errors=[]
        for e in (.04,.02,.01):
            errors.append(abs(e*ReverseSofa(e).area()-constant))
        self.assertLess(errors[1],.26*errors[0])
        self.assertLess(errors[2],.26*errors[1])

    def test_invalid_arguments(self):
        for e in (0,-1,math.pi/2,math.inf,math.nan):
            with self.assertRaises(ValueError): ReverseSofa(e)
        with self.assertRaises(ValueError): ReverseSofa(.3).support(-.1)
        with self.assertRaises(ValueError): ReverseSofa(.3).corner(.2)
        with self.assertRaises(ValueError): width_majorant(.3,1.1)


if __name__ == '__main__':
    unittest.main()
