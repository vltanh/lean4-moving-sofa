# An exact safe-strip bridge for the reference-scale hull class

**Scope.** This connects the two uploaded ideas on one specified class. For hulls congruent to k K_* with 63/64<=k<=1, every conventional partial-turn pair has a safe bridge to full turns. The minimum-width slack theorem SM1 then gives a sharp ordinary-area bound with an explicit positive margin when k<1. This does not prove a bridge or area bound for arbitrary hulls. Labels SB are local.

The proof uses only the explicit reference support, its contained face rectangle, and the existing same-body strip-transport lemma SI. No numerical width samples are used.

## 1. The complete set of safe strip directions

Write L=pi/2, s=1-k, m=1/(3 sin beta), beta=arctan Y, with 2/7<Y<3/10. In reference coordinates K_* has top/bottom faces [-m/2,m/2] at heights one/zero. The hull K_s=kK_*+(0,s) has minimum vertical width k, as proved in SM Section 1.

Let delta in [0,L] be the angular distance of a normal from the vertical direction, modulo pi. For 0<=delta<=beta, the exact circular-phase support, together with the reflection symmetries, gives

$$w_{K_*}(L\pm\delta)=1+m\sin\delta.$$

For beta<=delta<=L, the contained m-by-one rectangle gives

$$w_{K_*}(L\pm\delta)\ge m\sin\delta+\cos\delta.$$

This last expression is concave and positive on [beta,L], so its minimum there is at an endpoint. At delta=L its value is m>10/9. At delta=beta its value is 1/3+cos beta>1/3+9/10>10/9. The elementary bound cos beta>9/10 follows by squaring from Y<3/10.

Since k>=63/64,

$$k\,(10/9)\ge35/32>1.$$

Therefore no direction at distance at least beta from vertical is a safe unit-strip normal. Within beta, width is exactly k(1+m sin delta). Define

$$\eta_s=\arcsin\left(\frac{s}{km}\right).$$

This lies in [0,beta): s/(km)<=1/70, while sin beta>1/4. Consequently the entire safe set, modulo pi, is exactly

$$\boxed{\{\theta:w_{K_s}(\theta)\le1\}=[L-\eta_s,L+\eta_s]\pmod\pi.} \tag{SB.1}$$

In particular there is a single safe component on the projective direction circle. It is a singleton when s=0. This is a proved interval, not inference from three safe samples.

## 2. Conventional partial motions have their outgoing normals in that interval

Let S have actual convex hull congruent to K_s and two conventional reduced partial-turn witnesses from one common incoming normal. Work in the reference coordinates after undoing that congruence. Its incoming strip normal theta0 belongs to the interval in SB.1; choose its lift there. Put delta0=theta0-L.

In coordinates relative to the given incoming orientation, the lower and upper outgoing strip normals are alpha and pi-gamma, with 0<alpha,gamma<=L. In the reference coordinates their lifts lie in [delta0,delta0+pi], on opposite sides of theta0, and both are safe strip directions.

Because |delta0|<=eta_s<beta<pi/4, the only translate of the safe interval meeting this entire angular range is the one centered at L. The two outgoing normals and theta0 therefore lie in one common connected safe interval. Every direction between the outgoing normals has width at most one.

SI3 supplies both complete conventional turns of the same S after changing its incoming direction. SI2 transports those full turns along the safe component to the vertical minimum-width normal. No material is deleted, no dilation is applied, and no connected-component selection is needed. The original body and its ordinary area are unchanged.

**Theorem SB1.** Any compact connected body with actual hull congruent to k K_*, 63/64<=k<=1, and two conventional partial-turn witnesses has two full-turn witnesses in the reference minimum-width orientation.

For a statement covering arbitrary original motion signs, the earlier competitive conventional-motion reduction would be an additional input. The theorem here retains its stated conventional-witness premise rather than silently importing it.

## 3. The ordinary-area consequence

After the same-body transport, canonical tightening gives S subset E_full(K_s). SM1 proves

$$\boxed{|S|\le M-\Gamma(s)\le M-\frac83s^{3/2},\qquad s=1-k,}$$

$$\Gamma(s)=(1+s)^2\arctan\sqrt{s}-(1-s)\sqrt{s}.$$

Thus within this reference-scale actual-hull class, partial-turn completion and the sharp area comparison are both established by hand. At s=0 this gives the reference bound; at s>0 it has a strict margin. The result concerns every body with the stated actual hull and motions, not only the particular numerical construction in the upload.

There is no claim that arbitrary full-turn or partial-turn competitors have hulls in this class. Rotations and uniform scales of K_* do not describe a complete neighborhood of the reference: asymmetric support changes, altered faces and middle facets remain outside it. The global missing comparison is not discharged by this restricted bridge.

The general CC completion allowance remains necessary for partial-turn hulls with genuinely disconnected safe-strip components or an unsafe interval between the two outgoing normals. SB.1 verifies that obstruction is absent here, so this proof does not need to compare the cubic allowance to the three-halves margin or assume a relation between a missing angle and s.

All steps are pen-and-paper consequences of the displayed exact support data and prior SI/SM statements, with their self-review limitations retained. No CI, Lean/Lake compilation, dependency installation, manuscript build or numerical search was used.