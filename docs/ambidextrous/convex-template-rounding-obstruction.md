# Every diameter-one convex-template rounding decreases reference area to first order

**Purpose.** PV provides actual-body variations valid for full and partial turns. This note checks whether that entire family could supply the missing area-improving operation. At the reference, all of its classical first variations are uniformly negative. The same is true for sufficiently small prescribed tip cuts of the reference. This prunes this particular route; it is not a counterexample to optimality or a disproof of all possible geometric variations. Labels RT are local.

The inputs are the explicit reference arcs and their three contact phases from Note 14. Neither weighted optimality, the unrestricted value, nor a numerical perimeter estimate is used in the proof.

## 1. A perimeter bound from the explicit arcs

Write Y=tan(beta), L=pi/2 and b=L-beta. In the reference middle phase beta<=t<=b, p<=0<=q obey

$$p'=-(1+q)/2,\qquad q'=-(1-p)/2.$$

At the phase endpoints (p,q)=(0,z) and (-z,0), where

$$z=\frac{1}{2Y}-1>0.$$

Put x=1-p, y=1+q. The orbit has x^2+y^2=1+(1+z)^2, and lies on the positive-quadrant circular arc between (1,1+z) and (1+z,1). On that arc x+y>=2+z. Therefore

$$p^2+q^2=x^2+y^2-2(x+y)+2\le z^2.$$

The reference corner-arc length C thus satisfies

$$C=\int_\beta^b\sqrt{p^2+q^2}\,dt\le(L-2\beta)z.\tag{RT.1}$$

Let L_c be the sum of the two upper open-quarter outer arc lengths. The two corresponding inner tangencies have lengths

$$\int_0^b(1-\rho_g)dt+\int_\beta^L(1-\rho_f)dt=2b-L_c.$$

Here the reference first density vanishes before beta and the second after b; on the retained tangencies the densities are at most one. The lower niche boundary consists of these two tangencies and the middle corner arc. The actual sofa has two reflected niche boundaries and two copies of the outer arcs. Its full perimeter is consequently

$$P(\Sigma)=2L_c+2(2b-L_c+C)=4b+2C.$$

The actual horizontal hull faces are not added to this perimeter: except for their endpoints their interiors are absent from the sofa. Combining with RT.1 gives

$$\boxed{P(\Sigma)\le\pi+\frac{\pi/2-2\beta}{Y}.}\tag{RT.2}$$

This uses actual boundary arcs, not the larger finite staircase source-length measure from the weighted proof.

## 2. An explicit strict margin

The reference area is M=1/Y-2+beta, equivalently 1+4Y^2+beta by the defining cubic. Its elementary bounds are

$$149/500<Y<3/10,\qquad \beta>Y-Y^3/3>289/1000,\qquad\pi<22/7.$$

The cubic is increasing and has the indicated signs at the rational endpoints; the arctangent inequality follows by integrating 1/(1+t^2)>1-t^2. Using those bounds in 4M minus the right side of RT.2 gives

$$
4M-P(\Sigma)
>\frac{4-11/7+2(289/1000)}{3/10}-8+4(289/1000)-22/7
=\frac{92}{2625}>0.\tag{RT.3}
$$

No decimal approximation of perimeter is required.

## 3. All convex templates are covered simultaneously

The reference is invariant under a half turn about its center. Its arc-length measure of outward normals is therefore even. For any nonempty compact convex C with diameter at most one,

$$
P_C(\Sigma)=\frac12\int_{\partial\Sigma}
[h_C(n)+h_C(-n)]\,ds
\le\frac12P(\Sigma),
$$

since the bracket is a directional width of C and is at most one. This includes every such C, not only disks, segments, or a sampled list of polygons.

By the ordinary parallel-body first variation on this piecewise smooth reference and PV's scaling,

$$
\left.\frac{d}{dt}\left|\frac{\Sigma+tC}{1+t}\right|\right|_{0+}
=P_C(\Sigma)-2M
<-\frac{46}{2625}.\tag{RT.4}
$$

Thus every fixed template initially loses area, with a uniform bound on its first-order coefficient. This is not a claim of one uniform finite step size for all convex C, nor that a larger finite step could never behave differently. It rules out the hoped-for positive infinitesimal variation in this family.

## 4. The obstruction persists on asymmetric tip-cut families

Take the explicit double-tip cuts from MCA,

$$S_\tau=\Sigma\cap\{\tau(x+m/2)\le y\le1-\tau(x+m/2)\},\qquad\tau>0,$$

with m the reference face length. They are actual connected full-turn bodies for sufficiently small tau, because their vertical fibers retain the midline. Their areas tend to M. The only removed boundary pieces are near the four affected tip neighborhoods. Each removed circular arc and each new cut segment has length O(sqrt(tau)); the unchanged arcs retain their normals.

Normalize any template C by translating one of its points to zero. Its diameter bound gives |h_C|<=1. Hence the difference of the two anisotropic perimeter integrals is bounded uniformly in C by the total lengths of removed and newly introduced boundary pieces:

$$\sup_{\operatorname{diam}C\le1}|P_C(S_\tau)-P_C(\Sigma)|=O(\sqrt\tau).$$

The normalization does not change the integral, as the total boundary normal is zero. Together with area convergence and RT.4, this gives, for all sufficiently small tau and all such templates,

$$P_C(S_\tau)-2|S_\tau|<-23/2625.$$

These cut bodies need not be global maximizers, and this statement is not their sharp area calculation. It shows that the whole convex-template family fails to offer a first-order improvement even on these known suboptimal asymmetric near-reference examples. Satisfying PV's infinitesimal conditions therefore cannot be treated as identifying the optimum.

## 6. Discovery and scope

A bounded diagnostic sampled the explicit arcs at two prescribed resolutions and tested a disk, seven segment directions, and seven equilateral-triangle directions. All sampled first variations were negative. It used no optimizer or angle-coverage certificate. RT.1--RT.4 replace those observations by a bound for every diameter-one convex template.

The useful positive result remains PV's necessary finite-volume inequality and finite perimeter of an attained actual maximizer. The negative result prevents treating those necessary conditions as a sufficient solution of either global frontier. Other, more selective actual-body variations are not ruled out.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used. The arguments are written and self-reviewed; independent verification and unrestricted optimality remain unfinished.
