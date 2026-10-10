# Reflection averaging of the actual body fails even on the reference

**Purpose.** RS2 proves optimality in a left-right symmetric class. That does not make averaging an arbitrary body with its reflection a valid reduction to that class. This note gives a hand-proof negative control using the reference body itself. It does not refute a different, area-aware symmetrization of cap data or motions. Labels RA are local.

Inputs are the explicit reference geometry, the elementary conventional-motion reduction for area greater than 8/5, the complementary-angle identity RS.1, and the switching obstruction UC1. Neither the sharp weighted theorem nor the assertion of unrestricted reference optimality is used.

## 1. The averaging operation and the reference geometry

Let Sigma be Romik's compact connected reference body, centered so J(x,y)=(-x,y) is a symmetry, and its incoming strip is 0<=y<=1. Its actual hull K has width W_*>2 and identical centered top and bottom faces of length T_*>1. All four endpoints of these faces belong to Sigma, since they are extreme points of its actual hull. The reference area M is greater than 8/5.

Consider the natural Minkowski average of the actual sets

$$A=\tfrac12(\Sigma+J\Sigma)=\tfrac12(\Sigma+\Sigma).\tag{RA.1}$$

The sum is pointwise vector addition of sets, not averaging their indicator functions. A is compact and connected as a continuous image of Sigma times Sigma. It contains Sigma by taking two equal points. It lies inside the convex hull K, so

$$\operatorname{conv}(A)=K,\qquad |A|\ge M>8/5.$$

It is also J-symmetric. The midpoints of the two bottom-face endpoints and of the two top-face endpoints give

$$(0,0),(0,1)\in A.$$

Its left and right extreme points, inherited from Sigma, lie at horizontal distances W_*/2>1 from this vertical column.

## 2. The incoming orientation cannot be changed to evade the obstruction

K contains the rectangle `[-T_*/2,T_*/2] x [0,1]`. In a normal direction (cos theta,sin theta), its width is at least

$$T_*|\cos\theta|+|\sin\theta|.$$

Since T_*>1, this exceeds one at every nonvertical normal. For example restrict by absolute values to [0,pi/2]; the expression is concave, equals T_*>1 at zero and one at pi/2, and is strictly greater than one in the interior. Thus the only straight unit strip into which A can fit has vertical normal. Its incoming orientation is necessarily the horizontal-strip orientation used above, modulo reversal.

Suppose A were ambidextrous. Its area exceeds 8/5, so the existing motion reduction gives conventional endpoints beyond pi/4. Because A is J-symmetric, RS1 supplies both full supporting-quarter families. But UC1 forbids a body with both retained points (0,0),(0,1) and actual points at horizontal distances greater than one on both sides. This is a contradiction.

**Proposition RA1.** The set A in RA.1 is not an ambidextrous sofa, although it contains the reference body, is connected, has the same hull, and is reflection-symmetric.

The failure is not a finite-angle numerical artifact. The extra midpoint points fill portions that must remain absent for turning. The fact that Sigma was already symmetric does not make its Minkowski average idempotent: that identity would require convexity of the actual set.

## 3. What is and is not ruled out

This rules out the proposed universal operation S -> (S+JS)/2 on actual nonconvex bodies as a feasibility-preserving symmetrization. Merely retaining the same convex hull does not preserve the motions. It also shows why symmetry of the optimization problem is not a proof that a symmetric maximizer exists.

It does not rule out a more elaborate cap or motion transformation with its own ordinary-area comparison. In particular convex cap averaging behaves differently: averaging an already symmetric convex cap returns the same cap, but how its two niche sweeps interact still needs proof. No positive clipping term can be discarded by calling the cap data symmetric.

RS2 remains a conditional-class theorem. Unrestricted optimality still needs to address asymmetric end-point-face and opposite-end-positive-face cases, as well as partial-angle competitors not admitted by the symmetric completion. No CI, Lean/Lake compilation, numerical search, dependency installation or manuscript build is used.
