# Direction 1: critical faces instead of first-order balance alone

**First-attempt result.** The repository already contains the finite normal-cone equation (Note 53), visible-side derivative (Note 21), and finite area regularity (Note 54). Re-deriving them would not establish a new two-turn structural theorem. This note instead adds an exact second-order rejection test and a finite candidate reduction for each bounded fixed-angle polygon problem. It is not a proof of curvature domination at an infinite-angle maximizer.

Baseline: `80fb626e5672d9bb66a52c88d4b1b027b6c62e11`. This is elementary quadratic optimization applied to the earlier geometric charts, not a claim of a new general optimization theorem. Labels D1 are local.

## 1. Keep the feasible cone

On one actual admissible finite chart let area be

$$F(z)=c+g^Tz+\tfrac12z^THz,$$

with H symmetric. Its domain is a polytope P defined by affine chart and actual geometric constraints. Hull retention, strip constraints and nonempty fibers remain in P. At z in P a direction v is admissible for a short positive segment when it belongs to its polyhedral tangent cone.

The exact finite expansion is

$$F(z+tv)-F(z)=t\nabla F(z)^Tv+\tfrac12t^2v^THv.$$

Therefore either of the following certifies an actual improving variation **inside that chart**:

- grad F(z) dot v>0;
- grad F(z) dot v=0 and v^THv>0.

At a local maximum the Hessian must be nonpositive on the critical cone {v admissible: grad F dot v=0}. This does not mean it is negative semidefinite on all raw height directions. A direction leaving the feasible cone proves nothing about the body.

These tests are exact when H, z and v are rational. They complement Note 53's first-order multiplier equation; they do not discard its multipliers. The selection penalties of earlier notes would have to be included on their own affine branches before applying this test to a penalized problem.

## 2. A finite list suffices for a compact quadratic chart

**Theorem D1.1.** Let P be a nonempty compact polytope and F a quadratic polynomial. At least one global maximum is either a vertex of P or the unique relative stationary point of F on a face where the Hessian restricted to that face's tangent space is negative definite.

**Proof.** Choose among all global maximizers one whose minimal containing face Q has the smallest possible dimension. It lies in the relative interior of Q. All sufficiently small displacements in its tangent space are feasible with both signs, so the gradient restricted to that space is zero and the restricted Hessian is negative semidefinite. If the latter has a nonzero null vector v, the quadratic expansion makes F constant along the entire line through the maximizer in direction v. Compactness lets this line be followed inside Q to its boundary, yielding a global maximizer on a smaller face, a contradiction. Thus the Hessian is negative definite, unless Q has dimension zero. Negative definiteness gives a unique stationary point on the affine hull of Q. QED.

This supplies a finite algorithm: enumerate faces; retain vertices; on each positive-dimensional face with negative definite restricted Hessian solve its linear stationary equations and test membership in the face; compare the resulting values. Singular stationary ridges do not require choosing an arbitrary point on an infinite continuum, because a lower-dimensional face contains an equally good representative.

For rational normals, offsets and bounding polytopes, the finite line-arrangement construction of Note 53 produces rational polyhedral charts and rational area polynomials. A rational tangent basis reduces every retained stationary system to a nonsingular rational linear system. Consequently all listed candidates and area values are rational. This conclusion concerns the bounded *finite-angle* optimization, not the true infinite-angle optimum.

Taking the union over the finitely many incident charts preserves the conclusion. Chart walls may carry a maximum and cannot be omitted. If a raw total-envelope relaxation is used instead of the connected/hull-retaining class, its larger area still gives an upper bound, but its maximizing body cannot automatically be treated as a feasible connected sofa.

## 3. A genuine finite-hallway saddle with zero first variation

Use orthonormal rational directions n=(3/5,4/5), v=(-4/5,3/5), and coordinates z=u n+w v. Fix d=5/7, so the rotated square 0<=u,w<=d lies in a horizontal strip of width one. Let a,b in [d/4,3d/4]. Intersect this square with two unit L-hallways of opposite orientation:

$$H_1=\{u\le a+1,\ w\le b+1,\ u\ge a\ \text{or}\ w\ge b\},$$

$$H_2=\{u\ge a-1,\ w\ge b-1,\ u\le a\ \text{or}\ w\le b\}.$$

All outer inequalities are inactive on the square. The envelope is the union

$$[0,a]\times[b,d]\ \cup\ [a,d]\times[0,b],$$

including their common point and boundary lines. It is compact and connected for every parameter in the box. Its ordinary area is exactly

$$F(a,b)=a(d-b)+(d-a)b=d(a+b)-2ab.$$

At a=b=d/2 both first derivatives vanish. Nevertheless v=(1,-1) is an admissible parameter direction and

$$F(d/2+t,d/2-t)=d^2/2+2t^2>F(d/2,d/2).$$

Thus the stationary configuration is a strict saddle, not a maximum. The Hessian has off-diagonal entries -2 and zero diagonal entries. The finite critical-face reduction rejects the interior stationary point and finds the two maximizing box vertices (d/4,3d/4) and its reversal, with exact value

$$\boxed{\max F=5d^2/8=125/392.}$$

This example consists of two legitimate unit L positions and a containing incoming strip. It is **not** claimed to complete the intermediate rotations, to have its square as actual hull, or to be a fully canonical maximizing polygon. Its role is to test the finite chart reasoning and to disprove a generic inference from balanced derivatives to global area optimality. Every improving parameter step here preserves the actual connected finite envelope.

## 4. What the structural attempt accomplished

The attempt gives an exact procedure for excluding stationary saddles and replacing a continuous bounded rational finite-chart maximum by a finite list of critical-face candidates. This can be used with Direction 3's box and arrangement certificates, rather than trying to force all arbitrary raw height directions into a smooth Euler equation.

It did **not** show that a true maximizing hull has unit support curvature, injectivity, or no hidden boundary. Notes 21, 53 and 67 identify genuine remaining issues: visible outer length need not equal total outer length; active feasibility normals survive; and outer/inner-corner coincidences and the sharp absolutely continuous density bound remain. The new second-order test must be supplied with actual feasible directions at those configurations before it excludes them.

**Next gate:** obtain a uniform family of such feasible directions, or an exhaustive finite critical-face covering with a controlled infinite-angle remainder. A finite algorithm whose chart count has not been bounded or enumerated is not a completed certificate. This is a substantive test of the structural route, not an announcement that its continuum obstruction is solved.

Context: Baek's *Optimality of Gerver's Sofa*, arXiv:2411.19826, Sections 1.3--1.7 and Chapters 3--6, motivates the balancing/injectivity approach for one turn. No one-turn maximizing premise is transferred to the two-turn problem here.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long search is used. Mathematical statements and existing chart dependencies remain self-reviewed.
