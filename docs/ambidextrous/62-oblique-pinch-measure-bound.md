# 62. Oblique pinching against an affine ceiling has an absolutely continuous curvature law

This is a feasibility-based measure theorem for the global structural argument. It removes a class of pinching obstructions without assuming differentiability of the support, maximality, or proximity to the candidate. It applies when the lower corner meets a local affine ceiling whose slope is strictly between the two inner-wall slopes. The ceiling can come from the opposite motion or from an upper supporting line of the common hull.

It does not apply to arbitrary corner/corner pinches. The two parallel limiting cases are recorded separately instead of being absorbed into a strict inequality.

## 62.1 Corner-to-ceiling clearance

Use a compact interior lower-turn angular interval J, with

\[
f(t)=h_K(t),\quad g(t)=h_K(t+\pi/2),\quad
p=f'-g+1,\quad q=g'+f-1,
\]

\[
c=(f-1)\mu+(g-1)\nu,\qquad
\sigma_f=f+f'',\quad\sigma_g=g+g''.
\]

The two curvature measures are nonnegative. The functions f,g are Lipschitz and their derivatives are locally of bounded variation; atoms and singular-continuous curvature are allowed.

Let I be an open interval inside the horizontal projection of a connected feasible body S, and assume c_x(J) is contained in I. A local affine ceiling is a function ell(x)=a+kx such that

\[
(x,y)\in S,\quad x\in I\quad\Longrightarrow\quad y\leq\ell(x).
\tag{62.1}
\]

Since S has a point on every vertical line over I, the lower quadrant at parameter t implies

\[
H_\ell(t):=\ell(c_x(t))-c_y(t)\geq0\qquad(t\in J).
\tag{62.2}
\]

Equality says the corner itself is the unique possible surviving point on that fiber.

Put

\[
A_k(t)=k\cos t-\sin t,\qquad
B_k(t)=-k\sin t-\cos t.
\]

Then H_ell=a+A_k(f-1)+B_k(g-1). Differentiation in distributions gives

\[
H_\ell''=A_k\sigma_f+B_k\sigma_g+b_k(t)\,dt,
\tag{62.3}
\]

where

\[
b_k=-A_k-B_k+2B_kp-2A_kq.
\tag{62.4}
\]

To check the identity, A_k'=B_k, B_k'=-A_k, so H_ell'=A_k p+B_k q. Also p'=sigma_f-dt-q dt and q'=sigma_g-dt+p dt. Substitute these identities. The terms containing p and q are bounded densities; the singular curvature is retained explicitly in (62.3).

## 62.2 The slope condition is geometric

Suppose H_ell(t_0)=0 and c_x(t_0) lies inside I. The single lower quadrant at t_0 has a tent-shaped upper boundary: its slope to the left of the corner is tan(t_0), and its slope to the right is -cot(t_0). Every nearby fiber of S lies above that tent and below ell. Therefore

\[
-\cot t_0\leq k\leq\tan t_0.
\tag{62.5}
\]

This follows by subtracting the common value at the corner, dividing by the positive or negative horizontal displacement, and letting that displacement tend to zero.

The two inequalities are strict exactly when the ceiling is parallel to neither lower inner wall. In that case A_k(t_0)<0 and B_k(t_0)<0, and both stay strictly negative on a smaller angular interval.

At any contact satisfying (62.5), a downward jump in H_ell' is incompatible with the local minimum H_ell=0. Equation (62.3) consequently already excludes a source atom whenever its coefficient is strictly negative. In particular an oblique contact excludes atoms in both sigma_f and sigma_g. The next argument also controls the nonatomic singular part over families of contacts.

## 62.3 A whole family of ceilings, not an uncountable union of null sets

Fix J and I as above. Let L be a nonempty family of affine ceilings valid on I. Assume their slopes are bounded and, uniformly for all ell in L and t in J,

\[
A_k(t)\leq-\eta,\qquad B_k(t)\leq-\eta
\quad\text{for some }\eta>0.
\tag{62.6}
\]

Define H(t)=inf_{ell in L} H_ell(t). It is finite: (62.2) bounds it below by zero and any one member bounds it above. If K is contained in a fixed radius-R disk, f,g and both derivative traces are bounded by R. Thus (62.4) has a common upper bound C depending only on R and the slope bound, not on the individual ceiling intercept.

**Theorem 114 (uniform measure bound at oblique pinches).** With Z={t in int(J):H(t)=0},

\[
\boxed{(\sigma_f+\sigma_g)|_Z\leq(C/\eta)\,dt|_Z.}
\tag{62.7}
\]

In particular neither atoms nor singular-continuous curvature can be carried by this zero set.

**Proof.** Set mu=sigma_f+sigma_g and choose a convex primitive Psi with Psi''=mu on J. Equations (62.3) and (62.6) give

\[
(H_\ell+\eta\Psi-Ct^2/2)''\leq0.
\]

Each displayed function is concave. The infimum of finite concave functions is concave whenever it is finite, since its hypograph is the intersection of their convex hypographs. Therefore

\[
H''+\eta\mu\leq C\,dt.
\tag{62.8}
\]

In particular H is semiconcave. It is nonnegative, so every point of Z is a local minimum. Its one-sided derivatives satisfy H'_-(t)<=0<=H'_+(t), while semiconcavity gives the reverse ordering H'_+(t)<=H'_-(t). Both derivatives are zero and H'' has no atom at any point of Z. Apply Lemma 108 to -H: the nonatomic part of H'' restricted to Z vanishes as well. Thus H''|_Z=0 as a full signed measure. Restrict (62.8) to Z to obtain (62.7). QED.

The use of the entire infimum is important. Proving a null-set statement for each fixed ceiling and then taking an uncountable union would not establish the conclusion.

## 62.4 From local charts to all oblique affine-ceiling pinches

Let P be the set of interior source parameters t_0 for which c_x(t_0) is inside the projection and there exists a local affine ceiling touching c(t_0) with slope strictly between -cot(t_0) and tan(t_0).

For each such contact choose smaller angular and horizontal intervals with rational endpoints, and a compact rational slope interval, so that c_x(J) is contained in I and (62.6) holds on J for every slope in that interval. Take the family of **all** affine ceilings valid on I with slopes in the chosen interval. It is nonempty and includes the ceiling witnessing the contact, so its H vanishes at t_0.

There are only countably many choices of these rational intervals and positive rational lower bounds eta. Theorem 114 on these charts shows that sigma_f and sigma_g, restricted to P, have no singular part. The construction supplies measurable zero sets covering P, so it does not depend on a measurability assumption about the existentially described set P.

This is an exclusion from feasible geometry alone, not an Euler equation for a maximizer. Its density bound C/eta need not equal one.

## 62.5 Which ceiling contacts this covers

**An opposite inner wall.** In an interior-angle upper-turn placement, the forbidden region is above the maximum of two affine functions. If just one is active near a contact coordinate, that affine function is a ceiling for S on a neighborhood. An oblique lower-corner/upper-single-wall pinch is therefore covered by the countable-chart conclusion, even if the active upper angle changes from one contact to another.

**The top of the convex hull.** An upper supporting line of K with nonzero vertical normal component is a ceiling for S. If it passes through a lower canonical corner, it cannot be parallel to either lower inner wall: in the parallel case its supporting equality would contradict the unit offset h_K(n)-1 of that inner wall. Hence such an interior-projection contact is covered as well.

This second conclusion controls curvature in the two normals **defining the contacting corner**. It must not be relabeled as a bound in the generally different normal of the touched hull point. Note 60's outer-contact classification concerns that other normal.

## 62.6 Parallel contacts and corner/corner contacts remain distinct

If a lower inner wall and the parallel opposite-turn inner wall coincide, their defining equalities imply width **two**, not width one. For example a shared wall of normal n satisfies

\[
z\cdot n=h_K(n)-1=1-h_K(-n),
\quad\text{so }w_K(n)=2.
\]

Theorem 109 with a=2 excludes singular-continuous curvature in that shared-wall normal and gives only a density bound of two there. It says nothing about the perpendicular source normal. The strict two-coefficient estimate (62.6) cannot be applied at the parallel limit.

At a corner/corner pinch the upper constraint is locally a maximum of two affine lines. It need not admit any affine majorant that touches at the pinching point. The infimum-of-affine-ceilings proof therefore does not cover that case.

Neither parallel degeneracies nor corner/corner pinches are discarded as zero-area events. They remain among the actual constraints in the global variational problem.

## 62.7 What this adds to singular-curvature exclusion

Note 61 removes false obstructions from inactive corners. This note proves that active oblique affine-ceiling pinches cannot carry source singular curvature in the first place. Together with Note 58, they substantially specify which zero-gap configurations can still protect singular curvature at a global maximizer.

The unrestricted curvature cap is not yet established. The constants here are not the sharp density bound; outer corner coincidences, hidden edges, and the remaining pinching types require further work, as do endpoint completion and the two contact-order inequalities.

No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. These are written proofs subject to independent review.
