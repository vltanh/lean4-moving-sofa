# Two convex wings and an ordinary-area core

This begins a different certificate from the least-majorant repair. The variables are two **convex pieces of surviving material**, not the full convex hull of a nonconvex sofa. Their areas are retained explicitly. This prevents material clipped out by the opposite niche from silently being counted as safe material.

The new results are written, self-reviewed arguments. They are not independent verification of this or the previous branch. In particular, this note does **not** prove that every ambidextrous maximizer admits the decomposition below. The reference snapshot is `f5eb4327861caea4a962db98897ca507fee06473`; existing manuscript and Lean files are not changed.

## 1. The data domain

Write L=pi/2. For now choose pi/12<beta<pi/4 and b=L-beta; the sharp calibration will use the candidate's beta. Put c=cos(beta), s=sin(beta). Let R and D be nonempty compact convex bodies in the common strip 0<=y<=1, with support functions r and d. The letter D denotes the **left** wing here, not a deficit. The right wing is R.

Require, for each wing B,

$$
h_B(t)+h_B(t+\pi)\leq1\qquad(\beta\leq t\leq\pi-\beta).
\tag{TW.1}
$$

Define four affine points from the cut supports:

$$
P_R=\left(\frac{r(\beta)+r(-\beta)}{2c},
          \frac{r(\beta)-r(-\beta)}{2s}\right),
\qquad Q_R=P_R-(1/c,0),
$$

$$
P_D=\left(-\frac{d(\pi-\beta)+d(\pi+\beta)}{2c},
          \frac{d(\pi-\beta)-d(\pi+\beta)}{2s}\right),
\qquad Q_D=P_D+(1/c,0).
\tag{TW.2}
$$

The additional constraints are Q_R in R and Q_D in D. Together with TW.1 these imply equality of the two widths at the cut directions. For example,

$$
r(\pi+\beta)=1-r(\beta),\qquad
r(\pi-\beta)=1-r(-\beta).
$$

They also make r the support of the single vertex Q_R on [pi-beta,pi+beta]. Indeed every normal in that interval is a positive combination of its two endpoint normals, and Q_R attains both supporting bounds. The left-wing counterpart has vertex Q_D on [-beta,beta].

All these are genuine constraints on the data, not assertions about all sofas. They are preserved by Minkowski interpolation: cut points are affine, width inequalities are linear, and interpolation of a point in each convex body lies in the interpolated body.

## 2. A harmless completion of the outward corners

**Lemma TW1 (outward angular completion).** Replacing R by conv(R union {P_R}), and D by conv(D union {P_D}), preserves the data domain, preserves all the supports used by the core below, and can only increase the wing areas. After this replacement, the support on each of the two short gaps is the support of its corresponding vertex.

**Proof.** Consider R. At beta, an exposed point differs from P_R by a nonnegative multiple of n'_beta: its inequality at -beta forces this sign. Therefore its scalar product dominates that of P_R in every direction from beta to beta+pi. The exposed point at -beta gives the complementary half-circle. Together they show P_R does not change support outside (-beta,beta). Inside that gap, the two endpoint bounds and positive sine interpolation show that P_R dominates the old support.

Its ordinate lies in [0,1]. To check this, on the strip the two functions x c+y s and x c-y s differ by 2y s in [0,2s]. The difference of their maxima is therefore in that interval, which is exactly the assertion about the ordinate in TW.2. Thus the added point remains in the common height strip. The constrained widths involve no interior direction of the changed gap. The old Q_R stays in the larger body; all cut supports stay fixed. The left case is the reflected argument. Finally area is monotone under inclusion. QED.

This completion does not purport to preserve a sofa motion. It is an enlargement of **auxiliary data**, justified by the direction of the functional inequality. Its effect on the actual area comparison, when one exists, is favorable because it only increases the two explicitly counted convex areas.

## 3. The functional, including its endpoint terms

For any support function write h^rho(t)=h(-t)+sin(t), the support after reflection in y=1/2. On beta<=t<=b define

$$
z_-(t)=(r(t)-1)n_t+(d(t+L)-1)n_{t+L},
$$

$$
z_+(t)=\rho\big((r^\rho(t)-1)n_t+(d^\rho(t+L)-1)n_{t+L}\big),
\qquad \rho(x,y)=(x,1-y).
\tag{TW.3}
$$

These Lipschitz curves use only support values outside the completed gaps. Let I(z)=one half of the integral of det(z,z'). Define

$$
\begin{aligned}
\mathcal W(R,D)={}&|R|+|D|-I(z_-)+I(z_+)\\
&+\tfrac12\det(Q_R,z_+(\beta)-z_-(\beta))\\
&+\tfrac12\det(Q_D,z_-(b)-z_+(b)).
\end{aligned}
\tag{TW.4}
$$

All integrals use almost-everywhere derivatives. Convex supports are Lipschitz, so curvature atoms are allowed. The formula is a quadratic functional of the two support functions, including the affine corner offsets. It is invariant under a common translation of both bodies; this follows either by telescoping the closed curve terms or directly by expanding each determinant. It is invariant under horizontal reflection with exchange of the wings.

The quadratic symbol W must not be confused with the horizontal width used in earlier notes. We use the calligraphic symbol throughout this series.

## 4. An explicit sufficient geometric admission condition

Consider the closed curve formed, in order, by

$$
Q_R\to z_-(\beta)\to z_-(b)\to Q_D
\to z_+(b)\to z_+(\beta)\to Q_R,
$$

using the two curves on the middle portions and straight segments for the four joins. Suppose it is a simple clockwise Lipschitz Jordan curve, bounding a region C. Suppose also that the interiors of R,D,C are pairwise disjoint and that the proposed body S is contained in their union. Then Green's area formula gives

$$
\boxed{|S|\leq |R|+|D|+|C|=\mathcal W(R,D).}
\tag{TW.5}
$$

If S is exactly that union, equality holds. This is ordinary area, not a signed-area guess: the simple-curve orientation, disjointness and containment are the stated hypotheses. They must be established for any use of TW.5. Removing them is not justified by a later algebraic calibration.

Lemma TW1 may be applied after TW.5. Its enlarged wings need not remain disjoint from C or feasible themselves; only the already established inequality and the increase of the functional are used.

## 5. The candidate has this representation

Use the centered candidate support h_* from Note 14; its outer horizontal vertices are (a_*,1/2) and (-a_*,1/2). On the right outward semicircle -L<=t<=L put r_*(t)=h_*(t). On the two inward arcs put

$$
r_*(t)=1-h_*(t-\pi)
\quad\text{for }L\leq t\leq\pi-\beta
\text{ and }\pi+\beta\leq t\leq3L,
$$

and on the inward gap use Q_R dot n_t. Define d_*(t)=r_*(pi-t). These are the convex wings bounded by the candidate's outer flanks, its two right or left inner tails, and the two inward cut segments.

Their convexity can be checked from the displayed supports: on inward arcs the curvature is 1 minus the corresponding outer curvature, on outward arcs it is the nonnegative candidate curvature, and the two inward cut atoms each have length tan(beta). All other joins are continuous in the first derivative. The candidate's outer curvature is below 7/8 on the relevant arcs, as checked in Note 18. Each constrained width is one and the common strip is [0,1].

The two inward cut segments meet at Q_R or Q_D. The candidate's strictly monotone lower core and its reflection supply the intervening Jordan region. Their union with the two convex wings is the candidate. Equivalently this follows by tracing the boundary formulas in Notes 14 and 18; no full-hull area is being substituted for a wing area. Consequently

$$
\mathcal W(R_*,D_*)=|\Sigma|=M.
\tag{TW.6}
$$

The candidate geometry and its value here are cited dependencies from the existing explicit construction, not newly proved global optimality. The next notes prove a sharp algebraic inequality for this wing domain. The missing unrestricted step will remain whether arbitrary relevant bodies admit an upper comparison of the form TW.5 (or a verified extension of it).

## Scope and provenance

The auxiliary-convex-body organization is motivated by Baek's functional and the lower coercive machinery in PRs #8 and #9, but neither one-turn geometric admission nor Gerver's final theorem is imported. The new wing variables are introduced specifically to retain the clipping that defeated the whole-hull repair route. No CI or Lean/Lake process is used.
