# 18. A completed restricted optimality and uniqueness theorem

This note proves an actual sofa-area theorem, not merely a conditional certificate. Its admissible geometric class is explicitly restricted. It includes Romik's sofa, permits nonsymmetric competitors and moving contact switches, and has a complete area/equality argument. It does **not** yet cover every ambidextrous sofa.

All proofs are written and self-reviewed; they have not been independently refereed or formally checked. Identification with Romik's named candidate uses the matching path formulas in [his Section 5](https://arxiv.org/html/1606.08111v3#S5). The candidate's area is rederived here through the explicit functional, rather than assumed as an upper bound.

## 18.1 The class in the theorem

Let R be the class of compact connected bodies S satisfying all of the following after a proper rigid change of coordinates.

1. K=conv(S) has vertical span one and lies between y=0 and y=1. The body admits both canonical full conventional quarter-turn motions determined by h_K.
2. For h_K and h_K^rho, the quarter functions f,g are C^1 and piecewise C^2 with finitely many pieces. Their curvature densities satisfy 0<=f''+f<1 and 0<=g''+g<1 on each open piece.
3. For each half, p=f'-g+1 and q=g'+f-1 are strictly decreasing, have the endpoint signs in (16.1), and satisfy p<=q. Thus h_K belongs to the convex function domain C of Note 16.
4. The top and bottom exposed faces of K have identical horizontal intervals.

No reflection symmetry of S or K is assumed. The upper and lower functions, switching angles, and curved boundary shapes may differ, subject to the displayed conditions. Condition 4 is an alignment condition on two exposed faces, not symmetry of the rest of the body.

Unit span and correct angular signs are already available for every competitive body by Notes 10 and 15. Full-quarter endpoints, the curvature/velocity conditions, and face alignment have **not** been established as general reductions.

## 18.2 Convexity of the explicitly calibrated candidate hull

We first verify that the function h_* in Note 14 really defines a convex hull.

**Lemma 43 (support construction).** A continuous periodic function h, piecewise C^2 with one-sided first derivatives, is the support function of a compact convex set if its curvature measure h+h'' is nonnegative.

**Proof.** At a smooth parameter theta put P=h(theta)mu_theta+h'(theta)nu_theta. For a parameter phi with |phi-theta|<=pi, variation of constants in the equation h''+h=mu gives

\[
h(\phi)-P\cdot\mu_\phi
=\int_\theta^\phi\sin(\phi-s)\,d\mu(s)\geq0.
\]

For phi>=theta the sine is nonnegative; for phi<=theta both the sine and the orientation of integration are nonpositive. The same argument with one-sided derivatives gives both limiting points at a derivative jump. Thus these points lie in every supporting half-plane and attain the specified support in their own directions. Their limits cover the exceptional parameters by continuity. The intersection of all the half-planes is nonempty, closed, and bounded, and its support equals h in every direction. QED.

For h_* the curvature densities on the three upper phases are

\[
(\rho_f,\rho_g)=
\begin{cases}
(0,1/2),&0<t<\beta,\\
(\tfrac34R\cos(t/2+\pi/8),\ \tfrac34R\sin(t/2+\pi/8)),&\beta<t<b,\\
(1/2,0),&b<t<L.
\end{cases}
\tag{18.1}
\]

They are nonnegative. On the middle phase their maximum is A cos(beta)=1/(4Y)<7/8, since Y>2/7. To verify the endpoint value, matching f_* at beta gives R cos(beta/2+pi/8)=4A cos(beta)/3; the other maximum follows by the reflection relation (14.7). Thus all the required densities are strictly less than one.

At the top normal the derivative jump is

\[
g_*'(0)-f_*'(L)=(2A-1)-(2A/3-1)=4A/3>0.
\]

The bottom jump is the same by reflection. There are no other derivative jumps: the phase matching was proved in Lemma 36, and the derivatives at the horizontal normals match across reflection because f_*'(0)=1/2 and g_*'(L)=-1/2. Lemma 43 therefore constructs a compact convex hull K_* with support h_*.

Its top and bottom exposed faces are both

\[
[\ell_*,r_*]=[1-2A,\ 1-2A/3].
\tag{18.2}
\]

In particular K_* contains the positive-width rectangle [ell_*,r_*] times [0,1]. The velocity conditions placing h_* in C were checked in (16.4).

## 18.3 Feasibility, connectedness, and area of the candidate

Apply Theorem 41 to h_* and its reflection. Let F_* be the lower profile over [ell_*,r_*]. The candidate corner-height estimate of Note 4 gives

\[
c_{*,y}(t)\leq m=1/2+R-\sqrt2<1/2.
\]

The B_y contact height decreases from c_{*,y}(beta) to zero, and the D_y height increases from zero to c_{*,y}(b), by (17.4). The middle profile is the corner curve itself. Consequently

\[
0\leq F_*(x)\leq m<1/2.
\tag{18.3}
\]

Both reflected profiles lie in the central rectangle and are strictly separated. Define Sigma_* to be K_* with the two open canonical sweeps removed. Its central vertical sections are exactly

\[
[F_*(x),\ 1-F_*(x)],\qquad \ell_*\leq x\leq r_*;
\]

outside this interval, the sections are unchanged from K_*. Every section over the horizontal projection is nonempty. Hence Sigma_* is compact and connected by the interval-fiber argument of Theorem 26. The canonical hallway inclusions hold by construction; incoming and final strip widths are one. Thus Sigma_* is a feasible ambidextrous body with full quarter turns.

The removed profiles lie strictly over the interior of the two horizontal faces. All nonhorizontal exposed boundary points lie on the flanks x<=ell_* or x>=r_* and survive; the endpoints of the horizontal faces survive as well. Equivalently, on each convex flank the x-coordinate moves monotonically between a horizontal extremum and a face endpoint, as follows from P_x'=-(h+h'')sin(theta). Thus every support value of K_* is still attained in Sigma_*, and

\[
\operatorname{conv}(\Sigma_*)=K_*.
\tag{18.4}
\]

By exact profile subtraction and Theorem 40,

\[
|\Sigma_*|=\widetilde{\mathcal Q}(h_*)=M
=1+4Y^2+\arctan Y.
\tag{18.5}
\]

The canonical corner formulas are exactly the matched three-phase formulas of Note 14, which agree with Romik's supplied path. His construction as the intersection of that motion envelope with its reflection therefore identifies Sigma_* with his ambidextrous candidate, up to the chosen normalization.

## 18.4 Regular closedness needed for exact uniqueness

The continuous profile F_* vanishes at ell_*,r_* and its central surviving sections have length at least 1-2m>0. Outside that central rectangle the body is the unchanged convex hull. The upper and lower boundary functions of a two-dimensional convex body are continuous over the interior of its horizontal projection.

It follows that every point of Sigma_* whose x-coordinate is in the interior of that projection is a limit of interior points: on the central interval use the continuous separated graphs, and on the flanks use the convex boundary graphs. Near a horizontal extreme, the profiles are absent and the same assertion follows from regular closedness of a convex body with nonempty interior. Thus

\[
\Sigma_*=\overline{\operatorname{int}\Sigma_*}.
\tag{18.6}
\]

This is the required regular-closedness proof for the identified candidate. It is not a claim that all feasible saturated envelopes are regular closed.

## 18.5 The restricted theorem

**Theorem 44 (optimality and exact body uniqueness on R).** Every S in the class R satisfies

\[
|S|\leq M.
\]

Equality holds if and only if S is congruent to Sigma_*. In particular Sigma_* is the unique maximizing body in this class up to congruence.

**Proof.** Let K=conv(S) in the normalized coordinates. Theorem 26 gives the compact connected canonical saturation E_K containing S. Theorem 41 computes its two profile regions; Lemma 42 removes all clipping because the faces are aligned. Hence

\[
|S|\leq|E_K|=\widetilde{\mathcal Q}(h_K)\leq M,
\]

where the final inequality is the global adaptive maximization theorem, Theorem 40.

If |S|=M, equality in Theorem 40 gives h_K=h_*+a cos(theta). Therefore K is a horizontal translate of K_*, and all its canonical quadrants, profiles, and saturated envelope translate by the same vector. Thus E_K is that translate of Sigma_*. Since S is closed, S is contained in E_K, their areas agree, and E_K is regular closed by (18.6), Lemma 4 yields S=E_K. Undo the initial proper rigid coordinate change. The converse follows from (18.5) and the verified membership of Sigma_* in R. QED.

The proof identifies bodies, not their possible motion witnesses. It does not assume symmetric competitors, fixed switching times, or Baek's single-turn optimality theorem.

## 18.6 What the theorem leaves open

This proves the sharp constant and exact equality case on an explicit geometric class containing the candidate. An unrestricted theorem still requires a valid reduction to this class or a larger corrected functional that handles the excluded configurations. Specifically, partial endpoint angles, nonmonotone contact velocities, curvature outside the indicated range, and misaligned horizontal faces have not been eliminated for an arbitrary optimizer. They are not minor notation changes: the clipping formula (17.11) records a positive area correction that the present upper bound does not control.
