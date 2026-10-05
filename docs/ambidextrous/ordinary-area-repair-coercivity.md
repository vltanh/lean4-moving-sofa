# Ordinary-area repair supplement: coupled coercivity instead of a small-amplitude test

This note concerns the missing **ordinary-area comparison**, not another maximization of the already calibrated functional. It strengthens the area-gain calculation in Note 40: when both upper-quarter supports are repaired, their cross term has a favorable Dirichlet spectral gap. Expressing the gain in the **final** contact velocities removes the small-amplitude requirement from its positivity test.

The required geometry is explicit below. In particular, this does not prove that arbitrary maximizing hulls admit these repairs. No feasible interpolation, unchanged complete niche, or unrestricted closure is assumed. Labels RC1 onward are separate from the numbered notes and the AF/WG supplements.

## R.1 Geometric setting of the identity

Put L=pi/2. Consider the upper-quarter support functions f(t)=h(t), g(t)=h(t+L) of a common convex hull. Let another convex hull have upper-quarter functions

\[
f_c=f+u,\qquad g_c=g+v,
\qquad u,v\geq0.
\]

Assume u,v belong to H^1_0(J) on one closed interval J=[a,b] compactly contained in (0,L), and extend them by zero. The supports, all endpoint normalizations, and the other half of the hull are unchanged. Thus the reflection of this construction is **not** included automatically; a second half is accounted for by adding its separate gain.

Both ordinary surviving envelopes must be feasible connected bodies, and the following boundary accounting must hold:

1. The two changes preserve the respective right- and left-wall suprema which form the side portions of the affected lower niche. The other niche is unchanged.
2. The only changing part of the lower niche boundary is the standard corner arc c(t) for a<=t<=b, traversed with decreasing horizontal coordinate. Its endpoints are unchanged. There is no uncounted clipping by the hull or the other niche.
3. The support repairs satisfy the complementarity identities

\[
\int_Ju\,d\sigma_{f_c}=\int_Ju\,dt,
\qquad
\int_Jv\,d\sigma_{g_c}=\int_Jv\,dt,
\tag{R.1}
\]

where sigma_f=f+f'' and sigma_g=g+g'' are distributional curvature measures. These follow, for example, when each repaired curvature is one on the set where its increment is positive. They are hypotheses here, not conclusions about every support majorant.

The input and output can have curvature measures. Convex support functions are Lipschitz and their derivatives have locally bounded variation, so all measure pairings and H^1 expressions below are defined. The supports need not have pointwise second derivatives.

These conditions are met by the verified protected repairs when their two-wall roof and feasibility checks apply. They may also be checked for configurations not near the candidate. Smallness is not a hypothesis of the positivity theorem below; it can still be a way to verify the geometric conditions.

## R.2 Exact area change with two interacting support increments

Set

\[
p=f'-g+1,\quad q=g'+f-1,
\qquad p_c=p+u'-v,\quad q_c=q+v'+u.
\]

The lower inner corner is c=(f-1)mu+(g-1)nu, and its change is d=u mu+v nu. Expansion of the convex support-area integral gives the one-half hull gain

\[
\Delta |K|=\int_Ju\,d\sigma_f+\int_Jv\,d\sigma_g
+\frac12\int_J(u^2+v^2-u'^2-v'^2).
\tag{R.2}
\]

No factor two occurs: only one half of the support circle is being changed. Under the boundary conditions in R.1, direct expansion of the corner determinant integral gives the entire niche gain

\[
\Delta |N|=\int_J(qu-pv)
+\frac12\int_J(u^2+v^2+uv'-vu').
\tag{R.3}
\]

To verify this without differentiating an active parameter, expand det(c+d,(c+d)')/2. Integration by parts cancels the boundary cross term because d vanishes at a,b. The linear part is det(d,c')=qu-pv. The quadratic part is det(d,d')/2=(u^2+v^2+uv'-vu')/2. This is the positively oriented niche boundary contribution for the standard corner; it is not the formula for a reverse corner.

Complementarity (R.1), together with sigma_fc=sigma_f+(u''+u)dt in distributional notation, gives

\[
\int_Ju\,d\sigma_f=\int_Ju+\int_Ju'^2-\int_Ju^2,
\quad
\int_Jv\,d\sigma_g=\int_Jv+\int_Jv'^2-\int_Jv^2.
\tag{R.4}
\]

For measure inputs, the notation for u'' is distributional; integration by parts is the H^1/BV pairing. Its endpoint terms vanish. Subtract (R.3) from (R.2) and use (R.4).

**Lemma RC1 (two equivalent gain identities).** The actual surviving-area gain is

\[
\begin{aligned}
\Delta |S|={}&\int_J[(1-q)u+(1+p)v]\\
&+\frac12\int_J[u'^2+v'^2-2u^2-2v^2-uv'+vu']
\tag{R.5}
\end{aligned}
\]

and, equivalently,

\[
\boxed{\Delta |S|=\int_J[(1-q_c)u+(1+p_c)v]
+\frac12\int_J[u'^2+v'^2+uv'-vu'].}
\tag{R.6}
\]

**Proof.** The first expression is the subtraction just performed. Substituting q=q_c-v'-u and p=p_c-u'+v changes its linear integral by integral (u^2+v^2+uv'-vu'), giving the second expression exactly. QED.

The cross terms cannot be omitted when both walls change. In particular, adding two one-wall formulas with both using the original velocities misses the interaction.

## R.3 The quadratic remainder is coercive

Write z=u+iv, and let ell=b-a. For

\[
\mathcal B_+(u,v)=\frac12\int_J(u'^2+v'^2+uv'-vu')
\]

put y(t)=exp(it/2)z(t). Completing the square gives

\[
\mathcal B_+=\frac12\int_J\left(|y'|^2-\frac14|y|^2\right).
\tag{R.7}
\]

Since y vanishes at both ends, the Dirichlet inequality yields

\[
\boxed{\mathcal B_+\geq
\frac12\left(1-\frac{\ell^2}{4\pi^2}\right)\int_J|y'|^2.}
\tag{R.8}
\]

For ell<=pi/2 the coefficient is at least 15/32. In particular this expression is strictly positive whenever (u,v) is nonzero. The Dirichlet inequality can be proved by expanding (y'-(pi/ell)cot(pi(t-a)/ell)y)^2 for compactly supported smooth functions, then using density; real and imaginary parts give the complex version.

The quadratic part of (R.5) is coercive as well. With y_-(t)=exp(-it/2)z(t), it equals

\[
\mathcal B_0=\frac12\int_J\left(|y_-'|^2-\frac94|y_-|^2\right)
\geq\frac12\left(1-\frac{9\ell^2}{4\pi^2}\right)\int_J|y_-'|^2.
\tag{R.9}
\]

For ell<=pi/2 this coefficient is at least 7/32. These estimates involve only the repair increments; they require no spectral or numerical calculation on a sofa.

## R.4 A genuine improvement criterion without a size restriction

**Theorem RC2 (coercive coupled repair).** In the geometric setting R.1, suppose either

\[
(1-q_c)u+(1+p_c)v\geq0\quad\text{a.e. on }J,
\tag{R.10}
\]

or the analogous inequality with the original velocities p,q. Then every nonzero repair strictly increases the ordinary area.

In particular, (R.10) follows from q_c<=1 on {u>0} and p_c>=-1 on {v>0}. The original-velocity version follows from q<=1 and p>=-1 on the respective sets. Neither test requires a strict margin or small increments.

**Proof.** In the final-velocity case use (R.6) and (R.8); in the original-velocity case use (R.5) and (R.9). The linear integral is nonnegative and the quadratic term is positive unless u=v=0. QED.

More generally, negative linear work is permitted whenever its magnitude is smaller than the explicit quadratic bound in (R.8) or (R.9). This is an exact sufficient inequality, not a claim that the negative part is always so controlled.

For a global maximizer admitting such a nonzero **genuinely feasible** repair, RC2 is a contradiction. This statement is independent of the candidate or of the value M. It does not use the sharp adaptive theorem to declare an infeasible comparison valid.

## R.5 What this changes and what it leaves unresolved

The previous protected one-wall test used a pointwise positive coefficient such as 1-q-u. That discarded the coercive derivative term. RC2 keeps that term, admits simultaneous repairs, and can use final rather than original velocities. It eliminates small amplitude as a requirement for the sign of the gain.

It does not eliminate smallness from an argument that uses it to preserve the actual side-envelope assignment, standard corner orientation, absence of clipping, connectedness, or endpoint feasibility. Those are separately listed in R.1. Nor has the final-velocity bound been proved for an arbitrary repaired maximizing hull.

The purpose is to make a global geometric comparison cheaper to prove, not to rename the remaining geometric conditions as established facts. The unrestricted proof remains open. Only Markdown and pen-and-paper calculations were used; no CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
