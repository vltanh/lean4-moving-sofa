# A sharp two-wing calibration retaining the convex tail bodies

This proves a sharp auxiliary-body theorem on the explicit two-wing domain TW.1–TW.2. Unlike the earlier hull-repair calibrations, the positive area terms are the areas of the two convex wings themselves. Arbitrary curvature atoms in a competing wing are permitted. A geometric admission theorem for all unrestricted sofas is still required; it is not inferred from this calibration.

The proof combines a direct first-variation identity with the common-strip quadratic factorization WS1. It does not assume joint concavity on an unconstrained affine profile space. Labels WC are local.

## 1. Reference and weights

Let Y be the positive root of 4Y³+3Y-1=0, beta=arctan(Y), L=pi/2, and b=L-beta. The candidate comparison beta>pi/12 can be checked without decimals: at z=2-sqrt(3), the cubic is 109-63sqrt(3)<0 because 109²<3*63². Thus sin(2beta)>1/2, as required by WS1.

Let R_*,D_* be the explicit convex candidate wings in TW.6. Write rho(t) for the candidate's outer-right curvature density on beta<t<L. From the matched support formulas,

$$
\rho(t)=
\begin{cases}
\tfrac34 R_0\cos(t/2+\pi/8),&\beta<t<b,\\
1/2,&b<t<L,
\end{cases}
$$

where R_0=2/(3 sin(beta/2+pi/8)). Define on beta<t<pi-beta

$$
\mu(t)=1-\rho(\min\{t,\pi-t\}).
\tag{WC.1}
$$

The candidate formulas give 1/2<=rho<7/8; for the upper bound its largest value is 1/(4Y)<7/8 using Y>2/7. Hence

$$
1/8<\mu(t)\leq1/2.
$$

Both candidate wings have width one in every constrained normal t in [beta,pi-beta]. Their inward cut edges have length tan(beta). All their other nonzero curvature is absolutely continuous. The two outer corner gaps have zero curvature, not unrecorded atoms.

## 2. First variation on arbitrary convex competitors

Let (R,D) satisfy TW.1–TW.2 and the common strip condition. Let delta r,delta d be the differences from the candidate supports. The derivative of a convex body's area under Minkowski interpolation is the mixed-area expression integral delta h against the reference curvature measure. This follows by polarizing the full support-area identity and distributional integration by parts; it includes every reference atom.

For the lower core, writing z_*'=p_* n_t+q_* n_{t+L}, variation of -I(z_-) gives the interior term

$$
\int_\beta^b[-q_*\delta r(t)+p_*\delta d(t+L)]dt
$$

and the endpoint term -[det(z_*,delta z)/2]_beta^b. Only the reference is differentiated after integration by parts. The reflected physical upper core gives the same expression for the reflected support differences. Thus no derivative or contact-set regularity of the competitor is assumed.

On the candidate core,

$$
\rho_f=(1+q_*)/2,\qquad\rho_g=(1-p_*)/2.
$$

After adding the wing-area variations, the coefficient of the outer right support is rho_f-q_*=1-rho_f. Its opposite inner support already has coefficient 1-rho_f. The left pair has rho_g+p_*=1-rho_g and the same opposite coefficient. On the remaining tail intervals the two paired curvatures both equal 1/2. This gives precisely the weight WC.1 for both wings.

The cut atoms also cancel exactly. Here are the right-wing endpoint terms explicitly, rather than discarding them. At the reference,

$$
z_-(\beta)-Q_R=-\tan\beta\,n'_\beta,
\qquad z_+(\beta)-Q_R=\tan\beta\,n'_{-\beta}.
$$

Differentiating the core endpoint terms in TW.4 and the curve integrals gives

$$
\tan\beta\,[\delta r(\beta)+\delta r(-\beta)].
$$

The area variation of the two inward cut atoms is

$$
\tan\beta\,[\delta r(\pi+\beta)+\delta r(\pi-\beta)]
=-\tan\beta\,[\delta r(\beta)+\delta r(-\beta)],
$$

using the cut-width equalities forced by TW.2. The left cancellation is the horizontal reflection. These calculations allow the cut **positions** to vary; they are not merely a fixed-endpoint calculation.

**Lemma WC1 (exact dual first variation).**

$$
\boxed{
D\mathcal W(R_*,D_*)[(R,D)-(R_*,D_*)]
=\sum_{B\in\{R,D\}}\int_\beta^{\pi-\beta}
\mu(t)\,[w_B(t)-1]dt\leq0.
}
\tag{WC.2}
$$

The inequality follows from TW.1. At zero derivative, positivity of mu and continuity of widths imply w_B(t)=1 for both wings on the whole closed interval, including the vertical normal. This is the domain's strip-width slack, not an unproved geometric property of arbitrary sofas.

## 3. The exact deficit and its sign

Apply TW1 first and denote the completed wings by R^c,D^c. Their functional value is at least that of the original pair. By a common vertical translation put their higher top at one; reflect horizontally with wing exchange if needed to make it the right top. Neither operation changes the functional, reference shape, or width constraints.

The quadratic expansion is exact. Let delta be this completed, aligned support difference. Since the reference value is M,

$$
\boxed{
M-\mathcal W(R^c,D^c)
=\sum_{B\in\{R^c,D^c\}}\int_\beta^{\pi-\beta}
\mu(t)[1-w_B(t)]dt+B(\delta).
}
\tag{WC.3}
$$

Both terms are nonnegative: the first by the actual width constraints, the second by WS1's common-strip factorization. This is an identity followed by a proved sign, not a Taylor remainder approximation or a pointwise Hessian heuristic.

**Theorem WC2 (sharp calibration on the two-wing domain).** Every pair in the domain of TW.1–TW.2 satisfies

$$
\boxed{\mathcal W(R,D)\leq M.}
\tag{WC.4}
$$

Equality holds exactly for the candidate wing pair translated together horizontally in the normalized strip.

**Proof.** The inequality follows from completion and WC.3. At equality the two nonnegative terms of WC.3 vanish. WC1 gives both vertical widths equal to one. Since both bodies lie in the same strip, both touch y=0 and y=1. The three trace deficits in WS.7 are therefore zero. WS1's equality analysis forces both completed support functions to agree with the candidate after one common horizontal translation.

Completion changed only the two wing areas and left the core terms fixed. Equality in the original bound therefore also requires zero area increase for each completed wing. Each completed candidate wing has nonempty interior. A proper closed convex subset of such a body has strictly smaller area: a separating supporting line excludes an open set of positive area. Thus the original wings equal their completed versions. Conversely the candidate pair attains M by TW.6 and common translation invariance. QED.

No curvature-density upper bound, reflection symmetry of competing wings, or smooth boundary premise is used in this theorem. The common strip, constrained widths and inward cut-vertex requirements **are** hypotheses. No version with those requirements silently deleted is claimed.

## 4. The corresponding ordinary-area theorem

**Corollary WC3 (a proved geometric comparison on its admission class).** Suppose a compact body S admits wing data in TW.1–TW.2 satisfying the simple-core, disjointness and containment conditions of TW.5. Then |S|<=M. At equality, the wing data are the candidate pair up to a common translation, and the bounding core is the candidate core. Thus S is a closed subset of that translated candidate with the same area. The previously proved regular closedness of the candidate gives exact equality by Lemma 4.

This is a genuine ordinary-area implication once the listed geometric data are supplied. It is not a claim that all unrestricted ambidextrous bodies supply them. In particular, full-turn completion, placement of core cuts, monotonicity of the chosen core and the cut-vertex conditions must not be inferred from a zero-deficit theorem whose hypotheses already require them.

## 5. What this changes in the proof program

This formulation retains the actual wing areas, so it does not charge every change of the full hull's large horizontal face as surviving material. It uses the multi-convex-body organization suggested by the one-turn theory, while deriving its own two-wing quadratic sign and dual certificate. The curvature assumption has been removed from this **new data domain**, not yet from the admission of every unrestricted maximizing sofa.

The next test is geometric: construct such wing data, or a controlled upper comparison using them, for every relevant maximizer. The known axis-cut and shadow-clipping examples are mandatory checks; replacing their wing area by repaired hull area would undo the point of this construction. A finite or computer-assisted admission argument would need coverage of the full claimed class, not just agreement on the candidate.

All new statements are written proofs with self-review. Symbolic and numerical diagnostics of the algebra are recorded separately. No CI or Lean/Lake compilation is used, and no unrestricted-completion claim is made.
