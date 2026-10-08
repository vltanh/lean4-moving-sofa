# 59. Width-one contacts already satisfy the nonatomic curvature bound

This is a global convex-geometric reduction, not a candidate-neighborhood argument. It deals with one source of the coincident-contact obstruction: directions in which a common hull has width exactly one. No maximality, sofa motion, full-turn assumption, or input regularity is needed.

The result does not exclude edge atoms. That distinction is essential, and an explicit example is included below. The proof is supplied directly through one-dimensional Stieltjes measures; no differentiation of a curvature measure is assumed.

## 59.1 A locality lemma on a level set

Let w be locally semiconvex on an open real interval: on every compact subinterval, its distributional second derivative satisfies w'' >= -C dt for some finite C>=0. In particular w is locally Lipschitz and its one-sided derivatives exist. Fix a number a and let E={t:w(t)=a}.

**Lemma 108 (nonatomic second derivative on a level set).** On E the nonatomic part of w'' is zero. More precisely, except for a countable subset Z of E,

\[
w'_-(t)=w'_+(t)=0,\qquad w''|_{E\setminus Z}=0
\tag{59.1}
\]

as a signed measure. At the exceptional points atoms are not ruled out.

**Proof.** Work on a compact interval inside the domain. Points of the closed set E that are not accumulation points of E on both sides form a countable set: they are isolated points or endpoints of components of its open complement, together with the two interval endpoints. Each complementary component contains a distinct rational number.

At every remaining point, difference quotients along level-set sequences on each side are zero. The one-sided derivatives of a semiconvex function are limits of those quotients, so both are zero. Put G(t)=w'_+(t)+Ct. The distributional derivative dG=w''+C dt is a nonnegative Stieltjes measure, and G is continuous at these remaining points with G(t)=Ct there.

For completeness, if a nondecreasing function G is continuous on a compact set F and agrees with Ct on F, then

\[
dG(F)=C|F|.
\]

For a singleton both sides are zero. Otherwise let l=min(F), r=max(F). The absence of atoms at the endpoints gives dG([l,r])=C(r-l). Every complementary interval (u,v) of F inside [l,r] has endpoints in F and therefore dG((u,v))=C(v-u). Subtract their countable sum. This proves the displayed identity. Apply the same argument to every compact subset of E minus the exceptional points and use inner regularity of the two Radon measures. It follows that dG|_{E\setminus Z}=C dt|_{E\setminus Z}, which is (59.1). A nonatomic signed measure gives zero mass to the countable set Z. QED.

This is not an assertion that w'' vanishes on a neighborhood of E, or that it is an ordinary function. The localization is a restriction of measures to the level set itself.

## 59.2 Apply the lemma to the width of a convex hull

Let K be a compact convex body with nonempty interior. Write h(t) for its support function and sigma=h+h'' for its nonnegative surface-area/curvature measure. Define

\[
w(t)=h(t)+h(t+\pi),\qquad
\nu=\sigma+\sigma^{\pi},
\]

where sigma^pi(A)=sigma(A+pi), with angles interpreted periodically. Distributionally,

\[
w+w''=\nu\geq0.
\tag{59.2}
\]

Since w is bounded, this makes w locally semiconvex. For a finite measure mu, write mu_na for the measure obtained by deleting all its atoms; it retains both the absolutely continuous and singular-continuous parts.

**Theorem 109 (width-level curvature identity).** For any a>0, on E_a={t:w(t)=a},

\[
\boxed{\nu_{\rm na}|_{E_a}=a\,dt|_{E_a}.}
\tag{59.3}
\]

Consequently, at width-one directions,

\[
\boxed{\sigma_{\rm na}|_{\{w=1\}}\leq dt|_{\{w=1\}}.}
\tag{59.4}
\]

In particular, singular-continuous curvature gives zero mass to {w=1}, and the density of the absolutely continuous curvature is at most one almost everywhere on that set.

**Proof.** Apply Lemma 108 to w on finitely many coordinate intervals covering the circle. Outside its countable exceptional set, (59.2) restricted to E_a becomes nu=a dt. Remove atoms on the exceptional set; both the remaining measure and Lebesgue measure give that set zero mass. This proves (59.3). Since nu_na=sigma_na+(sigma^pi)_na and both summands are nonnegative, (59.4) follows. Its two stated consequences follow by the Lebesgue decomposition of sigma_na. QED.

For a body of constant width one, (59.3) reduces to the familiar identity sigma+sigma^pi=dt, with no singular part. Here the width is allowed to equal one on an arbitrary closed set rather than on the whole circle.

## 59.3 Why atoms must not be included

For the unit square, w(t)=|cos t|+|sin t|. It equals one at the four axis normals, and the curvature measure has positive atoms at precisely those directions. Thus sigma|_{w=1}<=dt is false if the word "nonatomic" is removed.

This also shows why a coincident unit-width constraint cannot be declared harmless for an exposed-edge variation. The theorem removes a possible diffuse-measure obstruction, not all normal-cone terms.

## 59.4 Consequence for the structural target

For any maximizing hull, the desired density cap and exclusion of singular-continuous curvature are already true on its width-one directions, independently of maximality. A future variation argument only needs to supply the remaining nonatomic bound away from that set, as well as whatever atomic control is required.

The next note identifies a class of coincident outer/inner-wall contacts that necessarily falls on this width-one set. This is a classification step in the global structural problem; it is not a new proof of unrestricted optimality or uniqueness.

No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. The new assertions are written proofs, subject to independent checking.
