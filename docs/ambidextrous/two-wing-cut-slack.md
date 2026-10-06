# Cut slack: independent inward vertices, not an assumed membership

This advances roadmap gate R4. The old inward-point requirement is stronger than equality of two directional widths. This note separates those conditions, proves a completion using the actual inward supporting lines, and computes the exact first variation of the resulting functional. The following quadratic note closes the sharp comparison when both wings span the common strip. Admission of every maximizing sofa remains unproved.

The baseline is TW/WS/WC at `f6a06be`. Labels CS are local. The candidate constants and wing curvatures are the explicit reference data of TW.6 and WC.1, not an assumption of unrestricted optimality.

## 1. The relaxed data and four genuine slacks

Keep the common strip 0<=y<=1, compact nonempty convex wings R,D, and every width inequality TW.1. Delete Q_R in R and Q_D in D. Retain the outward intersections P_R,P_D of TW.2, but replace the two inward points by the intersections of the **actual inward supporting lines**:

$$
I_R=\left(-\frac{r(\pi-\beta)+r(\pi+\beta)}{2c},
\frac{r(\pi-\beta)-r(\pi+\beta)}{2s}\right),
$$
$$
I_D=\left(\frac{d(\beta)+d(-\beta)}{2c},
\frac{d(\beta)-d(-\beta)}{2s}\right),
\qquad c=\cos\beta,\ s=\sin\beta.
$$

Define

$$
\epsilon_R^+=1-w_R(\beta),\quad
\epsilon_R^-=1-w_R(-\beta),\quad
\epsilon_D^+=1-w_D(\beta),\quad
\epsilon_D^-=1-w_D(-\beta).
\tag{CS.1}
$$

Every epsilon lies in [0,1]. Nonnegativity follows from the directional-width constraints (using pi-periodicity of width); the upper bound follows from nonnegativity of width. Direct subtraction gives

$$
I_R=Q_R+\left(\frac{\epsilon_R^++\epsilon_R^-}{2c},
\frac{\epsilon_R^+-\epsilon_R^-}{2s}\right),
$$
$$
I_D=Q_D-\left(\frac{\epsilon_D^++\epsilon_D^-}{2c},
\frac{\epsilon_D^+-\epsilon_D^-}{2s}\right).
\tag{CS.2}
$$

Thus scalar width deficits alone do not describe the old missing membership. Even when all deficits are zero, an inward supporting-line intersection can be outside its wing: a radius-one-half disk has width one everywhere, but its two supporting lines at pi-beta and pi+beta meet at distance 1/(2c)>1/2 from its center.

## 2. Complete the actual corners without altering constrained supports

**Lemma CS1 (two-sided angular completion).** Each wing can be enlarged by adding its actual outward and inward intersections and taking the convex hull. This stays in the common strip, changes support only inside the two open horizontal-normal gaps, and preserves every width in TW.1. The support on each gap becomes harmonic, namely the scalar product with its corresponding vertex. The core support functions in TW.3 are unchanged.

**Proof.** For supporting lines with normals theta_0-beta and theta_0+beta, intersect them at P. Their two exposed points show that P is dominated by an old support point in every direction outside the intervening open normal gap: each difference is a signed tangent vector, and its scalar products have the required sign on the corresponding half-circle. Inside the gap, positive sine interpolation of the two supporting inequalities bounds every old point by P. This proves the support assertion, as in TW1, without requiring P to have belonged to the old body.

For either gap centered on a horizontal normal, the two linear forms whose maxima define the intersection's ordinate differ by 2s times the ordinate of a point of the old wing. That difference is in [0,2s]. The difference of the two maxima is also in this interval; hence P has ordinate in [0,1]. Both completions stay in the strip. The two open gaps are disjoint, and neither contains a normal appearing in TW.1 or its opposite, so all constrained widths and all core supports are unchanged. The two completions commute. QED.

This is an auxiliary-body enlargement, not a claim about a feasible motion of the enlarged wings. Its only use after an ordinary-area comparison is that the wing areas increase while the core terms stay fixed.

## 3. Functional with the actual inward corners

Let z_-,z_+ be exactly the curves in TW.3. Define

$$
\begin{aligned}
\widehat{\mathcal W}(R,D)={}&|R|+|D|-I(z_-)+I(z_+)\\
&+\tfrac12\det(I_R,z_+(\beta)-z_-(\beta))\\
&+\tfrac12\det(I_D,z_-(b)-z_+(b)),\qquad b=\pi/2-\beta.
\end{aligned}
\tag{CS.3}
$$

Replacing Q by I is part of the new definition, not a proof that the old functional works on a larger domain. CS.2 gives their exact difference. CS1 increases this new functional by exactly the sum of the two gained wing areas: all its other data remain unchanged.

For geometric admission, join I_R to the lower core, then to I_D, then along the upper core back to I_R. If this is a simple clockwise boundary and the proposed body lies in the union of its bounded region and the two wings, Green's formula and subadditivity of area give

$$
|S|\leq\widehat{\mathcal W}(R,D).
\tag{CS.4}
$$

Pairwise disjoint interiors are sufficient for equality but are **not needed for this upper inequality**. Clockwise simplicity and containment, or a separately proved substitute, are still required. A nonsimple signed curve is not silently treated as an area.

## 4. The endpoint work is favorable, but half as large

For the candidate pair the old and actual inward points agree. Let mu(t)=1-rho(min(t,pi-t)) be the positive reference density from WC.1; in particular mu>1/8. Its two inward cut atoms on each wing have length tan(beta).

**Lemma CS2 (first variation on relaxed cut data).** The derivative at the reference pair is

$$
\boxed{
D\widehat{\mathcal W}_*[\delta]
=\sum_{B=R,D}\int_\beta^{\pi-\beta}\mu(t)[w_B(t)-1]dt
-\frac{\tan\beta}{2}
(\epsilon_R^++\epsilon_R^-+\epsilon_D^++\epsilon_D^-).
}
\tag{CS.5}
$$

This is an exact first variation along Minkowski interpolation, not a statement that the nonlinear remainder has a sign.

**Proof.** The interior support/curve terms are unchanged from WC1; their paired coefficients are mu. At the right candidate cut, write I_* for the inward point. The explicit endpoint identities are

$$
z_-(\beta)-I_*=-\tan\beta\,n'_\beta,
\quad z_+(\beta)-I_*=\tan\beta\,n'_{-\beta},
\quad z_+(\beta)-z_-(\beta)=(0,2s).
$$

Integration by parts in the two curve integrals, followed by differentiation of the cut determinant, gives the right endpoint contribution

$$
\frac{\tan\beta}{2}
[\delta r(\beta)+\delta r(-\beta)
-\delta r(\pi+\beta)-\delta r(\pi-\beta)].
$$

Here the sign of the inward terms follows from delta I_R,x=-(delta r(pi+beta)+delta r(pi-beta))/(2c). The two reference cut atoms add tan(beta) times the sum of those inward support differences. Their total is therefore tan(beta)/2 times the sum of the two width differences, or -tan(beta)(epsilon_R^++epsilon_R^-)/2. Reflect horizontally for the left wing. The strip density terms and these four endpoint terms give CS.5. QED.

The factor one half matters: reusing the old cut-width cancellation would give an incorrect coefficient once the inward vertex moves independently.

## 5. Exact status of the extension

The new domain removes the inward membership and cut-width equalities. The next note [two-wing-slack-quadratic.md](two-wing-slack-quadratic.md) proves its sharp maximum under the additional requirement that **each wing touches both boundaries of the common strip**. That requirement is automatic for the reference wings, not for arbitrary canonical pieces of an unrestricted body.

The general unequal-height case and the ordinary-area admission CS.4 remain roadmap tasks. A negative quadratic term by itself will not disprove the calibration: the nonnegative linear width slack in CS.5 must be retained.

No CI or Lean/Lake compilation is used. These are written arguments with self-review; the accompanying symbolic check concerns the explicit finite algebra, not unrestricted geometric admission.
