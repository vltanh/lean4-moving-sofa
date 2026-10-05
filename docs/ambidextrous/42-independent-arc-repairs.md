# 42. Independent arc repairs: a nonsymmetric local theorem without a curvature cap

The repair is not limited to the symmetric one-quarter example. It can be performed independently on all four open quarters, provided the perturbations stay away from the candidate's axis normals and contact-switching angles. This note records the exact gain for the second wall family and proves the resulting local theorem.

The fixed-junction-neighborhood restriction remains substantive. This is not an unrestricted local optimality theorem in Hausdorff distance, nor a reduction of an arbitrary global maximizer to the candidate neighborhood.

## 42.1 The analogous repair for g

For the L wall set

\[
s=\tan t,\qquad\psi(s)=\frac{1-g(t)}{\cos t}.
\]

Then L_t(x)=s x-psi(s), and

\[
\psi'(s)=D_x(t),\qquad
\psi''(s)=(1-\rho_g(t))\cos^3t.
\tag{42.1}
\]

Replace psi on a compact interior interval by its greatest convex minorant and set

\[
g_c(t)=1-\cos t\,\psi_c(\tan t),\qquad v=g_c-g\geq0.
\]

The proof of Lemma 79, with sine and cosine interchanged, gives endpoint agreement, C^1 control, and 0<=rho_g,c<=1. The supremum of the L family is unchanged.

Changing g by v changes c by v nu and p by -v, so B=c+p nu is unchanged identically. On a standard corner arc, the niche-area increment is -integral p v plus one half of integral v^2. Thus a single-half g repair in the middle contact regime gives

\[
\Delta |E|=\int(1+p-v)v\,dt+\tfrac12\int v'^2\,dt.
\tag{42.2}
\]

There is no factor two here: the reflected half need not be changed along with it. The corresponding one-half f formula is

\[
\Delta |E|=\int(1-q-u)u\,dt+\tfrac12\int u'^2\,dt,
\tag{42.3}
\]

where u=f_c-f. These follow by the same support-area expansion and integration by parts as Lemma 80.

## 42.2 A repair on a side-only contact arc

The candidate's first f phase has zero curvature, its last g phase has zero curvature, and its other side-only phases have positive curvature. On a protected last-phase f interval (b,L), p<0 and q<0: only the R tangency family participates there, not the corner roof. An f repair preserves that R supremum and fixes D, so neither niche changes on that interval. Its hull gain is

\[
\Delta|E|=\int(1-u/2)u\,dt+\tfrac12\int u'^2\,dt.
\tag{42.4}
\]

The identical expression with v holds for a g repair on a protected first-phase interval (0,beta), where p>0 and q>0 and only the L tangency family participates.

For example, to obtain (42.4) expand the one-half hull area as integral rho_f u plus one half of integral (u^2-u'^2), then use u''+u=1-rho_f wherever u>0. No corner term is subtracted in this phase. Counting a middle-phase q term here would be incorrect.

## 42.3 Perturbations strictly inside a zero-curvature phase vanish

**Lemma 82 (zero-curvature interval test).** Let J have length less than pi. Suppose delta is C^2, vanishes near the endpoints of J, and delta''+delta>=0. Then delta=0.

**Proof.** Let m be the midpoint of J. The function cos(t-m) is strictly positive on J and solves w''+w=0. Twice integrating by parts gives

\[
\int_J(\delta''+\delta)\cos(t-m)\,dt=0,
\]

because delta and its first derivative vanish at the endpoints. The nonnegative integrand must vanish, so delta''+delta=0. The zero endpoint data then give delta=0. QED.

Therefore a convex support perturbation supported strictly inside a candidate zero-curvature phase cannot create a new arc while keeping both ends and their tangent traces fixed. The relevant protected repairs occur only in the positive-curvature phases.

## 42.4 The four-half protected neighborhood

Choose finitely many disjoint closed angle windows, each with a slightly larger disjoint buffer window, strictly inside the candidate's phase intervals and away from 0,beta,b,L. Allow independent C^2 perturbations of f and g on the upper half and of their reflected-coordinate counterparts on the lower half, supported in the smaller windows. They are not required to be reflections of each other. Assume the resulting global support function h is convex and its quarterwise C^1 displacement from h_* is sufficiently small.

The axis values and one-sided derivatives are unchanged, so the common top and bottom exposed faces remain [ell,r]. Each modified quadrant has the candidate's strict positive-height/baseline-intercept margins on its compact angular window. All changes therefore remain inside the retained central rectangle, and the two sweeps stay strictly separated. The full envelope E_h is connected, feasible, and retains hull h.

The hybrid roof verification of Section 41.3 extends as follows. B depends only on f and D only on g. Any changed B parameter lies in (beta,L), where its candidate abscissa is strictly between x_a=c_x(beta) and r. Any changed D parameter lies in (0,b), where its abscissa is strictly between ell and x_b=c_x(b). These inequalities persist in the buffered windows, even if their abscissae develop folds. Outside those windows the relevant candidate paths are unchanged. Hence the right roof is the R supremum, the left roof is the L supremum, and the middle is the standard decreasing corner graph, exactly as in Note 41.

Perturbations of the unused zero-curvature phases vanish by Lemma 82. The contact signs and switches are unchanged because the perturbations vanish near the switches and remain C^1-small elsewhere.

## 42.5 Sequential repair and strict improvement

Convexify each modified f or g wall obstacle in its buffered window. Perform the finitely many repairs successively, on the upper and lower halves independently. Each operation is C^1-continuous at the candidate by Lemma 79, so choosing the original perturbation sufficiently small ensures that all intermediate hulls retain the preceding strict margins.

The candidate satisfies q_*<1 and p_*>-1 on its middle phase. There is therefore a common eta>0 for the fixed windows such that every repair gain in (42.2)–(42.4) is at least

\[
\eta\int w\,dt+\tfrac12\int w'^2\,dt,
\tag{42.5}
\]

where w is its nonnegative support increase. The other wall family's envelope is fixed algebraically, and the family being convexified has unchanged supremum. The only changing niche term is the explicitly counted middle corner, when present. Thus these are gains of **actual feasible bodies**, not just gains of the formal functional.

The final hull has curvature between zero and one on every open quarter. Its contact inequality p<q persists by C^1 smallness relative to the candidate's uniform positive gap. Theorem 65 now applies to its feasible canonical envelope.

**Theorem 83 (independent protected-arc optimality).** Every convex support perturbation in Section 42.4 satisfies

\[
|E_h|\leq M,
\]

with equality exactly when h=h_*. If w_j are its successive repair increments, then

\[
M-|E_h|\geq
\sum_j\left(\eta\int w_j+\tfrac12\int w_j'^2\right).
\tag{42.6}
\]

In particular a perturbation with excessive curvature in any protected window is strictly suboptimal.

**Proof.** Sum the actual gains (42.5), then apply Theorem 65 to the repaired hull. If any repair is nonzero, the gain is strictly positive. If all are zero, the original hull already lies in that theorem's class; its equality case is a horizontal translate of h_*. The unchanged axis values force the translation to vanish. QED.

For any closed connected body S following the same canonical full turns and with this hull, S is contained in E_h, so the same area bound follows. At equality E_h is the candidate and is regular closed, and Lemma 4 yields exact equality of S with it.

## 42.6 The remaining boundary of this local result

The theorem allows independent, nonsymmetric, high-frequency changes and imposes no upper bound on the original curvature in the protected windows. It therefore goes beyond the earlier curvature-assumed theorem in a genuine geometric neighborhood.

It still fixes neighborhoods of the switching and axis normals and requires C^1 proximity to the candidate. Perturbations that move a switching region, change a face trace, produce clipping or contact between the two niches, or use partial endpoint angles require a separate argument. Nor has every global maximizer been placed in this neighborhood. Those are unproved extensions, not consequences of the repair formula.
