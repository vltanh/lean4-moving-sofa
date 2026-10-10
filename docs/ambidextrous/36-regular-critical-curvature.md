# 36. Curvature excess is confined to endpoint degeneracies at a regular critical point

This is a maximality-based calculation, unlike the false high-area curvature reduction refuted in Note 28. Under an explicitly stated regular-contact variation hypothesis it derives the curvature cap in the interior-contact case, without assuming that cap or p<=q. It also identifies the exceptional endpoint behavior rather than silently removing it.

The hypothesis has not been proved for every unrestricted maximizer or for the selected polygonal limit. Therefore this is not the missing unrestricted structural theorem.

## 36.1 Precisely which regular variation is assumed

Consider a full-turn unit-span common hull K with quarter functions f,g that are C^2, so rho_f,rho_g are continuous and nonnegative. Use p,q from Note 35. Suppose its lower positive-height niche roof admits a finite collection of stable contact charts of these types:

- nondegenerate single-wall tangencies R or L, with strictly smaller companion height;
- transverse standard or reverse corner graphs, with nonzero horizontal derivative.

Chart interiors are disjoint in x; they cover the roof except for finitely many joins. Parameter intervals within each type have disjoint interiors. No positive-length coincident-contact segment, clipping loss, or motion of the outer horizontal face intervals is included. Joins are assumed to match continuously and to vary differentiably under the considered perturbations.

For compactly supported changes of f alone in an interval where rho_f>0, and of g alone where rho_g>0, assume the perturbed support functions remain feasible two-turn common hulls, that the chart description persists, and that the surviving body area is hull area minus the two unchanged-in-topology niche areas. The reflected half is fixed when the upper half is varied. Finally assume this actual area has a local maximum at the original hull for both signs of each such perturbation.

These assumptions can, for example, be verified locally in a separated, unclipped, strictly feasible contact configuration. They are not consequences of compactness or of a formal Euler equation. A proof of their applicability to arbitrary maximizers remains necessary.

## 36.2 The correct balance equations

For almost every t, let b(t),d(t) be the indicators that this parameter supplies an R-tangency chart or an L-tangency chart. Let chi(t)=1 for an active standard corner, -1 for a reverse corner, and 0 otherwise. An angle can supply both a corner and a separate tangent point; b,d,chi are not mutually exclusive.

The first-variation formulas (35.6)–(35.7), and the support-area derivative, give

\[
\begin{aligned}
\delta|E|=\int_0^L\bigl[&\rho_f-b(1-\rho_f)-\chi q\bigr]v\,dt\\
+\int_0^L\bigl[&\rho_g-d(1-\rho_g)+\chi p\bigr]w\,dt.
\end{aligned}
\tag{36.1}
\]

The moving chart endpoints cancel because adjacent roof values agree. The upper niche is unchanged under an upper-half support variation. For the hull term, differentiation of one half of integral (h^2-h'^2) and integration by parts gives integral rho times the support perturbation.

**Lemma 72 (regular critical-point equations).** Under Section 36.1,

\[
(1+b)\rho_f=b+\chi q\quad\text{a.e. where }\rho_f>0,
\]

\[
(1+d)\rho_g=d-\chi p\quad\text{a.e. where }\rho_g>0.
\tag{36.2}
\]

**Proof.** Apply local maximality to both signs of every compactly supported test function in each positive-curvature open set. The coefficient of that test function in (36.1) must vanish as a distribution, hence almost everywhere. No equation is asserted on a zero-curvature interval where both signs may violate convexity. QED.

If chi=1, these equations include the candidate's familiar possibilities rho=1/2, rho_f=(1+q)/2, and rho_g=(1-p)/2. They also explicitly allow an inactive tangency, in which case rho_f=q or rho_g=-p. Omitting the inactive case would assume the curvature conclusion in the derivative calculation.

## 36.3 A maximum principle for curvature excess

The kinematic identities, valid independently of maximality, are

\[
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p.
\tag{36.3}
\]

**Theorem 73 (regular critical curvature cap, with endpoint exceptions).** Under Section 36.1:

(a) every connected component of {rho_f>1} must begin at t=0. On any such component,

\[
p(t)=-t,\qquad\rho_f(t)=q(t)>1,
\qquad q'\leq-1/2\quad\text{a.e.},
\tag{36.4}
\]

and necessarily p(0)=0;

(b) every connected component of {rho_g>1} must end at t=L. On it,

\[
q(t)=L-t,\qquad\rho_g(t)=-p(t)>1,
\qquad p'\leq-1/2\quad\text{a.e.},
\tag{36.5}
\]

and necessarily q(L)=0.

In particular, if p(0)>0 and q(L)<0, then rho_f,rho_g<=1 on the whole quarter.

**Proof of (a).** On an open component J with rho_f>1, Lemma 70 excludes an R tangency, so b=0 almost everywhere. Equation (36.2) gives rho_f=chi q. The choice chi=0 is impossible. The reverse choice chi=-1 would give rho_f=-q<1 by the positive-height strip estimate (35.4), also impossible. Thus chi=1, p<0<q, and rho_f=q throughout J except possibly a measure-zero set. Continuity extends the equality and the weak sign bounds.

If rho_g>0, its balance equation gives rho_g=(d-p)/(1+d), hence

\[
q'=\frac{p-1}{1+d}\leq-1/2.
\]

If rho_g=0, (36.3) gives q'=p-1<=-1. Thus q, and therefore rho_f, is strictly decreasing on J. A component with a left endpoint a>0 would have rho_f(a)=1 by continuity and could not increase above one immediately to its right. Hence J starts at zero. On J the first identity in (36.3) gives p'=-1.

The support contact at the rightmost normal has y-coordinate f'(0)=p(0), which is nonnegative because K lies in the incoming strip. Standard corner signs give p(t)<=0 as t decreases to zero, so p(0)=0. Therefore p(t)=-t. This proves (a).

**Proof of (b).** If rho_g>1, Lemma 70 gives d=0. Equation (36.2) and the reverse-corner strip estimate force chi=1 and rho_g=-p. If rho_f>0, its balance equation gives p'=-(1+q)/(1+b)<=-1/2; if rho_f=0, then p'=-1-q<=-1. Thus rho_g=-p increases strictly and the component can only end at L. Equation (36.3) gives q'=-1 there.

The leftmost upper support contact has y-coordinate -g'(L)=-q(L)>=0, so q(L)<=0. Standard corner signs imply q(L)>=0. Thus q(L)=0 and q(t)=L-t. QED.

The result applies independently to the reflected half when it satisfies the same variation hypotheses. The endpoint inequalities have a geometric meaning: the relevant extreme support contacts lie strictly above the incoming bottom wall, and their reflected counterparts strictly below the top wall.

## 36.4 What this advances

Excess curvature at a regular critical point is not just "a wall might be inactive." If it is inactive, its corner must be active; the critical equations then force the excess to decrease towards the interior. A new excess interval cannot start in the interior. Reverse corners cannot carry excess curvature because their strip geometry bounds the relevant contact distances below one.

Thus the general curvature task separates into concrete issues:

- obtain a justified variation/contact-measure statement for arbitrary maximizing hulls, including atoms and degenerate contacts;
- control the endpoint case in (36.4) or (36.5), or prove strict interior placement of those support contacts;
- derive the separate contact-order condition needed by Theorem 65 and handle partial endpoint angles.

The new theorem does not resolve these by assuming ordinary monotone velocities or the candidate's contact pattern. Its actual regularity and admissibility assumptions remain listed in Section 36.1.
