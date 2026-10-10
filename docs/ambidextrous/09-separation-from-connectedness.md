# 9. Niche separation follows from connectedness in the conventional angle sectors

This is a stronger geometric advance than the candidate-specific height estimate in Note 4. For correctly signed angular sectors, the two niches are vertically one-sided. Their overlap over the horizontal projection of a connected sofa is impossible. No injectivity, uniform corner-height bound, symmetry, or maximizing assumption is needed.

**Scope restriction:** the lower-turn hallway uses dual angles in [0,pi/2], and the upper-turn hallway uses dual angles in [-pi/2,0]. Theorem 21 does not yet prove that arbitrary two-turn witnesses can be put into these signs. This restriction must remain visible in every use of the result.

## 9.1 A topological separation lemma

Call an open set D vertically downward closed if
\((x,y)\in D\) implies \((x,y-s)\in D\) for every s>=0. Define upward closed similarly.

**Theorem 24 (vertical barrier).** Let S be a nonempty compact connected subset of the plane. Let D be open and downward closed and let U be open and upward closed, with \(S\cap(D\cup U)=\varnothing\). If I is the horizontal projection of S, then

\[
(D\cap U)\cap(I\times\mathbb R)=\varnothing.
\tag{9.1}
\]

**Proof.** The continuous image I of connected S is an interval; compactness makes it the closed interval between the minimum and maximum x-coordinates of S. If (x,y) lies in both D and U, downward closure puts the whole vertical half-line below it in D, and upward closure puts the half-line above it in U. Consequently the entire vertical line at x is forbidden. But x in I means that this line contains a point of S, a contradiction. QED.

In fact the argument only requires every x in I to occur in S; connectedness is what guarantees the interval needed below. The statement is about overlap over the actual horizontal projection, not about niches everywhere in the plane.

## 9.2 Why the two swept niches have the required direction

In the common-hull notation of Note 8, a forbidden quadrant has inequalities

\[
p\cdot u(t)<h_K(u(t))-1,\qquad
p\cdot v(t)<h_K(v(t))-1.
\tag{9.2}
\]

For the lower turn with t in [0,pi/2], \(u_y=\sin t\geq0\) and \(v_y=\cos t\geq0\). Decreasing the y-coordinate of a forbidden point preserves both strict inequalities. Each quadrant, and hence their union W_-, is downward closed.

For the upper turn with t in [-pi/2,0] and handedness sigma=-1, \(u_y=\sin t\leq0\), \(v_y=-\cos t\leq0\). Increasing y preserves both inequalities. Its union W_+ is upward closed.

The same observation works for noncanonical corner placements in these sectors; support tightening is not used to prove vertical monotonicity. The common-hull reduction is useful to make the relevant outer set's horizontal projection equal to that of S.

**Corollary 25 (disjoint niches inside the common hull).** Suppose S has canonical witnesses in the two conventional sectors, let K=conv(S), and set

\[
N_-=K\cap W_-,\qquad N_+=K\cap W_+.
\]

Then

\[
N_-\cap N_+=\varnothing.
\tag{9.3}
\]

**Proof.** Canonical feasibility says S avoids both sweeps. The horizontal projections of S and K are equal because that of S is already an interval. Apply Theorem 24. QED.

This is exact set disjointness for the open forbidden sweeps, not just zero area overlap. Their closures may touch. It does not assert a common **horizontal** separator: the available separating height can vary with x.

## 9.3 The entire canonical envelope is now connected

**Theorem 26 (vertically convex connected saturation).** Under the hypotheses of Corollary 25, the full canonical envelope

\[
E_K=K\setminus(W_-\cup W_+)
\]

is compact, connected, feasible for both canonical motions, contains S, and has convex hull K. Every nonempty vertical section of E_K is a closed interval, and there is such a section at every x in I.

**Proof.** At a fixed x the section of K is a closed interval. The section of W_- is either empty, all of the line, or an open downward half-line; the section of W_+ has the corresponding upward form. Removing these sets from the section of K leaves a closed interval or the empty set. It is not empty for x in I, since it contains the section of S. No points of K occur outside I.

The set E_K is compact because K is compact and the sweeps are open. To prove connectedness, suppose it is a union of two disjoint nonempty relatively closed sets A and B. They are compact. No vertical section can meet both A and B, since that section is an interval and would then be separated by its intersections with A and B. Hence the compact horizontal projections of A and B are disjoint, nonempty, and have union I. This separates the interval I, a contradiction.

Feasibility follows from all canonical outer inequalities on K and exclusion from the forbidden quadrants, with the endpoint widths from Lemma 20. Finally \(S\subseteq E_K\subseteq K=\operatorname{conv}(S)\) gives \(\operatorname{conv}(E_K)=K\). QED.

Thus the extra-component relaxation warned about in Note 6 is absent in this sector after common-hull tightening. It can still occur for arbitrary witness boxes, other angular signs, or convex sets not arising as the hull of a feasible connected body.

## 9.4 A slice formula and an exact full-niche area identity

For x in I define extended-real thresholds

\[
f(x)=\sup\{y:(x,y)\in W_-\},\qquad
g(x)=\inf\{y:(x,y)\in W_+\},
\]

with f=-infinity for an empty lower section and g=+infinity for an empty upper section. Neither section is the whole line at x in I. Write the section of K as \([b_K(x),t_K(x)]\). Theorem 24 gives f(x)<=g(x), and the surviving section is exactly

\[
(E_K)_x=
[\max\{b_K(x),f(x)\},\ \min\{t_K(x),g(x)\}].
\tag{9.4}
\]

The endpoints are in the indicated order because the section contains a point of S. In particular the formula needs no positive-part correction for an empty section. Fubini, or simply disjoint subtraction, gives

\[
\boxed{|E_K|=|K|-|N_-|-|N_+|.}
\tag{9.5}
\]

The thresholds are measurable: for example {x:f(x)>a} is the union over rational q>a of the open horizontal sections {x:(x,q) in W_-}. Thus the corresponding slice integrals are well-defined.

Equation (9.5) is precisely the double subtraction that was invalid without disjointness in Note 2. The missing sign justification is now supplied for the stated sector. Therefore **full-niche** lower bounds a<=|N_-| and b<=|N_+| give the valid majorant

\[
|E_K|\leq |K|-a-b.
\tag{9.6}
\]

Clipping at a fixed midline is no longer necessary on this route. The full-niche bounds still have to be constructed; a signed sweep integral is not automatically a niche-area lower bound.

## 9.5 What this closes, and what it does not

Proved here, in the conventional sectors:

- universal separation of the two niches over the actual hull;
- connectedness of the entire canonical saturated envelope;
- reduction to vertically convex bodies and an exact full-niche objective.

Not proved here:

- reduction of every unrestricted two-turn body to these angular signs;
- extension of partial turns to full quarter turns;
- injectivity or multiplicity control for either sweep;
- a sharp global bound on the common-hull full-niche objective;
- regular closedness of arbitrary saturated envelopes.

The proof works for partial conventional angles as well as full quarter turns. Therefore it is worth retaining variable endpoint angles rather than assuming full turns just to obtain separation.

The strict horizontal separation margin at Romik's candidate remains useful for perturbations, but it is no longer the only available separation statement. The global topological result uses connectedness where the candidate calculation used explicit height inequalities.
