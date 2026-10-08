# 15. Unit incoming span can be achieved by reorientation, not dilation

This note closes another normalization issue left in Theorem 30. A body of area greater than one can be reoriented, through poses lying entirely in the incoming arm, to have vertical span exactly one. The same initial reorientation works for both turning witnesses. It does not force either final turning angle to be a quarter turn.

## 15.1 A rotation inside the incoming arm

Assume S is in the common incoming pose supplied by Proposition 14, so S is a compact subset of H_0. Let K=conv(S), with vertical width w_K(e_y)<=1. For a proper rotation R_theta put

\[
v(\theta)=w_{R_\theta K}(e_y).
\]

This function is continuous by support continuity.

**Theorem 38 (unit-span representative).** If |S|>1, then S is congruent to an ambidextrous body S_* whose common incoming vertical span is exactly one. The congruence and its reversal can be performed inside the incoming arm before either turn.

**Proof.** If v(0)=1 there is nothing to do. Otherwise v(0)<1. Since K lies in a rectangle of its horizontal and vertical widths,

\[
|S|\leq|K|\leq w_K(e_x)w_K(e_y),
\]

so w_K(e_x)>1. Therefore v(pi/2)>1. Let theta_* be the first theta in [0,pi/2] for which v(theta)=1. By continuity, v(theta)<=1 throughout [0,theta_*].

For these angles define the continuously varying translation

\[
a_x(\theta)=1-\max_{p\in R_\theta S}p_x,
\qquad
a_y(\theta)=-\min_{p\in R_\theta S}p_y.
\]

Then \(R_\theta S+a(\theta)\subseteq H_0\): its rightmost x-coordinate is one, its bottom y-coordinate is zero, and its height is v(theta)<=1. All extrema vary continuously with theta, so this is a continuous proper motion in H_0. First join the given incoming pose to S+a(0) by a translation; the joining segment of poses remains in H_0 by convexity, just as in Proposition 14.

Set \(S_*=R_{\theta_*}S+a(\theta_*)\). To turn S_* in either direction, first reverse this in-arm motion to the original S and then follow the original witness. Both new witnesses start at the same S_* orientation and use only proper motions. They preserve area and connectedness. The chosen representative has height exactly one. QED.

This is not an anisotropic scaling argument. No assertion is made that stretching a sofa vertically preserves feasibility.

## 15.2 Consequence for the common-hull program

Every body that could equal or beat M>8/5 has a congruent representative with

\[
h_K(\pi/2)=1,\qquad h_K(3\pi/2)=0.
\]

Apply support tightening and angle erasure to its new two witnesses, then use the wrong-way exclusion. The separated common-hull reduction of Theorem 30 therefore covers all competitive bodies with the exact vertical normalization used by the quadratic calculations in Notes 12–14.

The endpoint angles alpha,gamma still belong to (0,pi/2] and may be partial turns. Reorientation may change those endpoint angles, and nothing in the proof identifies them with pi/2.

## 15.3 An attempted stronger normalization, and why the argument stops

It is tempting to choose an extreme orientation among all directions in which K fits a unit strip, and claim that a partial turn would contradict that extremality. This does not follow from Theorem 38: the reorientation path must stay inside a connected component of the allowed strip-orientation set. The set of all allowed orientations need not be connected.

Here is an exact counterexample to the proposed **width-only inference**. Let K be the diamond with vertices

\[
(\pm7/2,0),\qquad(0,\pm101/200).
\]

Its width in a direction making an angle delta with the vertical is

\[
w(\delta)=\max\{(101/100)|\cos\delta|,\ 7|\sin\delta|\}.
\]

The vertical direction has width 101/100>1. But at
\(\delta_0=\arccos(100/101)\),

\[
(101/100)\cos\delta_0=1,
\qquad 7\sin\delta_0=7\sqrt{201}/101<1,
\]

since \(49\cdot201=9849<10201=101^2\). There are therefore permitted strip orientations on both sides of the forbidden vertical interval, giving distinct components. The diamond has area 707/200, so a high-area condition alone does not repair this width-only argument.

This diamond is **not claimed to be a feasible sofa**; in fact its large area is a warning not to confuse strip feasibility with corner feasibility. The example isolates the precise logical gap: a proof of full-angle reduction would need more of the moving-sofa geometry than continuity of widths and the two-strip bound.
