# Ordered horizontal faces: a direct ordinary-area bound

This closes one geometric part of the narrow curvature-dominated case without using the possibly false inequality |S|<=Q_tilde(h_K). If the horizontal face intervals are ordered, meaning r_b<=ell_t or r_t<=ell_b, the entire convex hull has area at most pi/2, strictly below the ambidextrous candidate. Touching endpoints are permitted; a point face lying strictly inside the other interval is not covered by that ordering hypothesis.

The argument uses two containing unit circles and convexity of an elementary corner-area function. No motion, contact-order, or full-turn hypothesis is required. Labels DF1 onward are local to this supplement.

## 1. Unit-circle containment of a quarter flank

Let K be a compact convex body with nonempty interior and vertical span one, between y=0 and y=1. Let its horizontal projection be [x_-,x_+], and let its top and bottom exposed faces be [ell_t,r_t] times {1} and [ell_b,r_b] times {0}. Suppose its curvature measure is dominated by angular Lebesgue measure on the upper-left open quarter.

For 0<=t<=L=pi/2 put g(t)=h_K(L+t). The measure inequality implies g is W^{2,infinity} on the closed quarter in the one-sided-trace sense, with

\[
g(0)=1,\quad g'(0)=-\ell_t,\quad0\leq g''+g\leq1\quad\text{a.e.}
\]

Variation of constants gives

\[
g(t)=\cos t-\ell_t\sin t+\int_0^t\sin(t-s)\rho_g(s)ds
\leq1-\ell_t\sin t.
\tag{DF.1}
\]

The right side is the support of the closed unit disk centered at (ell_t,0) in the normal direction (-sin(t),cos(t)). For a point (x,y) in K with x<=ell_t and y>=0, choose the normal parallel to (x-ell_t,y) when that vector is nonzero. It belongs to this closed quarter. Inequality (DF.1) implies

\[
\boxed{(x-\ell_t)^2+y^2\leq1.}
\tag{DF.2}
\]

At the zero vector the inequality is immediate. Endpoint directions are included by continuity. Thus the upper hull graph on x_-<=x<=ell_t is at most sqrt(1-(x-ell_t)^2), and ell_t-x_-<=1.

Reflecting both coordinates gives the companion assertion at the right endpoint r_b of the bottom face: if the lower-right curvature is dominated, then for points of K with x>=r_b,

\[
\boxed{(x-r_b)^2+(y-1)^2\leq1.}
\tag{DF.3}
\]

Hence the lower hull graph there is at least 1-sqrt(1-(x-r_b)^2), and x_+-r_b<=1.

These are one-sided flank containments, not a claim that one unit disk contains the entire body. Axis curvature atoms are allowed and determine the chosen face endpoints.

## 2. Two opposite corner losses

Define, for 0<=s<=1,

\[
G(s)=\int_0^s(1-\sqrt{1-u^2})du
=s-\frac12\left(s\sqrt{1-s^2}+\arcsin s\right).
\tag{DF.4}
\]

This function is nonnegative, increasing, and convex: G'(s)=1-sqrt(1-s^2) is nonnegative and increasing. Set

\[
W=x_+-x_-,\quad l=\ell_t-x_-,\quad r=x_+-r_b.
\]

The two containments yield

\[
\boxed{|K|\leq W-G(l)-G(r).}
\tag{DF.5}
\]

To justify the addition even when the horizontal intervals overlap, write the area deficit from the width-W, height-one rectangle as

\[
W-|K|=\int_{x_-}^{x_+}(1-t_K(x))dx+
\int_{x_-}^{x_+}b_K(x)dx.
\]

The first integral includes the upper-left loss at least G(l); the second includes the lower-right loss at least G(r). They are distinct vertical losses. No removed region is counted twice: the convex hull has b_K<=t_K on its full projection.

## 3. A complete exclusion for ordered horizontal faces

**Theorem DF1 (ordered-face area bound).** Suppose the curvature of K is dominated by dtheta on all four open coordinate quarters and its face endpoints satisfy

\[
r_b\leq\ell_t\quad\text{or}\quad r_t\leq\ell_b.
\]

Then W<=2 and

\[
\boxed{|K|\leq
\frac W2\sqrt{1-\frac{W^2}{4}}+\arcsin\frac W2
\leq\frac\pi2.}
\tag{DF.6}
\]

In particular any sofa contained in K has area strictly below M_A.

**Proof.** After a horizontal reflection if necessary, ell_t>=r_b. This includes touching intervals and ordered single-point faces. Then

\[
l+r=W+\ell_t-r_b\geq W.
\]

Since each of l,r is at most one by (DF.2)–(DF.3), W<=2. Monotonicity and convexity of G give

\[
G(l)+G(r)\geq2G((l+r)/2)\geq2G(W/2).
\]

Insert this in (DF.5) and simplify using (DF.4). If u=W/2, the derivative of u sqrt(1-u^2)+arcsin u is 2sqrt(1-u^2)>=0 on [0,1]; its value at one is pi/2. This proves (DF.6).

Finally pi/2<11/7<8/5<M_A, using pi<22/7 and the candidate lower bound proved in Note 10. The horizontal reflection proves a geometric inequality invariant under reflection; no reflection is inserted into a sofa's physical motion. QED.

## 4. Effect on the closure route

The earlier narrow counterexample has ordered top and bottom faces and is covered by DF1. Its positive functional-enclosure error is therefore harmless for proving area below M_A: the hull itself is too small. We do not attempt to make its false enclosure inequality true.

Together with CW4, DF1 removes two cases **conditional on curvature domination**:

- W>=2: the existing wide-hull theorem gives the sharp comparison and equality case;
- ordered top/bottom faces: the direct hull estimate gives the strict pi/2 bound, without even needing full turns.

The still-unsettled curvature-dominated case has W<2 and face intervals not satisfying the ordering alternative. These can overlap or one can be a point strictly inside the other. The general problem also still includes curvature violations. Neither issue is claimed resolved by this flank-area estimate.

The quantitative profile gap in the width-certificate note supplies one possible error budget for the remaining narrow case. DF1 instead gives a proved ordinary-area exclusion for an entire geometric class. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
