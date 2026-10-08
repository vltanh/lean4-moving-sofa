# 65. Two moving corners can control a pinch without an affine ceiling

Note 62 treats a corner touching an affine ceiling. Here both boundaries may be moving corner graphs. On a strictly transverse graph chart, the lower graph has nonnegative singular second derivative and the upper graph has nonpositive singular second derivative. Feasibility makes their gap nonnegative. At a zero gap, these singular contributions cannot persist.

No curvature cap, smoothness of the input hull, maximality, or candidate proximity is assumed. The strict chart hypotheses are stated below. This is not a claim that every corner coincidence has such a chart.

## 65.1 Support functions and bounded-variation velocities

On a compact interior lower-turn interval J, write

\[
f(t)=h_K(t),\quad g(t)=h_K(t+\pi/2),\quad
\sigma_f=f+f'',\quad\sigma_g=g+g''.
\]

The last two quantities are nonnegative measures. Compact convex support functions are Lipschitz, and their first derivatives have bounded variation on J. Define, using their one-sided traces,

\[
p=f'-g+1,\qquad q=g'+f-1,
\quad c=(f-1)\mu_t+(g-1)\nu_t,
\]

\[
a=p\cos t-q\sin t=c_x',\qquad
b=p\sin t+q\cos t=c_y'.
\tag{65.1}
\]

The derivatives of c exist almost everywhere; c itself is Lipschitz. Distributionally,

\[
Dp=\sigma_f-(q+1)dt,\qquad
Dq=\sigma_g+(p-1)dt.
\tag{65.2}
\]

Fix numbers 0<eta<=H. Assume **every one-sided trace** on J satisfies one of the following two alternatives throughout the chart:

\[
-H\leq p\leq-\eta,\quad\eta\leq q\leq H
\qquad\text{(standard orientation)},
\]

or

\[
\eta\leq p\leq H,\quad-H\leq q\leq-\eta
\qquad\text{(reverse orientation)}.
\tag{65.3}
\]

Then a has constant sign epsilon in {-1,1}, with eta<=|a|<=sqrt(2)H. Consequently x(t)=c_x(t) is bi-Lipschitz onto its image. The graph F defined by

\[
F(x(t))=c_y(t)
\]

is Lipschitz and has a bounded-variation derivative

\[
F'(x(t))=z(t):=b(t)/a(t)\quad\text{a.e.}
\tag{65.4}
\]

The word "graph" concerns this selected corner curve. It need not be the complete swept roof away from the contact points under consideration.

## 65.2 Exact measure accounting, including edge atoms

Use the notation sigma_na for a measure with its atoms deleted. On nonatomic parts, the bounded-variation chain rule applied to z gives

\[
(Dz)_{\rm na}
=\frac{-q\,\sigma_{f,\rm na}+p\,\sigma_{g,\rm na}}{a^2}
+\frac{q-p+2p^2+2q^2}{a^2}\,dt.
\tag{65.5}
\]

At a jump t, put m_f=sigma_f({t}) and m_g=sigma_g({t}). Equation (65.2) gives p_+-p_-=m_f and q_+-q_-=m_g. Direct subtraction of the two quotients gives

\[
z_+-z_-=
\frac{p_-m_g-q_-m_f}{a_+a_-}.
\tag{65.6}
\]

The denominator is positive. Under (65.3), multiplying either (65.5)'s curvature part or (65.6) by epsilon makes every curvature coefficient positive.

For clarity, (65.5) uses the ordinary one-dimensional BV chain rule for a C^1 function of (t,p,q) on a region with a bounded away from zero. Its partial derivatives in p,q are -q/a^2 and p/a^2; its explicit t derivative is (p^2+q^2)/a^2. Substituting (65.2) gives (65.5). At jumps the rule uses the exact difference, not the derivative at one arbitrarily chosen trace; that is why (65.6) is separate. The C^1 rule also follows by telescoping increments over partitions, using the first-order expansion on intervals of small oscillation, isolating the finitely many large jumps, and then letting their cutoff tend to zero; the total error is bounded by the modulus of continuity of the gradient times the total variation. A primary general reference is Crasta and De Cicco, *A chain rule formula in BV and applications to conservation laws*, [arXiv:1011.0910](https://arxiv.org/abs/1011.0910).

For a monotone parameter change, the derivative measure transforms by

\[
D_xF'=\varepsilon\,x_\#(Dz).
\tag{65.7}
\]

The orientation factor is essential. For example, it reverses the sign of a jump when the graph is traversed from right to left. Formula (65.7) follows directly by evaluating both measures on intervals and comparing the endpoint traces.

**Lemma 120 (positive curvature measure of a corner graph).** On x(J),

\[
D^2F=\mu_F+\beta_F(x)\,dx,
\tag{65.8}
\]

where

\[
\mu_F\geq\frac{\eta}{2H^2}\,x_\#(\sigma_f+\sigma_g),
\qquad
|\beta_F|\leq\frac{2H+4H^2}{\eta^3}.
\tag{65.9}
\]

In particular F is locally semiconvex. Its measure mu_F includes, and positively controls, both the atomic and nonatomic input curvature.

**Proof.** Define mu_F by pushing forward epsilon times the curvature term of (65.5) and the full jump in (65.6). The trace inequalities and |a|<=sqrt(2)H give the lower coefficient eta/(2H^2), including at jumps because a_+a_-<=2H^2. All remaining terms are the pushforward of the displayed dt density in (65.5). A bi-Lipschitz change of variables divides that density by |a|, giving the bound on beta_F. This proves (65.8) and (65.9). QED.

No second derivative of a curvature measure has been taken. In particular a curvature atom has not been omitted by replacing a BV derivative with its almost-everywhere value.

## 65.3 Compare a lower corner graph with a reflected upper corner graph

Let S be a compact connected feasible body with K=conv(S). The motions may have partial conventional endpoints. Choose one interval J_- in its lower motion and one interval J_+ in the positive reflected parameter for its upper motion, each satisfying (65.3), with possibly different constants and orientations.

Let F be the lower graph and let G=1-F_+ be the actual upper graph obtained from the lower graph of rho K. Work on an open interval I contained in both graph projections and in the interior of the horizontal projection of S.

For each x in I there is a point of S on that vertical line. The particular lower corner at x forbids every height below F(x); the particular upper corner at x forbids every height above G(x). Therefore

\[
v(x):=G(x)-F(x)\geq0\quad(x\in I).
\tag{65.10}
\]

This argument does not assume that F and G are the full swept boundaries throughout I. They are individual valid constraints. When F(x)=G(x), the entire surviving fiber is necessarily the singleton at that common height, so both corners are active there.

Write the measure decompositions of Lemma 120 as

\[
D^2F=\mu_-+\beta_-dx,\qquad
D^2G=-\mu_+-\beta_+dx.
\]

Then

\[
D^2v=-(\mu_-+\mu_+)+b(x)dx,
\qquad b=-\beta_--\beta_+,
\quad |b|\leq C.
\tag{65.11}
\]

In particular v is semiconcave. Set Z={x in I:v(x)=0}.

**Lemma 121 (zero-gap measure identity).**

\[
D^2v|_Z=0,\qquad
(\mu_-+\mu_+)|_Z=b(x)dx|_Z\leq C\,dx|_Z.
\tag{65.12}
\]

**Proof.** At every point of Z, nonnegativity of v gives left derivative <=0 and right derivative >=0. Semiconcavity gives the opposite ordering between its one-sided derivatives. They must both be zero, so D^2v has no atom on Z. Apply Lemma 108 to the semiconvex function -v to conclude that its nonatomic second derivative is also zero on this level set. Thus D^2v|_Z=0. Restrict (65.11) to Z. Positivity of the two mu measures gives the final inequality. QED.

The use of locality is a restriction of measures to Z, not a claim that the second derivative vanishes near Z. The set Z may be a nontrivial closed set or a set of isolated pinches.

## 65.4 Source singular curvature is excluded at these pinches

**Theorem 122 (transverse corner/corner pinch bound).** On the source parameters whose corner images belong to Z, each of the four source curvature measures is absolutely continuous, with a bound depending only on the two charts' eta,H constants. In particular neither an exposed-edge atom nor singular-continuous source curvature can be supported at those parameters.

**Proof.** Lemma 120 and (65.12) dominate each pushed-forward source measure restricted to Z by a finite multiple of dx. Each graph parameter map is bi-Lipschitz. Pulling this bound back gives domination by a finite multiple of dt on its inverse image of Z. Explicitly, for a chart with constants eta,H, its coefficient is at least c=eta/(2H^2), and x is sqrt(2)H-Lipschitz, so the pulled-back bound is at most C sqrt(2)H/c times dt. Bi-Lipschitz maps preserve Lebesgue-null sets, giving the assertion for the singular parts. QED.

This is a local measure inequality on actual feasible bodies; no maximality is needed. It does not have the sharp coefficient one, and therefore does not alone supply Theorem 65's full hypothesis.

## 65.5 Scope and countable covering

The result handles precisely the previously unaddressed situation of two moving corner graphs, without a touching affine ceiling, when both have strictly transverse, fixed-orientation trace bounds. Rational-ended parameter subintervals, rational interior x-intervals, and constants eta=1/n,H=n form a countable covering family of such charts. Applying Theorem 122 on this family does not take an uncountable union of null sets.

No assertion is made that every pinch has one of these charts. Zero velocity components, changes of sign, stationary or noninvertible corner abscissae, endpoint angles, and mixed one-sided traces at a jump require separate treatment. A curvature measure at an outer point that is itself a different inner corner is another contact problem; it is not automatically a source measure in (65.11).

Thus this deletes the transverse two-corner portion of the residual pinch set but does not establish global curvature domination, full-quarter turns, or the contact-order inequalities. The proof is pen-and-paper and is committed for independent checking. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
