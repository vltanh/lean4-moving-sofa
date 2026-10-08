# Local \(P_J\) stability: the moving-corner term is essential

**Main calculation PJ-MID1.** For a smooth support perturbation confined
to the open middle curved arc of Romik's **one-turn cap**, the sharp
middle-half spatial functional has an exact negative quadratic change:

\[
\boxed{P_J(U_\varepsilon)-P_J(U_*)
=\varepsilon^2\left(\frac12\int\phi^2-
\int|\phi'|^2\right)
\le-\frac78\varepsilon^2\int|\phi'|^2.}
\tag{PJ-MID.1}
\]

This is a **local, branch-stable theorem** for sufficiently small
\(\varepsilon\), not a global concavity statement.
Crucially, the source support affects *both* a smooth first-wall
niche region and a moving inner-corner region. Omitting the latter
produces an erroneous nonzero first derivative and falsely suggests
that the reference violates the \(P_J\) value conjecture.

This proof is self-reviewed, pen and paper; it uses the explicit reference
contact chart, not Lean or numerical optimization.

## 1. Perturbation domain

Put \(L=\pi/2\), \(Y>0\) with \(4Y^3+3Y-1=0\),
\(\beta=\arctan Y\), and
\(R=\cos\beta/\sin(3\beta/2+\pi/8)\).
On the middle curved source arc \(T=(\beta,L-\beta)\), the reference
upper-quadrant supports are

\[
f(t)=R\cos(t/2+\pi/8)+\tfrac12\sin t,\qquad
g(t)=R\sin(t/2+\pi/8)+\tfrac12\cos t.
\tag{PJ-MID.2}
\]

Let \(\phi\in C_c^2(T)\), and vary **only** the first support:
\(f_\varepsilon=f+\varepsilon\phi\); retain \(g\)
and every support outside \(T\). The horizontal projection remains
\([-m,m]\), and its middle half
\(J=[-m/2,m/2]\) stays fixed. The original upper roof is one
on \(J\), and its full positive niche is supported inside \(J\).
For small enough \(|\varepsilon|\), the resulting upper support
is convex: its curvature density
\(\rho_\varepsilon=f_\varepsilon''+f_\varepsilon\)
remains strictly between zero and one on the compact support
of \(\phi\); all other original support arcs are unchanged.
The upper boundary remains below height one away from the original
top face, so it gives a normalized downward convex cap \(U_\varepsilon\).

The **reference exposed-contact chart** has the following two pieces
associated with \(t\in T\):

* the smooth *first-wall* niche graph at the stationary wall point
  \(Z(t)=O(t)-(\cos t,\sin t)\);
* the *moving two-wall corner* graph
  \(C(t)=(f(t)-1)n_t+(g(t)-1)n_t^\perp\).

Here \(O(t)=f(t)n_t+f'(t)n_t^\perp\) is the exterior support point,
\(n_t=(\cos t,\sin t)\), and
\(n_t^\perp=(-\sin t,\cos t)\).
On the open reference middle chart the standard contact signs are
\(p=f'-g+1<0<q=g'+f-1\), and \(0<\rho<1\).
Consequently \(x_O'<0\), \(x_Z'>0\), and \(x_C'<0\).
At the smooth first-wall branch its companion wall is strictly above
the active wall, while the corner branch is the meeting of two
oppositely varying walls. These are the *exposed* branches, not
unverified tangency candidates.

Because \(\phi\) has compact support inside the strict reference chart,
for sufficiently small \(|\varepsilon|\) the same three exposed graph
types persist on the affected compact subintervals. The nearby
unaffected intervals, including the branch switches at
\(\beta,L-\beta\), remain literally unchanged. This follows from
strict wall comparisons, \(0<\rho<1\), \(p<0<q\), and the implicit
function theorem; thus the following parameter-area formulas retain
their signs and have no missing global-envelope branches.
In particular, we do **not** assume an arbitrary optimizer has
the reference contact chart.

## 2. The outer-roof contribution

Write \(c=\cos t,s=\sin t,\rho=f''+f\). The right
exterior point is

\[
O=(x_O,y_O)=(fc-f's,\;fs+f'c),\qquad
x_O'=-\rho s.
\]

Let \(\zeta=\phi s+\phi'c\) and
\(\kappa=\phi''+\phi\).
The perturbed outer point changes by
\(\delta x_O=\phi c-\phi's\),
\(\delta y_O=\zeta\), and
\(\delta(-x_O')=\kappa s\).
The affected exterior-roof area is
\(\int y_O(-x_O')dt\).
Its linear change is the standard support-curvature variation
\(\varepsilon\int_T\rho\phi\,dt\). Its **exact** quadratic
coefficient, after integrations by parts and vanishing endpoint
terms, is

\[
Q_{\rm out}
=\int_T\zeta\kappa s\,dt
=\frac12\int_T(\phi^2-\phi'^2)\,dt.
\tag{PJ-MID.3}
\]

Other exterior roof pieces are unchanged, and the affected exterior
pieces lie entirely outside \(J\).

## 3. Smooth first-wall niche branch

The inner stationary point is \(Z=O-n_t\).
Thus

\[
x_Z'= (1-\rho)s,\qquad y_Z=y_O-s.
\]

This graph is increasing in \(x\).
Its niche-area piece is \(\int y_Zx_Z'dt\).
The first-order term is
\(\varepsilon\int_T(1-\rho)\phi\,dt\),
using the wall-height envelope theorem at fixed \(x\).
Its exact quadratic coefficient is the *negative* of the outer
quadratic coefficient, because
\(\delta y_Z=\zeta\) and
\(\delta x_Z'=-\kappa s\):

\[
Q_{\rm stat}=-Q_{\rm out}.
\tag{PJ-MID.4}
\]

This is **not** the entire niche variation.

## 4. Moving two-wall corner branch

The actual inner-wall corner is

\[
C=(x_C,y_C)=(f-1)n_t+(g-1)n_t^\perp,\qquad
C'=p\,n_t+q\,n_t^\perp.
\]

Because \(p<0<q\), its \(x\)-coordinate decreases and its
niche-area piece is \(\int y_C(-x_C')dt\).
The first-support perturbation changes
\(\delta C=\phi n_t\). Therefore

\[
\delta x_C'=\phi'c-\phi s,\qquad
\delta y_C=\phi s.
\]

The first-order moving-corner contribution is

\[
\int_T \phi(-s x_C'+c y_C')dt
=\int_T q\,\phi\,dt,
\tag{PJ-MID.5}
\]

and the **exact** quadratic coefficient is

\[
\begin{aligned}
Q_{\rm corner}
&=\int_T-\phi s(\phi'c-\phi s)\,dt\\
&=\int_T[-sc\,\phi\phi'+s^2\phi^2]dt
=\tfrac12\int_T\phi^2\,dt.
\end{aligned}
\tag{PJ-MID.6}
\]

The last equality is integration by parts with
\((sc)'=c^2-s^2\). The corner term is *positive*.
Discarding it is precisely the false first-variation shortcut.

## 5. Exact cancellation and strict quadratic deficit

The explicit reference middle formulas give

\[
\rho=\tfrac34R\cos(t/2+\pi/8),\qquad
q=\tfrac32R\cos(t/2+\pi/8)-1=2\rho-1.
\tag{PJ-MID.7}
\]

Hence the niche first variation is

\[
\delta N
=\int_T[(1-\rho)+q]\phi\,dt
=\int_T\rho\phi\,dt,
\]

which cancels the exterior first variation **exactly**.
The niche quadratic coefficient is

\[
Q_N=Q_{\rm stat}+Q_{\rm corner}
=-Q_{\rm out}+\tfrac12\int_T\phi^2
=\tfrac12\int_T\phi'^2.
\]

Subtracting niche area from the exterior roof gives the
exact identity PJ-MID.1 (not merely a formal Taylor coefficient)
throughout the small-\(\varepsilon\), branch-stable interval.
Indeed all three boundary graph areas are quadratic polynomials
in \(\varepsilon\), and their endpoints are unchanged because
\(\phi\) and its derivatives vanish near the switches.

Since \(T\) has length \(L-2\beta<\pi/2\), the one-dimensional
Dirichlet inequality gives
\(\int_T\phi^2\le\frac14\int_T\phi'^2\).
Therefore

\[
\boxed{M/2-P_J(U_\varepsilon)
=\varepsilon^2\left(\int_T\phi'^2
-\tfrac12\int_T\phi^2\right)
\ge\tfrac78\varepsilon^2\int_T\phi'^2>0}
\]

for nonzero \(\phi\) and sufficiently small nonzero
\(\varepsilon\), of **either** sign.

## 6. A fully explicit compactly supported example

On \(11/20\le t\le19/20\), choose
\(\phi(t)=\sin^4\bigl(\frac{5\pi}{2}(t-11/20)\bigr)\),
and put \(\phi=0\) elsewhere. This is \(C^2\), with compact
support in \(T\). Elementary beta-integral identities yield

\[
\int\phi^2\,dt=\frac7{64},\qquad
\int(\phi')^2dt=\frac{25\pi^2}{16}.
\]

Thus, for sufficiently small \(|\varepsilon|\),

\[
\boxed{
P_J(U_\varepsilon)=\frac M2-
\varepsilon^2\left(\frac{25\pi^2}{16}-\frac7{128}\right).
}\tag{PJ-MID.8}
\]

This also gives a useful finite-angle diagnostic (a sampled niche
underestimates the continuum niche and can introduce a false small
positive apparent excess). The exact mathematical claim uses no
sampled values.

## 7. Boundaries and next targets

PJ-MID1 does **not** establish global Minkowski concavity (CF5
is already disproved) or a sharp value bound for arbitrary caps.
It analyzes a single upper middle support arc of the **reference**,
with an unchanged companion support and verified active regions.
Mixed deformations of both arcs, changes at switching contacts,
moving width, and non-reference geometries remain separate tasks.

What it does establish is that a sharp local \(P_J\) analysis must
retain **both** stationary-wall and moving-corner contributions.
The new strict deficit is a concrete starting point for mixed
two-sided and endpoint/contact-switch stability calculations.
No Lean, CI, or independent peer review was performed.
