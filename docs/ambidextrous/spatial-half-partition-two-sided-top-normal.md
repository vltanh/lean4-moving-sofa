# Sharp \(P_J\) under sign-changing top-normal support perturbations

**New theorem PJ-TN1.** The spatial-partition one-cap inequality is sharp
on a class strictly broader than the nested reference cuts in
[PJ-CUT](spatial-half-partition-reference-cut-certificate.md):
**neither** \(U\subseteq U_*\) **nor** \(U_*\subseteq U\) is required.
Inward losses, outward gains, and changes of sign in the perturbed
top-normal supports are permitted. The only retained support data are
on the directions outside a fixed open window about the upper vertical.
The proof uses exact ordinary roof/niche accounting and the reference
circular-tail pairing; **not** global concavity, curvature domination,
a signed functional calibration, or numerical sampling.

## 1. Statement and hypotheses

Use the centered Romik downward cap \(U_*\) from
[TC](tail-paired-cut-deficit.md): horizontal projection
\(I=[-m,m]\), \(m=1/(3\sin\beta)\),
\(\beta=\arctan Y\), \(4Y^3+3Y-1=0\), with
top-face interval \(J=[a,b]=[-m/2,m/2]\).
Let \(A_*,n_*\) be its upper roof and full positive niche roof, and
\(M\) the known area of Romik's actual feasible sofa.
The reference satisfies \(n_*=0\) outside \(J\) and
\(P_J(U_*)=M/2\).

Fix \(0<\eta<\beta\) and let \(D=\sin(\eta)/2\).
Let \(U\) be **any compact, convex, downward-closed cap**
in \(I\times[0,1]\) with horizontal projection \(I\) and exact
support agreement

\[
\boxed{h_U(\theta)=h_*(\theta)\quad
\text{for }\theta\in
[0,\pi/2-\eta]\cup[\pi/2+\eta,\pi].}
\tag{PJ-TN.1}
\]

In fact the projection hypothesis is redundant for a nonempty
downward-closed convex cap: the two specified horizontal axis
supports force its projection to be \(I\). The height need not
be attained at one; the upper containing strip suffices.

**Theorem PJ-TN1 (two-sided sharp top-normal theorem).**
With the middle half \(J\) *fixed by the common projection*,

\[
\boxed{\quad
P_J(U)=\int_{I\setminus J}A_U(x)\,dx-\int_Jn_U(x)\,dx
\ \le\ \frac M2=P_J(U_*).
\quad}\tag{PJ-TN.2}
\]

The theorem allows arbitrarily signed changes in
\(h_U-h_*\) within the window and makes no nesting assumption.
It is **not** a theorem for arbitrary caps: the exact angular
support agreement PJ-TN.1 is essential.

## 2. A signed pointwise tail pairing

For \(0<d<D\), write \(t=\pi/2-\arcsin(2d)\),
\(c=\cos t=2d\), \(s=\sin t\), \(x_o=b+d\) (outside
the face) and \(x_i=b-d\) (inside). The candidate formulas TC.1
and TC Section 1 give

\[
A_*(x_o)=\frac{h_*(t)-x_oc}{s},
\qquad
n_*(x_i)=\frac{h_*(t)-1-x_ic}{s}
=\frac12-\sqrt{\frac14-d^2}>0.
\tag{PJ-TN.3}
\]

Put \(\delta(t)=h_U(t)-h_*(t)\), **of arbitrary sign**.
The outer supporting line of \(U\) gives

\[
\boxed{A_U(x_o)-A_*(x_o)\le\delta(t)/s.}
\tag{PJ-TN.4}
\]

The first forbidden-quadrant wall for the same \(t\) at \(x_i\)
has height \(R_U=n_*(x_i)+\delta(t)/s\).
We claim the companion wall is higher than \(R_U\), regardless of
the sign and magnitude of \(\delta\).

Indeed \(t+\pi/2\in[\pi-\eta,\pi]\), so PJ-TN.1 leaves the
second outer support **exactly** at its reference value
\(g_*(t)=m s+c/2\). Its wall at \(x_i\) is

\[
G_U=\frac{g_*(t)-1+x_i s}{c}
=\frac{(m+x_i)s+c/2-1}{c}.
\tag{PJ-TN.5}
\]

Here is an elementary uniform clearance check, with no small
perturbation assumption. Since the unique root \(Y\) lies between
\(7/25\) and \(3/10\),

\[
1<m<5/4,\quad c<3/10,\quad s>19/20,\quad
x_i=m/2-d,\quad d<3/20.
\]

Consequently

\[
(m+x_i)s>(3/2-3/20)(19/20)
=513/400>23/20>1+c/2,
\]

hence \(G_U>1\). Meanwhile \(U\subset I\times[0,1]\)
implies \(h_U(t)\le mc+s\), whence

\[
R_U
\le1-\frac1s+\frac{(m/2+d)c}{s}
\le\left(\frac58+\frac3{20}\right)
\frac{3/10}{19/20}
=\frac{93}{380}<1.
\tag{PJ-TN.6}
\]

Thus \(G_U>1>R_U\). At this one actual hallway frame the
full niche of \(U\) has height at least
\(\max(0,\min(R_U,G_U))\ge R_U\).
Subtract PJ-TN.3:

\[
\boxed{n_U(b-d)-n_*(b-d)
\ \ge\ \delta(t)/s
\ \ge\ A_U(b+d)-A_*(b+d).}
\tag{PJ-TN.7}
\]

**No sign assumption** occurs in this chain; in particular if
\(R_U<0\), the nonnegative niche roof is still at least \(R_U\).
Reflecting the cap horizontally gives the corresponding left pairing,

\[
n_U(a+d)-n_*(a+d)\ge A_U(a-d)-A_*(a-d).
\tag{PJ-TN.8}
\]

The reflected cap has the same two outer support-agreement
intervals because the reference is horizontally symmetric.

## 3. Nothing outside the paired tails can increase \(P_J\)

First, for each \(x\in[-m,a-D]\cup[b+D,m]\), the reference
upper roof has an attaining outward normal in one of the
unchanged intervals of PJ-TN.1: these are the reference flank
positions beyond the circular tail. Testing \(U\) against that
same unchanged support gives

\[
A_U(x)-A_*(x)\le0.
\tag{PJ-TN.9}
\]

Second, at every \(x\in J\setminus
((a,a+D)\cup(b-D,b))\) where \(n_*(x)>0\), TC Section 1
provides a reference niche-attaining hallway parameter in
\([\eta,\pi/2-\eta]\); **both** of its support normals occur
in the unchanged directions PJ-TN.1. The same forbidden
quadrant therefore gives \(n_U(x)\ge n_*(x)\).
Where \(n_*(x)=0\), this also holds by nonnegativity. Thus

\[
n_U(x)-n_*(x)\ge0
\quad\text{a.e. on the unpaired part of }J.
\tag{PJ-TN.10}
\]

Note that TC's reference attaining-parameter statement does **not**
require \(U\subseteq U_*\). Nesting was only needed in TC to obtain
the reverse niche monotonicity and the particular deficit TC.4.
Here all we need is the unchanged reference forbidden quadrant.

Subtracting the two *exact* spatial functionals gives

\[
P_J(U)-P_J(U_*)
=\int_{I\setminus J}(A_U-A_*)\,dx
-\int_J(n_U-n_*)\,dx.
\tag{PJ-TN.11}
\]

Pair the two length-\(D\) exterior strips with the inner strips
using PJ-TN.7–PJ-TN.8. Their total contribution to PJ-TN.11
is nonpositive. The remaining exterior integral is nonpositive
by PJ-TN.9, and the remaining negative niche integral is
nonpositive by PJ-TN.10. Therefore \(P_J(U)\le P_J(U_*)=M/2\).
Equality is attained by \(U=U_*\). QED.

## 4. What this closes and what it does not

- This gives a **two-sided**, sign-independent *local-in-support*
  inequality, without assuming closeness in Hausdorff distance
  or curvature bounds. It includes all the old inward cuts and
  any outward/mixed perturbation satisfying PJ-TN.1 and the
  fixed horizontal/vertical bounding box.
- For two *actual full-turn hull caps* \(U,V\) each in this class,
  SPB1 yields the ordinary area bound
  \(|S|\le P_J(U)+P_J(V)\le M\).
  Arbitrary cap-pair intersections are **not** asserted connected.
- A near-reference Hausdorff bound does **not** force exact
  support agreement outside the top-normal window. Neither an
  arbitrary opposite-positive-face hull nor a partial-turn cap
  is automatically admitted.
- Global Minkowski concavity of \(P_J\) remains false; this proof
  instead exploits a signed **roof/niche transport pairing** at
  genuinely retained reference hallway parameters.

**Next task:** identify additional perturbation regions with
retained support directions where a similar sign-independent
transport comparison holds, or find a rigorous obstruction.
A general sharp \(P_J\) bound remains unproved.

This is a self-reviewed pen-and-paper argument, not Lean
formalization, a computer certificate, or independent review.
