# Different Gerver-like halves can beat both identical-half choices near Romik

**Theorem PII1 (exact anti-Jensen identity for compatible one-turn caps).**
Let U,V be two normalized compact downward convex one-turn caps
of the same projection I, each of height one, with full positive
niche roofs \(n_U,n_V\) and top-face intervals \(J_U,J_V\).
Assume

* the caps contain the lower half-height rectangle
  \(I\times[0,1/2]\);
* the complete positive niches have heights at most \(1/2\);
* \(n_U=0\) outside \(J_U\), and \(n_V=0\) outside \(J_V\).

Write \(\rho(x,y)=(x,1-y)\),
\(T_X=X\setminus N(X)\), and
\[
E_{UV}=T_U\cap\rho T_V,\quad
E_{UU}=T_U\cap\rho T_U,\quad
E_{VV}=T_V\cap\rho T_V.
\]
All three are actual connected complete-two-turn sofas,
since their vertical interval sections contain height \(1/2\).
Then the **exact ordinary-area identity** is

\[
\boxed{
|E_{UV}|-\frac{|E_{UU}|+|E_{VV}|}{2}
=
\int_I\!\left[
  \min(n_U,1-A_V)+\min(n_V,1-A_U)
\right]dx\ge0.
}
\tag{PII.1}
\]

Here \(A_U,A_V\) are the actual cap roofs.
If some niche of one parent is positive on an open interval
outside the other parent's top face (where its outer roof is
strictly less than one), the inequality is **strict**.

Thus a generic two-cap intersection is *not* dominated
by the **average** of the areas of its two identical-half
constructions. No false appeal to a Minkowski-concavity
principle is made: PII.1 is a direct area computation.

**Theorem PII2 (strictly beats both identical choices,
arbitrarily close to Romik).** There exists an explicit
\(\epsilon_0>0\), for example \(\epsilon_0=1/2000\),
and a two-sided family of genuine Romik curved one-turn
caps \(U_{+\delta},U_{-\delta}\),
defined by the horizontal shear of the true Romik curved core
in [SCR.2](sheared-romik-core-sharp-local-theorem.md),
such that for every \(0<|\delta|\le\epsilon_0\),

\[
\boxed{
|E_{+\delta,-\delta}|
>
|E_{+\delta,+\delta}|
=
|E_{-\delta,-\delta}|
\quad\text{and}\quad
|E_{+\delta,-\delta}|<M.
}
\tag{PII.2}
\]

All three are **connected sofas following the entire lower
and upper conventional quarter turns**. Their areas tend
to the exact Romik area \(M\) as \(\delta\to0\).

Therefore the tempting proposed structural assertion

> Any intersection of two arbitrary Gerver-like one-turn
> survivors has area at most the larger of the two
> symmetric (identical-parent) intersections

is false **arbitrarily near the sharp candidate**.
It cannot be the missing theorem establishing existence
of an identical-parent maximizing pair.

The result does **not** contradict Romik optimality:
the unequal-parent intersection still has a strict
quadratic deficit to M, by SCR1. It pinpoints
why a global sharp proof has to **pay for the
positive mixed-pair clipping credit**, rather
than delete that credit by a symmetrization slogan.

## Proof of PII1: ordinary fibers, no signed-roof assumption

For each cap X let \(A_X\) be its concave upper
roof and \(n_X\) the full positive niche roof.
By the assumptions, the surviving one-turn section
is \([n_X(x),A_X(x)]\), and contains \(1/2\).
Thus the mixed two-turn section is the nonempty
interval
\[
E_{UV,x}=
[\max(n_U(x),1-A_V(x)),
\ \min(A_U(x),1-n_V(x))].
\]
The elementary min/max identity of OT1, integrated,
gives
\[
|E_{UV}|=\Psi(U)+\Psi(V)+G(U,V)
\]
where
\[
G(U,V)=\int_I\bigl[
\min(n_U(x),1-A_V(x))+
\min(n_V(x),1-A_U(x))\bigr]dx.
\]
Because \(n_X\) vanishes outside its own
top face and \(A_X=1\) *on* that face,
the self clipping vanishes exactly:
\(G(U,U)=G(V,V)=0\).
Hence
\[
|E_{UU}|=2\Psi(U),\qquad
|E_{VV}|=2\Psi(V),
\]
and subtraction proves PII.1.

If \(x\) lies in \(J_U\setminus J_V\), then
\(A_V(x)<1\) whenever the top face \(J_V\)
is its exact full height-one set.
On any open subinterval where also \(n_U(x)>0\),
the first integrand is positive; the second
integrand is always nonnegative.
The analogous conclusion holds with U,V exchanged.
This proves the strictness claim.

## Proof of PII2: shear reflection and positive niche tips

The shear family is a *fixed true Romik curved core*
plus the true reference half-height rectangular
summand, not a polygonal approximation:
\[
U_\delta
=
A_\delta(V_*)+
([0,T]\times[0,1/2]),\quad
A_\delta(x,y)=(x+2\delta y,y).
\]
Its projection is \([0,2T]\), its height one, its
top face \([T/2+\delta,3T/2+\delta]\),
and it contains the full half-height rectangle.
SCR1 proves the complete niche height is \(<1/2\)
and its projection is confined to the corresponding
top face for \(|\delta|\le1/2000\), using the
open-quarter strict curvature bound and
actual support formulas. Thus PII1 applies.

Let \(J(x,y)=(2T-x,y)\) be horizontal reflection.
The centered reference core is invariant under
reflection about \(x=T/2\); therefore
\[
\boxed{J(U_\delta)=U_{-\delta}.}
\tag{PII.3}
\]
A conventional lower-turn hallway at angle t,
after horizontal reflection, is exactly the
conventional lower-turn hallway at angle
\(\pi/2-t\), with its two perpendicular arms
exchanged. Hence full positive niche areas,
cap areas and horizontal widths are unchanged.
Thus
\[
\Psi(U_\delta)=\Psi(U_{-\delta}),
\quad
|E_{\delta,\delta}|
=|E_{-\delta,-\delta}|=2\Psi(U_\delta).
\tag{PII.4}
\]

It remains to show that the mixed correction
\(G(U_\delta,U_{-\delta})\) is **strictly positive**
for every nonzero \(\delta\).
Assume \(\delta>0\); the negative case follows
by exchanging parents.

Put \(a_\pm=T/2\pm\delta\),
\(b_\pm=3T/2\pm\delta\),
\(l=0,r=2T\). Because T>1
and \(\delta\le1/2000\), the open
intervals
\[
I_L=(a_-,a_+),\qquad
I_R=(b_-,b_+)
\]
are nonempty and lie respectively in
\((a_-,r-1)\) and \((l+1,b_+)\).

**Exact positive niche near the left tip.**
For any cap X of height one and top face [a_X,b_X]
with projection [l,r], consider x with
\(a_X<x<r-1\).
At t→0, its companion support satisfies
\[
g_X(t)=1-a_Xt+o(t),
\]
so the second inner wall roof is
\[
\frac{g_X(t)-1+x\sin t}{\cos t}
=(x-a_X)t+o(t)>0
\]
for every sufficiently small t>0.
The first wall numerator tends to
\(r-1-x>0\), so its positive roof is
also positive. Choosing a sufficiently
small positive height produces a **genuine
positive point in the full niche**. Hence
\[
n_X(x)>0\quad(a_X<x<r-1).
\tag{PII.5}
\]

By reversing the angle \(t\to\pi/2\)
and using f_X(L)=1 and
f_X'(L^-)=-b_X, the dual statement is
\[
n_X(x)>0\quad(l+1<x<b_X).
\tag{PII.6}
\]

For \(x\in I_L\), (PII.5) gives
\(n_{-\delta}(x)>0\), while
\(A_{+\delta}(x)<1\)
because x lies strictly left of the
exact plus top face.
For \(x\in I_R\), (PII.6) gives
\(n_{+\delta}(x)>0\), while
\(A_{-\delta}(x)<1\)
because x lies strictly right of the
exact minus top face.
Therefore **both** nonnegative clipping
integrals in PII.1 are strictly positive:
\[
G(U_{+\delta},U_{-\delta})>0.
\]
With the equal self areas PII.4 this proves
the strict first inequality in PII.2.

For the final upper inequality, the existing
[SCR1](sheared-romik-core-sharp-local-theorem.md)
proved the independent two-shear sharp bound
\[
|E_{+\delta,-\delta}|
\le M-\frac3{250}(2\delta^2)<M.
\]
As \(\delta\to0\), cap supports, niche areas
and the ordinary two-turn envelope converge to
their reference data, so the areas tend to M.
This finishes PII2.

## Consequence for the actual sharp research program

There is a **real** benefit to pairing
unequal one-turn shapes, even arbitrarily near
the reference optimizer. This does **not**
imply an asymmetric optimizer exists; all
these examples remain below M.
But it mathematically falsifies the
strongest tempting first step toward proving
that the optimal pair must consist of two
identical copies simply by replacing an arbitrary
pair with the better identical-parent pairing.

The relevant inequality now has the correct sign:
\[
M-|E_{UV}|=
\underbrace{(M/2-\Psi(U))+
(M/2-\Psi(V))}_{\text{individual one-turn deficits}}
-\underbrace{G(U,V)}_{\text{genuine pairing benefit}}.
\]
A global sharp proof must either control
this *difference* for all actual feasible
pairs or find a **different** area-preserving
structural reduction not covered by the
falsified pair-to-identical selection map.

PII1 and the strict mixed gain are self-contained
area/support geometry given the stated cap
admission. PII2's strict sub-M conclusion imports
the written local SCR1 theorem, whose AF/SD/SR
dependencies are self-reviewed, not Lean
formalized or independently refereed.
No numerical mesh, global area search, CI
or independent verification is claimed.
