# Sharp Romik bound for two distinct symmetric caps with arbitrary horizontal misalignment

**Theorem TCS1 (hand sharp-area theorem, independent cap shapes).**
Let \(m>0\), \(b=m/2\), and \(I=[-m,m]\).
Let \(U,V\subset I\times[0,1]\) be **independent**
compact, convex, horizontally reflection-symmetric,
downward-closed normalized one-turn caps, each satisfying

1. \(I\times[0,1/2]\subset U,V\);
2. each cap's horizontal top face is exactly \(J=[-b,b]\);
3. each full positive-height one-turn niche
   \(N(U),N(V)\) is contained in
   \[
   \boxed{\{(x,y):0\le y<1/2,\quad |x|+y\le b\}.}
   \tag{TCS.1}
   \]
   (The niches need not be convex, have interval
   horizontal sections, or share their contact patterns.)

Put \(T_U=U\setminus N(U)\),
\(T_V=V\setminus N(V)\), and
\(\rho(x,y)=(x,1-y)\).
For every \(d\in\mathbb R\),

\[
\boxed{\begin{aligned}
|T_U\cap(\rho T_V+(d,0))|
&\le \Psi(U)+\Psi(V)
-\frac{\min(|d|,b)^2}{m(m+1)}\\
&\le M-\frac{\min(|d|,b)^2}{m(m+1)}.
\end{aligned}}
\tag{TCS.2}
\]

Here \(\Psi(U)=|U|-|N(U)|-m\) is the
**signed, full-niche** one-turn width-penalized
functional, and \(M\) is Romik's exact feasible
candidate area. The second inequality invokes
the already written universal one-turn
weighted theorem
[WV2](one-turn-weighted-value.md);
the **first inequality is a new self-contained
ordinary-area hand proof** that does not
depend on WV2.

The theorem includes asymmetric two-turn
intersections of *two different* convex
one-turn caps, with arbitrary horizontal
misalignment. Neither a maximizer condition
nor reference proximity, full curvature
domination or contact ordering is assumed.
It is **not** a theorem for arbitrary
two-turn sofas: admitting their caps to the
triangular-niche/half-height hypotheses
TCS.1 remains an essential open step.

## 1. Unshifted pair: exact area without a clipping remainder

Let \(A_U(x),A_V(x)\) denote the cap's
upper roofs, and \(n_U,n_V\) its full
positive niche roofs. From the half-height
rectangle and TCS.1,
\[
A_U,A_V\ge1/2,\qquad
0\le n_U,n_V<1/2.
\]
Both one-turn survivors have vertical
interval fibers
\([n_U(x),A_U(x)]\) and
\([n_V(x),A_V(x)]\), each containing
height 1/2, over all x in I.

For \(d=0\), their full two-handed
intersection has length
\[
\ell_0(x)=
\min(A_U(x),1-n_V(x))
-\max(n_U(x),1-A_V(x)).
\]
On the common top-face interval J
the cap roofs are both one; hence
\(\ell_0=1-n_U-n_V\).
On \(I\setminus J\), TCS.1 implies
\(n_U=n_V=0\); hence
\(\ell_0=A_U+A_V-1\).
Integrating, and using
\(|I|=2m\), yields **exactly**
\[
\boxed{|T_U\cap\rho T_V|
=|U|+|V|-|N(U)|-|N(V)|-2m
=\Psi(U)+\Psi(V).}
\tag{TCS.3}
\]
This is *ordinary surviving area*,
not a signed overlap approximation.
The fibers contain the midline
throughout the common horizontal
projection, so the unshifted body
is connected and follows both
canonical full motions.

## 2. The two-cap translation rearrangement inequality

For each cap, upper horizontal sections
for \(z\in[1/2,1]\) are centered intervals
\([-R_U(z),R_U(z)]\) and
\([-R_V(z),R_V(z)]\).
Convexity implies both radii are concave
with endpoint values \(m,b=m/2\).
The **identical chord inequality** holds
for either profile:
\[
\boxed{R_X(z)\ge m-m(z-1/2),\quad
R_X(1-y)\ge b+my,\qquad X=U,V.}
\tag{TCS.4}
\]

For \(0\le y<1/2\), the lower
sections of each survivor are
\([-m,m]\setminus N_X(y)\), where
the full niche sections satisfy
\(N_X(y)\subseteq[-(b-y),b-y]\)
and are empty at heights \(y\ge h_X\),
for some \(h_X<1/2\).
Compactness of the explicit triangular
containment with strict \(y<1/2\)
alone does not force a uniform
\(h_X<1/2\) for an arbitrary cap,
so **assume** here the stronger explicit
ceiling
\[
\boxed{\sup\{y:(x,y)\in N(X)\}<1/2,
\quad X=U,V.}
\tag{TCS.5}
\]
For the Romik cap this follows from
the explicit support formulas; for
a general cap it is a genuine
admission condition. It can be added
to hypothesis 3 above without any
curvature assumption.

For centered intervals of radii
\(a\ge c\), let \(D_{a,c}(d)\) be
the overlap loss after horizontal
translation \(|d|\), as in
[SO.3](shifted-cap-overlap-rearrangement.md).
Splitting the area
\(\Phi(d)=|T_U\cap(\rho T_V+(d,0))|\)
into lower and upper halves, and
subtracting the two notch contributions,
gives the **exact** two-cap counterpart
of SO.4.

At zero shift all niche sections lie
inside the opposite upper sections,
since \(R_X(1-y)\ge b\ge b-y\).
At nonzero shift, each possible loss
of that notch-overlap is bounded by
the corresponding interval loss
\(D_{R_Y(1-y),b-y}(|d|)\).
Therefore
\[
\begin{aligned}
\Phi(0)-\Phi(d)\ge
&\int_{1/2}^1
\left[D_{m,R_U(z)}(|d|)
+D_{m,R_V(z)}(|d|)\right]dz\\
&-\int_0^{h_U}D_{R_V(1-y),b-y}(|d|)dy\\
&-\int_0^{h_V}D_{R_U(1-y),b-y}(|d|)dy.
\end{aligned}
\tag{TCS.6}
\]

Differentiate the right side a.e.
with respect to \(t=|d|\).
For \(0<t<b\), **each** of the
two outer interval losses has a
derivative whose integrated value
is at least \(t/m\), from
\(m-R_X(z)\le m(z-1/2)\).
Each corresponding notch-loss
derivative has integrated value
at most \(t/(m+1)\), from
\[
R_Y(1-y)-(b-y)\ge(m+1)y.
\]
Thus, on \(0<t<b\),
\[
\boxed{
\frac{d}{dt}\left[
\text{right side of TCS.6}
\right]\ge\frac{2t}{m(m+1)}.
}
\tag{TCS.7}
\]

For \(b<t<m+b\), each outer
interval-loss derivative integrates
to \(1/2\), while the two notch
derivatives integrate to at most
\(h_U+h_V<1\). The total derivative
is strictly positive. For
\(t\ge m+b\), both notch derivatives
vanish because their participating
radii sum to at most \(m+b\), and
the total derivative is nonnegative.

The right side of TCS.6 starts
at zero and is absolutely
continuous. Integrating proves
\[
\boxed{\Phi(0)-\Phi(d)\ge
\frac{\min(|d|,b)^2}{m(m+1)}.}
\tag{TCS.8}
\]
Combine with TCS.3 and WV2 to obtain
TCS.2. QED.

## 3. A true asymmetric class near the sharp constant

Choosing \(U=V=U_*\), the actual
Romik reference cap, gives the
[RH1 horizontal-misalignment theorem]
(romik-horizontal-misalignment-sharp-bound.md).
It has an explicitly certified
triangular niche and height \(<.41\).
For every sufficiently small
positive shift, the actual two-turn
intersection has positive, opposite-end
top and bottom hull faces of length
equal to the shift, is connected, and
has area strictly below M yet
converging to M. Thus TCS1 directly
handles *genuinely asymmetric*
near-optimal sofa configurations
that are not in the earlier
aligned-face geometric class.

Because U and V in TCS1 may be
**different**, this is not only
a one-parameter family: it is an
infinite-dimensional class of
independent horizontally symmetric
one-turn caps, coupled by an
arbitrary real relative shift.

## 4. Exact limits on the inference

The class is still special. It
requires both original cap
profiles to be horizontally
symmetric *before their relative
translation*, to possess a
full half-height rectangle with
face length half their width, and
to have sufficiently low,
triangularly confined niches.
An arbitrary competitive two-turn
hull need satisfy none of these.
Showing it can be transformed
into this class without reducing
area is **not** a proved consequence
of convexity, Steiner symmetrization,
connectedness, or the original
full-turn motion constraints.
Previous exact counterexamples
to naive hull symmetrization
must not be ignored.

The second inequality uses WV2,
a written self-reviewed result
not yet independently refereed.
No new Lean formalization, CI,
numerical area bound or giant
certificate was performed.
The full sharp global ambidextrous
optimality theorem remains open.
