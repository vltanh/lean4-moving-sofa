# A cubic interaction law for two genuinely different curved rectangular cores

**Theorem CCC1 (the missing clipping cost is cubic under strict curvature).**
Let \(0<\eta\le1\), \(T>0\), \(I=[0,2T]\).
Let \(U,V\subset I\times[0,1]\) be arbitrary
compact convex downward-closed *one-turn caps* with:

1. a **shared full half-height rectangle**
   \(I\times[0,1/2]\subset U\cap V\);
2. horizontal top-face intervals of the same length T,
   \[
   J_U=[a,a+T],\qquad J_V=[b,b+T];
   \tag{CCC.1}
   \]
   these faces may be **different** and neither cap is
   assumed horizontally symmetric;
3. full positive lower-turn niche roofs \(n_U,n_V\)
   supported, respectively, inside \(J_U,J_V\),
   with \(0\le n_U,n_V\le1/2\);
4. the **open-quarter support curvature densities**
   \(\rho_f=f''+f\), \(\rho_g=g''+g\) of each cap
   are measurable and satisfy
   \(0\le\rho_f,\rho_g\le1-\eta\) almost everywhere
   on each open quarter, with no singular measure
   there. Top-normal face atoms are allowed.

Assume \(0<\delta:=|a-b|\le\min(T,\eta)\).
Let \(E=(U\setminus N(U))\cap
\rho(V\setminus N(V))\),
where \(\rho(x,y)=(x,1-y)\).
Then E has nonempty vertical interval sections
and its genuine ordinary area obeys
\[
\boxed{
|E|=\Psi(U)+\Psi(V)+G,\qquad
0\le G\le\frac{2\delta^3}{3\eta}.
}
\tag{CCC.2}
\]
In particular, using the branch's written universal
weighted one-turn value theorem WV2,
\[
\boxed{|E|\le M+\frac{2\delta^3}{3\eta}.}
\tag{CCC.3}
\]
The **cubic geometric estimate** in CCC.2
is self-contained and does not use WV2.

More sharply, if the *actual weighted deficits*
\[
\Delta_U=M/2-\Psi(U),\qquad
\Delta_V=M/2-\Psi(V)
\]
satisfy \(\Delta_U+\Delta_V\ge
2\delta^3/(3\eta)\), then
\(\boxed{|E|\le M}\) exactly.
This last implication is a **conditional
sharp criterion**, not a proof that all cap
pairs meet the deficit premise.

This theorem is directly motivated by
“two independently shaped curved cores plus
a central rectangular filling.”
It controls the otherwise positive
ordinary-area *clipping credit*, rather
than silently replacing the two caps by
the same one-turn optimizer.

## 1. A universal quadratic niche-tip law from support curvature

We prove a one-cap fact independent of
the other cap. Let U be a cap with top
face [a,b] at height one.
Its upper support functions on
\(0<t<L=\pi/2\) are
\[
f(t)=h_U((\cos t,\sin t)),\qquad
g(t)=h_U((-\sin t,\cos t)).
\]

The top-face endpoints provide the
one-sided support values and derivatives
\[
g(0)=1,\quad g'(0+)=-a,\qquad
f(L)=1,\quad f'(L-)=-b.
\tag{CCC.4}
\]

Assume the open-quarter curvature bounds
\(\rho_g=g''+g\le1-\eta\) and
\(\rho_f=f''+f\le1-\eta\) a.e.
The positive sine Green kernel on
\(0\le t\le L\) gives the exact
integral representation
\[
g(t)=\cos t-a\sin t+
\int_0^t\sin(t-z)\rho_g(z)\,dz.
\]
Since the kernel is nonnegative,
\[
\boxed{
g(t)\le1-a\sin t-\eta(1-\cos t).
}
\tag{CCC.5}
\]

For x=a+d, \(0\le d<\eta\),
the second inner-wall roof satisfies
\[
\begin{aligned}
L_t(x)
&=\frac{g(t)-1+x\sin t}{\cos t}\\
&\le d\tan t-\eta(\sec t-1).
\end{aligned}
\tag{CCC.6}
\]
Put \(z=\tan t\in[0,\infty)\).
The supremum of
\(d z-\eta(\sqrt{1+z^2}-1)\)
over all z≥0 is
\(\eta-\sqrt{\eta^2-d^2}\):
the unique stationary point is
\(z=d/\sqrt{\eta^2-d^2}\).
Because the **true** positive niche
roof is the positive part of the
supremum of **minima** of the two
inner-wall roofs, it cannot exceed
the positive supremum of this
second-wall roof. Therefore
\[
\boxed{
0\le n_U(a+d)
\le\eta-\sqrt{\eta^2-d^2}
=\frac{d^2}{\eta+\sqrt{\eta^2-d^2}}
\le\frac{d^2}{\eta}
\quad(0\le d<\eta).
}
\tag{CCC.7}
\]

Reverse the angular variable near
\(t=L\): the same sine-kernel
argument applied to \(f(L-t)\)
with endpoint derivative b gives
\[
\boxed{
n_U(b-d)\le\eta-\sqrt{\eta^2-d^2}
\le d^2/\eta\quad(0\le d<\eta).
}
\tag{CCC.8}
\]

These are **actual continuum-angle
inequalities** and hold for arbitrary
non-symmetric cap profiles in this
strict-curvature class. They are
not merely asymptotic Taylor series.
The bounds at d=eta follow by
continuity and monotonicity of
the right-hand expression; the
integrable estimate d²/eta is
valid almost everywhere on [0,eta].

## 2. Exactly localize the two-cap clipping term

Because each cap contains its whole
bottom half-height rectangle and its
niche is at most half-height,
the reflected pair E has nonempty
closed interval fibers containing
height 1/2 over the common
projection I. The exact ordinary
fiber identity [OT1](one-turn-reduction.md)
therefore gives
\[
\begin{aligned}
|E|&=\Psi(U)+\Psi(V)+G,\\
G&=\int_I[
\min(n_U(x),1-A_V(x))
+\min(n_V(x),1-A_U(x))]dx,
\end{aligned}
\tag{CCC.9}
\]
where \(A_U,A_V\) are the outer
upper roofs.

Suppose without loss of generality
\(a\le b\). Set \(\delta=b-a\le T\).
The top-face intervals overlap, with
\[
J_U\setminus J_V=[a,b),\qquad
J_V\setminus J_U=(a+T,b+T].
\tag{CCC.10}
\]
On \(J_V\) the outer roof \(A_V=1\),
so \(\min(n_U,1-A_V)=0\);
outside \(J_U\) the niche roof n_U=0.
Thus the *first* integrand is supported
only on the left sliver [a,b].
Similarly the second integrand is
supported only on the right sliver
[a+T,b+T]. Consequently
\[
\boxed{
0\le G\le
\int_a^{a+\delta}n_U(x)\,dx+
\int_{b+T-\delta}^{b+T}n_V(x)\,dx.
}
\tag{CCC.11}
\]

This localization uses neither
competitor symmetry nor any
claim that the two niche roofs
have the same active contact
angles. It is **exactly** the
mismatched-flat-face mechanism
that appears as the positive
clipping correction in the
double-turn area identity.

## 3. Integrate the quadratic tip bounds

Apply CCC.7 to n_U at its
left top-face endpoint a;
apply CCC.8 to n_V at its
right top-face endpoint b+T.
Since \(\delta\le\eta\),
\[
\begin{aligned}
G
&\le\int_0^\delta\frac{d^2}{\eta}\,dd
+\int_0^\delta\frac{d^2}{\eta}\,dd\\
&=\boxed{\frac{2\delta^3}{3\eta}}.
\end{aligned}
\tag{CCC.12}
\]
For b<a the roles and the
left/right tips are interchanged;
the same bound holds.

Thus **cubic growth of the
interaction correction** is a
direct consequence of the
positive sine Green kernel and
strict subunit support curvature,
not a numerical conjecture.

## 4. Why this is progress but not closure

At the Romik reference cap
the written support formulas
have open-quarter curvature
at most 7/8, so \(\eta=1/8\)
is available for its own support
profile. The new theorem is
applicable to caps with a
**uniform** strict gap of this
kind and whose full positive
niches stay inside their
respective top-face intervals.

However the weighted one-turn
value theorem alone proves only
\(\Delta_U,\Delta_V\ge0\);
it does **not** prove the
quantitative bound
\[
\Delta_U+\Delta_V\ge
\frac{2|a-b|^3}{3\eta}.
\tag{CCC.13}
\]
Nor is every arbitrary competitive
sofa known to have both of its
canonical caps in the strict
curvature/niche confinement class.
Proving either new admission or
an exact deficit inequality
requires additional geometric work.
Thus CCC.2 **does not** establish
unrestricted Romik optimality.

The practical gain of the user's
filled-core viewpoint is now a
specific analytic split:
the two one-turn losses are
nonnegative by weighted sharpness,
while their **entire positive
coupling is confined to two
opposite tiny tip regions** and
costs at most cubic in their
relative top-face displacement.
This is a sharply formulated
ordinary-area mechanism that
can be tested on near-reference
counterexamples without assuming
a false symmetrization.

No Lean formalization, CI,
large area search or independent
refereeing was performed.
