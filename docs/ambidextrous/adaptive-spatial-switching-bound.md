# A canonical spatial relaxation with an exact switching-mismatch remainder

**Scope.** This strengthens the direct actual-area upper bound SPB without a curvature premise, a common-face background, a prescribed middle-half interval, or any auxiliary maximizing-cap hypothesis. It supplies a single intrinsic scalar coupled-area target and identifies precisely the residual lost by replacing two independently switching safe-wall alternatives with their aggregate. The sharp upper bound on this target is **not proved**. Labels AS are local.

Only the elementary full-turn fiber accounting of OT/SPB is used. The result is valid for any two caps with nonempty surviving fibers; when applied to a compact connected full-turn body it bounds its actual area. No numerical experiment is a proof premise.

## 1. Exact fiber variables

Let \(U,V\) be the upper and reflected-lower downward caps of the same compact full-turn body in \(0\le y\le1\), with common horizontal projection \(I=[l,r]\) and width \(W\). Denote their roof heights by \(A_U,A_V\), and their **full** positive niche roofs by \(n_U,n_V\). Set
\[
d_U=1-A_U,\qquad d_V=1-A_V,\qquad
D=d_U+d_V,\qquad N=n_U+n_V.
\]
All four fiber deficits are nonnegative. For the actual connected body's canonical envelope, every vertical fiber is nonempty and has exact length
\[
\ell(x)=1-\max\{d_U(x),n_V(x)\}
          -\max\{d_V(x),n_U(x)\}.
\tag{AS.1}
\]
This is OT1/SPB.1 in the deficit variables. It accounts for all positive clipping, rather than subtracting untruncated niche areas from a hull without a correction.

## 2. The intrinsic aggregate upper bound

At every abscissa,
\[
\max(d_U,n_V)+\max(d_V,n_U)
\ge\max(d_U+d_V,n_U+n_V)=\max(D,N).
\]
Hence:

**Theorem AS1 (adaptive spatial ordinary-area enclosure).** Every compact connected full-turn body with the preceding actual caps satisfies
\[
\boxed{|S|\le |E|\le \mathscr C(U,V)
 :=W-\int_I\max\{D(x),N(x)\}\,dx.}
\tag{AS.2}
\]

The expression is translation invariant and symmetric in the two turns. It requires no arbitrarily chosen spatial window or independent scalar bound on either cap. This is a genuine ordinary-area upper comparison, although its global sharp maximum is not determined by the theorem.

**Exact mismatch remainder.** Put
\[
a(x)=n_U(x)-d_V(x),\qquad b(x)=n_V(x)-d_U(x).
\]
Then \(N-D=a+b\), and \(\max(d_V,n_U)=d_V+a_+\), \(\max(d_U,n_V)=d_U+b_+\). Subtracting gives
\[
\boxed{\mathscr C(U,V)-|E|
=\int_I\left[a_++b_+-(a+b)_+\right]dx
=\int_I\left[\min(a_+,(-b)_+)+\min(b_+,(-a)_+)\right]dx\ge0.}
\tag{AS.3}
\]
Thus the relaxation is **exact** whenever the two cross-deficits \(a,b\) have the same sign almost everywhere. It loses exactly the smaller conflicting safe-wall surplus where their signs oppose. No winding or clipping term is silently dropped.

There is also a symmetric one-turn-area representation:
\[
\boxed{\mathscr C(U,V)
=\frac{\mathcal A(U)+\mathcal A(V)}2
 -\frac12\int_I|N(x)-D(x)|\,dx,}
\tag{AS.4}
\]
where \(\mathcal A(U)=|U|-|N(U)|\). To check this identity, expand \(\max(D,N)=(D+N+|D-N|)/2\) and use \(\int_I D=2W-|U|-|V|\).

## 3. The new bound dominates every fixed spatial partition

For **any measurable** \(J\subseteq I\), define the two-turn band relaxation
\[
\mathscr P_J(U,V)
=\int_J[1-N(x)]dx+\int_{I\setminus J}[1-D(x)]dx.
\]
No half-measure condition is required to state this *pair* bound. At every point it selects either the niche-only bound or the hull-only bound, both of which dominate the actual fiber length. The optimum among all such bands is
\[
\boxed{\inf_{J\subseteq I\ \mathrm{measurable}}\mathscr P_J(U,V)
=\mathscr C(U,V),\qquad J_{\rm opt}=\{x:N(x)\ge D(x)\}.}
\tag{AS.5}
\]
Indeed choosing the smaller integrand pointwise minimizes the integral. The defining functions are measurable and the interval is bounded.

More precisely,
\[
\boxed{\mathscr P_J(U,V)-\mathscr C(U,V)
=\int_{I\setminus J}(N-D)_+dx
 +\int_J(D-N)_+dx.}
\tag{AS.6}
\]

If \(|J|=W/2\), \(\mathscr P_J=\mathcal P_J(U)+\mathcal P_J(V)\) for SPB's scalar definition. In particular the centered middle-half upper bound SPB3 is always at least the new \(\mathscr C\). The explicit identity AS.6 locates its avoidable spatial-partition slack.

Combining AS.3 and AS.6 recovers exactly SPB.4; this is an algebraic cross-check, not an additional geometric hypothesis.

## 4. Sharpness and the remaining mathematical target

For Romik's reference, \(U=V=U_*\), and on its horizontal top-face interval \(J_*\) one has \(D=0\); outside it the reference niches vanish, so \(N=0\). On each abscissa \(a=b\). Therefore both AS.3 and AS.6 vanish with \(J=J_*\), and
\[
\boxed{\mathscr C(U_*,U_*)=|\Sigma|=M.}
\]

An exactly stated **sufficient** full-turn theorem is now
\[
\boxed{\mathscr C(U,V)\le M
\quad\text{for every actual compatible full-turn cap pair}.}
\tag{AS.7, unproved}
\]
The global maximum in AS.7 is still unknown. It cannot be inferred from \(\Psi(U),\Psi(V)\le M/2\), because the new functional retains the same spatial clipping effects. Nor is it a claim of a new calibrated auxiliary optimum.

Unlike the individual \(\mathcal P_J\) route, AS.7 is genuinely **coupled** and does not require an independent one-cap inequality whose validity may be stronger than necessary. It may be approached by a hand comparison for \(N-D\), an exact integral inequality, or a verified covering of compatible support data. A finite sample of cap parameters would not establish AS.7.

The large unresolved global admission issue remains: the previous CB/CT method cannot assign common half-height-niche backgrounds to every full-turn body merely by containment. The explicit parallelogram obstruction in [full-turn-common-background-obstruction.md](full-turn-common-background-obstruction.md) proves that unconditional claim false. Its area is too small to rule out a **competitive-only** admission theorem. The direct spatial inequality above avoids the background premise entirely but has a separate sharp maximization obligation.

No long computation, CI, Lean/Lake compilation, dependency installation or manuscript build was used. All identities are hand proofs. Unrestricted full-turn optimality is **not** claimed.

## 5. Relation to the weighted deficits, and cases where no relaxation is lost

For full niches on a common width, the signed cap identity gives
\[
\Psi(U)+\Psi(V)=W-\int_I(D+N).
\]
Consequently there is the **exact** equality
\[
\boxed{\mathscr C(U,V)=\Psi(U)+\Psi(V)+\int_I\min(D,N)\,dx.}
\tag{AS.8}
\]
The original two-turn positive clipping term is
\[
G=\int_I[\min(n_U,d_V)+\min(n_V,d_U)]\,dx
\le\int_I\min(N,D)\,dx,
\]
and the difference is exactly the mismatch remainder AS.3. Thus the proposed scalar bound AS.7 is *stronger* than the original sharp clipping budget. A proof of AS.7 would suffice, but it must not be inferred from the existing weighted inequality; a counterexample to this stronger aggregate bound would not be a counterexample to the moving-sofa conjecture.

There are two elementary situations in which this stronger comparison loses **no** material:

1. If the two caps agree, \(U=V\), their cross-deficits are equal, \(a=b=n_U-(1-A_U)\), and AS.3 vanishes. Thus AS is exact on every nonempty-fiber vertically symmetric full-turn envelope, whether or not its niche is clipped.
2. If the actual feasible full-turn body is convex, then its convex hull is the body itself. Canonical tightening deletes no point of this hull, so its full envelope equals the body. At each abscissa, \(n_U\le d_V\) and \(n_V\le d_U\) (all retained vertical fiber points must meet both motions). Both cross-deficits are nonpositive, and AS.3 again vanishes. The explicit thin full-turn parallelogram in CGA is one such example.

These examples show that AS is geometrically faithful for both the reference sofa and certain very different full-turn shapes. They do **not** establish the unproved global maximum of \(\mathscr C\). In general the cross-deficits can have opposite signs, and the new aggregate clipping charge \(\int\min(D,N)\) exceeds the actual \(G\); that excess must be treated as relaxation error, not charged twice.

## 6. The stronger aggregate bound is proved on the existing paid-tail domains

The AS sufficient inequality is not a mere numerical guess near the reference. The already proved TC/CT/MT clipped-tail bounds actually imply the **stronger** AS.7 whenever the two input caps have their positive niches supported in one common interval \(J\), and their signed deficits satisfy
\[
\Delta(U)\ge\int_J(1-A_U),\qquad
\Delta(V)\ge\int_J(1-A_V).
\tag{AS.9}
\]
Indeed \(N=0\) outside \(J\), while \(D\ge0\) everywhere, so
\[
\int_I\min(D,N)
=\int_J\min(D,N)\le\int_JD
\le\Delta(U)+\Delta(V).
\]
Insert this into AS.8 to get \(\mathscr C(U,V)\le M\). This is an exact hand proof without an appeal to the switching remainder. In particular it applies to the actual TC tail cuts, the signed fixed-middle variants, and admitted two-background comparisons for which the relevant per-cap deficits and common projection/face interval are verified.

Thus the direct aggregate target is compatible with all of those sharp near-reference cases. What is **not** proved is AS.9 or an alternative aggregate compensation for arbitrary saturated opposite-end-face competitors. The new CGA example prevents assigning compatible common half-height-niche backgrounds to *every* member of that class merely by containing its original caps. Competitive-only admission or a different global inequality remains necessary.

## 7. An exact \(L^1\) stability bound for the aggregate switching error

The switching mismatch is controlled by **asymmetry of the two actual one-turn surviving thickness profiles**, without any curvature or reference hypotheses. Continue to write
\[
a=n_U-d_V,\qquad b=n_V-d_U.
\]
The identity \(x_+=(x+|x|)/2\) improves AS.3 to the exact triangle-defect formula
\[
\boxed{\mathscr C(U,V)-|E|
=\frac12\int_I\bigl(|a|+|b|-|a+b|\bigr)\,dx.}\tag{AS.10}
\]
For two real numbers the integrand vanishes if \(a,b\) have the same sign. If their signs differ, it is twice the smaller absolute value, at most \(|a-b|\). Therefore
\[
\boxed{0\le \mathscr C(U,V)-|E|
\le\frac12\int_I
\left|(A_U-n_U)-(A_V-n_V)\right|dx.}\tag{AS.11}
\]
Indeed
\[
a-b=(n_U-d_V)-(n_V-d_U)
=(A_V-n_V)-(A_U-n_U).
\]
No assumption that one of these profiles is a signed objective maximizer occurs in the derivation.

**Corollary AS2.** If the two full one-turn survivor thickness profiles coincide almost everywhere,
\[
A_U(x)-n_U(x)=A_V(x)-n_V(x)\quad\text{for a.e. }x,
\]
then \(\mathscr C(U,V)=|E|\). This includes identical caps as a special case but does not require that the actual upper and reflected-lower convex caps themselves coincide. The same estimate bounds the overcount when the two profiles are merely close in \(L^1\).

This is a **stability of the relaxation**, not a global area bound: it does not show that the right side of AS.11 is paid by \(M-|E|\). In particular a small mismatch does not imply \(\mathscr C\le M\) when a feasible body's area is close to \(M\). The bounded falsification screens are consistent with this estimate, but it holds by the algebra above, not by their measurements.
