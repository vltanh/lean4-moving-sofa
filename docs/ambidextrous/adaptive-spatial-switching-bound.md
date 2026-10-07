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
