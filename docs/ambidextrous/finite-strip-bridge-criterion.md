# A finite width-slack criterion for completing partial turns

**Scope.** SI3 assumes an entire interval of safe straight-strip directions. This note gives finite sufficient tests for that continuum hypothesis. It closes the completion step for bodies passing those tests, but does not prove every competitive body passes them. It is independent of the weighted cap theorem, background admission, and numerical area constants. Labels FS are local. Baseline: `9307910d73167a19f92c1785433aa27febacd375`.

## 1. The sharp two-strip interpolation bound

Let w(theta) be the directional width of a compact set S. It equals the width of its convex hull. Suppose

$$w(a)\le A,\qquad w(b)\le B,\quad 0<b-a=\delta<\pi,$$

with A,B>=0. For a<=theta<=b, the exact positive-combination identity for unit normals gives

$$n_\theta=\frac{\sin(b-\theta)}{\sin\delta}n_a+
\frac{\sin(\theta-a)}{\sin\delta}n_b.$$

Subadditivity and positive homogeneity of support functions, applied to n and -n, therefore give

$$\boxed{w(\theta)\le
\frac{A\sin(b-\theta)+B\sin(\theta-a)}{\sin\delta}.}\tag{FS.1}$$

This is an upper bound, not an interpolation identity for arbitrary support data. The intersection of centered strips of widths A,B at these two normals is a parallelogram and attains the upper expression throughout the intervening angle interval. Thus no smaller universal upper envelope follows from these two widths alone. That parallelogram is not being asserted to be an ambidextrous sofa.

## 2. A finite test for every intermediate strip

Write c=cos(delta), s=sin(delta)>0, and assume A,B<=1. The expression in FS.1, with t=theta-a, equals

$$F(t)=A\cos t+\frac{B-Ac}{s}\sin t.$$

It is nonnegative on the interval, and F''=-F<=0. Its maximum is therefore either an endpoint or its single interior stationary point. It is at most one whenever at least one of the following exact alternatives holds:

$$\boxed{B\le Ac,\quad A\le Bc,\quad
A^2+B^2-2cAB\le s^2.}\tag{FS.2}$$

Indeed the first alternative makes the initial derivative nonpositive, so the maximum is A. The second makes the final derivative nonnegative, so the maximum is B. In the remaining case the interior maximum is

$$\sqrt{A^2+((B-Ac)/s)^2},$$

and its square is at most one exactly when the last inequality holds. Degenerate zero-width cases follow directly or by continuity.

**Lemma FS1.** If FS.2 holds, every strip direction between a and b has width at most one. For the two-strip upper envelope, these alternatives are also exhaustive: when both endpoint-maximum cases fail, the third is necessary.

If the normals have rational coordinates, c and s are their rational dot product and oriented determinant. For rational width bounds A,B, the test is rational arithmetic, including equality at one. The proof needs no sampling of intermediate angles.

## 3. A finite chain implies actual motion completion

Let S have the conventional lower and upper reduced turns of magnitudes alpha,gamma, with alpha+gamma>pi/2. Its two outgoing strip normals in the standard angle lift are

$$a_0=\alpha,\qquad a_N=\pi-\gamma,$$

and each has width at most one. Choose finitely many intervening normals

$$a_0<a_1<\cdots<a_N,$$

and valid bounds w(a_i)<=A_i<=1. Check FS.2 for every consecutive pair, with its actual dot product and determinant.

**Theorem FS2.** If all these tests pass, S has two full conventional quarter-turn motions after a change of incoming orientation, with no change to its area.

**Proof.** FS1 proves w<=1 on each closed subinterval. Their union is the complete bridge [alpha,pi-gamma], with no missing endpoints or gaps. SI3 then constructs continuous full canonical motions for the same S. For area greater than one, SI4 transports them to a unit-span endpoint of the safe-strip component. No dilation, hull replacement, or area estimate is used. QED.

The construction is an exact finite admission criterion. Merely listing a few safe normals without checking the inequalities between them is not a certificate.

## 4. One sufficiently thin intermediate strip is enough

There is a particularly simple special case. Put

$$\delta=\pi-\alpha-\gamma,\qquad
\eta=(\alpha+\pi-\gamma)/2.$$

If

$$\boxed{w(\eta)\le\cos(\delta/2),}\tag{FS.3}$$

then the bridge is safe. On the first half use A=1, B=cos(delta/2) in the first alternative of FS.2. On the second half use the reverse endpoint alternative. Thus the full-turn completion follows from a single extra, sufficiently narrow strip.

More generally any intermediate eta works if

$$w(\eta)\le\min\{\cos(\eta-\alpha),\cos(\pi-\gamma-\eta)\}.$$

The inequalities are hypotheses on the actual body, not consequences of its three original unit strips. A body that fails this test might still have a safe bridge or even full turns by another construction. Failure is only non-admission by this test.

## 5. What remains in the partial-turn problem

FS replaces an infinite list of width checks by explicit finite sufficient inequalities when there is adequate width slack. It does not imply that a putative maximizer has that slack. A width bump above one remains possible from the width information alone; additional hallway and retained-point geometry is needed to rule it out for the remaining feasible bodies.

This criterion also does not say that the reoriented full-turn body belongs to the current CT/CB background domain or to an aligned-face class. Those ordinary-area obligations remain independent. No optimality theorem is inferred merely from completing the rotations.

The interpolation, endpoint tests and motion application are pen-and-paper arguments. A short rational checker tests the algebra and boundary cases separately. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used. Unrestricted optimality remains unproved.
