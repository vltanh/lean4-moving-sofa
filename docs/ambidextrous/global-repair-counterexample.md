# A wide, fully feasible counterexample to unconditional curvature-repair monotonicity

The global operator R in [GM2](global-curvature-majorant.md) is well defined and increases **hull** area. It does not always increase the ordinary area of the sofa. This note constructs a compact connected full-turn example of width 63/25>2 for which replacing its hull by R(K) strictly decreases surviving area. It also disproves unconditional enclosure by Q_tilde(h_R(K)).

This is not a counterexample to Romik's optimality, nor to a possible repair theorem specifically for global maximizers. It rules out the stronger feasibility-only comparison before that comparison is used to claim closure. All analytic steps are supplied below. Sixteen small rational polynomial positivity checks certify the displayed numerical margins; the standard-library checker is committed separately.

## 1. Exact curvature data for the reference hull

Write T(z)=2 arctan(z), L=pi/2 and a=63/50. On [0,L] set

\[
r_-(t)=1_{[T(1/10),T(7/16)]}(t)
       +1_{[T(4/5),L]}(t),
\]

\[
r_+(t)=\lambda\,1_{[T(4/15),T(7/10)]}(t),
\qquad \lambda=\frac{23630025177}{23807644250}\in(0,1).
\tag{GR.1}
\]

The constant is chosen by the exact moment identity

\[
m:=\int_0^L r_-\sin t\,dt
=\frac{658053}{1263005}
=\int_0^L r_+\sin t\,dt.
\tag{GR.2}
\]

All these moments are rational because sin(T(z))=2z/(1+z^2) and cos(T(z))=(1-z^2)/(1+z^2).

For either sign, let f_sign be the unique solution

\[
f''+f=r_{\rm sign},\qquad f(0)=a,\quad f(L)=1,
\]

and set g_sign(t)=f_sign(L-t). An explicit formula, fixing every constant, is

\[
f(t)=a\cos t+
\left(1-\int_0^Lr(s)\cos s\,ds\right)\sin t
+\int_0^t\sin(t-s)r(s)ds.
\tag{GR.3}
\]

Define the upper semicircle of bar h by f_- and g_-. Define the upper semicircle of bar h^rho by f_+ and g_+, where bar h^rho(theta)=bar h(-theta)+sin(theta). These prescriptions agree at the horizontal normals and specify one continuous periodic support candidate.

Its four open-quarter curvatures lie in [0,1]. The two horizontal-normal derivative jumps are both

\[
1-\int_0^L(r_-+r_+)\cos t\,dt
=\frac{151354}{183135725}>0.
\tag{GR.4}
\]

The top and bottom jumps are both 2(a-m)>0. Thus the full distribution bar h+bar h'' is nonnegative, and bar h is a convex-body support function. Call the body K_0. Its width is 2a=63/25, its vertical span is one, and both horizontal exposed faces are

\[
[-b,b],\qquad b=a-m=\frac{9333333}{12630050}>\frac12.
\tag{GR.5}
\]

In particular [-b,b] times [0,1] is contained in K_0. The construction is symmetric in x but not assumed symmetric in y; its two quarter-density functions are different.

## 2. Complete-motion feasibility, certified by strict vertical margins

For each half define its lower canonical corner ordinate

\[
Y(t)=(f(t)-1)\sin t+(g(t)-1)\cos t.
\]

The following bounds hold on the **entire** parameter interval:

\[
Y_-(t)<53/100,\qquad Y_+(t)<23/50.
\tag{GR.6}
\]

The exact verification of these bounds is described in Section 5, rather than inferred from a sampled plot.

Here is the geometric consequence. With curvature in [0,1], the baseline intercepts of each forbidden quadrant are nondecreasing functions

\[
d(t)=\frac{1-g(t)}{\sin t},\qquad e(t)=\frac{f(t)-1}{\cos t}.
\]

Their endpoint ranges are d: -b to 1-a, and e: a-1 to b. This follows by differentiating: d'=D_y/sin^2(t), e'=B_y/cos^2(t), while D_y>=0 and B_y>=0 follow from the curvature bound and their zero baseline endpoints. Since a>1, d(t)<e(t) at every interior angle. Every positive-height lower forbidden triangle consequently lies over [-b,b], with height at most 53/100. The reflected upper triangles lie over the same interval and above 1-23/50=27/50.

Remove the two open canonical sweeps from K_0 and call the result S_0. On the central rectangle every surviving vertical fiber has length greater than 1/100. Outside that rectangle no positive-height niche is removed. All fibers over the hull projection are nonempty intervals, so S_0 is compact and connected. Its definition verifies every canonical hallway inclusion and both full-quarter endpoint strips. All nonhorizontal hull flanks and the face endpoints survive, hence conv(S_0)=K_0.

The two niches are separated, lie entirely inside K_0, and have nonnegative signed roofs. The signed-roof identity SR1 therefore gives exactly

\[
|S_0|=\widetilde{\mathcal Q}(\bar h).
\tag{GR.7}
\]

This uses the proved area identity for curvature-dominated full-turn hulls with aligned faces, not universal enclosure of ordinary area by the functional.

## 3. A circular arc whose inward displacement increases sofa area

Set

\[
J=[T(3/25),T(1/8)].
\]

It lies strictly inside the first interval where r_-=1. Put

\[
p=f_-' -g_-+1,\qquad q=g_-' +f_- -1.
\]

The exact margins on all of J are

\[
p<-1/250,\qquad q>101/100,\qquad Y_->1/10.
\tag{GR.8}
\]

Thus this is a strictly standard, positive-height corner interval, not a tangential or zero-height degeneracy. The source outer curvature is exactly one there.

Choose any nonzero nonnegative C^2 bump psi supported on J, vanishing together with its first derivative at the endpoints. For example, with J=[j_0,j_1], use (t-j_0)^3(j_1-t)^3 inside J and zero outside. Replace only the first upper quarter by

\[
f_\varepsilon=f_- -\varepsilon\psi,
\tag{GR.9}
\]

leaving g_- and both reflected upper functions unchanged. For every sufficiently small epsilon>0 this is a convex support function: on J its curvature is 1-epsilon(psi''+psi)>=0, and all other curvature and axis jumps are unchanged. Denote its hull by K_epsilon.

The four axis supports and horizontal faces are unchanged. Therefore its entire central rectangle is retained. Its changed lower niche only shrinks, because the first inner-wall threshold decreases; the opposite niche is unchanged. It follows just as above that its full canonical envelope S_epsilon is compact, connected, feasible for both full turns, and has actual hull K_epsilon. This is an actual sofa comparison, not a disconnected relaxation or merely formal support variation.

We next check exactly which part of the roof changes. On J the original B=c+p nu is constant because f_-''+f_-=1. Its abscissa is strictly to the right of the standard corner interval by p<0. The unchanged D abscissa is nondecreasing. For sufficiently small epsilon the perturbed corner abscissa remains strictly decreasing with the same endpoints, and the perturbed B abscissae remain strictly to the right of that whole small corner interval.

For x on that interval, choose the unique parameter where the perturbed corner has abscissa x. The identity dL_t(x)/dt=(x-D_x(t))/cos^2(t) bounds all earlier L values by the one at that parameter. The identity dR_t(x)/dt=(x-B_x(t))/sin^2(t) bounds all later R values similarly. Their equality at the corner proves it is the actual max-min roof. Outside that interval the roof is unchanged: on one side the minimum is the unchanged L family; on the other it is the R family, whose supremum is unchanged. Indeed the original R family is affine in -cot(t) on J, its endpoint values are unchanged, and lowering its interior cannot change its endpoint-attained supremum.

Thus the only changing niche area is the positively oriented corner contribution with fixed endpoints. Expansion of its determinant integral gives

\[
|N_\varepsilon|-|N_0|
=-\varepsilon\int_Jq\psi
+\frac{\varepsilon^2}{2}\int_J\psi^2.
\tag{GR.10}
\]

The exact support-area expansion, using original curvature one on J, gives

\[
|K_\varepsilon|-|K_0|
=-\varepsilon\int_J\psi
+\frac{\varepsilon^2}{2}\int_J(\psi^2-\psi'^2).
\]

Subtract (GR.10). The ordinary surviving-area gain is

\[
\boxed{|S_\varepsilon|-|S_0|
=\varepsilon\int_J(q-1)\psi
-\frac{\varepsilon^2}{2}\int_J\psi'^2>0}
\tag{GR.11}
\]

for every sufficiently small positive epsilon. The strict first-order coefficient follows from q>101/100 and psi nonzero. This explains precisely why the pointwise final-velocity condition in RC2 cannot be omitted from a claim of area-improving repair.

## 4. The global curvature majorant restores the worse sofa

On J the projective obstacle for bar h is affine, since its source curvature is one. The obstacle for h_epsilon is that affine function plus epsilon psi/k, and the two obstacles agree outside J. The original convex obstacle is a minorant of the new one; every convex minorant of the new one is bounded above by the original chord on J because their endpoint data agree. Hence their greatest convex minorants coincide.

All other quarters already have curvature at most one and are unchanged. Therefore GM2 gives

\[
R(K_\varepsilon)=K_0.
\tag{GR.12}
\]

Combining (GR.7), (GR.11), and (GR.12) proves:

**Theorem GR1 (failure of unconditional global-repair enclosure).** There are compact connected ambidextrous bodies S_epsilon of width 63/25>2, with full conventional turns and aligned horizontal faces, such that

\[
\boxed{|S_\varepsilon|>
\widetilde{\mathcal Q}(h_{R(\operatorname{conv}S_\varepsilon)})
=|S_0|.}
\]

In particular, applying the least curvature-dominated hull majorant is not an area-nondecreasing operation on all wide feasible bodies.

The examples can be chosen strictly below M. AF3 gives |S_0|<M because its width 63/25 differs from the candidate width. The exact area formula is continuous in epsilon, so sufficiently small epsilon keeps |S_epsilon|<M. The examples are not global maximizers and do not refute a theorem using maximality essentially. They do not invalidate the analytic width exclusion or CW4: the input h_epsilon violates the curvature cap somewhere, while K_0 itself satisfies CW4.

## 5. Reproducible exact scalar verification

Run, without Lean or CI:

```
python docs/ambidextrous/computer-assisted/verify_global_repair_counterexample.py
```

The checker uses only Python's standard-library Fraction arithmetic. Each constant-density solution has the form rho+A cos(t)+B sin(t), with rational coefficients. At a knot, changing rho by Delta updates A and B by -Delta cos(t) and -Delta sin(t), preserving the value and derivative. All knot sines/cosines are rational.

Using z=tan(t/2), the corner ordinate is a polynomial of degree at most four divided by (1+z^2)^2; p and q have quadratic numerators divided by 1+z^2. The upper-half partition is the union of the original knots and their reflected knots (1-z)/(1+z). Thus one verifies the entire continuum, not a grid of angles.

For each polynomial inequality, substitute z=l+(r-l)x and express its numerator in the Bernstein basis binom(n,j)x^j(1-x)^(n-j). Every basis element is nonnegative and their sum is one. Strict positivity of every rational coefficient proves the inequality on that whole interval. One interval in the reflected ceiling calculation is bisected; all other original intervals certify directly.

The executed checks used seven lower-ceiling intervals, six reflected-ceiling intervals, and three source-window inequalities. The largest bisection depth was one. No unresolved polynomial was accepted. The output, source hash, and a discovery/correction disclosure are recorded in the adjacent result JSON and review note.

These finite scalar checks certify the explicit example, not the unrestricted moving-sofa theorem. The geometric proof still requires the construction and area comparison in Sections 1--4. The earlier global functional and geometric dependencies remain written, self-reviewed proofs rather than independently verified results.
