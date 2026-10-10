# Attainment for the width-penalized right-angle cap problem

This proves the existence part of the weighted one-turn program proposed in OT.7. It does not assume Romik optimality, does not use Gerver's sharp area bound, and does not prove the value or uniqueness of this maximum. The objective is the signed cap-minus-full-niche functional, not the positive-part objective in the imported polygon search. Labels PA are local.

## 1. Precisely fixed domain

A normalized right-angle cap U is a compact convex subset of `[0,W] x [0,1]` for some W>0, with horizontal projection `[0,W]`, maximum ordinate one, and the downward-closure property

$$
(x,y)\in U,\quad0\le v\le y\quad\Longrightarrow\quad(x,v)\in U.
$$

In particular it contains its full bottom segment `[0,W] x {0}`. This is the standard full-right-angle cap class in these coordinates. Translation of any horizontal projection to start at zero does not affect the objective.

With `mu_t=(cos t,sin t)` and `nu_t=(-sin t,cos t)`, define

$$
N(U)=\{y\ge0\}\cap\bigcup_{0<t<\pi/2}
\{p:p\cdot\mu_t<h_U(t)-1,\ p\cdot\nu_t<h_U(t+\pi/2)-1\},
$$

$$
\mathcal A(U)=|U|-|N(U)|,
\qquad \Psi(U)=\mathcal A(U)-\tfrac12W.
\tag{PA.1}
$$

The subtraction is over the entire niche, even when it is not contained in U. Thus A(U) need not equal the ordinary area of `U minus N(U)`. No connectivity or feasibility claim for that difference is part of the domain definition.

## 2. Two elementary coercive bounds

**Lemma PA1.** Every cap in this domain satisfies

$$
\boxed{\Psi(U)\le\min\{W/2,\ 2\sqrt2-W/2\}.}
\tag{PA.2}
$$

**Proof.** Since the cap lies in a rectangle of area W and niche area is nonnegative, A(U)<=W, giving the first bound.

Put T=U minus N(U). Since U satisfies its outer support bounds and T avoids the forbidden quadrant at pi/4, T lies in the corresponding supporting unit hallway. That hallway is contained in the union of two full strips of width one, normal to mu_(pi/4) and nu_(pi/4). Each strip meets a horizontal line in an interval of length sqrt(2). T also lies in 0<=y<=1. Fubini therefore gives |T|<=2sqrt(2), with no connectedness hypothesis. Finally

$$
\mathcal A(U)=|T|-|N(U)\setminus U|\le|T|,
$$

so the second bound follows. QED.

These are compactness bounds for the auxiliary problem, not a new sharp bound on ambidextrous sofas.

The objective has a positive competitor without using any candidate theorem. Let U_c have upper boundary

$$
a(x)=\tfrac12+\sqrt{\tfrac14-(x-\tfrac12)^2},\qquad0\le x\le1,
$$

and bottom zero. Its upper support is

$$
h(t)=\tfrac12+\tfrac12\cos t+\tfrac12\sin t\quad(0\le t\le\pi).
$$

The corresponding inner corner height is `(1-sin t-cos t)/2 <= 0`, so no open forbidden quadrant meets y>=0. Hence N(U_c) is empty,

$$
|U_c|=\tfrac12+\pi/8,\qquad \Psi(U_c)=\pi/8>0.
\tag{PA.3}
$$

The strict quadrant inequalities are important at the endpoint angles, which are not included in the niche.

## 3. Upper semicontinuity of the signed objective

Consider a sequence of caps U_n with widths in a fixed compact interval `[w_0,w_1]`, where w_0>0. They lie in one compact rectangle. By compactness of convex bodies, a subsequence converges in Hausdorff distance to a compact convex U. One may obtain this directly from uniformly bounded, uniformly Lipschitz support functions and Arzela--Ascoli. Width, the two vertical extrema and the horizontal extrema pass to the limit. Downward closure also passes to the limit by approximating a given point and lowering its approximants. Thus U is again a normalized cap.

The limit contains a nondegenerate bottom segment and a point at height one, so it has nonempty interior. Convex-body area is continuous under Hausdorff convergence here. For completeness, outer neighborhood containment gives the upper limit, while inner homothetic copies about an interior ball lie in U_n eventually and give the lower limit. Letting the homothety tend to one proves convergence of areas.

The niche area is **lower** semicontinuous. At every point p with y>0 in N(U), one fixed interior angle witnesses two strict inequalities. Uniform support convergence makes the same inequalities true for U_n eventually. The line y=0 has zero planar area. Fatou therefore gives

$$
|N(U)|\le\liminf_n|N(U_n)|.
\tag{PA.4}
$$

All these niche areas are finite, uniformly. Indeed the rectangle bounds give

$$
h_U(t)\le W\cos t+\sin t,
\qquad h_U(t+\pi/2)\le\cos t.
$$

If y>=0, the second strict inner inequality excludes x<=0, and the first excludes x>=W. For a forbidden point, multiplying its two inequalities by sin(t), cos(t) respectively yields

$$
y<(h_U(t)-1)\sin t+(h_U(t+\pi/2)-1)\cos t
\le W/2.
$$

Consequently N(U_n) lies in the fixed finite-area rectangle `[0,w_1] x [0,w_1/2]`. Together with area and width continuity, PA.4 proves

$$
\limsup_n\Psi(U_n)\le\Psi(U).
\tag{PA.5}
$$

No convergence of a selected niche parametrization, contact pattern, or derivative of h has been assumed.

## 4. The existence theorem

**Theorem PA2 (signed penalized maximum is attained).** There is a normalized right-angle cap U_max such that

$$
\Psi(U)\le\Psi(U_{\max})\quad\text{for every normalized right-angle cap U}.
$$

**Proof.** PA.2 bounds the supremum above, and PA.3 makes it positive. Choose a maximizing sequence. Eventually its values are at least pi/16, so PA.2 puts its widths in

$$
\pi/8\le W_n\le4\sqrt2-\pi/8.
$$

Apply the compactness and upper semicontinuity just proved. The limit attains the supremum. QED.

The proof neither claims that N(U_max) is contained in U_max nor determines its contact or curvature structure. Those require additional arguments if needed for the sharp comparison.

## 5. Exactly what transfers from unpenalized variations

For any admissible family of caps with fixed horizontal axis supports,

$$
\Psi(U_\varepsilon)-\Psi(U_0)
=\mathcal A(U_\varepsilon)-\mathcal A(U_0).
\tag{PA.6}
$$

Thus a maximizer from PA2 maximizes A against these fixed-axis competitors. In a finite support-coordinate model, differentiability gives the exact algebraic rule

$$
\partial_i\Psi=\partial_i\mathcal A
-\tfrac12\partial_i[h(0)+h(\pi)].
$$

When the two axis supports are separate coordinates, only their two derivatives acquire the minus-one-half term. Interior coordinate derivatives are unchanged. This explains why the usual local floating-wall computations are relevant.

However, PA.6 is not maximality against **all** unpenalized caps. Nor does it justify a particular variation if that variation leaves the cap domain. Carrying the discrete balance estimate, approximation errors, pinned constraints and arm bounds through to U_max is still an unproved part of the proposed W-Gerver theorem.

The cap optimization above is full-angle by definition. There is no extra terminal-angle theorem to prove inside PA2. The separate problem of representing an arbitrary partially turning ambidextrous body by these full-angle caps remains open wherever the face criterion in OT4/OA.3 does not apply.

## 6. Status

This discharges the attainment subproblem in OT.7 without numerical optimization or the conjectured sharp constant. It does not prove `max Psi = M/2`, exclude the exceptional point-face configurations, or yield global ambidextrous uniqueness. Its role is to make the next maximizer-specific question mathematically well posed.

This is a pen-and-paper proof with self-review. It uses standard compactness and elementary measure arguments, not CI, Lean/Lake, or a computer certificate.
