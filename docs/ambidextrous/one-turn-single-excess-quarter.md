# At most one quarter of a weighted maximizer can have excessive curvature

**Scope.** This strengthens the remaining one-turn reduction: every maximizer of the signed width-penalized cap objective has unit curvature on at least one of its two open upper quarters. Any remaining excess is confined to one explicit short interval after a possible horizontal reflection. The sharp weighted value and unrestricted ambidextrous optimality are not proved by this note. Labels SE are local.

Inputs are HF1--HF3, the genuine connected one-turn body supplied by PT/TS, the stronger arm criterion CG1, and the established ordinary moving-sofa upper bound of Gerver's area. Unlike an invalid transfer of one-turn maximality, the last input is applied only as an area bound to an actual feasible one-turn body. No assertion that the weighted cap maximizes unpenalized area is made.

## 1. An explicit rational bound for the ordinary one-turn problem

Let G be Gerver's area. The existing one-turn optimality theorem bounds the area of every feasible connected one-turn sofa by G. A primary reference is Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826. This is an external mathematical dependency, not a new proof or a new verification of that theorem.

For the constants needed here, no rounded value of G is used. At the pinned repository baseline `942c3b85553843c6d7d4ced926c1e73e31394989`, `MovingSofaOptimality/Gerver/AreaBounds.lean` gives the following six enclosures for the reference parameter solution:

| Named enclosure | Interval |
|---|---|
| ga_curveArea_A_mem | [7201/10000,7202/10000] |
| ga_curveArea_C_mem | [13339/10000,13340/10000] |
| ga_segArea_mem | [8068/10000,8069/10000] |
| ga_curveArea_x_mem | [6013/10000,6015/10000] |
| ga_curveArea_B_mem | [-31/10000,-30/10000] |
| ga_curveArea_D_mem | [-370/10000,-369/10000] |

The area formula there is A+C+segment-x+B+D. Taking the corresponding upper endpoints gives

$$
\boxed{G\le\frac{7202+13340+8069-6013-30-369}{10000}
=\frac{22199}{10000}=:G_0.}
\tag{SE.1}
$$

The source enclosures assume the reference solution and its stated parameter bounds, established elsewhere in the repository. This note uses that existing chain; it does not claim to have compiled or independently audited it. Its relevant blob is `2bfae7fc6cd56c35793f18843cc91ed6e1462aa2`.

## 2. A perimeter lower bound, not an unjustified perimeter maximum

Let U be any global maximizer of the signed objective Psi. HF gives

$$
T=W(U)/2>1,\qquad
U=V+([0,T]\times[0,1/2]),
$$

where V is a convex cap of width T and height one half, with zero vertical end edges and a point top face. Write its base endpoints as (0,0),(T,0), and its top point as (A,1/2), where 0<=A<=T. Its upper-boundary length L_c is at least the sum of the lengths of the two chords joining these three points:

$$
L_c\ge\sqrt{A^2+1/4}+\sqrt{(T-A)^2+1/4}
\ge\sqrt{T^2+1}.
\tag{SE.2}
$$

The second inequality is the triangle inequality for the vectors (A,1/2) and (T-A,1/2). Rectifiability and the chord lower bounds hold for convex boundaries without smoothness. HF3 supplies the stationary identity 2 Psi(U)=L_c. Thus

$$\Psi(U)\ge\tfrac12\sqrt{T^2+1}.\tag{SE.3}$$

This is a lower bound on the value at a stationary weighted maximizer, coupled with its face length. It is not a universal lower bound for the signed objective on arbitrary caps.

## 3. Apply the actual one-turn area bound

PT3 and TS1 show N(U) lies inside U and has height at most one half. ST1 gives the full half-height rectangle inside U. Hence B=U minus N(U) is compact and connected, with every vertical section containing its point at height one half. The canonical placements give it a full one-turn motion. Therefore B qualifies for the ordinary moving-sofa upper bound, and

$$
|B|=|U|-|N(U)|=\Psi(U)+W(U)/2=\Psi(U)+T\le G_0.
$$

Combining with SE.3 gives

$$\boxed{T+\tfrac12\sqrt{T^2+1}\le G_0.}\tag{SE.4}$$

This does not import an unpenalized maximizing-cap premise. Only feasibility of B, already obtained by a separate construction, is used.

**Theorem SE1 (weighted top length below 48/35).** Every weighted maximizer has

$$\boxed{1<T<48/35.}\tag{SE.5}$$

**Proof.** The left side of SE.4 is strictly increasing for T>=0. At t0=48/35, G_0-t0>0, and exact arithmetic gives

$$
t0^2+1-4(G_0-t0)^2=\frac{1471551}{1225000000}>0.
$$

Thus t0+sqrt(t0^2+1)/2>G_0, contradicting SE.4 if T>=t0. The lower bound was HF1. QED.

In particular the cap width is less than 96/35. This estimate concerns weighted maximizers and does not improve the unrestricted ambidextrous width theorem without a new reduction.

## 4. The two endpoint arms cannot both be bad

The endpoint arms satisfy the exact identity

$$d_R+d_L=W+T=3T.$$

Consequently

$$
\min(d_R,d_L)\le\tfrac32 T<72/35<\sqrt{17}/2,
$$

where the last comparison is exact because

$$\frac{17}{4}-\left(\frac{72}{35}\right)^2=\frac{89}{4900}>0.$$

The improved criterion CG1 gives:

**Corollary SE2 (one good quarter for every weighted maximizer).** Every weighted maximizer satisfies at least one of

$$\boxed{f''+f\le1\text{ a.e.},\qquad g''+g\le1\text{ a.e.}}\tag{SE.6}$$

on the entire interval (0,pi/2). After horizontal reflection if necessary, one may arrange that g''+g<=1 everywhere and the only possible curvature excess is that of f, supported by CG2 inside

$$\boxed{(\arcsin(2/9),1/2).}\tag{SE.7}$$

The reflection is a symmetry of the weighted problem, not averaging two caps or asserting symmetry of an optimizer. The remaining offending arm, if any, must exceed sqrt(17)/2 and is still bounded above by 9/4.

## 5. What this does not establish

One good quarter is not two good quarters. It is invalid to take the good quarter of one maximizer and the reflected good quarter of another and assume their concatenation is a feasible cap with at least the same objective. Likewise a one-sided curvature result is not sufficient for AR4 or the signed-roof theorem as presently stated.

The new conclusion removes simultaneous high-arm obstructions and localizes the remaining weighted problem to a single short window, using a chord bound and an existing ordinary one-turn area bound rather than a hidden-exposure hypothesis. The remaining task is to exclude the possible excess in that window or prove an area comparison that pays it.

Even a completed weighted theorem still requires a valid upper comparison for arbitrary two-turn bodies. The symmetric construction from a weighted maximizer has zero clipping, but it has not been proved to dominate every ambidextrous competitor. These are separate quantifiers.

All new inequalities here have hand proofs. A short rational check verifies only SE.1 and the displayed rational comparisons. No CI, Lean/Lake compilation, dependency installation, manuscript build or long numerical search is used. Written arguments and their historical dependencies remain subject to independent review.
