# Superlevel trimming for the signed width-penalized cap objective

This is a maximizer-specific geometric reduction for the signed one-turn problem PA2. It does not assume a curvature bound, niche containment, a contact pattern, or the conjectured sharp value. It does not assert that an arbitrary ambidextrous maximizer is a maximizer of this auxiliary objective.

Labels ST are local. A cap and its full niche have exactly the definitions in [PA.1](one-turn-penalized-attainment.md). Throughout this note the niche area is subtracted **without clipping it to the cap**.

## 1. Inclusion monotonicity of the full niche

If nonempty compact caps V and U satisfy V subset U, their supports satisfy h_V <= h_U. Every strict forbidden quadrant for V at an angle t is therefore contained in the corresponding quadrant for U. After taking the union and intersecting with y>=0,

$$
N(V)\subseteq N(U).
\tag{ST.1}
$$

A horizontal translation of the cap translates the full niche by the same vector and does not change its area. Thus nested caps can be compared before renormalizing their left endpoints to zero.

## 2. Trim to the part of the upper roof above the penalty height

Let 0<lambda<1 and define

$$
\Psi_\lambda(U)=|U|-|N(U)|-\lambda W(U).
$$

Write the cap as

$$
U=\{(x,y):x\in I=[l,r],\ 0\le y\le a(x)\},
$$

where a is the upper roof, is concave, and attains maximum one. It is continuous on its whole interval. Interior continuity is standard concavity; at an endpoint, concavity gives a limiting height at least the endpoint value, while compactness gives the reverse inequality. Put

$$
J_\lambda=\{x\in I:a(x)\ge\lambda\},\qquad
U_\lambda=U\cap(J_\lambda\times\mathbb R).
$$

The set J_lambda is a nonempty compact interval with positive length: continuity and max(a)=1>lambda give a one-sided interval even if a maximizer is at an endpoint. The new cap is compact, convex, downward closed and still has maximum height one. It is in the PA cap domain after horizontal translation.

**Theorem ST1 (exact gain under superlevel trimming).**

$$
\boxed{
\Psi_\lambda(U_\lambda)-\Psi_\lambda(U)
=\int_{I\setminus J_\lambda}(\lambda-a(x))\,dx
 +|N(U)\setminus N(U_\lambda)|\ge0.
}
\tag{ST.2}
$$

If a(x)<lambda anywhere on I, the inequality is strict.

**Proof.** The cap area lost is the integral of a over I minus J_lambda. The width lost is the length of that same set. ST.1 gives nested, finite-measure niches, so their area difference is the area of their set difference. These three observations give the equality. On the removed set lambda-a is positive; if the removed set is nonempty, continuity supplies a positive-length interval with a positive integral. QED.

No statement that the removed niche lies inside the removed cap is needed. Its full area change is nonnegative independently of that geometry.

## 3. Consequences at lambda=1/2

Let P be the attained maximum supplied by PA2. Every maximizing cap U satisfies

$$
\boxed{a(x)\ge\tfrac12\text{ on its entire projection}.}
\tag{ST.3}
$$

Equivalently it contains its full projection rectangle I times [0,1/2]. In particular both vertical end-edge lengths are at least one half. A cap violating ST.3 has an explicit strictly better competitor, rather than merely failing a formal stationarity equation.

There is also a quantitative statement which does not insert an unproved value for P:

$$
\int_I(\tfrac12-a(x))_+\,dx
+|N(U)\setminus N(U_{1/2})|
\le P-\Psi(U).
\tag{ST.4}
$$

This follows from ST.2 and Psi(U_(1/2))<=P. It is not an estimate using the conjectural M/2 in place of P.

The same conclusions hold for maximizers of Psi_lambda, whenever that maximum exists, with one half replaced by lambda. The elementary compactness argument in PA2 extends to 0<lambda<1 using Psi_lambda<=min((1-lambda)W,2sqrt(2)-lambda W) and a positive cap competitor for lambda<1.

## 4. Limits of this reduction

ST.3 does **not** prove that the full niche has height at most one half, that it lies inside the cap, or that the end-edge lengths are exactly one half. It also does not yield upper curvature domination. Those would require different comparisons.

The reduction applies to a maximizer of the signed one-turn objective; it is not automatically a permissible operation on an ambidextrous body with a fixed opposite motion. Nor does it eliminate the positive clipping term in the two-cap identity OA.2. It is useful precisely because PA2 supplies an actual maximizer of this signed objective to which ST1 can be applied without those extra premises.

This note is a written elementary argument with self-review. No numerical computation, CI, or Lean/Lake compilation is a proof input.
