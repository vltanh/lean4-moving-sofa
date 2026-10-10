# The exact convex tail regions preserved by the global repair

This gives a positive geometric identity relevant to the auxiliary-body organization in PR #9. The least curvature-majorant operation preserves a full family's **one-wall safe region** exactly. It does not preserve the paired-wall niche or the actual area obtained after intersection with the outer hull. The distinction is explicit and prevents the shadow-clipping failure from being hidden in a new notation.

The proof is convex duality in two variables, written out below. It uses the definition of GM2, not a numerical observation or the conjectured optimality. Labels TR are local to this note.

## 1. A single angular interval

Let J=[a,b] have length strictly less than pi and let m=(a+b)/2. Put

$$
n_t=(\cos t,\sin t),\quad
k(t)=\cos(t-m)>0,\quad z=\tan(t-m).
$$

For a continuous support profile h on J, define the closed convex one-wall safe region

$$
C_J(h)=\bigcap_{t\in J}\{x\in\mathbb R^2:x\cdot n_t\geq h(t)-1\}.
\tag{TR.1}
$$

It is generally unbounded; it is not asserted to be a sofa. Set phi(z)=(1-h(t))/k(t), and let Cphi be the greatest convex minorant of phi on the compact z interval. Define bar h=1-k Cphi, the quarterwise repair when J is a coordinate quarter.

**Theorem TR1 (one-wall invariance).**

$$
\boxed{C_J(h)=C_J(\bar h).}
\tag{TR.2}
$$

Moreover

$$
\boxed{\bar h(t)=1+\inf_{x\in C_J(h)}x\cdot n_t
\qquad(t\in J).}
\tag{TR.3}
$$

**Proof.** Since n_t=k(t)(n_m+z n_m^\perp), the function

$$
\ell_x(z)=-x\cdot n_m-z\,x\cdot n_m^\perp
$$

is affine in z. The point x belongs to C_J(h) exactly when ell_x<=phi on the whole interval. Every affine minorant of phi is a convex minorant, so it lies below Cphi. Conversely Cphi<=phi. Thus ell_x<=phi if and only if ell_x<=Cphi, proving (TR.2).

Every affine function of z has the form ell_x for a unique x in the plane. The greatest convex minorant of a continuous function on an interval is the supremum of its affine minorants; this follows from the supporting-line characterization of convex functions, with endpoint limits included. Consequently Cphi(z)=sup_{x in C_J(h)}ell_x(z). Substitute into bar h=1-k Cphi to obtain (TR.3). In particular the infimum is finite in each displayed direction. No boundedness of C_J is needed. QED.

For the Lipschitz support profiles used in GM2, its endpoint-contact proof also supplies the endpoint supporting lines. Thus (TR.3) includes the closed interval and does not silently omit an axis constraint.

This is not the assertion that a maximum of two-wall minima is invariant. It is a statement about an **intersection of all individual half-planes**, where each candidate point tests one affine minorant.

## 2. What actual tail bodies do under repair

Let K be a convex body and let bar K=R(K) be its least all-quarter curvature-dominated majorant. For a whole coordinate quarter J, Theorem TR1 gives one common unbounded safe region C=C_J(h_K)=C_J(h_barK). Therefore the clipped convex tail bodies satisfy

$$
B=K\cap C\subseteq\bar B=\bar K\cap C,
$$

and their exact difference is

$$
\boxed{\bar B\setminus B=(\bar K\setminus K)\cap C.}
\tag{TR.4}
$$

This identity is just set algebra after (TR.2), but its interpretation is important: only added hull points lying in C contribute to this particular safe tail. The total added hull area is not the safe-tail gain.

The same reasoning applies to the reflection exchanging the two turns. Intersecting the appropriate right-wall safe regions for both turns gives a common convex set C_R, and intersecting the left-wall safe regions gives C_L. Both are invariant under the all-quarter repair. Points of C_R satisfy the right inner-wall alternative at every angle for both turns; points of C_L satisfy the left alternative. After intersecting with the corresponding convex hull they also satisfy the outer-wall bounds.

Thus K intersect C_R and K intersect C_L are genuine simultaneously safe convex pieces for the full-turn constraints; their repaired versions grow according to (TR.4). This does not assert that these pieces cover the whole sofa: points using different wall alternatives at different angles can lie outside both. It also does not impose full-quarter endpoints on a body originally known to stop earlier.

For a **proper subinterval** J of a coordinate quarter, the repair defined using J preserves C_J by TR1. The all-quarter repair need not preserve every proper-subinterval safe region. That distinction matters for tail cuts at beta and pi/2-beta in a candidate-based certificate.

## 3. A fixed-point obstruction to simply iterating repair and saturation

The shadow-clipping family gives an exact test. Its saturated body B_z has actual hull H_z and

$$
R(H_z)=\bar K_z,\qquad
\mathcal E(\bar K_z)=B_z=\mathcal E(H_z)
$$

by SC2 and the definition of B_z. Hence the operation

$$
T\longmapsto\mathcal E(R(\operatorname{conv}T))
$$

has B_z as a fixed point, although its actual hull H_z violates open-quarter curvature domination and |B_z|<M. Re-extracting the actual hull and repeating the same operation does not remove that violation or increase its area.

This is not a failure of GM2: its output bar K_z has the stipulated curvature cap. The failure is to identify the actual hull of the surviving body with that output. The positive clipping term in SC.8 measures material that never survives, and (TR.4) shows why a full hull-area charge cannot replace the clipped-body calculation.

## 4. Consequence for a coercive extremal framework

PR #9's source retains auxiliary convex bodies subject to wall and inclusion constraints before applying its quantitative certificate. TR1 suggests a corresponding natural language for an ambidextrous comparison: the one-wall convex regions are exact geometric objects, while their clipped tail bodies and the mixed-wall core must be accounted for separately.

What remains unproved is a sharp inequality for that coupled **ordinary-area** decomposition. Neither TR1 nor PR #9 establishes such an inequality for two-turn maximizers. No further auxiliary maximum is declared to be the missing area bound. The already proved width exclusion and the conditional CW4 route are unchanged.

The identities in this note need no computer assistance. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. They are written proofs with self-review, not an independent audit of the historical branch.
