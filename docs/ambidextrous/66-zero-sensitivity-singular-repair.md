# 66. A zero contact coefficient makes the feasibility repair cheaper than the area gain

The measure estimate in Note 65 weights the first source curvature by |q| and the second by |p|. This note treats a complementary case: singular second-source curvature where p=0 and q is nonzero, and the exchanged first-source case. A circular replacement may close a pinching fiber, so it is not called feasible without correction. Instead its uniform hallway error is estimated and repaired by an explicit scaling. The scaling cost is smaller than the retained area gain.

The conclusion applies to general bodies, not a candidate neighborhood, and permits partial endpoint angles. Strict outer clearance and a floating source normal are still hypotheses. No claim is made about the simultaneous-zero case p=q=0 or about a masked outer edge.

## 66.1 A uniform error can be repaired exactly

Let T be compact and connected and contained in a compact convex outer set K_c. Suppose the prescribed canonical motions for K_c have all their outer inequalities satisfied on T. Suppose also that, for each of their angles and each z in T, at least one inner inequality holds with error at most e>=0:

\[
z\cdot u\geq h_{K_c}(u)-1-e
\quad\text{or}\quad
z\cdot v\geq h_{K_c}(v)-1-e.
\tag{66.1}
\]

Assume K_c has width at most one in all prescribed incoming and terminal strip normals. Set lambda=1/(1+e). Multiplying (66.1) by lambda gives the exact inner disjunction for the support heights lambda h_{K_c}, since lambda(1+e)=1. The outer bounds and endpoint widths also hold after scaling. These heights define continuous rigid hallway placements at the same angles.

**Lemma 123 (uniform inner-error repair).** The body lambda T is genuinely feasible for both complete prescribed motions, with the same endpoint angles. Its area is |T|/(1+e)^2.

**Proof.** The preceding scalar inequalities give every hallway and endpoint inclusion. Scaling preserves compactness and connectedness, and the canonical placements have proper-motion histories. Initial translations may be adjusted within the incoming arms as in Proposition 14; no initial rotation or reflection of the body is inserted. QED.

The enclosing support data need not be the actual support function of T. Containment suffices. This lemma retains the area cost: a first-order error cannot be discarded in a first-variation argument.

## 66.2 A sharper roof estimate when p is small

Fix a compact interval around an interior lower-turn angle t_0. On a smaller J=[t_0-r,t_0+r], keep f fixed and replace g by a circular majorant g_c>=g agreeing at the endpoints and satisfying g_c''+g_c=1. Put

\[
u=g_c-g,\quad U=\|u\|_\infty,
\qquad |p|\leq a_r,
\qquad |q|\geq\eta>0
\tag{66.2}
\]

on all one-sided traces on J. Assume q has one fixed sign there, U<=C_0 r, and all old supports and first derivative traces are uniformly bounded. The constants in what follows may depend on that bound, eta, C_0, and the fixed interior angular interval, but not on r.

The two wall heights are

\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
L_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\]

Only L changes, by u/cos(t). Let I_r contain all old and new corner abscissae for t in J. Its length is O(r): the old corner is Lipschitz and the new displacement is O(U)=O(r). For any x in I_r and t in J,

\[
|x-c_x(t)|\leq C r,
\]

\[
|\partial_t R_t(x)|\leq C(r+a_r),
\qquad
\partial_t L_t(x)=q(t)/\cos t+O(r).
\tag{66.3}
\]

These identities follow from (35.1); they hold almost everywhere and can be integrated because the wall heights are absolutely continuous. For small r, L_t(x) is strictly monotone with the sign of q and with derivative magnitude at least a fixed positive number.

The changed family L_c is affine in tan(t). Endpoint agreement implies its value at any t is at most the larger old endpoint value. Also L_c(t,x)>=L(t,x). Therefore there is a parameter tau, toward the maximizing endpoint, such that

\[
L_\tau(x)=L_{c,t}(x),\qquad |\tau-t|\leq C U.
\]

The first estimate in (66.3) gives

\[
R_\tau(x)\geq R_t(x)-C(r+a_r)U.
\]

Thus

\[
\min(R_\tau,L_\tau)
\geq\min(R_t,L_{c,t})-C(r+a_r)U.
\tag{66.4}
\]

Outside I_r the complete old and new roofs agree: to one side the minimum is R throughout J and unchanged; to the other it is L throughout J and its supremum is unchanged by the affine, endpoint-matched replacement. Constraints outside J are unchanged.

**Lemma 124 (small-coupling roof bound).** The complete lower roof rises by at most

\[
\boxed{e_r=C(r+a_r)U}
\tag{66.5}
\]

at every horizontal coordinate. It never decreases. The statement does not assume a unique active parameter, a stable contact pattern, a positive surviving fiber, or differentiability of the roof.

**Proof.** On I_r, (66.4) supplies an old parameter against every new one. Take the supremum and include the unchanged angles. Off I_r use the preceding equality. Raising g makes each changed minimum nondecreasing, proving the other sign. QED.

For a first-source f replacement, exchange R and L: the analogous hypotheses are |q|<=a_r and |p|>=eta with fixed sign. The changed R family is affine in -cot(t). The same proof shifts toward its maximizing endpoint. Reflection gives the upper-turn versions.

The improvement over the generic roof estimate O(U) is the small factor r+a_r. This factor, rather than a statement that a pinch is harmless, pays for the actual feasibility correction below.

## 66.3 Singular-continuous source mass on the zero-coefficient set

Consider the second source measure sigma_g and the set

\[
Z_p=\{t:p_-(t)=p_+(t)=0\}.
\]

On a compact interval, (65.2) shows that p+C t has a nonnegative derivative measure for a sufficiently large constant C. It is continuous on Z_p and equals C t there. The Stieltjes restriction argument in Lemma 108 therefore gives

\[
Dp|_{Z_p}=0,
\qquad\sigma_f|_{Z_p}=(q+1)dt|_{Z_p}.
\tag{66.6}
\]

In particular sigma_f gives zero mass to a Lebesgue-null subset of Z_p, including the part carrying singular-continuous sigma_g. By differentiation of Radon measures, at sigma_g-singular-almost every such point,

\[
\frac{|J_r|}{\sigma_g(J_r)}\to0,
\qquad\frac{\sigma_f(J_r)}{\sigma_g(J_r)}\to0.
\tag{66.7}
\]

Use the good doubling scales from Section 58.5, and put m_r=sigma_g([t_0-r/2,t_0+r/2]). At those scales,

\[
\sigma_g(J_r)\leq4m_r,\quad r=o(m_r),\quad
\sigma_f(J_r)=o(m_r),\quad m_r\to0.
\tag{66.8}
\]

If q(t_0) is nonzero, delete the countable source jump sets and restrict to sufficiently small intervals to get a fixed sign and |q|>=eta. Equation (65.2), p(t_0)=0, and (66.8) give

\[
a_r:=\sup_{J_r}|p|\leq\sigma_f(J_r)+C r=o(m_r).
\tag{66.9}
\]

Apply Lemma 106 to the second source. It produces the circular support replacement with U=O(m_r r), nonnegative outward gluing, and hull gain at least c m_r^2 r. Lemma 124 now gives

\[
\boxed{e_r=O((r+a_r)m_r r)=o(m_r^2r).}
\tag{66.10}
\]

The gain and error are on different scales. This is stronger than estimating the total area removed by a narrow corner band: it estimates the **maximum constraint violation**, which is what must be repaired at a point connection.

The first-source version uses the zero set of q. Restricting Dq in (65.2) gives sigma_g=(1-p)dt there, and the same relative-density argument applies to singular sigma_f.

## 66.4 A connected comparison body before the small scaling

Let S be its same-hull canonical saturation for correctly signed motions, and suppose the unique exposed point of K at the chosen nonatomic source normal is strictly clear of the closures of both old swept niches. The replacement window must avoid every pinned incoming or terminal strip normal and every axis normal.

Construct

\[
T_r=K_c\setminus(W_-\cup W_+),
\tag{66.11}
\]

using the **old** swept niches, not the enlarged ones. It contains the old S. Its projection is unchanged, and each vertical section is an interval containing an old body point. Thus T_r is compact and connected. All added hull points tend to the unique exposed point, as proved in Section 58.3; strict clearance therefore retains all added hull area for small r. Consequently

\[
|T_r|-|S|\geq c m_r^2r.
\tag{66.12}
\]

This T_r is not falsely asserted to follow the new exact motions. The new outer supports contain it, the endpoint widths are unchanged, and Lemma 124 bounds its possible inner error by e_r. A vertical roof error e_r bounds a wall scalar-product error by at most e_r, since sine and cosine are at most one. The opposite turn has no error. Lemma 123 makes

\[
\widehat S_r=T_r/(1+e_r)
\]

genuinely feasible for both motions. If A=|S| and G_r=|T_r|-A, then exactly

\[
|\widehat S_r|-A
=\frac{G_r-A(2e_r+e_r^2)}{(1+e_r)^2}>0
\tag{66.13}
\]

for small chosen radii, by (66.10) and (66.12).

**Theorem 125 (zero-sensitivity singular exclusion without fiber clearance).** A globally maximizing canonical body has no singular-continuous second-source curvature on the set of floating normals with p_-=p_+=0, q nonzero, and a strictly clear exposed outer point. The exchanged statement holds for first-source curvature where q_-=q_+=0 and p is nonzero. No neighborhood fiber-gap condition or affine ceiling is required.

**Proof.** At almost every singular point in the stated set, (66.7) and the good scales apply. Equations (66.11)–(66.13) then give a strictly larger compact connected feasible body. This contradicts maximality. QED.

The differentiation input is the same standard Radon-measure theorem explicitly cited in Section 58.5. The measure identity (66.6) is essential; without it there is no reason for the companion variation to be o(m_r).

## 66.5 The corresponding atom test

Suppose sigma_g has an atom at t_0, both traces of p are zero, and both traces of q have the same nonzero sign. Then sigma_f has no atom there, p tends uniformly to zero on shrinking intervals, and |q| stays bounded away from zero. Lemma 103 gives U=O(r), while (66.5) gives e_r=o(r).

If a compact relative-interior segment of the exposed outer edge is strictly clear of both old niches, its added triangle in T_r has area at least c r by Section 56.4. The same scaling comparison gives a strict gain, since the correction costs only o(r).

**Corollary 126.** Such an edge atom cannot occur at a global maximizer, even if the changed corner is an actual pinching point. The exchanged first-source and reflected upper-turn statements hold as well.

This requires the same-sign nonzero traces of the other velocity. A jump crossing that sign, a simultaneous zero of both velocities, a masked edge, or a pinned normal is not covered. The support replacement may create endpoint atoms; no claim is made that it regularizes the whole hull in one step.

## 66.6 What has and has not been obtained

The pinch-measure argument of Note 65 and the present vanishing-coefficient argument are complementary. The former controls source singular curvature when its graph coefficient is uniformly positive. The latter supplies an actual maximality contradiction at some zeros of that coefficient, paying explicitly for any lost feasibility by a smaller-order scaling.

They do not establish global absolute continuity or the sharp density cap. Simultaneously stationary corners, mixed-trace degeneracies, obstructed outer points and pinned/end-angle conditions still need treatment. No contact multiplier is discarded merely because the old affected fiber has zero area.

All estimates and comparisons are pen-and-paper. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. The written arguments remain subject to independent checking.
