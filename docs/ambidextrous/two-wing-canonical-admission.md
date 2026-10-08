# Canonical wings: arbitrary heights, a conditional admission theorem, and a junction obstruction

**Status: written, self-reviewed arguments. Not independently audited.** Numerical statements are floating-point diagnostics and are labelled as such. No CI or Lean/Lake process was used. The baseline is PR #3 at `cb91e77`. Existing manuscript and Lean files are unchanged. **Unrestricted optimality and uniqueness are still not proved.**

This note works on roadmap gates R3, R4 and R5 for the two-wing certificate of [TW](two-wing-domain.md), [WS](two-wing-strip-quadratic.md), [WC](two-wing-calibration.md), [CS](two-wing-cut-slack.md), [SQ](two-wing-slack-quadratic.md) and [NH](two-wing-near-full-height.md). The labels GH, CW, CA and JX are local to this note.

## 0. Results

1. **GH1 (R4).** The cut-slack calibration extends to arbitrary unequal wing heights, including *crossed* wings, where one wing touches only the top of the strip and the other only the bottom. NH1 does not cover crossed wings. The sufficient condition is two explicit linear inequalities in the three normalised trace deficits. The finite algebra is checked exactly: 8 rational identities pass and 3 deliberate mutations are rejected.
2. **CW1 (R3).** The depth-defined *canonical wings* of any convex hull in the strip are nonempty, compact, convex, lie in the strip and satisfy TW.1 automatically.
3. **CW3 and CW4 (R5).** Assume the contact velocities satisfy condition (M): p ≤ 0 on [β, π/2] and q ≥ 0 on [0, b] for both motions. The candidate satisfies (M), with p = 0 exactly at β and q = 0 exactly at b. Under (M), whether a surviving point lies in a wing is decided by the four cut walls alone (CW3). Under zero cut slack and outward cut arms, every point that lies beyond the cut walls and outside the wing quadrants has clockwise winding number one with respect to the core curve (CW4). This lemma uses neither (M) nor regularity.
4. **Theorem CA.** Take a connected body with both quarter turns complete. Assume (M) and four further conditions: core regularity, zero cut slack, outward arms, and the order of the two apexes. The candidate satisfies all of them, and only (M) is tight there. Then the ordinary-area admission |S| ≤ Ŵ(R, D) holds for the canonical wings. With GH1 this gives a conditional optimality-and-uniqueness theorem (Corollary CA2). Its hypotheses differ from the curvature domination of [CW4 (curvature-only wide hulls)](curvature-only-wide-hulls.md); that note's label CW4 is unrelated to the lemma CW4 here.
5. **JX (R5, negative).** Without (M) at the junctions, the canonical admission is false. The β-wall can touch R only at or above z₋(β) + p(β⁺) n_{β+π/2} (JX1). If p(β⁺) > 0, the core curve enters the wing side and closes a loop with negative winding. Hulls arbitrarily close to the candidate do this. Numerically, |S| − Ŵ is positive, converges under refinement, and equals the loop area to within about 10%. Since (M) holds with equality at the candidate, it cannot be obtained from proximity to the candidate.
6. **New mandatory test body.** The *shaved Romik hull* has facets of depth ε at the normals ±π/2 ± β. It violates both the curvature hypothesis of curvature-only CW4 and (M), so neither conditional route covers it. Two other families show the routes are complementary. Horizontally compressed hulls satisfy curvature-only CW4, but they violate (M) and the canonical admission fails on them numerically. Hulls shaved at ±π/4, ±3π/4 have facets, so curvature-only CW4 does not apply, but the canonical admission holds on them numerically.

## 1. Notation

Write L = π/2, b = L − β, n_t = (cos t, sin t), y = tan β and k = sin 2β, where β = arctan Y is Romik's angle. Here y is a scalar, not a coordinate. Let K be a compact convex body in the strip 0 ≤ x₂ ≤ 1 touching both boundary lines, with support function h. Put

$$
\Phi_\theta(x)=h(\theta)-x\cdot n_\theta ,
$$

the depth of x below the supporting line of K with normal n_θ. For another convex body B, write Φ^B_θ(x) = h_B(θ) − x·n_θ.

**Tight-wall envelope.** The lower motion at angle t ∈ [0, L] removes the open quadrant Q(t) = {Φ_t > 1, Φ_{t+L} > 1}. The reflected motion removes Q^ρ(t) = {Φ_{−t} > 1, Φ_{−t−L} > 1}. The second formula follows from ρx·n_s = x·n_{−s} + sin s and h_{ρK}(s) = h(−s) + sin s. Put

$$
T(K)=K\setminus\bigcup_{t\in[0,L]}\bigl(Q(t)\cup Q^\rho(t)\bigr).
$$

Let S be a body with both quarter turns complete in the common incoming normalisation, and let K = conv S. Then S ⊆ T(K), because the actual walls at every angle dominate the tight ones. This is the canonical-placement reduction of the earlier notes. It is cited, not re-proved.

**Contact velocities.** These are the same as in AF3 and SC3. Since h is Lipschitz, the following hold almost everywhere:

$$
p(t)=h'(t)-h(t+L)+1,\qquad q(t)=h'(t+L)+h(t)-1,
$$
$$
p^\rho(t)=-h'(-t)-h(-t-L)+1,\qquad q^\rho(t)=-h'(-t-L)+h(-t)-1 .
$$

The last two are the velocities of h^ρ(t) = h(−t) + sin t. The lower corner x(t) = (h(t) − 1) n_t + (h(t+L) − 1) n_{t+L} has velocity p n_t + q n_{t+L}.

## 2. GH1: arbitrary unequal heights with arbitrary cut slack

Use the relaxed data and actual-intersection functional Ŵ of CS.1–CS.3. The cut slacks r_±, d_± are nonnegative, and s_R, e_R, s_D, e_D are as in SQ.1. Complete the actual corners by CS1. Translate both wings vertically together until the higher of the two tops is at the top of the unit strip. If necessary, reflect horizontally and exchange the wings so that this is the right wing. Define A, B₀, C₀ ≥ 0 by WS.7: A is the left top deficit, B₀ the right bottom deficit and C₀ the left bottom deficit, each divided by cos β. NH1 is the special case B₀ = C₀.

**Lemma GH2 (exact remainder).** Minimise the arc interpolants, the core endpoints and (X, Z, z₀) as in WS.2–WS.9, keep the four cut slacks of SQ.6, and use the general traces of WS.8:

$$
(U,V)=(-z_0,-A-z_0),\qquad (U^\rho,V^\rho)=(-B_0+z_0,-C_0+z_0).
$$

The minimised finite remainder is then exactly

$$
B_{\rm fin}=P_k(A,B_0,C_0)+P_{\rm cut}(s,e)+\mathcal C,
\tag{GH.1}
$$

where P_k is WS.10, P_cut is SQ.9, and the general mixed term is

$$
\mathcal C=-\alpha_R s_R-\alpha_D s_D-\gamma\,(e_R+e_D),
\tag{GH.2}
$$

with

$$
\alpha_R=\tfrac{1-y}2A+B_0+\tfrac{1-y}2C_0,\qquad
\alpha_D=A+\tfrac{1-y}2B_0+C_0,\qquad
\gamma=\tfrac{1-y}4\,(A+B_0-C_0).
\tag{GH.3}
$$

The 2×2 and 3×3 Hessians are exactly those of WS.6 and WS.9/SQ.8, so both minimisations are global. At B₀ = C₀ = T, GH.2 reduces to NH.8. At zero slack the remainder reduces to WS.10, and at zero heights to SQ.9. All of these are exact rational identities in y, verified by `computer-assisted/check_two_wing_general_height.py`.

**Identity GH.4 (absorption).** Put E = e_R + e_D and Δ = e_R − e_D. Let a = (y² + 2y + 3/y)/8 and β' = (1 + 3/y)/8; the letter β' is a coefficient here, not an angle. Let

$$
\varrho=\tfrac y4\bigl[s_R(1-s_R)+s_D(1-s_D)+y\bigl(s_R(1-s_D)+s_D(1-s_R)\bigr)\bigr]\ \ge0 .
$$

Then

$$
y(s_R+s_D)+B_{\rm fin}
=\Bigl(\tfrac{y(3-y)}4-\alpha_R\Bigr)s_R+\Bigl(\tfrac{y(3-y)}4-\alpha_D\Bigr)s_D
+(aE^2-\gamma E)+\beta'\Delta^2+P_k+\varrho .
\tag{GH.4}
$$

This is also checked exactly.

**Theorem GH1.** Let R, D be nonempty compact convex wings in one unit strip satisfying TW.1, with arbitrary cut slacks. Assume

$$
\alpha_R+|\gamma|\le\tfrac{y(3-y)}4,\qquad \alpha_D+|\gamma|\le\tfrac{y(3-y)}4 .
\tag{GH.5}
$$

Then Ŵ(R, D) ≤ M. Equality holds exactly for the reference wing pair up to a common horizontal translation.

**Proof.** After completion, the exact quadratic expansion and the first variation CS2 give

$$
M-\widehat{\mathcal W}\ \ge\ \sum_{B}\int_\beta^{\pi-\beta}\mu(1-w_B)+y(s_R+s_D)+B_{\rm fin}.
$$

This is the same chain as SQ.10 and NH1, with nonnegative residuals discarded. Since |e_R| ≤ s_R and |e_D| ≤ s_D, we have |E| ≤ s_R + s_D, so aE² − γE ≥ −|γ|(s_R + s_D). By GH.4, the right-hand side is at least

$$
\Bigl(\tfrac{y(3-y)}4-\alpha_R-|\gamma|\Bigr)s_R+\Bigl(\tfrac{y(3-y)}4-\alpha_D-|\gamma|\Bigr)s_D+P_k .
$$

Each coefficient is nonnegative by GH.5. Also P_k ≥ 0 by the copositive factorisation WS.11, which is valid since 1/2 < k < 1.

For the equality case, the width integral must vanish. Since μ > 1/8, every width equals one on [β, π − β], including the vertical width. Both wings then span the strip, so A = B₀ = C₀ = 0, and SQ1's equality analysis identifies the reference pair. The completion has gained no area. ∎

**Remarks.**
- GH.5 contains NH1. With B₀ = C₀ = T, the binding inequality is (5 − y)A/4 + (3 − y)T/2 ≤ y(3 − y)/4, which follows from A + T ≤ y/2 as in NH.11.
- A crude sufficient form is A + B₀ + C₀ ≤ y(3 − y)/(5 − y) ≈ 0.171.
- For crossed wings with A = B₀ and C₀ = 0, GH.5 allows deficits up to y(3 − y)/(4(2 − y)) ≈ 0.118.

*Diagnostic (floating point; not part of the proof).* I minimised the finite remainder over the slack box along rays in (A, B₀, C₀). The table compares the level at which that minimum first becomes negative with the GH.5 threshold.

| ray | first negative free minimum | GH.5 threshold |
|---|---|---|
| A only | 0.230 | 0.171 |
| crossed, A = B₀ | 0.149 | 0.118 |
| shared bottom, B₀ = C₀ | 0.149 | 0.149 |
| A = B₀ = C₀ | 0.096 | 0.080 |

Among 400 random height triples, the free minimum was nonnegative at every sample inside GH.5.

## 3. Canonical wings

Let

$$
J_R=[\beta,L]\cup[-L,-\beta],\qquad J_D=[L,\pi-\beta]\cup[\pi+\beta,3L],
$$

and define

$$
R=\{x\in K:\Phi_\theta(x)\le1\ \forall\theta\in J_R\},\qquad
D=\{x\in K:\Phi_\theta(x)\le1\ \forall\theta\in J_D\}.
$$

Equivalently, R consists of the points of K lying in the outgoing arm of both motions for every angle in [β, L], and D of those lying in the incoming arm for every angle in [0, b]. These are the "actual safe pieces" requested in R3.

**Lemma CW1.** R and D are nonempty, compact and convex, lie in K, and satisfy TW.1.

**Proof.** Each is an intersection of K with closed half-planes {x·n_θ ≥ h(θ) − 1}. For θ ∈ J_R, h_R(θ) ≤ h(θ) and h_R(θ + π) ≤ 1 − h(θ), so w_R(θ) ≤ 1. Every direction in [β, π − β] is either in J_R or differs by π from a direction in J_R, and width is π-periodic. The case of D is symmetric.

For nonemptiness, let x₀ be a support point at θ = 0. Every z ∈ K − x₀ has z₁ ≤ 0 and −x₀,₂ ≤ z₂ ≤ 1 − x₀,₂. Hence for θ ∈ [β, L], z·n_θ ≤ z₂ sin θ ≤ 1. For θ ∈ [−L, −β], z·n_θ ≤ −z₂ sin|θ| ≤ x₀,₂ ≤ 1. So x₀ ∈ R. The leftmost point lies in D in the same way. ∎

Canonical wings need not touch either strip line, need not attain h on the core directions, and may have cut slack. GH1 and CS deal with heights and slack. Theorem CA below assumes the regularity it needs.

## 4. One-way transitions under monotone contact

**Lemma CW2.** Let x₀ be a point, I ⊆ [0, L] an interval, and suppose x₀ ∉ Q(t) for t ∈ I. Put u(t) = 1 − Φ_t(x₀) and v(t) = 1 − Φ_{t+L}(x₀). Then u and v are Lipschitz, and almost everywhere on I

$$
u'=v-p,\qquad v'=-u-q .
\tag{CW.1}
$$

1. If p ≤ 0 a.e. on I and u(t₀) ≥ 0, then u ≥ 0 on I ∩ [t₀, ∞).
2. If q ≥ 0 a.e. on I and v(t₁) ≥ 0, then v ≥ 0 on I ∩ (−∞, t₁].

**Proof.** Differentiate u = 1 − h(t) + x₀·n_t and use x₀·n_{t+L} = v − 1 + h(t + L). This gives u' = −h'(t) + x₀·n_{t+L} = v − p. Differentiating v in the same way gives v' = −u − q.

For (1), whenever u < 0 we have v ≥ 0, because x₀ ∉ Q(t); hence u' = v − p ≥ 0 a.e. there. Suppose u(t₂) < 0 for some t₂ > t₀. Let s be the last zero of u in [t₀, t₂]. On (s, t₂] the function u is negative and nondecreasing, so u(t₂) ≥ u(s) = 0, a contradiction.

For (2), whenever v < 0 we have u ≥ 0, so v' = −u − q ≤ 0. Suppose v(t₂) < 0 for some t₂ < t₁. Let s be the first zero of v in [t₂, t₁]. On [t₂, s) the function v is negative and nonincreasing, which contradicts continuity at s. ∎

In words: under (M), a surviving point enters the outgoing arm at most once and leaves the incoming arm at most once.

**Condition (M).** p ≤ 0 a.e. on [β, L] and q ≥ 0 a.e. on [0, b], and the same for p^ρ and q^ρ.

**The candidate satisfies (M).** From the explicit phases of Notes 14 and 18, with R₀ = 2/(3 sin(β/2 + π/8)) and A = 1/(4 sin β):

$$
p_*=\begin{cases}\tfrac12-2A\sin t,&0\le t\le\beta,\\ 1-\tfrac32R_0\sin(\tfrac t2+\tfrac\pi8),&\beta\le t\le b,\\ 1-2A\sin t,&b\le t\le L,\end{cases}
\qquad
q_*=\begin{cases}2A\cos t-1,&0\le t\le\beta,\\ \tfrac32R_0\cos(\tfrac t2+\tfrac\pi8)-1,&\beta\le t\le b,\\ 2A\cos t-\tfrac12,&b\le t\le L.\end{cases}
$$

Each piece is monotone. p_* vanishes at β from both sides and q_* vanishes at b from both sides. Hence p_* ≤ 0 on [β, L] and q_* ≥ 0 on [0, b], each with equality only at that endpoint. The value R₀ coincides with cos β / cos(3(π/4 − β)/2); I checked this to 40 digits. By ρ-symmetry the reflected motion satisfies the same.

**Corollary CW3.** Assume (M) and x₀ ∈ T(K). Then

$$
x_0\in R\iff\Phi_\beta(x_0)\le1\ \text{and}\ \Phi_{-\beta}(x_0)\le1,\qquad
x_0\in D\iff\Phi_{\pi-\beta}(x_0)\le1\ \text{and}\ \Phi_{\pi+\beta}(x_0)\le1 .
$$

**Proof.** The lower constraints of R are u(θ) ≥ 0 for θ ∈ [β, L]. By CW2(1) with I = [β, L] and t₀ = β, they all follow from u(β) ≥ 0. The reflected motion gives u^ρ(t) = 1 − Φ_{−t}(x₀), and the same argument applies. The lower constraints of D are v(s) ≥ 0 for s ∈ [0, b]; by CW2(2) with t₁ = b they follow from v(b) ≥ 0, that is, Φ_{π−β}(x₀) ≤ 1. The reflected case gives Φ_{−π+β} = Φ_{π+β}. ∎

## 5. The core curve has winding one at surviving non-wing points

Let r = h_R and d = h_D. Let z₋, z₊ be the TW.3 curves on [β, b], and let Γ be the CS.4 closed curve:

I_R → z₋(β) → z₋ → z₋(b) → I_D → z₊(b) → z₊ (with t decreasing) → z₊(β) → I_R.

Define the wing quadrants

$$
Q_w(t)=\{\Phi^R_t>1,\ \Phi^D_{t+L}>1\},\qquad Q^\rho_w(t)=\{\Phi^R_{-t}>1,\ \Phi^D_{-t-L}>1\}.
$$

Their apexes are z₋(t) and z₊(t).

The following condition is (Z), **zero cut slack**: w_R(±β) = w_D(±β) = 1. Under (Z), I_R is the intersection of the walls ℓ^R_{±β} = {x·n_{±β} = r(±β) − 1}. Moreover z₋(β) ∈ ℓ^R_β and z₊(β) ∈ ℓ^R_{−β}, and similarly on the left.

The following condition is (V), **outward arms**:

$$
z_-(\beta)-I_R\in(0,\infty)(\sin\beta,-\cos\beta),\qquad z_+(\beta)-I_R\in(0,\infty)(\sin\beta,\cos\beta),
$$
$$
z_-(b)-I_D\in(0,\infty)(-\sin\beta,-\cos\beta),\qquad z_+(b)-I_D\in(0,\infty)(-\sin\beta,\cos\beta).
$$

For the candidate, all four arms have length tan β.

**Lemma CW4.** Assume (Z) and (V). Let x₀ ∉ Γ satisfy three conditions:

- (a) x₀ ∉ Q_w(t) ∪ Q_w^ρ(t) for every t ∈ [β, b];
- (b) Φ^R_β(x₀) > 1 or Φ^R_{−β}(x₀) > 1;
- (c) Φ^D_{π−β}(x₀) > 1 or Φ^D_{π+β}(x₀) > 1.

Then the clockwise winding number of Γ about x₀ is 1.

**Proof.** For t ∈ [β, b] write

$$
x_0-z_-(t)=U\,n_t+V\,n_{t+L},\qquad U=1-\Phi^R_t(x_0),\quad V=1-\Phi^D_{t+L}(x_0).
$$

By (a), the pair (U, V) never lies in the open third quadrant {U < 0, V < 0}. Since x₀ ∉ Γ, it is never the origin. The set of nonzero vectors outside the open third quadrant has angles filling the interval [−π/2, π], so (U, V) has a continuous angle θ(t) with values in [−π/2, π]. A continuous argument of z₋(t) − x₀ is therefore t + π + θ(t).

The reflected computation gives a continuous angle θ^ρ(t) ∈ [−π/2, π], and a continuous argument of z₊(t) − x₀ is π − t − θ^ρ(t). The linear part of ρ reverses angles.

Along the two curves, traversed as in Γ, the argument therefore changes by

$$
2(b-\beta)+\theta(b)-\theta(\beta)+\theta^\rho(b)-\theta^\rho(\beta).
$$

*Right V.* By (Z) and (V), both arms lie on the boundary rays of the closed convex cone I_R + C, where C = {v : v·n_β ≥ 0, v·n_{−β} ≥ 0}. By (b), x₀ is not in this cone. A closed convex set not containing x₀ is strictly separated from it, so the cone is seen from x₀ within an open half-circle of directions. Hence the change of argument along z₊(β) → I_R → z₋(β) lies in (−π, π). It is congruent modulo 2π to a₋ − a₊, where

$$
a_-=\beta+\theta(\beta)-\pi,\qquad a_+=\pi-\beta-\theta^\rho(\beta).
$$

It remains to show a₋ − a₊ ∈ (−π, π). Consider three cases.

- *U(β), U^ρ(β) both negative.* Then V(β) ≥ 0 and V^ρ(β) ≥ 0 by (a). So θ(β) and θ^ρ(β) lie in (π/2, π], and a₋ − a₊ ∈ (2β − π, 2β].
- *U(β) < 0 ≤ U^ρ(β).* Again θ(β) ∈ (π/2, π]. The vector w = I_R − x₀ satisfies w·n_β > 0 and w·n_{−β} ≤ 0, so its argument lies in [L − β, L + β]. By (V), z₊(β) − x₀ is w plus a positive multiple of (sin β, cos β), whose argument is L − β. So the argument of z₊(β) − x₀ also lies in [L − β, L + β]. The representative a₊ ranges over [−β, 3L − β], an interval of length less than 2π that contains [L − β, L + β], so a₊ is that argument. This forces θ^ρ(β) ∈ [L − 2β, L] and a₋ − a₊ ∈ (−π, 2β − L].
- *U^ρ(β) < 0 ≤ U(β).* This is the ρ-image of the previous case.

In every case the change along the right V equals

$$
2\beta-2\pi+\theta(\beta)+\theta^\rho(\beta).
$$

*Left V.* The same argument, mirrored by x ↦ −x and using (c), gives the change −2b − θ(b) − θ^ρ(b).

*Total.* Adding the four contributions gives −2π. The clockwise winding number is therefore 1. ∎

Neither (M) nor regularity is used in CW4. They enter only to place every surviving non-wing point in the hypotheses (b) and (c), and to keep Γ free of negatively wound regions.

## 6. Theorem CA: conditional ordinary-area admission

**Theorem CA.** Let S be a compact connected ambidextrous body with both quarter turns complete in the common incoming normalisation, and let K = conv S. Let R, D be its canonical wings. Assume:

1. condition (M);
2. **core regularity**: r = h on [β, b] ∪ [−b, −β], and d = h on [L + β, π − β] ∪ [π + β, 3L − β];
3. zero cut slack (Z) and outward arms (V);
4. the left apex is strictly left of the right apex: I_D,₁ < I_R,₁.

Then Γ has clockwise winding number in {0, 1} almost everywhere, S ∖ (R ∪ D) ⊆ {w_Γ = 1}, and

$$
\boxed{|S|\le|R|+|D|+\int w_\Gamma=\widehat{\mathcal W}(R,D)} .
$$

Here Ŵ = 𝒲 because the slack is zero.

**Proof.** *Step 1: containment.* Let x₀ ∈ S ∖ (R ∪ D) with x₀ ∉ Γ. Then x₀ ∈ T(K). By CW3 and regularity at the four cut directions, x₀ satisfies (b) and (c) of CW4. By regularity on the core directions, Q_w = Q and Q_w^ρ = Q^ρ on [β, b], so (a) holds. CW4 then gives w_Γ(x₀) = 1.

*Step 2: Γ has no negatively wound region.* By regularity, z₋' = p n_t + q n_{t+L} with p ≤ 0 ≤ q. Its first coordinate p cos t − q sin t is therefore nonpositive, and it vanishes only where p = q = 0, that is, only where z₋' = 0. If two parameters give the same abscissa, the abscissa is constant between them, so z₋' = 0 a.e. there and z₋ is constant there. Hence z₋ is the graph of a continuous function g₋ over [z₋(b)₁, z₋(β)₁], traversed leftward. In the same way z₊ is the graph of g₊, traversed rightward. By (V), z₋(β)₁ and z₊(β)₁ exceed I_R,₁, and z₋(b)₁ and z₊(b)₁ are less than I_D,₁. So both domains contain [I_D,₁, I_R,₁].

Integrating the velocity gives

$$
(z_-(t)-z_-(\beta))\cdot n_\beta=\int_\beta^t\bigl(p\cos(s-\beta)-q\sin(s-\beta)\bigr)ds\le0,
$$

with equality only if z₋(t) = z₋(β). Likewise

$$
(z_-(t)-z_-(b))\cdot n_{\pi-\beta}=\int_t^b\bigl(p\sin(b-s)-q\cos(b-s)\bigr)ds\le0 .
$$

So z₋ lies strictly beyond the walls ℓ^R_β and ℓ^D_{π−β} except at its endpoints. In particular, at each abscissa it lies strictly below these walls. The reflected statements hold for z₊, which lies strictly above ℓ^R_{−β} and ℓ^D_{π+β}.

Next, the cone I_R + C lies in {x₁ ≥ I_R,₁}, because v·n_β + v·n_{−β} = 2v₁ cos β. Similarly the left cone lies in {x₁ ≤ I_D,₁}. By hypothesis 4 the two Vs are disjoint, and R ∩ D = ∅.

A point of S with the largest first coordinate is a support point at θ = 0, so it lies in R by the proof of CW1. Hence x_R ≥ I_R,₁; similarly x_L ≤ I_D,₁. Since S is connected, every vertical line with abscissa in [I_D,₁, I_R,₁] meets S. Such points lie outside both cones, hence outside R ∪ D.

The open vertical ray below the apex z₋(t) lies in Q_w(t) ⊆ Q(t), because (0, −1) = −sin t·n_t − cos t·n_{t+L}. Since S ⊆ T(K), every point of S at abscissa x lies at height at least g₋(x), and similarly at most g₊(x). Hence g₋ ≤ g₊ on [I_D,₁, I_R,₁]. To the right of I_R,₁, g₋ lies below ℓ^R_β, which is below I_R,₂, and g₊ lies above ℓ^R_{−β}, which is above I_R,₂; the left side is the mirror image.

Now count signed crossings of Γ along a vertical line, with leftward pieces contributing +1 and rightward pieces −1:

- *Abscissa in (I_D,₁, I_R,₁).* Γ is crossed only at g₋, contributing +1, and at g₊, contributing −1.
- *Abscissa right of I_R,₁.* The lower pair, g₋ and the lower arm, is present exactly when the abscissa is less than z₋(β)₁. The upper pair, the upper arm and g₊, is present exactly when it is less than z₊(β)₁. When both are present, the crossings occur in the order g₋ < lower arm < upper arm < g₊, with signs +1, −1, +1, −1. A single pair contributes +1 then −1.
- *Abscissa left of I_D,₁.* This is the mirror image.

In every case the partial sums lie in {0, 1}, so w_Γ ∈ {0, 1} almost everywhere.

*Step 3.* By subadditivity and Step 1,

$$
|S|\le|R|+|D|+|S\setminus(R\cup D)|\le|R|+|D|+|\{w_\Gamma=1\}|=|R|+|D|+\int w_\Gamma ,
$$

and the right side is TW.4. ∎

**Corollary CA2 (conditional optimality and uniqueness).** Under the hypotheses of CA, suppose also that the canonical wings satisfy GH.5. Then |S| ≤ M.

Equality holds only for Romik's sofa, up to the normalisation's translations. Indeed, equality gives Ŵ = M, so the wings and core are the reference ones by GH1 and SQ1. Then S is a closed subset of the candidate with full measure, and the candidate's regular closedness (WC3) gives equality.

**Scope.** Romik's candidate satisfies every hypothesis of CA2. (M) is the one that is tight there: p = 0 at β and q = 0 at b. I have not written out stability statements for the other hypotheses under perturbation. **(M) is not proved for unrestricted maximizers.** Section 7 shows that it fails for hulls arbitrarily close to the candidate, so it would have to come from maximality, through first variations of the contact structure, rather than from proximity. CA2 is a second conditional theorem alongside curvature-only CW4. The two have different hypotheses, and Section 7 gives examples where each applies and the other does not.

## 7. The junction obstruction

**Proposition JX1.** Let B be convex with Φ_θ ≤ 1 on B for all θ in some interval [β, β + ε). Then every point of B on the wall ℓ_β = {Φ_β = 1} has the form

$$
(h(\beta)-1)n_\beta+\sigma n_{\beta+L},\qquad \sigma\ge h'(\beta^+).
$$

In particular, if r(β) = h(β) and d(β + L) = h(β + L), so that z₋(β) is the hull corner, then

$$
R\cap\ell_\beta\subseteq z_-(\beta)+[\,p(\beta^+),\infty)\,n_{\beta+L}.
$$

**Proof.** For such a point, Φ_β = 1 and the right derivative of θ ↦ Φ_θ at β equals h'(β⁺) − σ. If σ < h'(β⁺), then Φ_θ > 1 just after β. ∎

**Proposition JX2.** Assume (Z) and core regularity on a right neighbourhood of β, and suppose the right derivative z₋'(β⁺) = p(β⁺) n_β + q(β⁺) n_{β+L} exists with p(β⁺) > 0. Then z₋(β + τ) lies strictly on the R side of ℓ^R_β for all small τ > 0.

Suppose the first return of z₋ to ℓ^R_β lies on the open lower arm (I_R, z₋(β)). Then the arm and the arc z₋([β, t_c]) bound a loop traversed counterclockwise, so Γ has a region of winding −1 and the TW.5/CS.4 hypothesis fails.

This is the generic situation for hulls whose support is C¹-close to the candidate's. The candidate's p_* decreases strictly through 0 at β, so a small positive p(β⁺) turns negative after a time comparable to p(β⁺) itself. The excursion and its return point therefore stay within O(p(β⁺)) of z₋(β), while the lower arm has length close to tan β. This last sentence is a perturbative sketch, not a quantitative theorem. ∎

The loop lies on the wing side of ℓ^R_β but outside R. In the experiments it contains no surviving material, because it lies in the niche. The signed core area then undercounts by exactly the loop area. Separately, surviving points between ℓ^R_β and R's inner envelope above the loop are uncovered, because they lie outside R and have winding 0. These are the "backward" points that CW2 excludes under (M).

**Numerical evidence (floating point, diagnostic only).** The table uses saturated bodies T(conv T(K)), all connected with width greater than 2. The resolution levels are x/t grids of 2000/4000, 4000/8000 and 8000/12000, with wing angle grids of 1441, 2881 and 4001. The quantity p(β) is a one-sided finite difference of the computed wing support. "Neg. loop" is the total area of the faces of Γ with negative winding, computed by polygonising the sampled curve. On the candidate itself the method gives |T| − Ŵ = +2·10⁻⁵ at the coarsest level, which is discretisation error.

| body | p(β) | \|T\| − Ŵ at the three levels | neg. loop at the three levels | M − Ŵ |
|---|---|---|---|---|
| candidate | ≈ 0 | +2·10⁻⁵ (one level) | 0 | 0 |
| compressed, x ↦ 0.95x | +0.039 | 3.7, 5.2, 6.1 ×10⁻⁵ | 6.4, 5.5, 5.5 ×10⁻⁵ | 0.0098 |
| compressed, x ↦ 0.90x | +0.079 | 5.19, 5.50, 5.60 ×10⁻⁴ | 5.48, 5.47, 5.47 ×10⁻⁴ | 0.039 |
| shaved, ε = 0.04 | +0.063 | 7.5, 6.0 ×10⁻⁵ (two levels) | 8.2, 5.2 ×10⁻⁵ | 0.034 |
| shaved, ε = 0.08 | +0.103 | 3.94, 3.38, 3.21 ×10⁻⁴ | 3.90, 3.27, 3.09 ×10⁻⁴ | 0.108 |
| shaved at ±π/4, ±3π/4, ε = 0.02, 0.05, 0.1 | ≈ 0 | +4.6·10⁻⁶, +3.3·10⁻⁶, −2.5·10⁻⁵ | ≤ 6·10⁻⁷ | 0.012, 0.045, 0.118 |
| stretched, x ↦ 1.1x | −0.038 | +2·10⁻⁵ | — | 0.039 |

The compressed hulls have h + h'' ≤ 0.91 on all four open quarters, so curvature-only CW4 applies to them. The hulls shaved at the four junction normals have facets there, so it does not apply. Stretching by 1.15 or more disconnects T, since the two niches overlap. Connectedness is therefore a necessary hypothesis and not decoration.

Per junction, the loop area is about 0.23–0.28 p(β)³ for the compressed hulls and 0.05–0.07 p(β)³ for the shaved ones; the facets change the local curvature. A linearisation gives (2/3) q p³/(κ + q)² with κ = 1 + q − h − h'', which is about 0.20 p³ at the candidate's values. Meanwhile M − Ŵ is quadratic in the perturbation, or of order ε^{3/2} for the shavings. In every test the defect is at least about two orders of magnitude below the calibration margin.

**The shaved Romik hull as a mandatory test.** Let K_ε be the candidate hull cut by the four half-planes {x·n_θ ≤ h_*(θ) − ε} at θ = ±L ± β, and let S_ε be its saturated envelope. Then S_ε is compact, connected, has both quarter turns complete and width about 2.32, and its area is below M by an amount that tends to 0 as ε → 0.

Its hull has facets with normals in all four open quarters. So h + h'' ≤ dθ fails, and curvature-only CW4 does not apply. It also has p(β⁺) > 0 and q(b⁻) < 0, so (M) fails at all four junctions, and the canonical two-wing admission fails on it numerically. Any unrestricted proof must handle this family. It plays the same role as the axis-cut and shadow-clipping families.

## 8. What this changes in the roadmap

- **R4.** GH1 removes the shared-bottom restriction of NH1 for small deficits. What remains is large height deficits, where the free algebra is genuinely negative.
- **R3.** Canonical wings automatically satisfy TW.1 and the strip condition (CW1). Their heights are not controlled in general: for the ε = 0.08 shaving, R occupies only 0.0069 ≤ x₂ ≤ 0.9931, which is still inside GH.5.
- **R5.** For canonical wings, admission is exactly a matter of monotone contact. Under (M) and the other hypotheses of CA it holds, with an explicit proof. Without (M) at a junction it fails, by an amount equal to the loop area in the experiments.

**Three ways forward.**

1. *Derive (M) from maximality.* This would close R5 for canonical wings and, together with GH1 and R2, the problem. The candidate's p = 0 at β is exactly the contact transition of Romik's phases. A maximizer should satisfy a first-order condition that excludes p(β⁺) > 0. That is a statement about the actual contact structure; the variation tools of [Note 57](57-focused-structural-status.md) are the natural input.
2. *Use a loop-corrected functional.* Experimentally |S| ≤ Ŵ + Σ loops, with the loops cubic in p(β⁺). A local theorem would follow from a bound Σ loops ≤ ∫μ(1 − w) + y Σ s + B(δ). For spread-out perturbations the left side is cubic and the right side quadratic. For perturbations concentrated near β, both sides are cubic, because B contains ½∫|δz₋'|² minus a signed area. So the constants matter and a careful estimate is needed. A global version would need a new inequality.
3. *Use a different admission map.* Non-canonical wings, or cut angles adapted to the zero of p, would need their own calibration. As a warning: cutting later than β lets the canonical wing absorb niche material, so the functional is no longer tight at the candidate and its calibration would have to be redone. I have not computed this.

R2 (terminal angles) is untouched by this note.

## 9. Files

- `computer-assisted/check_two_wing_general_height.py` is the exact SymPy checker for GH.1–GH.4 and the WS.11 factorisation, with regressions to NH.8, SQ.9 and WS.10 and three mutation controls.
- `computer-assisted/two-wing-general-height-checks.json` is its executed record: 8 identities passed, 3 mutations rejected, SymPy 1.14.0, Python 3.13.16.
- The floating-point diagnostics used for Section 7 and the GH.5 table are listed with commands in the accompanying README. They are not certificates.
