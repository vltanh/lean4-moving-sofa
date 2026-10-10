# Gate 2 closure: the sharp value for independent partial turns

**October 10, 2026. Gate 2: PASS as a written mathematical proof.** The
argument below proves the universal partial spatial theorem and its
implication for the entire original compact connected motion domain.
The constituent proofs, final reflected-envelope estimate, sign and
boundary coverage, and original-motion deduction received separate
mathematical checks within this research session. External refereeing
and Lean verification remain outstanding.

The proof retains each actual outgoing strip, both signs of the middle
slope, and both independent terminal angles. It uses the completed
[Gate 1 theorem](gate1-sharp-full-turn-closure.md) at the full-turn
boundary and in an explicitly proved negative-tilt completion subcase.
Gate 1's external ordinary one-turn dependency remains part of the chain.
The separate [Gate 3 closure](gate3-sharp-equality-and-uniqueness.md)
now classifies every original equality cap and proves literal
compact-body uniqueness, with its complete manuscript and accepted
dependency review.

## 1. Exact statements

Put

\[
L=\pi/2,\qquad
M=1+4Y^2+\arctan Y,\qquad
4Y^3+3Y-1=0,\quad Y>0.
\tag{G2C.1}
\]

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact downward
convex cap. Write its projection as \(I=[l,r]\), its width as \(W=r-l\),
its roof as \(A\), and its middle half as

\[
J=[l+W/4,r-W/4].
\]

For \(0<t<L\), define

\[
\mu_t=(\cos t,\sin t),\qquad \nu_t=(-\sin t,\cos t),
\]
\[
R_t(x)=\frac{h_U(\mu_t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{h_U(\nu_t)-1+x\sin t}{\cos t}.
\tag{G2C.2}
\]

For \(\pi/4\le\alpha<L\), the actual partial barrier and score are

\[
N_{U,\alpha}(x)=\max\left\{0,
\sup_{0<t<\alpha}\min\{R_t(x),S_t(x)\},\ R_\alpha(x)\right\},
\]
\[
\mathcal P_\alpha(U)=\int_{I\setminus J}A(x)\,dx
-\int_JN_{U,\alpha}(x)\,dx.
\tag{G2C.3}
\]

The terminal term is the whole first inner wall, imposed by the
whole-body outgoing strip. At \(\alpha=L\), use the full positive
two-wall niche of Gate 1. The limiting terminal wall is nonpositive
because the cap has height at most one.

**Theorem G2C1 (universal partial-cap value).** Every cap and every angle
in this domain satisfy

\[
\boxed{\mathcal P_\alpha(U)\le M/2.}
\tag{G2C.4}
\]

The global supremum is \(M/2\), attained by the full-turn reference cap.
The statement includes arbitrary asymmetry, subunit height, nonsmooth
roofs and unbounded polygon complexity. A zero-width cap has score zero.

**Theorem G2C2 (original ambidextrous area).** Every compact connected
body admitting both original unit-corridor passages from a common
incoming orientation, including independent partial terminal rotations
and nonmonotone motions, satisfies

\[
\boxed{|S|\le M.}
\tag{G2C.5}
\]

Romik's reference attains equality, so the unrestricted area supremum
in the original motion domain is exactly \(M\). The same upper bound
holds for Gate 0's signed joint functional on arbitrary auxiliary convex
hulls. The signed integral is not identified with ordinary area when
such a hull has empty survivor fibers.

## 2. A hypothetical failure has an attained canonical maximizer

Suppose G2C.4 fails. The global domain theorem
[PD](gate2-partial-cap-domain-reductions.md) supplies an attained joint
maximum over caps and angles. Choose a maximizing pair with the largest
terminal angle, and apply the score-preserving canonical reductions at
that angle. The selected cap has height one, affine middle roof, and a
top face meeting the middle window. Its unused outer normals are
saturated while every used support and the outgoing wall are preserved.

These reductions apply to both signs of the middle slope. They begin
with arbitrary heights and boundaries, prove width coercivity using an
actual 45-degree tent, and justify continuity of the partial barrier
including its endpoint-angle tails. Thus the finite polygon selection
used for source regularity targets this chosen global maximizer.

If \(\alpha=L\), G1C1 already contradicts the supposed score excess.
For proper angles the all-width certificate
[AT](gate2-all-width-terminal-angle-exclusion.md) gives

\[
\pi/4\le\alpha\le\arctan(8/3)
\quad\Longrightarrow\quad
\mathcal P_\alpha(U)<5259/6400<M/2.
\tag{G2C.6}
\]

It follows that \(\alpha>\arctan(8/3)>3\pi/8\). All three
genuine tents at \(\pi/8,\pi/4,3\pi/8\) have been visited.

The partial source theorem
[PS](gate2-partial-endpoint-source-and-green.md) rederives actual
endpoint complementarity, positive endpoint pressures, regular used-wing
curvature bounds, source balance and the Green identity for this
objective. It retains the possible first terminal facet atom and excludes
the companion terminal atom. It does not import the source law of a
different full-turn maximizer.

The finite three-angle comparisons transferred in
[TP](gate2-terminal-facet-and-prefix-reduction.md) give the short-width,
initial wide-width and tilt cuts. The new
[WC](gate2-three-angle-width-cut.md) uses the partial endpoint pressures
and a joint bound on the two positive-floor losses to sharpen the width
cut without a full-niche endpoint-box assumption. Hence, with
\(I=[-2C,2C]\) and \(J=[-C,C]\),

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
0\le |A(C)-A(-C)|<\frac{17}{50}.
\tag{G2C.7}
\]

Horizontal reflection is used only to compare this symmetric set of
three tents, with the barrier reflected at the same time. It is not
asserted to preserve the fixed partial objective.

## 3. The actual terminal facet and its source mass

Keep the original orientation and put

\[
A(-C)=1-h_L,\qquad A(C)=1-h_R,\qquad
h_L,h_R\ge0,\quad \min(h_L,h_R)=0,
\]
\[
c=\cos\alpha,\qquad s=\sin\alpha.
\]

If \(h_R>0\), the negative-tilt theorem
[NT](gate2-negative-tilt-completion.md) already proves
\(N_{U,\alpha}\ge n_U\) on \(J\), and hence
\(\mathcal P_\alpha(U)\le\mathcal P_L(U)\le M/2\), unless

\[
0<h_R<1-s,\qquad
\alpha<L-\arctan(h_R/(2C)).
\tag{G2C.8}
\]

Discard the completed branch. In every remaining sign, put

\[
H=1-h_R>s,\qquad
d=\frac{1-Hs}{c},\qquad w=c-d>0.
\tag{G2C.9}
\]

Let \(T_L,T_R\) be the height-one top overhangs outside the left and
right ends of \(J\). They are zero on a strictly lower middle side.
The canonical first support immediately after the terminal angle is
the point \((C+T_R,H)\); in the negative case it remains so until the
unvisited central normal. The first terminal facet has charged horizontal
length \(m\), and the whole outgoing wall is

\[
R_\alpha(-C+z)=\frac cs(2C+T_R-d-z).
\tag{G2C.10}
\]

Using the correct one-sided angle derivative with historical ties from
[TV](gate2-terminal-angle-variations.md), TP proves

\[
\boxed{m\le w<\frac c2,\qquad T_L+2T_R\le d.}
\tag{G2C.11}
\]

The first inequality uses the largest-angle choice: a longer facet would
make the outgoing wall redundant and permit a small angle increase
without changing the barrier. The second comes from the finite-source
horizontal projection, passed on compact positive-barrier intervals.
It does not assume continuity of the length of a zero set.

PS additionally gives a terminal occupation \(\chi\) with
\(0\le\chi\le1\), total horizontal mass \(\int_J\chi=m\), and
\(\chi=1\) on the strict exposure set

\[
E=\{x\in J:R_\alpha(x)>n_\alpha(x)\},\qquad
n_\alpha=\max\{0,\sup_{0<t<\alpha}\min(R_t,S_t)\}.
\tag{G2C.12}
\]

Only this strict-exposure statement is needed below. No common
fractional occupation for separate shape and angle variations is used.

## 4. A weighted companion moment gives the contradiction

Let \(g\) be the support of the left charged wing and \(v=g''+g\)
its regular curvature. For positive tilt use the low-left surrogate:
the omitted high-point companion wall is nonpositive on \(J\).
In the other two signs use the actual companion support. Then

\[
g(0)=1-h_L,\qquad g'(0+)=C+T_L.
\]

Put

\[
\theta=\arcsin(C-T_L),\qquad \lambda=\tan\theta,
\]
\[
\mathcal E_\theta
=\int_0^\theta(v(t)-1)_+
\bigl(\lambda\cos t-\sin t\bigr)\,dt.
\tag{G2C.13}
\]

The quantity \(C-T_L\) is positive by G2C.7, G2C.9 and G2C.11.
The exact weighted moment theorem
[MP](gate2-companion-moment-prefix-exclusion.md) proves, throughout
\(0\le z\le w\),

\[
n_\alpha(-C+z)
\le\sqrt{1-(C-T_L)^2}-\sqrt{1-(C+z)^2}
+\mathcal E_\theta.
\tag{G2C.14}
\]

To explain the localization, a positive global companion-wall maximum
has an interior maximizing angle and shifted support abscissa
\(D_x=-C+z\). The outer support point has \(X\ge-2C\), so
\(\sin t\le C+z\). The derivative relations
\(D_x'=(1-v)\cos t\), \(D_y'=(1-v)\sin t\) then yield
G2C.14 by weighting horizontal displacement with \(\lambda\).
The weight changes sign at \(\theta\); curvature above one after
that angle contributes no adverse error.

MP's exact scalar comparison, retaining all top overhangs and the lower
negative-tilt terminal height, gives the strict uniform margin

\[
R_\alpha(-C+z)
-\left[\sqrt{1-(C-T_L)^2}-\sqrt{1-(C+z)^2}\right]
>\frac{39}{4400}c
\quad(0\le z\le w).
\tag{G2C.15}
\]

This follows from two concave-in-width comparisons of symmetric
integral averages of \(x/\sqrt{1-x^2}\), with exact rational endpoint
certificates covering \(c\le1/3\) and \(c\ge1/3\). It is not an
angular discretization of the niche.

Consequently it suffices to prove

\[
\mathcal E_\theta\le\frac{39}{4400}c.
\tag{G2C.16}
\]

If G2C.16 holds, the entire interval \([-C,-C+w]\) is strictly
exposed to the outgoing wall. Continuity extends strict exposure a
positive distance beyond its interior right endpoint. Thus
\(|E|>w\ge m\), contradicting G2C.12. The remaining task is the
weighted error estimate, with no full-wing unit-curvature assumption.

## 5. The two overlapping angle ranges pay the weighted error

Write \(\kappa=\cot\alpha\). We have \(0<\kappa<3/8\).
Reflect the support equations only, by \(r=L-t\), and set
\(P=-q\), \(Q=-p\), \(U=v\), \(V=u\). On regular used intervals
where the surrogate agrees with the actual relevant supports, the local
equations and source laws give

\[
P'=U-1-Q,\qquad Q'=V-1+P,
\]
\[
P\le1,\quad Q\ge-1,\quad
U\le\max\{|Q|,(1+|Q|)/2\},
\quad V\le\max\{|P|,(1+|P|)/2\}.
\tag{G2C.17}
\]

The final removed positive-central interval has \(U=V=0\) directly;
no surrogate arm inequality is claimed or needed on that interval.

On the initial positive \(P,Q\) component, \(U=0,V\le1/2\).
Every later positive-\(Q\) component has amplitude at most \(1/8\).
The harmonic unused gap has zero regular curvature. The first terminal
facet becomes a single upward impulse in \(Q\), of size
\(j=m/s\le\delta=c/(1+s)\). The unused negative central atom is
removed by the right-wing surrogate; no used support changes. The
initial reflected state is

\[
(P,Q)=(e,d_0-1),\qquad
\begin{cases}
e=e_L,\ d_0=3C+T_R,&\text{positive or horizontal},\\
e=e_L+h_R,\ d_0=3C,&\text{negative}.
\end{cases}
\tag{G2C.18}
\]

For the energy \(\mathcal H=(P-1/2)^2+(Q+1)^2\), the exact
unused-gap and terminal-impulse calculation is

\[
\mathcal H((L-\alpha)+)-\mathcal H(0)
\le\delta^2\left[
\frac{2e-1+\delta^2}{1+\delta^2}-d_0c\right].
\tag{G2C.19}
\]

### The range \(0<\kappa\le1/8\)

The [reflected-tail theorem RX](gate2-reflected-tail-cot-one-eighth.md)
uses the valid small-deficit endpoint box, the two parameter pairs in
G2C.18, and G2C.19. It proves that every possible reflected first-density
excess has ended before \(18/25\). Since
\(\cos(18/25)>37/50>C\), this yields

\[
v(t)\le1\quad\text{for a.e. }0<t<\arcsin C.
\tag{G2C.20}
\]

It bounds the shorter interval ending at \(\theta\), so
\(\mathcal E_\theta=0\), proving G2C.16 on this whole range.

### The range \(1/8\le\kappa<3/8\)

The [all-angle reflected-envelope theorem AC](gate2-all-angle-reflected-cubic-exclusion.md)
uses the actual outgoing-wall value in the endpoint pressures. It gives
\(e<179/200,d_0<2311/1000\) for positive or horizontal middle, and
\(e<1,d_0<111/50\) for negative middle. The impulse cost in
G2C.19 is below \(1/30\).

After the first \(P\)-zero, the source equations give the quadratic
decay \(Q-1\le\varepsilon_0-\rho/2-\rho^2/4\). A coupled
time-and-amplitude bound is monotone in the two initial parameters;
its exact endpoint certificates place every possible excess before
\(91/100\). The resulting uniform linear envelope is

\[
(U(r)-1)_+\le\frac{19}{25}(91/100-r)_+.
\tag{G2C.21}
\]

The proof includes a first zero before the terminal impulse, the
impulse itself, both tail heights, and all later source components.

Under \(t=L-r\), put \(t_0=L-91/100\). Since
\(\cos\theta>2/3\) and
\(\arccos(C-T_L)>147/200\), the potentially relevant excess
interval has length less than \(7/40\). The exact weight is
\(\lambda\cos t-\sin t=\sin(\theta-t)/\cos\theta\). Thus
G2C.21 yields the cubic payment

\[
\mathcal E_\theta
<\frac{19/25}{6(2/3)}\left(\frac7{40}\right)^3
=\frac{6517}{6400000}
<\frac{117}{110000}
<\frac{39}{4400}c.
\tag{G2C.22}
\]

The final inequality uses \(c\ge1/\sqrt{65}>3/25\). The strict
rational gap between the middle two fractions is
\(3193/70400000\). This proves G2C.16 on the second range.

The two ranges overlap at \(\kappa=1/8\). Together they contradict
every proper-angle maximizing pair left by Sections 2--3. The
full-turn boundary was already bounded by G1C1. Hence no cap in the
original scalar domain has score above \(M/2\), proving G2C1.

## 6. Deduction for both independent original motions

The [Gate 0 original-motion audit](original-motion-global-bridge-gate0-audit.md)
applies to every actual compact connected competitor of area above
\(\sqrt2\). It supplies independent terminal magnitudes
\(\alpha,\gamma\in[\pi/4,L]\) while retaining both actual outgoing
strips. Its reduction uses the angles visited by the original continuous
motions, so it also covers backtracking and nonmonotone rotations.

Let \(K\) be the actual convex hull in its incoming strip. Its upper
downward cap \(U\) and vertically reflected lower downward cap \(V\)
share the same horizontal projection \(I\) and middle half \(J\).
Gate 0's exact signed fiber is

\[
\ell(x)=1-\max\{1-A_V(x),N_{U,\alpha}(x)\}
-\max\{1-A_U(x),N_{V,\gamma}(x)\}.
\tag{G2C.23}
\]

On the middle half, \(\ell\le1-N_{U,\alpha}-N_{V,\gamma}\).
On its complement, \(\ell\le A_U+A_V-1\). The constants cancel
because both regions have length \(W/2\). Therefore, for every
auxiliary hull as well as the actual one,

\[
\int_I\ell\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V)\le M.
\tag{G2C.24}
\]

For an actual connected body, every projected fiber of the canonical
envelope is nonempty and contains the body fiber. Gate 0 consequently
gives \(|S|\le\int_I\ell\). For an auxiliary hull, G2C.24 is
still a bound on the signed integral, without dropping its possible
negative fibers or replacing it by its positive part.

Bodies of area at most \(\sqrt2\) are already below \(M\), since
G1C.6 gives \(M>41/25>\sqrt2\). This proves G2C2 on the entire
original domain. Romik's genuine two-full-turn body is also admissible
in that domain and has exact area G2C.1. Its reference caps attain
equality in the spatial partition, as recorded in
[the reference calculation](spatial-half-partition-bound.md). The
unrestricted supremum is therefore exactly \(M\).

## 7. Scope and verification

The [dependency and coverage audit](gate2-dependency-coverage-audit.md)
records every angle boundary, middle-slope sign, source convention and
original-motion implication. The
[fixed exact arithmetic checker](computer-assisted/check_gate2_final_exact.py)
passes 83 rational and squared comparisons used in the final scalar and
reflected-envelope arguments. It does not verify the continuum geometry
or replace the written source proofs.

The mathematical dependency on Gate 1 includes Baek's ordinary one-turn
theorem and the existing Gerver area enclosure, documented in G1C
Section 6. Gate 2 adds no application of that ordinary area theorem to
an unproved partial survivor. All new arguments are in the research
documentation tree. External refereeing and Lean verification remain
separate from the written-proof acceptance condition. No equality
classification or uniqueness result is asserted here.
