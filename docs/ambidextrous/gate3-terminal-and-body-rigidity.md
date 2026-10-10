# Gate 3: terminal-angle rigidity and recovery of the actual body

Written mathematical proof, October 10, 2026. This note separates three
equality questions: the terminal angle in the scalar partial-cap
functional, the possible outgoing strips of the reference actual hull,
and exact recovery of a compact maximizing body. The main new argument
replaces Gate 2's largest-angle selection by a fixed-cap contradiction:
an equality-preserving angle extension would turn a positive terminal
facet into a forbidden interior charged atom.

The sharp value theorem is [G2C](gate2-sharp-partial-turn-closure.md).
The full-turn equality inputs are CE1, CE3 and CE4 in
[the full-turn cap equality note](gate3-full-turn-cap-equality.md).
The other inputs are the actual partial-cap domain and source theorems
[PD](gate2-partial-cap-domain-reductions.md),
[PS](gate2-partial-endpoint-source-and-green.md), the one-sided angle
law [TV](gate2-terminal-angle-variations.md), and the terminal geometry
[TP](gate2-terminal-facet-and-prefix-reduction.md). All statements are
written mathematics; this note makes no Lean verification claim.

Labels TB are local. Put \(L=\pi/2\). A *joint maximizer* below means a
maximizer of the actual partial-cap functional over both cap and angle.
By G2C its value is exactly \(M/2\). It need not have the largest angle
among such maximizers.

## 1. The equality-selection issue

G2C proves the upper bound by assuming a value greater than \(M/2\),
selecting a joint maximizer with the largest terminal angle, and
contradicting that selection. This alone does not prove that an
individual equality cap has terminal angle \(L\): the global equality
set already contains the full-turn reference, so its largest angle is
\(L\) regardless of whether another equality cap has a proper angle.

The only use of that selection in the quantitative terminal argument
is TP.10's final step. TP first proves that a terminal facet with
\(m>w_H\) allows a small angle increase with the *same cap* and
unchanged barrier. The largest-angle choice then supplies its stated
contradiction. The next section gives a different contradiction at the
same point, valid for every proper-angle joint maximizer.

PS explicitly states that its fixed-angle identities and regularity
hold without a largest-angle choice. Its first theorem concerns the
actual charged outer measure of the prescribed maximizing cap: it has
bounded density on the visited open arcs, with a possible atom only at
the first terminal normal. This stronger quantifier is essential here.

## 2. A short terminal facet at every proper-angle maximizer

Let \((U,a)\) be any height-one, affine-middle joint maximizer with
\(a<L\), in PD's used-support normal form. The strict numerical cuts
AT, TP Section 1 and WC apply at value \(M/2\): each excluded range has
an explicit upper bound strictly smaller than \(M/2\). Thus

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
\frac{1001}{2000}<C<\frac{37}{50},\qquad
a>\arctan(8/3).
\tag{TB.1}
\]

Write the middle heights as
\(A(-C)=1-h_L\), \(A(C)=1-h_R\), with
\(h_L,h_R\ge0\), \(\min(h_L,h_R)=0\), and
\(h_L+h_R<17/50\) by TP Section 1. If the middle tilt
is negative, temporarily restrict to the residual case of
[NT](gate2-negative-tilt-completion.md):

\[
0<h_R<1-\sin a,\qquad
a<\theta_0=L-\arctan(h_R/(2C)).
\tag{TB.2}
\]

The other negative cases will be handled in Section 3. Put

\[
c=\cos a,\qquad s=\sin a,\qquad H=1-h_R,\qquad
b=C+T_R,\qquad d=\frac{1-Hs}{c},\qquad w=c-d.
\tag{TB.3}
\]

Then \(s<H\le1\), \(0<d<c<C\), and \(0<w<c/2\). The
actual first terminal facet has endpoints

\[
(b,H),\qquad (b+m,H-mc/s),\qquad m\ge0,
\tag{TB.4}
\]

and its shifted endpoints and outgoing zero are

\[
B_+=(b-c,H-s),\qquad B_-=B_++(m,-mc/s),\qquad r_0=b-d.
\tag{TB.5}
\]

The facet is on the charged right wing: \(b\ge C\), and if
\(m>0\), its open segment has \(x>C\) and arclength \(m/s>0\).
Its supporting normal is \((\cos a,\sin a)\).

The source horizontal-moment proof of TP.11 does not use a largest
angle or the terminal-facet bound. It gives

\[
T_L+2T_R\le d,\qquad T_R<d.
\tag{TB.6}
\]

In particular
\(0<(B_+)_x<r_0<C\). The same terminal-corner estimate as
TP.9 gives

\[
(z_a)_x<(B_+)_x.
\tag{TB.7}
\]

**Lemma TB1 (the terminal mass bound needs no extremal-angle
selection).** Under TB.1--7,

\[
\boxed{m\le w.}
\tag{TB.8}
\]

**Proof.** Suppose \(m>w\). Then
\((B_-)_x>r_0\). If
\((z_a)_x<x<(B_-)_x\), the terminal companion wall is greater
than the first wall, while the first wall has strictly negative left
angle derivative:

\[
S_a(x)>R_a(x),\qquad
\partial_-R_a(x)=\frac{x-(B_-)_x}{s^2}<0.
\tag{TB.9}
\]

The first identity is the two-wall intersection criterion; the second
uses the lower/right endpoint of the terminal support facet. The
companion support has no terminal atom by PS. Therefore sufficiently
close earlier angles have both walls strictly above \(R_a(x)\), so

\[
n_a(x)>R_a(x)
\quad\text{for }(z_a)_x<x<(B_-)_x.
\tag{TB.10}
\]

Here \(n_a\) includes the positive floor. For \(x\ge(B_-)_x\),
the outgoing wall is negative since \((B_-)_x>r_0\). Thus every
strict terminal exposure, and every relevant terminal tie, lies at
\(x\le(z_a)_x<(B_+)_x\). The right angle-variation inequality TV.3
is valid at every joint maximizer. Its nonnegative tie term vanishes
on this region, while its strict-exposure integrand is bounded above
by the strictly negative constant \((z_a)_x-(B_+)_x\). It follows
that the strict exposure set has measure zero. Continuity gives

\[
n_a\ge R_a\quad\text{on }J,\qquad N_a=n_a.
\tag{TB.11}
\]

We record explicitly that the ensuing angle extension keeps \(U\)
fixed. Choose

\[
\max\{-C,(z_a)_x\}<\zeta<(B_+)_x<r_0
<r_*<\min\{C,(B_-)_x\}.
\tag{TB.12}
\]

These choices are possible by TB.5--7 and \(m>w\). Immediately
after \(a\), the first support of this same cap is the fixed point
\((b,H)\). For negative tilt choose all angle increments below
\(\theta_0-a\); for the other two signs this harmonic tail runs to
\(L\). Its attached first walls have

\[
\partial_t R_t(x)=\frac{x-(b-\cos t)}{\sin^2t}.
\]

For \(x\le\zeta\) and \(t\ge a\) close to \(a\), this is
negative, so \(R_t(x)\le R_a(x)\le n_a(x)\). On the compact
interval \([\zeta,r_*]\), TB.10 gives a uniform strictly positive
gap \(n_a-R_a\). Uniform convergence of \(R_t\) to \(R_a\)
pays every new first wall there. Finally the positive zero of the new
first wall,

\[
r_0(t)=b-\frac{1-H\sin t}{\cos t},
\]

is continuous at \(a\), so it remains below \(r_*\) for a
sufficiently small increment. The new first walls are nonpositive for
\(x\ge r_*\). Consequently, for some \(\beta\in(a,L)\),

\[
R_t\le n_a\quad\text{on }J\quad(a\le t\le\beta).
\tag{TB.13}
\]

Every newly visited two-wall minimum is at most its first wall; the
new outgoing wall is also covered by TB.13. All old visited minima
remain in the new history. Therefore, pointwise on \(J\),

\[
N_{U,\beta}=N_{U,a},\qquad
\mathcal P_\beta(U)=\mathcal P_a(U)=M/2.
\tag{TB.14}
\]

The cap, height, projection, affine middle, and both charged wings have
not changed. Its used-support normal form is preserved as well: if
\(\ell\) is the same middle chord, the newly added support constraints
are valid for \(U\), so
\(U\subseteq\operatorname{Sat}_{\beta}(U)\cap\{y\le\ell\}
\subseteq\operatorname{Sat}_{a}(U)\cap\{y\le\ell\}=U\).
In particular the positive facet in TB.4 is still outside
the same middle window \(J\), still has arclength \(m/s>0\), and
still has normal \(a\). But now \(a\in(0,\beta)\): it is an
interior visited first normal for the joint maximizer \((U,\beta)\).
PS applies to this prescribed cap at its new fixed angle and forbids
any charged atom there. In the residual negative case
\(a<\beta<\theta_0\), so this is not the uncharged middle normal;
positive and horizontal middles likewise have no middle normal at
\(a<L\). This contradicts the unchanged positive charged facet.
Hence \(m\le w\). \(\square\)

No repeated continuation, limiting reachable set, new cap or change of
horizontal window occurs in this proof. The contradiction is already
available after one fixed-cap angle increment.

## 3. Every scalar equality cap has a full terminal angle

**Theorem TB2 (strict proper-angle cap inequality).** For every
downward compact convex cap \(U\) of height at most one,

\[
\boxed{\pi/4\le a<L
\quad\Longrightarrow\quad\mathcal P_a(U)<M/2.}
\tag{TB.15}
\]

**Proof.** G2C gives the non-strict upper bound. Suppose equality
holds at a proper angle. The height and middle-chord reductions of
PD do not decrease the score and keep the angle fixed. By the already
proved universal bound they therefore give a height-one affine-middle
joint maximizer at that same proper angle. PD4 and PD5 give its top
localization and used-support normal form. The cuts in TB.1 apply.

First suppose the canonical middle is negative and belongs to an
NT-completed branch: either \(a\ge\theta_0\) or
\(h_R\ge1-\sin a\). NT gives

\[
M/2=\mathcal P_a(U)\le\mathcal P_L(U)\le M/2.
\tag{TB.16}
\]

CE1 (or the stronger CE3) identifies this canonical full-turn equality
cap with the reference cap. That already contradicts a negative
middle slope. There is also a direct incompatibility with the partial unused-source
condition, as can be seen directly from its final circular phase.
In centered reference coordinates let

\[
\beta_* =\arctan Y,\qquad
m_* =\frac1{3\sin\beta_*},\qquad C_* =m_*/2.
\]

By CE4, for \(L-\beta_*<t<L\), its first support is

\[
f_*(t)=\frac12+C_*\cos t+\frac12\sin t,
\qquad f_*''+f_*=\frac12.
\tag{TB.17}
\]

The actual support point on this phase is

\[
\left(C_*+\tfrac12\cos t,\ \tfrac12+\tfrac12\sin t\right).
\tag{TB.18}
\]

Its abscissa is strictly greater than \(C_*\), so this is charged
right-wing curvature. The nonempty interval
\((\max\{a,L-\beta_*\},L)\) lies in the unused first arc of the
proper partial maximizer and has curvature density \(1/2\), contrary
to PD5 or PS1. Thus no NT-completed equality case exists.

All other cases are positive, horizontal or residual negative middle.
Lemma TB1 supplies \(m\le w_H\) without a largest-angle selection,
and TB.6 supplies the top projection bound. The remainder of Gate 2's
quantitative argument is now applicable to this individual maximizer.
For precision, its uses of an above-reference assumption were only to
ensure global maximality and the strict fixed numerical cuts; value
\(M/2>41/50\) already supplies those same hypotheses. The subsequent
estimates themselves use the displayed geometry and local source laws.

For \(0<\cot a\le1/8\),
[RX](gate2-reflected-tail-cot-one-eighth.md) gives \(v\le1\) through
\(\arcsin C\). For \(1/8\le\cot a<3/8\),
[AC](gate2-all-angle-reflected-cubic-exclusion.md) gives the weighted
early-excess bound. The [MP comparison](gate2-companion-moment-prefix-exclusion.md)
then gives a strict terminal exposure interval longer than \(w_H\),
contradicting the separate fixed-angle PS occupation identity with
total occupation \(m\le w_H\). This exhausts the angle and tilt
cases and proves TB.15. \(\square\)

The theorem concerns the original individual cap and angle. The
canonical replacements are only used inside a contradiction and keep
that angle fixed. It does not assert that an original equality cap is
identified merely by choosing some other full-turn maximizer.

## 4. An independent global strip obstruction for the reference hull

The following elementary fact is stronger than a local terminal-angle
area penalty when the hull is the *actual hull* of the body.

**Lemma TB3 (only the horizontal unit-strip direction fits the reference
hull).** In its centered normalization the reference hull \(K_*\)
has width one in the vertical normal direction. Its width in every
other normal direction is strictly greater than one.

**Proof.** Its top and bottom faces both contain
\([-m_*/2,m_*/2]\), so

\[
[-m_*/2,m_*/2]\times[0,1]\subset K_*.
\tag{TB.19}
\]

The root equation \(4Y^3+3Y=1\), \(Y>0\), gives \(Y<1/3\)
and therefore \(\sin\beta_*<1/3\); hence \(m_*>1\).
For a unit normal \(n=(c,s)\), support width is at least the
width of the contained rectangle:

\[
\operatorname{width}_{K_*}(n)\ge m_*|c|+|s|.
\tag{TB.20}
\]

If \(c\ne0\), this is greater than \(|c|+|s|\ge1\).
For \(c=0\), the hull's vertical span is exactly one. This proves
the assertion. \(\square\)

Since convex hulls preserve support widths, every body whose actual
hull is \(K_*\) has the same obstruction. In particular a
correct-handed outgoing unit strip at a conventional angle
\(0\le a<L\) is impossible:

\[
\operatorname{width}_{K_*}(u_a)
\ge m_*\cos a+\sin a>1.
\tag{TB.21}
\]

This is a statement about the whole outgoing strip, independent of
which interior corners were visited. It also identifies the possible
incoming unit-strip normal of the reference body, up to sign.

There is no conflict with the partial auxiliary envelopes in
[the outgoing-strip area note](romik-terminal-angle-outgoing-strip-rigidity.md).
An envelope cut from an auxiliary \(K_*\) may discard its extremal
face points and have a smaller actual hull. Lemma TB3 asserts the
obstruction when \(K_*\) remains the body's actual convex hull;
the older EP estimates instead bound the area lost by those cuts.

## 5. From equality caps to the actual compact body

Consider a compact connected admissible body \(S\) with \(|S|=M\).
Use the common-pose normalization and the *actual-hull* construction
of [Gate 0](original-motion-global-bridge-gate0-audit.md). It supplies
\(K=\operatorname{conv}S\subset\mathbb R\times[0,1]\), its
upper and reflected-lower downward caps \(U,V\), a common projection
\(I\), and independent conventional terminal angles
\(a,b\in[\pi/4,L]\). The actual body is contained in its canonical
envelope, and every envelope fiber is nonempty by connectedness of
\(S\). The sharp chain is

\[
M=|S|\le |E_{a,b}(K)|
\le\mathcal P_a(U)+\mathcal P_b(V)\le M.
\tag{TB.22}
\]

The second inequality is PD.4's spatial partition, with the signed
integral equal to ordinary area on this actual hull. Both scalar
deficits are nonnegative, so equality forces

\[
\mathcal P_a(U)=\mathcal P_b(V)=M/2.
\tag{TB.23}
\]

Equivalently, ED1 in the
[equality dependency audit](gate3-equality-dependency-audit.md)
expresses \(M-|S|\) as the sum of the two original scalar deficits,
the nonnegative spatial-partition defect, and the nonnegative filling
defect \(|E_{a,b}(K)\setminus S|\). Thus TB.23 retains the original
caps, rather than only their canonical replacements.

Theorem TB2 gives \(a=b=L\). CE3 now recovers each *original*
full-turn equality cap as a horizontal translate of the reference
cap, with height one. The two caps have the same projection \(I\),
so their horizontal translations agree. Their roofs recover the actual
hull by

\[
A_K=A_U,\qquad B_K=1-A_V.
\tag{TB.24}
\]

Thus the normalized actual hull is the corresponding translate of
\(K_*\). The exact support-tightened full-turn envelope is then the
same translate of the reference sofa \(\Sigma_*\), by the
[direct reference construction](gate3-manuscript-introduction.md), Section 3.
The containment from Gate 0 was for the original \(S\), so

\[
S\subseteq\Sigma_*,\qquad |S|=|\Sigma_*|.
\tag{TB.25}
\]

No cap replacement is substituted for the original body in TB.25.
The reversal of height extrusion and middle canonicalization occurs
inside CE3, before the original hull is identified.

**Lemma TB4 (regular-closed recovery).** If \(F\) is compact and
regular closed, \(S\subseteq F\) is closed, and
\(|S|=|F|\), then \(S=F\).

**Proof.** If \(p\in F\setminus S\), closedness of \(S\) gives
an open ball about \(p\) disjoint from \(S\). Since
\(F=\overline{\operatorname{int}F}\), that ball contains an
interior point of \(F\) and hence a smaller ball in
\(F\setminus S\). This has positive area, contradicting the area
equality. \(\square\)

The same direct construction proves that \(\Sigma_*\) is regular closed. Its central
survivor fibers are bounded by continuous strictly separated graphs;
outside the middle interval they are the unchanged convex-hull fibers.
At the horizontal extremes the convex flanks are limits of interior
points. Therefore every point of \(\Sigma_*\) is a limit of its
interior points, including face endpoints and extreme tips.

Applying TB4 to TB.25 and undoing the common rigid normalization gives
the exact body statement:

\[
\boxed{|S|=M\quad\Longrightarrow\quad
S\text{ is congruent to }\Sigma_*.}
\tag{TB.26}
\]

The converse is the already verified feasibility and exact area of
the reference. Lemma TB3 supplies an independent check that the
identified actual body cannot end a conventional turn at a proper
angle. The conclusion concerns the body and the extracted conventional
terminal angles; it does not claim that its arbitrary physical motion
witnesses have unique parameterizations or histories.

## 6. What happens to measure-zero changes

Area equality by itself does not imply equality of compact connected
sets: a disk together with an attached line segment has the disk's
area. That generic example is not a feasible equality counterexample
to TB.26. The proof uses two additional facts about the actual body.

First, an appendage outside the recovered reference hull would change
one of the original equality caps, contrary to CE3 and TB.24. An
appendage inside that hull but outside \(\Sigma_*\) would violate
the actual canonical envelope containment. Hence no new zero-area
appendage is left unexamined by the support argument.

Second, a proper closed subset of the regular-closed reference cannot
have its full area, by TB4. Thus no compact zero-area deletion is
possible either. The regular-closed hypothesis belongs to the larger
identified envelope; no regularity assumption on arbitrary competing
bodies has been introduced.

Compactness matters for literal set uniqueness. If it were dropped,
removing one upper boundary point of \(\Sigma_*\) would leave a
nonclosed set with the same area and the same feasible motions. Choose
the removed point away from the horizontal midline. Every remaining
point can still be joined vertically to that midline, and then along
the midline, so the resulting set remains connected. This is a genuine
counterexample to literal uniqueness in a broader class of nonclosed
connected measurable bodies; it lies outside the stated compact-body
domain.

Motion witnesses are also nonunique even for the same exact body:
time reparameterization, waiting, or additional translations while
fully inside a straight arm preserve feasibility. No equality claim
here identifies those choices.
