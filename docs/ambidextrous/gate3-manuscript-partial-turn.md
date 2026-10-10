# Partial turns and strict terminal-angle rigidity

Put \(L=\pi/2\), and let

\[
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y=1,\qquad Y>0.
\tag{PT.1}
\]

This chapter gives the partial-turn part of the area and rigidity
theorem. The universal value theorem
[G2C1](gate2-sharp-partial-turn-closure.md) establishes that the joint
maximum of the cap functional below is \(M/2\), attained by the
full-turn reference. We use this established maximum before analyzing
equality. In particular, an arbitrary cap attaining \(M/2\) is a
joint maximizer; none of the following equality arguments replaces its
angle by the largest angle of some other maximizer.

The full-turn equality input is
[CE1--CE3](gate3-full-turn-cap-equality.md): a full-turn equality cap
is a horizontal translate of the centered reference cap, whose middle
roof is horizontal. All longer source, finite-angle and reflected
estimates used here have complete proofs in the linked notes.

## 1. The actual outgoing-wall functional

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact downward
convex cap, with projection \(I=[l,r]\), roof \(A\), width
\(W=r-l\), and middle half
\(J=[l+W/4,r-W/4]\). For \(0<t<L\), set

\[
\mu_t=(\cos t,\sin t),\quad \nu_t=(-\sin t,\cos t),\qquad
f(t)=h_U(\mu_t),\quad g(t)=h_U(\nu_t),
\]
\[
R_t(x)=\frac{f(t)-1-x\cos t}{\sin t},\qquad
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}.
\tag{PT.2}
\]

For \(\pi/4\le a<L\), define the visited niche, actual barrier,
and score by

\[
n_a(x)=\max\{0,\sup_{0<t<a}\min(R_t(x),S_t(x))\},
\quad N_a(x)=\max\{n_a(x),R_a(x)\},
\]
\[
\mathcal P_a(U)=\int_{I\setminus J}A(x)\,dx-
\int_JN_a(x)\,dx.
\tag{PT.3}
\]

The term \(R_a\) is the whole first inner wall imposed by the
outgoing strip. It is not replaced by the terminal two-wall minimum.
At \(a=L\), use the full positive niche: the limiting outgoing
wall is nonpositive because the cap has height at most one. A
zero-width cap has score zero.

**Partial-cap theorem.** Every cap in this domain satisfies

\[
\mathcal P_a(U)\le M/2\quad(\pi/4\le a\le L),
\qquad
\mathcal P_a(U)<M/2\quad(\pi/4\le a<L).
\tag{PT.4}
\]

The non-strict statement is G2C1. We prove its strict refinement by
excluding every proper-angle equality cap. The same quantitative
estimates constitute the proper-angle contradiction in the value
theorem; their use at equality requires the fixed-cap argument in
Section 4.

## 2. Canonical reduction and prescribed-cap source laws

Suppose \(\mathcal P_a(U)=M/2\) with \(a<L\). The domain
theorems [PD1--PD5](gate2-partial-cap-domain-reductions.md) permit
vertical extrusion to height one, cutting by the chord over \(J\),
and restoring height. These operations keep \(a\) fixed and do not
decrease the score, so the known universal upper bound forces equality
throughout. The resulting canonical cap has height one, affine middle
roof, and top face meeting \(J\). For this prescribed cap, saturation
by precisely the used supporting halfplanes, followed by intersection
with its middle chord, is again a nondecreasing comparison. Maximality
therefore gives the identity

\[
U=\operatorname{Sat}_a(U)\cap\{y\le\ell(x)\},
\tag{PT.5}
\]

where \(\ell\) is its middle chord. The saturation step retains all
used supports, including the outgoing support; extrusion and chord
cutting need not retain them. PD also supplies width coercivity and
joint attainment for the value proof.

These are reductions of the actual spatial objective. Vertical
extrusion raises every attached inner wall by the extrusion height;
the positive-floor maximum can increase by at most that amount.
Since the charged exterior and middle window have equal lengths, the
roof gain pays the barrier increase. Cutting by the middle chord
preserves the exterior roof and decreases all supports, so it cannot
raise the niche penalty. Saturation restores every point allowed by
the used supports without changing their barrier, and the chord
intersection retains the affine middle. The same domain
argument controls the angular endpoint tails, making the barriers
continuous under the compact cap and angle limits used for attainment.
None of these steps assumes smoothness or bounds polygon complexity.

The source theorem [PS1](gate2-partial-endpoint-source-and-green.md)
applies to this prescribed maximizing cap at its fixed angle. Its
finite approximants carry a vanishing support penalty toward that cap,
so the conclusion is not an existence assertion about an unrelated
regular maximizer. Translate horizontally to
\(I=[-2C,2C]\), \(J=[-C,C]\), and put
\(Q_\pm=A(\pm C)+N_a(\pm C)\). The actual endpoint heights
satisfy

\[
e_R=A(2C)=\frac{3Q_+-Q_-}{4}>0,\qquad
e_L=A(-2C)=\frac{3Q_--Q_+}{4}>0.
\tag{PT.6}
\]

The limiting finite-source measure equals the actual arclength measure
of the charged outer roof above \(I\setminus J\), omitting vertical
end faces and the horizontal top. It has bounded density on the
visited open normal arcs. Its only possible atom is at the first
terminal normal \(a\); there is no companion terminal atom and no
charged curvature on unused open arcs. The affine middle remains an
uncharged facet. These distinctions also hold when it is tilted.

The finite-source proof retains the floor in every finite maximum and
uses actual moving-window variations for PT.6. A nonterminal source
has exposure bounded by a constant times its angular mesh, excluding
both interior atoms and singular concentration in the limit. The
whole outgoing line is the one exceptional source and is kept
separately. The equality of the limiting source measure with the
actual charged wing measure is obtained before interpreting its
terminal mass. This order matters: no arclength identity for a
possibly vanishing-height limiting barrier is substituted for the
source theorem.

If the terminal charged facet has horizontal length \(m\), there is
a measurable terminal occupation \(0\le\chi\le1\) such that

\[
\int_J\chi(x)\,dx=m,\qquad
\chi=1\text{ a.e. on }E:=\{x\in J:R_a(x)>n_a(x)\}.
\tag{PT.7}
\]

Only strict exposure is used. Positive-length historical ties may have
fractional occupation; shape and angle variations are not assigned a
common fractional choice.

## 3. Exact angle, width and tilt reductions

The all-width certificate
[AT](gate2-all-width-terminal-angle-exclusion.md) gives

\[
a\le\arctan(8/3)
\quad\Longrightarrow\quad
\mathcal P_a(U)<5259/6400<M/2.
\tag{PT.8}
\]

Hence an equality pair has \(a>\arctan(8/3)>3\pi/8\).
The three genuine tents at \(\pi/8,\pi/4,3\pi/8\) are
therefore visited. Their comparisons in
[TP, Section 1](gate2-terminal-facet-and-prefix-reduction.md) and
[WC](gate2-three-angle-width-cut.md), using PT.6 and the joint
positive-floor loss, give

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
A(-C)=1-h_L,\quad A(C)=1-h_R,
\]
\[
h_L,h_R\ge0,\qquad \min(h_L,h_R)=0,\qquad
h_L+h_R<\frac{17}{50}.
\tag{PT.9}
\]

These cuts have strict bounds below \(M/2\), so they apply at
equality. The width proof uses the actual partial endpoint pressures;
it requires no full-niche endpoint box at moderate angles. Reflection
in the three-tent comparison reflects its barrier as well. We retain
the original orientation for all subsequent outgoing-wall arguments.

Write \(c=\cos a\), \(s=\sin a\), and
\(\kappa=\cot a\). Then
\(0<c<3/\sqrt{73}\) and \(0<\kappa<3/8\). For a negative
middle tilt, \(h_R>0\), the exact completion theorem
[NT1](gate2-negative-tilt-completion.md) gives
\(N_a\ge n_L\) on \(J\) if either

\[
a\ge\theta_0:=L-\arctan(h_R/(2C)),\qquad
h_R\ge1-s.
\tag{PT.10}
\]

It follows on the same cap that
\(M/2=\mathcal P_a(U)\le\mathcal P_L(U)\le M/2\).
Full-turn equality makes its middle horizontal, contradicting
\(h_R>0\). The remaining negative case has
\(a<\theta_0\), \(0<h_R<1-s\). Positive and horizontal
middles remain in the original orientation.

## 4. Terminal geometry and the fixed-cap facet contradiction

For every remaining sign put

\[
H=1-h_R>s,\qquad b=C+T_R,\qquad
d=\frac{1-Hs}{c},\qquad w=c-d,
\tag{PT.11}
\]

where \(T_L,T_R\) are the height-one top overhangs outside the
ends of \(J\). They vanish on a strictly lower middle side. The
terminal facet endpoints, shifted endpoints, and outgoing zero are

\[
(b,H),\quad(b+m,H-mc/s),\qquad
B_+=(b-c,H-s),\quad B_-=B_++(m,-mc/s),
\]
\[
r_0=b-d,\qquad
R_a(-C+z)=\frac cs(2C+T_R-d-z).
\tag{PT.12}
\]

Let \(z_a\) be the intersection of the two terminal inner lines.
The corner estimate and horizontal source moment of TP give,
independently of any terminal mass bound,

\[
(z_a)_x<(B_+)_x,\qquad T_L+2T_R\le d,\qquad
0<d<c<C,\quad0<w<c/2.
\tag{PT.13}
\]

In particular \(0<(B_+)_x<r_0<C\). We now establish
\(m\le w\) for this individual equality pair.

Suppose \(m>w\). Then \((B_-)_x>r_0\). On
\((z_a)_x<x<(B_-)_x\), the terminal companion wall is above
the first wall, and the left angle derivative is

\[
S_a(x)>R_a(x),\qquad
\partial_-R_a(x)=\frac{x-(B_-)_x}{s^2}<0.
\tag{PT.14}
\]

Nearby earlier two-wall minima are consequently strictly greater
than \(R_a(x)\), giving \(n_a(x)>R_a(x)\) there. For
\(x\ge(B_-)_x\), the outgoing wall is negative. Thus strict
exposure and relevant ties occur only to the left of \((z_a)_x\).
The exact right angle law
[TV3](gate2-terminal-angle-variations.md), with
\(F=\{R_a=n_a\}\), says

\[
\int_E(x-(B_+)_x)\,dx+
\int_F(x-(B_+)_x)_+\,dx\ge0.
\tag{PT.15}
\]

The second integral vanishes and the first has a strictly negative
integrand. Hence \(|E|=0\); continuity gives \(n_a\ge R_a\)
everywhere on \(J\).

Choose

\[
\max\{-C,(z_a)_x\}<\zeta<(B_+)_x<r_0
<r_*<\min\{C,(B_-)_x\}.
\tag{PT.16}
\]

Immediately after \(a\), the first support of this same saturated
cap is the fixed point \((b,H)\), until \(\theta_0\) in the
negative case. Its first-wall derivative is
\(\partial_tR_t(x)=(x-b+\cos t)/\sin^2t\). It is negative
on \(x\le\zeta\) for sufficiently small angle increments.
On \([\zeta,r_*]\), the strict gap \(n_a-R_a\) has a positive
minimum, which covers the uniformly close new walls. For
\(x\ge r_*\), the new walls remain nonpositive because their
zero \(b-(1-H\sin t)/\cos t\) stays below \(r_*\).
Thus some \(a<\beta<L\), with \(\beta<\theta_0\) when
needed, satisfies

\[
R_t\le n_a\text{ on }J\ (a\le t\le\beta),\qquad
N_{U,\beta}=N_{U,a},\qquad \mathcal P_\beta(U)=M/2.
\tag{PT.17}
\]

Every new two-wall minimum is bounded by its first wall, while all
old minima remain available. This proves exact barrier equality.
The cap, projection, window and middle chord have not changed.
Moreover
\(U\subseteq\operatorname{Sat}_\beta(U)\cap\{y\le\ell\}
\subseteq\operatorname{Sat}_a(U)\cap\{y\le\ell\}=U\).

The original facet still has an open charged segment with \(x>C\)
and positive arclength \(m/s\), but its normal \(a\) is now
interior to the visited first arc \((0,\beta)\). It is not the
middle normal: in the negative case \(a<\beta<\theta_0\),
and in the other cases that normal is at least \(L\). PS applied
to this prescribed maximizing pair forbids the unchanged charged
atom. This contradiction proves

\[
\boxed{m\le w.}
\tag{PT.18}
\]

This is the equality upgrade [TB1](gate3-terminal-and-body-rigidity.md).
The value proof may instead select the largest maximizing angle and
contradict PT.17 directly. The atom argument proves PT.18 without
that selection and therefore applies to each equality cap.

## 5. A weighted companion moment

Let \(g\) now denote the left charged-wing support, with regular
curvature \(v=g''+g\ge0\). For positive tilt take the low-left
surrogate. Removed high-right points satisfy \(X\ge C,Y\le1\),
so their companion walls on \(J\) are bounded by
\(1-\sec t+(x-C)\tan t\le0\). Thus in every sign

\[
g(0)=1-h_L,\quad g'(0+)=C+T_L,\qquad
n_a(x)\le[\max_{0\le t\le a}S_t(x)]_+.
\tag{PT.19}
\]

Set \(A_0=C-T_L\), \(\theta=\arcsin A_0\),
\(G(x)=\sqrt{1-x^2}\), and \(\lambda=\tan\theta\).
The shifted companion support point satisfies

\[
D_x=-g'\cos t-(g-1)\sin t,\quad
D_y=-g'\sin t+(g-1)\cos t,
\]
\[
D_x'=(1-v)\cos t,\quad D_y'=(1-v)\sin t,\qquad
S_t'(x)=\frac{x-D_x(t)}{\cos^2t}.
\tag{PT.20}
\]

At \(x=-C+z\), \(0\le z\le w\), any positive maximizing
wall is interior and satisfies \(D_x(t)=x\),
\(S_t(x)=D_y(t)\), and \(\sin t\le C+z\). Indeed its outer
support abscissa is \(D_x-\sin t\ge-2C\), so the wall is
strictly decreasing when \(\sin t>C+z\); and
\(C+z\le C+c/2<s\).

The initial shifted point is \((-C-T_L,-h_L)\). Integration
at a maximizing angle gives the exact weighted identity

\[
D_y(t)+h_L-\lambda(T_L+z)
=\int_0^t(1-v(r))(\sin r-\lambda\cos r)\,dr.
\tag{PT.21}
\]

Define the early excess cost

\[
\mathcal E_\theta=
\int_0^\theta(v(r)-1)_+
\frac{\sin(\theta-r)}{\cos\theta}\,dr.
\tag{PT.22}
\]

Before \(\theta\), PT.21's integrand is bounded by this positive
excess; afterward it is bounded by \(\sin r-\lambda\cos r\)
because \(v\ge0\). Maximizing the resulting expression over
\(t\le\arcsin(C+z)\) yields

\[
n_a(-C+z)\le
[-h_L+G(C-T_L)-G(C+z)+\mathcal E_\theta]_+
\le G(C-T_L)-G(C+z)+\mathcal E_\theta.
\tag{PT.23}
\]

This is [MP.10--16](gate2-companion-moment-prefix-exclusion.md).
Curvature above one after \(\theta\) causes no adverse error.

MP's exact scalar comparison gives, uniformly for \(0\le z\le w\),

\[
R_a(-C+z)-[G(C-T_L)-G(C+z)]>\frac{39c}{4400}.
\tag{PT.24}
\]

For clarity, its reduction uses \(z=w\), \(T_L\le d\),
\(T_R\ge0\), and \(d\ge\delta=c/(1+s)\). After division
by \(c\), the remaining lower bound is

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta),\qquad
\mathcal A_q(y)=\frac1q\int_{y-q/2}^{y+q/2}
\frac{x}{\sqrt{1-x^2}}\,dx,\quad
\eta=\frac{c^3}{2(1+s)^2}.
\tag{PT.25}
\]

The average is increasing in its center and width and convex in its
center. Exact comparisons at \(C=1/2,37/50\), split at
\(c=1/3\), give lower margins \(8/495\) and \(39/4400\).
Concavity in \(C\) proves PT.24 throughout the interval; all radical
comparisons in MP.20--23 are certified by squaring positive rationals.

It remains to pay \(\mathcal E_\theta\le39c/4400\). Then
PT.23--24 make \([-C,-C+w]\) strictly exposed. Continuity extends
exposure a positive distance beyond its interior right endpoint, so
\(|E|>w\ge m\), contradicting PT.7.

## 6. Reflected curvature bounds pay the complete angle range

Reflection is used only on local support equations. For corresponding
wing supports put \(u=f''+f\), \(p=f'-g+1\),
\(q=g'+f-1\), and under
\(r=L-t\) write

\[
P(r)=-q(L-r),\quad Q(r)=-p(L-r),\quad
U(r)=v(L-r),\quad V(r)=u(L-r),
\]
\[
P'=U-1-Q,\quad Q'=V-1+P.
\tag{PT.26}
\]

On regular retained intervals the actual source laws give

\[
P\le1,\quad Q\ge-1,\qquad
U\le\max\{|Q|,(1+|Q|)/2\},\quad
V\le\max\{|P|,(1+|P|)/2\}.
\tag{PT.27}
\]

In the positive \(P,Q\) sector, \(U=0,V\le1/2\). Every later
positive-\(Q\) component has amplitude at most \(1/8\), hence
cannot carry \(U>1\). The unused gap has \(U=V=0\); at its
end \(\varepsilon=L-a\), the terminal facet produces one upward
jump \(j=m/s\le\delta=c/(1+s)\) in \(Q\). There are no
further used-angle atoms. For negative tilt the unused central atom
is removed by the right-wing surrogate, preserving every used first
support. On the final removed positive-central interval both densities
vanish directly, without an appeal to reflected arm bounds.

The initial reflected state is \((P,Q)=(e,d_0-1)\), where

\[
(e,d_0)=
\begin{cases}
(e_L,3C+T_R),&h_R=0,\\
(e_L+h_R,3C),&h_R>0.
\end{cases}
\tag{PT.28}
\]

For \(\mathcal H=(P-1/2)^2+(Q+1)^2\), the exact gap and
impulse calculation gives

\[
\mathcal H(\varepsilon+)-\mathcal H(0)
\le\delta^2\left[
\frac{2e-1+\delta^2}{1+\delta^2}-d_0c\right].
\tag{PT.29}
\]

**The range \(0<\kappa\le1/8\).** The valid small-deficit
endpoint bounds and PT.29 give impulse cost below \(1/480\).
The theorem [RX](gate2-reflected-tail-cot-one-eighth.md) proves that
every possible reflected excess has ended before \(18/25\). It
includes a first \(P\)-zero in the unused gap and the terminal
jump. Since \(\cos(18/25)>37/50>C\),

\[
v(t)\le1\quad\text{a.e. on }(0,\arcsin C),\qquad
\mathcal E_\theta=0.
\tag{PT.30}
\]

**The range \(1/8\le\kappa<3/8\).** Here the actual outgoing
wall in PT.6 yields \(e<179/200,d_0<2311/1000\) for
positive or horizontal middle, and \(e<1,d_0<111/50\) for
negative middle. The impulse cost is below \(1/30\). The theorem
[AC](gate2-all-angle-reflected-cubic-exclusion.md) starts its decay
comparison at the first \(P\)-zero, or at \(\varepsilon\) if
that zero preceded the terminal impulse. With \(\rho\) the elapsed
time from this starting point, it obtains
\(Q-1\le\sqrt Z-2-\rho/2-\rho^2/4\), where
\(Z=d_0^2-e(1-e)+1/30\). Its coupled time and amplitude
comparison puts every excess endpoint before \(91/100\), giving

\[
(U(r)-1)_+\le\frac{19}{25}(91/100-r)_+
\quad\text{for a.e. }r.
\tag{PT.31}
\]

AC checks the first zero before, at, and after the impulse. Its two
parameter endpoint certificates are exact squared inequalities, and
its control of subsequent source components is uniform in the tilt.

More explicitly, after \(P\le0\), an interval with \(Q>1\)
has \(P'\le-1\). The arm bound for \(V\) then gives
\(Q'\le-1/2-\rho/2\) until the predicted excess ends. Its
duration is at most
\(D(Z)=\sqrt{1+4(\sqrt Z-2)_+}-1<13/25\).
When the zero follows the impulse, its time is bounded by
\(\tau(d_0,e)=d_0-\sqrt{d_0^2-2e}\). The relevant expression
\(\tau+D\) is increasing in both parameters on \(Z>4\), and
the two parameter pairs above give upper bounds \(91/100\) and
\(9/10\). If the zero precedes the impulse, the direct bound is
\(\varepsilon+D<22/25\). Factoring the quadratic decay supplies
the slope \(19/25\) in PT.31. This gives a coupled time and
amplitude estimate, including the nonsmooth terminal jump.

Return to \(t=L-r\), and put \(t_0=L-91/100\).
Since \(C-T_L<37/50\),
\(\cos\theta>2/3\) and
\(\arccos(C-T_L)>147/200\). Thus
\(\ell=(\theta-t_0)_+<7/40\). Using
\(\sin(\theta-t)\le\theta-t\) in PT.22 gives

\[
\begin{aligned}
\mathcal E_\theta
&\le\frac{19}{25\cos\theta}
\int_{t_0}^{\theta}(t-t_0)(\theta-t)\,dt\\
&=\frac{19\ell^3}{150\cos\theta}
<\frac{6517}{6400000}
<\frac{117}{110000}<\frac{39c}{4400}.
\end{aligned}
\tag{PT.32}
\]

If \(\ell=0\), the cost is zero and the integral is omitted.
The last comparison uses \(c\ge1/\sqrt{65}>3/25\), and the
middle rational gap is \(3193/70400000>0\). This pays the
weighted error on the entire second range. The ranges overlap at
\(\kappa=1/8\).

## 7. Strictness for the original equality angle

The order of the value and equality arguments can now be stated
explicitly. To prove the non-strict bound, assume a score greater
than \(M/2\). PD gives an attained global maximum and a largest
terminal angle among its maximizers. Its full-turn boundary is
excluded by the full-turn value theorem. PT.8--9 and the source laws
apply because the maximum exceeds the same strict numerical
thresholds. A completed negative case is excluded immediately by
\(\mathcal P_a(U)\le\mathcal P_L(U)\le M/2\), using no
full-turn equality theorem. For the remaining signs, the barrier
equality in PT.17 would preserve that larger maximum and contradict
the largest-angle choice if \(m>w\). Thus PT.18 holds,
and the weighted estimate and the two payments give the source
occupation contradiction. This is the universal value proof G2C1.
The reference attains \(M/2\), so the maximum is known exactly.

Only after that result do we start with an arbitrary equality cap,
as in Section 2. The same-cap interior-atom argument in Section 4
replaces the largest-angle choice. This is the only change needed
in the terminal mass step; the local source, geometric and reflected
estimates depend on the displayed quantitative hypotheses, which
hold unchanged at equality. The completed negative case now uses
the full-turn equality classification on that same cap.

PT.30 or PT.32 supplies the cost bound required after PT.25, giving
the contradiction to terminal occupation in every residual middle
sign. The completed negative branch was excluded on the same cap by
full-turn equality, and PT.8 includes the lower boundary
\(a=\pi/4\). No proper-angle canonical equality pair remains.

An arbitrary proper-angle equality cap would have produced such a
pair through the score-preserving, angle-preserving reductions of
Section 2. It therefore cannot exist. This proves the strict part of
PT.4 for all original caps, including subunit height and nonsmooth
boundaries. At \(a=L\), the non-strict bound and full-cap equality
classification apply. Consequently, when the original two-cap area
inequality is an equality, each of its two original scalar terminal
angles is \(L\), independently of the other angle.
