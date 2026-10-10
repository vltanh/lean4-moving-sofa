# Gate 2: terminal facet mass and the initial companion prefix

Written mathematical reduction, October 10, 2026. This note treats all
three signs of the affine middle roof. It retains the actual outgoing
wall and does not assume a common terminal occupation for shape and
angle variations. Its final exclusion is conditional on an explicitly
stated initial companion-curvature bound, supplied by separate
curvature arguments in [the Gate 2 closure](gate2-sharp-partial-turn-closure.md).

The inputs are [PD](gate2-partial-cap-domain-reductions.md),
[PS](gate2-partial-endpoint-source-and-green.md),
[TV](gate2-terminal-angle-variations.md), and the
[negative-tilt completion theorem](gate2-negative-tilt-completion.md).
The all-width [angle exclusion](gate2-all-width-terminal-angle-exclusion.md)
supplies the three visited angles used in Section 1. Gate 2 is not
asserted by this note alone; [the Gate 2 closure](gate2-sharp-partial-turn-closure.md) records the complete
dependency chain.

Labels TP are local. Suppose an above-reference joint partial-cap
maximum exists. Select one with the largest terminal angle, then apply
the score-preserving canonical reductions at that angle. Write

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad a=\alpha<\pi/2,
\qquad c=\cos a,\quad s=\sin a.
\]

Use \(N\) for the actual partial barrier, including the outgoing wall.
All source measures below are the selected finite-source limits of PS.

## 1. Width and tilt cuts that use only three actual angles

The angle exclusion gives \(a>\arctan(8/3)>3\pi/8\). Consequently
the genuine two-wall tents at \(\pi/8,\pi/4,3\pi/8\) all occur in
the partial history. Their maximum is unchanged by horizontal
reflection, which exchanges the first and third tents.

For the purposes of this three-angle comparison only, orient the high
middle endpoint to the right and put

\[
A(-C)=1-h,\quad A(C)=1,\quad
q_-=N(-C),\quad q_+=N(C),\quad 0\le h<1/2.
\]

If the cap was reflected, reflect \(N\) as well. There is no assertion
that the reflected barrier is another partial objective with the same
first outgoing wall. PS's endpoint equations, simply relabeled, give

\[
e_R=\tfrac12+\tfrac h4+\tfrac{3q_+-q_-}{4},\qquad
e_L=\tfrac12-\tfrac{3h}{4}+\tfrac{3q_--q_+}{4}.
\tag{TP.1}
\]

The affine middle roof and concavity imply \(e_R\le1\) and
\(e_L\le1-3h/2\). Eliminating the opposite barrier endpoint from
TP.1 therefore gives the useful direct inequalities

\[
\boxed{e_R\ge\tfrac13+\tfrac h2+\tfrac23q_+,\qquad
e_L\ge\tfrac13-\tfrac{2h}{3}+\tfrac23q_-.}
\tag{TP.2}
\]

In particular the lower bounds used in TW.22,
\(e_R\ge1/3+h/4\) and \(e_L\ge1/3-3h/4\), remain valid even
when one endpoint is charged by the whole outgoing wall. No endpoint
niche box bound is needed for this step.

The short-width proofs TS and GAP in
[the Gate 1 width note](gate1-tilted-width-exclusions.md), Parts A--B,
bound exterior area minus the maximum of precisely the three displayed
tents. Their lifted support calculations and all floor/window clips
therefore bound the present score. The wide proof TW in Part C does
the same; its only use of a two-sided endpoint box estimate is to derive
TW.22, for which TP.2 is a stronger replacement. Its other endpoint
inputs are TP.1 and the nonnegativity of \(q_\pm\). Finally INT in
Part D uses only the 45-degree tent and the affine roof. These explicit
transfers give, for every remaining sign of the middle tilt,

\[
\boxed{\frac{1001}{2000}<C<\frac45,\qquad 0\le h<\frac{17}{50}.}
\tag{TP.3}
\]

The horizontal case is included by \(h=0\). This invokes the actual
finite-angle area estimates, not the full-turn maximizer laws.

## 2. Tail data without reflecting the outgoing wall

Return to the original orientation. Write

\[
A(-C)=1-h_L,\qquad A(C)=1-h_R,
\qquad h_L,h_R\ge0,\quad \min(h_L,h_R)=0.
\]

Let \(T_L,T_R\) be the lengths of any height-one top overhangs
outside the left and right ends of \(J\). Thus \(T_L=0\) when
\(h_L>0\), and \(T_R=0\) when \(h_R>0\).

If \(h_R>0\), the negative-tilt theorem already completes the cap
unless

\[
h_R<1-s,\qquad
a<\theta_0:=\pi/2-\arctan(h_R/(2C)).
\tag{TP.4}
\]

Discard that completed branch. Set

\[
b=C+T_R,\qquad H=1-h_R,\qquad
d=\frac{1-Hs}{c},\qquad w_H=c-d.
\tag{TP.5}
\]

In all remaining cases, \(s<H\le1\), and hence

\[
0<d<c,\qquad
0<w_H\le\frac{sc}{1+s}<\frac c2.
\tag{TP.6}
\]

PD's support saturation and PS's facet pinning identify the first
support immediately after \(a\) with the point \((b,H)\). For
positive or horizontal middle this is the right endpoint of the top
face. For negative middle it is \((C,1-h_R)\), until the unused
central normal \(\theta_0\). The second support immediately after
\(a\) is the outer left endpoint \((-2C,e_L)\), and PS excludes
a companion terminal atom.

The first terminal facet therefore has endpoints

\[
(b,H),\qquad (b+m,H-mc/s),\qquad m\ge0,
\tag{TP.7}
\]

where \(m\) is its charged horizontal length. Its shifted endpoints,
the outgoing wall, and its zero are

\[
B_+=(b-c,H-s),\qquad B_-=B_++(m,-mc/s),
\]
\[
R_a(x)=\frac cs(b-d-x),\qquad r_0=b-d.
\tag{TP.8}
\]

## 3. Two unconditional terminal bounds

The terminal corner \(z_a\) satisfies

\[
(z_a)_x-(B_+)_x
=s[1-(b+2C)s+(H-e_L)c]<0.
\tag{TP.9}
\]

Indeed \(b\ge C>1/2\), \(H\le1\), and \(e_L\ge0\). Since
\(a>3\pi/8\), we have \(s>12/13\) and \(c<5/13\), so
\((b+2C)s+(e_L-H)c\ge3Cs-c>1\).

**Terminal facet bound.** One has

\[
\boxed{m\le w_H.}
\tag{TP.10}
\]

Here is the direct extension of PU's largest-angle argument, including
the lower tail height \(H\). If \(m>w_H\), then
\((B_-)_x>r_0\). At every
\(x\in((z_a)_x,(B_-)_x)\), the second terminal wall exceeds
\(R_a(x)\), while the left angle derivative of the first wall is
negative. A sufficiently close earlier quadrant strictly exceeds
\(R_a\) there. Every positive strip exposure or terminal tie must
therefore lie left of \((z_a)_x<(B_+)_x\). TV.3 makes the strict
exposure set null, since its entire derivative integrand is negative;
continuity then gives \(n_a\ge R_a\) on \(J\).

Choose \(\zeta\) between \((z_a)_x\) and \((B_+)_x\), taking
its intersection with \(J\) when appropriate. Immediately after
\(a\), the first supports are the fixed point \((b,H)\). Below
\(\zeta\) their walls decrease with angle, because the shifted
point's abscissa \(b-\cos t\) increases. Above \(\zeta\) their
positive support ends at
\(b-(1-H\sin t)/\cos t\), which stays below \((B_-)_x\) for
a sufficiently small angle increment. The compact intervening
interval has a strict old-history gap; uniform continuity pays every
new first wall there. The new two-wall minima are bounded by those
same first walls. Thus the partial barrier is unchanged for a small
increase of \(a\), contradicting the largest-angle choice. In the
negative case the increment is chosen below \(\theta_0-a\).

**Top projection bound.** The exact source horizontal moment is
\(2C-T_L-T_R\). Uniform convergence on compact positive-barrier
intervals gives

\[
2C-T_L-T_R\ge |\{x\in J:N(x)>0\}|
\ge |J\cap(-\infty,r_0)|.
\]

If \(T_R\ge d\), the last length is \(2C\), impossible because
\(d>0\). Thus \(T_R<d\). Also \(r_0>C-c>0>-C\), so the
same inequality now yields

\[
\boxed{T_L+2T_R\le d.}
\tag{TP.11}
\]

No zero-set convergence or ordinary continuum source-arclength
identity has been assumed in this projection argument.

## 4. The ordinary endpoint box is recovered at small deficit

Put \(H_0(C)=1-\sqrt{1-C^2}\). The unit-height box gives
\(n_a(C),n_a(-C)\le H_0(C)\) for the visited niche: use its
first wall at \(C\) and its second wall at \(-C\), respectively.
The outgoing wall at \(C\) is negative by TP.11, whereas

\[
R_a(-C)=\frac cs(2C+T_R-d)\le 2C\cot a.
\]

For \(C>1/2\),
\(H_0(C)=C^2/(1+\sqrt{1-C^2})\ge C^2/2>C/4\).
Consequently

\[
\cot a\le\tfrac18
\quad\Longrightarrow\quad
\boxed{N(-C),N(C)\le H_0(C).}
\tag{TP.12}
\]

The [three full triangle width proof](gate1-tilted-full-triangle-width-cut.md)
FT.4--FT.26 uses the three visited tents, the endpoint equations, and
these two box bounds. Every one of those inputs now holds for the
partial score, including after the purely comparative reflection of
Section 1. Its exact upper bound excludes \(C\ge37/50\). Thus

\[
\boxed{\cot a\le1/8\quad\Longrightarrow\quad C<37/50.}
\tag{TP.13}
\]

This is a transfer of a finite-angle scalar upper bound. It does not
assert that a full-turn extremizer theorem applies to the partial cap.

## 5. An initial companion-unit bound suffices

Let \(g\) be the support of the left charged wing. When \(h_L>0\),
this is the usual low-wing surrogate; the omitted high-point second
wall is nonpositive on \(J\). In the other two cases it is the
actual second support. In all cases

\[
g(0)=1-h_L,\qquad g'(0)=C+T_L,\qquad
g(a)=2C\sin a+e_L\cos a.
\tag{TP.14}
\]

Suppose additionally that

\[
0<c\le1/25,\qquad
0\le v(t):=g''(t)+g(t)\le1
\quad\text{for a.e. }0<t<\arcsin(C+w_H).
\tag{TP.15}
\]

This prefix lies before \(a\): TP.13 gives \(C<37/50\), and
TP.6 gives \(C+w_H<19/25<s\). We claim TP.15 is impossible at
the selected maximizer.

For \(x=-C+z\), \(0\le z\le w_H\), the second terminal wall is
strictly negative. Indeed, using \(e_L\le1\),

\[
S_a(x)=e_L-\frac{1-(C+z)s}{c}
\le1-\frac{1-19/25}{1/25}<0.
\tag{TP.16}
\]

At zero the wall limit is \(-h_L\le0\). Therefore a positive
maximum of the whole second-wall family on \([0,a]\) is attained
at an interior angle. Its stationary equation is
\(D_x(t)=x\), where the outer support point has horizontal
coordinate at least \(-2C\). Since \(D_x=X+\sin t\),

\[
\sin t\le C+z\le C+w_H.
\tag{TP.17}
\]

The support representation and TP.15 then give

\[
g(t)\le(1-h_L)\cos t+(C+T_L)\sin t+1-\cos t,
\]
\[
S_t(-C+z)\le-h_L+(T_L+z)\tan t
\le c\,K(C+c/2),\qquad K(x)=\frac{x}{\sqrt{1-x^2}}.
\tag{TP.18}
\]

The last step uses TP.11 and \(z\le w_H=c-d\), which give
\(T_L+z\le c-2T_R\le c\), as well as TP.17. If no positive
maximum exists, the same upper bound for the positive visited niche
is immediate. The surrogate support is continuously differentiable
on the proper used interval by PS after removal of the uncharged
central facet; thus the stationary equation used here introduces
no unexamined support atom.

For \(1/2\le C\le37/50\) and \(0<c\le1/25\),

\[
\boxed{K(C+c/2)<2C-c.}
\tag{TP.19}
\]

To check this exact scalar comparison, its margin decreases with
\(c\), and is concave in \(C\), since \(K\) is convex. It is
enough to check \(c=1/25\) and the two width endpoints. At
\(C=1/2\), \(K(13/25)<2/3<24/25\); at \(C=37/50\),
\(K(19/25)<6/5<36/25\). Both radical bounds follow by squaring
positive quantities: \(169/625<4/13\) and
\(361/625<36/61\).

By TP.8, throughout the same spatial interval,

\[
R_a(-C+z)=\frac cs(2C+T_R-d-z)
\ge\frac cs(2C-c)>cK(C+c/2)\ge n_a(-C+z).
\tag{TP.20}
\]

Thus the strict terminal exposure set contains
\([-C,-C+w_H]\), and by strictness and continuity it contains
a further interval to its right. This endpoint is interior to \(J\).
Its measure is consequently greater than \(w_H\). But PS.34--35
give full terminal occupation on strict exposure and total occupation
\(m\le w_H\), a contradiction.

**Conclusion TP1.** No above-reference largest-angle partial maximizer
can satisfy TP.15. The argument covers positive, horizontal, and the
remaining negative middle tilt, and uses only an initial bound on
the companion curvature. The separate curvature bounds and complete
angle coverage are assembled in [the Gate 2 closure](gate2-sharp-partial-turn-closure.md).
