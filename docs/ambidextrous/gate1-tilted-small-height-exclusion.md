# Exact scalar exclusion of every remaining sufficiently small tilt

Written proof, independently checked within this research session, October 10, 2026. This combines the initial
floor-energy criterion with the actual ordinary-area lower bound. It uses
no sampled optimization or assumed contact chart. Every displayed final
certificate is rational.

## 1. Statement and dependencies

Let U be the selected canonical global maximizer of the actual spatial
one-cap objective P, with

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
A(-C)=1-h,\quad A(C)=1,
\]

\[
\frac23<C<\frac{37}{50},\qquad
0<h\le\frac{509}{10000}.
\tag{SH1}
\]

Then U cannot exist.

The established ingredients used below are:

* The endpoint pressures, regularity, and stationary identity
  \(2P=L_{\rm wing}\).
* The positive-corner confinement and genuine ordinary one-turn
  feasibility theorem in
  [CG](gate1-tilted-corner-confinement.md).
* The reflected terminal-unit and projection theorem in
  [RT](gate1-tilted-reflected-tail-and-projection.md). In the current
  width range it gives positive top overhang and zero left endpoint
  niche, without either global unit-curvature assumption.
* The early-end theorem and endpoint estimates ET1--ET18 in
  [ET](gate1-tilted-first-excess-ends-early.md).
* The initial floor-energy criterion IE1--IE2 in
  [IE](gate1-tilted-initial-floor-energy.md).
* The general first-good exclusion in
  [GF](gate1-tilted-first-wing-exclusion.md).

The ordinary one-turn bound remains the already recorded exact enclosure

\[
|\mathcal S|\le G_0:=\frac{22199}{10000}.
\tag{SH2}
\]

Here \(\mathcal S=U\setminus N(U)\) is the genuine connected one-turn body
supplied by the confinement theorem. No equality between U and the convex
hull of \(\mathcal S\) is required.

## 2. Exact endpoint and leakage information

Write the top face as \([C,C+T]\times\{1\}\), and put

\[
z=n_U(C),\qquad s=\sqrt{h(2-h)},\qquad
K=\frac{C}{\sqrt{1-C^2}},\qquad
J_f=\int_0^{\pi/2}(u(t)-1)_+\sin t\,dt.
\]

The projection theorem and the actual pressure equations give

\[
T>0,\quad n_U(-C)=0,
\]

\[
e_R=\frac12+\frac h4+\frac{3z}{4},\qquad
e_L=\frac12-\frac{3h}{4}-\frac z4.
\tag{SH3}
\]

The pinned low middle point and the endpoint estimate ET16 imply

\[
T\le s,\qquad 0\le z\le KT,\qquad K<\frac{10}{9}.
\tag{SH4}
\]

For completeness, the first inequality follows from the signed second
wall envelope at its zero \(x_{\rm zero}=-C+T\). The low middle point
\((-C,1-h)\) gives the lower wall
\(1-h-\sec t+T\tan t\). Its value at \(\sin t=T\) is
\(1-h-\sqrt{1-T^2}\), and cannot be positive at an envelope zero.
Thus \(T^2\le h(2-h)\). We have \(T\le C<1\), so this angle is
proper. The bound on K follows by squaring and using
\(81\cdot1369<100\cdot1131\).

The ordinary box estimate also gives

\[
z\le1-\sqrt{1-C^2}<\frac{33}{100}.
\tag{SH5}
\]

The early-end proof bounds all possible first-source excess by one
initial envelope

\[
(u(\alpha+\tau)-1)_+
\le\left(\varepsilon-\frac\tau2-\frac{\tau^2}{4}\right)_+,
\qquad \varepsilon<\frac{19}{100}<\frac7{36}.
\]

Its duration is less than \(1/3\), and all excess occurs at angles
less than \(11/15\). Since the parabola with initial value \(7/36\)
vanishes at \(1/3\),

\[
\int(u-1)_+\,dt
<\int_0^{1/3}\left(\frac7{36}-\frac\tau2-\frac{\tau^2}{4}\right)d\tau
=\frac{11}{324}.
\]

Consequently

\[
J_f<\frac{11}{15}\frac{11}{324}
=\frac{121}{4860}<\frac1{40};
\qquad \frac1{40}-\frac{121}{4860}=\frac1{9720}.
\tag{SH6}
\]

ET17--ET18 and convexity of the actual niche on the right wing give

\[
N_{\rm out}\le\frac{(T+J_f)z}{2}.
\tag{SH7}
\]

The left wing contributes no outside niche: its niche roof is convex
with zero values at both endpoints. The middle cap area is \(2C-Ch\).
Thus

\[
|\mathcal S|\ge P+C(2-h)-\frac{(T+J_f)z}{2}.
\tag{SH8}
\]

## 3. A common tangent lower bound for the wing lengths

Define the fixed constants

\[
C_0=\frac{\sqrt{17}}6,\quad
R_0=\frac{\sqrt{26}}6,\quad
S_0=2C_0+R_0,
\]

\[
\lambda=\sqrt{\frac{17}{26}},\qquad
m=\frac{3}{4\sqrt{26}},\qquad
a=\frac{1-\lambda}{2}.
\tag{SH9}
\]

The two charged-wing vertical drops are

\[
r_R=1-e_R=\frac12-\frac h4-\frac{3z}{4},\qquad
r_L=1-h-e_L=\frac12-\frac h4+\frac z4.
\]

They are nonnegative by the actual cap geometry. The top overhang has
length T, while the nonhorizontal right wing has horizontal displacement
\(C-T\). The stationary length identity and the two chord bounds yield

\[
P\ge\frac12\left[T+
\sqrt{(C-T)^2+r_R^2}+\sqrt{C^2+r_L^2}\right].
\tag{SH10}
\]

The tangent inequality for the Euclidean norm at \((C_0,1/2)\) is

\[
\sqrt{x^2+y^2}\ge\lambda x+\frac{3}{\sqrt{26}}y.
\]

Apply it to the two chords in SH10, and use
\(\lambda C_0+3/(2\sqrt{26})=R_0\). Combining with SH8 gives

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-Ch-m(h+z)+aT-\frac{(T+J_f)z}{2}.
\tag{SH11}
\]

The following rational enclosures follow by squaring positive numbers:

\[
\frac{8086}{10000}<\lambda<\frac{8087}{10000},\qquad
m<\frac{1471}{10000},\qquad a>\frac{956}{10000}.
\tag{SH12}
\]

Since SH4 implies \(T\ge9z/10\), SH6 and SH12 imply

\[
-mz+aT-\frac{J_fz}{2}\ge-\frac{1839}{25000}z.
\]

Here

\[
\frac{1471}{10000}+\frac1{80}
-\frac{956}{10000}\frac9{10}
=\frac{1839}{25000}.
\]

In particular the useful common lower bound is

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-\frac{8871}{10000}h-\frac{1839}{25000}z-\frac{Tz}{2}.
\tag{SH13}
\]

Finally

\[
S_0>\frac{2\cdot4123+5099}{6000}
=\frac{2669}{1200}>G_0,
\quad \frac{2669}{1200}-G_0=\frac{16}{3750}.
\tag{SH14}
\]

The radical comparisons here are
\((4123/1000)^2<17\) and \((5099/1000)^2<26\).

## 4. Failure of the second initial-energy inequality is impossible

Put

\[
d=3C,\qquad B=e_R-1+h=-\frac12+\frac{5h+3z}{4}.
\]

The second initial-floor criterion is

\[
Q:=d^2+B^2+B(1-h)-ds\le4.
\]

Suppose it fails. The exact square completion is

\[
Q=\left(3C-\frac s2\right)^2
+\frac9{16}(h+z)^2-\frac14,
\]

so

\[
\left(3C-\frac s2\right)^2
+\frac9{16}(h+z)^2>\frac{17}{4}.
\tag{SH15}
\]

Write \(w=h+z\). SH1 and SH5 give \(w<2/3\), and
\(3C-s/2>0\). Rationalizing the difference of the two positive
square roots gives

\[
\frac{\sqrt{17}}2-
\sqrt{\frac{17}{4}-\frac9{16}w^2}
=\frac{9w^2/16}{\sqrt{17}/2+
\sqrt{17/4-9w^2/16}}
<\frac9{64}w^2.
\]

The denominator exceeds four because \(w<2/3\). Therefore SH15
implies

\[
C-C_0>\frac s6-\frac3{64}(h+z)^2.
\tag{SH16}
\]

Insert SH16 into SH13. Use the lower enclosure for \(\lambda\) on
the positive s term, its upper enclosure on the negative squared term,
and SH4 on all occurrences of z and T. The result is

\[
|\mathcal S|-S_0\ge
\frac{57955}{150000}s
-\frac{8871}{10000}h-\frac59s^2
-\frac{84261}{640000}
\left(h+\frac{10}{9}s\right)^2.
\tag{SH17}
\]

The linear coefficient is exactly

\[
\frac{2+8086/10000}{6}
-\left(\frac{1471}{10000}+\frac1{80}
-\frac{956}{10000}\frac9{10}\right)\frac{10}{9}
=\frac{11591}{30000}=\frac{57955}{150000}.
\]

Here is a complete rational positivity certificate for SH17. Set

\[
A=\frac{11591}{30000},\quad
D=\frac{8871}{10000},\quad
Q_0=\frac{84261}{640000},\quad
k=\frac{10000}{19491},\quad s_* =\frac{63}{200}.
\]

Since \(h\le509/10000\),

\[
h\le ks^2,\qquad 0<s<s_*.
\]

Indeed \(s^2=h(2-h)\ge(19491/10000)h\), and

\[
s_*^2-\frac{509}{10000}\frac{19491}{10000}
=\frac{1581}{100000000}>0.
\]

The right side of SH17 is consequently at least

\[
s\left[A-\left(Dk+\frac59\right)s
-Q_0s\left(\frac{10}{9}+ks\right)^2\right].
\]

The bracket decreases for \(s\ge0\). Its value at \(s_*\) is
exactly

\[
A-\left(Dk+\frac59\right)s_*
-Q_0s_*\left(\frac{10}{9}+ks_*\right)^2
=\frac{11102231813}{13507522880000}>0.
\tag{SH18}
\]

Thus \(|\mathcal S|>S_0>G_0\), contradicting SH2. Failure of
IE2 is impossible on SH1.

## 5. Failure of the first initial-energy inequality is impossible

Suppose instead that

\[
9C^2+B^2>5.
\tag{SH19}
\]

Write \(\xi=(5h+3z)/4\), so \(B=-1/2+\xi\).
SH1 and SH5 imply \(0<\xi<1/2\), hence \(-1/2<B<0\).
It follows from SH19 that

\[
C>\frac{\sqrt{19}}6>\frac{29}{40}.
\tag{SH20}
\]

Also

\[
B^2>5-9\left(\frac{37}{50}\right)^2
=\frac{179}{2500}>\frac{16}{225}.
\]

The last gap is \(11/22500\). Since B is negative,

\[
B<-\frac4{15},\qquad \xi<\frac7{30}.
\tag{SH21}
\]

These inequalities give a useful improved endpoint bound

\[
z<\frac{27}{100}.
\tag{SH22}
\]

To verify it, if \(h\le1/40\), then
\(s<9/40\) and SH4 gives \(z<1/4\).
If \(h\ge1/40\), then
\(\xi\ge1/32+3z/4\); SH21 therefore gives
\(z<97/360<27/100\).

Use SH20 together with \(C_0<11/16\),
\(2+\lambda>14/5\), and SH14. Since the width difference is positive,

\[
S_0+(2+\lambda)(C-C_0)
>\frac{2669}{1200}+\frac{14}{5}
\left(\frac{29}{40}-\frac{11}{16}\right)
=\frac{559}{240}.
\]

Finally \(T\le s<63/200\). Substituting this, SH1 and SH22 into
SH13 gives

\[
\begin{aligned}
|\mathcal S|
&>\frac{559}{240}
-\frac{8871}{10000}\frac{509}{10000}
-\left(\frac{1839}{25000}+\frac{63}{400}\right)
\frac{27}{100}\\
&=\frac{666488123}{300000000}.
\end{aligned}
\tag{SH23}
\]

Its exact margin over the ordinary bound is

\[
\frac{666488123}{300000000}-G_0
=\frac{518123}{300000000}>0.
\tag{SH24}
\]

This contradicts SH2 and excludes failure of IE1 throughout the same
height range as Section 4.

## 6. Conclusion

If both initial-floor inequalities hold, IE gives \(u\le1\) on the
whole first quarter, and the general first-good theorem excludes the
tilted global maximizer. Sections 4 and 5 exclude failure of either
inequality. Therefore every cap satisfying SH1 is impossible.

This is an actual selected-maximizer branch exclusion. It does not assert
the global first-quarter curvature bound for larger tilts, and it does
not by itself settle Gate 1.

Together with the [final height reduction](gate1-tilted-final-height-reduction.md),
this closes every remaining tilted canonical maximizer. See the
[complete Gate 1 theorem](gate1-sharp-full-turn-closure.md) for the global implication.
[The fixed Fraction checker](computer-assisted/check_gate1_final_scalar_exact.py)
reproduces the rational certificates without sampling or optimization.
