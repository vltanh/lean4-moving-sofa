# Gate 2: a companion-unit prefix for every remaining angle at short width

Written mathematical argument, October 10, 2026. This note proves an
initial companion-curvature bound for every remaining terminal angle
when \(C\le7/10\). It concerns the selected largest-angle joint maximizer
of the actual partial objective. It does not reflect that objective or
discard its outgoing strip.

The geometric and finite-source inputs are
[PS](gate2-partial-endpoint-source-and-green.md),
[TP](gate2-terminal-facet-and-prefix-reduction.md), and the reflected
support equations developed in
[RP](gate2-small-deficit-companion-prefix.md). The estimates below replace
RP's small-angle parameter bounds; its reflection and exact impulse
calculation remain unchanged.

## 1. All-sign initial parameters

Suppose

\[
\frac12<C\le\frac7{10},\qquad
0<\kappa=\cot a<\frac38,\qquad
c=\cos a,\quad s=\sin a,\quad
\varepsilon=\pi/2-a,\quad \delta=\frac{c}{1+s}.
\tag{SW.1}
\]

The negative-tilt branch already completed by NT is discarded. In the
remaining negative case \(0<h<1-s\), and the unvisited central atom is
removed by the right-wing surrogate, exactly as in RP. In the positive
case use the low-left-wing surrogate. No charged used support is changed.

The elementary angle bounds are

\[
s>\frac{14}{15},\quad c<\frac9{25},\quad
\varepsilon<\frac9{25},\quad
\delta<\frac2{11},\quad \delta^2<\frac1{30}.
\tag{SW.2}
\]

Indeed \(s>8/\sqrt{73}>14/15\), and
\(c<3/\sqrt{73}<9/25\). Also
\(\tan(9/25)>9/25+(9/25)^3/3>3/8\), while
\(\delta<3/(8+\sqrt{73})<2/11\). The last comparison uses
\(\sqrt{73}>17/2\), and \(4/121<1/30\).

The visited niche at \(-C\) has the box bound
\(H_0(C)=1-\sqrt{1-C^2}\). TP's terminal wall and projection bound give
\(R_a(-C)\le2C\kappa\). Consequently, since
\(H_0(7/10)<3/10<21/40\),

\[
N(-C)\le\max\{H_0(C),2C\kappa\}\le\frac{21}{40}.
\tag{SW.3}
\]

Reflect the support equations by \(r=\pi/2-t\), and write
\(P=-q\), \(Q=-p\), \(U=v\), \(V=u\). The initial state is
\((P(0),Q(0))=(e,d-1)\). The parameters satisfy

\[
\begin{array}{c|c|c}
\text{middle}&e&d\\ \hline
\text{positive or horizontal}&e_L<143/160<9/10&
3C+T_R<2191/1000\\
\text{remaining negative}&e_L+h<1&3C\le21/10.
\end{array}
\tag{SW.4}
\]

For the first row use
\(e_L=1/2-3h/4+(3N(-C)-N(C))/4\), with \(h=0\) in the
horizontal case, and \(T_R\le\delta/2<1/11\). Thus
\(d<21/10+1/11=241/110<2191/1000\). For the second row,

\[
e_L+h=\frac12+\frac{5h}{4}
+\frac{3N(-C)-N(C)}4
<\frac12+\frac1{12}+\frac{63}{160}<1.
\]

Both rows have \(d>3/2\) and \(e\ge0\). Both regular densities vanish
on \((0,\varepsilon)\), and at \(\varepsilon\) only \(Q\) jumps,
by \(j=m/s\le\delta\). There are no further used atoms. The initial
\(Q\) stays positive: its smallest possible pre-impulse value obeys

\[
Q(\varepsilon-)+1=ds-(1-e)c
>\frac32\frac{14}{15}-\frac9{25}>1.
\tag{SW.5}
\]

## 2. Impulse energy and the only possible excess component

Let \(E=(P-1/2)^2+(Q+1)^2\). The exact RP impulse identity is

\[
E(\varepsilon+)-E(0)
\le\delta^2\left[
\frac{2e-1+\delta^2}{1+\delta^2}-dc\right]
<\frac1{30},
\tag{SW.6}
\]

because \(e\le1\). On the reflected used interval the local source
laws give \(U=0,V\le1/2\) while \(P,Q>0\), and
\(E'=2(Q+1)(V-1/2)\le0\) there. If the first \(P\)-zero is
after the impulse, its value satisfies

\[
(Q+1)^2\le Z:=d^2-e(1-e)+\frac1{30}.
\tag{SW.7}
\]

If \(P\le0\) already at the impulse, the same inequality holds at
that time, since \((P-1/2)^2\ge1/4\). Later positive-\(Q\)
components have amplitude at most \(1/8\), by the local same-sign
propagation, and therefore cannot give \(U>1\).

While \(P>0\) on the first component, \(Q'\ge-1\), its impulse is
upward, and \(P'=-1-Q\le-d+r\). Thus the first zero, if relevant,
occurs by

\[
\tau(d,e)=d-\sqrt{d^2-2e}.
\tag{SW.8}
\]

On the part with \(P\le0,Q>1\), the usual quadratic envelope gives
\(P\le-\rho\) and \(Q'\le-(1+\rho)/2\) for elapsed time
\(0\le\rho\le1\). Therefore the possible excess has ended within

\[
D(Z)=\begin{cases}
0,&Z\le4,\\
\sqrt{4\sqrt Z-7}-1,&Z>4
\end{cases}
\tag{SW.9}
\]

of that zero or of the impulse, whichever is later. All the duration
bounds below are less than one, so the comparison is valid throughout
the required interval. These facts use only the actual partial local
source inequalities, including their reflected versions; the final
removed positive-tilt interval has \(U=0\) directly.

## 3. Uniform end-time bound, including a zero before the impulse

In the positive/horizontal row, \(Z< (2191/1000)^2+1/30<(11/5)^2\),
so \(D(Z)<7/20\). In the negative row,
\(Z\le(21/10)^2+1/30<(211/100)^2\), so \(D(Z)<1/5\).
Thus a comparison starting at the impulse ends before
\(9/25+7/20=71/100\) in either row.

If \(e\le1/4\), SW.8 gives \(\tau<1/5\), since \(d>3/2\).
The same bound \(71/100\) therefore covers this entire low-\(e\)
case, even when the first zero precedes the impulse. If the positive
component ends earlier through \(Q=0\), it creates no excess.

It remains to consider \(e\ge1/4\), a first zero after the impulse,
and \(Z>4\). Put

\[
W(d,e)=d-\sqrt{d^2-2e}+\sqrt{4\sqrt Z-7}-1.
\]

Write \(A=\sqrt{d^2-2e}\), \(S=\sqrt Z\), and
\(Q_0=\sqrt{4S-7}\). Then

\[
W_e=\frac1A+\frac{2e-1}{SQ_0},\qquad
W_d=1-\frac dA+\frac{2d}{SQ_0}.
\tag{SW.10}
\]

On both parameter rectangles in SW.4, restricted to \(Z>4\), these
derivatives are positive. Indeed \(d^2>4-1/30>(199/100)^2\),
\(d/A<3/2\), \(S<11/5\), and \(Q_0<27/20\). These give
\(W_d>-1/2+(398/100)/[(11/5)(27/20)]>0\). For \(e<1/2\)
the possible negative term in \(W_e\) is at most \(1/4\), whereas
\(1/A\ge1/d>4/9\); for \(e\ge1/2\) both terms are positive.

The clipped function \(\tau+D(Z)\) is increasing in \(e\), including
across \(Z=4\), because below that level it is just \(\tau\).
Increase \(e\) to its row's upper endpoint. If this reaches \(Z\le4\),
the resulting bound is \(\tau<3/5\), since \(d>199/100\) and
\(e\le1\). Otherwise increase \(d\) to its upper endpoint using
SW.10. Only the following two exact pairs need checking:

\[
\begin{array}{c|c|c|c}
(d,e)&\tau&\sqrt Z&D(Z)\\ \hline
(2191/1000,9/10)&<23/50&<109/50&<5/16\\
(21/10,1)&<11/20&<211/100&<1/5.
\end{array}
\tag{SW.11}
\]

For the first time bound,
\(2(2191/1000)(23/50)-(23/50)^2>9/5\); its squared energy is
\((2191/1000)^2-9/100+1/30<(109/50)^2\).
For the second time bound,
\(2(21/10)(11/20)-(11/20)^2>2\). The duration comparisons are
\(43/25<(21/16)^2\) and \(36/25=(6/5)^2\), respectively.

Consequently every possible reflected excess ends before

\[
\max\{71/100,\ 23/50+5/16,\ 11/20+1/5\}
=\frac{309}{400}<\frac{31}{40}.
\tag{SW.12}
\]

## 4. The companion prefix

The elementary lower bound
\(\cos x\ge1-x^2/2+x^4/25\) for \(0\le x\le1\) gives
\(\cos(31/40)>7/10\). Hence
\(\arccos C>31/40\), and SW.12 implies

\[
\boxed{v(t)\le1\quad\text{for almost every }
0<t<\arcsin C.}
\tag{SW.13}
\]

In particular this bounds the shorter prefix
\(0<t<\arcsin(C-T_L)\) required by the weighted terminal-exposure
comparison. The theorem covers positive, horizontal and the remaining
negative middle for every angle in SW.1. The use of that weighted
comparison to exclude the cap is a separate stated implication; no
unproved all-angle unit bound is part of SW.13.
