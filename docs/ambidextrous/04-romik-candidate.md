# 4. Exact candidate constants and a strict separation certificate

**Scope.** This note proves an analytic property of Romik's specified candidate path, not a property of all ambidextrous sofas. In particular it proves that the midline partition majorant of Note 3 is tight at that path and in a neighborhood of it.

**External input.** Use the path and constants in Romik, *Differential equations and exact solutions in the moving sofa problem*, [arXiv:1606.08111v3](https://arxiv.org/html/1606.08111v3), Theorems 3–5, specifically (SOL1), (SOL6), (SOL5), and equations (61)–(67), (69). Feasibility of his full body and the area formula are cited inputs, not re-proved here. We use only the displayed vertical coordinates and their matching. No global or local maximality assumption enters the calculations below.

## 4.1 One algebraic parameter suffices for the benchmark area

Let Y be the positive solution of

\[
4Y^3+3Y-1=0,\qquad \beta=\arctan Y,
\qquad s=\sin\beta,\quad c=\cos\beta.
\tag{4.1}
\]

**Lemma 12 (root isolation and the area parameter).** Y exists uniquely, and

\[
2-\sqrt3<Y<\tfrac13,\qquad
\frac\pi{12}<\beta<\arctan(1/3)<\frac\pi4.
\tag{4.2}
\]

The unique positive solution X of \(X^2(X+3)=8\) is

\[
X=1+4Y^2.
\tag{4.3}
\]

Thus Romik's benchmark area can be written as

\[
M=X+\beta=1+4Y^2+\arctan Y.
\tag{4.4}
\]

**Proof.** The polynomial p(y)=4y^3+3y-1 is strictly increasing on the real line, since p'(y)=12y^2+3>0. Also p(0)<0 and p(1/3)=4/27>0. At \(z=2-\sqrt3\),

\[
p(z)=109-63\sqrt3<0,
\]

because \(109^2=11881<11907=3\cdot63^2\). Hence \(z<Y<1/3\). The identity \(\tan(\pi/12)=2-\sqrt3\) gives (4.2).

Squaring \(4Y^3+3Y=1\) gives

\[
16Y^6+24Y^4+9Y^2=1.
\]

For \(X=1+4Y^2\), direct expansion yields

\[
X^2(X+3)
=4(1+4Y^2)^2(1+Y^2)
=4(1+9Y^2+24Y^4+16Y^6)=8.
\]

The function \(x^2(x+3)\) is strictly increasing for positive x and crosses 8, proving uniqueness. Equation (4.4) is then a reformulation of the cited area formula, not a new integration of the boundary. QED.

For a radicals check, take \(u=\sqrt[3]{\sqrt2+1}\), \(v=\sqrt[3]{\sqrt2-1}\). Then uv=1 and \(u^3-v^3=2\), so \(Y=(u-v)/2\) satisfies (4.1). Also \(u^2+v^2-1=1+4Y^2\). This recovers both radicals in the cited area expression without numerical root finding.

## 4.2 Vertical coordinates without the large radical constants

Let

\[
a=\frac1{4s},\qquad L=\frac\pi4-\beta,
\qquad R=\frac{c}{\cos(3L/2)}.
\tag{4.5}
\]

For Romik's specified path, the vertical coordinate q(t) is

\[
q(t)=
\begin{cases}
\tfrac12+a\sin(2t)-\sin t-\tfrac12\cos t,
       &0\leq t\leq\beta,\\[2pt]
\tfrac12+R\cos\bigl(\tfrac32(t-\pi/4)\bigr)
       -\sqrt2\cos(t-\pi/4),
       &\beta\leq t\leq\pi/2-\beta,\\[2pt]
q(\pi/2-t),&\pi/2-\beta\leq t\leq\pi/2,
\end{cases}
\tag{4.6}
\]

where the last line uses the first-phase formula at its reflected argument.

Here is the reduction from the cited path formulas. Multiplying (SOL1) by the rotation matrix with \(a_2=0\) and \(\kappa_{1,2}=1/2\) gives the first line directly. The vertical part of (SOL6) is

\[
\tfrac12+f_1\sin(3t/2)-f_2\cos(3t/2)-\sin t-\cos t.
\]

Since \(f_2=(1-\sqrt2)f_1\), its first two trigonometric terms equal
\(R\cos(3(t-\pi/4)/2)\), with \(R=f_1/\cos(\pi/8)>0\). The matching of the vertical coordinates at t=beta gives the simpler expression (4.5): the first line of (4.6) has value \(1/2-s\), while the middle line has value \(1/2+R\cos(3L/2)-s-c\). (SOL5), \(e_1=a\), \(e_2=0\), and \(\kappa_{5,2}=1/2\) give the reflected last phase. This calculation avoids needing a radical expression for f_1.

We have only rewritten the given path; this is not an independent verification of all its vector matching equations or its contact pattern.

## 4.3 An exact maximum for the corner height

**Theorem 13 (strict candidate ceiling).** For the path (4.6),

\[
\max_{0\leq t\leq\pi/2}q(t)
=q(\pi/4)=\tfrac12+R-\sqrt2<\tfrac12.
\tag{4.7}
\]

The maximum is attained only at t=pi/4.

**Proof, first phase.** Write \(z=\sin t\), so \(0\leq z\leq s\) and \(\cos t\geq c\). Then

\[
q(t)-\tfrac12
=\cos t\left(\frac{z}{2s}-\frac12\right)-z.
\]

The coefficient of cos(t) is nonpositive. Therefore

\[
q(t)-\tfrac12
\leq c\left(\frac{z}{2s}-\frac12\right)-z
=z\left(\frac{c}{2s}-1\right)-\frac c2
\leq-s,
\tag{4.8}
\]

where the final inequality uses \(c/(2s)=1/(2Y)>1\) and z<=s. Equality is attained at t=beta. Thus the first-phase maximum is \(1/2-s\); the last phase has the same maximum by reflection.

**Proof, middle phase.** By (4.2), \(0<L<\pi/6\), so

\[
\cos(3L/2)>1/\sqrt2,
\qquad R=\frac{c}{\cos(3L/2)}<\sqrt2.
\tag{4.9}
\]

Also

\[
R\geq c>\frac3{\sqrt{10}}>\frac{2\sqrt2}{3}.
\tag{4.10}
\]

The first strict inequality follows from \(\beta<\arctan(1/3)\); the second follows by squaring, since \(9/10>8/9\).

Set \(F(z)=R\cos(3z/2)-\sqrt2\cos z\). It is even. For \(0<z\leq L<\pi/6\), both z and 3z/2 lie in (0,pi/2), so \(\sin(3z/2)\geq\sin z>0\). Hence

\[
F'(z)=-\tfrac32R\sin(3z/2)+\sqrt2\sin z
\leq-(\tfrac32R-\sqrt2)\sin z<0.
\tag{4.11}
\]

Thus the middle-phase maximum is attained uniquely at its center and equals \(1/2+R-\sqrt2\). Its endpoint value agrees with the first-phase maximum, and is strictly smaller than its center value. This proves the global assertion and, using (4.9), the strict ceiling. QED.

## 4.4 Consequence for the two niches and the partition

Let

\[
\delta=\sqrt2-R>0,\qquad m=\tfrac12-\delta.
\]

In Romik's sofa-fixed quarter-turn frame the forbidden quadrants are
\(\mathbf{x}(t)-a\mu_t-b\nu_t\) with a,b>0. Lemma 8 and Theorem 13 imply

\[
W_-\subseteq\{y\leq\tfrac12-\delta\},\qquad
\rho W_-\subseteq\{y\geq\tfrac12+\delta\}.
\tag{4.12}
\]

Thus the candidate's two swept niches are disjoint with a vertical gap of width at least \(2\delta\). Intersecting with any common outer set K preserves the assertion. In particular, the exact midline majorant satisfies

\[
P_{h=1/2}(K,U,V)=|K\setminus(U\cup V)|
\tag{4.13}
\]

for these candidate witnesses. Independent perturbations of the two normalized paths whose vertical uniform errors are less than delta retain tightness, by the same ceiling argument.

This is a candidate-level certificate of **zero mask loss**. It does not prove the clipped-niche analytic estimates, a sharp global bound on P or Q, stationarity under every admissible perturbation, or uniqueness of the body among all competitors. In particular, uniqueness of the scalar root Y is not uniqueness of an optimal sofa.

No numerical experiments, CAS, Lean compilation, or CI are used in this proof. The candidate formulas and area remain explicitly attributed inputs; the height calculation is a pen-and-paper derivation from them.
