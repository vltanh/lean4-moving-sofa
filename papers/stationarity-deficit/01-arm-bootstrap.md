# 1. A maximum-deficit principle for the arm inequalities

This section is an independent real-analysis argument. It assumes the displayed integral inequalities, not maximality, symmetry, or the moving-sofa optimality theorem. It replaces the iteration in Baek, Section 6.5, once the geometric reduction has supplied those inequalities.

Put

\[
k(x)=\max\{|x-1|,(|x-1|+1)/2\},\qquad m(x)=x-k(x),\quad x\ge0.
\]

Directly from the definition,

\[
m(x)=\begin{cases}3x/2-1&0\le x\le1,\\x/2&1\le x\le2,\\1&x\ge2,\end{cases}
\qquad
m(x)\ge\tfrac12-\tfrac32(1-x)_+ .                 \tag{1.1}
\]

## Theorem 1.1 (one-step bootstrap)

Let \(0<L<5/3\). Suppose \(f,g:[0,L]\to[0,\infty)\) are continuous and

\[
f(t)\ge1+\int_0^t m(g(s))\,ds,\qquad
 g(t)\ge1+\int_t^L m(f(s))\,ds.                 \tag{1.2}
\]

Then, for every \(t\in[0,L]\),

\[
 f(t)\ge1+t/2,\qquad g(t)\ge1+(L-t)/2.        \tag{1.3}
\]

**Proof.** Set \(p=(1-f)_+\), \(q=(1-g)_+\), and let \(H\) be the maximum of both functions over the interval. Nonnegativity of \(f,g\) gives \(0\le H\le1\).

If \(H\le1/3\), (1.1) gives \(m(f),m(g)\ge0\), so (1.2) implies \(f,g\ge1\). Hence \(H=0\).

It remains to exclude \(H>1/3\). Put \(b=(3H-1)/2>0\). Since \(m(f),m(g)\ge-b\),

\[
p(t)\le\min\{H,bt\},\qquad q(t)\le\min\{H,b(L-t)\}.
\]

At a point where either deficit attains \(H\), use the corresponding inequality in (1.2), then (1.1). Reflect the integration variable for the \(p\)-case. Enlarging the interval and taking a positive part gives

\[
H\le I_L(H):=\int_0^L\left[\tfrac32\min\{H,br\}-\tfrac12\right]_+dr.       \tag{1.4}
\]

The integrand is zero until \(r=1/(3b)\), then rises linearly to \(b\) at \(r=H/b\), and thereafter equals \(b\). The rising interval has length

\[
(H-1/3)/b=2/3.
\]

Its triangular area is \(b/3\). If \(L\le H/b\), therefore,

\[
I_L(H)\le b/3=(3H-1)/6<H.
\]

If \(L>H/b\), then

\[
I_L(H)=b(L+1/3)-H<2b-H=2H-1\le H,
\]

where the strict inequality uses \(L<5/3\). Both cases contradict (1.4). Thus \(H=0\). Finally \(m(x)\ge1/2\) for \(x\ge1\), so substitution in (1.2) proves (1.3). \(\square\)

The proof does not assume \(g(t)=f(L-t)\). Reflection is only a change of integration variable. The number \(5/3\) comes from the explicitly evaluated triangular envelope, not an empirical iteration count. The moving-sofa interval qualifies because \(\pi/2<11/7<5/3\).

## Theorem 1.2 (uniform additive errors)

Let \(0<L<5/3\), set

\[
c_L=\min\{1/3,5/3-L\},
\]

and suppose \(\varepsilon\ge0\) satisfies

\[
 (1+3L/2)\varepsilon<c_L.                         \tag{1.5}
\]

Replace (1.2) by

\[
f(t)\ge1-\varepsilon+\int_0^t m(g(s))ds,
\quad
g(t)\ge1-\varepsilon+\int_t^L m(f(s))ds.           \tag{1.6}
\]

Then

\[
\max\{(1-f(t))_+,(1-g(t))_+\}\le\varepsilon,
\]

and

\[
 f(t)\ge1-\varepsilon+(1/2-3\varepsilon/2)t,
\quad g(t)\ge1-\varepsilon+(1/2-3\varepsilon/2)(L-t).       \tag{1.7}
\]

**Proof.** Use the same \(p,q,H\). If \(H\le1/3\), (1.1) and (1.6) immediately give \(H\le\varepsilon\). If \(H>1/3\), put \(b=(3H-1)/2\). Now

\[
p(t)\le\min\{H,\varepsilon+bt\},\qquad
q(t)\le\min\{H,\varepsilon+b(L-t)\}.
\]

The maps \(x\mapsto\min(H,x)\) and \(x\mapsto x_+\) are 1-Lipschitz. Repeating (1.4) gives

\[
H\le I_L(H)+(1+3L/2)\varepsilon.                  \tag{1.8}
\]

For \(L\le H/b\), the preceding computation gives

\[
H-I_L(H)\ge H-b/3=H/2+1/6>1/3.
\]

For \(L>H/b\),

\[
H-I_L(H)=\tfrac32(1-L)H+L/2+1/6.
\]

When \(L\ge1\), its minimum on \(H\in[1/3,1]\) is \(5/3-L\); when \(L\le1\), its minimum is \(2/3\). Thus \(H-I_L(H)\ge c_L\) in all cases. Equations (1.5) and (1.8) contradict this. Hence \(H\le\varepsilon\), and (1.1) gives \(m(f),m(g)\ge1/2-3\varepsilon/2\). Substitute in (1.6). \(\square\)

At \(L=\pi/2\), the sufficient condition is

\[
\varepsilon<\frac{5/3-\pi/2}{1+3\pi/4}.
\]

No optimality of this error threshold is asserted. The result gives uniform deficit control; it does not give strict positivity at an endpoint in the presence of error.

## Negative result 1.3 (the length restriction cannot simply be removed)

On \(0\le t\le L_0:=5\pi/9\), define

\[
f(t)=\tfrac23\left(1+\cos(3t/2+\pi/3)\right),\qquad
g(t)=\tfrac23\left(1-\sin(3t/2+\pi/3)\right).
\]

The phase ranges from \(\pi/3\) to \(7\pi/6\), so both functions lie in \([0,1]\). They satisfy \(f(0)=g(L_0)=1\) and

\[
f'=\tfrac32g-1=m(g),\qquad g'=-\bigl(\tfrac32f-1\bigr)=-m(f).
\]

Consequently (1.2) holds with equality. But \(g(\pi/9)=0\) and \(f(4\pi/9)=0\). Thus an assertion of Theorem 1.1 for all \(L\) is false. This example does not show that \(5/3\) is sharp, and it is not a moving-sofa construction.

## Application boundary

The geometric input still needed is the derivation of (1.2) for the appropriate cap arms, including absolute continuity and the endpoint values. This section replaces the scalar bootstrap only; it does not obtain curvature bounds from maximality or prove feasibility of a cap-minus-niche set.

Source for the original arm inequality and iteration: J. Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826v1, Sections 6.4-6.5. The proofs above are written out independently and do not invoke any finite numerical certificate.
