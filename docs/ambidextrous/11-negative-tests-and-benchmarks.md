# 11. Negative tests and an exactly solved benchmark family

These are explicit obstructions, not merely cautions. They rule out two tempting shortcuts. Neither is a counterexample to optimality of Romik's sofa.

## 11.1 Signed corner area is not automatically removed area

Consider the closed disk S=K of radius 1/2 centered at (0,1/2). It is a connected ambidextrous body with full correctly signed quarter-turn witnesses: every directional width is one, so at any canonical placement the disk lies in each of the two unit strips and hence in the hallway. Thus both niches inside K are empty.

For the lower turn its canonical corner path is

\[
c(t)=\left(\frac{\sin t-\cos t}{2},\
\frac{1-\sin t-\cos t}{2}\right),\qquad0\leq t\leq\pi/2.
\tag{11.1}
\]

Define the signed corner-loop functional, closed along the baseline y=0, by

\[
I(c)=\frac12\int_0^{\pi/2}\det(c(t),c'(t))\,dt.
\]

The baseline contributes zero to the integral. Direct differentiation gives

\[
\det(c,c')=\frac12-\frac{\sin t+\cos t}{4},
\qquad I(c)=\frac\pi8-\frac14>0.
\tag{11.2}
\]

But \(|N_-|=0\). The reflected upper turn gives the same positive signed value when expressed in its lower-turn reflected coordinates. Consequently

\[
Q_0(K):=|K|-I_-(K)-I_+(K)=\frac12
<\frac\pi4=|S|.
\tag{11.3}
\]

**Conclusion.** The naive inequality \(|N_d|\geq I_d\), and hence the naive global majorant \(|S|\leq Q_0(K)\), is false even for a connected, convex, correctly rotating common-hull body. Here the corner loop lies below the strip and its signed area counts a region that is not a niche inside K.

This body is below the competitive threshold sqrt(2). The example does not rule out a theorem with an additional high-area or maximizing hypothesis; it proves that such a hypothesis and its consequences cannot simply be omitted. It also does not invalidate the purely algebraic concavity of Q_0, established separately in Note 12.

## 11.2 Reflected Hammersley witnesses: exact geometry

Use the standard semicircular corner paths

\[
c_r(t)=r(\cos2t-1,\sin2t),\qquad r\geq0,
\tag{11.4}
\]

and their reflections across y=1/2. This family is described in Romik, [Section 2, generalized Hammersley sofas](https://arxiv.org/html/1606.08111v3#S2). The calculations below are provided explicitly; no numerical optimization is used.

The lower outer support bounds are \(c_r\cdot\mu_t+1=1\) and \(c_r\cdot\nu_t+1=1+2r\sin t\). Thus its upper cap consists of two unit quarter-disks separated by a rectangle of width 2r. Intersecting this cap with its reflection gives a common outer set K_r with sections

\[
(K_r)_y=[-2r-m(y),m(y)],\quad0\leq y\leq1,
\]

\[
m(y)=\min\{\sqrt{1-y^2},\sqrt{1-(1-y)^2}\}.
\tag{11.5}
\]

Its area is

\[
|K_r|=C+2r,\qquad
C=4\int_0^{1/2}\sqrt{2y-y^2}\,dy
=\frac{2\pi}{3}-\frac{\sqrt3}{2}.
\tag{11.6}
\]

The lower forbidden sweep in y>=0 is the upper half-disk of radius r centered at (-r,0), with boundary conventions irrelevant to area. To see this directly, the two rays from c_r(t) along -mu_t and -nu_t meet y=0 at (-2r,0) and (0,0), respectively. The portion of that quadrant in y>=0 is the triangle under this common base and the apex c_r(t). Every such triangle lies in the half-disk by convexity; their union, as the apex runs along the semicircle, fills its interior. Reflection gives the upper niche. The parts inside the strip lie in the central rectangle of K_r.

These are legitimate simultaneous witness data. At r>1/2 their full envelope is disconnected, but its positive-area components remain legitimate connected bodies following both motions. These witnesses have not been tightened to the convex hull of one such component.

## 11.3 Exact partition value and the best connected member

For the midline partition functional of Note 3,

\[
P(r)=C+2r-4\int_0^{\min(r,1/2)}\sqrt{r^2-y^2}\,dy.
\tag{11.7}
\]

Hence

\[
P(r)=
\begin{cases}
C+2r-\pi r^2,&0\leq r\leq1/2,\\
C+2r-\sqrt{r^2-1/4}-2r^2\arcsin(1/(2r)),&r>1/2.
\end{cases}
\tag{11.8}
\]

In fact P(r) equals the total area of the full envelope for every r. A point of the lower disk above the midline is automatically in the upper disk: its distance to the reflected center is smaller. Thus the lower-exclusive niche lies below the midline, and the upper-exclusive niche lies above it. The exact mask loss (3.5) vanishes even when the disks overlap.

For r<=1/2 every section over the horizontal projection survives, and the envelope is connected by the vertical-section argument of Theorem 26. For r>1/2 the section at x=-r is empty, while both side lenses have positive area; therefore the envelope is disconnected.

On the connected range, completing the square gives

\[
P(r)=C+\frac1\pi-\pi(r-1/\pi)^2.
\tag{11.9}
\]

The unique maximizing parameter is r=1/pi, with value C+1/pi. The formula on r>1/2 is strictly decreasing, as shown below, so the same value is the maximum of the full-envelope relaxation over all r>=0.

This family cannot reach the Romik benchmark. Indeed, using the elementary bounds \(3<\pi<22/7\) and \(\sqrt3>12/7\),

\[
C+1/\pi<44/21-6/7+1/3=11/7<8/5<M,
\tag{11.10}
\]

where M>8/5 was proved in Note 10. This is an exact exclusion of the reflected-semicircular-path ansatz, not a numerical guess.

## 11.4 Genuine failure of concavity in a natural witness family

For r>1/2 put z=1/(2r). Differentiating (11.8) gives

\[
P'(r)=2-4r\arcsin z<0,
\]

because arcsin(z)>z for z in (0,1). A second differentiation gives

\[
P''(r)=4\left(\frac{z}{\sqrt{1-z^2}}-\arcsin z\right)>0.
\tag{11.11}
\]

The strict sign follows since the expression in parentheses vanishes at zero and has derivative \(z^2/(1-z^2)^{3/2}>0\).

Thus P is strictly **convex**, not concave, on this portion of the family. Both paths c_r depend affinely on r, and \(K_r=K_0+[-2r,0]e_x\) depends Minkowski-affinely on r. This is a concrete failure of concavity in natural geometric witness variables, even for symmetric witnesses.

The obstruction occurs where the full envelope has disconnected. It therefore does not disprove concavity on a smaller viable common-hull class from Theorem 30. It does rule out proving concavity of the raw partition functional on the entire initial witness relaxation without further qualifications.

## 11.5 What survives these tests

- The common-hull/sign/separation reduction is unaffected.
- A signed corner functional needs a correct geometric bridge; algebraic concavity alone is not that bridge.
- A corrected quadratic majorant may still be useful even though the exact raw area is not concave on a larger relaxation.
- The reflected Hammersley family provides a fully solved analytic benchmark for future candidate bounds and equality calculations.

All results above are pen-and-paper calculations. The elementary ansatz and counterexamples carry no novelty claim.
