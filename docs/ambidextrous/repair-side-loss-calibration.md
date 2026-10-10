# A sharp corrected bound that also pays for side-only repair mass

The corrected calibration AC1 includes adverse corner-contact work. Side-only repairs have a different quadratic mass term. This note includes that term too, and proves the same sharp bound over the entire possible width range of a competitive body, using DU1.

This remains a theorem about an explicit auxiliary functional. It supplies an exact sufficient geometric budget; it does not claim that all ordinary-area changes fit that budget. The labels AS are local to this supplement.

## 1. The larger correction

Use the notation and function space of AC1, but restrict the centered half-width to

\[
1\leq a\leq2.
\]

For each of the two halves, u,v are independent nonnegative H^1_0(0,L) functions, L=pi/2. Put

\[
\begin{aligned}
\mathcal J_{\rm side}(h;\mathbf u)
={}&\widetilde{\mathcal Q}(h)
-\sum\int[(1-q_+)u+(1+p_-)v]\\
&-\sum B_+(u,v)+\frac12\sum\int(u^2+v^2),
\end{aligned}
\tag{AS.1}
\]

where p_-=min(p,0), q_+=max(q,0), and

\[
B_+(u,v)=\tfrac12\int(u'^2+v'^2+uv'-vu').
\]

The sums range over the two reflected upper-half descriptions, with their own independent increments. No symmetry, curvature or contact-sign hypothesis is imposed on h.

**Theorem AS1 (corrected sharp bound on widths two to four).**

\[
\boxed{\mathcal J_{\rm side}(h;\mathbf u)\leq M.}
\tag{AS.2}
\]

Equality holds exactly for the candidate profile up to horizontal translation and all increments identically zero.

Since J_side>=J, this is stronger than AC1 on the indicated width interval. By DU1 and AW-W, every global maximizer has width strictly inside this interval in an incoming unit-span normalization. No candidate-neighborhood assumption is being made.

## 2. The fixed-width estimate with the extra mass

Repeat the exact Bregman-square completion AC.3--AC.6. The additional half-mass in (AS.1) changes the remaining energy to

\[
B_+(u,v)-\int(u^2+v^2)
=\tfrac12\int\left(|y'|^2-\tfrac94|y|^2\right)
\geq\tfrac7{32}\int|y'|^2,
\tag{AS.3}
\]

where y=e^{it/2}(u+iv). The original fixed-width profile energy is nonnegative and can be dropped for this estimate. Write b(a) for the largest positive excess of either reference velocity beyond one as in AC.6. The torsion estimate there gives

\[
\int(u+v)\leq\sqrt{L^3/6}\,\|y'\|_2.
\]

Completing a scalar square, and adding the two halves, yields

\[
\boxed{\mathcal J_{\rm side}(h;\mathbf u)
\leq\Phi(a)+\frac{\pi^3}{21}b(a)^2.}
\tag{AS.4}
\]

All factors are explicit: the one-half maximal credit is 4L^3 b^2/21, and there are two halves. The elementary bound pi<22/7 gives pi^3/21<3/2.

AC.9 established b(a)<=(3a/2-2)_+ from the exact fixed-width optimizers. Thus the correction vanishes for 1<=a<=4/3. For larger widths it is enough to control

\[
G(a)=\Phi(a)+\tfrac32(3a/2-2)^2.
\tag{AS.5}
\]

## 3. An exact scalar bound, not a sampled width search

Put tau=tan(pi/8)=sqrt(2)-1. On the three-phase family SW1,

\[
-\Phi''(a)=12\frac{c-\tfrac12Cs}{2s+cC}\leq12\tau<6.
\tag{AS.6}
\]

Here s=sin(beta), c=cos(beta), C=cot(beta/2+pi/8). For a direct proof of the inequality, put z=tan(beta/2) and y=tan(beta). Then C=(1-tau z)/(tau+z). The required inequality is

\[
1-\tau C\leq(\tfrac12C+2\tau)y.
\]

After substitution and multiplication by the positive denominator (tau+z)(1-z^2), the right side minus the left side is

\[
z\,[3\tau^2+3\tau z+(1+\tau^2)z^2]\geq0.
\]

On the all-contact tail, AF gives -Phi''=12tau exactly. The first derivatives match where the two explicit families join. Therefore G is convex throughout [4/3,2]: almost everywhere

\[
G''=\Phi''+27/4>3/4.
\tag{AS.7}
\]

Its maximum on this compact interval occurs at an endpoint. At a=4/3 it equals Phi(4/3)<M by AF3, since the unique maximizing half-width a_* is strictly below 4/3.

The other endpoint has a simple exact value. The all-contact half optimizer has

\[
f=R\cos(t/2+\pi/8)+B\sin t,\quad
 g=R\sin(t/2+\pi/8)+B\cos t,
\]

where R=a/cos(pi/8), B=1-a tau. The all-contact integrand is

\[
\tfrac12[f^2+g^2-2f'^2-2g'^2-fg'+gf'+g'-f'].
\]

The quadratic part simplifies to (9/4)RB sin(3t/2+pi/8), whose integral is 3aB. The linear part integrates to a-1. Hence

\[
\Phi(a)=2(3aB+a-1)-2a=-6\tau a^2+6a-2
\tag{AS.8}
\]

on this tail. It includes a=2, since 2/(3tau)<2. Consequently

\[
G(2)=\frac{71}{2}-24\sqrt2<\frac85<M.
\tag{AS.9}
\]

The strict radical comparison follows from sqrt(2)>113/80, whose square is checked by 12800>12769. We conclude that G(a)<M on [4/3,2]. This is an analytic proof for the entire width interval, not a finite list of sampled values.

## 4. Finish the theorem and its equality case

For a<=4/3, b(a)=0 and (AS.4) gives J_side<=Phi(a)<=M. For a>=4/3, (AS.4)--(AS.9) give J_side<M. Equality can therefore occur only at a=a_*.

At that width the two reference coefficients 1-(q_a)_+ and 1+(p_a)_- are uniformly positive. Retaining them in the Bregman completion and using the strictly positive energy in (AS.3), equality forces all increments to vanish. Fixed-width strict concavity then identifies both halves with the candidate, up to the previously removed horizontal translation. The converse follows from the candidate value. This proves AS1.

## 5. What geometric inequality would now suffice

Let S be an arbitrary potentially maximizing body, with W>2 from AW-W and W<4 from DU1. Let bar h be a normalized proposed repaired profile of the same width, with nonnegative quarter increments u,v. It is sufficient to prove

\[
\begin{aligned}
|S|\leq\widetilde{\mathcal Q}(\bar h)
-\sum\int[(1-\bar q_+)u+(1+\bar p_-)v]
-\sum B_+(u,v)
+\tfrac12\sum\int(u^2+v^2).
\end{aligned}
\tag{AS.10}
\]

Then AS1 supplies |S|<=M, and equality forces both zero repair and the candidate profile. Exact equality of the original body still uses containment in the resulting candidate envelope and regular-closed recovery, rather than hull equality alone.

For the already proved standard-corner accounting RC1, (AS.10) follows from AC.12 because the additional mass is nonnegative. For a side-only one-wall increment with no niche change, the exact hull gain is integral u plus one half of integral (u'^2-u^2), precisely the type of mass term allowed in AS.10. These checks explain the enlargement; they do not prove the formula for arbitrary simultaneous, topology-changing repairs.

The global operator GM2 supplies bar h and increments for every convex input. What remains unproved is (AS.10) for its actual ordinary-area geometry, including partial endpoints, clipping and changes of contact orientation or component. AS1 solves the enlarged **analytic** budget without assuming those geometric facts. No unrestricted completion is claimed.
