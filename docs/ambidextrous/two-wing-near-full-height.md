# Cut slack with unequal wing heights near the full strip

This closes another explicit subcase of roadmap gate R4. The full-height theorem SQ1 is not needed if the two wings share a common bottom and their top deficits are sufficiently small. The threshold is elementary:

\[
\boxed{1-H_R,\ 1-H_D\leq \frac{\sin\beta}{2}.}
\]

Here \(H_R,H_D\) are the two vertical spans after translating their common bottom to zero, and \(\beta\) is Romik's reference angle. Arbitrary cut-width slack is allowed. No curvature upper bound or reflection symmetry is assumed.

This result is designed for the canonical lower safe wings, which naturally share the incoming baseline. It does **not** prove that every maximizing sofa supplies wings satisfying the displayed height threshold. That is now a concrete R3/R5 geometric obligation rather than an unquantified algebraic one.

Use the actual-intersection functional \(\widehat{\mathcal W}\) and cut slacks of CS/SQ. Put

\[
y=\tan\beta,\qquad k=\sin2\beta=\frac{2y}{1+y^2},
\]
\[
s_R=(r_++r_-)/2,\quad e_R=(r_+-r_-)/2,\qquad
s_D=(d_++d_-)/2,\quad e_D=(d_+-d_-)/2.
\]

All four original slacks are nonnegative, hence
\[
0\le s_R,s_D\le1,\qquad |e_R|\le s_R,\quad |e_D|\le s_D.
\tag{NH.1}
\]

## 1. Normalize the two unequal heights

Assume the two completed wings lie in one strip of height one and share their lower supporting line. Translate their common bottom to height zero and, after exchanging the wing labels if necessary, write

\[
H_R=1-a_R,\qquad H_D=1-a_D,\qquad
0\le a_R\le a_D.
\]

Translate both auxiliary bodies upward by \(a_R\). The functional is invariant under this common translation. In the notation of WS.7 the three nonnegative vertical trace parameters become

\[
B_0=C_0=T:=\frac{a_R}{\cos\beta},
\qquad
A:=\frac{a_D-a_R}{\cos\beta}.
\tag{NH.2}
\]

Thus
\[
A+T=\frac{a_D}{\cos\beta}.
\tag{NH.3}
\]

The height hypothesis \(a_D\le\sin\beta/2\) is exactly

\[
\boxed{A+T\le y/2.}
\tag{NH.4}
\]

This normalization is only a bookkeeping translation. It neither makes the original sofa symmetric nor changes the relative vertical placement of the wings.

## 2. The exact finite remainder with both kinds of slack

Repeat the core and arc minimizations WS.2--WS.9, but keep the four cut slacks from SQ.6. The three-variable Hessian is unchanged and positive definite. After minimizing over the core endpoints and over \(X,Z,z_0\), the finite quadratic remainder splits exactly as

\[
B_{\rm fin}=P_{\rm height}(A,T,T)+P_{\rm cut}(s_R,s_D,e_R,e_D)+C,
\tag{NH.5}
\]

where the height term is the WS.10 expression

\[
P_{\rm height}
=\frac{(A-T)^2+T^2}{8}
 +(k-\tfrac14)AT+(k-\tfrac34)T^2\ge0,
\tag{NH.6}
\]

the pure cut term is the SQ.9 expression

\[
\begin{aligned}
P_{\rm cut}={}&
\frac{y^2+2y+3/y}{8}(e_R+e_D)^2
+\frac{1+3/y}{8}(e_R-e_D)^2\\
&-\frac y4(s_R^2+s_D^2+2y s_Rs_D),
\end{aligned}
\tag{NH.7}
\]

and the mixed term is

\[
\boxed{
C=\frac14\Big[
A(y-1)(e_R+e_D+2s_R)-4A s_D
+2T(y-3)(s_R+s_D)
\Big].
}
\tag{NH.8}
\]

These are rational identities in \(y\). They come from the same explicit finite expression SQ.6 with the lower traces
\[
(U,V)=(-z_0,-A-z_0)
\]
and reflected traces
\[
(U^\rho,V^\rho)=(-T+z_0,-T+z_0).
\]
No small-height expansion is being used.

The accompanying exact checker reconstructs NH.5--NH.8 independently from SQ.6 and rejects sign mutations.

## 3. The first-order cut work absorbs the mixed term

The exact deficit contains the favorable first-order cut contribution
\[
y(s_R+s_D).
\]
SQ.10 and its proof give

\[
y(s_R+s_D)+P_{\rm cut}
\ge
\frac{y(3-y)}4(s_R+s_D)
+\frac{y^2+2y+3/y}{8}(e_R+e_D)^2
+\frac{1+3/y}{8}(e_R-e_D)^2.
\tag{NH.9}
\]

For the mixed term, NH.1 and \(0<y<1\) give
\[
e_R+e_D+2s_R\le3s_R+s_D.
\]
Therefore

\[
C\ge
-\frac{3A(1-y)}4s_R
-\frac{A(5-y)}4s_D
-\frac{T(3-y)}2(s_R+s_D).
\tag{NH.10}
\]

For the \(s_D\) coefficient, and hence also for the weaker \(s_R\) coefficient,

\[
\frac{A(5-y)}4+\frac{T(3-y)}2
\le \frac{(A+T)(3-y)}2
\le \frac{y(3-y)}4.
\tag{NH.11}
\]

The first inequality uses
\[
(3-y)/2-(5-y)/4=(1-y)/4>0.
\]
For \(s_R\), the corresponding comparison is even stronger because
\[
(3-y)/2-3(1-y)/4=(3+y)/4>0.
\]

Combining NH.9--NH.11 proves
\[
\boxed{y(s_R+s_D)+P_{\rm cut}+C\ge0.}
\tag{NH.12}
\]

The full interpolation residuals are nonnegative by WS/SQ, and the width-integral term from WC/CS is nonnegative. Adding NH.6 completes the sign.

## 4. The theorem and equality case

**Theorem NH1 (near-full-height arbitrary-slack calibration).** Let \(R,D\) be nonempty compact convex wings contained in one unit-height strip, sharing the same bottom supporting line. Assume the directional-width inequalities TW.1 and allow arbitrary nonnegative cut slacks CS.1. If, after translating the common bottom to zero,

\[
\min\{H_R,H_D\}\ge1-\frac{\sin\beta}{2},
\]

then

\[
\boxed{\widehat{\mathcal W}(R,D)\le M.}
\tag{NH.13}
\]

Equality holds exactly for the reference wing pair up to a common horizontal translation.

**Proof.** Complete the actual corners by CS1. Apply the exact quadratic expansion at the reference. The first variation is CS2. The width integral is nonnegative; NH.5--NH.12 make the remaining finite part nonnegative.

If equality holds, the height term NH.6 must vanish. The WS.11 equality analysis applied to \((A,B_0,C_0)=(A,T,T)\) gives \(T=0\) and then \(A=0\). Thus both wings have full height. The strict cut-slack term from SQ1 then forces \(s_R=s_D=0\), hence all four cut slacks vanish. The remaining interpolation residuals recover the reference supports modulo the common horizontal translation, exactly as in WC2/SQ1. Completion can have gained no area, so the original wings equal their completed reference copies. The converse is TW.6. QED.

The numerical value of the threshold is irrelevant to the proof; it is retained symbolically as \(\sin\beta/2\).

## 5. Consequence for the roadmap

R4 no longer needs a completely general unequal-height theorem if R3/R5 can prove that the canonical bottom-anchored wings of every relevant maximizer each have height at least \(1-\sin\beta/2\). That is a concrete geometric statement about actual safe pieces.

The theorem does not assert this height property. A body with a very short canonical wing remains outside NH1, and the free algebra really has negative directions there. Such directions are not automatically realizable by a high-area feasible sofa; the next task is to use the ordinary-area decomposition, connectedness and maximality rather than enlarging the algebraic domain without geometric control.

No CI or Lean/Lake compilation is used. The symbolic checks are exact finite-algebra diagnostics; geometric admission remains a written proof obligation.
