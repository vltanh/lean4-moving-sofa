# 19. The fixed-switch majorant fails for feasible bodies arbitrarily near the candidate

The disk in Note 14 showed that the fixed-contact quadratic is not an area upper bound for all bodies. One could still hope that an area threshold or a small neighborhood of Romik's candidate would repair that comparison. This note disproves that hope by realizing the perturbation in Note 16 as an actual connected ambidextrous sofa.

This is a negative result about a proposed **proof route**, not about optimality of Romik's sofa. Every body constructed below has area strictly smaller than M.

## 19.1 A horizontal-segment summand can be removed

For sufficiently small epsilon>0 set

\[
h_\varepsilon(\theta)=h_*(\theta)-\varepsilon|\cos\theta|.
\tag{19.1}
\]

On each open quarter the subtracted function solves delta''+delta=0, so the curvature densities of h_epsilon agree with those of h_*. The derivative jumps at the two vertical normals each decrease by 2epsilon. They remain positive when epsilon<2A/3. Lemma 43 therefore gives a compact convex body K_epsilon with support h_epsilon.

Equivalently, K_* is the Minkowski sum of K_epsilon and the horizontal segment [-epsilon,epsilon]e_x. This statement follows from addition of support functions; no set subtraction preserving convexity is assumed without the curvature check.

The top and bottom faces of K_epsilon are aligned on

\[
[\ell_\varepsilon,r_\varepsilon]
=[\ell_*+\varepsilon,r_*-\varepsilon].
\tag{19.2}
\]

Its vertical span is still one. The curvature bounds in (18.1) are unchanged, and the monotone-velocity conditions hold for all sufficiently small positive epsilon by the explicit check in (16.7). The zero a_epsilon of p_epsilon lies strictly after beta, while the zero b_epsilon of q_epsilon lies strictly before b=L-beta; these remain ordered.

## 19.2 The entire perturbed niche still lies below the midline

Let c_epsilon,B_epsilon,D_epsilon be the three paths of (17.2). Direct substitution yields

\[
c_\varepsilon(t)=c_*(t)-\varepsilon(\cos2t,\sin2t),
\]

\[
B_\varepsilon(t)=B_*(t)-\varepsilon e_x,
\qquad D_\varepsilon(t)=D_*(t)+\varepsilon e_x.
\tag{19.3}
\]

On the new middle phase [a_epsilon,b_epsilon], sin(2t)>=0, so c_epsilon,y<=c_*,y<=m<1/2. On the new B phase [a_epsilon,L], the height equals B_*,y and is at most B_*,y(beta), because a_epsilon>beta and B_*,y decreases. On the D phase [0,b_epsilon], its height equals D_*,y and is at most D_*,y(b), because b_epsilon<b and D_*,y increases.

Theorem 41 therefore gives a perturbed profile F_epsilon satisfying

\[
0\leq F_\varepsilon(x)\leq m<1/2,
\tag{19.4}
\]

supported on the face interval (19.2). Its reflected upper profile is strictly separated. Both lie in the central rectangle contained in K_epsilon.

Define S_epsilon by removing the two open canonical sweeps from K_epsilon. As in Section 18.3, the continuous central vertical sections have positive length, the flanks are unchanged, and the face endpoints survive. Thus S_epsilon is compact, connected, feasible for both full quarter turns, and has convex hull K_epsilon. It belongs to the class R in Theorem 44.

## 19.3 A strict inequality in the wrong direction

There is no clipping for this family, so the exact area is

\[
|S_\varepsilon|=\widetilde{\mathcal Q}(h_\varepsilon).
\]

Using (16.8),

\[
\boxed{
|S_\varepsilon|-\mathcal Q_{\beta,L-\beta}(h_\varepsilon)
=\int_\beta^{a_\varepsilon}p_\varepsilon(t)^2\,dt
+\int_{b_\varepsilon}^{L-\beta}q_\varepsilon(t)^2\,dt>0.
}
\tag{19.5}
\]

Both intervals have positive length. The integrands are nonzero in their interiors, because the velocity components strictly decrease to their unique zeros.

At the same time Theorem 40 gives

\[
|S_\varepsilon|<M,
\]

since h_epsilon-h_*=-epsilon|cos(theta)| is not a single horizontal-translation mode. The adaptive functional is continuous in these explicit functions and their first derivatives on each quarter, so |S_epsilon| tends to M as epsilon decreases to zero. In particular the counterexamples have area greater than sqrt(2), or greater than any fixed threshold strictly below M, for sufficiently small epsilon.

## 19.4 Size of the failure

There is an exact useful comparison with the quadratic deficit. For delta=-epsilon|cos(theta)|, the factorization (13.10) gives

\[
M-\mathcal Q_{\beta,L-\beta}(h_\varepsilon)
=2\varepsilon^2\left(L-2\beta+\sin2\beta\right).
\tag{19.6}
\]

To check it, on the upper quarters f=-epsilon cos(t), g=-epsilon sin(t), hence X=Y=0, P=2epsilon sin(t), and the boundary square supplies the remaining endpoint term. The reflected half is identical.

The positive switch correction in (19.5) is of order epsilon cubed: the two switch displacements are O(epsilon), since the candidate derivatives at their zeros are nonzero, and p_epsilon,q_epsilon are O(epsilon) on those intervals. This order statement follows from the mean value theorem and uniform derivative bounds near the two switches. No asymptotic expansion is needed to establish the strict counterexample.

Thus the wrong fixed-switch inequality can fail by a small cubic amount while the candidate remains quadratically optimal. Numerical proximity to the candidate, or a correct Hessian at the candidate, would not detect the missing geometric inequality by itself.

## 19.5 Consequences for the proof program

- The fixed quadratic in Theorem 37 has the right sharp constant and equality kernel, but cannot be the direct area majorant even in a high-area neighborhood of the candidate.
- Replacing fixed switches by the sign-selected adaptive functional is necessary for this route; it repairs the comparison on R and retains exact concavity and rigidity on C.
- The remaining obstacle is not moving contacts alone. The positive rim-clipping corrections in (17.11), partial endpoint angles, and the unproved general regularity/velocity reductions still require separate arguments.

This counterexample and its positive replacement are both committed so that the failed fixed-switch route is not inadvertently reused as an unrestricted optimality proof.
