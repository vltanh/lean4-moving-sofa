# Qualitative stability for arbitrary moving sofas

**Status:** written proof using the paper's optimality, uniqueness and supporting-hallway results. Not Lean-checked or independently reviewed. No injectivity assumption is made in this theorem. No explicit power-law rate is asserted.

Let M=|G| and

    d_rig(S,G) = inf_{theta,a} d_H(S, R_theta G+a).

## Theorem

For every eta>0 there is epsilon>0 such that every moving sofa S with |S|>=M-epsilon satisfies d_rig(S,G)<eta. Equivalently, if |S_n| tends to M, then d_rig(S_n,G) tends to zero. After suitable rigid motions, convergence also holds in symmetric-difference area.

This is the global, qualitative version of stability. The explicit square-root cap theorem in `01-cap-coercivity.md` is stronger in rate but narrower in class; the two conclusions must not be conflated.

## 1. A connected sofa has a bounded supporting-corner height

Suppose S is a nonempty compact connected subset of the strip H=R x [0,1], and S is contained in its supporting hallway L_S(t) for 0<t<pi/2. Write x=x_S(t) for the inner corner and

    a(p)=(p-x).u_t,   b(p)=(p-x).v_t.

On S, a<=1, b<=1 and max(a,b)>=0. Both upper values 1 are attained because the outer walls are supporting lines of the compact set S.

If x_y>1, then a(p)sin(t)+b(p)cos(t)=p_y-x_y<0 throughout S. The two closed sets

    {p in S:a(p)>=0},   {p in S:b(p)>=0}

cover S and are disjoint. They are both nonempty: a point attaining a=1 has b<0, and a point attaining b=1 has a<0. This contradicts connectedness. Therefore x_S(t)_y<=1.

This argument applies to S itself. No balancedness, cap regularity, area continuity, or maximality is used.

## 2. Uniform boundedness of large sofas modulo translation

The paper's Fact `fact:angle` supplies, for every moving sofa with area at least 11/5, a rotation angle

    omega in [omega0,pi/2],   omega0=arccos(5/11)>pi/4,

and a translation into standard position. Such a sofa is in H and in L_S(t) for every 0<=t<=omega; see the supporting-hallway paragraph of Section 2 (Baek's Theorem 2.3.2). In particular t=pi/4 is available.

Put h1=h_S(pi/4), h2=h_S(3pi/4). The previous lemma gives

    (h1+h2-2)/sqrt(2) = x_S(pi/4)_y <= 1.

The two outer walls and y>=0 give, for p in S,

    -sqrt(2)h2 <= p_x <= sqrt(2)h1.

The length of this containing interval is at most 2+2sqrt(2). Translate its midpoint to zero. Every large sofa therefore has a horizontal translate in the fixed compact rectangle

    B=[-(1+sqrt(2)),1+sqrt(2)] x [0,1].

This last translation retains h_S(pi/2)=1, the strip condition, the supporting-hallway containments, and the endpoint width condition

    h_S(omega)+h_S(omega+pi)<=1.                       (1)

It need not retain h_S(omega)=1; that equality will not be assumed below.

## 3. The relevant class is closed under Hausdorff limits

Let nonempty compact connected S_n in B converge in Hausdorff distance to S, let omega_n tend to omega in [omega0,pi/2], and assume the strip/top normalization, (1), and S_n subset L_{S_n}(t) for every t in [0,omega_n]. Then S is compact, nonempty, and connected. The last assertion follows, for example, because a separation of S into two nonempty compact pieces at positive distance would separate S_n into two disjoint neighborhoods for large n.

For compact sets, convex or not,

    |h_{S_n}(t)-h_S(t)| <= d_H(S_n,S)

uniformly in t. Supports are also uniformly Lipschitz in t, since all sets lie in B. Thus the top normalization and (1) pass to the limit, including the changing direction omega_n.

Fix s in [0,1], set t_n=s omega_n and t=s omega, and take p_n in S_n tending to any p in S. In the two wall-frame coordinates relative to x_{S_n}(t_n), the closed conditions for hallway membership are

    a_n<=1,   b_n<=1,   max(a_n,b_n)>=0.

Uniform convergence of the supports and t_n->t allow all three inequalities to pass to the limit. Consequently S subset L_S(t) for every t in [0,omega]. The use of max is important: no strict forbidden-wedge inequality is passed through a limit.

Now construct, rather than assume, a motion of the limiting sofa:

    Phi_s(p)=R_{-s omega}(p-x_S(s omega)),   0<=s<=1.

The corner x_S(t) is continuous, so this is a continuous rigid motion, starting at a translation. At s=0, h_S(pi/2)=1 and S subset H imply Phi_0(S) subset H_L. At s=1, the first coordinate is

    p.u_omega-h_S(omega)+1 in [0,1]

by (1), while the second is at most 1 by its supporting-wall inequality. Thus Phi_1(S) subset V_L. At intermediate times Phi_s(S) subset L. The limit is a moving sofa.

This step avoids the false shortcut of assuming that arbitrary original motion paths have an equicontinuous convergent subsequence.

## 4. Compactness and upper semicontinuity of area

The nonempty compact subsets of the fixed compact rectangle B form a compact space for Hausdorff distance. This is the compact-hyperspace theorem, not just Blaschke's theorem for convex bodies. One elementary proof applies Arzela-Ascoli to the distance functions dist(.,S_n), which are uniformly bounded and 1-Lipschitz on B. The zero set of a uniform limit is nonempty and yields Hausdorff convergence along that subsequence. Connectedness is retained as in Section 3.

Area is upper semicontinuous on this hyperspace: for every delta>0, eventually S_n lies in the closed delta-neighborhood S_delta, so

    limsup |S_n| <= |S_delta|.

As delta decreases to zero, these finite-area neighborhoods decrease to S. Continuity from above of Lebesgue measure gives

    limsup |S_n| <= |S|.                               (2)

Area is NOT generally continuous on nonconvex compact sets, even connected ones: connected square-grid skeletons have area zero and converge in Hausdorff distance to a square of positive area. Only (2) is used.

## 5. Apply uniqueness to the limit

Suppose |S_n|->M but d_rig(S_n,G)>=eta for a fixed eta>0. For large n their areas exceed 11/5. Normalize them as in Section 2; translations do not change d_rig. Extract S_n->S in B and omega_n->omega. Section 3 makes S a moving sofa; (2) gives |S|>=M. Optimality gives the reverse inequality. The paper's uniqueness theorem therefore gives S=R_theta G+a for a fixed theta,a. But then

    d_rig(S_n,G) <= d_H(S_n,S) -> 0,

a contradiction. This proves the theorem.

For the symmetric-difference conclusion, choose rigid images of S_n converging to G. For every delta>0, eventually S_n subset G_delta, whence |S_n minus G|<=|G_delta minus G|->0 as delta decreases to zero. Moreover

    |G minus S_n| = M-|S_n|+|S_n minus G| ->0.

Thus |S_n symmetric_difference G|->0 as well. No unproved continuity of nonconvex area or of the niche map is used.

## What this does not prove

The argument yields a modulus tending to zero, not an effective epsilon(eta), and in particular does not establish d_rig(S,G)<=C sqrt(M-|S|). Uniform control of approximate maximality through the angle/injectivity reduction would still be needed for that claim. The earlier explicit cap estimate is not silently applied to the S_n here.

## Source dependencies

The paper branch at 51c9be18 contains all sofa-specific inputs: Section 2's `fact:angle`, its supporting-hallway construction, optimality, and `thm:main` in Section 9. The rest of the proof is elementary compactness and measure theory. The midpoint corner-height lemma is proved here for the original connected set rather than cited only for balanced maximum caps.
