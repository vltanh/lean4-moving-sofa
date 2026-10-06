# Unrestricted square-root stability for moving sofas

**Status:** written continuous analytic proof, not Lean-checked or independently reviewed. The local nonsmooth certificate and terminal-strip lemma in notes 05--07 are new mathematical inputs. No assertion of Ki membership for arbitrary near-maximizers is made. This theorem completes the quantitative reduction left open in notes 01--03.

Write M=|G|, v=pi/2 and K0=K_G. Hausdorff distance between the actual compact sets, not merely their convex hulls, is used below.

## Theorem

There are constants C,C_area,epsilon0>0 depending only on Gerver's sofa such that every moving sofa S with

    epsilon=M-|S| in [0,epsilon0)

has a rigid image S_hat satisfying

    d_H(S_hat,G) <= C sqrt(epsilon),
    |S_hat symmetric_difference G| <= C_area sqrt(epsilon). (1)

In the manuscript's convention, where the initial motion is a translation into the horizontal hallway arm, a translation suffices. It can be fixed by the two support normalizations

    h_S_hat(v)=1,     h_S_hat(pi)=h_G(pi).                  (2)

For any of the rotation angles omega in [omega0,v] provided by the paper's angle reduction, one also has, for sufficiently small epsilon,

    0<=v-omega<=C_angle*epsilon.                            (3)

No smoothness, curvature-density, injectivity, or special-envelope hypothesis is imposed on S. The constants are uniform, but the entry threshold epsilon0 uses the compactness/uniqueness argument below and is not asserted to be an effectively computed number.

## 1. Qualitative entry in the correct frame

For every sufficiently large sofa, the source supplies omega in [omega0,v], with omega0>pi/4, supporting-hallway containments for 0<=t<=omega, and unit width in directions v and omega. Translate it to satisfy (2). These two independent coordinate directions make this normalization well-defined, with no division by cos(omega).

The corner-height argument in 02-global-qualitative.md bounds its horizontal span by 2+2sqrt(2). Pinning its leftmost coordinate by (2), rather than centering the containing interval, still puts all normalized sofas in a fixed compact rectangle. The top normalization and initial width put them in 0<=y<=1.

We claim that for every rho>0 there is epsilon_rho>0 such that every normalized pair (S_hat,omega) with |S_hat|>=M-epsilon_rho satisfies

    d_H(S_hat,G)<rho,       0<=v-omega<rho.                 (4)

Otherwise take a violating maximizing sequence. The compactness and closure proof in 02-global-qualitative.md gives a Hausdorff limit S_* and an angle limit omega_*, with S_* a moving sofa and |S_*|=M. The manuscript's Corollary `cor:translate` says that a maximal sofa in this orientation convention is a translate of G. The two normalizations (2) force that translate to be zero. The terminal width condition passes to the limit, so G has width at most 1 in direction omega_*. By the manuscript's Lemma `lem:gerver-width`, this forces omega_*=v. This contradicts the violation of (4).

This uses only qualitative entry into a fixed neighborhood. No quantitative conclusion is extracted from compactness, and no convergence of the original arbitrary motion paths is assumed.

## 2. A right-angle cap associated with the original sofa

Let K be the downward completion to y=0 of conv(S_hat). Equivalently,

    K={y>=0} intersect intersection_{0<=t<=pi} H_S_hat(t).

This is a normalized right-angle cap containing S_hat. Its upper support is exactly h_S_hat: lowering a point cannot increase a support with sin(t)>=0. Its lower support is determined by its two floor endpoints. Hence

    h_K(v)=1,  h_K(pi)=h_K0(pi),
    d_H(K,K0)<=d_H(S_hat,G).                                (5)

Here the downward completion of conv(G) is K0, as follows from Gerver's outer contacts and cap representation. The inequality follows directly from support functions on the upper semicircle and the endpoint formulas on the lower one.

The supporting hallways of K and S_hat agree for 0<=t<=omega, because both normals t and t+v lie in [0,pi]. The terminal strip condition is

    p.u_omega >= h_K(omega)-1 for p in S_hat.

Choose the qualitative neighborhood (4) small enough for both the local cap theorem (06) and terminal-angle proposition (07). Those results apply to K without asserting that it lies in Ki. With alpha=v-omega, U=K minus N(K), and delta=d_H(K,K0), they give

    c alpha<=epsilon,
    0<=M-A(K)<=epsilon,
    delta<=C_K sqrt(epsilon),      C_K=2sec(phi),
    |S_hat minus U|<=epsilon,
    |U minus S_hat|<=2epsilon.                              (6)

The pinned translation in the cap theorem is zero by (5). This establishes the cap rate and angle rate (3).

## 3. Directed distance from the original sofa to Gerver

Fix a uniform containing radius R for the cap neighborhood and put

    beta=delta+2R alpha.

The approximate full-angle hallway inequality (07, (7)) gives

    m_K0(t,p)>=-beta   for p in S_hat and 0<=t<=v.           (7)

Use the reference geometric margins proved in 03-nonconvex-recovery.md. A point p in S_hat outside K0 is within delta of G: a nearest point in K0 cannot belong to the niche rectangle, whose upper support gaps have a fixed positive minimum. This argument uses S_hat subset K, not full-angle movability of S_hat.

If p belongs to K0 minus G, let q=(p_x,gamma(p_x)) and d=q_y-p_y. At a core roof point q=x_G(t), both reference slacks decrease by at least d sin(phi) when moving vertically down. At a tail roof point, the active slack decreases by at least d cos(theta), while the inactive slack has a uniform strictly negative margin gamma_tail. Once beta<gamma_tail, (7) rules out d>beta/sin(phi). Thus

    sup_{p in S_hat} dist(p,G)<=beta/sin(phi).               (8)

Using (6), the right side is bounded by

    [C_K+2R sqrt(epsilon0)/c] csc(phi) sqrt(epsilon).        (9)

This is the point where treating S_hat as a subset of U would have been incorrect. The explicit 2R alpha allowance pays for its omitted final hallway constraints.

## 4. Directed distance from Gerver to the original sofa

Let kappa,r0>0 be the interior-ball constants proved in 03-nonconvex-recovery.md: every p in G and 0<rho<=r0 admit a ball of radius kappa*rho in G intersect B(p,rho). The same note proves, without a Ki hypothesis,

    G_{-r} subset U,             r=sqrt(2)delta,             (10)

where G_{-r}={p in G:dist(p,G complement)>=r}.

Choose epsilon0 small enough that r<=kappa*r0/2 and 2epsilon0<pi*kappa^2*r0^2/4. For p in G set d=dist(p,S_hat). If d<=4r/kappa, (6) already gives the square-root estimate. Otherwise take rho=min(d/2,r0). An interior ball of radius kappa*rho exists. Its concentric half-radius ball lies in G_{-r}, hence in U, whenever rho>=2r/kappa. It is disjoint from S_hat, since the entire original ball lies in B(p,rho) and rho<d. Therefore

    2epsilon >= |U minus S_hat|
                 >= pi*kappa^2*rho^2/4.                    (11)

If d>=2r0 then rho=r0, and the choice of epsilon0 contradicts (11). Otherwise rho=d/2; the case d>4r/kappa guarantees rho>2r/kappa, and (11) gives

    d<=4sqrt(2)/(kappa sqrt(pi)) sqrt(epsilon).

Together with the first case,

    sup_{p in G}dist(p,S_hat)
      <= max(4sqrt(2)C_K/kappa,
             4sqrt(2)/(kappa sqrt(pi))) sqrt(epsilon).      (12)

For epsilon=0 one can either use the exact uniqueness theorem or the same missing-area/interior-ball argument directly. Taking the maximum of the constants in (9) and (12) proves the Hausdorff estimate (1).

## 5. Symmetric-difference area

The preceding proof also supplies an area rate in the same alignment. Points of S_hat outside K0 occupy area at most

    perimeter(K0)*delta+pi*delta^2,

by K subset K0+delta*unit_disk and the planar convex parallel-body formula. Points of S_hat in the reference niche lie in a vertical band of thickness beta/sin(phi) below the roof, by the argument for (8), so they occupy area at most (b-a)beta/sin(phi). Hence

    |S_hat minus G|
      <= perimeter(K0)*delta+pi*delta^2+(b-a)beta/sin(phi).

Since |G|-|S_hat|=epsilon,

    |S_hat symmetric_difference G|=epsilon+2|S_hat minus G|.

Insert (6) and alpha<=epsilon/c. For epsilon<=epsilon0 this is at most C_area sqrt(epsilon), proving the second part of (1).

## Dependency audit

- Optimality and exact uniqueness: the existing paper, used for qualitative entry only.
- Canonical-hallway compactness: 02-global-qualitative.md, applied in a pinned frame; the paper's width lemma also locates the limiting angle.
- Algebraic nonsmooth deficit certificate: 05-nonsmooth-certificate.md; no competitor regularity is used.
- Local geometric area bound: 06-local-upper-bound.md; core derivative inequalities hold a.e. and tails use strict cut separation.
- Missing final angles: 07-terminal-angle-loss.md; the terminal strip removes more area than the omitted wedges can add.
- Nonconvex recovery: reference roof margins, erosion inclusion, and the explicit interior-ball proof in 03-nonconvex-recovery.md.

There is no quantitative selection argument hidden in the proof, no assumed smoothness of a near-maximizer, no assumed full-angle motion of S_hat, and no area-continuity assertion for arbitrary Hausdorff limits. The older conditional theorem remains valid, but its envelope hypothesis is no longer needed for (1).
