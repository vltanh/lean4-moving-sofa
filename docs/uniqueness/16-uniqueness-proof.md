# Gerver's sofa is the unique maximizing shape: paper proof

Date: 2026-10-02.

**Status.** This is the author's completed pen-and-paper argument. The new selection, variation, limit, and rigidity lemmas are proved in the linked notes; the earlier proposed extensions in notes 05–06 are no longer used as unproved inputs. This has not been independently reviewed and is not a Lean theorem. The earlier Lean/CI checks do not certify this manuscript.

## Theorem

Let G be Gerver's sofa in the unit right-angled hallway, with the definition used in this repository. Let S be a nonempty, closed, connected moving sofa. If its planar Lebesgue area is |G|, then there is a Euclidean isometry U such that

    U(S)=G.

The equality is an equality of actual sets, not just almost everywhere. The theorem does not assert uniqueness of the motion, nor restrict competing sofas to Gerver's or Romik's construction.

## Notation

Put L=pi/2, u_t=(cos t,sin t), v_t=(-sin t,cos t), and h_K(t)=max_{p in K} p.u_t for a compact convex body. A standard omega-cap has upper supports h_K(omega)=h_K(L)=1, lower supports h_K(omega+pi)=h_K(3L)=0, and the allowed defining normals of Baek's cap space. Let

    N_omega(K)=the fan intersected with the union of open inner quadrants,
    A_omega(K)=|K|-|N_omega(K)|.

This uses the fan correction recorded in the repository, not the erroneous bounded-parallelogram niche formula from the printed polygon definition.

## Previously established inputs

These are inputs from the existing optimality development, not new uniqueness assumptions.

1. **Optimality and area.** G is a moving sofa, |G|>2.2, and every moving sofa has area at most |G| (Theorem 1.1.1 and the Gerver area/structure results).
2. **Angles and monotonization.** A sofa of area at least 2.2 has an admissible angle omega in [arcsec(2.2),L]. After translation to standard position it is contained in its own monotonization, which is a moving sofa of that angle. For a monotone sofa M with its own cap K, M=K minus N_omega(K) and |M|=A_omega(K) (Theorem 1.5.1; Proposition 2.3.1; Theorems 2.3.2, 2.4.3, 2.5.10).
3. **Maximal cap values.** At every fixed omega, the maximum of A_omega is attained by a cap whose cap-minus-niche set is a moving sofa (Theorems 3.5.2–3.5.6). Consequently A_omega(K)<=|G| for every cap K. This conclusion does not assume that arbitrary caps give moving sofas.
4. **General finite-angle and convex geometry.** The completed inner polygonal boundary has the same endpoints as the upper cap boundary; its normal lengths are tau(t). The general outward assigned-height first variation is sigma(t)-tau(t). Supporting vertices, curvature measures, and arm lengths satisfy the general identities of Chapters 2, 3, 5 and 6. These formulas precede any use of balancedness. The pinned niche-variation sign is taken in its corrected form.
5. **The two fixed-angle scalar estimates.** The small comparison region in Lemma 4.2.2 has area below 2.2. With d_min as in §4.2, d_min<=d<=tan omega, r_y=1-d cot omega and g=sqrt(1-r_y^2), Lemma 4.2.4 gives d sin omega>1 and g>2 cos omega throughout omega in [arcsec(2.2),L), with the range correction in the repository.
6. **The upper-bound functional.** For every cap K in K^i, its canonical extension x=(K,B_K,D_K) lies in the convex domain L_script and

       A_L(K)<=Q(x)<=Q(x_G)=|G|.

   Along a convex segment the concavity gap of Q is the sum of the nonnegative convexity gaps of the four cap Mamikon terms and the two tail terms. These are the existing Chapter 8 results.
7. **Gerver's geometry.** The cap, contact curves, rotation path, and envelope satisfy the structure facts used explicitly in [note 07](07-regular-closedness.md). In particular the niche has the envelope description, the cap has its stated top edge, and the path height is at most one. These facts are already proved in the repository's Gerver modules.

The original numbered statements and their corrections are indexed by `REPORT.md` and `scripts/Audit.lean`. Nothing below assumes that an arbitrary maximizer is a balanced maximum cap.

## Lemma A. Selection of a specified maximizing cap

For a fixed cap maximizer K_*, there exist polygon caps K_n->K_* maximizing

    A_n(K)-lambda_n P(K),
    P(K)=integral_0^(L+omega) (h_K-h_{K_*})^2,

where lambda_n->0. Here A_n is the finite-angle upper approximation on a uniform dyadic mesh of spacing delta_n. At a right angle use a fixed box with K_* strictly inside its horizontal bounds; those artificial bounds are eventually inactive.

**Proof.** On the relevant compact cap family, [note 12](12-compact-selection-proof.md) proves uniform convergence A_n->A using explicit continuous wedge heights and the decreasing circumscribed caps. Write e_n=sup|A_n-A|. The recovery caps r_n=C_n(K_*) preserve every sampled support, converge to K_*, and satisfy A_n(r_n)>=A(K_*). Choose lambda_n with e_n/lambda_n->0. Comparing a penalized maximizer with r_n gives

    P(K_n)<=P(r_n)+e_n/lambda_n ->0.

The upper support data identify a standard cap, so the only zero of P is K_*. Compactness gives convergence of the entire sequence. The common interior ball for omega<L, and the fixed-mesh interior ball at omega=L, are proved in notes 12 and 15. QED.

## Lemma B. Every maximizing right-angle cap belongs to K^i

**Proof.** Apply Lemma A with omega=L. The exact sine-hat variation in [note 10](10-local-variation-audit.md), including redundant neighboring facets and the two end cells, gives

    sigma_n(t)<=tau_n(t)+C lambda_n delta_n

at each floating normal. No claim of exact balance is made.

The purely geometric inner-wall estimate, proved before imposing maximality in [note 13](13-every-right-angle-maximizer.md), is

    tau_n(t)<=tan(delta_n)(|g_n^+(t)-1|+tan(delta_n/2))
                 +(2tan(delta_n/2)-sigma_n(t))_+.

Solving this scalar inequality and using the uniform diameter bound gives

    sigma_n(t)<=delta_n k(g_n^+(t))
                  +C(delta_n^2+lambda_n delta_n),
    k(x)=max(|x-1|,(|x-1|+1)/2).

The total error tends to zero. Note 13 proves the weak limit by spreading atoms over adjacent mesh cells and testing across the end normal 0, not only away from it. Reflection handles pi. Thus the specified K_* satisfies

    sigma_{K_*}|[0,L)<=k(g(t))dt,
    sigma_{K_*}|(L,pi]<=k(f(t-L))dt.

These include absence of atoms at 0 and pi, but allow the top atom at L. The support/arm identities give nonnegative continuous arm functions, with f(0)=g(L)=1, satisfying

    f(t)>=1+integral_0^t m(g(s))ds,
    g(t)>=1+integral_t^L m(f(s))ds,   m(x)=x-k(x).

The entirely analytic [maximum-deficit lemma, note 11](11-analytic-arm-bootstrap.md), proves for L<5/3 that

    f(t)>=1+t/2,   g(t)>=1+(L-t)/2.

Here L=pi/2<5/3. The separate support restrictions on [0,L] and [L,pi] are C^1 with their own one-sided top derivatives, so the inner corner is C^1 and

    x_K'(t)=(1-f(t))u_t+(g(t)-1)v_t.

The two component signs are strict in (0,L). This is the full injectivity condition; |K_*|>=A_L(K_*)=|G|>2.2 supplies the area requirement for K^i. All these regularity and endpoint steps are proved in note 13. QED.

## Lemma C. A maximizing monotone sofa can gain a right-angle motion without changing shape

Suppose omega in [arcsec(2.2),L), M is a monotone sofa, A_omega(C_omega(M))=|M|>=2.2, and its own cap is a global maximizer of A_omega. Then a rotated copy of M admits a right-angle motion.

**Proof.** Use Lemma A at the fixed smaller angle. Floating defects d_n(t)=sigma_n(t)-tau_n(t) are at most C lambda_n delta_n. [Note 14](14-fixed-angle-maximizer.md) proves feasible pinned-strip variations and their actual-versus-assigned support comparison. Its uniform interior-ball estimate gives d_n(omega),d_n(L)<=C_omega lambda_n.

The common-boundary endpoint identity gives

    sum_t d_n(t)sin t=0.

Since all sines are positive, the weighted sum of the negative defects equals that of the positive defects. Summing the floating bounds and the two pinned bounds, then dividing only by the fixed pinned sines, proves

    tau_n(omega)<=sigma_n(omega)+o(1),
    tau_n(L)<=sigma_n(L)+o(1).

The geometric gap bounds w_n^circ<=tau_n(L), z_n^circ<=tau_n(omega), continuity of the gaps, and upper semicontinuity of pinned edge lengths now give for the SPECIFIED cap

    w_K^circ<=sigma_K({L}),   z_K^circ<=sigma_K({omega}).

Note 14 then proves the extra width property directly. The established two scalar estimates in §4.2, together with those inequalities, place the triangle

    Delta=conv{O,c u_0,c v_omega},   c=sec omega-tan omega,

in the niche of K. Reflection, when used to choose the larger extent, preserves this triangle and the relevant normal interval; the conclusion transfers back to the original M, as checked in note 15. After cutting Delta off P_omega, the width in every direction u_t, omega<=t<=L, is at most

    max(sin t,cos(t-omega))<=1.

Thus M itself has those widths. Rotate a copy of M clockwise through L-omega inside the horizontal strip, translate it to the start of its original motion, and then follow that motion. The support functions provide continuous strip-positioning translations. The total angle is L. This changes the placement, not the sofa, and preserves every contained subset. QED.

## Lemma D. A maximizing cap in K^i is a horizontal translate of C(G)

**Proof.** For its canonical extension x, input 6 gives A(K)=Q(x)=Q(x_G)=|G|. The Q value along the segment from x_G to x is constant by concavity and maximality. Therefore each nonnegative Mamikon gap, in particular the four cap gaps, is zero.

Here is the rigidity calculation, with its full nonsmooth justification in [notes 01](01-mamikon-equality.md) and [02](02-cap-rigidity.md). Let f=h_K-h_{C(G)} and phi be Gerver's fixed angle, with psi=L-phi. A Mamikon term is one half the integral of the squared tangent displacement alpha. Under Minkowski interpolation alpha is affine, so its midpoint gap is

    (1/8) integral (alpha_K-alpha_{C(G)})^2.

Zero gap gives equality of tangent displacements almost everywhere. For a tangent target T this reads

    sin(T-t)f'(t)+cos(T-t)f(t)=f(T),

whose solutions are f(t)=f(T)cos(T-t)+C sin(T-t). For the outer-corner term it reads f'(t)=f(t+L). Support functions are Lipschitz and hence absolutely continuous; solving on interior subintervals and taking continuous endpoint limits needs no smooth-boundary assumption.

Use the four cap intervals in the order 4,3,2,1. On (L,pi), target T=pi and f(L)=0 give f(t)=a cos t, a=-f(pi). On (psi,L), target T=pi-phi, the already known f(T) and f(L)=0 give the same formula. On (phi,psi), the outer-corner equation gives f'(t)=-a sin t and endpoint matching removes the additive constant. On (0,phi), target T=L gives f(t)=A cos t and matching gives A=a. Thus

    h_K(t)-h_{C(G)}(t)=a cos t,   0<=t<=pi.

The lower supports of a standard right-angle cap are those of its bottom segment, because the cap is downward closed. Its two bottom endpoints also translate by (a,0), so the full support functions agree after that translation. Hence K=C(G)+(a,0). Horizontal translation commutes with the niche construction. QED.

## Lemma E. Gerver's sofa is regular closed

    G=closure(interior G).

**Proof.** [Note 07](07-regular-closedness.md) derives this from input 7. The niche boundary is a continuous height graph H over the projection I of the cap's top edge, and the cap contains I x [0,1]. The two envelope pieces have height strictly below one. A height-one point on the remaining rotation-path piece satisfies

    -alpha(t)/beta(t)=cot t.

The left side is nondecreasing and the right side strictly decreasing, so there is at most one such point. Thus H<1 on a dense subset of I. Approaching any point of G over I by points strictly between H and 1 gives interior approximation, including endpoints and a possible single contact. Outside I the niche is absent locally and the convex cap has dense interior. Closedness gives the reverse inclusion. QED.

## Proof of the theorem

### 1. Keep the starting sofa and monotonize it

Because |S|=|G|>2.2, input 2 supplies an angle omega in [arcsec(2.2),L] and a translation S_0 of S in standard position. Let M be the monotonization of S_0. Then

    S_0 subset M,
    |G|=|S_0|<=|M|<=|G|.

Thus M has area |G|. Its OWN cap K satisfies M=K minus N_omega(K) and A_omega(K)=|G|. By input 3, this K is a global cap maximizer. The auxiliary cap used to establish input 3 is not substituted for K and need not contain S_0.

### 2. Add a right-angle motion to this same M

If omega=L, no change is needed. Otherwise Lemma C supplies a rotation V for which V(M) admits a right-angle motion. In either case V(S_0) remains a subset of V(M), and both have area |G|.

Translate V(M) into standard right-angle position by W and monotonize once more, obtaining T. Then

    W(V(S_0)) subset W(V(M)) subset T,
    |T|=|G|

by the same area sandwich. Its own cap J is a global right-angle cap maximizer and T=J minus N_L(J).

### 3. Identify the containing sofa

Lemma B puts J in K^i. Lemma D gives J=C(G)+(a,0) and therefore

    T=G+(a,0).

Composing the actual translations and rotations above with translation by (-a,0) gives an isometry U with

    U(S) subset G,   |U(S)|=|G|.

This is an actual containment, not a conclusion drawn from comparing two unrelated maximal areas.

### 4. Recover the original set exactly

The set U(S) is closed. If it omitted an interior point of G, its open complement and the interior of G would contain a common positive-radius ball. That ball would be a positive-area subset of G minus U(S), contradicting equality of the finite areas. Hence interior G is contained in U(S). Taking closures and applying Lemma E yields G subset U(S). Together with the preceding containment this proves

    U(S)=G.

QED.

## What was closed in this revision

The former outstanding obligations were selection of a specified cap, mesh-scale perturbation errors, pinned-strip feasibility and signs, and endpoint-safe passage to curvature inequalities. They are proved in notes 10, 12, 13 and 14, with the explicit checks in [note 15](15-final-proof-audit.md). Note 11 additionally replaces the finite scalar bootstrap by an analytic inequality proof.

The record preserves the failed exact-maximizer selection, equal-area set inference, geometry-free perturbation bound, full-circle sine-hat estimate, and globally C^1 support shortcut. None is used here. No noncongruent optimal sofa has been constructed.

The paper argument is closed relative to the explicitly listed, previously established inputs. It remains a claim requiring independent mathematical review; no new formal verification is claimed.
