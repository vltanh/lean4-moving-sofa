# 08. Candidate proof: Gerver's sofa is the unique maximizing shape

Date: 2026-10-02.

**Status:** a complete proposed pen-and-paper argument, assembled from the preceding research notes. It is NOT a Lean theorem, has not been independently reviewed, and must not be presented as a kernel-checked result. The principal new and most delicate claims are the penalized polygon extensions in notes 05 and 06. The intended theorem is full equality of sets up to congruence, not uniqueness within Romik's ansatz or equality modulo null sets.

## Theorem under investigation

Let G be Gerver's sofa as defined in this repository. If S is a closed, connected moving sofa in the unit right-angled hallway and its planar Lebesgue area equals |G|, then there exists a Euclidean isometry U such that

    U(S)=G.

In particular the allowance of zero-area subsets or appendages does not produce another maximizing shape in this class.

The proof uses the already established optimality bound |S|<=|G| and the existing geometric/analytic results of Baek's proof, with the corrections recorded by the repository. Its proposed new contribution is equality and rigidity, including extensions needed to keep track of the PARTICULAR starting sofa.

## Lemmas supplied by the research notes

1. **Cap rigidity (notes 01-02).** Equality in the convexity of the four cap Mamikon terms forces the cap support difference to be a cos(t). Consequently every maximizing cap in K^i is a horizontal translate of C(G).
2. **Specified right-angle maximizers (notes 04-05).** Every cap maximizing A_{pi/2}, not merely one chosen as a balanced limit, satisfies the injectivity condition and belongs to K^i.
3. **Specified-angle motion (notes 04 and 06).** If a monotone sofa M of area at least 2.2 has angle omega in [arcsec(2.2),pi/2), and its own cap maximizes A_omega, a rotated copy of that SAME M admits a pi/2-angle motion.
4. **Set recovery (notes 03 and 07).** G is regular closed: G=closure(interior G). Every closed subset of G with area |G| therefore equals G.

Lemma 2 comes from a support-function penalty selecting the specified cap. Its per-facet error is O(lambda_n delta_n), so the limiting surface-measure inequality survives. Lemma 3 additionally treats the two pinned strip directions: their errors are O(lambda_n), and the boundary-vector identity supplies the reverse inequalities at those fixed directions. These arguments do not assert that every maximizing cap meets the existing definition `IsBalancedMaxCap`.

## Proof, with containment maintained throughout

### Step 1. Choose a motion angle for the given sofa

Because |S|=|G|>2.2, the existing angle-bound theorem (Theorem 1.5.1) gives a motion angle

    omega in [arcsec(2.2),pi/2].

The standard-position construction (Proposition 2.3.1) translates S to a set S_0 in standard position for that angle. Write S_0=U_0(S), with U_0 an isometry.

### Step 2. Monotonize the given sofa, rather than selecting an unrelated maximum

Let M=I_omega(S_0), its monotonization. Theorem 2.3.2, including its connectedness result, gives

    S_0 subset M,
    M is a moving sofa with angle omega.

Monotonicity of measure and the existing global optimality bound give

    |G|=|S_0| <= |M| <= |G|,

so |M|=|G|. Let K=C_omega(M). The cap/niche identities give

    M=K minus N_omega(K),
    A_omega(K)=|M|=|G|.

The cap K is a global maximizer of A_omega. To check this point without assuming that arbitrary caps give moving sofas: Theorems 3.5.5-3.5.6 provide a balanced cap maximizing A_omega whose cap-minus-niche set IS a moving sofa. Thus the maximum of A_omega is at most |G| by the existing global bound, and K attains it. No containment relation to that auxiliary balanced cap is needed or asserted.

### Step 3. Obtain a right-angle motion while retaining M

If omega=pi/2, set V to be the identity. Otherwise apply Lemma 3 to K and M. It yields an isometry V, in fact a rotation, such that V(M) admits a pi/2-angle motion.

This is the step for which the original `gm_area_le` is insufficient: that proof changes to selected balanced maxima. Note 06 instead establishes the horizontal-side inequalities for K itself and uses the three-phase motion construction on M itself.

In either case V(S_0) is still a subset of V(M), and both have area |G|.

### Step 4. Monotonize once more, now at a right angle

Translate V(M) by an isometry W into standard right-angle position, and set

    T=I_{pi/2}(W(V(M))).

Then W(V(M)) is a subset of T, and T is a moving sofa. The same area sandwich gives |T|=|G|. Its cap J=C_{pi/2}(T) satisfies

    A_{pi/2}(J)=|G|,
    T=J minus N_{pi/2}(J).

As in Step 2, J is a global cap maximizer at this angle.

### Step 5. Identify the right-angle cap and its canonical sofa

By Lemma 2, J lies in K^i. By Lemma 1 there is a real a with

    J=C(G)+(a,0).

The niche is covariant under horizontal translation, so

    T=G+(a,0).

Let Z be translation by (-a,0). Composing the actual containments above yields

    U(S) subset G,
    U=Z composed with W composed with V composed with U_0.

No mere area comparison has been substituted for a containment in this composition.

### Step 6. Recover the original set exactly

The set U(S) is closed and has area |G|. By Lemma 4, G is the closure of its interior. If a point of interior(G) were absent from U(S), closedness would leave a positive-radius ball in G minus U(S), contradicting equality of the finite areas. Hence interior(G) is contained in U(S), and taking closures gives G subset U(S).

Together with the containment from Step 5 this proves U(S)=G. This is the desired equality of shapes.

## Dependency and noncircularity check

- The existing OPTIMALITY theorem is an input; the desired UNIQUENESS theorem is never assumed.
- The cap rigidity argument needs only equality in the cap Mamikon terms. It does not assume that auxiliary tail bodies B,D are uniquely represented.
- Neither penalized sequence is declared to consist of exact unpenalized maximizers. The errors are retained until their limits are justified.
- The numerical arm bootstrap and the angle inequalities are the previously established scalar results; no new floating-point evidence is used as proof.
- The proof does not infer set equality from measure equality without closedness, containment, and regular-closedness.
- Every new result in this chain is mathematical prose. The original Lean challenge, original optimality proof, and axiom allowlist remain unchanged. CI has not been used to validate this research.

## What needs adversarial review first

The strongest review priority is notes 05-06: uniform convergence of the finite-angle objectives on the chosen compact cap families; the support perturbation's mesh-locality at extreme cells; feasibility and objective comparison for pinned-strip changes; and the limit passage that removes the balancing hypothesis from the original analytic inputs.

The cap ODE rigidity and envelope-based set recovery are shorter independent arguments and can be reviewed separately. An error in a reduction would leave those results available, rather than erase all progress. No noncongruent maximizing sofa has been constructed in this investigation.
