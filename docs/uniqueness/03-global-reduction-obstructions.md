# 03. Why cap rigidity is not yet global sofa uniqueness

Date: 2026-10-02. Status: negative results and a proved conditional set-recovery lemma.

The target is: for every closed connected moving sofa S with |S|=|G|, there is a Euclidean isometry U with S=U(G), as equality of sets. A reflection is allowed in the congruence relation. Merely having the same area, the same Romik parameters in an ansatz, or equality modulo null sets is not the target.

## Negative result A: convergence of discrete maxima cannot select every continuum maximizer

A tempting inference is: every maximizing cap is a limit of maximum polygon caps, so every maximizing cap is balanced. The existing proof does not establish this, and the corresponding general compactness principle is false.

Counterexample: on X=[0,1], set F(x)=0 and F_n(x)=x/n. Then:

- X is compact;
- each F_n is continuous;
- F_n decreases pointwise to F and converges uniformly;
- F_n is an upper approximation to F;
- every F_n has the unique maximizer x=1;
- every x in X maximizes F.

Only 1 can be approached by exact discrete maximizers. For example 0 cannot. Thus even decreasing uniform upper approximations do not justify the desired converse.

This invalidates a PROOF METHOD, not shape uniqueness. It does not construct a non-Gerver optimal sofa.

The repository defines `IsBalancedMaxCap` through a subsequential limit of exact maximum polygon caps. `theorem8_1_1_balanced` applies to that class. No converse from an arbitrary `sofaArea` maximizer to `IsBalancedMaxCap` has been supplied.

## Negative result B: the current area comparison does not preserve the given shape

In `MovingSofaOptimality/Main.lean`, `gm_area_le`:

1. obtains a rotation angle for the given sofa S;
2. chooses a balanced maximum sofa at that angle and compares AREAS;
3. rotates that selected sofa to a right-angle motion;
4. compares its area to a selected balanced maximum right-angle sofa.

The crucial first comparison is not a containment of S in the selected balanced sofa. Equality throughout therefore does not recover S, even after note 02 identifies the selected right-angle cap.

Similarly `theorem1_5_2` has the hypothesis `IsBalancedMaxSofa S omega`. Applying it to an arbitrary area maximizer merely because it is maximal would drop a hypothesis.

A proof for all sofas must repair both the right-angle/representation step and the injectivity step for the PARTICULAR starting shape, or replace these steps with a different shape-preserving argument.

## Negative result C: area equality is not equality of closed connected sets

Let E=[0,1]^2 and F=E union ([1,2] x {0}). Both are compact and connected; E is a proper subset of F and |E|=|F|=1. They are not congruent, for example their diameters differ. Consequently compactness, connectedness, containment, and equal areas alone do not rule out zero-area appendages.

This example is not asserted to be an optimal moving sofa. It records the exact logical obstacle for recovering a set from measure comparisons.

## Positive result: closed subsets of a regular-closed host

Lemma. Let T be a closed, finite-area planar set satisfying T=closure(interior(T)). If S is closed, S is a subset of T, and |S|=|T|, then S=T.

Proof. If q in interior(T) were outside S, closedness of S and openness of interior(T) would give an open ball about q contained in T minus S. That ball has positive area, contradicting equality of the finite areas. Thus interior(T) is a subset of S. Taking closures gives T subset S, and hence equality.

Accordingly a shape-preserving enlargement of an optimal S to a congruent copy of G would finish the set-recovery step once regular-closedness of G is established. Equality of areas with an unrelated selected maximizer cannot use this lemma.

## Routes that remain worth testing

A. Derive the injectivity condition for every maximizing right-angle cap directly from variational optimality, rather than from the definition of balancedness.

B. Approximate a SPECIFIED maximizing cap by maxima of suitably penalized finite-angle objectives. The penalty must tend to zero and select the specified cap, while its first variations must be controlled well enough to preserve the limiting surface-measure inequality. Merely proving convergence of penalized maximizers is not enough.

C. Establish a genuinely shape-preserving right-angle enlargement or a strict area loss for a maximizer that cannot admit a right-angle motion.

D. Search for feasible zero-area appendages under alternative motions. Such an appendage must be proved to move with the whole sofa; appending a segment in a static drawing is not a counterexample.

No assertion that these routes succeed is made in this note. Failed approaches should stay in this log instead of being silently converted into hypotheses.
