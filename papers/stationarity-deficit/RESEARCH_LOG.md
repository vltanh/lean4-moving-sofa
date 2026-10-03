# Research log: stationarity, deficit, and rigidity

Date: 2026-10-03.

This paper branch starts from main at cf4fefff35971554e635d84a7ef5593c66e5c6e4. It does not change the proof branch or use CI, Lean, Lake, or a proof-source generator. The existing uniqueness source at 36dec2efe72f3a75ea1fb6bd99578dc956530b14 is an uncompiled research input, not a verified theorem.

## 1. Negative result: the proposed balance-free outline omitted feasibility

An unrestricted cap K need not contain its niche N(K), and K minus N(K) need not satisfy the connectedness required of a moving sofa. In particular

    A(K) = |K| - |N(K)|

is not automatically the area of a feasible connected sofa. The exact identity is

    |K minus N(K)| = A(K) + |N(K) minus K|.

Consequently, selecting an ordinary maximizer of A does not by itself produce the sofa to which the additional-motion construction applies. Nor does abstract stationarity alone prove niche containment. Replacing Baek's balanced-maximum existence theorem by an ordinary cap maximum without addressing this point would be an invalid proof.

This corrects the earlier conversational outline. It does not disprove the existing optimality theorem or the equality-case research.

The new manuscript will distinguish:

1. a conservative route retaining Baek's independently proved feasible-maximizer theorem, while replacing the arm iteration and reorganizing the terminal quadratic argument;
2. the stronger specified-maximizer stationarity route needed for uniqueness;
3. a genuinely balance-free route, which additionally needs an independent feasible-attainment theorem.

The completed global optimality theorem must not be used as an input when presenting a new proof of optimality. In particular the current library helper cap_area_le_gerver calls theorem1_1_1 and is unsuitable for such a reorganization before the upper bound is re-established.

## 2. Sources consulted

- J. Baek, Optimality of Gerver's Sofa, arXiv:2411.19826v1, especially Sections 1.3.2, 2.5, 3.4-3.5, 6.5, and 8.3-8.5. The arXiv HTML display has a regenerated date; the stable citation here is the versioned arXiv identifier, not that display date.
- Repository uniqueness research at commit 36dec2efe72f3a75ea1fb6bd99578dc956530b14, especially SelectedCaps, PaperReductions, ShapeUniqueness, and the equality/rigidity notes.

Further results and failed shortcuts will be recorded in separate commits. No assertion of independent review or machine verification is attached to this manuscript.
