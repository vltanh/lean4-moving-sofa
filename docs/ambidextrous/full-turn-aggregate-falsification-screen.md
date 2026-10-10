# Direct falsification screen of the stronger adaptive full-turn area bound

**Status: no certified counterexample found; no global bound proved.** This continuation tests the stronger proposed upper estimate from AS on preselected genuine full-turn constructions and on separate geometric diagnostics. Numerical values are approximate; the uncut reference itself produces a positive *false* excess under the same discretization. Hence these samples do not prove either inequality. This is a negative-result-pruning checkpoint, not an optimization certificate or a claim of convergence.

The sole active mathematical target remains full-turn optimality; partial turns are frozen.

## 1. Which inequality was tested

For an actual full-turn canonical envelope with common horizontal width W and full niche roofs n_U,n_V, let d_U=1-A_U,d_V=1-A_V. The exact identities are

\[
|E|=W-\int_I[\max(d_U,n_V)+\max(d_V,n_U)]dx,
\quad
\mathscr C(U,V)=W-\int_I\max(d_U+d_V,n_U+n_V)\,dx.
\]

The first equality is ordinary area, assuming its actual fibers are nonempty. The second expression is a **stronger upper relaxation**:

\[
|E|\le\mathscr C(U,V),\qquad
\mathscr C-|E|=\int_I[a_++b_+-(a+b)_+]dx\ge0,
\]

where a=n_U-d_V and b=n_V-d_U. The proposed \(\mathscr C\le M\) is still **unproved** and stronger than the necessary full-turn bound. If a rigorous example had \(\mathscr C>M\) but \(|E|\le M\), that would refute the proposed stronger lemma **without** refuting Romik's candidate.

For comparison, \(\Delta(U)+\Delta(V)-G=M-|E|\) is the exact original area assertion, not an independently established inequality.

## 2. Four preselected screens (not an optimizer campaign)

All screens used the explicit closed-form Romik upper support, finite sampled angle extrema and trapezoidal area integration. M was computed from the positive cubic root. Each invocation was under an external five-second cap; NumPy was already installed. A complete locally executed reproduction package accompanies the conversation. Source SHA-256 hashes and raw outputs are retained there. Do not describe the scripts as interval-arithmetic, global search, or a continuum feasibility verifier.

**A. Signed top-normal affine cuts of the reference.** An independently chosen signed slope in
\[
\{-0.11,-0.075,-0.05,-0.03,-0.015,-0.005,0,
0.005,0.015,0.03,0.05,0.075,0.11\}
\]
is applied to the upper and reflected-lower reference roofs, anchored at the appropriate original top-face endpoint. The 169 ordered cap pairs retain the reference middle-height segment and have niches no larger than the reference niches; their canonical envelopes are full-turn feasible. At 700 horizontal samples the maximum displayed \(\mathscr C-M\) was +0.000229312 **at the uncut reference**; at 1,500 samples it was +0.000105140, again at the reference. The largest sampled switching mismatch at 1,500 was about 0.002908, in a pair whose aggregate estimate was about 0.053816 *below* M.

**B. Independently prescribed support-plane cuts at middle or tail upper normals.** Six cut depths between 0.001 and 0.06 were used at 16 upper normals ranging from \(\pi/2-0.64\) to \(\pi/2+0.64\), plus the uncut reference. All 97 cap roof profiles passed the stated sampled roof-height test; 9,409 ordered pairs passed sampled nonempty-fiber tests. This **does not certify continuum fiber feasibility or that the input caps equal the hull caps of the envelope**. The maximum apparent excess was again the uncut-reference error (+0.000220005 at 680 samples, +0.000128604 at 1,200). The largest sampled switching mismatch at 1,200 was about 0.004076, while that pair's aggregate estimate was about 0.038361 *below* M. Some planes modify reference middle arcs and are outside the earlier exact small top-normal cut theorem; the numerical test does not enlarge that theorem.

**C. Convex-template segment deformations of the actual reference sofa.** For each of 13 fixed upper-half-plane unit-segment directions and each of eight fixed positive coefficients t, use the *actual body*
\[
S_{t,\phi}=(\Sigma+t[0,(\cos\phi,\sin\phi)])/(1+t).
\]
Lemma PV1 proves **both complete turns for every one of these 104 shapes**, without relying on sampled fiber conditions. The convex hull support is known exactly as a Minkowski-support sum, and the two cap roofs and niches were numerically reconstructed from it. At 600 samples the largest apparent \(\mathscr C-M\) was +0.000153 for t=0.005, decreasing to about +0.000055 on the 1,000-sample replay. These very small positive readings are commensurate with the known reference discretization error and are not violations. The largest switching mismatch at 1,000 was about 0.005638, whereas that aggregate value was about 0.258223 *below* M.

**D. Auxiliary profile screens only.** 234 mirrored asymmetric elliptic-flank cap profiles were sampled; only 23 passed sampled fiber nonemptiness. Their largest displayed \(\mathscr C-M\) was about −0.042408. The sampled condition has **not** been promoted to certified continuum feasible motions. Separately, 174 circular-stadium cap profiles passed analogous sampled-fiber tests; none produced a sampled violation of the *independent* earlier spatial-half one-cap bound. The closest sampled value was \(\mathcal P_J-M/2\approx-0.011219\). These two diagnostics are exploratory, not verified sofa counterexample searches.

## 3. The reference bias prevents a proof claim

Exactly at the reference one has \(G=0\), \(a=b\), and
\[
\mathscr C(U_*,U_*)=|E_*|=M.
\]
The same code reports **positive false excesses** of roughly \(10^{-4}\) at moderate resolution. The fact that these apparent excesses decrease on higher-resolution fixed replays is not a rigorous error enclosure. Small numerical differences—even with the correct sign—cannot be interpreted as exact upper or lower bounds.

The experiments did not reveal a defensible counterexample to \(\mathscr C\le M\) in the tested families. They also do **not** establish that \(\mathscr C\le M\) is possible globally: neither finite angle meshes nor these low-dimensional families exhaust the compatible saturated positive opposite-face class. A failure of the stronger bound would still be consistent with \(|E|\le M\), since its switching-mismatch remainder can be positive.

## 4. Concrete next hand-proof gate

Rather than run an indefinite parameter optimizer, attempt a **compatible-pair local comparison** that simultaneously controls (i) changed reference outer-roof mass, (ii) saved true niche mass, and (iii) the cross-switching mismatch. The explicit middle-normal plane cuts are particularly useful stress cases because they alter support data outside the earlier reference-tail comparison domain; the PV deformations give full-turn feasibility without making any assumption about face alignment.

To certify a suspected violating example, first establish the entire quarter-angle safety, connected nonempty fibers, and actual hull-cap support data; then bound \(\mathscr C-M\) rigorously (for instance with exact rational geometry or validated interval error). No positive numerical reading in this note meets those requirements. Conversely, proving the stronger global \(\mathscr C\le M\) would complete the full-turn case, but it has **not** been done.

All new scripts were constrained to five seconds per invocation. No Lean/Lake compilation, CI, dependencies, manuscript build, long search, or claim of unrestricted full-turn optimality was made.
