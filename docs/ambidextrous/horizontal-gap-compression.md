# Horizontal gap compression removes the connectedness obstruction for canonical envelopes

**Scope.** This is an actual-body construction, not an auxiliary area calibration. A compact, possibly disconnected set in a horizontal strip of width at most one, satisfying prescribed conventional lower/upper canonical hallway families and their endpoint strips, can be converted to a **connected** body of at least the same area satisfying those same angular families. If its original vertical fibers are intervals or empty, the area is preserved exactly. In particular this applies to a full canonical envelope left disconnected by completing a partial turn.

It does **not** prove the sharp full-turn area bound or pay the positive completion loss in CC. It does remove the separate obstacle to applying a future connected full-turn area theorem to the **total** area of a disconnected completed envelope. It also allows variations of total full-envelope area without requiring the varied envelope itself to stay connected. Labels GC are local. Baseline: `de6671090ea2c940263851eedf8699656253d0f0`.

The only motion input is support-tightening and the conventional normal intervals used in SI. The construction, area argument and connectedness proof are given here. No numerical result is a premise.

## 1. A contraction preserves every safe support depth

Let S be a nonempty compact subset of a horizontal strip of vertical span H<=1. Write h_S(n)=max_{q in S} q dot n for a unit normal n=(n_x,n_y). Let T be a nondecreasing 1-Lipschitz function on the horizontal projection interval, and set F(x,y)=(T(x),y).

**Lemma GC1 (safe-depth preservation).** For every p in S and every unit normal n,

$$\boxed{h_{F(S)}(n)-F(p)\cdot n\le\max\{h_S(n)-p\cdot n,\ H|n_y|\}.} \tag{GC.1}$$

In particular a depth at most one remains at most one.

**Proof.** Fix q in S. If n_x(q_x-p_x)>=0, monotonicity and the Lipschitz bound imply

$$n_x(T(q_x)-T(p_x))\le n_x(q_x-p_x).$$

Adding n_y(q_y-p_y) bounds the new scalar-product difference by the old depth of p. If n_x(q_x-p_x)<0, monotonicity makes the new horizontal term nonpositive, so the new difference is at most n_y(q_y-p_y)<=H|n_y|. Take the supremum over q. QED.

A canonical hallway contains p exactly when at least one of its two inner support depths is at most one (outer inequalities use the actual supports and are automatic). GC1 preserves whichever inner wall protected p, for every p and every visited angle. If S fits a unit strip with normal n, every point has n-depth at most one; hence F(S) still fits such a strip. Thus **all original safe strip directions are preserved**, not just the horizontal incoming strip.

This argument does not say arbitrary affine stretching is feasible. It changes x by a monotone contraction and leaves y unchanged; its use of H<=1 is essential.

## 2. Collapse exactly the empty horizontal gaps

Let D=proj_x S be compact, with convex hull [l,r]. Define

$$T(x)=\int_l^x 1_D(t)\,dt,\qquad \bar S=\{(T(x),y):(x,y)\in S\}. \tag{GC.2}$$

T is continuous, nondecreasing and 1-Lipschitz. It collapses every open component of [l,r] minus D. Moreover

$$\boxed{\operatorname{proj}_x\bar S=[0,|D|].} \tag{GC.3}$$

Indeed T maps [l,r] continuously onto that interval. A value attained at a point of a complementary open gap is also attained at either endpoint of the gap, which lies in D. The zero-measure case |D|=0 simply gives a vertical set and causes no area difficulty.

**Lemma GC2 (exact area preservation before vertical filling).**

$$\boxed{|\bar S|=|S|.} \tag{GC.4}$$

**Proof.** Enumerate the open gaps of D and let T_N collapse only the first N gaps. On each of the finitely many remaining horizontal bands, F_N(x,y)=(T_N(x),y) is a translation. Different bands have images with disjoint horizontal interiors; they can meet only on vertical boundary lines. Consequently |F_N(S)|=|S|.

The sum of all gap lengths is finite, at most r-l, so T_N converges uniformly to T. Since S is compact, F_N(S) converges in Hausdorff distance to bar S. Compact-set area is upper semicontinuous under Hausdorff convergence: for every delta>0 the approximants eventually lie in the delta-neighborhood of bar S, and the areas of those bounded neighborhoods decrease to |bar S|. Therefore |bar S|>=limsup |F_N(S)|=|S|.

For the reverse inequality, each horizontal section is mapped by the same 1-Lipschitz real function T, which cannot increase one-dimensional Lebesgue measure. This follows by covering a compact section with open intervals and using that each image interval has no greater length. Thus |T(S_y)|<=|S_y| for every y. Both S and bar S are compact and measurable; integrating the horizontal sections proves |bar S|<=|S|. QED.

GC1 applies to T and to each T_N. The area calculation is not a claim that Hausdorff convergence generally preserves area: it uses exact finite-gap area preservation and the separate nonexpansion inequality.

## 3. Fill vertical fibers without changing any support or hallway constraint

For a nonempty compact set Q with interval horizontal projection, define its vertical filling

$$V(Q)=\{(x,(1-t)y_0+t y_1):(x,y_0),(x,y_1)\in Q,\ 0\le t\le1\}. \tag{GC.5}$$

This set is compact: it is the continuous image of the compact set of pairs of points of Q with the same abscissa, times [0,1]. It has the same horizontal projection and vertical extrema as Q. Also

$$Q\subseteq V(Q)\subseteq\operatorname{conv}Q,$$

so it has **exactly the same support function** as Q.

A conventional lower-turn canonical hallway has both frame-normal y-components nonnegative. On a fixed vertical line its outer conditions are upper bounds on y, and its inner disjunction is a union of two upward rays, hence one upward ray, possibly all or none. Their intersection is an interval. At axis endpoints the same assertion follows directly from the horizontal/vertical inequalities. The upper-turn family has the reversed y signs and likewise has interval vertical sections. Any endpoint straight strip also has interval vertical sections.

Consequently, if Q lies in every hallway/strip of these prescribed families, each filled vertical segment lies in them as well. Since its support is unchanged, this can be stated either using the pre-filling canonical placements or its own support-tightened ones.

**Lemma GC3 (connectedness).** V(Q) is connected whenever proj_x Q is an interval.

**Proof.** If V(Q) separated into two disjoint nonempty relatively closed sets, compactness would make both pieces compact. Each nonempty vertical fiber is an interval, so it lies wholly in one piece. The projections of the two pieces would then be disjoint nonempty compact sets partitioning an interval, a contradiction. QED.

Applied to Q=bar S, GC3 and GC1 give a compact connected body S^sharp=V(bar S) with |S^sharp|>=|bar S|=|S|, preserving every prescribed conventional hallway orientation and endpoint strip. Continuity of support functions supplies continuous canonical corner translations over each closed turning interval; the usual straight motions in the endpoint strips can be appended. Thus the statement concerns actual motions, not just a finite collection of placements.

## 4. Exact preservation for canonical envelopes

If the original S has vertical fibers that are intervals or empty, vertical filling after compression can change area only on **countably many vertical lines**. In fact, at any abscissa z with a unique preimage x under T, the fiber of bar S is just the already interval fiber S_x. A value with two different preimages comes from a nontrivial interval on which the monotone T is constant. The interiors of these maximal constant intervals are disjoint and each contains a rational, so their values are countable. Filling the fibers at those values adds zero planar area.

**Theorem GC4 (connectedification with unchanged area).** Let S be nonempty and compact, contained in a horizontal strip of span at most one, with interval-or-empty vertical fibers. Suppose S satisfies the two prescribed conventional canonical hallway families and endpoint strips. Then S^sharp constructed above is compact, connected, has the **same area**, preserves the vertical extrema, and admits the **same two angular intervals**. Its horizontal width may decrease; no claim of preserving the original convex hull or fixed horizontal width is made.

The theorem also applies when an angular family is a full quarter. It does not add missing angles to a set that did not already satisfy them.

## 5. Consequences for the actual full-turn optimization

Let A_F be the supremum of areas of connected compact bodies admitting the two complete conventional turns, with an incoming horizontal strip of width at most one. The supremum is unchanged if connectedness is dropped from the definition: for any compact feasible set, first compress its empty projection gaps and then fill its vertical fibers, using GC1--GC3 to obtain a connected feasible set of no smaller area.

More specifically, for any bounded convex K in the unit incoming strip, let E_full(K) be K minus both full canonical open sweeps. This set is compact and has interval-or-empty vertical fibers. If nonempty, GC4 produces a connected full-turn body of area exactly |E_full(K)|. Its endpoint strips follow from K's incoming vertical span and the full-quarter endpoint frames. Therefore

$$\boxed{|E_{\rm full}(K)|\le A_F,} \tag{GC.6}$$

**even when E_full(K) itself is disconnected**. In particular a proof of A_F<=M for connected full-turn bodies would bound the total area of every such completed envelope, not just its individual connected components.

This is a proved modification of the completed set, not the invalid assertion that it was already connected. It repairs the specific issue illustrated by `candidate-functionals-disconnected-cap-pairs.md` without retracting that counterexample.

For the partial-turn estimate CC2,

$$|S|\le |E_{\rm full}(K)|+\lambda(\varepsilon)+\lambda(\varepsilon'),$$

GC.6 now gives the valid general bridge

$$\boxed{|S|\le A_F+\lambda(\varepsilon)+\lambda(\varepsilon').} \tag{GC.7}$$

The positive allowances are **still present**. The theorem does not imply A_F=M or that a partial-turn optimum equals A_F.

## 6. A concrete change to maximizer-based work

If S attains the full-turn maximum and K=conv(S), same-hull saturation may first be taken without decreasing area. For any other bounded convex K' in the same unit incoming strip, the total full-envelope area |E_full(K')| cannot exceed |S|: otherwise GC4 would turn that envelope into a connected full-turn body with larger area.

Thus a global maximizing hull may legitimately be compared against perturbations whose **full envelope disconnects or develops empty fibers**. Those events are no longer reasons to reject a perturbation outright. When expressing total area by fibers, however, one must still integrate the positive part of the signed length. The positive-part correction does not disappear, and differentiability through pinches is not asserted.

No consequence about curvature bounds, vanishing normal-cone multipliers, smooth contacts, or the sharp area value is inferred without further argument. This removes one specific global admissibility obstruction; it does not replace the remaining shape analysis.

All statements above are hand proofs. No CI, Lean/Lake compilation, numerical optimization, dependency installation or manuscript build was used. Independent review and the unrestricted full-turn upper bound remain outstanding.
