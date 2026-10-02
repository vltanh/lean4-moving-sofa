# 06. Keep the specified sofa when passing to a right-angle motion

Date: 2026-10-02. Status: proposed pen-and-paper extension; not Lean-checked or independently reviewed. This note supplies the endpoint argument missing from a naive use of the selection method. Constants may depend on the fixed angle omega<pi/2; no uniformity as omega approaches pi/2 is asserted or needed.

Put L=pi/2. Fix omega in (0,L) and a cap K_* maximizing A_omega. The main claim is that K_* satisfies the two horizontal-side inequalities

    w_{K_*}^circ <= sigma_{K_*}({L}),
    z_{K_*}^circ <= sigma_{K_*}({omega}).                 (H)

These are the inputs used in the geometric proof of Theorem 4.2.5. Establishing them for the specified maximizer, rather than a newly selected balanced maximizer, preserves the sofa's geometry in the angle reduction.

## 1. A common interior ball at each fixed angle

Every standard omega-cap lies in the bounded parallelogram P_omega and contains

    O=(0,0),  (c_omega,0),  o_omega=(c_omega,1),
    c_omega=sec(omega)-tan(omega)>0.

Indeed the two consecutive allowed top normals omega and L have support 1, so their intersection o_omega belongs to the cap. All other upper normals are in [0,omega] union [L,L+omega]. Their scalar product with o_omega is positive, so O satisfies their inequalities; it also satisfies the two lower inequalities. Moving o_omega downward to (c_omega,0) decreases all upper scalar products and stays in the fan. This proves the assertion from the defining half-plane intersection.

The fixed triangle with these vertices therefore lies in every cap. Choose an interior ball B(q,rho_omega) in this triangle. Its radius is positive and independent of the polygon mesh. This will control actual support functions when a pinned strip is moved and some other assigned heights cease to be actual supports.

## 2. Select polygon caps converging to K_*

Use the compact space X of all standard omega-caps, its polygon subspaces X_n with uniform dyadic mesh delta_n=omega/2^n, and

    P(K)=integral_0^{L+omega} (h_K-h_{K_*})^2.

Equality P=0 identifies the upper support functions and hence the full caps, whose remaining defining lower heights are fixed. The circumscribed polygon recovery caps preserve sampled supports and converge to K_*.

The polygon area objectives A_n converge uniformly to A_omega. To justify niche continuity without a singular endpoint division, write points of the fan as

    p=s(u_0-v_omega)+r(u_0+v_omega),  r>=|s|.

For 0<=t<=omega, the scalar products of u_0+v_omega with u_t and with v_t are, respectively,

    cos t-sin(omega-t),   cos(omega-t)-sin t.

Both are strictly positive, uniformly on this compact interval when omega<L. The two inner-quadrant inequalities therefore define continuous upper thresholds for r. Subtract |s|, take the minimum of those thresholds and its positive part, and then maximize over t. At t=0 and t=omega the height is zero because one inner inequality lies on a boundary of the fan. The relevant s-range is uniformly bounded, using the bounded supports and these positive denominators. Thus the full and finite-mesh niche areas converge uniformly by continuity on a compact parameter space. The circumscribed-cap areas converge uniformly as well; the common interior ball makes continuity of the finite intersections immediate. This proves uniform A_n convergence.

Choose lambda_n->0 more slowly than the uniform approximation error, and maximize A_n-lambda_n P on X_n. Note 04 gives K_n->K_*.

## 3. One-sided defect bounds at floating normals

For every sampled upper normal t other than the pinned normals omega,L, put

    d_n(t)=sigma_n(t)-tau_n(t).

Exactly as in note 05, an outward displacement of a positive facet changes the support function on at most two neighboring mesh cells of the upper normal domain. At its extreme endpoints 0 and L+omega the virtual-corner formula has coefficient at most sec(delta_n). Consequently

    d_n(t)<=C_omega lambda_n delta_n.                   (F)

For zero-length facets this holds automatically. No exact balancedness or niche containment is used.

## 4. Pinned-strip variations: O(lambda_n), not O(lambda_n delta_n)

Let t be omega or L, with sigma_n(t)>0. Increase its top height by epsilon and its parallel bottom height by epsilon, preserving width one. Leave the other assigned heights fixed. The feasibility statement of Lemma 3.4.8 says that the resulting intersection is a polygon cap translate for sufficiently small positive epsilon.

Normalize it back to standard position. If t=omega the normalizing translation is (-epsilon/cos omega,0). If t=L it is (epsilon tan omega,-epsilon). The normalized defining heights differ from those of K_n by at most C_omega epsilon.

Crucially, the assigned heights need not all be actual supporting heights. We do NOT assume they are. The actual supports are no larger, so the niche formed from them is contained in the niche formed from the assigned heights. The cap intersection is unchanged. Therefore the actual normalized cap's A_n is at least the extended objective of the assigned-height perturbation, exactly the monotonicity in Proposition 3.3.7.

There is a mesh-independent Hausdorff bound for this perturbation. In general suppose K is defined by unit-normal inequalities with heights h_i, contains B(q,rho), and K' is defined by heights h_i' with |h_i'-h_i|<=a epsilon. Put eta=a epsilon/rho. Directly checking each inequality gives

    (1-eta)K+eta q  subset K' subset (1+eta)K-eta q.

For the second inclusion apply the original inequalities to (x'+eta q)/(1+eta). Thus d_H(K,K')<=C epsilon when K is uniformly bounded. Applied with the common ball from Section 1, this shows |P(K')-P(K_n)|<=C_omega epsilon uniformly in n.

The extended area variation is (sigma_n(t)-tau_n(t))epsilon+O(epsilon^2). For a pinned strip the cap variation is sigma_n(t)-sigma_n(t+pi), and the niche variation is tau_n(t)-sigma_n(t+pi); the subtraction yields sigma_n(t)-tau_n(t). The displayed niche sign in the original paper's proof of Lemma 3.4.7 is reversed; the corrected subtraction is used here, consistently with the repository's proved result.

Penalized maximality and the objective comparison above now give

    d_n(omega)<=C_omega lambda_n,
    d_n(L)<=C_omega lambda_n.                           (P)

Again zero facet length makes these upper bounds automatic.

## 5. The boundary-vector identity supplies the missing lower bounds

For EVERY polygon cap, its upper boundary and its niche polyline have the same endpoints. Their vector displacements therefore give

    sum_t d_n(t) v_t=0,
    hence sum_t d_n(t) sin t=0.                         (V)

All upper sampled normals lie strictly between 0 and L+omega<pi, so their sines are positive. Summing the upper bounds (F) and (P), weighted by sin t, gives a bound C_omega lambda_n: there are O(1/delta_n) floating facets.

For either pinned normal k, (V) implies

    -d_n(k) sin k = sum_{t != k} d_n(t) sin t
                  <= C_omega lambda_n.

Since sin omega>0 and sin L=1, this proves

    tau_n(omega)<=sigma_n(omega)+C_omega lambda_n,
    tau_n(L)<=sigma_n(L)+C_omega lambda_n.               (R)

This weighted identity avoids dividing errors by the small sines of the end mesh cells. It is needed only at the two pinned normals, whose sines are fixed and nonzero.

## 6. Horizontal gaps in the limit

Before using balancedness, the geometric proof of Theorem 4.1.2 establishes for any polygon cap

    w_K^circ<=tau_K(L),   z_K^circ<=tau_K(omega).

For example the bottom segment that remains outside every wedge has length at least w_K^circ and is part of the niche polyline in direction L. The limiting wedge endpoint at t->omega is O, so the segment is not truncated below that length by the fan. The left-hand statement is its reflection.

Combine this with (R). The gap infima are continuous in Hausdorff distance for fixed omega<L, with Lipschitz bound 1+sec omega. Weak convergence of surface-area measures gives

    limsup_n sigma_n({k}) <= sigma_{K_*}({k})

at each fixed normal k. Taking limits proves (H).

## 7. A right-angle motion of the SAME monotone sofa

Now suppose omega>=arcsec(2.2), A_omega(K_*)>=2.2, and M=K_* minus N(K_*) is a monotone sofa. The geometric proof of Theorem 4.2.5 uses balancedness only through (H). In more detail:

- The cap-area lower bound forces one of its two horizontal extents past the threshold d_{omega,min}.
- Reflect if necessary. The right extent and the supporting line at omega determine a right triangle with hypotenuse 1 and horizontal length g.
- The wedge geometry gives g<=w_K^circ. By (H), the top edge has length at least g, so the second point q_1 used in that proof belongs to K_*.
- The explicit inequalities of Lemmas 4.2.2-4.2.4 then place O, o_omega-v_0 and o_omega-u_omega in the closure of one inner quadrant.

Consequently M has width at most one in every normal direction between omega and L. It can be rotated through L-omega wholly inside the horizontal strip, translated in that strip, and then moved using its original omega-angle motion. This constructs an L-angle motion of a rotated copy of M, not of an unrelated maximizing sofa.

The repository makes this separation particularly explicit: after the call to `theorem4_2_5`, `theorem1_5_2` in `MovingSofa/Angle/RightAngle.lean` uses only `ang_width_le_one`, boundedness, and the original motion to construct the three phases. Those phases do not use balancedness again.

## Status

Sections 1-6 are the proposed new extension of the horizontal-side inequality to a specified cap maximizer. Section 7 then reuses the existing geometric and numerical angle argument with its actual inputs, rather than silently applying a theorem with a missing balancedness hypothesis.

Together with note 05 and the rigidity theorem in note 02, this gives a route to an actual containment of any optimal sofa in a congruent copy of G. The remaining set-recovery point is regular-closedness of G; equal areas alone do not settle that point, as note 03 emphasizes.
