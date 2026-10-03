# 15. Final mathematical audit of the new reductions

Date: 2026-10-02. Author's paper audit, not an independent review. This records explicit checks used by the completed argument in note 16 and distinguishes failed shortcuts from the statements actually proved.

## 1. The common triangle does not assume an unproved contact at o

For omega<L set c=sec omega-tan omega and o=(c,1). A standard cap has a point p on its omega supporting line and a point q on its top line. The strip inequalities imply

    p=o-lambda v_omega,  q=o-mu u_0,  lambda,mu>=0.

For r in [0,omega], v_omega.u_r=sin(r-omega)<=0, so

    h_K(r)>=p.u_r>=o.u_r.

For r in [L,L+omega], cos r<=0, so

    h_K(r)>=q.u_r>=o.u_r.

Hence o satisfies every upper defining inequality, as well as both lower ones, and belongs to K. This proves its membership directly without assuming any smoothness or a positive pinned facet.

The direction of o is (L+omega)/2. Consequently o.u_r>=c>0 throughout [0,L+omega]. The origin satisfies all upper inequalities strictly and lies on the lower fan boundaries. Also (c,0) satisfies the inequalities, since moving o down decreases each upper scalar product and stays in the fan. Thus conv{O,(c,0),o} lies in every cap, exactly as required in notes 12 and 14.

## 2. Exact algebra for the short remaining inner-wall segment

This expands the line-intersection calculation in note 13. Write h_-=h(t-delta), h_0=h(t), h_+=h(t+delta). On b(t) parameterize a point as

    p=(h_0-1)u_t+y v_t.

The inequalities p.u_(t-delta)>=h_--1 and p.u_(t+delta)>=h_+-1 give

    (h_+-1-(h_0-1)cos delta)/sin delta <= y
      <= ((h_0-1)cos delta-h_-+1)/sin delta.

Their signed interval length is

    (2h_0 cos delta-h_--h_++2(1-cos delta))/sin delta
      =-sigma_K(t)+2 tan(delta/2).

Here sigma_K(t)=(h_-+h_+-2h_0 cos delta)/sin delta is the outer facet length. Taking the positive part gives precisely (2 tan(delta/2)-sigma_K(t))_+. The virtual normals 0 and pi are valid at the end cells because their supporting lines meet the first/last sampled facet at the same bottom vertex.

Thus the sigma term in note 13's geometric inequality does not come from balancedness; it comes from consecutive supporting-line geometry.

## 3. Reflection in the fixed-angle argument preserves the specified body

The cap reflection across the line of angle (L+omega)/2 sends u_t to u_(L+omega-t). It preserves P_omega, exchanges u_0 with v_omega, and consequently preserves

    Delta=conv{O,c u_0,c v_omega}.

It swaps w^circ with z^circ and the pinned normals L with omega. Therefore both horizontal-gap hypotheses transfer to the reflected cap. The right-extent proof in note 14 applies whichever extent is large.

There is no hidden replacement by a balanced reflected maximizer: reflection sends the normal interval [omega,L] to itself. Its width conclusion transfers straight back to the ORIGINAL M on exactly that interval. Alternatively, the inner-quadrant conclusion transfers back with the parameter t replaced by omega-t and with the same triangle Delta. The subsequent strip motion is a motion of a rotated copy of the original M.

## 4. A negative result: curvature regularity away from the top does not make h globally C^1

Let a>0 and take the Minkowski sum of the upper unit half-disc with the horizontal segment [-a,a] x {0}. This is a standard right-angle cap. On upper normal angles its support function is

    h(t)=1+a|cos t|,  0<=t<=pi.

The curvature density is 1 on each open upper quadrant, there are no atoms at 0 or pi, but

    h'_-(L)=-a,  h'_+(L)=a,
    sigma({L})=2a.

Thus absolute continuity on [0,L) and (L,pi] does NOT justify identifying these two top derivatives. This is a counterexample to a regularity shortcut, not an alternative maximizing sofa.

The proof in note 13 instead uses separate C^1 restrictions [0,L] and [L,pi], with their respective one-sided top derivatives. The inner-corner formula combines those two restrictions and is C^1 on its parameter interval despite the permitted top edge. No top atom is excluded or silently moved into an absolutely continuous density.

## 5. The two limits are not interchanged

For each fixed n and positive facet, take epsilon down to zero in the penalized first variation. Only the resulting linear defect bound is passed to n going to infinity. The possible lack of a uniform admissible epsilon, and mesh-dependent coefficients of O(epsilon^2), do not affect that order of limits.

The quantities that DO need uniform control are proved uniform: the upper-interval sine-hat integral, the pinned-strip Hausdorff/penalty bound, the polygon diameter, and the O(delta^2) geometric error. The resulting total floating error is O(lambda_n+delta_n), not O(lambda_n/delta_n).

## 6. Endpoint measures are included rather than guessed

The weak-limit test functions in note 13 are supported on a circular arc (-epsilon,L), not merely inside (0,L). They may be nonzero at 0. The first floating atoms are spread onto their preceding mesh cells, and the spreading error is bounded by the modulus of continuity of the test function times a uniformly bounded mass. This proves no atom at 0. Reflection proves the same at pi. Testing only away from the endpoints would NOT suffice.

For the pinned atoms in note 14 the direction is limsup sigma_n({k})<=sigma({k}). The gap inequalities give a lower bound for sigma_n({k}), so this is the correct semicontinuity direction.

## 7. Check of the new scalar bootstrap

In note 11, M=max((1-f)_+,(1-g)_+) over the interval is at most 1 because f,g>=0. If M>1/3, set c=(3M-1)/2. The extremal integral has a rising ramp of width

    M/c-1/(3c)=2/3,

height c, and triangular area c/3. Before the ramp ends its integral is less than M. Afterwards it is c(L+1/3)-M, which is strictly less than 2M-1<=M when L<5/3. This checks both cases and the strict inequalities. No bound above on f or g is needed beyond the nonnegative-deficit bound M<=1.

## 8. Exact-set recovery

The proof of regular-closedness in note 07 uses a continuous niche graph H over the horizontal top interval I, a full rectangle I x [0,1] in the cap, and H<1 on a dense subset of I. The possible single height-one contact causes no isolated remnant: approach its abscissa by x_n with H(x_n)<1 and choose heights strictly between H(x_n) and 1. The same construction handles both endpoints of I. Outside I, the niche is absent locally and convexity supplies interior approximations.

Thus G=closure(interior G), not merely an almost-everywhere equality. The final proof obtains an ACTUAL containment U(S) subset G before using equality of areas and closedness. The square-with-an-attached-segment example from note 03 therefore does not invalidate the final recovery step.

## Proof status

Notes 10–14 supply the formerly proposed selection/variation extensions; notes 01–02 and 07 supply the independent rigidity and regular-closedness arguments. The explicit identities above check the remaining endpoint, reflection, and sign issues. Note 16 assembles them without an additional uniqueness assumption.

This is a completed paper argument by its author. It has not received independent mathematical review and is not a Lean theorem. Historical CI results apply only to the earlier equality lemmas, not to this proof.
