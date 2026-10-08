# Full-turn maximizers admit variations of total envelope area without connectedness constraints

**Scope.** GC's actual-body gap compression supplies a missing admissibility argument for the maximizer route. At an attained full-turn area maximum, the total canonical envelope area is maximal under arbitrary continuous perturbations of the hallway offsets that preserve the two vertical endpoint supports. The perturbed profiles need not be convex support functions; their envelopes need not retain the proposed outer hull, remain connected, or have nonempty fibers everywhere.

This does not assert smooth differentiability, balance at coincident walls, disappearance of hidden-edge atoms, or the sharp curvature bound. It removes connectivity, full horizontal fiber coverage, and proposed-hull retention as *feasibility constraints* for this unpenalized full-turn value problem. It does not retroactively remove the constraints of a fixed-width or support-penalized optimization. Labels FV are local.

## 1. Continuous profiles define possibly disconnected full-turn envelopes

Put L=pi/2. Fix vertical endpoint supports H_t,H_b with H=H_t+H_b in (0,1]. The body-coordinate incoming strip is [-H_b,H_t] in the y coordinate. Let h be any real continuous 2pi-periodic function satisfying

$$h(L)=H_t,\qquad h(3L)=H_b.$$

No convexity or curvature property is required. For every t in [0,L] union [pi,3L], define

$$\mathcal H_h(t)=\{z:z\cdot n_t\le h(t),\ z\cdot n_{t+L}\le h(t+L),\
 z\cdot n_t\ge h(t)-1\ \text{or}\ z\cdot n_{t+L}\ge h(t+L)-1\}.$$

Let

$$E(h)=\bigcap_{t\in[0,L]\cup[\pi,3L]}\mathcal H_h(t). \tag{FV.1}$$

The four axis outer inequalities bound E(h) horizontally by -h(pi)<=x<=h(0) and vertically by -H_b<=y<=H_t. Thus E(h) is compact, or empty. Each vertical fiber is an interval or empty, as proved directly for these hallway normals in GC Section 3.

At the lower initial/final angles, every point of that vertical span fits the relevant unit endpoint strip [H_t-1,H_t], since H_t+H_b<=1. At the upper endpoints it fits the unit strip [-H_b,1-H_b]. These unit strips have the same incoming orientation; straight translations inside an infinite corridor connect compatible initial positions when H<1. The corner offsets built from h are continuous. Therefore all points of E(h) satisfy both complete continuous motion families, apart from the possible failure of connectedness.

GC4 now converts E(h), when nonempty, to a connected full-turn body of **exactly the same area**, preserving its vertical extrema. This conversion may change the horizontal width and the convex hull. Neither is constrained in the unrestricted full-turn value problem.

## 2. Exact variational principle at an actual maximum

Let A_F denote the full-turn optimal value in the common strip of width at most one, and suppose a compact connected S attains it. Put h_0=h_{conv S}, H_t=h_0(L), H_b=h_0(3L). Canonical tightening implies S subset E(h_0). GC4 applied to E(h_0) and maximality imply

$$|E(h_0)|=|S|=A_F.$$

For any real continuous periodic v with v(L)=v(3L)=0, and any real epsilon, h_epsilon=h_0+epsilon v satisfies the same vertical normalization. Section 1 and GC4 therefore give:

**Theorem FV1 (unconstrained envelope-value variation).**

$$\boxed{|E(h_0+\varepsilon v)|\le|E(h_0)|=A_F.} \tag{FV.2}$$

This is an exact finite inequality for every epsilon, with the empty-set case interpreted as area zero. The profile h_epsilon may fail to be a support function, and E(h_epsilon) may split into components or lose some extreme witnesses. These are no longer reasons to discard the comparison: GC constructs a legitimate connected competitor of that total area.

The theorem uses *global unpenalized* maximality. It does not apply unchanged at an optimizer constrained to keep its width, its hull, its exact unit span when its perturbed envelope loses that span, or a penalty measured against a prescribed support function. In particular it does not erase Note 53's normal-cone terms for that note's different constrained optimization problem.

Nor does FV.2 claim that the original body itself deforms continuously into the newly connected body as epsilon varies. For an area comparison only the separate existence of each competitor and its own two continuous hallway motions is needed.

## 3. Consequence for finite-angle first variations

The same argument holds for a finite set of conventional hallway orientations containing the endpoint frames. Use independent real offsets for the finite hallway walls and intersect their hallway sets. At a global maximum of total finite-envelope area, any resulting nonempty disconnected polygon can be compressed and vertically filled to a connected polygon of equal area, preserving the same sampled orientations and endpoint strips. This is a statement about the finite-angle relaxation, not continuous feasibility between sampled angles.

In a local fixed-line arrangement chart, the total area is computed by integrating the **positive part** of the signed fiber length. Nonempty fibers throughout the proposed hull projection and retention of all proposed hull vertices are not restrictions on these unpenalized competitors.

In a nondegenerate arrangement with no coincident positive-length boundary segments, let z_j translate one outer wall and its associated inner wall by the same signed normal distance, keeping all other wall data fixed. To first order the total area changes by

$$\frac{\partial |E|}{\partial z_j}
=\ell_j^{\rm outer,visible}-\ell_j^{\rm inner,visible}. \tag{FV.3}$$

Here the first length counts only the exposed outer-wall boundary portions of the actual envelope, and the second counts the exposed associated inner-wall boundary portions. Intersections of distinct nonparallel lines contribute only O(epsilon^2) triangular changes; the open side strips supply the displayed first-order terms. Coincident inner/outer line portions and positive-length pinches are deliberately excluded from this differentiable formula.

At an interior free-offset maximum, both signs are admissible by GC, so FV.3 vanishes:

$$\boxed{\ell_j^{\rm outer,visible}=\ell_j^{\rm inner,visible}.} \tag{FV.4}$$

This equation counts actual exposed lengths, not full convex-hull edge lengths. It gives no immediate bound on a hull edge whose relative interior is hidden in a niche.

## 4. Pinches are retained in the objective, not as connectivity constraints

For a finite-line perturbation with uniformly bounded fiber directional derivatives, write ell_epsilon(x) for its signed top-minus-bottom height. Total area is

$$\mathcal A(\varepsilon)=\int (\ell_\varepsilon(x))_+\,dx.$$

Whenever ell_epsilon has a right directional derivative dot-ell_v a.e. with a uniform integrable difference-quotient bound, dominated convergence gives

$$D_+\mathcal A(0)[v]
=\int_{\{\ell_0>0\}}\dot\ell_v
 +\int_{\{\ell_0=0\}}(\dot\ell_v)_+. \tag{FV.5}$$

Thus empty fibers and pinches must still be accounted for. They are not a restriction forbidding the perturbation; they enter the derivative through the positive part. At a maximum the right side is nonpositive. At wall ties dot-ell_v may depend nonlinearly on v, so one must not infer a two-sided linear balance merely by discarding those terms.

This is the specific gain over imposing connectivity and then retaining an uncontrolled normal multiplier for its active constraints. The remaining nonsmooth area terms are different and cannot simply be set to zero.

## 5. Remaining structural task

FV1 provides actual competitors for every continuous offset perturbation of a maximizing full-turn envelope. To finish the maximizer route one still needs a justified continuum first-variation or comparison theorem covering coincident contacts and hidden hull edges, followed by a sharp area bound. GC does not imply that the limiting hull curvature is absolutely continuous or bounded by one.

The original sharp target |S|<=M, and the equivalent clipping-deficit inequality, remain unproved. The value of this result is that future unpenalized full-turn arguments need not first solve connectedness of every perturbed envelope or impose actual-hull retention as an artificial admissibility condition.

The continuum statement is conditional only on attainment of the actual full-turn maximum and on the established canonical-motion setup; it does not assume a smooth maximizing hull, reference proximity, or a weighted-cap maximizing property. All new reasoning is pen and paper. No CI, Lean/Lake compilation, numerical optimizer, dependency installation or manuscript build was used. Independent review remains necessary.
