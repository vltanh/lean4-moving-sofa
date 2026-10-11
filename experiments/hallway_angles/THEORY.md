# Geometry, surviving rigidity, and limitations

These are pen-and-paper derivations for an exploratory numerical experiment, not Lean-checked theorems. No claim of novelty is made for the elementary baseline constructions. References are in README.md.

## 1. The actual hallway angle

Let `0 < beta < pi` be the bend in the direction of travel. Set

$$n_0=(0,1),\qquad n_1=(\sin\beta,\cos\beta).$$

The sharp, unit-width hallway with inner corner at the origin is

$$H_\beta=\{z:n_0\cdot z\le1,\ n_1\cdot z\le1,\ \max(n_0\cdot z,n_1\cdot z)\ge0\}.$$

It is the union of two half-strips. The incoming travel direction is `(1,0)` and the outgoing direction is `(cos beta,-sin beta)`. The angle between the rays pointing *away* from the corner is `pi-beta`. At `beta=pi/2` this is the usual L-shaped hallway, reflected relative to some conventions.

A hallway pose in the fixed-sofa frame is `c(u) + R(theta(u)) H_beta`. Its two wall normals are

$$(-\sin\theta,\cos\theta),\qquad(\sin(\beta-\theta),\cos(\beta-\theta)).$$

The computation intersects these poses with the fixed strip `0 <= y <= 1`. It considers two restricted families:

- **forward:** `theta(u)=beta*u`, with endpoint corner heights `0,0`;
- **reverse:** `theta(u)=(beta-pi)*u`, with endpoint heights `0,1`.

In each case the final outgoing strip coincides with the initial horizontal strip. The middle corner's horizontal coordinate is fixed to zero to remove a translation freedom. No theorem here reduces all possible motions to these two families, proves symmetry, or excludes partial/backtracking rotation. In particular, translation-only motion is also considered separately.

## 2. An exact translation-only optimum

The parallelogram

$$P_\beta=\{z:0\le n_0\cdot z\le1,\ 0\le n_1\cdot z\le1\}$$

has area `1/sin(beta)`, because the determinant of the two unit normals has absolute value `sin(beta)`. It translates into the corner along `(1,0)` and out along `(cos beta,-sin beta)`: before reaching `P_beta`, translate it by `(-a,0)`, `a>=0`; afterwards translate it by `a*(cos beta,-sin beta)`. On the first leg the first strip condition stays fixed and the other upper-wall coordinate decreases. On the second leg the second strip condition stays fixed and the first upper-wall coordinate decreases. Thus the shape remains in the hallway throughout.

Conversely, any shape traversing the hallway using translations only must fit in a translate of each of the two width-one strips. Their intersection is a parallelogram of the same area, regardless of the offsets. Hence

$$\boxed{A_{\mathrm{translations}}(\beta)=\csc\beta.}$$

This is an optimum for that restricted class, not for arbitrary rigid motions. It diverges at both degenerate endpoints. The experiment excludes exactly `0` and `pi`.

## 3. A fixed-inner-corner rotating construction

Set `c(u)=0` in the forward family. The inner wedge removes no point of the upper half-plane from the intersection. Indeed, for `0<=theta<=beta`, the nonnegative linear combination of the two normals with weights `sin(beta-theta)` and `sin(theta)` is `(0,sin beta)`. For `y>=0`, their two scalar products cannot both be negative.

The outer normals cover the angular interval `[pi/2-beta, pi/2+beta]`. When `beta<pi/2`, the resulting cap consists of a circular sector of angle `2*beta` and two tangent triangles, cut off by `y=0`. Its area is `beta+cot(beta)`. When `beta>=pi/2`, those normals contain the whole upper semicircle; the extra directions are redundant for the unit upper half-disk. Therefore

$$\boxed{A_{\mathrm{fixed\ corner}}(\beta)=\begin{cases}\beta+\cot\beta,&\beta<\pi/2,\\ \pi/2,&\beta\ge\pi/2.\end{cases}}$$

The endpoint strip conditions give entry and exit by translation. This exact formula tests both acute and obtuse hallway geometry; it is not an optimality claim for rotating sofas.

## 4. What survives from the uniqueness proof

For this derivation write `u_t=(cos t,sin t)` and `v_t=(-sin t,cos t)`, and order the normals counterclockwise as `u_t,u_(t+beta)`. This is the same normal separation as in the hallway, with the order exchanged. If `h` is a differentiable support function, the intersection `Y_beta(t)` of the two support lines is

$$Y_\beta(t)=h(t)u_t+\frac{h(t+\beta)-\cos\beta\,h(t)}{\sin\beta}v_t.$$

This follows by taking its scalar product with each normal. Subtracting the two unit wall widths moves the corner by

$$u_t+\tan(\beta/2)v_t,$$

whose norm is `sec(beta/2)`. Thus simply replacing a quarter-turn by `beta` but keeping orthogonal corner coordinates would be incorrect.

The tangent displacement from the support point `h(t)u_t+h'(t)v_t` is

$$D_\beta h(t)=\frac{h(t+\beta)-\cos\beta\,h(t)}{\sin\beta}-h'(t).$$

It is linear in `h`. Consequently, whenever Mamikon's hypotheses apply, its quadratic term has the same square-gap identity:

$$\frac{1-\lambda}{2}\int(D_\beta h_0)^2+\frac\lambda2\int(D_\beta h_1)^2-\frac12\int(D_\beta((1-\lambda)h_0+\lambda h_1))^2
=\frac{\lambda(1-\lambda)}2\int(D_\beta(h_0-h_1))^2.$$

Equality forces the oblique tangent equation

$$\boxed{\sin\beta\,\Delta'(t)+\cos\beta\,\Delta(t)=\Delta(t+\beta).}$$

At the right angle this reduces to the equation in the uniqueness manuscript.

### Full-circle kernel (a conditional rigidity result)

For a `2*pi`-periodic `H^1` function, the Fourier multiplier of `D_beta` on frequency `k` is

$$d_k(\beta)=\frac{e^{ik\beta}-\cos\beta}{\sin\beta}-ik.$$

If it vanishes, then `exp(ik beta)=cos beta+ik sin beta`. Taking squared moduli gives

$$1=\cos^2\beta+k^2\sin^2\beta,$$

so `k=1` or `k=-1`. Both do vanish. Therefore, on the **full circle**, the kernel is exactly

$$\ker D_\beta=\operatorname{span}\{\cos t,\sin t\},$$

the two translation directions. For any finite Fourier truncation, the square functional is strictly convex after those two modes are removed. This is a useful ingredient for a future concave relaxation, not that relaxation itself. Equality on only a contact subinterval does not imply the full-circle hypothesis. The actual partial-arc gluing and endpoint conditions still need to be proved. The operator also becomes poorly conditioned near degenerate angles; strictness alone does not give a uniform numerical stability estimate.

## 5. Continuous-motion enclosure, not just sampled collisions

Let `S_N` be the exact intersection of sampled hallway poses and the fixed strip. Let the piecewise-linear path be sampled on a grid containing all its knots. Suppose consecutive samples differ by at most `delta` in angle and `D` in corner position. Let `R` bound `|p-c_i|` for every `p in S_N` and every sampled corner `c_i`.

For a point in a grid cell, choose the nearer endpoint in the path parameter. Its angle distance is at most `delta/2` and its corner distance at most `D/2`. For either normal coordinate `f_j(u)=n_j(theta(u)) dot (p-c(u))`,

$$|f_j(u)-f_j(u_i)|\le 2R\sin(\delta/4)+D/2=:\varepsilon.$$

This follows from the chord length between unit normals and the triangle inequality. Thus impose at **every sample** the tightened conditions

$$f_0\le1-\varepsilon,\quad f_1\le1-\varepsilon,\quad\max(f_0,f_1)\ge\varepsilon.$$

Every retained point then lies in every intervening hallway. The upper inequalities remain at most `1`, and whichever inner inequality was at least `epsilon` remains nonnegative. Therefore

$$S_N^{\mathrm{inner}}\subseteq S_{\mathrm{continuous}}\subseteq S_N.$$

The maximum norm used for `R` is attained at an exterior polygon vertex and a corner-path knot: a convex norm on each of the corresponding convex hulls attains its maximum at vertices. The implementation keeps the largest positive-area polygon component, rather than silently adding the areas of disconnected pieces.

At the first and last poses the retained shape is in the designated incoming/outgoing strip. Moving the hallway farther along the opposite travel direction at those fixed orientations only decreases the other outer-wall coordinate. This supplies entry and exit translations and hence a complete motion, not merely an in-place rotation animation.

The theorem is an exact-real construction. **NumPy and GEOS do not provide directed rounding or exact Boolean geometry.** The implementation includes a small numerical guard and an independent denser containment audit, but neither turns its decimal areas into machine-certified lower bounds. Interval/exact arithmetic is still required for publication-quality numerical certificates.

## 6. Failed shortcuts and unresolved work

### Affine shear does not transport the solution

For `A=[[1,1],[0,1]]` and a quarter-turn `R`,

$$ARA^{-1}=\begin{pmatrix}1&-2\\1&-1\end{pmatrix},$$

which is not orthogonal. A general affine map may change the corridor angle, but the conjugated motion is not rigid. Only similarities preserve all rotations this way. Hence an affine image of Gerver and its original motion is not a solution of the new problem by itself.

### Finite intersections can lie about feasibility

For the stationary right-angle motion, checking only angles `0` and `pi/2` accepts `[-1,1] x [0,1]`, of area `2`. The point `(1,1)` collides at angle `pi/4`, since an outer-wall scalar product is `sqrt(2)>1`. The true continuous intersection has area `pi/2`. A finer grid improves an outer approximation; it does not by itself certify a feasible sofa.

### The sharp functional Q has not been generalized

Baek's upper bound uses an enlarged space of triples and a core/tail partition chosen using Gerver's angle `phi` (arXiv:2411.19826, Section 1.8 and Chapter 8). The equality machinery does not automatically construct those partitions for a different hallway. A positive square-gap identity is insufficient to establish an area majorant, its sharpness, or an exhaustive reduction to its domain. It also does not make the direct path-area objective concave.

Accordingly, the code is a **local, nonconvex path search**, not a generic convex optimizer rediscovering the global solution without a contact-pattern assumption. Its useful output is reproducible candidates, active geometry to inspect, and counterexamples to overly strong computational claims. Deriving a sharp arbitrary-angle relaxation and proving its equality case remain explicit open steps of this experiment.
