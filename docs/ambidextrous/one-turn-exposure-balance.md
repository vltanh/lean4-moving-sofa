# Exact limiting wall-exposure balance for weighted maximizing caps

**Scope.** This advances the exposure/balance step proposed in Section 9 of the imported arm reduction. The earlier positive-top result PT3 makes horizontal shortening admissible for the selected polygons. Finite differentiation and the summable WP defects then prove exact limiting exposure balance. No differentiability formula for the full infinite-angle niche is assumed. This does not identify exposure by the proposed saturated ODE, and does not prove the optimal value. Labels EB are local.

Dependencies: WP1--WP2, WR1, PT1--PT3 in [one-turn-positive-top-face.md](one-turn-positive-top-face.md), and the finite niche derivatives established in WP Section 4.

## 1. A genuinely two-sided finite variation

Select an arbitrary weighted maximizer U_* by WP1, with grid polygons U_n, height H_n<=1, width W_n, top-face length T_n, support h_n, penalty coefficient eta_n->0, and weights w_j of total at most one. PT3's proof gives a uniform positive lower bound for T_n for large n. The artificial vertical box sides are inactive by WP1.

For a real s near zero with s>-T_n, define U_(n,s) by leaving the left endpoint of each horizontal section fixed and moving its right endpoint by s. Horizontal sections have lengths at least T_n, so this remains a nonempty compact convex downward-closed cap of the same height. Its support at every upper normal theta is exactly

$$
h_{n,s}(\theta)=h_n(\theta)+s(\cos\theta)_+.
\tag{EB.1}
$$

Indeed a positive cosine tests the right endpoint, a negative cosine tests the unchanged left endpoint, and a vertical normal tests the unchanged height. The grid polygon remains a grid polygon. Small s of either sign remains inside the fixed artificial box.

Section widths change by s at every height from zero to H_n. Therefore

$$
|U_{n,s}|=|U_n|+sH_n,\qquad W(U_{n,s})=W_n+s.
\tag{EB.2}
$$

The coefficient is H_n, not one: the selected penalized polygons are not assumed to have exact height one.

## 2. Differentiate only the finite union

Let tau_(n,j) be the first-wall exposure length of the full finite niche at theta_j, for 0<j<n. Under EB.1 its first inner wall moves by s cos(theta_j); companion walls stay fixed. Consequently

$$
\left.\frac{d}{ds}|N_n(U_{n,s})|\right|_{s=0}
=\sum_{0<j<n}\tau_{n,j}\cos\theta_j.
\tag{EB.3}
$$

This is a finite polygon-union identity. On the relative interior of an exposed edge, area changes by its normal displacement times its length. Nonparallel wall intersections contribute O(s^2). The finite source normals are distinct and nonhorizontal; no moving wall coincides on a segment with another source wall or the floor. Birth or disappearance of a zero-area triangle contributes O(s^2). The same coefficient holds from both sides. Multiple components or zero-height contacts require no connectedness assumption.

The finite objective maximized by U_n is F_n(U)-eta_n D_n(U,U_*)^2. Its derivative along EB.1 vanishes. The penalty derivative is

$$
2\eta_n\sum_jw_j(h_n(\theta_j)-h_*(\theta_j))(\cos\theta_j)_+.
$$

All supports have absolute value at most the fixed B from WP2. Thus

$$
\left|H_n-\frac12-\sum_{0<j<n}\tau_{n,j}\cos\theta_j\right|
\le4B\eta_n.
\tag{EB.4}
$$

Since H_n->1,

$$
\sum_{0<j<n}\tau_{n,j}\cos\theta_j\longrightarrow\frac12.
\tag{EB.5}
$$

Reflect horizontally to obtain the second-quarter version, whose positive weight is -cos(theta), or sin(t) with theta=t+pi/2. No claim about a derivative of |N(U_*)| was used.

## 3. Exposure measures are uniformly bounded away from concentration

Define first-quarter exposure measures

$$
\nu_n=\sum_{0<j<n}\tau_{n,j}\delta_{\theta_j}.
$$

The neighboring-wall estimate WR.1, the uniform support bound, and 2 tan(delta/2)<=2 delta imply

$$
0\le\tau_{n,j}\le C\delta
\tag{EB.6}
$$

with a constant independent of n and j. This estimate holds for all interior grid indices, including the first and last, using WR's endpoint-angle qualification. Therefore every subsequential weak limit nu is absolutely continuous with bounded density on [0,pi/2] and has no endpoint atoms.

WP2 gives ell_(n,j)<=tau_(n,j)+b_(n,j), with sum_j b_(n,j)->0. Testing with nonnegative continuous functions supported in the open quarter and passing to the limit gives

$$
\rho_f(t)\,dt\le\nu.
\tag{EB.7}
$$

Here rho_f is the bounded open-quarter curvature of U_* from WR1, not its axis atom.

The actual right upper boundary has y-coordinate f sin(t)+f' cos(t). Its derivative is rho_f cos(t). WR1 gives initial height 1/2, while its final height is one. Hence

$$
\int_0^{\pi/2}\rho_f(t)\cos t\,dt=\frac12.
\tag{EB.8}
$$

Equations EB.5 and EB.8 give zero integral of cos(t) against the nonnegative difference in EB.7. The weight is strictly positive on the open quarter; EB.6 excludes an atom at its zero endpoint. Thus the difference vanishes.

**Theorem EB1 (limiting exposure equals curvature).** For every prescribed weighted maximizer selected by WP1,

$$
\boxed{\nu_n\ \rightharpoonup\ \rho_f(t)\,dt.}
\tag{EB.9}
$$

The reflected second-quarter exposure measures converge to rho_g(t) dt. Every subsequential limit is the same, so the convergence holds along the full sequence.

The result identifies the limit of the finite full-niche exposures. It is not a claim that an unproved formula involving the active continuum corner curve defines those measures.

## 4. In fact the total interior facet defect tends to zero

One can strengthen weak convergence to a statement at the sampled facets:

$$
\boxed{\sum_{0<j<n}|\tau_{n,j}-\ell_{n,j}|\longrightarrow0,}
\tag{EB.10}
$$

and similarly in the second quarter.

Here are the missing endpoint details. The right vertical facet length ell_(n,0) tends to 1/2. WR's near-axis floating bound is C delta+b_(n,j); hence uniformly little non-axis mass lies in (0,a) when a is small. Curvature-measure convergence on (-a,a), followed by a decreasing to zero, then forces the axis atom to converge to WR.3's value 1/2. This rules out an unaccounted concentration of floating facets at the axis.

Projection of the cap's right boundary gives

$$
\sum_{0<j<n}\ell_{n,j}\cos\theta_j=H_n-\ell_{n,0}.
$$

Combine this with EB.4 to see that the cosine-weighted signed defect tends to zero. The negative part of each defect is at most b_(n,j), so its total tends to zero. Thus the cosine-weighted positive defect tends to zero as well.

On [0,pi/2-a] the weight is at least sin(a), which controls the unweighted positive defect there. On the remaining angular strip, its positive part is at most tau_(n,j), whose sum is at most C(a+delta) by EB.6. First let n tend to infinity, then a tend to zero. This proves EB.10.

## 5. Exact progress and remaining boundary

PT3 removes the point-top exception. EB1 and EB.10 supply the exact balance of the finite exposure measures and their limit, without assuming differentiability of the full niche. They address two explicit obstacles in AR Section 9.

They do **not** supply the assertion that every admissible local tangent/corner contribution is globally exposed. The proposed saturated ODE sets the curvature equal to the largest local exposure bound. EB1 equates curvature to actual limiting exposure, which could be smaller when parts of the envelope are hidden or folded. That remaining identification must be proved or replaced by a valid inequality before SP1 can be invoked for a maximizing cap.

Even a completed weighted maximum remains an auxiliary one-turn theorem; the two-turn clipping/winding comparison still needs proof. No CI or Lean/Lake compilation, dependency installation, or manuscript build was used. These are self-reviewed written arguments with their historical dependencies stated, not independent or kernel verification.
