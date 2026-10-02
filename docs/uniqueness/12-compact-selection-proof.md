# 12. Compact selection of a specified maximizing cap

Date: 2026-10-02. Paper proof. This supplies the approximation and selection hypotheses used in the two variational reductions. No assertion about limits of exact unpenalized maximizers is made.

## Notation

Let L=pi/2 and fix 0<omega<=L. A standard cap is a nonempty compact convex set with upper strip supports h(omega)=h(L)=1, lower supports h(omega+pi)=h(3L)=0, and defining normal directions in

    J_omega union {omega+pi,3L},
    J_omega=[0,omega] union [L,L+omega].

Repeated strip conditions are identified when omega=L. Let

    Theta_n={j delta_n:1<=j<2^n},  delta_n=omega/2^n.

Let C_n(K) be the circumscribed cap using the two fixed strips and the sampled upper supports at Theta_n and Theta_n+L. Let N_n(K) be the fan intersected with the union of the corresponding open inner quadrants. Put

    A_n(K)=|C_n(K)|-|N_n(K)|,
    A(K)=|K|-|N(K)|.

These are the corrected cap/fan definitions in the repository; the fan is not replaced by the bounded parallelogram.

## 1. Compact cap families

When omega<L, let X be all standard omega-caps. They lie in the fixed parallelogram

    P_omega={0<=y<=1, 0<=p.u_omega<=1}.

They contain the fixed triangle with vertices O=(0,0), (c,0), o=(c,1), where c=sec(omega)-tan(omega)>0. Indeed the adjacent top supporting normals omega,L meet at o, which belongs to every cap by consecutive-normal geometry. For each allowed upper normal s, o.u_s>0, so O satisfies every defining inequality. Moving o vertically down to (c,0) decreases the upper scalar products and stays in the lower fan. Convexity supplies the triangle. Fix a ball B(q,rho) in its interior. Both q and rho>0 depend only on omega.

When omega=L, fix the target K_* and choose R so that its horizontal projection is strictly inside (-R,R). Let X be all standard right-angle caps inside [-R,R] x [0,1]. Degenerate vertical segments are allowed in X.

In either case X is compact in Hausdorff distance. Boundedness gives subsequential compactness for nonempty compact convex sets. Strip supports are preserved by uniform convergence of support functions. The restriction on allowed normal directions is closed: in the full-dimensional case use weak convergence of curvature measures, whose support stays in the fixed closed set of allowed normals. In the right-angle case this also follows directly from downward closure above y=0, which is preserved under Hausdorff limits; downward closed convex sets are intersections of their upper supporting half-planes and y>=0. This argument includes degenerate vertical limits.

Let X_n be the polygon caps of this mesh lying in X. These are closed subfamilies and hence compact. The finite-intersection continuity argument in section 3 proves closedness directly as well. For the right-angle target, X_n is nonempty for all sufficiently large n because C_n(K_*) eventually lies inside the box.

## 2. Niche areas converge uniformly

### Right angle

For x in [-R,R] and 0<t<L define the height of one wedge by

    F(K,x,t)=max(0,min(
      (h_K(t)-1-x cos(t))/sin(t),
      (h_K(t+L)-1+x sin(t))/cos(t))).

No wedge above the x-axis has an abscissa outside [-R,R]. For example h_K(t)<=R cos(t)+sin(t) implies that its right intercept is at most R+(sin(t)-1)/cos(t)<R; the left estimate is its reflection.

The supports are uniformly Lipschitz because all caps are in one bounded box. Since h_K(L)=1, the second threshold is at most C_R t near t=0, uniformly in K,x. The first is at most C_R(L-t) near t=L. Thus F extends jointly continuously by zero at t=0,L. Notice that this uses the MINIMUM of the two thresholds; neither threshold individually has a continuous endpoint extension.

The full niche height is max_[0,L] F and the finite niche height is max over the mesh including endpoints. Uniform continuity on the compact space X x [-R,R] x [0,L] proves their uniform convergence in K,x. Integration over x proves uniform convergence of niche areas. Strict versus non-strict boundary inequalities do not change these areas.

### Fixed smaller angle

Put e_-=u_0-v_omega and e_+=u_0+v_omega. Write points of the fan uniquely as

    p=s e_-+r e_+,   r>=|s|.

The determinant of this coordinate change is 2 cos(omega)>0. The coefficients of r in p.u_t and p.v_t are

    a(t)=cos(t)-sin(omega-t),
    b(t)=cos(omega-t)-sin(t).

They are strictly positive for 0<=t<=omega, with a positive minimum depending on omega. For example

    a(t)=(1-sin omega)cos t+cos omega sin t>0;

for b(t), positivity follows from b(t)=cos omega cos t-(1-sin omega)sin t and tan t<=tan omega<cos omega/(1-sin omega).

Each inner quadrant therefore cuts out an interval |s|<=r<T(K,s,t), where T is the minimum of two continuous affine thresholds divided by a(t),b(t). The wedge height is (T-|s|)_+. At t=0,omega it is zero, since the corresponding quadrant lies strictly outside one boundary of the fan.

There is a uniformly bounded relevant s-range. At r=|s|, if s>=0 then p=2s u_0 and p.u_t>=2s cos omega. If s<0 then p=-2s v_omega and p.v_t>=2|s| cos omega. Increasing r increases both scalar products. Bounded supports consequently bound |s| whenever the wedge is nonempty. The positive lower bounds for a,b then bound its r-height as well.

We now have continuous wedge heights on a common compact parameter space. Taking full versus sampled maxima and integrating with the fixed Jacobian proves uniform niche-area convergence exactly as above. This also proves continuity of |N(K)| on X.

## 3. Circumscribed cap areas converge uniformly

For each K, the sets C_n(K) decrease to K: the sampled normal directions are nested and dense in J_omega, and support functions are continuous. They are uniformly bounded. For omega<L they lie in P_omega; for omega=L the constraints at delta_n and pi-delta_n put them in a slightly enlarged fixed box, since delta_n<=pi/4 for n>=1.

For each FIXED n the finite intersection C_n(K) depends continuously on K. For omega<L the common interior ball in section 1 gives this by the elementary homothetic perturbation estimate. For omega=L, choose a top contact point (x_0,1) of K. The point (x_0,1/2) is strictly inside every finite defining half-plane: at each sampled upper normal s in (0,pi) its slack is at least sin(s)/2, and its bottom slack is 1/2. Thus C_n(K) has an interior ball of radius bounded below for this fixed mesh, even when K is a vertical segment. The finite-half-plane continuity estimate again applies.

Area is continuous under Hausdorff convergence of compact convex planar sets, including degenerate ones. One elementary proof uses convergence of membership off the boundary for a full-dimensional limit; that boundary has area zero. For a degenerate limit, the approximating bodies lie in arbitrarily thin neighborhoods of a segment, and their areas tend to zero.

Consequently the continuous functions K->|C_n(K)| decrease pointwise to the continuous function K->|K| on compact X. Dini's theorem proves uniform convergence. Combining with section 2 yields

    e_n=sup_X |A_n-A| -> 0,    A_n>=A.                         (1)

The latter order follows from C_n(K) containing K and N_n(K) contained in N(K).

The same fixed-mesh interior argument shows that X_n is closed: if polygon caps K_j of this mesh converge in X, then K_j=C_n(K_j) implies K=C_n(K).

## 4. Recovery and selection

Suppose K_* globally maximizes A and write M=A(K_*). Set r_n=C_n(K_*). For all sufficiently large n, r_n belongs to X_n. At every sampled or pinned normal its actual support equals h_{K_*}: inclusion of K_* gives one inequality and the defining constraint gives the other. Hence

    A_n(r_n)=A_n(K_*)>=M,   r_n->K_*.

Let

    P(K)=integral_0^(L+omega) (h_K-h_{K_*})^2.

P is continuous and nonnegative. P(K)=0 implies equality of the continuous supports on J_omega; together with the fixed lower defining heights, these identify the cap, so P(K)=0 iff K=K_*.

Choose lambda_n>0 with lambda_n->0 and e_n/lambda_n->0. For example lambda_n=sqrt(e_n)+1/n works. Choose an exact maximizer K_n of A_n-lambda_n P on compact X_n. Comparing it with r_n gives

    A_n(K_n)-lambda_n P(K_n) >= M-lambda_n P(r_n).

On the other hand A_n(K_n)<=A(K_n)+e_n<=M+e_n, because K_* is a GLOBAL maximizer of A. Therefore

    0<=P(K_n)<=P(r_n)+e_n/lambda_n ->0.                         (2)

Every cluster point in X has penalty zero and is K_*. Compactness therefore gives K_n->K_* for the whole sequence.

For omega=L the artificial horizontal box constraints are eventually inactive, since K_* has a strict horizontal margin. Thus all sufficiently small floating-facet perturbations at each sufficiently large n are legitimate competitors. There is no need to assert that K_n is an exact maximizer of A_n or a balanced polygon.

## Dependency boundary

This proof uses only compact convex geometry, explicit wedge coordinates, finite intersections, continuity of area, and Dini's theorem. It does not use cap rigidity or injectivity. It does not assume that every maximizer is approximated by exact unpenalized maximizers; note 03 shows that this assumption would be false in general.

The cap, circumscribed-cap and fan-niche definitions are those of `MovingSofa/Monotone/CapDefs.lean` and `MovingSofa/Balanced/PolygonCap.lean`. The new selection argument is independent of the repository's definition of `IsBalancedMaxCap`.
