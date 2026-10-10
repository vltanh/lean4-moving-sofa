# An exact small-deficit obstruction to zero-loss in-place completion

**Scope.** The uploaded PC numerical family is not a continuum feasibility proof. This note gives a simpler exact example: a triangle has a partial lower turn with a small deficit and a full upper turn, but it fails a specified missing lower orientation. Completing its given canonical lower path deletes positive area. This validates the need for an error term in a general in-place completion argument. It does not prove the supplied near-reference family, preclude a different incoming orientation, or produce a competitive counterexample to optimality. Labels IC are local.

No computer-assisted result is a premise. A short preselected triangle screen suggested the constants; the proof below covers all relevant angles analytically.

## 1. A rational triangle and its endpoints

Set k=1/10, v=20/99, epsilon=2 arctan(k), and alpha=pi/2-epsilon. Consider

$$T=\operatorname{conv}\{A=(0,0),\ D=(1/10,1),\ F=(-1,20/99)\}.$$

It is compact, convex and connected. Its vertical span is one and its area is

$$|T|=\tfrac12(1+kv)=101/198.$$

The outgoing normal is n_alpha=(20/101,99/101). The scalar products of A,F with n_alpha are zero, and that of D is one. Hence T fits an outgoing unit strip at alpha. Its upper full-turn endpoint uses its incoming vertical span one.

For a normal pair u=(cos t,sin t), w=(-sin t,cos t), write the two canonical depths at p as h_T(u)-p dot u and h_T(w)-p dot w. A point is in its supporting hallway exactly when at least one depth is at most one. These pointwise conditions over a closed angular interval supply an actual continuous canonical motion, because supports and canonical translations are continuous.

## 2. Every visited lower orientation is feasible

Write c=cos t, s=sin t for 0<=t<=alpha. D maximizes the first support: its value is H=kc+s. Here H<=1, and F dot u=-X with X=c-vs>=0. For the second support, the values at D,F,A are Z=c-ks, Y=s+vc, and zero. Throughout this interval Z>=k>0 and Y>0.

If Z>=Y, the entire second directional width is Z<=1, so every point is protected by the second wall.

Otherwise the second support is Y, attained at F. It suffices to check the three edges: from any interior point, moving a short distance in direction -u-w increases both depths until a boundary point is reached. Thus a violation inside would imply one on an edge.

On AD the first depth is at most H<=1.

On FD, the two supports are attained at opposite endpoints. Their maximum smaller depth is at most

$$\frac{|D-F|}{2\sqrt2}<1,$$

by AB/(A+B)<=(A+B)/4<=sqrt(A^2+B^2)/(2 sqrt(2)) for its two nonnegative projection gaps. Here

$$|D-F|^2=(11/10)^2+(79/99)^2<2.$$

On AF, use p=zF, 0<=z<=1. The depths are H+zX and Y(1-z). If Y<=H, the second depth is already at most H<=1. Otherwise their crossing lies in the segment and the maximum smaller depth is

$$\frac{Y(H+X)}{X+Y}.$$

This is at most one precisely when X-Y(X+H-1)>=0. Put r=tan(t/2), so 0<=r<=9/11. Direct rational substitution gives

$$X-Y(X+H-1)
=\frac{(1-r)(9-11r)(5335+6811r-6345r^2)}{49005(1+r^2)^2}\ge0.$$

The first two factors are nonnegative. Since 0<=r<=1, the last is at least 5335+(6811-6345)r>0. This proves lower hallway containment for every t in [0,alpha]. No finite angular sampling is used.

## 3. The complete upper turn is feasible

It suffices to give the complete lower turn of the reflected triangle with vertices A=(0,0), D'=(k,-1), F'=(-1,-v). A translation of this reflected copy changes no support depth.

For t in [0,pi/2] its supports satisfy

$$h(u)=\max(0,kc-s)\le k,\qquad h(w)=\max(0,s-vc)\le s.$$

Put t_1=2 arctan(v). For 0<=t<=t_1,

$$s\le\sin(t_1)=3960/10201<2/5.$$

The sum of the two depths is affine in p. At A it is at most k+s<1/2. At D' it is at most

$$k+s+(1-k)c+(1+k)s\le1+(2+k)s<46/25<2.$$

At F' it is at most

$$k+s+(1+v)c+(v-1)s\le k+1+v+vs
<11/10+(7/5)(20/99)<2.$$

Hence the depth sum is below two throughout the triangle, so its smaller depth is below one.

For t>=t_1, h(u)=0 and the entire first directional width is

$$\max(s-kc,\ c+vs)\le1.$$

The first expression is at most s<=1. For the second, the half-angle variable tan(t/2)>=v gives c+vs<=1 directly. Thus the first wall protects the entire triangle for the rest of the quarter. This proves a full upper turn of the original T.

## 4. A missing lower angle definitely deletes material

Take

$$t_* = \pi/2-\arctan(1/10),$$

strictly between alpha and pi/2. Then cos(t_*)=1/sqrt(101) and sin(t_*)=10/sqrt(101). At the actual point A=(0,0), the first canonical depth is

$$D\cdot n_{t_*}=\sqrt{101}/10>1,$$

and the second is at least

$$F\cdot n_{t_*+\pi/2}=1010/(99\sqrt{101})>1,$$

where the latter strict comparison follows from 1010^2>99^2*101. Therefore A is strictly inside a missing forbidden quadrant. By continuity the same holds in a neighborhood of A, whose intersection with the nondegenerate triangle has positive area. Full in-place canonical completion consequently removes positive ordinary area.

Canonical support tightening also means that no alternative translation at this same missing orientation makes T fit; it is not merely failure of one chosen corner path. A different initial orientation or a different class of motion is not ruled out.

**Theorem IC1.** T is a genuine compact connected partial-lower/full-upper body of area 101/198, with missing angle epsilon=2 arctan(1/10), for which extending the given lower turn in place requires a positive loss of material. This deficit is smaller than the existing TE cutoff, but the body is far below competitive area. Thus the example shows the need for a completion allowance at small angles without asserting any no-gap theorem near M.

## 5. Relation to closure

The sharp circular-corner allowance CC remains an upper bound on the lost area. IC gives a rigorous nonzero-loss example; it does not assert saturation of CC's allowance, the supplied PC near-reference asymptotics, or impossibility of all other ways to complete turns. The full-turn sharp inequality and the corresponding partial-turn margin remain unproved.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation was used. These are self-reviewed hand arguments, with the canonical support formulation as their sole general motion dependency.
