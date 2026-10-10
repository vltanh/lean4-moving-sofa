# Five rational anchor tests localize competitive widths below three

**Scope.** This publishes the pen-and-paper result previously supplied in `optimality_anchor_followon.zip`. It is a width localization, not a proof of the optimal value. It uses actual extreme points and connectedness, with no curvature, symmetry, full-quarter-turn, or auxiliary enclosure premise. Labels AL are local.

Use the common incoming coordinates of the established motion reduction in Notes 8--10: S is compact, connected, ambidextrous, and lies in 0<=y<=1. If |S|>8/5, its conventional endpoint magnitudes both exceed arccos(5/8). Only that elementary motion reduction is imported here.

## 1. Actual extreme-point witnesses

Translate the projection to [0,W]. Compactness gives

$$P=(0,a),\quad Q=(W,b)\in S,\qquad a,b\in[0,1],\quad d=a-b.$$

Connectedness makes the full interval [0,W] the projection. Use half-angle parameters

$$r\in\{1/5,3/10,2/5,12/25\},\qquad
(c_r,s_r)=((1-r^2)/(1+r^2),2r/(1+r^2)).$$

Every such angle is visited by both turns: the smallest cosine is 481/769>5/8, since 8*481-5*769=3.

If W<=12/5 the final conclusion already holds. Otherwise W exceeds the tangent and cotangent of every selected angle. The two-point supports in the lower frame u_t=(c_t,s_t), v_t=(-s_t,c_t) are

$$A_t=Wc_t+bs_t,\qquad B_t=ac_t.$$

In the upper frame e_s=(c_s,-s_s), j_s=(-s_s,-c_s), they are

$$A_s^+=Wc_s-bs_s,\qquad B_s^+=-ac_s.$$

These formulas follow by comparing P and Q. The largest selected cotangent is 12/5 and the largest tangent is 600/481<12/5. The forbidden quadrants defined using these supports minus one are subsets of the actual body's canonical forbidden quadrants, so S avoids them.

## 2. Opposite-turn anchored quadrants must be disjoint

If a lower and upper anchored open quadrant intersect at an abscissa in [0,W], downward and upward closure make their union cover the whole vertical line. This contradicts the projection property of S.

Intersection is impossible at x<=0: their companion-wall inequalities require

$$y<a+x\tan t-\sec t,\qquad y>a-x\tan s+\sec s.$$

At x>=W their other walls require

$$y<b+(W-x)\cot t-\csc t,\qquad y>b+(x-W)\cot s+\csc s.$$

Hence for every selected ordered pair,

$$\boxed{Q_-(t)\cap Q_+(s)=\varnothing.}\tag{AL.1}$$

Actual extreme witnesses and connectedness are essential here.

## 3. Exact disjunction

Put lambda=t+s, S_lambda=sin(lambda)>0, C_lambda=cos(lambda). A separating normal has nonnegative scalar products with u_t,v_t and nonpositive scalar products with e_s,j_s. These normals form a pointed cone. Its two extreme rays suffice to test separation, since every other such normal is their nonnegative combination. Equivalently eliminate y and x from the four strict wall inequalities.

For C_lambda>=0, the extreme rays are -j_s and v_t. Put K=1+(1+C_lambda)/S_lambda. Disjointness is equivalent to

$$Wc_t-ds_t\le K\quad\text{or}\quad Wc_s+ds_s\le K.$$

For C_lambda<0 the extreme rays are u_t and -e_s. Put K=1+(1-C_lambda)/S_lambda. The disjunction is

$$Ws_s-dc_s\le K\quad\text{or}\quad Ws_t+dc_t\le K.$$

Thus

$$W\le F_{t,s}(d):=
\begin{cases}
\max(K/c_t+d s_t/c_t,\ K/c_s-d s_s/c_s),&C_\lambda\ge0,\\
\max(K/s_s+d c_s/s_s,\ K/s_t-d c_t/s_t),&C_\lambda<0.
\end{cases}\tag{AL.2}$$

For example the first separating dot product in the second case equals S_lambda*(K-W*s_s+d*c_s); substituting the displayed two-point supports gives the others. All coefficients are rational. Equality is permitted because the quadrants are open.

Since F_(t,s)(-d)=F_(s,t)(d) and every ordered pair is available, it suffices to cover 0<=d<=1. Each F is a maximum of two affine functions, so its maximum on an interval is at an endpoint.

## 4. Five rational cases

| d interval | tan(t/2) | tan(s/2) | maximum of F on the interval |
|---|---:|---:|---:|
| [0,1/10] | 2/5 | 2/5 | 1229/420 |
| [1/10,1/4] | 2/5 | 12/25 | 59069/20200 |
| [1/4,1/3] | 3/10 | 2/5 | 9311/3185 |
| [1/3,16/25] | 3/10 | 12/25 | 275521/93795 |
| [16/25,1] | 1/5 | 12/25 | 2999/1020 |

The first four values are below the last by, respectively,

$$5/357,\quad16471/1030200,\quad10919/649740,\quad5773/2126020.$$

For the last row the two affine functions are

$$429/170+(5/12)d,\qquad152262/40885-(600/481)d.$$

Their endpoint values give 2999/1020, attained by the first at d=1. The five intervals cover [0,1] with no gaps.

**Theorem AL1.** Every body satisfying the stated motion reduction with |S|>8/5 obeys

$$\boxed{W\le2999/1020<3.}$$

Proof: widths at most 12/5 already qualify; otherwise use AL.1 and the covering in AL.2. Together with the separate analytic exclusion AW-W, this places normalized maximizers in 2<W<=2999/1020. It does not imply closeness in shape to the candidate.

## 5. Replay and provenance

The original bundle's `check_anchor_width.py` was freshly executed in this continuation. It reproduced all five exact rows, 10,368 independent rational quadrant tests and 272 touching cases, and rejected four incorrect formula/coverage controls. Its SHA-256 is `58f087095d78c7b82ac1d681c8fc0bf34ef5ff2b76952ccbd97773ce394c4375`.

The continuum proof is the five-case argument above, not those finite regression samples. The original bundle also contains the separate restricted ordinary-area certificate and its exact replay. Publication here does not assert an unrestricted area bound. No CI or Lean/Lake compilation was used. The proof and software remain subject to independent review.
