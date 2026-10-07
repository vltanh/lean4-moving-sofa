# Central short faces: three explicit ordinary-area extensions

**Scope.** This applies the six-point strip lemma SCG to a class not covered by LF1: both horizontal faces span the central interval, but their lengths may be less than one. Their alignment and full turns are derived rather than assumed. The sharp area step uses the existing written weighted theorem WV2 through SCG1. Labels CSF are local. Unrestricted optimality remains open.

## 1. The geometric class and threshold

Let S be compact, connected and ambidextrous in the common unit-height incoming strip. Write K=conv(S), its horizontal projection as [l,r], and W=r-l>2. Suppose both its top and bottom horizontal faces contain the interval

$$[l+1,r-1].\tag{CSF.1}$$

This is an inclusion of intervals in the two exposed faces. It does not claim that their interiors belong to S.

Choose actual extreme points P=(l,y_L), Q=(r,y_R) of S. For some 0<=m<=1/2 suppose

$$m\le y_L,y_R\le1-m.$$

Define

$$w_m=2+\frac{\sqrt{1+(1-m)^2}-1}{1-m}.$$

**Theorem CSF1.** If W>w_m and CSF.1 holds, then

$$\boxed{|S|\le M.}\tag{CSF.2}$$

No curvature, smoothness, symmetry, full-turn or weighted-maximizer premise on S is used. The conclusion is conditional on the stated face and witness geometry, not a claim that every remaining maximizer has it.

Useful exact cases are:

| Extreme-height information | Sufficient width |
|---|---|
| None beyond 0<=y_L,y_R<=1 | W>1+sqrt(2) |
| Both extreme witnesses in [1/4,3/4] | W>7/3 |
| Both extreme witnesses at height 1/2 | W>sqrt(5) |

These are identities for w_m at m=0,1/4,1/2. They are not numerical rounding of thresholds.

## 2. Initial angles force a common left endpoint

For |S|<=8/5, the conclusion follows from M>8/5. Assume |S|>8/5, so the conventional initial turns are available from the earlier motion reduction.

Write the top and bottom face intervals as [a_+,b_+], [a_-,b_-]. Their endpoints are extreme points of K and hence actual points of S. By CSF.1,

$$a_+,a_-\le l+1<r-1\le b_+,b_-.$$

The initial floor-trace exclusions OT3, also proved in LF Section 1, say that a_- is not in (a_+,r-1), and a_+ is not in (a_-,r-1). Since both left endpoints are strictly below r-1, they must coincide. Put

$$a=a_+=a_-,\qquad b=\min(b_+,b_-),\qquad T=b-a.$$

Then K contains [a,b] times [0,1], the two points (a,0),(a,1) are retained, and

$$T\ge W-2,\qquad r-a\ge W-1,\qquad b-l\ge W-1.\tag{CSF.3}$$

At this stage b may lie in the interior of one face; its two points at heights zero and one are only known to belong to K. They will not be used as retained points before alignment is proved.

## 3. The strict strip test is positive on the entire allowed T interval

If T>=1, the common rectangle contains a unit square and forces both reduced turns to be full, exactly as in FL. Suppose 0<T<1. Then x=W-2 belongs to (0,1) and T in [x,1). Consider

$$H(T)=2T(W-1)+m(1-T^2)-(1+T^2).$$

This is concave as a function of T. At its two bounding endpoints,

$$H(x)=(1-m)x^2+2x-(1-m),\qquad H(1)=2x>0.\tag{CSF.4}$$

The positive zero of the first quadratic is precisely w_m-2. Hence W>w_m makes H(x)>0. Concavity then gives H(T)>0 throughout [x,1]. In particular

$$2T(r-a)+\min(y_R,1-y_R)(1-T^2)>1+T^2,$$

and the analogous left inequality follows from CSF.3. Also r-a,b-l>1.

Apply the strip lemma SCG.3 to the top point (b,1) of K and actual right extreme Q. Together with the retained lower point (a,0), it proves that the width of K in every possible lower outgoing interior normal is greater than one. Reflection proves the same for the upper outgoing normals. Thus both reduced turns are full. This part requires (b,1) in K, not in S, since it is only a support-width estimate.

## 4. Full turns force the right endpoints to agree

Now use the final floor-trace exclusions. Both b_+,b_- are at least r-1>l+1. The retained bottom right endpoint cannot lie in (l+1,b_+), so b_->=b_+. The reflected exclusion gives b_+>=b_-. Therefore

$$b_+=b_-=b.$$

All four corners at a,b are now actual retained points. The faces coincide. If T>=1, FL1 applies. If T<1, the two strict SCG inequalities already proved in Section 3 apply. SCG1 confines both positive niches to (a,b), gives zero clipping and proves the ordinary-area bound. This proves CSF1.

The order of these steps matters: an interior point of a hull face is not automatically in the actual body. The width argument precedes the use of the two right face endpoints as forbidden-quadrant witnesses.

## 5. Nonvacuous parameter enlargement, and remaining cases

For example W=12/5, a=l+1, b=r-1 and y_L=y_R=1/2 give a common face of length 2/5. These support parameters pass SCG with margin 19/50. Thus the sufficient class genuinely permits face lengths less than one; LF1's two-long-face hypothesis is not being restated.

At a width near the reference width, the condition with extreme heights in [1/4,3/4] is sufficient whenever both faces span [l+1,r-1] and W>7/3. This is a conditional region, not an independently proved localization of every optimizer to those heights or face positions.

The theorem does not cover a point face: W>2 makes the central interval have positive length. It also does not cover all shifted, one-sided, or very short faces, nor all widths between two and w_m. It supplies no universal positive gap below M on those remaining families.

Sections 2--4 are hand proofs using support bounds, elementary concavity and retained endpoints. The sharp constant depends on the branch's self-reviewed WV chain. A short rational checker verifies the displayed polynomial identities, but is not needed for their proof. No long computation, CI, Lean/Lake compilation, dependency installation or manuscript build is used.
