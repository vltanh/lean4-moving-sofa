# Full turns with aligned positive faces: no length-one restriction

**Scope.** This proves the ordinary-area bound for every full-conventional-turn body with coincident nondegenerate top and bottom hull faces. The common face can have any positive length. It removes the old length-at-least-one restriction in this full-turn class. It does not cover a point face, nonaligned faces, or arbitrary partial turns. Labels FAS are local.

Inputs: the branch's analytic AW-W theorem through the scaling corollary SW1, canonical support tightening, and the written weighted inequality WV2 through SCG1. The new argument is elementary retained-point geometry and a rational polynomial identity. It uses no computer certificate or curvature premise. The prior weighted and width proofs still require independent review.

## 1. Reduction and notation

Let S be compact, connected, ambidextrous, with both full conventional quarter turns, in 0<=y<=1. Let K=conv(S) have vertical span one, projection [l,r] of width W, and identical horizontal top and bottom faces [a,b], with T=b-a>0. Face endpoints are extreme points of K and hence belong to S.

**Theorem FAS1.** Then

$$\boxed{|S|\le M.}\tag{FAS.1}$$

If W<=1001/500, SW1 already gives a strict bound below M. If T>=1, FL1 applies. It therefore remains to treat

$$W>1001/500>2,\qquad0<T<1.$$

The initial floor-trace exclusion, applied to the retained right endpoint b, gives b>=r-1. The final exclusion, applied to a, gives a<=l+1. Thus

$$r-a\ge W-1>1,\qquad b-l\ge W-1>1.\tag{FAS.2}$$

Choose actual extreme points P=(l,y_L), Q=(r,y_R). Define flank widths

$$k_L=a-l,\qquad k_R=r-b,\qquad W=T+k_L+k_R,$$

and Y_L=max(y_L,1-y_L), Y_R=max(y_R,1-y_R), each at least one half. Put

$$t_1=2\arctan T,\qquad c_1=\frac{1-T^2}{1+T^2},\qquad s_1=\frac{2T}{1+T^2}.$$

Here c1,s1 are positive because 0<T<1.

## 2. Feasibility bounds both flanks on a fixed angular interval

For every t in (0,t1),

$$T\sin t+\cos t>1.$$

The top point (a,1) therefore makes the second inner-wall gap strictly positive at the retained bottom point (b,0). To remain outside the lower forbidden quadrant, that bottom point must satisfy the first wall. Testing the actual right extreme Q against that wall gives

$$k_R\cos t+y_R\sin t\le1.$$

Use the reflected upper motion and the retained top point (b,1) to replace y_R by 1-y_R. Together,

$$\boxed{k_R\cos t+Y_R\sin t\le1\quad(0<t<t_1).}\tag{FAS.3}$$

For the left flank, use lower angles pi/2-t and the retained point (a,0). The top point (b,1) now strictly violates its first inner wall, so the second must be safe. The left extreme P gives k_L cos t+y_L sin t<=1. Reflection gives 1-y_L. Hence

$$\boxed{k_L\cos t+Y_L\sin t\le1\quad(0<t<t_1).}\tag{FAS.4}$$

Full turns are used in the left-flank argument near the terminal angle. They are not inserted as a consequence of the calculations. Continuity extends FAS.3--FAS.4 to t=t1.

## 3. A face too short would already force width at most two

Since Y_L,Y_R>=1/2, the endpoint inequalities give

$$W\le T+2\frac{1-s_1/2}{c_1}.$$

The difference of this last expression from two is exactly

$$\frac{T(4T-T^2-1)}{1-T^2}.\tag{FAS.5}$$

For 0<T<=2-sqrt(3), it is nonpositive. This contradicts W>2. Therefore T>2-sqrt(3), so t1>pi/6. Evaluating FAS.3--FAS.4 at pi/6 yields

$$\boxed{k_L,k_R\le\sqrt3/2.}\tag{FAS.6}$$

This conclusion is not a curvature or diameter assumption. It is forced by the opposite full-height face endpoint and both actual motions.

## 4. Failure of a clipping certificate would force a width below 2.002

Use m_R=1-Y_R in the right-hand SCG condition. Since r-a=T+k_R, its failure is equivalent to

$$2T(T+k_R)+(1-Y_R)(1-T^2)\le1+T^2$$

or

$$k_Rs_1\le Y_Rc_1.\tag{FAS.7}$$

But the endpoint of FAS.3 says k_R c1+Y_R s1<=1. Since c1,s1>0, FAS.7 gives Y_R>=k_R s1/c1, and substitution gives k_R/c1<=1. Thus k_R<=c1. Together with FAS.6,

$$W\le T+c_1+\sqrt3/2.\tag{FAS.8}$$

The same estimate holds if the left SCG condition fails instead.

The following rational bound holds for every 0<=T<=1:

$$T+\frac{1-T^2}{1+T^2}<\frac{227}{200}.\tag{FAS.9}$$

Here is a direct identity proving it. Put x=T-3/10. The positive numerator of the difference is

$$\begin{aligned}
200(1+T^2)\left[\frac{227}{200}-T-\frac{1-T^2}{1+T^2}\right]
&=27-200T+427T^2-200T^3\\
&=107\left(x+\frac{11}{1070}\right)^2
+200(1-T)x^2+\frac2{107}>0.
\end{aligned}\tag{FAS.10}$$

Also sqrt(3)/2<13/15, since 169/225-3/4=1/900>0. Therefore any failed SCG condition would imply

$$\boxed{W<227/200+13/15=1201/600<1001/500.}\tag{FAS.11}$$

The last rational difference is 1/3000. This contradicts the remaining width regime. Consequently both strict short-chord inequalities SCG.1 hold. Their additional R>1 and B>1 hypotheses are FAS.2.

## 5. The actual area bound

All six SCG witnesses are actual retained points, and both inequalities have now been derived from feasibility rather than assumed. SCG1 proves that both positive niches lie over [a,b], hence inside K, without clipping. Connectedness excludes their overlap along any vertical fiber. The two-cap identity consequently reduces to

$$|S|\le\Psi(U)+\Psi(V)\le M,$$

where the last step is the universal weighted bound WV2. This proves FAS1.

The proof uses the old strict width gap only to absorb the small possible range in FAS.11. No numerical maximum of T+c1 was used; FAS.10 is an exact sum-of-nonnegative-terms identity.

## 6. What has and has not been removed

The common face no longer needs length at least one, nor a previously assumed curvature bound, endpoint height range or special contact pattern. The full-turn aligned class with T>0 is now covered.

The case T=0 remains different: the small-angle safety interval t1 disappears, and the initial/final floor tests no longer force a<=l+1 and b>=r-1. It is not legitimate to take T down to zero within this proof while keeping W>2. Nor is an arbitrary partial-turn body admitted by pretending the left-flank terminal tests were visited.

Nonaligned face configurations and the point-face class still need an ordinary-area comparison or a valid improving operation at a maximizer. This is a conditional-case closure, not unrestricted optimality. No CI, Lean/Lake compilation, dependency installation, manuscript build or long computation is used.
