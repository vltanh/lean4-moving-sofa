# Extra certified hallway angles from the extreme-point anchors

This is an ordinary-area certificate input, not a curvature theorem. It improves the previously used fixed angle list and corrects two unjustified implications in the preceding suggested roadmap. Labels AA are local. Baseline: fcb13c5c07592f54281783cbb77e8cae9721850d.

## 1. Geometry and the only prior motion input

Let S be a compact connected ambidextrous body in 0 <= y <= 1, of area greater than 8/5. Use the common incoming coordinates of the branch's canonical-motion reduction. Its conventional lower and upper endpoint magnitudes alpha,gamma lie in (arccos(5/8),pi/2]. The outgoing strips have normals (cos(alpha),sin(alpha)) and (cos(gamma),-sin(gamma)), respectively.

Translate the horizontal projection to [0,W]. Compactness supplies actual body points P=(0,a), Q=(W,b), with 0 <= a,b <= 1. Put d=a-b. The necessary terminal-strip inequalities are

$$
|W\cos\alpha-d\sin\alpha|\le1,\qquad
|W\cos\gamma+d\sin\gamma|\le1.
$$

These use actual retained points, not arbitrary vertices of an enclosing rectangle.

## 2. A uniform test on a parameter box

Suppose W is in [w0,w1], a in [a0,a1], and b in [b0,b1], with w0>0. Write d0=a0-b1 and d1=a1-b0. For a rational half-angle parameter r in (0,1), set

$$
c=(1-r^2)/(1+r^2),\qquad s=2r/(1+r^2),\qquad t=2\arctan r.
$$

**Lemma AA1.** The lower turn must visit angle t if either c>=5/8 or w0*c-d1*s>1. The upper turn must visit magnitude t if either c>=5/8 or w0*c+d0*s>1.

**Proof.** The first alternative is the prior endpoint bound. For the other lower alternative, consider f(v)=W cos(v)-d sin(v) on [0,t]. Its minimum on that interval is attained at an endpoint. One direct justification is that f'=-W sin(v)-d cos(v). If d>=0 it is strictly negative in the interior. If d<0, its sole possible interior zero is a maximum, since f''=-f<0 there. At the endpoints f(0)=W and f(t)>1. The strict inequality f(t)>1 with |d|<=1 and 0<t<pi/2 also implies W>0, but for the application below we explicitly use W>2, already supplied for competitive maximizers by AW-W. Thus f(v)>1 for every v in [0,t]. If alpha<=t the outgoing lower strip would have width greater than one on P,Q, a contradiction. Hence alpha>t. Replace d by -d for the upper turn. QED.

For use beyond the W>2 class, require w0>1 in the second alternative. The fixed-angle alternative needs no such extra width assumption. Every extended certificate invoking the second alternative must check this width precondition.

All comparisons are rational. The lower/upper angles may be different; no reflected-motion assumption is made. A failed angle test is simply not permission to use that frame. It does not prove the angle was not visited.

## 3. How the test strengthens exact area certificates

Conditioning on P,Q already gives singleton and pair occupation inequalities from the forbidden-triple equivalence. AA1 adds further frames to those inequalities. The certificate checker should reconstruct the interval endpoints, the rational c,s, and the appropriate signed anchor test for every frame. It must not trust an angle selected by a floating-point optimizer.

The original four angles with half-angle parameters 1/5,3/10,2/5,12/25 remain valid. This extension does not change the logical status of a dual bound: any finite collection of rigorously verified inequalities gives an ordinary-area upper bound, whether or not the proposing linear program was solved optimally.

## 4. Corrections to the previously suggested closing chain

Small |a-b| alone does not imply a and b are close to 1/2. It only places them near the diagonal of [0,1]^2. Mid-height localization needs a separate estimate involving their common height.

Also, the arm reduction AR6 concerns maximizers of the signed one-turn objective Psi, not arbitrary ambidextrous maximizers. Certifying small arm distances for a two-turn body does not authorize applying the weighted-maximizer curvature theorem to it. A valid connection between those optimization domains would still be necessary.

Consequently the direct computational target remains actual two-turn area. No computer localization will be declared complete merely because surviving boxes satisfy these weaker endpoint conditions. A local finishing theorem must apply to the exact residual class that the certificate describes.

## 5. Execution and scope

The inequalities above have a pen-and-paper proof. Numerical search can choose which of them to use, but is not a premise. No CI or Lean/Lake compilation was used. The prior unpublished anchor certificate was freshly replayed in this continuation and retained its two restricted-bin bounds; it does not cover the whole width/height domain. The unrestricted optimal value remains unproved.
