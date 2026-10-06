# The square-root Hausdorff exponent cannot be improved

**Status:** analytic argument, not Lean-checked or independently reviewed. The statement concerns arbitrary closed connected moving sofas, for which interior holes are allowed. It does not assert sharpness of the constant in the cap theorem or sharpness within the monotone-cap class.

## Proposition

There is a family of moving sofas S_r, r decreasing to zero, such that

    M-|S_r|=pi*r^2,
    inf_g d_H(S_r,gG)=r,

where g ranges over orientation-preserving rigid motions. Consequently no uniform estimate d_rig(S,G)<=C(M-|S|)^p with p>1/2 can hold for all sufficiently near-optimal moving sofas.

## 1. Remove a small interior disk without disconnecting the sofa

Use the reference rectangle R=[a,b] x [H,1] contained in G, where H<1 is the maximum niche-roof height. Choose p in the interior of R and r>0 so small that the closed disk of radius r about p lies in the interior of R. Put

    S_r=G minus B_open(p,r).

This is closed, compact, and inherits a movement from G. It is connected: R minus the open disk is path connected and contains the boundary of R. Every point in the middle part of G below R can be joined vertically to R's lower boundary. The two convex wings can be joined to (a,H) and (b,H), respectively, without entering the disk. Thus all of S_r lies in a connected union. Its area is M-pi*r^2.

The identity alignment gives d_H(S_r,G)=r: p is at distance r from S_r, and every point in the deleted disk is within r of its boundary circle, which is retained.

## 2. Small rigid displacements cannot hide the missing disk

For any compact set X with nonempty interior and any p in its interior, there exists eta_p>0 such that

    d_H(gX,X)<eta_p implies p in gX                         (1)

for every rigid motion g. This statement is special to rigid copies, not to arbitrary Hausdorff-close sets.

To prove it, suppose g_nX tends to X but p is not in g_nX. Rotation angles lie in a compact circle, and translations are bounded since X is nonempty compact and the images remain in a fixed bounded neighborhood. Pass to g_n tending to g. Then gX=X. Therefore g^{-1}p belongs to the interior of X, and g_n^{-1}p also belongs to X for large n, a contradiction. The argument permits nontrivial rigid symmetries of X; no assumption about Gerver's stabilizer is needed.

Apply (1) to X=G. Choose r with 2r<eta_p. If some g had d_H(S_r,gG)<r, then

    d_H(gG,G)<=d_H(gG,S_r)+d_H(S_r,G)<2r<eta_p,

so p would belong to gG. But dist(p,S_r)=r, contradicting d_H(S_r,gG)<r. The identity alignment already attains r, so the infimum is exactly r.

## 3. Consequence

For p_exponent>1/2, the ratio

    d_rig(S_r,G)/(M-|S_r|)^p_exponent
       = pi^(-p_exponent) r^(1-2p_exponent)

tends to infinity. Thus the exponent 1/2 in 08-unrestricted-theorem.md is optimal for the Hausdorff metric on the stated class.

This example does not imply optimality of the square-root exponent for symmetric-difference area: for this family the symmetric-difference area is exactly the area deficit. It also does not constrain the best rate for monotone envelopes, since S_r is not a monotone sofa.
