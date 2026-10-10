# Review of the supplied minimum-width-frame package

**Status.** The package gives a useful same-body change of frame and an exact signed area identity. It does not prove the universal full-turn upper bound. The preceding partial-turn package has already been reviewed in `partial-turn-package-audit.md`; its sharpened circular allowance is in `circular-corner-completion-bound.md`. This review does not take credit for those earlier commits.

Attribution is to the user-supplied `minimum-width-frame-package.zip`; no author name was supplied. Review baseline: `ce0a2c2de9071be1e385756bf9f590453e782e73`. The archive and all original files, including the author's output, are preserved unchanged in the session reproduction bundle. The review's executed output is separate.

## 1. Input identity and actual replay

Archive SHA-256: `21bc2d3b71b1deac325b94faca87d1eaac3d0849a012a0d689049f026f6eeff8`.

Original files, relative to `docs/ambidextrous/`:

| File | SHA-256 |
|---|---|
| `minimum-width-frame.md` | `8b2c7d27b0b8fd9d54c230b06f5688d05177196155c225d3efebf391a18c4007` |
| `computer-assisted/minimum-width-frame/check_minimum_width_frame.py` | `05451e2cbad40c25612fd263569ed1d2c16a909010f0a37b92b65bbb0c92ec69` |
| `computer-assisted/minimum-width-frame/README.md` | `8fc3eb722c49fc1cc8efb733197aa7863b289e6aec90530428992242052f820a` |
| `computer-assisted/minimum-width-frame/minimum-width-frame-checks.json` | `a1075bf816c38ca71828dd571515d197aa2932205b1684b9ae862b966a6bd647` |

The original checker ran unchanged in an external eight-second subprocess cap, with `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`. It exited normally under Python 3.13.5 and reported 1.86 seconds internally. All 200 exact Fraction angle cases passed. Its five prescribed floating-point hard-family cases and offset-face control reproduced the stated pattern. Maximum absolute slack-identity residual was 4.440892098500626e-16. The offset-face control had G_s approximately 0.0047449923, not a nonpositive correction; this is a diagnostic, not an independently certified body at its true minimum width.

The fresh output's script hash matches the supplied script. Passing finite samples does not verify the continuum motion, minimum orientation, face detection, or area signs. In particular this is not a numerical proof of G_s<=0 on arbitrary caps.

## 2. Same-body minimum-width frame and overlapping faces

Let a compact connected body S have both complete conventional turns. Let J be the connected component of its safe-strip directions, w(theta)<=1, containing its incoming normal. The existing SI2 transports both full motions along J without changing S or its area. Choose a direction minimizing w on J and write that width as H=1-s, with 0<H<=1. Rotate and translate, without stretching, so the actual hull lies between y=s and y=1 and touches both.

Let its top face be [a,b] at height one and its bottom face [c,d] at height s. The support-derivative identities give

$$w'(L-)=c-b,\qquad w'(L+)=d-a,\qquad L=\pi/2.$$

At the chosen minimum, these imply

$$\boxed{c\le b,\qquad a\le d.}$$

Thus the horizontal face intervals overlap. This is the genuinely useful contrast with evaluating at a boundary of J, where the same body's faces can be at opposite ends. It does not say the faces coincide, have positive length, or contain a specified central interval.

**Qualification to the supplied justification.** The sentence `w>1 off J` is not true globally: there may be other safe-strip components. If min_J w<1, the minimum is interior and is a local minimum, so the argument is valid directly. If min_J w=1 and J is nontrivial, choose an interior point where w is constant. If J is a singleton, a positive left derivative or a negative right derivative would place a whole adjacent interval in {w<1}, contradicting singleton connectedness. This gives the same two derivative signs. The overlap conclusion survives without claiming all directions outside J are unsafe.

For competitive bodies the analytic AW-W width exclusion must be reapplied in this transported frame, whose incoming height is at most one; the horizontal width is not assumed unchanged by rotation.

## 3. The signed slack identity is correct

Write the actual convex-hull fibers as [B(x),A(x)] over I=[l,r], W=r-l. Form the two height-one downward caps with roofs A and 1+s-B. The second is obtained from the reflection (x,y)->(x,1+s-y), not the old reflection about y=1/2. Let n_U,n_V be their complete positive niche roofs.

The actual full canonical envelope containing S has nonempty interval fibers

$$[\max(B,n_U),\ \min(A,1+s-n_V)].$$

Define Psi(C)=area(C)-area(N(C))-W(C)/2. Elementary max/min algebra gives

$$\boxed{|E|=\Psi(U)+\Psi(V)+G_s,}$$

$$\boxed{G_s=\int_I[\min(n_U,B)+\min(n_V,1+s-A)]\,dx-sW.}$$

Unlike the unit-span correction G_0, G_s can be negative. Setting

$$T_s=\int_I[\min(n_U,s)+\min(n_V,s)]\,dx,$$

$$C_s=\int_I[(\min(n_U,B)-s)_++(\min(n_V,1+s-A)-s)_+]\,dx,$$

one obtains exactly

$$G_s=T_s+C_s-sW,\qquad C_s\ge0.$$

The negative slab term is only **sW**, not 2sW: there are two sub-slab integrals, but the cap-width penalties and the containing strip height leave the one stated subtraction. With Delta=M/2-Psi, the existing written weighted theorem gives |S|<=M-Delta(U)-Delta(V)+G_s. No area is gained by an unproved affine normalization.

## 4. Reviewed conditional geometric estimates

The package's eight endpoint disjunctions follow by testing one retained face endpoint against the hallway at t=arccos(1-s) or its complementary angle. With sigma=sqrt(2s-s^2), r0=1/(1-s), their useful consequences are

$$a,c<r-r_0\Longrightarrow |a-c|\le\sigma,$$

$$b,d>l+r_0\Longrightarrow |b-d|\le\sigma.$$

These are conditional near-alignment estimates, not automatic centrality. The unit end intervals become wider when H=1-s decreases; call them intervals of width r0, not literally unit intervals when s>0.

The supplied MW7 confinement proof also works: its early-angle test uses the exact threshold tan(t/2)<=1-s; its remaining angles use the lower bound tan(pi/4-u/2)>=1-u. Under the four stated central-face conditions (H1)-(H2), it proves C_s=0. Then a sufficient remaining criterion is

$$T_s\le sW,$$

which follows if the two niche footprint lengths total at most W. Neither footprint bound nor central-face admission has been proved for every competitor. At s=0, overlapping positive faces reduce to the already covered aligned-face case; point-face endpoint configurations remain.

## 5. Numerical qualifications and what is new

The original Markdown table refers to a finer 3001-by-3001 calculation, whereas the supplied executable and its JSON use 2001 spatial samples and 1999 interior niche angles. The replay agrees with the executable's output, not every rounded entry in the prose table. For example its first area deficit is approximately 0.0012140108 rather than 0.00124. This is consistent with ordinary discretization differences and is not a rigorous error bound.

Calling the sampled scaled reference hull itself a feasible sofa would be wrong: the constructed competitor is its surviving canonical envelope (or a known scaled reference sofa inside it), not the whole convex hull. Positive sampled fibers alone are not a continuum certificate. The near-reference frame examples can instead be justified from uniform scaling of the actual reference and support tightening.

The packet is useful because it changes coordinates without forcing unit span and exposes a negative term already present in the true area identity. It avoids the affine-normalization error highlighted by AN. It still replaces the original global clipping target by another exact form of that target, not by an already proved inequality.

## 6. Relation to the partial-turn bridge and closure

The live branch already has the improved missing-angle allowance

$$\lambda(e)=\tan(e/2)-e/2=e^3/24+O(e^5).$$

It bounds completion loss in a unit incoming representation using signed full fibers. It does not prove the completed set connected. The minimum-width frame is available after both full turns have actually been obtained; for a partial body it cannot simply be used to add missing angles. In general one cannot combine these results by ignoring the completion allowance or changing frames on a completed disconnected set without proof.

The remaining full-turn theorem is still G_s<=Delta(U)+Delta(V) on all admitted minimum-width actual-body data. Under central confinement it is the sub-slab inequality T_s<=sW+Delta(U)+Delta(V). For partial turns a further margin paying lambda(e)+lambda(e') remains. Neither universal assertion is supplied by the upload.

A companion hand argument in `scaled-reference-slack-margin.md` converts the packet's observed three-halves-power margin for a specific reference-scale family into an explicit analytic lower bound. That result is not asserted here before its proof is given.

The package is incorporated as attributed proof input, not independently refereed mathematics. Original files and author outputs remain unchanged in the reproduction bundle. No CI, Lean/Lake compilation, dependency installation, manuscript build, or long numerical search was used.