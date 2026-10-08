# Audit of the user-supplied one-turn reduction

**The unrestricted proof is not closed.** The proposal supplies useful geometric reductions, but its weighted one-turn maximum and its exclusion of exceptional two-turn configurations are not proved. This audit distinguishes accepted identities, necessary qualifications, and numerical issues. It is a fresh written review, not independent refereeing of the entire branch.

## 1. Provenance and preservation

The user supplied `ambidextrous-one-turn-reduction-draft.zip` and attributed it to **Claude Opus 5.5 Max**. That attribution is recorded as supplied by the user; the generating model was not independently verified.

Archive SHA-256:

`014daaf2bf99accf21b28310612d2f5260d6b6cceb8fd7066da2885a2db14625`

Its nine text files were imported at their proposed repository paths. The mathematical draft was imported in `179b936`; the scripts in `b67403f`, with two transcription corrections in `7ddefce` and `7c2cb37`. At `7c2cb37b55ebd00d7c9d7717f170f6205101a946`, all nine Git blob IDs match the uploaded bytes. Original claims and diagnostic tables are preserved rather than silently rewritten as our results.

| File, relative to `docs/ambidextrous/` | Original/imported Git blob |
|---|---|
| `one-turn-reduction.md` | `e2f6cf5cdcc2248f4b08da12cdb36f632e3ed153` |
| `computer-assisted/one-turn/README.md` | `5cfed9a4752bb4ab7417de479dcf66395f081f4a` |
| `computer-assisted/one-turn/cand.py` | `6ff625d676f0fee041616d6c2bf6f133d3b8bb10` |
| `computer-assisted/one-turn/polycap.py` | `14735a5b15488d4a313dfbdf3c3b58fbc26d3655` |
| `computer-assisted/one-turn/optimize_psi.py` | `b28d8db821e11b611285ebe7bc4e634727766fdd` |
| `computer-assisted/one-turn/optimize_pairs.py` | `41e7a32f95d535296e1d6404522959dc87273012` |
| `computer-assisted/one-turn/repair.py` | `c0c17afe730fcc8ce96556ec959b9b1d46fe589e` |
| `computer-assisted/one-turn/repair_search.py` | `cee3afc31986e4e8829f2a2306ea63afb4f2ee96` |
| `computer-assisted/one-turn/af_chain.py` | `4edae37c7a9eba7c4448475703b8efb7632789b5` |

The imported numerical table reports its author's experiments. Those optimization runs have not been independently reproduced here. Separate small diagnostics and exact algebra checks must be labelled separately.

## 2. The exact cap-pair identity is useful, with full-turn coverage retained

For caps U,V with the same horizontal projection I of length W, use upper roofs a,b in [0,1] and nonnegative full-niche roofs alpha,beta. Put

$$
d(x)=\min(a,1-\beta)-\max(\alpha,1-b),
$$

$$
g(x)=\min(\alpha,1-b)+\min(\beta,1-a).
$$

Direct scalar algebra gives

$$
d=a+b-1-\alpha-\beta+g.
\tag{OA.1}
$$

Thus OT1 is correct when every fiber is nonempty. For arbitrary pairs the exact extension is

$$
|E|=\mathcal A(U)+\mathcal A(V)-W+\int_I g\,dx
       +\int_I(-d)_+\,dx.
\tag{OA.2}
$$

The last term is the empty-fiber correction. It is zero under OT1's hypothesis, not in a general finite-dimensional pair search. When every fiber is nonempty, alpha<=a and beta<=b, so each one-turn niche is contained in its own cap. Then the two summands in g are exactly the portions clipped outside the common hull.

**Coverage qualification.** Constructing the full-quarter caps of a partial-turn body does not show that body is contained in their full-turn envelope. The unconditional `S subset E` line in OT.0 must be read with OT1's explicit full-canonical-turn hypothesis. OT3's initial-angle arguments, by contrast, apply before that reduction.

**No sign shortcut.** Even a proof of `A(U)-W/2 <= M/2` for both caps would give `|E| <= M+G`, not `|E| <= M`, while G is positive. SC3 shows that G can be positive for fully saturated bodies whose areas approach M. The proposal does not eliminate that obstruction merely by renaming the two terms.

## 3. Floor traces and face classification survive the audit

OT3 follows directly by testing the retained horizontal extreme and top-face endpoint against each of the two strict inner inequalities. No differentiability or curvature bound is involved. Extreme-point retention then gives OT3a. The three alternatives A/P/R in OT4 follow by comparing the two left endpoints and applying those interval exclusions. The stronger part of OT4 follows from the common unit-height rectangle and the terminal strip.

There is a useful quantitative strengthening. If `|S| > q > 1`, the strip determinant bound gives each reduced endpoint omega greater than arccos(1/q). A rectangle of width d and height one has width at least d cos(omega)+sin(omega) in either outgoing normal. Therefore

$$
\boxed{d\ge q-\sqrt{q^2-1}\quad\Longrightarrow\quad
\text{both reduced turns are full}.}
\tag{OA.3}
$$

**Proof.** For a partial endpoint,

$$
d\cos\omega+\sin\omega>1
\iff d>\frac{1-\sin\omega}{\cos\omega}
=\tan(\pi/4-\omega/2).
$$

The expression on the right decreases strictly with omega and its value at arccos(1/q) is q-sqrt(q^2-1). This contradicts the terminal width at most one. The proof works for either sign of the outgoing normal. QED.

In OT4(A), take d=x_0-l. For bodies of area at least M>41/25, the sufficient threshold becomes

$$
d\ge\frac{41-4\sqrt{66}}{25},
$$

rather than tan(pi/8). This strengthens the admitted case, but does not exclude the exceptional cases.

OT.8's description that both faces are crowded at one end is not a consequence of OT4(R) alone: R only locates **at least one** face there. Any proposed area bound for that case must retain the other face as a variable. No elementary exclusion of the entire case is supplied by the classification.

## 4. No-clipping and the transfer of maximality need their hypotheses

OT5's connected-family argument is valid when the corner-height positivity holds for **each** cap, including the cap of the reflected hull. Positivity for one turn does not by itself establish the conclusion for the other.

A common face length at least one supplies both positivities: with face length D and s=sin(t), c=cos(t), each corner height is at least

$$
Dsc+1-s-c\ge sc+1-s-c=(1-s)(1-c)>0.
$$

Its baseline intervals then form one connected interval. The retained endpoints exclude escape past the common faces. The full-turn fiber condition bounds the heights, yielding OT5's zero clipping and additive objective exactly.

OT5a proves only constrained one-turn maximality: comparison caps must give a connected, fully feasible two-turn intersection with the fixed opposite cap. It does **not** justify all variations admitted in Baek's unconstrained one-turn balance theorem. In particular, nonempty fibers need not remain nonempty under both signs of an arbitrary support perturbation. The admissibility step remains explicit.

OT2's lower-bound construction can slightly be enlarged: the assumption N(V) subset V is unnecessary if the niche height is at most 1/2. On the nonempty interval where a>=1/2, the actual intersection has fibers through the common midline and follows both canonical motions as a subset of each cap-minus-niche. The same scalar inequality yields area at least `2 A(V)-W`, where A retains the **signed** cap-minus-full-niche definition. This is a lower-bound construction, not the desired universal upper bound.

## 5. The proposed weighted one-turn problem is not already solved

Write Psi(V)=A(V)-W(V)/2 with `A(V)=|V|-|N(V)|`.

- A width penalty leaves the interior finite-support derivatives unchanged when the axis supports are fixed. It changes the endpoint optimality conditions. One must prove existence, approximate maximality and the needed endpoint/arm estimates for the new objective; the old unpenalized maximizing-cap premise cannot be reused.
- The statement W-Gerver in OT.7 is over **right-angle caps already**. A separate full-angle theorem is not needed to define or maximize that fixed-domain functional. It is still needed wherever a partial-turn ambidextrous body is to be represented by those caps.
- The large-width cutoff should be retained exactly as `2 |Gerver| - M`, or use an explicitly proved rational upper bound for Gerver's area. A rounded decimal in the imported draft is not an exact certificate.
- The arm-length condition at most two and the balance-to-measure argument are not proved by numerical convergence to the candidate. Nor is the endpoint transversality sketch a proof that arbitrary nonsmooth maximizers have those endpoint edges.

A separate [attainment note](one-turn-penalized-attainment.md) proves existence of a maximizer for this signed right-angle objective directly, without invoking ambidextrous optimality or Gerver's sharp theorem. It does not compute that maximum or its equality case.

## 6. Numerical objective mismatch and interpolation issue

The imported `polycap.psi` evaluates

$$
\int(a-\alpha)_+\,dx-W/2,
$$

whereas OT.7 asks to maximize

$$
\Psi=\int(a-\alpha)\,dx-W/2.
$$

Their exact difference is

$$
\boxed{\int(\alpha-a)_+\,dx=|N(V)\setminus V|.}
\tag{OA.4}
$$

They agree for caps containing their niche, not for all caps in the imported search domain. A local maximum of the clipped objective is not automatically a maximum of the signed objective.

This is not just a formal possibility. For the rectangle cap `[0,4] x [0,1]`, the pi/4 quadrant alone gives

$$
\alpha(x)\ge1+\min(x,4-x)-\sqrt2.
$$

Hence the objective discrepancy is at least

$$
\int_{\sqrt2}^{4-\sqrt2}
[\min(x,4-x)-\sqrt2]dx=(2-\sqrt2)^2>0.
$$

Also `top_profile_from_vertices` says it removes repeated x-coordinates by keeping the highest y, but its implementation only sorts them. On the exact rectangle vertices `[(4,0),(4,1),(0,1),(0,0)]`, the returned top at x=4 is zero instead of one. This affects numerical integration even though the geometric endpoint has measure zero.

Finally, omitting hallway angles gives a pointwise relaxation if exact supports and spatial integration are used. Trapezoidal spatial integration, endpoint errors, interpolated supports and floating-point arithmetic do **not** preserve a rigorous upper-bound direction. The imported statements about overestimation are therefore not certified bounds.

The original scripts are retained unchanged for provenance. The separate review utility reports signed area, surviving area, leakage and empty-fiber correction distinctly, and does not silently replace one objective with another. Neither its samples nor the author's optimization table closes the continuum problem.

## 7. Result of this pass

The proposal is incorporated, not dismissed. OT1 and OT3–OT5 provide a useful face-based organization which avoids assuming a global curvature cap at the outset. OA.3 strengthens its full-turn admission. The new signed-objective attainment theorem removes one existence obligation.

The remaining tasks are still substantial: prove the sharp weighted one-turn inequality; exclude or control exceptional face configurations, especially point faces; and justify every motion/variation used in transferring a two-turn maximizer to the one-turn problem. No claim is made that those tasks are routine, that the two-wing route has been superseded, or that the unrestricted theorem has been obtained.

All new commits include `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Original diagnostic results, newly executed checks and mathematical statements are kept separate.
