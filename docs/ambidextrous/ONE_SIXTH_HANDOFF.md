# Current continuation: the requested 1/6 improvement is NOT proved

Read this checkpoint with the existing HANDOFF.md. The new work does not improve the absolute global upper bound. It identifies a rigorous obstruction to continuing the previous constant-tuning route and a different general reduction.

## Actual mathematical results

**SX:** [one-sixth-six-hallway-obstruction.md](one-sixth-six-hallway-obstruction.md) gives a compact connected polygon of exact area 5/3 that fits six prescribed hallway positions: both handed versions of asin(3/5), 45 degrees and asin(4/5). Its seven-piece rational profile supplies a hand proof. Since 5/3 exceeds the requested `2 sqrt(2)-7/6`, no improvement of the current three-hallway coefficients alone can reach that target. This is a finite-position witness, NOT a continuously moving sofa.

**JT:** [joint-terminal-strips-one-sixth-transfer.md](joint-terminal-strips-one-sixth-transfer.md) couples the two outgoing strip normals. For area A > sqrt(2), missing angles e_-,e_+ and actual outgoing widths q_-,q_+ satisfy

`e_- + e_+ <= asin(q_- q_+ / A)`.

Combining this with the earlier circular loss and GC connectedification gives

`A <= A_F + lambda(asin(1/A))`, where `lambda(e)=tan(e/2)-e/2`.

This proves the general value comparison `0 <= mu_A-A_F <= 1/80`. It is NOT an absolute area bound of 1/80, nor equality of the two suprema.

The exact sufficient implication is

`A_F <= 33/20 = 1.65 ==> mu_A <= 41543/25000 = 1.66172 < 2 sqrt(2)-7/6`.

**The full-turn premise A_F <= 1.65 is unproved.** Do not omit that premise or announce the conditional right-hand side as a new global result. Exact Romik optimality would be stronger than the full-turn premise, but is not necessary for this approximate target.

## Bounded attempts at the remaining full-turn target

Five prescribed rational-angle meshes were locally optimized from reference placements, with symmetric handed profiles and at most 80 iterations. Approximate local raster areas ranged from 1.661784 (11 angles per turn) to 1.648460 (47 per turn). Four runs hit the iteration cap. These are NOT global upper bounds. In particular, observing 1.648460 at one locally searched configuration does not prove `A_F <= 1.65`.

Each search invocation was limited externally to five seconds; recorded numerical search times were below 0.34 seconds. No full parameter covering, large certificate, CI, Lean compilation, dependency installation or manuscript build was performed. The numerical scripts and full outputs were delivered in `one_sixth_target_attempt.zip` in the conversation.

## Verification and dependencies

[check_one_sixth_target.py](computer-assisted/check_one_sixth_target.py) passed 77 exact rational assertions, including all 22 affine-order cells for the hand polygon profile and the rational margins in JT. Its executed Git blob `351945ddf278f2d9c45e4d57cf3a8bc3e596d8c6` matches the committed source. [Record](computer-assisted/one-sixth-target-checks.json).

The continuum statements remain self-reviewed. JT depends on the existing canonical motion/no-sideways setup, circular completion geometry and GC gap compression; its proof spells out which facts are used. Finite arithmetic checks are not an independent verification of those continuum arguments.

## Single target after this checkpoint

Prove an actual ordinary-area full-turn bound `A_F <= 33/20`, using additional angular constraints or a valid continuum structural inequality. Such a proof would, by JT, deliver the user's requested approximate upper bound for general partial motions too. A local optimum, a partial covering, or a cap regularity assumption not proved for all competitors is insufficient. Do not continue optimizing the old three-hallway constant toward 1/6: SX proves that route cannot work.

The earlier JD `2 sqrt(2)-1-1/51` hand claim and the external 353/200 computer-assisted benchmark retain their stated review boundaries. No sharp optimality or uniqueness theorem was closed in this continuation. Keep the PR open and draft.
