# Second research round: direct shape optimization

Starting point: PR #7 at `2e5448439d7e8337cc5ec4942a3de8e815c11615`.

The aim is better arbitrary-bend constructions, not a rephrasing of the uniqueness proof. Existing negative results and path fixtures will be preserved. No CI, workflow run, or Lean build is used.

## Routes to test

1. Derive and test the area gradient of a finite hallway intersection from the lengths of its exposed wall segments. Use that gradient to optimize many more path coordinates without finite-differencing the entire polygon calculation for every coordinate.
2. Compare piecewise-linear, smooth-interpolated, and refined paths; retain exact path coordinates and optimizer termination reports. A smooth ansatz can help optimization, but the motion actually validated must be identified precisely.
3. Continue good solutions in the hallway angle, try both rotation directions and nonsymmetric perturbations, and compare on identical continuous-motion enclosure settings.
4. Seek useful analytic constructions or bounds independently of the cap/Mamikon machinery.

## Boundary variation to investigate

For a pose with unit outer-wall normals n1,n2 and inner corner c, the allowed region is

    n1.(x-c) <= 1, n2.(x-c) <= 1,
    max(n1.(x-c), n2.(x-c)) >= 0.

Away from changes of the active boundary, translation by dc contributes

    dA = sum_j (outer_exposed_length_j - inner_exposed_length_j) n_j.dc.

This is the standard shape-derivative / balanced-wall-pressure route, not a new general principle. Relevant primary reference: Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1, Sections 2.1 and 2.3, https://arxiv.org/html/2608.11206v1 . That work also already reports competing motion patterns. Any crossing measured here must be described as replication/refinement, not discovery of that phenomenon.

Coincident active walls, zero-length edges, changing largest components, and disconnected intersections require explicit handling and regression tests. A local stationary point is not a global optimum. Dense floating-point checks are not interval certificates.

## Checkpoints

- Plan committed before implementation. Outcomes, including failures, will be appended in subsequent commits.
