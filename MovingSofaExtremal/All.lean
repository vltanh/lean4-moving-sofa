module

public import MovingSofaExtremal.Main
public import MovingSofaExtremal.Unified

/-!
# The coercive route

Optimality, uniqueness and stability of Gerver's sofa from the coercive certificate
`MovingSofaStability.coercive_certificate`, without Baek's Theorem 1.1.1, his results on balanced
caps, or the modules of the first proof of uniqueness:

* `Main`: the maximizing right-angle caps have sofa area `|G|` and are the horizontal translates
  of Gerver's cap (`right_angle_maximizer_value`, `right_angle_maximizer_eq_gerver`); with the
  assembly of `MovingSofaUniqueness.Maximizing`, this gives optimality (`gerver_sofa_optimal`) and
  uniqueness (`image_eq_gerver_of_volume_eq`, `translate_eq_gerver_of_volume_eq`);
* `Unified`: `gerver_sofa_optimal_unique_stable`, with the stability theorems of
  `MovingSofaStability`, whose global step uses the uniqueness of `Main`.

`SolutionCoercive.lean` proves the statements of `Challenge.lean` through these theorems.
-/
