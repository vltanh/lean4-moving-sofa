module

public import MovingSofaExtremal.Geometry
public import MovingSofaExtremal.HorizontalTranslation
public import MovingSofaExtremal.CoerciveRigidity
public import MovingSofaExtremal.Optimality
public import MovingSofaExtremal.Uniqueness
public import MovingSofaExtremal.Unified

/-!
# The coercive route

Optimality, uniqueness and stability of Gerver's sofa from the coercive certificate
`MovingSofaStability.coercive_certificate`, without Baek's Theorem 1.1.1, his results on balanced
caps, or the modules of the first proof of uniqueness:

* `Geometry`: maximizing caps, the injectivity condition and the right-angle motion;
* `HorizontalTranslation`: horizontal translates of caps, niches and sofas;
* `CoerciveRigidity`: the maximizing right-angle caps are the translates of Gerver's cap;
* `Optimality`: `gerver_sofa_optimal`;
* `Uniqueness`: `image_eq_gerver_of_volume_eq`, `translate_eq_gerver_of_volume_eq`;
* `Unified`: `gerver_sofa_optimal_unique_stable`, with the stability theorems of
  `MovingSofaStability`, whose global step uses `Uniqueness`.

`SolutionCoercive.lean` proves the statements of `Challenge.lean` through these theorems.
-/
