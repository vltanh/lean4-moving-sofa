"""Exact rational checks for RATIONAL_ANGLE_EXCLUSION.md.

This consumes constants already certified in the round-six crossing record.
It does not reprove the analytic contact-model certificate or identify the
model crossing with the global phase transition.
"""
from fractions import Fraction as F

S = 1 << 96

ROOT_LO = F(136672184698, 180_000_000_000)
ROOT_HI = F(136672184699, 180_000_000_000)

LEFT = F(257315, 338889)
RIGHT = F(292174, 384799)
MEDIANT = F(549489, 723688)

GAP_LO_UPPER = F(405343882600452697, S)
DERIVATIVE_UPPER = F(-109505625206996195173306350356, S)
PI_LOWER = F(248902613312231085230521944622, S)


def mediant_gap_upper() -> F:
    return GAP_LO_UPPER + DERIVATIVE_UPPER * PI_LOWER * (MEDIANT - ROOT_LO)


def prove() -> dict:
    assert LEFT < ROOT_LO < MEDIANT < ROOT_HI < RIGHT
    assert RIGHT.numerator * LEFT.denominator - LEFT.numerator * RIGHT.denominator == 1
    assert MEDIANT == F(LEFT.numerator + RIGHT.numerator,
                        LEFT.denominator + RIGHT.denominator)
    gap = mediant_gap_upper()
    if gap >= 0:
        raise ArithmeticError("stored derivative/gap bounds do not exclude the mediant")
    return {
        "format": "rational-angle-exclusion-v1",
        "root_ratio_interval": [str(ROOT_LO), str(ROOT_HI)],
        "farey_neighbors": [str(LEFT), str(RIGHT)],
        "minimum_possible_denominator_before_mediant_exclusion": 723688,
        "mediant": str(MEDIANT),
        "mediant_gap_upper": str(gap),
        "conclusion": "if beta_model/pi=p/q in lowest terms then q>723688",
        "scope": "contact-model crossing only; not the unrestricted phase transition",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(prove(), indent=2))
