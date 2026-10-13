#!/usr/bin/env python3
"""Verify the finite rational table in all-angle-bootstrap.tex.

This is a standalone paper-certificate check, not a CI job or Lean build.
It uses integer and Fraction arithmetic only. It does not establish the
geometric hypotheses of the arm theorem; those are proved in the papers.
"""
from __future__ import annotations

from fractions import Fraction

CERTIFICATE: tuple[tuple[int, ...], ...] = (
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (866, 733, 600, 466, 333, 200, 66, 0, 0, 0, 0, 0),
    (866, 733, 600, 466, 333, 213, 119, 53, 13, 0, 0, 12),
    (869, 735, 602, 471, 348, 239, 148, 81, 41, 28, 28, 41),
    (874, 747, 619, 494, 377, 273, 187, 124, 85, 72, 72, 85),
    (883, 764, 645, 529, 420, 325, 246, 188, 153, 144, 144, 160),
    (898, 794, 689, 586, 491, 407, 338, 289, 261, 257, 257, 276),
    (921, 839, 758, 676, 601, 535, 483, 448, 432, 432, 436, 462),
    (959, 912, 866, 819, 775, 738, 712, 699, 699, 701, 719, 753),
)


def integer_step(row: tuple[int, ...]) -> tuple[int, ...]:
    """Apply the exact downward-rounded recurrence printed in the paper."""
    if len(row) != 12 or any(not 0 <= value <= 1000 for value in row):
        raise ValueError("Expected twelve integers between zero and 1000.")
    prefix = 0
    heights = [15000]
    for i, value in enumerate(reversed(row), start=1):
        prefix += value
        heights.append(15000 - 2000 * i + 3 * prefix)
    return tuple(
        min(1000, max(value, 0, min(heights[i], heights[i + 1]) // 15))
        for i, value in enumerate(row)
    )


def fraction_step(row: tuple[int, ...]) -> tuple[int, ...]:
    """Independently integrate the reflected step function using Fractions."""
    values = [Fraction(value, 1000) for value in row]
    heights = [Fraction(1)]
    for value in reversed(values):
        heights.append(heights[-1] + Fraction(2, 15) * (Fraction(3, 2) * value - 1))
    output = []
    for i, old in enumerate(row):
        lower = 1000 * min(heights[i], heights[i + 1])
        rounded_down = lower.numerator // lower.denominator
        output.append(min(1000, max(old, 0, rounded_down)))
    return tuple(output)


def main() -> None:
    for index, (previous, expected) in enumerate(zip(CERTIFICATE, CERTIFICATE[1:]), start=1):
        for name, step in (("integer", integer_step), ("Fraction", fraction_step)):
            actual = step(previous)
            if actual != expected:
                raise ArithmeticError(f"{name} check failed at row {index}: {actual} != {expected}")
    minimum = Fraction(min(CERTIFICATE[-1]), 1000)
    if minimum <= Fraction(2, 3):
        raise ArithmeticError("Final lower bound does not exceed 2/3.")
    print(f"All eight rows verified by both methods; final minimum = {minimum} > 2/3.")


if __name__ == "__main__":
    main()
