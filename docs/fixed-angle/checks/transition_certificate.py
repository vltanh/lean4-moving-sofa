#!/usr/bin/env python3
"""Exact polynomial checks for transition-model.tex; no CI or Lean calls.

This verifies algebra in the displayed certificate, not geometric hypotheses
or the infinite-dimensional optimality/sofa-transfer arguments.
"""
from __future__ import annotations
from fractions import Fraction as Q

Poly = tuple[Q, ...]


def evaluate(p: Poly, x: Q) -> Q:
    value = Q(0)
    for coefficient in reversed(p):
        value = value * x + coefficient
    return value


def derivative(p: Poly) -> Poly:
    return tuple(Q(i) * p[i] for i in range(1, len(p))) or (Q(0),)


def product(a: Poly, b: Poly) -> Poly:
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return tuple(out)


def integral(p: Poly, a: Q, b: Q) -> Q:
    return sum((v * (b ** (i + 1) - a ** (i + 1)) / (i + 1)
                for i, v in enumerate(p)), Q(0))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def main() -> None:
    left, right = Q(3, 2), Q(2)
    q0 = (Q(0), Q(-3, 16))
    q1 = (Q(0), Q(0), Q(-1, 4), Q(1, 12))
    v0, v1 = derivative(q0), derivative(q1)
    h = (Q(0), Q(1, 2), Q(-1, 4))
    X = (Q(0), Q(0), Q(-1, 4), Q(1, 6))
    require(evaluate(q0, left) == evaluate(q1, left), 'q does not join.')
    require(evaluate(v0, left) == evaluate(v1, left), 'v does not join.')
    require(evaluate(q1, right) == Q(-1, 3), 'Wrong terminal primitive.')
    require(evaluate(v1, right) == 0, 'Wrong terminal derivative.')
    require(evaluate(X, left) == 0 and evaluate(X, right) == Q(1, 3),
            'Wrong exposed abscissa endpoints.')
    energy = (left * Q(3, 16) ** 2 + integral(product(v1, v1), left, right)) / 2
    tail = integral(product(h, derivative(X)), left, right)
    require(energy == tail == Q(229, 7680), 'Wrong one-sided energy or tail.')
    require(energy + tail == Q(229, 3840), 'Wrong model minimum.')
    old_h = tuple(2 * x for x in h)
    old_X = tuple(2 * x for x in X)
    old_tail = integral(product(old_h, derivative(old_X)), left, right)
    require(old_tail == Q(229, 1920), 'Wrong unperturbed one-sided tail.')
    print('One-sided kinetic energy:', energy)
    print('One-sided optimized tail:', tail)
    print('One-sided model minimum:', energy + tail)
    print('Two-sided transition coefficient:', 2 * (energy + tail))
    print('Two-sided unperturbed coefficient:', 2 * old_tail)
    print('All polynomial joins and exact integral checks passed.')


if __name__ == '__main__':
    main()
