"""Discover and verify all non-analytic contact-certificate pieces.

Only the Python standard library is required. Floating-point Newton steps
are untrusted proposals: every accepted box passes interval root and
geometry verification. Failure raises or writes an incomplete checkpoint;
it never yields a certificate for an uncovered parameter interval.

Examples:
  python build_contact_cover.py --part 1 --output-dir certificates
  python build_contact_cover.py --part all --output-dir certificates
  python verify_contact_cover.py certificates/*.json
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import time
from contact_core import residual, float_order
from interval_contact import I, AD, down, up
from jet_contact import evaluate, certificate
from endpoint_contact import endpoint_residual, endpoint_shoot, endpoint_certificate

PARTS = ((1.01, 1.1), (1.1, 1.3), (1.3, 1.5), (1.5, 1.565), (1.565, 1.5706))


def inverse3(matrix):
    """An untrusted approximate preconditioner; verified afterwards."""
    rows = [list(map(float, r)) + [float(i == j) for j in range(3)]
            for i, r in enumerate(matrix)]
    for j in range(3):
        pivot = max(range(j, 3), key=lambda k: abs(rows[k][j]))
        rows[j], rows[pivot] = rows[pivot], rows[j]
        div = rows[j][j]
        if not math.isfinite(div) or div == 0:
            raise ArithmeticError("Singular proposal matrix")
        rows[j] = [x / div for x in rows[j]]
        for i in range(3):
            if i != j:
                coef = rows[i][j]
                rows[i] = [a - coef * b for a, b in zip(rows[i], rows[j])]
    return [r[3:] for r in rows]


def product(matrix, vector):
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def derivatives(z, parameter, endpoint=False):
    if endpoint:
        data = endpoint_shoot(I(parameter), [I(t) for t in z], AD)[0]
    else:
        data = evaluate(I(parameter), [I(t) for t in z],
                        float_order(parameter, *z), AD)[0]
    mid = lambda v: (v.lo + v.hi) / 2
    return [[mid(v) for v in row.grad[:3]] for row in data], [mid(row.grad[3]) for row in data]


def newton(guess, parameter, endpoint=False):
    """Find a proposal, not a validated root."""
    fun = endpoint_residual if endpoint else residual
    z = list(map(float, guess))
    previous = math.inf
    for _ in range(40):
        val = fun(z, parameter)
        norm = max(map(abs, val))
        if norm < 3e-15:
            return z
        jac, _ = derivatives(z, parameter, endpoint)
        change = product(inverse3(jac), val)
        best, best_norm = z, norm
        for backtrack in range(12):
            lam = 2.0 ** -backtrack
            trial = [a - lam * d for a, d in zip(z, change)]
            if not endpoint and not (0 < trial[0] < trial[1] < trial[2] < parameter):
                continue
            try:
                trial_norm = max(map(abs, fun(trial, parameter)))
            except (ArithmeticError, ValueError, OverflowError):
                continue
            if trial_norm < best_norm:
                best, best_norm = trial, trial_norm
        if best is z:
            if norm < 1e-11:
                return z
            raise ArithmeticError(("Newton discovery stalled", parameter, norm))
        z = best
        if best_norm >= previous and best_norm < 1e-11:
            return z
        previous = best_norm
    raise ArithmeticError(("Newton iteration limit", parameter))


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2, allow_nan=False) + '\n')
    temporary.replace(path)


def build_bulk(part, directory):
    lower, upper = PARTS[part - 1]
    left, target = down(lower), up(upper)
    d0 = 0.01
    guess = [3 * d0 * d0 / 16, 1.5 * d0, 2 * d0]
    guess = newton(guess, 1.01)
    warm = 1.01
    while warm < left:
        following = min(left, warm + min(.005, (warm - 1) / 10))
        jac, dw = derivatives(guess, warm)
        slope = product(inverse3(jac), dw)
        predicted = [x - (following - warm) * s for x, s in zip(guess, slope)]
        guess = newton(predicted, following)
        warm = following
    width = min(.0004, (left - 1) / 30)
    accepted = []
    failures = 0
    start = time.monotonic()
    path = directory / f'compact-{part}.json'
    def checkpoint(status):
        save(path, {'status': status, 'requested_left': lower,
                    'requested_right': upper, 'boxes': accepted,
                    'failed_attempts': failures})
    while left < target:
        if len(accepted) >= 10000:
            checkpoint('incomplete')
            raise ArithmeticError("Box limit; no complete certificate claimed")
        right = min(left + width, target)
        mid, radius = (left + right) / 2, (right - left) / 2
        center = newton(guess, mid)
        jac, dw = derivatives(center, mid)
        preconditioner = inverse3(jac)
        slope = product(preconditioner, dw)
        radii = [1.9 * (abs(s) + margin) * radius + 5e-12
                 for s, margin in zip(slope, (.002, .005, .01))]
        try:
            bounds = certificate(left, right, center, radii, preconditioner)
        except ArithmeticError as error:
            bounds = {'ok': False, 'reason': str(error)}
        if not bounds['ok']:
            failures += 1
            width /= 2
            if width < 1e-11:
                checkpoint('incomplete')
                raise ArithmeticError(("No certified continuation", left, bounds))
            continue
        accepted.append({'wlo': left, 'whi': right, 'center': center,
                         'radii': radii, 'inverse': preconditioner, 'bounds': bounds})
        left, guess = right, center
        if bounds['ratio'] < .65:
            width = min(width * 1.18, .0015)
        elif bounds['ratio'] > .9:
            width *= .9
        if len(accepted) % 50 == 0:
            checkpoint('incomplete')
            print(f'part {part}: {len(accepted)} boxes, through {left:.16g}', flush=True)
    checkpoint('complete')
    print(f'part {part}: complete, {len(accepted)} boxes, {time.monotonic()-start:.1f}s', flush=True)


def build_endpoint(directory):
    rows = []
    guess = [.0391773648, .88949482, math.pi / 2]
    for j in range(16):
        lo, hi = j / 512, (j + 1) / 512
        mid, radius = (lo + hi) / 2, (hi - lo) / 2
        center = newton(guess, mid, endpoint=True)
        jac, dh = derivatives(center, mid, endpoint=True)
        preconditioner = inverse3(jac)
        slope = product(preconditioner, dh)
        radii = [1.9 * (abs(s) + margin) * radius + 1e-10
                 for s, margin in zip(slope, (.002, .005, .01))]
        bounds = endpoint_certificate(lo, hi, center, radii, preconditioner)
        if not bounds['ok']:
            raise ArithmeticError(('Endpoint box failed', j, bounds))
        rows.append({'hlo': lo, 'hhi': hi, 'center': center,
                     'radii': radii, 'inverse': preconditioner, 'bounds': bounds})
        guess = center
    joins = []
    for aa, bb in zip(rows, rows[1:]):
        h = aa['hhi']
        center = newton(aa['center'], h, endpoint=True)
        jac, _ = derivatives(center, h, endpoint=True)
        preconditioner = inverse3(jac)
        lower = [max(a - r, b - s) for a, r, b, s in
                 zip(aa['center'], aa['radii'], bb['center'], bb['radii'])]
        upper = [min(a + r, b + s) for a, r, b, s in
                 zip(aa['center'], aa['radii'], bb['center'], bb['radii'])]
        radii = [.4 * min(x - lo, hi - x) for x, lo, hi in zip(center, lower, upper)]
        if min(radii) <= 0:
            raise ArithmeticError('Endpoint root boxes do not have a common interior')
        bounds = endpoint_certificate(h, h, center, radii, preconditioner)
        if not bounds['ok']:
            raise ArithmeticError(('Joining box failed', h, bounds))
        joins.append({'hlo': h, 'hhi': h, 'center': center,
                      'radii': radii, 'inverse': preconditioner, 'bounds': bounds})
    save(directory / 'endpoint.json', {'status': 'complete', 'parameter': 'h=w-c',
                                      'left': 0, 'right': 1 / 32, 'boxes': rows, 'joins': joins})
    print('endpoint: complete, 16 parameter boxes and 15 joining boxes', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part', choices=('1', '2', '3', '4', '5', 'endpoint', 'all'), default='all')
    parser.add_argument('--output-dir', type=Path, default=Path('certificates'))
    args = parser.parse_args()
    if args.part == 'all':
        for i in range(1, 6):
            build_bulk(i, args.output_dir)
        build_endpoint(args.output_dir)
    elif args.part == 'endpoint':
        build_endpoint(args.output_dir)
    else:
        build_bulk(int(args.part), args.output_dir)


if __name__ == '__main__':
    main()
