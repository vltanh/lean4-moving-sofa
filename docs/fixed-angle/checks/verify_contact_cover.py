"""Replay contact-root certificates without trusting their recorded bounds.

Usage: python verify_contact_cover.py certificates/*.json --report replay.json
Only the standard library is used. '--partial' checks every supplied box
but deliberately does not assert coverage of the full required ranges.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import time
from interval_contact import I, down, up, HALF_PI
from jet_contact import certificate
from endpoint_contact import endpoint_certificate

SOURCES = ('contact_core.py', 'interval_contact.py', 'jet_contact.py',
           'endpoint_contact.py', 'verify_contact_cover.py')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def number(value):
    require(type(value) in (float, int) and math.isfinite(value), 'Invalid certificate number')
    return float(value)


def validate_row(row, endpoint=False):
    lo, hi = ('hlo', 'hhi') if endpoint else ('wlo', 'whi')
    left, right = number(row[lo]), number(row[hi])
    require(left <= right, 'Reversed parameter interval')
    require(len(row['center']) == len(row['radii']) == len(row['inverse']) == 3,
            'A root box must have three coordinates')
    center = [number(x) for x in row['center']]
    radii = [number(x) for x in row['radii']]
    require(all(x > 0 for x in radii), 'Root radii must be positive')
    require(all(len(r) == 3 for r in row['inverse']), 'Preconditioner must be 3 by 3')
    inverse = [[number(x) for x in r] for r in row['inverse']]
    return left, right, center, radii, inverse


def root_box(row):
    return [I(down(c-r), up(c+r)) for c, r in zip(row['center'], row['radii'])]


def check_joins(data):
    rows, joins = data['boxes'], data['joins']
    require(len(rows) >= 1 and len(joins) == len(rows)-1, 'Missing endpoint joining boxes')
    require(rows[0]['hlo'] == 0 and rows[-1]['hhi'] == 1/32,
            'Endpoint chain must span [0,1/32] exactly')
    for j, (aa, bb, join) in enumerate(zip(rows, rows[1:], joins)):
        h = aa['hhi']
        require(h == bb['hlo'] == join['hlo'] == join['hhi'],
                f'Incorrect shared parameter at endpoint join {j}')
        inner = root_box(join)
        for outer in (root_box(aa), root_box(bb)):
            require(all(a.lo <= b.lo and b.hi <= a.hi for a, b in zip(outer, inner)),
                    f'Joining root box {j} is not contained in both neighbors')


def exact_coverage(intervals, left, right):
    """Compare exact dyadic endpoints with exact rational coverage targets."""
    edge = left
    for lo, hi in sorted((Fraction.from_float(a), Fraction.from_float(b)) for a,b in intervals):
        if hi < edge:
            continue
        require(lo <= edge, f'Uncovered parameter gap starts at {edge}')
        edge = max(edge, hi)
        if edge >= right:
            return
    require(edge >= right, f'Coverage stops at {edge}, before {right}')


def coverage_documents(documents):
    bulk = []
    endpoint_count = 0
    for data in documents:
        if data.get('parameter') == 'h=w-c':
            check_joins(data)
            endpoint_count += 1
        else:
            bulk.extend((number(r['wlo']), number(r['whi'])) for r in data['boxes'])
    require(endpoint_count == 1, 'Exactly one fully joined endpoint chain is required')
    exact_coverage(bulk, Fraction(101,100), Fraction(7853,5000))
    return {'compact_angle_interval': ['101/100','7853/5000'],
            'endpoint_parameter_interval': ['0','1/32'], 'no_parameter_gaps': True}


def replay(paths, partial=False):
    start = time.monotonic()
    documents = []
    outputs = []
    total = 0
    for filename in paths:
        path = Path(filename)
        data = json.loads(path.read_text())
        require(data.get('status') == 'complete', f'{path}: incomplete generation checkpoint')
        require(isinstance(data.get('boxes'), list) and data['boxes'], f'{path}: no boxes')
        endpoint = data.get('parameter') == 'h=w-c'
        if endpoint:
            check_joins(data)
        records = data['boxes'] + (data['joins'] if endpoint else [])
        results = []
        for index, row in enumerate(records):
            args = validate_row(row, endpoint)
            out = (endpoint_certificate if endpoint else certificate)(*args, geometry=True)
            require(out['ok'], f'{path}, row {index}: verification failed: {out}')
            results.append(out)
            total += 1
            if total % 100 == 0:
                print(f'Replayed {total} root and geometry boxes', flush=True)
        outputs.append({'file': path.name, 'sha256': digest(path),
                        'parameter_boxes': len(data['boxes']),
                        'joining_boxes': len(data.get('joins', [])),
                        'maximum_contraction': max(x['contraction'] for x in results),
                        'maximum_p_second': max(x['max_p_second'] for x in results),
                        'maximum_p0': max(x['max_p0'] for x in results),
                        'maximum_d': max(x['max_d'] for x in results),
                        'maximum_event_orders': max(x.get('orders',1) for x in results)})
        documents.append(data)
    report = {'all_supplied_boxes_passed': True, 'partial': bool(partial),
              'total_boxes_including_joins': total, 'files': outputs,
              'source_sha256': {f: digest(Path(__file__).parent / f) for f in SOURCES},
              'python': sys.version, 'platform': platform.platform(),
              'elapsed_seconds': time.monotonic() - start}
    if not partial:
        report['coverage'] = coverage_documents(documents)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificates', nargs='+', type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--partial', action='store_true')
    args = parser.parse_args()
    report = replay(args.certificates, args.partial)
    text = json.dumps(report, indent=2, allow_nan=False)
    if args.report:
        args.report.write_text(text + '\n')
    print(text)


if __name__ == '__main__':
    main()
