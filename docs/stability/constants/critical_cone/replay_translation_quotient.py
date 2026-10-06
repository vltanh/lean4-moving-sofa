"""Replay the continuum translation-quotient certificate and verify its cover.

Acceptance uses integer/Fraction predicates only. The analytic kernel/quotient
identities remain inputs. A receipt without this replay is not a proof.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform
from certify_translation_quotient_compact import certificate
from compact_rank2 import CompactModel
from dyadic_interval import iv, SCALE


def canonical(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode()


def check_cover(result):
    if result['status'] != 'passed' or result['frontier'] or result['failed']:
        raise AssertionError('an unfinished search is not a certificate')
    if F(result['coefficient']) != F(93, 100):
        raise AssertionError('this receipt is specifically for coefficient 93/100')
    m = CompactModel(iv.mpf(['0.039177264', '0.039177465']),
                     iv.mpf(['0.681301409', '0.681301610']))
    ranges = m.ranges()
    rows = result['leaf_certificate']
    leaves = {}
    count = Counter()
    areas = Counter()
    maximum = F(0)
    for row in rows:
        rt, i, nt, ru, j, nu = row['cell']
        if not (0 <= rt <= ru < 6 and nt > 0 and nu > 0 and
                nt & (nt-1) == 0 and nu & (nu-1) == 0 and
                0 <= i < nt and 0 <= j < nu):
            raise AssertionError('invalid dyadic rectangle')
        key = tuple(row['cell'])
        if key in leaves:
            raise AssertionError('duplicate certificate rectangle')
        q = row['squared_upper']
        if q['denominator'] != SCALE or q['lower_numerator'] != q['upper_numerator']:
            raise AssertionError('malformed outward upper endpoint')
        upper = F(q['upper_numerator'], q['denominator'])
        if not upper < F(93, 100)**2:
            raise AssertionError('a leaf does not prove its coefficient bound')
        maximum = max(maximum, upper)
        leaves[key] = row
        count[rt, ru] += 1
        areas[rt, ru] += F(1, nt*nu)
    # Reconstruct the generator's splitting tree independently. Every internal
    # rectangle splits into two covering, interior-disjoint children. Consuming
    # precisely the supplied leaves proves coverage AND absence of overlaps.
    stack = [(r, 0, 1, s, 0, 1) for r in range(6) for s in range(r, 6)]
    consumed = set()
    visits = 0
    while stack:
        rt, i, nt, ru, j, nu = key = stack.pop()
        visits += 1
        if key in leaves:
            consumed.add(key)
            continue
        if nt*nu > 2**42:
            raise AssertionError('missing leaf or cover gap')
        wt = (ranges[rt][2] - ranges[rt][1]).b / nt
        wu = (ranges[ru][2] - ranges[ru][1]).b / nu
        if wt >= wu:
            stack.extend([(rt, 2*i, 2*nt, ru, j, nu),
                          (rt, 2*i+1, 2*nt, ru, j, nu)])
        else:
            stack.extend([(rt, i, nt, ru, 2*j, 2*nu),
                          (rt, i, nt, ru, 2*j+1, 2*nu)])
    if consumed != set(leaves) or visits != result['visited']:
        raise AssertionError('cover tree or visitation count mismatch')
    if any(areas[r, s] != 1 for r in range(6) for s in range(r, 6)):
        raise AssertionError('a parameter rectangle is not fully covered')
    if len(rows) != result['leaves'] or visits != 2*len(rows)-21:
        raise AssertionError('binary forest identity failed')
    normalized = sorted(rows, key=lambda x: x['cell'])
    for name, expected in result['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != expected:
            raise AssertionError('generator source does not match receipt: '+name)
    return {'status': 'passed', 'coefficient': '93/100',
            'parameter_box': result['parameter_box'], 'roots': 21,
            'visited': visits, 'leaves': len(rows), 'frontier': 0,
            'maximum_squared_upper_exact': str(maximum),
            'per_root_leaves': {f'{r},{s}': count[r,s] for r in range(6) for s in range(r,6)},
            'all_root_areas_exactly_one': True, 'tree_partition_verified': True,
            'canonical_leaf_sha256': hashlib.sha256(canonical(normalized)).hexdigest(),
            'source_hashes': result['source_hashes'],
            'arithmetic': '90-bit outward dyadic intervals; exact rational comparisons',
            'scope': 'rank-two continuum quotient upper bound; analytic identities are inputs',
            'not_claimed': ['effective original-sofa entry', 'optimal feasible coefficient',
                            'Lean verification']}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, help='validate a locally generated full receipt')
    ap.add_argument('--output', type=Path, default=Path('translation-quotient-replay.json'))
    ap.add_argument('--expect', type=Path, help='compare invariant fields with a committed replay')
    args = ap.parse_args()
    result = json.loads(args.input.read_text()) if args.input else certificate('0.93', 1000000, 40)
    summary = check_cover(result)
    # An explicit failing target exercises the non-acceptance branch.
    negative = certificate('0.5', 100, 4)
    if negative['status'] == 'passed':
        raise AssertionError('negative coefficient control unexpectedly accepted')
    summary['negative_control'] = {'coefficient': '1/2', 'status': negative['status'],
        'visited': negative['visited'], 'failed_cells': len(negative['failed']),
        'frontier': negative['frontier']}
    summary['replay_source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.expect:
        old = json.loads(args.expect.read_text())
        if canonical(summary) != canonical(old):
            raise AssertionError('recomputed invariant receipt differs')
    args.output.write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
