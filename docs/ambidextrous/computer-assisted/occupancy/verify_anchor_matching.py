"""Exact replay of ordinary-area exclusions, not an optimality certificate.

Only Python unbounded integers and fractions.Fraction decide acceptance.
Empty cells are re-derived; matching pairs must be disjoint and independently
incompatible. Every width interval in the declared region must be covered.
"""
from __future__ import annotations
import argparse
import base64
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import lcm
from pathlib import Path
import re
import zlib

THRESHOLD = Q(8, 5)
TARGET = Q(411, 250)
LIMIT = 50_000_000


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(value) -> Q:
    require(type(value) is str and len(value) <= 80 and
            re.fullmatch(r'[+-]?\d+(?:/\d+)?', value) is not None,
            'Expected an integer or fraction string')
    return Q(value)


def interval(value):
    require(type(value) is list and len(value) == 2, 'Expected interval')
    lo, hi = map(rat, value)
    require(lo <= hi, 'Reversed interval')
    return lo, hi


def site_data(spec, parameters):
    wl, wh = interval(spec['width'])
    al, ah = interval(spec['left_height'])
    bl, bh = interval(spec['right_height'])
    require(1 < wl <= wh <= 4 and 0 <= al <= ah <= 1 and
            0 <= bl <= bh <= 1, 'Invalid parameter range')
    require(type(spec['grid']) is list and len(spec['grid']) == 2,
            'Invalid grid')
    nx, ny = spec['grid']
    require(all(type(k) is int and 1 <= k <= 256 for k in (nx, ny)),
            'Grid outside supported range')
    den = lcm(nx, ny, *(x.denominator for x in (wl, wh, al, ah, bl, bh)))
    sites = [(i*den//nx, (i+1)*den//nx, j*den//ny, (j+1)*den//ny)
             for i in range(nx) for j in range(ny)]
    sites += [(0, 0, int(al*den), int(ah*den)),
              (den, den, int(bl*den), int(bh*den))]
    frames = []
    for text in parameters:
        r = rat(text)
        require(0 < r < 1, 'Invalid half-angle')
        p, q = r.numerator, r.denominator
        c, s, d = q*q-p*p, 2*p*q, q*q+p*p
        for turn, sign in (('lower', 1), ('upper', -1)):
            extreme = wl*c + ((bl-ah) if sign == 1 else (al-bh))*s
            if Q(c, d) >= Q(5, 8) or extreme > d:
                frames.append((text, turn, ((c, sign*s), (-s, sign*c)),
                               d*den*den))
    require(frames, 'No guaranteed hallway frames')
    return sites, nx*ny, (int(wl*den), int(wh*den), den), frames


def separated(base, other, normal, scale, threshold):
    u, v = normal
    wl, wh, den = scale
    dx = other[0]-base[1] if u >= 0 else other[1]-base[0]
    dy = other[2]-base[3] if v >= 0 else other[3]-base[2]
    return min(u*wl*dx, u*wh*dx) + v*den*dy > threshold


def incompatible(ids, sites, scale, frames):
    # All sites in ids are assumed met. Find a uniformly forbidden ordered
    # triple; repeated witnesses are allowed by CF1.
    for _, _, normals, threshold in frames:
        for p in ids:
            if (any(separated(sites[p], sites[q], normals[0], scale, threshold)
                    for q in ids if q != p) and
                any(separated(sites[p], sites[q], normals[1], scale, threshold)
                    for q in ids if q != p)):
                return True
    return False


def verify_bin(spec, pairs, parameters):
    sites, count, scale, frames = site_data(spec, parameters)
    anchors = (count, count+1)
    require(not incompatible(anchors, sites, scale, frames),
            'All-anchor contradiction needs an infeasibility certificate')
    empty = {i for i in range(count)
             if incompatible((i, *anchors), sites, scale, frames)}
    require(type(pairs) is list and len(pairs) <= count//2,
            'Invalid matching size')
    used = set(empty)
    for pair in pairs:
        require(type(pair) is list and len(pair) == 2 and
                all(type(i) is int and 0 <= i < count for i in pair),
                'Invalid matching pair')
        a, b = pair
        require(a != b and a not in used and b not in used,
                'Matching is not disjoint from itself and the empty cells')
        require(incompatible((a, b, *anchors), sites, scale, frames),
                'Pair incompatibility not proved')
        used.update(pair)
    occupation = count-len(empty)-len(pairs)
    upper = interval(spec['width'])[1]*Q(occupation, count)
    require(upper < TARGET, 'Exact area upper bound does not exclude target')
    return dict(width=spec['width'], grid=spec['grid'], empty_cells=len(empty),
                disjoint_pairs=len(pairs), occupation_upper=occupation,
                conditional_area_upper=str(upper),
                unconditional_area_upper=str(max(THRESHOLD, upper)),
                target_margin=str(TARGET-upper), guaranteed_frames=len(frames))


def verify(data):
    require(type(data) is dict and set(data) == {'format', 'region', 'parameters', 'bins'},
            'Invalid root')
    require(data['format'] == 'ambi-anchor-matching-v1', 'Unknown format')
    region = data['region']
    require(set(region) == {'width', 'left_height', 'right_height'}, 'Invalid region')
    start, stop = interval(region['width'])
    parameters = data['parameters']
    require(type(parameters) is list and 1 <= len(parameters) <= 100 and
            len(set(parameters)) == len(parameters), 'Invalid frame parameters')
    require(type(data['bins']) is list and 1 <= len(data['bins']) <= 1000,
            'Invalid covering')
    reports = []
    for item in data['bins']:
        require(set(item) == {'width', 'grid', 'pairs'}, 'Invalid bin')
        lo, hi = interval(item['width'])
        require(lo == start and lo < hi <= stop, 'Gap or overlap in width covering')
        spec = dict(width=item['width'], left_height=region['left_height'],
                    right_height=region['right_height'], grid=item['grid'])
        reports.append(verify_bin(spec, item['pairs'], parameters))
        start = hi
    require(start == stop, 'Incomplete width covering')
    return dict(accepted=True, region=region, target=str(TARGET),
                unconditional_area_upper=str(max(Q(x['unconditional_area_upper']) for x in reports)),
                bins=reports, arithmetic='Python unbounded integers and Fraction',
                global_optimality_proved=False, ci_or_lean_used=False,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def read_certificate(path):
    raw = path.read_bytes()
    require(len(raw) <= LIMIT, 'Oversized file')
    if path.suffix == '.b64':
        compressed = base64.b64decode(b''.join(raw.split()), validate=True)
        decoder = zlib.decompressobj()
        raw = decoder.decompress(compressed, LIMIT+1)
        require(len(raw) <= LIMIT and decoder.eof and not decoder.unconsumed_tail
                and not decoder.unused_data, 'Invalid or oversized compression')
    return raw, json.loads(raw)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw, data = read_certificate(args.certificate)
    result = verify(data)
    result['certificate_sha256'] = sha256(raw).hexdigest()
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')
