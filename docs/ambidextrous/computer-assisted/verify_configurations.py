"""Exact ordinary-area certificates for the partial-terminal-angle exclusion.

Only standard-library rational/integer arithmetic is trusted. Neither SciPy,
LP optimality, support regularity, nor a calibrated sofa functional is used.
The mathematical argument is configuration-area-certificate.md (CF1--CF2).
"""
from __future__ import annotations
import argparse
import base64
import zlib
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from typing import Any

START = Q(12, 25)
END = Q(29, 50)
TARGET = Q(41, 25)
THRESHOLD = Q(8, 5)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def rational(value: Any) -> Q:
    require(type(value) is str and len(value) <= 80, 'Expected a rational string')
    return Q(value)


def integer(value: Any, lo: int, hi: int, what: str) -> int:
    require(type(value) is int and lo <= value <= hi, 'Invalid '+what)
    return value


def direction(r: Q) -> tuple[Q, Q]:
    require(0 <= r <= 1, 'Angle must be in the conventional quarter')
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)


def frame_data(row: dict, rlo: Q, rhi: Q) -> tuple:
    require(set(row) == {'turn', 'r'}, 'Unexpected frame fields')
    r = rational(row['r'])
    c, s = direction(r)
    if row['turn'] == 'lower':
        require(r <= rlo, 'Lower frame not guaranteed to be visited')
        normals = ((c,s),(-s,c))
    elif row['turn'] == 'upper':
        ca, sa = direction(rhi)
        independent = c >= 1/THRESHOLD
        coupled = ca*c-sa*s <= 0 and sa*c+ca*s > 1/THRESHOLD
        require(independent or coupled, 'Upper frame not guaranteed to be visited')
        normals = ((c,-s),(-s,-c))
    else:
        raise ValueError('Unknown turning direction')
    ca0,sa0 = direction(rlo)
    ca1,sa1 = direction(rhi)
    bounds = []
    for nx,ny in normals:
        aa = sorted((nx/ca0,nx/ca1))
        bb = sorted((ny-nx*sa0/ca0,ny-nx*sa1/ca1))
        bounds.append((aa,bb))
    return tuple(bounds)


def product_min(a: list, b: tuple) -> Q:
    return min(x*y for x in a for y in b)


def separation(bounds: tuple, p: int, q: int, n: int) -> Q:
    ip,jp = divmod(p,n)
    iq,jq = divmod(q,n)
    dx = (Q(iq-ip-1,n),Q(iq-ip+1,n))
    dy = (Q(jq-jp-1,n),Q(jq-jp+1,n))
    return product_min(bounds[0],dx)+product_min(bounds[1],dy)


def verify_bin(data: dict) -> dict:
    require(set(data) == {'lo','hi','n','frames','triples'}, 'Unexpected bin fields')
    lo,hi = rational(data['lo']),rational(data['hi'])
    require(START <= lo < hi <= END, 'Unsupported endpoint interval')
    n = integer(data['n'],1,64,'grid size')
    count = n*n
    require(type(data['frames']) is list and 1 <= len(data['frames']) <= 80,
            'Invalid frame list')
    frames = [frame_data(f,lo,hi) for f in data['frames']]
    require(type(data['triples']) is list and len(data['triples']) <= 20000,
            'Invalid triple list')
    loads = [0]*count
    total = 0
    minimum = None
    for row in data['triples']:
        require(type(row) is list and len(row)==5, 'Malformed triple witness')
        fi = integer(row[0],0,len(frames)-1,'frame index')
        p,q,r = [integer(i,0,count-1,'cell index') for i in row[1:4]]
        require(len({p,q,r})==3, 'The three cells must be distinct')
        weight = integer(row[4],1,10**15,'integer weight')
        d1 = separation(frames[fi][0],p,q,n)
        d2 = separation(frames[fi][1],p,r,n)
        require(d1>1 and d2>1, 'Unproved forbidden triple')
        margin = min(d1,d2)-1
        minimum = margin if minimum is None else min(minimum,margin)
        for i in (p,q,r):
            loads[i] += weight
        total += weight
    require(total>0, 'Empty weighted certificate')
    # Renormalization makes every degree at most one exactly. Thus any small
    # numerical infeasibility in a proposed matching is removed, never trusted.
    denominator = max(loads)
    require(denominator>0, 'Zero denominator')
    matching = Q(total,denominator)
    unoccupied = sum(Q(denominator-x,denominator) for x in loads)
    coefficient_sum = 2*matching+unoccupied
    require(coefficient_sum == count-matching, 'Dual bookkeeping mismatch')
    cmin,_ = direction(hi)
    upper = coefficient_sum/(count*cmin)
    require(upper < TARGET, 'The exact area bound does not reach the target')
    return {'lo':str(lo),'hi':str(hi),'grid_n':n,
            'verified_triples':len(data['triples']),
            'matching_mass':str(matching),'minimum_strict_margin':str(minimum),
            'area_upper':str(upper),'target_margin':str(TARGET-upper)}


def verify(data: dict) -> dict:
    require(set(data)=={'format','bins'},'Unexpected root fields')
    require(data['format']=='ambi-forbidden-triples-v1','Unknown format')
    require(type(data['bins']) is list and 1<=len(data['bins'])<=100,
            'Invalid covering')
    expected=START
    results=[]
    for item in data['bins']:
        require(rational(item['lo'])==expected,'Gap or out-of-order endpoint interval')
        result=verify_bin(item)
        expected=rational(item['hi'])
        results.append(result)
    require(expected==END,'Incomplete endpoint covering')
    return {'accepted':True,'ordinary_area_bound':str(TARGET),
            'excluded_half_tangent_interval':['0',str(END)],
            'both_turns':'Both reduced endpoint magnitudes exceed 2 arctan(29/50) for area >= 41/25',
            'unrestricted_optimality_proved':False,
            'full_quarter_turns_proved':False,
            'arithmetic':'Python unbounded integers and fractions.Fraction only',
            'bins':results}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    stored=args.certificate.read_bytes()
    require(len(stored)<=10_000_000,'Certificate too large')
    if args.certificate.suffix=='.b64':
        compressed=base64.b64decode(b''.join(stored.split()),validate=True)
        dec=zlib.decompressobj()
        raw=dec.decompress(compressed,10_000_001)
        require(len(raw)<=10_000_000 and dec.eof and not dec.unconsumed_tail
                and not dec.unused_data,'Invalid or oversized compressed certificate')
    else:
        raw=stored
    result=verify(json.loads(raw))
    result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
    result['verifier_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
