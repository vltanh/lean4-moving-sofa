"""Exact replay for anchored occupation certificates, without trusting an LP.

Certificates cover a stated interval of one reduced terminal half-tangent.
They do not prove Romik optimality or full quarter turns. Geometry, nonnegative
integer dual weights, and every covering endpoint are checked from scratch.
Only Python integers and fractions.Fraction enter acceptance decisions.
"""
from __future__ import annotations
import argparse
import base64
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import zlib

TARGET = Q(41, 25)
START = Q(12, 25)


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def rat(x) -> Q:
    require(type(x) is str and len(x) <= 80, 'Invalid rational encoding')
    return Q(x)


def integer(x, lo: int, hi: int) -> int:
    require(type(x) is int and lo <= x <= hi, 'Invalid integer')
    return x


def direction(r: Q) -> tuple[Q, Q]:
    require(0 <= r <= 1, 'Direction outside a conventional quarter')
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)


def product_min(a, b):
    return min(x*y for x in a for y in b)


def strip_width_limit(r: Q) -> Q:
    return Q(4) if r == 1 else min(Q(4), (1+r)/(1-r))


def verify_leaf(data: dict, alo: Q, ahi: Q, glo: Q, ghi: Q) -> dict:
    require(set(data) == {'wlo','whi','nx','ny','nangles','denominator','terms'},
            'Unexpected leaf fields')
    wlo, whi = rat(data['wlo']), rat(data['whi'])
    require(2 <= wlo < whi <= 4, 'Invalid width box')
    nx, ny = integer(data['nx'],1,512), integer(data['ny'],1,256)
    count = nx*ny
    require(count <= 65536, 'Grid too large')
    nangles = integer(data['nangles'],1,128)
    den = integer(data['denominator'],1,10**15)
    require(type(data['terms']) is list and 0 < len(data['terms']) <= 200000,
            'Missing or oversized dual')

    @lru_cache(None)
    def cell(i: int):
        integer(i,0,count+1)
        if i == count:
            return Q(0),Q(0),Q(0),Q(1)
        if i == count+1:
            return wlo,whi,Q(0),Q(1)
        x,y = divmod(i,ny)
        return Q(x)*whi/nx,Q(x+1)*whi/nx,Q(y,ny),Q(y+1,ny)

    @lru_cache(None)
    def frame(fi: int):
        integer(fi,0,2*nangles-1)
        upper = fi >= nangles
        j = fi % nangles + 1
        r = (glo if upper else alo)*j/nangles
        c,s = direction(r)
        sign = -1 if upper else 1
        return (c,sign*s),(-s,sign*c)

    @lru_cache(None)
    def projection(i: int, fi: int, coordinate: int):
        x0,x1,y0,y1 = cell(i)
        a,b = frame(fi)[coordinate]
        return (min(a*x0,a*x1)+min(b*y0,b*y1),
                max(a*x0,a*x1)+max(b*y0,b*y1))

    terminal = []
    for r0,r1,sign in ((alo,ahi,1),(glo,ghi,-1)):
        c0,s0 = direction(r0)
        c1,s1 = direction(r1)
        terminal.append(((c1,c0),tuple(sorted((sign*s0,sign*s1)))))

    loads = [0]*count
    rhs = 0
    min_margin = None
    kinds = {'h':0,'s':0}
    for row in data['terms']:
        require(type(row) is list and len(row) in (5,6), 'Malformed witness')
        kind = row[0]
        if kind == 'h':
            require(len(row)==6, 'Hallway witness needs six fields')
            _,fi,p,q,r,weight = row
            for i in (p,q,r): integer(i,0,count+1)
            frame(fi)
            d1 = projection(q,fi,0)[0]-projection(p,fi,0)[1]
            d2 = projection(r,fi,1)[0]-projection(p,fi,1)[1]
            margin = min(d1,d2)-1
            edge = set((p,q,r))
        elif kind == 's':
            require(len(row)==5, 'Strip witness needs five fields')
            _,fi,p,q,weight = row
            integer(fi,0,1)
            for i in (p,q): integer(i,0,count+1)
            pc,qc = cell(p),cell(q)
            dx = (qc[0]-pc[1],qc[1]-pc[0])
            dy = (qc[2]-pc[3],qc[3]-pc[2])
            cn,sn = terminal[fi]
            margin = product_min(cn,dx)+product_min(sn,dy)-1
            edge = set((p,q))
        else:
            raise ValueError('Unknown geometric witness')
        require(margin > 0, 'Unproved strict geometric separation')
        require(len(edge) >= 2, 'Degenerate witness')
        weight = integer(weight,1,10**15)
        min_margin = margin if min_margin is None else min(min_margin,margin)
        kinds[kind] += 1
        # Both virtual extreme-witness variables are exactly one, not fractional.
        rhs += weight*(len(edge)-1-sum(i >= count for i in edge))
        for i in edge:
            if i < count:
                loads[i] += weight
    numerator = rhs + sum(max(den-c,0) for c in loads)
    upper = whi*Q(numerator,count*den)
    require(upper < TARGET, 'Dual bound does not strictly beat the area threshold')
    return {'wlo':str(wlo),'whi':str(whi),'nx':nx,'ny':ny,
            'verified_terms':kinds,'area_upper':str(upper),
            'margin_below_target':str(TARGET-upper),
            'minimum_geometric_margin':str(min_margin)}


def verify(data: dict) -> dict:
    require(set(data)=={'format','end','alpha_bins'}, 'Unexpected root fields')
    require(data['format']=='anchored-terminal-v1','Unknown certificate format')
    end = rat(data['end'])
    require(START < end < 1, 'Invalid claimed endpoint range')
    require(direction(START)[0] > 1/TARGET, 'Initial strip exclusion failed')
    require(type(data['alpha_bins']) is list and 0 < len(data['alpha_bins']) <= 256,
            'Invalid alpha covering')
    expected_a = START
    records = []
    for ab in data['alpha_bins']:
        require(set(ab)=={'lo','hi','forced_gamma_lo','gamma_bins'},'Unexpected alpha fields')
        alo,ahi,gstart = rat(ab['lo']),rat(ab['hi']),rat(ab['forced_gamma_lo'])
        require(alo==expected_a and alo < ahi <= end,'Gap or overlap in alpha covering')
        require(0 <= gstart < 1,'Invalid forced gamma lower bound')
        ca,sa = direction(ahi)
        cg,sg = direction(gstart)
        require(ca*cg-sa*sg <= 0 and sa*cg+ca*sg > 1/TARGET,
                'Unproved coupled terminal-angle restriction')
        require(type(ab['gamma_bins']) is list and 0 < len(ab['gamma_bins']) <= 256,
                'Invalid gamma covering')
        expected_g = gstart
        for gb in ab['gamma_bins']:
            require(set(gb)=={'lo','hi','width_leaves'},'Unexpected gamma fields')
            glo,ghi = rat(gb['lo']),rat(gb['hi'])
            require(glo==expected_g and glo < ghi <= 1,'Gap or overlap in gamma covering')
            wend = min(strip_width_limit(ahi),strip_width_limit(ghi))
            require(type(gb['width_leaves']) is list and len(gb['width_leaves']) <= 1024,
                    'Invalid width covering')
            if wend <= 2:
                require(not gb['width_leaves'],'Unneeded leaves for analytically empty width domain')
            else:
                expected_w = Q(2)
                for leaf in gb['width_leaves']:
                    require(rat(leaf['wlo'])==expected_w,'Gap or overlap in width covering')
                    require(rat(leaf['whi'])<=wend,'Width leaf exceeds its covered domain')
                    rec = verify_leaf(leaf,alo,ahi,glo,ghi)
                    records.append({'alpha':[str(alo),str(ahi)],
                                    'gamma':[str(glo),str(ghi)],**rec})
                    expected_w=rat(leaf['whi'])
                require(expected_w==wend,'Incomplete width covering')
            expected_g=ghi
        require(expected_g==1,'Incomplete gamma covering')
        expected_a=ahi
    require(expected_a==end,'Incomplete alpha covering')
    require(bool(records),'Empty certificate')
    return {'accepted':True,'area_threshold':str(TARGET),
            'excluded_terminal_half_tangent':['0',str(end)],
            'maximum_verified_leaf_bound':str(max(Q(r['area_upper']) for r in records)),
            'leaf_count':len(records),'leaves':records,
            'arithmetic':'Python integers and fractions.Fraction only',
            'unrestricted_optimality_proved':False,'full_quarter_turns_proved':False,
            'scope':'Terminal-angle exclusion conditional on the stated geometric reductions',
            'ci_or_lean_used':False}


def decode(path: Path) -> bytes:
    stored=path.read_bytes()
    require(len(stored)<=30_000_000,'Oversized stored certificate')
    if path.suffix!='.b64':
        return stored
    compressed=base64.b64decode(b''.join(stored.split()),validate=True)
    dec=zlib.decompressobj()
    raw=dec.decompress(compressed,30_000_001)
    require(len(raw)<=30_000_000 and dec.eof and not dec.unconsumed_tail
            and not dec.unused_data,'Invalid compressed certificate')
    return raw


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    raw=decode(args.certificate)
    result=verify(json.loads(raw))
    result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
    result['verifier_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
