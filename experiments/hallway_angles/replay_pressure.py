"""Replay saved integer control points, validate, or make interval certificates."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import numpy as np
from geometry import Motion
from pressure_search import interpolation_matrix
from fast_geometry import enclose_fast


def decode_candidate(record: dict, denominator: int) -> Motion:
    if not isinstance(denominator,int) or denominator<=0:
        raise ValueError('invalid control denominator')
    controls=np.asarray(record['controls_i'],dtype=float)/denominator
    n=len(controls)
    samples=(n-1)*record['subdivisions']+1
    matrix=interpolation_matrix(n,samples,record['basis'])
    dense=matrix@controls
    dense[0,1]=0.
    dense[-1,1]=0. if record['mode']=='forward' else 1.
    dense[samples//2,0]=0.
    return Motion(math.radians(float(record['bend_degrees'])),record['mode'],dense)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=Path(__file__).parent/'results'/'pressure-candidates.json')
    parser.add_argument('--candidate',required=True)
    parser.add_argument('--samples',type=int,default=16385)
    parser.add_argument('--skip-enclosure',action='store_true')
    parser.add_argument('--certificate',type=Path)
    parser.add_argument('--rows',type=int,default=4096)
    parser.add_argument('--inset',type=float,default=.00015)
    parser.add_argument('--proposal-subdivisions',type=int,default=16)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--max-depth',type=int,default=8)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    if data.get('format')!='hallway-pressure-candidates-v1':raise ValueError('unknown data format')
    choices=[r for r in data['candidates'] if r['id']==args.candidate]
    if len(choices)!=1:raise ValueError('candidate must identify exactly one record')
    if args.verify and not args.certificate:raise ValueError('--verify requires --certificate')
    record=choices[0];motion=decode_candidate(record,data['control_denominator'])
    out={'candidate':args.candidate,'controls_file_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest()}
    if not args.skip_enclosure:
        n=len(motion.corners)-1
        if args.samples<=1 or (args.samples-1)%n:raise ValueError('samples must subdivide the saved path')
        out['enclosure']=enclose_fast(motion,(args.samples-1)//n,True)[0]
    if args.certificate:
        from make_certificate import propose
        certificate=propose(motion,args.rows,args.inset,args.proposal_subdivisions,str(record['bend_degrees']))
        args.certificate.parent.mkdir(parents=True,exist_ok=True)
        args.certificate.write_text(json.dumps(certificate,separators=(',',':'))+'\n')
        out['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
        out['proposal']=certificate['proposal']
        if args.verify:
            from interval_verify import verify
            out['interval']=verify(certificate,args.max_depth)
            out['interval'].pop('selected_indices')
            r=out['interval'];q=r['area_numerator']*10**6//r['area_denominator']
            r['area_decimal_floor_6']=f'{q//10**6}.{q%10**6:06d}'
    text=json.dumps(out,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
