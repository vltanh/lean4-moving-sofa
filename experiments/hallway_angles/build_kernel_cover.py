"""Propose and independently check a gap-free kernel-dual cover locally.

Only this builder uses scipy. The verifier uses the standard library.
Each accepted record is saved before proceeding; no CI or remote jobs.
A partially completed file is not a complete angle certificate.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time,argparse
from reverse_kernel_proposals import make
from reverse_kernel_dual import rationalize,verify_box

ROOT=Path(__file__).resolve().parent


def run(part,seconds=25):
    if part not in ('moment','arms'):raise ValueError(part)
    if not seconds>0:raise ValueError('positive execution budget required')
    path=ROOT/f'{part}_cover_work.json'
    if path.exists():data=json.loads(path.read_text())
    else:
        if part=='moment':box=['57/50','123/100',None,None]
        else:box=['123/100','3927/2500','0','1/2']
        data=dict(part=part,queue=[box],accepted=[],rejected=0)
    begin=time.monotonic()
    while data['queue'] and time.monotonic()-begin<seconds:
        box=data['queue'].pop();el,eh=map(F,box[:2]);ul=None if box[2] is None else F(box[2]);uh=None if box[3] is None else F(box[3])
        e=(el+eh)/2;u=None if ul is None else (ul+uh)/2
        proposal=make(float(e),u,N=24,checks=4)
        record=rationalize(proposal)
        record['e']=str(e)
        check=verify_box(record,el,eh,ul,uh,subdivisions=8)
        if check['accepted']:
            data['accepted'].append(dict(box=box,dual=record,check=check))
        else:
            data['rejected']+=1
            # Subdivision is a search rule, never mathematical acceptance.
            if ul is None or 10*(eh-el)>(uh-ul):
                mid=(el+eh)/2
                data['queue'].extend([[str(el),str(mid),box[2],box[3]],[str(mid),str(eh),box[2],box[3]]])
            else:
                mid=(ul+uh)/2
                data['queue'].extend([[str(el),str(eh),str(ul),str(mid)],[str(el),str(eh),str(mid),str(uh)]])
        temp=path.with_suffix('.tmp');temp.write_text(json.dumps(data,separators=(',',':')));temp.replace(path)
    print(json.dumps(dict(part=part,accepted=len(data['accepted']),pending=len(data['queue']),rejected=data['rejected'],elapsed=time.monotonic()-begin)))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('part',choices=['moment','arms']);p.add_argument('--seconds',type=float,default=25)
    a=p.parse_args();run(a.part,a.seconds)
