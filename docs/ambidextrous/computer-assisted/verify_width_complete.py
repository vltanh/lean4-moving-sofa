"""Stateless complete replay of a width-two covering certificate.

No checkpoint, search log, numerical score, or claimed bound is trusted.
Run with --pure for the standard-library arbitrary-precision proof kernel.
"""
import argparse,gzip,hashlib,json,time
from pathlib import Path
from exact_width import (template_certificate, exact_area_bound,
                         verify_template_box, next_axis, MAX_DEPTH_PER_COORDINATE)


def replay_python(codes, rows):
    stack=[([0]*8,[0]*8)]; counts=[0,0,0]; maximum_depth=0
    for code in codes:
        if not stack: raise ValueError('trailing data')
        ids,dep=stack.pop()
        if code==0:
            axis=next_axis(dep)
            if dep[axis]>=MAX_DEPTH_PER_COORDINATE:raise ValueError('excessive depth')
            d=dep.copy();d[axis]+=1;l=ids.copy();r=ids.copy();l[axis]*=2;r[axis]=l[axis]+1
            maximum_depth=max(maximum_depth,d[axis]);stack.append((r,d.copy()));stack.append((l,d))
        elif code==1:
            n,d=exact_area_bound(ids,dep)
            if n*250>d*411:raise ValueError('false spatial area claim')
        elif code==2:
            if not verify_template_box(ids,dep,rows):raise ValueError('invalid template domain')
        else:raise ValueError('unknown or unresolved node')
        counts[code]+=1
    if stack:raise ValueError('incomplete covering')
    return counts,maximum_depth


def replay_accelerated(codes, rows):
    import numpy as np
    from numba import njit
    from fast_exact import area_bound_int,template_box_int,axis_int

    @njit(cache=True)
    def replay(data, coefficients):
        # Depth is at most 8*13; a binary DFS stack has at most depth+1 entries.
        indices=np.zeros((106,8),np.int64);depths=np.zeros((106,8),np.int64)
        top=1;counts=np.zeros(3,np.int64);md=0
        for code in data:
            if top==0:raise ValueError('trailing data')
            top-=1;ids=indices[top].copy();dep=depths[top].copy()
            if code==0:
                ax=axis_int(dep)
                if dep[ax]>=13:raise ValueError('excessive depth')
                d=dep.copy();d[ax]+=1;l=ids.copy();r=ids.copy();l[ax]*=2;r[ax]=l[ax]+1
                if top+2>106:raise ValueError('stack overflow')
                md=max(md,d[ax]);indices[top]=r;depths[top]=d
                indices[top+1]=l;depths[top+1]=d;top+=2
            elif code==1:
                n,d=area_bound_int(ids,dep)
                # Independent division/remainder comparison avoids n*250 overflow.
                integer=n//d;remainder=n%d
                cap=(d//250)*161+((d%250)*161)//250
                if integer>1 or (integer==1 and remainder>cap):
                    raise ValueError('false spatial area claim')
            elif code==2:
                if not template_box_int(ids,dep,coefficients):
                    raise ValueError('invalid template domain')
            else:raise ValueError('unknown or unresolved node')
            counts[code]+=1
        if top!=0:raise ValueError('incomplete covering')
        return counts,md

    answer,md=replay(np.frombuffer(codes,dtype=np.uint8),np.array(rows,dtype=np.int64))
    return [int(x) for x in answer],int(md)


def verify(path, pure=False):
    data=path.read_bytes()
    if path.suffix=='.gz':data=gzip.decompress(data)
    rows,maximum,pivots,opt=template_certificate()
    if max(abs(x) for row in rows for x in row)>=2**31:
        raise ValueError('template coefficient overflow guard')
    start=time.time()
    counts,md=(replay_python if pure else replay_accelerated)(data,rows)
    result={'complete':True,'target':'411/250','tree_sha256':hashlib.sha256(data).hexdigest(),
            'visited':len(data),'splits':counts[0],'area_leaves':counts[1],
            'template_leaves':counts[2],'maximum_coordinate_depth':md,
            'template_maximum':str(maximum),'seconds':time.time()-start,
            'mode':'arbitrary_precision_python' if pure else 'guarded_int64',
            'independently_reviewed':False,'lean_or_ci_used':False}
    if counts[1]+counts[2]!=counts[0]+1:raise ValueError('tree count identity failed')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('tree',type=Path);p.add_argument('--pure',action='store_true');p.add_argument('--output',type=Path)
    a=p.parse_args();result=verify(a.tree,a.pure);text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text)
