"""Untrusted matching discovery; replay each accepted certificate exactly.

The generator builds only conflicts valid for the whole parameter box, then
uses a graph algorithm to propose disjoint pairs. The independent verifier
reconstructs every accepted inequality with unbounded integers. No solver
status or discovery arithmetic is trusted by that replay.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import heapq
import json
from pathlib import Path
from time import perf_counter
import numpy as np
import networkx as nx
from verify_anchor_matching import site_data, interval, TARGET, verify_bin

DEFAULT_PARAMETERS = [str(Q(k, 50)) for k in range(5, 40)]


def conflict_graph(spec: dict, parameters: list[str]):
    sites, count, scale, frames = site_data(spec, parameters)
    wl, wh, den = scale
    coords = np.array(sites, dtype=np.int64)
    total = count+2
    blocked = np.zeros(count, dtype=bool)
    conflicts = np.zeros((count, count), dtype=bool)
    for _, _, normals, threshold in frames:
        relations = []
        for u, v in normals:
            # Guard all acceleration arithmetic in Python integers first.
            bound = abs(u)*max(abs(wl),abs(wh))*den+abs(v)*den*den
            if bound >= 2**62 or threshold >= 2**62:
                raise OverflowError('Use smaller rational denominators')
            relation = np.ones((total,total), dtype=bool)
            for w in set((wl,wh)):
                lo = u*w*coords[:,0 if u>=0 else 1]+v*den*coords[:,2 if v>=0 else 3]
                hi = u*w*coords[:,1 if u>=0 else 0]+v*den*coords[:,3 if v>=0 else 2]
                relation &= lo[None,:]-hi[:,None]>threshold
            relations.append(relation)
        U,V = relations
        anchors = (count,count+1)
        if any(U[a,b] and V[a,b] for a,b in (anchors,anchors[::-1])):
            raise ValueError('All-anchor contradiction; need distinct leaf type')
        ua = U[:count,count:].any(axis=1)
        va = V[:count,count:].any(axis=1)
        blocked |= ua&va
        # Contradictory triple with one of the free cells as its base.
        directional = (U[:count,:count]|ua[:,None])&(V[:count,:count]|va[:,None])
        conflicts |= directional|directional.T
        # Contradictory triple with a mandatory anchor as its base.
        for a,b in (anchors, anchors[::-1]):
            u,v = U[a,:count],V[a,:count]
            blocked |= (u|U[a,b])&(v|V[a,b])
            conflicts |= (u[:,None]|u[None,:]|U[a,b])&(v[:,None]|v[None,:]|V[a,b])
    conflicts[blocked,:] = False
    conflicts[:,blocked] = False
    np.fill_diagonal(conflicts,False)
    return blocked, conflicts, len(frames)


def greedy_matching(adj: np.ndarray):
    neighbors = [set(map(int,np.flatnonzero(row))) for row in adj]
    heap = [(len(n),i) for i,n in enumerate(neighbors) if n]
    heapq.heapify(heap)
    used = set()
    pairs = []
    while heap:
        d,i=heapq.heappop(heap)
        if i in used or len(neighbors[i])!=d or not d:
            continue
        j=min(neighbors[i], key=lambda k:(len(neighbors[k]),k))
        pairs.append([min(i,j),max(i,j)])
        used.update((i,j))
        for x in (i,j):
            for k in list(neighbors[x]):
                neighbors[k].discard(x)
                if k not in used and neighbors[k]:
                    heapq.heappush(heap,(len(neighbors[k]),k))
            neighbors[x].clear()
    return sorted(pairs)


def discover(spec: dict, parameters: list[str] | None = None,
             exact_matching: bool = False, replay: bool = True):
    start=perf_counter()
    if parameters is None:
        parameters=DEFAULT_PARAMETERS
    blocked, adj, nframes=conflict_graph(spec,parameters)
    pairs=greedy_matching(adj)
    if exact_matching:
        graph=nx.from_numpy_array(adj)
        if nx.is_bipartite(graph):
            colors=nx.bipartite.color(graph)
            top={i for i,c in colors.items() if c==0}
            match=nx.bipartite.hopcroft_karp_matching(graph,top_nodes=top)
            pairs=sorted(sorted((i,j)) for i,j in match.items() if i in top)
        else:
            pairs=sorted([sorted(e) for e in nx.max_weight_matching(graph,maxcardinality=True)])
    count=len(blocked)
    upper=interval(spec['width'])[1]*Q(count-int(blocked.sum())-len(pairs),count)
    report=dict(spec=spec,empty_cells=int(blocked.sum()),disjoint_pairs=len(pairs),
                edges=int(adj.sum())//2,guaranteed_frames=nframes,
                proposal_upper=str(upper),target_margin=str(TARGET-upper),
                target_reached=upper<TARGET,exact_replay=None,
                algorithm='networkx maximum matching' if exact_matching else 'minimum-degree greedy',
                discovery_seconds=perf_counter()-start)
    if replay and upper<TARGET:
        report['exact_replay']=verify_bin(spec,pairs,parameters)
    return pairs,report


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--width',nargs=2,required=True)
    ap.add_argument('--left-height',nargs=2,required=True)
    ap.add_argument('--right-height',nargs=2,required=True)
    ap.add_argument('--grid',nargs=2,type=int,default=[48,20])
    ap.add_argument('--exact-matching',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    spec=dict(width=args.width,left_height=args.left_height,right_height=args.right_height,grid=args.grid)
    pairs,report=discover(spec,exact_matching=args.exact_matching)
    data=dict(format='ambi-anchor-matching-v1',region={k:spec[k] for k in ('width','left_height','right_height')},
              parameters=DEFAULT_PARAMETERS,bins=[dict(width=args.width,grid=args.grid,pairs=pairs)])
    args.output.write_text(json.dumps(data,separators=(',',':'))+'\n')
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
