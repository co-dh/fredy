#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["networkx"]
# ///
"""Louvain community detection for the dependency-graph viewer's 'Communities' overview level.

k-means on the SVD embedding degenerates here (one mega-blob) because the codebase's dependency
structure is a smooth gradient, not separated clumps. Modularity-optimizing community detection
(Louvain) works: it finds Q=0.59 communities — thematic bundles of related sections that respect
chapter boundaries (91% chapter-pure). Those are the natural mid-level between the 4 chapters and
the 248 sections, so the viewer collapses to them for the overview.

Writes graph/communities.tsv (name \\t community_id). The community label is derived in the viewer
from each community's dominant section (the viewer already knows every node's file). Deterministic
(seed=0). Run after regenerating the graph:
  lake env lean --run scripts/ExtractGraph.lean; uv run scripts/community.py
"""
import csv
from collections import defaultdict
import networkx as nx
REPO_DECLS='graph/decls.tsv'; REPO_DEPS='graph/deps.tsv'; OUT='graph/communities.tsv'
RESOLUTION=1.0                    # higher => more, smaller communities (0.5→69, 1.0→82, 4.0→113)

idx={}; names=[]
for r in csv.reader(open(REPO_DECLS), delimiter='\t'):
    if len(r) < 4 or r[0] in idx: continue
    idx[r[0]] = len(names); names.append(r[0])
n=len(names)
w=defaultdict(int)
for r in csv.reader(open(REPO_DEPS), delimiter='\t'):
    if len(r) < 2: continue
    a,b = idx.get(r[0]), idx.get(r[1])
    if a is not None and b is not None and a != b:
        w[(min(a,b), max(a,b))] += 1     # symmetrize: a dependency is an undirected tie
G=nx.Graph(); G.add_nodes_from(range(n))
G.add_weighted_edges_from((u,v,c) for (u,v),c in w.items())

comms=nx.community.louvain_communities(G, weight='weight', resolution=RESOLUTION, seed=0)
comms=sorted(comms, key=len, reverse=True)          # id 0 = biggest, stable ordering
Q=nx.community.modularity(G, comms, weight='weight')
cid={}
for i,c in enumerate(comms):
    for node in c: cid[node]=i
with open(OUT,'w') as f:
    for i in range(n):
        f.write(f"{names[i]}\t{cid[i]}\n")
print(f"wrote {OUT}: {n} nodes in {len(comms)} communities (Louvain res={RESOLUTION}, Q={Q:.3f})")
