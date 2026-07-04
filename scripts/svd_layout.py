#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["numpy", "scipy"]
# ///
"""Precompute a deterministic SVD seed layout for the dependency-graph viewer (graph/viz/index.html).

Positions each declaration by (u2, u3) of the SVD of the hub-removed dependency matrix — the
allegory-vs-category and limits-vs-subobjects axes — so the in-browser ForceAtlas2 starts from a
structure-aware, REPRODUCIBLE arrangement instead of random noise. That makes the layout the same on
every load (ForceAtlas2 itself is deterministic; the only randomness was the old random init) and lets
it converge in fewer iterations. Writes graph/pos.tsv (name \\t x \\t y); the viewer falls back to
random when the file is absent.

Run after regenerating the graph:  lake env lean --run scripts/ExtractGraph.lean; uv run scripts/svd_layout.py
"""
import numpy as np, csv
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import svds

HUB_INDEG = 100; K = 8; SCALE = 1000.0
idx={}; names=[]
for r in csv.reader(open('graph/decls.tsv'), delimiter='\t'):
    if len(r) < 4 or r[0] in idx: continue
    idx[r[0]] = len(names); names.append(r[0])
n=len(names); rows=[]; cols=[]
for r in csv.reader(open('graph/deps.tsv'), delimiter='\t'):
    if len(r) < 2: continue
    a,b = idx.get(r[0]), idx.get(r[1])
    if a is not None and b is not None: rows.append(a); cols.append(b)
A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(n,n)).tocsr()
indeg = np.asarray(A.sum(0)).ravel()
Ah = (A @ diags((indeg <= HUB_INDEG).astype(float))).tocsr(); Ah.eliminate_zeros()

U,S,_ = svds(Ah.astype(float), k=K); o = np.argsort(-S)
u2, u3 = U[:, o[1]], U[:, o[2]]                       # the two topical contrast axes (skip u1 = core-usage gradient)
# rank-normalise each axis to a uniform spread: keeps the SVD *ordering* but drops the heavy tails
# (a few extreme u2/u3 values would otherwise fly off as far outliers and wreck the framing).
def rank_uniform(v): return (np.argsort(np.argsort(v)) / (len(v) - 1) - 0.5)
x = rank_uniform(u2) * SCALE
y = rank_uniform(u3) * SCALE
h = (np.arange(n) * 1103515245 + 12345) % 10007       # deterministic tiny jitter: break exact overlaps
x += (h / 10007 - 0.5) * 18
y += ((h * 7) % 10007 / 10007 - 0.5) * 18

with open('graph/pos.tsv', 'w') as f:
    for i in range(n):
        f.write(f"{names[i]}\t{x[i]:.2f}\t{y[i]:.2f}\n")
print(f"wrote graph/pos.tsv: {n} positions (SVD u2/u3 seed)")
