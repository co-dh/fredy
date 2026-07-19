#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["numpy", "scipy"]
# ///
"""Graph-based duplicate-lemma detector for the Freyd dependency graph.

Candidate generation: nearest neighbours in the SVD embedding of the hub-removed dependency matrix.
Each declaration's row (what it uses) is compressed to a K-D fingerprint; duplicates have near-identical
fingerprints. This catches duplicates that share only *mid-frequency* dependencies — a rare-dep inverted
index (the earlier approach) misses those, and SVD-NN found a strict superset of its results.

Then filter: cross-file (kills same-file symmetric siblings like left/right, Preserves/Reflects),
same kind, high row-Jaccard on the hub-removed rows; corroborate & rank by name and type agreement.

Hubs (deps used by > HUB_INDEG decls, e.g. Cat.Hom) are dropped everywhere: they're in almost every
row so they carry no duplicate signal.

Run:  uv run scripts/dep_dup.py     (regen data first: lake env lean --run scripts/ExtractGraph.lean)
"""
import numpy as np, csv, re, collections
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import svds

HUB_INDEG = 100    # dep used by more than this many decls = hub, dropped from every row
K         = 32     # SVD embedding dimension
COS       = 0.90   # nearest-neighbour cosine threshold for a candidate pair
MIN_SHARED= 3      # shared non-hub deps required (unless name/type corroborates)
MIN_J     = 0.80   # row-Jaccard (hub-removed) threshold
TOP       = 50     # how many ranked candidates to print
DECLS, DEPS = 'graph/decls.tsv', 'graph/deps.tsv'

# --- load ---
info={}; idx={}; names=[]
for r in csv.reader(open(DECLS), delimiter='\t'):
    if len(r) < 4 or r[0] in idx: continue
    idx[r[0]] = len(names); names.append(r[0])
    info[r[0]] = (r[1], r[2], r[3], r[4] if len(r) > 4 else '')     # kind, file, line, type
n=len(names); rows=[]; cols=[]
for r in csv.reader(open(DEPS), delimiter='\t'):
    if len(r) < 2: continue
    a,b = idx.get(r[0]), idx.get(r[1])
    if a is not None and b is not None: rows.append(a); cols.append(b)
A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(n,n)).tocsr()
indeg = np.asarray(A.sum(0)).ravel()                       # dep in-degree (also a decl's own in-degree)
keep  = (indeg <= HUB_INDEG).astype(float)
Ah    = (A @ diags(keep)).tocsr(); Ah.eliminate_zeros()    # hub columns zeroed
dout  = [set(Ah.indices[Ah.indptr[i]:Ah.indptr[i+1]]) for i in range(n)]

# --- SVD embedding + nearest-neighbour candidate generation ---
U,S,_ = svds(Ah.astype(float), k=K); E = U*S
nz = np.linalg.norm(E, axis=1); good = nz > 1e-9
En = E.copy(); En[good] /= nz[good][:,None]
cand=set(); gi=np.where(good)[0]
for s in range(0, len(gi), 1000):
    blk = gi[s:s+1000]; C = En[blk] @ En.T
    for r,i in enumerate(blk):
        for j in np.where(C[r] >= COS)[0]:
            if j > i and good[j]: cand.add((int(i), int(j)))

# --- name / type tokenisation ---
def toks(s):
    ts=[]
    for p in re.split(r'[^A-Za-z0-9]+', s):
        ts += re.findall(r'[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+', p)
    return set(t.lower() for t in ts if t)
def jac(a,b): return len(a&b)/len(a|b) if (a or b) else 0.0
def name_sim(a,b):
    tail=lambda x: toks('.'.join(x.split('.')[-2:])); return jac(tail(a), tail(b))

# --- score & filter ---
rows_out=[]
for a,b in cand:
    ia,ib = info[names[a]], info[names[b]]
    if ia[0] != ib[0] or ia[1] == ib[1]: continue         # same kind, cross-file
    da,db = dout[a], dout[b]
    if not da or not db: continue
    sh = len(da&db); j = jac(da,db)
    if j < MIN_J: continue
    ns = name_sim(names[a], names[b]); ts = jac(toks(ia[3]), toks(ib[3]))
    if sh < MIN_SHARED and not (ts >= 0.9 or ns >= 0.5): continue
    unused = indeg[a]==0 or indeg[b]==0
    score = 0.45*ns + 0.35*ts + 0.20*j
    rows_out.append((score, j, unused, ns, ts, sh, names[a], names[b], ia, ib))
rows_out.sort(key=lambda x:(x[0], x[2]), reverse=True)

# --- report ---
def verdict(k, ts):                                        # cheap real/verify guess
    if k=='thm' and ts>=0.999: return 'DUP  '              # same statement, proof-irrelevant
    if k=='thm' and ts>=0.85:  return 'likely'
    return 'verify'
print(f"hubs removed (in-degree > {HUB_INDEG}): {int((~(keep>0)).sum())}; SVD k={K}, cos>={COS}")
print(f"candidate pairs {len(cand)} -> {len(rows_out)} pass (cross-file, same-kind, Jaccard>={MIN_J})\n")

TESTS=[('Alg.recip_Sup','Alg.recip_Sup'+"'"),('Alg.AllegoryFunctor.mono','Alg.AllegoryFunctor.map_mono'),
       ('FibreDensityProof.fibrePinEqualizers','UniformCap.uniformPinEqualizers'),
       ('innerSliceCartesianNil','innerSliceCartesianNilLoc')]
rank={frozenset((r[6],r[7])):i for i,r in enumerate(rows_out)}
print("=== known duplicates (test) ===")
for a,b in TESTS:
    i=rank.get(frozenset((a,b)))
    print(f"  {'rank #%-3d'%(i+1) if i is not None else 'MISSED  '}  {a} ~ {b}")

print(f"\n=== top {min(TOP,len(rows_out))} candidates ===")
for i,(_,j,un,ns,ts,sh,a,b,ia,ib) in enumerate(rows_out[:TOP]):
    print(f"#{i+1:<3} {verdict(ia[0],ts)} name={ns:.2f} type={ts:.2f} J={j:.2f} sh={sh}{' U' if un else '  '} [{ia[0]}]")
    print(f"      {a} ({ia[1].split('/')[-1]}:{ia[2]})  ~  {b} ({ib[1].split('/')[-1]}:{ib[2]})")

hc=[r for r in rows_out if r[3]>=0.6 and r[4]>=0.9]
print(f"\nhigh-confidence (name>=0.6 & type>=0.9): {len(hc)} pairs")
