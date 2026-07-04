#!/usr/bin/env python3
"""Graph-only duplicate detector for the Fredy dependency graph (Fable 5's stage-4 idea).

Targets the repo's known duplicate-generating process: parallel worktree agents re-deriving
the same helper in different files. Such a pair is CROSS-FILE, same kind, and has near-identical
*rare* dependencies (after deleting universal hubs like `Cat.Hom` that everything uses). The
cross-file requirement is what avoids the main false positive — same-file symmetric siblings
(`inter_subset_left/right`, `Preserves`/`Reflects`) whose rows are identical but are distinct.

Reads graph/decls.tsv + graph/deps.tsv (regen: lake env lean --run scripts/ExtractGraph.lean).
Pure stdlib, runs in seconds. Not a rewrite tool — it surfaces ranked candidates to inspect.
"""
import csv, sys, re, collections
from itertools import combinations

HUB_INDEG   = 100   # a dep used by more than this many decls is a "hub": drop it from similarity
CAND_INDEG  = 40    # only pairs that share a dep this rare become candidates (discriminative)
GROUP_CAP   = 80    # skip a shared dep used by more than this (would blow up the pair count)
MIN_SHARED  = 3     # need at least this many shared non-hub deps (avoid 1-dep coincidences)
MIN_JACCARD = 0.80  # out-neighbour Jaccard (hub-removed) threshold

DECLS, DEPS = 'graph/decls.tsv', 'graph/deps.tsv'

# --- load ---
info = {}   # name -> (kind, file, line, type)
for r in csv.reader(open(DECLS), delimiter='\t'):
    if len(r) < 4: continue
    info[r[0]] = (r[1], r[2], int(r[3]), r[4] if len(r) > 4 else '')

out    = collections.defaultdict(set)   # name -> deps it uses
indeg  = collections.Counter()          # dep -> how many decls use it (also = a decl's in-degree)
for r in csv.reader(open(DEPS), delimiter='\t'):
    if len(r) < 2: continue
    out[r[0]].add(r[1]); indeg[r[1]] += 1

hubs = {d for d, c in indeg.items() if c > HUB_INDEG}
dout = {n: (s - hubs) for n, s in out.items()}   # hub-removed out-sets

# --- name / type tokenisation for secondary ranking ---
def toks(s):
    parts = re.split(r'[^A-Za-z0-9]+', s)
    ts = []
    for p in parts:
        ts += re.findall(r'[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+', p)   # split camelCase
    return set(t.lower() for t in ts if t)

def jac(a, b):
    return len(a & b) / len(a | b) if (a or b) else 0.0

def name_sim(a, b):
    # compare the last two dotted components (enclosing namespace tail + lemma name), which
    # captures both `AllegoryFunctor.mono` vs `AllegoryFunctor.map_mono` and bare renames.
    tail = lambda n: toks('.'.join(n.split('.')[-2:]))
    return jac(tail(a), tail(b))

# --- candidate generation: co-occurrence in a rare dep's user list ---
inv = collections.defaultdict(list)
for n, s in dout.items():
    for d in s:
        if indeg[d] <= CAND_INDEG:
            inv[d].append(n)

cand = set()
for d, lst in inv.items():
    if 2 <= len(lst) <= GROUP_CAP:
        for a, b in combinations(sorted(lst), 2):
            cand.add((a, b))

# --- score candidates ---
rows = []
for a, b in cand:
    ia, ib = info.get(a), info.get(b)
    if not ia or not ib: continue
    if ia[0] != ib[0]:          continue      # same kind only (a def dup is a def, etc.)
    if ia[1] == ib[1]:          continue      # CROSS-FILE only (kills same-file siblings)
    da, db = dout[a], dout[b]
    shared = len(da & db)
    if not da or not db:        continue
    j = jac(da, db)
    if j < MIN_JACCARD:         continue
    nsim = name_sim(a, b)
    tsim = jac(toks(ia[3]), toks(ib[3]))                          # type-token overlap
    # a 1–2 shared-dep match is a coincidence UNLESS the name or type corroborates it
    if shared < MIN_SHARED and not (tsim >= 0.9 or nsim >= 0.5): continue
    unused = (indeg[a] == 0) or (indeg[b] == 0)                    # one copy never used
    # rank so accidental renames (high name+type agreement) float above the case-study anchors
    # (same abstract theorem restated per case study: J=type=1 but low name similarity)
    score = 0.45*nsim + 0.35*tsim + 0.20*j
    rows.append((score, j, unused, nsim, tsim, shared, a, b, ia, ib))

rows.sort(key=lambda x: (x[0], x[2]), reverse=True)

# --- report ---
print(f"hubs removed (in-degree > {HUB_INDEG}): {len(hubs)} deps; "
      f"top: {', '.join(d for d,_ in indeg.most_common(5))}")
print(f"candidate pairs: {len(cand)} -> {len(rows)} pass "
      f"(cross-file, same-kind, ≥{MIN_SHARED} shared non-hub deps, Jaccard ≥ {MIN_JACCARD})\n")

TESTS = [('Alg.AllegoryFunctor.mono','Alg.AllegoryFunctor.map_mono'),
         ('FibreDensityProof.fibrePinEqualizers','UniformCap.uniformPinEqualizers'),
         ('innerSliceCartesianNil','innerSliceCartesianNilLoc')]
rank_of = {frozenset((r[6], r[7])): i for i, r in enumerate(rows)}
print("=== known duplicates (test of the method) ===")
for a, b in TESTS:
    i = rank_of.get(frozenset((a, b)))
    if i is None:
        print(f"  MISSED  {a}  ~  {b}")
    else:
        _, j, un, ns, ts, sh, *_ = rows[i]
        print(f"  rank #{i+1:<3} J={j:.2f} name={ns:.2f} type={ts:.2f} shared={sh} unused={un}  {a}  ~  {b}")

print(f"\n=== top {min(30,len(rows))} candidates ===")
for i, (_, j, un, ns, ts, sh, a, b, ia, ib) in enumerate(rows[:30]):
    flag = ' UNUSED' if un else ''
    print(f"#{i+1:<3} name={ns:.2f} type={ts:.2f} J={j:.2f} shared={sh}{flag}  [{ia[0]}]")
    print(f"       {a}   ({ia[1].split('/')[-1]}:{ia[2]})")
    print(f"       {b}   ({ib[1].split('/')[-1]}:{ib[2]})")

hc = [r for r in rows if r[3] >= 0.6 and r[4] >= 0.9]   # high name & type agreement = likely real dup
print(f"\n=== high-confidence (name>=0.6 & type>=0.9): {len(hc)} pairs ===")
for _, j, un, ns, ts, sh, a, b, ia, ib in hc:
    print(f"  [{ia[0]}]{' UNUSED' if un else ''}  {a} ({ia[1].split('/')[-1]}:{ia[2]})  ~  {b} ({ib[1].split('/')[-1]}:{ib[2]})")
