#!/usr/bin/env -S uv run --script
"""Group each declaration under the CONCEPT it belongs to, for the viewer's 'concepts' level.

Two mechanisms, both semantic (no statistics):
  1. Definitional: a decl folds into the longest dotted-prefix that is itself a declared name
     (Cat.id, Cat.comp, Cat.assoc -> the structure Cat). This bundles a structure with its fields.
  2. Subject: a standalone theorem folds into the concept it is most ABOUT = the concept among its
     dependencies maximising (#uses) * idf(concept). The idf (specificity) weight stops the ubiquitous
     hub Cat (composition/hom/id, used by everything) from swallowing every theorem — a theorem attaches
     to its most DISTINCTIVE subject instead.

9135 decls collapse to ~400 named concept nodes (Cat, Topos, Subobject, Allegory, PowerAllegory, …),
median size ~10. Theorems that reference no structure fall back to their book section (§x.y).
Writes graph/concepts.tsv (name \\t concept). Deterministic; stdlib only.
Run after regenerating the graph:  lake env lean --run scripts/ExtractGraph.lean; python3 scripts/concept.py
"""
import csv, math, re
from collections import Counter, defaultdict

names=[]; nameset=set(); file={}
for r in csv.reader(open('graph/decls.tsv'), delimiter='\t'):
    if len(r) < 4 or r[0] in nameset: continue
    names.append(r[0]); nameset.add(r[0]); file[r[0]] = r[2]
N=len(names)

def parent(name):                                  # longest proper dotted-prefix that is itself a decl
    parts=name.split('.')
    for i in range(len(parts)-1, 0, -1):
        p='.'.join(parts[:i])
        if p in nameset: return p
    return None
par={x:parent(x) for x in names}
def root(x):
    seen=set()
    while par[x] is not None and x not in seen: seen.add(x); x=par[x]
    return x
rt={x:root(x) for x in names}
members=defaultdict(list)
for x in names: members[rt[x]].append(x)
concepts={r for r,m in members.items() if len(m) >= 2}    # a root with pieces = a real concept
concepts.discard('Cat')   # Cat (composition/hom/id) is a ubiquitous hub — the 'the' of this graph;
                          # drop it as a subject so theorems attach to their DISTINCTIVE concept, not Cat

out=defaultdict(list); indeg=Counter()
for r in csv.reader(open('graph/deps.tsv'), delimiter='\t'):
    if len(r) < 2: continue
    a,b=r[0],r[1]
    if a in nameset and b in nameset: out[a].append(b); indeg[b]+=1
pop=Counter()                                       # concept popularity = total in-degree of its members
for c in concepts:
    for m in members[c]: pop[c]+=indeg[m]
idf={c: math.log(N/(1+pop[c])) for c in concepts}   # hubs (high pop) get low weight

def sectionOf(f):
    m=re.search(r'/S(\d+)_(\d)', f);  return f'§{m[1]}.{m[2]}' if m else None
    # (only used as a fallback label below)
def sect(f):
    m=re.search(r'/S(\d+)_(\d)', f)
    if m: return f'§{m[1]}.{m[2]}'
    m=re.search(r'/A(\d+)_', f);  return f'AoP {m[1]}' if m else f.split('/')[-1].replace('.lean','')

def concept_of(x):
    r=rt.get(x); return r if r in concepts else None
subj={}
for x in names:
    if rt[x] in concepts: subj[x]=rt[x]; continue
    score=defaultdict(float)
    for d in out[x]:
        c=concept_of(d)
        if c: score[c]+=idf[c]
    subj[x]= max(score, key=score.get) if score else sect(file[x])   # fallback: the book section

with open('graph/concepts.tsv','w') as f:
    for x in names:
        if x=='Cat' or x.startswith('Cat.'): continue     # Cat.* removed from the visualisation entirely
        f.write(f"{x}\t{subj[x]}\n")
ng=len({subj[x] for x in names if not (x=='Cat' or x.startswith('Cat.'))})
print(f"wrote graph/concepts.tsv: {N} decls -> {ng} concept groups (Cat.* excluded)")
