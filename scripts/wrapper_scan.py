"""One-line wrapper THEOREMS in Fredy/*.lean: body is a single short term-mode expression
delegating to exactly one other repo declaration. Excludes defs/abbrevs (naming a concept is
legitimate). Splits output: book-numbered statements (block mentions '§' — the deliverable,
keep) vs plain helpers (inline+delete candidates), sorted by call-site count."""
import re, glob
from collections import defaultdict

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([A-Za-z_][\w.\']*)')

files = sorted(f for d in ('Fredy', 'AOP', 'leet', 'rel')
               for f in glob.glob(d + '/**/*.lean', recursive=True))
blocks = []
for fp in files:
    lines = open(fp).read().splitlines()
    starts = [(i, m[1], m[2]) for i, l in enumerate(lines) if (m := DECL.match(l))]
    for j, (i, kind, name) in enumerate(starts):
        end = starts[j+1][0] if j+1 < len(starts) else len(lines)
        blocks.append((fp, i+1, kind, name, lines[i:end]))

nameset = {b[3] for b in blocks}
lastsegs = {n.split('.')[-1] for n in nameset}

def strip_comments(txt):
    txt = re.sub(r'/-.*?-/', ' ', txt, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', txt)

def toplevel_assign(txt):
    """index just past the first top-level `:=` (all brackets balanced), or None."""
    depth = 0; i = 0; pairs = {'(':1,')':-1,'[':1,']':-1,'{':1,'}':-1,'⟨':1,'⟩':-1}
    while i < len(txt)-1:
        c = txt[i]
        if c in pairs: depth += pairs[c]
        elif c == ':' and txt[i+1] == '=' and depth == 0: return i+2
        i += 1
    return None

IDENT = re.compile(r"[A-Za-z_][\w.']*")
KEYWORDS = {'fun','let','by','exact','if','then','else','match','with','rfl','trivial','And','Or',
            'Iff','Eq','fst','snd','mp','mpr','symm','trans','le','lt','val','property','intro',
            'obtain','have','show','from','this','of','left','right','elim','rec','mk','ext'}

cands = []
for fp, ln, kind, name, src in blocks:
    if kind not in ('theorem', 'lemma'): continue
    txt = strip_comments('\n'.join(src))
    p = toplevel_assign(txt)
    if p is None: continue
    body = txt[p:].strip()
    if not body: continue
    if '\n' in body:
        head, *rest = body.split('\n')
        if any(l.strip() for l in rest): continue
        body = head.strip()
    if len(body) > 110 or body == 'rfl': continue
    if body.startswith('by') and not body.startswith('by exact '): continue
    refs = set()
    for tok in IDENT.findall(body):
        seg = tok.split('.')[-1]
        if tok == name or seg == name.split('.')[-1] or seg in KEYWORDS: continue
        if tok in nameset or seg in lastsegs: refs.add(seg)
    if len(refs) != 1: continue
    isbook = '§' in '\n'.join(src)
    cands.append((fp, ln, name, body, refs.pop(), isbook))

alltext = [strip_comments(open(fp).read()) for fp in files]
owntext = defaultdict(str)
for fp, ln, kind, name, src in blocks:
    owntext[name.split('.')[-1]] += strip_comments('\n'.join(src))

rows = []
for fp, ln, name, body, ref, isbook in cands:
    seg = name.split('.')[-1]
    # NOT \b: primed names (cover_comp'') end in a non-word char, where \b never matches
    # before whitespace — that bug misreported every primed wrapper as uses=0.
    pat = re.compile(r"(?<![\w'])" + re.escape(seg) + r"(?![\w'])")
    uses = sum(len(pat.findall(t)) for t in alltext) - len(pat.findall(owntext[seg]))
    rows.append((uses, isbook, fp, ln, name, body, ref))
rows.sort(key=lambda r: (r[1], r[0]))

helpers = [r for r in rows if not r[1]]
book    = [r for r in rows if r[1]]
print(f"total {len(rows)}: {len(helpers)} plain helpers, {len(book)} book-numbered (§ in block)\n")
print(f"=== PLAIN HELPERS (inline+delete candidates) ===")
for uses, _, fp, ln, name, body, ref in helpers:
    print(f"uses={uses:3d}  {fp}:{ln}  {name}  ->  {body}")
print(f"\n=== BOOK-NUMBERED (statement is the deliverable — keep) === ({len(book)}, not listed)")
import collections
print("helper uses histogram:", dict(sorted(collections.Counter(r[0] for r in helpers).items())))
