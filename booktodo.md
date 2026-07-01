# booktodo.md — bugs in the Typst book transcription (vs the original scan)

Source of truth: `/home/dh/anki/categories-allegories.pdf` (the original Freyd scan), read VISUALLY
(the Read tool renders PDF pages as images). The `.typ` files under
`/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.typ` are an OCR-derived transcription and
have errors. Below are bugs found 2026-06-30 while verifying the §2.41 power-allegory definition.
Each lists: file:line — what the `.typ` has now → what the scan shows (book page / PDF page).

## FIX PLAN (2026-06-30 full-book review — read this before editing any fix_ocr)

**Scope of this pass:** all 15 sections reviewed (§1.1–1.10, §2.1–2.5) by one agent per section comparing
`.typ` against the scan, then independently gated by re-checking every SEMANTIC finding myself (grep for
self-contradiction within the `.typ`, or a PDF re-read/zoom when no internal tell existed) before recording it
here — see "Verification-tier note" below the §1.7 entries for what CONFIRMED/PLAUSIBLE mean. **Coverage
caveat: this catches false positives well; it does NOT prove completeness. Absence of an entry means
"unaudited," not "clean," except where a section says otherwise.** §1.1/§1.10 audit still pending a redispatch
(original agent's transcript was lost); will be appended when it lands.

**Fix this BEFORE anything else — 3 regressions where a prior fix_ocr made the `.typ` WRONG, so the current
text looks deliberate/reviewed but isn't:**
1. `fix_ocr_1.4.py` line ~68 (`SCRIPT_SUBS`): `chapters/1.4/section-1.4.typ:77` — its own `Val(Y)` rewrite is
   backwards; revert to `\mathcal{H}(Y)` on this ONE site only (the script correctly leaves the *other* `ℋ(Y)`
   sites alone — don't touch those).
2. `fix_ocr_1.8.py`'s `ARROW_SUBS` — `chapters/1.8/section-1.8.typ:77` collapses a 3-object adjoint diagram
   into 2 objects, leaving "adjoint on the right" and "adjoint on the left" with the literal identical defining
   clause (provably wrong on its face). Also `SPL_SUBS` in the same file (line 226) — wrong spelling *and* wrong
   font (`\mathbf{Spl}` should be `\mathit{Split}`, per §1.2's dozens of correct uses of the full word).
3. `fix_ocr_1.9.py`'s `_DROPPED_ARROW` regex — inserts `\to` unconditionally into every dropped-space gap; at
   `chapters/1.9/section-1.9.typ:140,144` the book actually has `\leftrightarrow` (the §1.914 Heyting
   double-arrow operation), and the substituted `\to` produces an ill-typed formula (intersecting a subobject
   with a morphism). **Audit every hit of this regex in §1.9** before trusting the rest of that file's arrows.

**Then fix by CLASS, not by line — the ~150 findings collapse to about 10 systemic patterns. One
`fix_ocr_<sec>.py` substitution table per class per section, on the `fix_ocr_1.3.py` `INFLATION_C` precedent
(exact-string subs, scoped, never a blanket regex across a whole file):**

| # | Class | Where found | Fix approach |
|---|-------|-------------|--------------|
| 1 | `∃`(exists)/`∋`(membership) confusion, and `∀`/`A` in §1.3's Q-tree material | §1.3, §1.9, §2.4 (both directions — see §2.4's caution below) | Exact-string subs. **Never blanket `\exists`→`\ni`** — §2.4 line 334 and §1.9 line 191 have genuine correct `\exists`/`\exists!`; the tell is a bound variable (`\exists_A`) vs bare backward-E. |
| 2 | Calligraphic/script-word letter confusion (the broadest class: single-letter `C`/`G`/`O`/`E`/`I` swaps, and multi-letter cursive words `Sub`/`Rel`/`Dom`/`Map`/`Split`/`Cor`/`Sh`/`Ab`/`Val`/`Ker`/`Cok`/`Sid` each mis-OCR'd differently almost every occurrence) | Nearly every section — §1.2 (class-of-objects), §1.3 (𝒪(Y), Γ_*), §1.5 (Sh/Ab/C-as-E), §1.6 (S/I, LH/M), §1.9 (Sub variants), §2.1/§2.2/§2.3 (Dom/Map/Split/Cor — **zero prior fix_ocr coverage, highest raw count**), §2.5 (Dom, S/I) | Per-section substitution table, one entry per garbled spelling → canonical word. **Never a project-wide regex** — the same raw glyph/string means different things in different sections (documented case: `\mathcal{O}(Y)` is genuinely the open-set lattice in §1.373+ but a mis-OCR of inflation-class 𝒞 in §1.36 — CLAUDE.md already flags this). Scope every sub to the section + context it was verified in. |
| 3 | Γ (capital Gamma, functor names) misread as `T`/`I`/`r`/`{\cal T}` | §1.3 (sheafification Γ_*), §1.5 (Henkin-Lubkin `T_B`'s own Γ factor), §1.7 (scone functor, §1.72(10)–1.734) | Same shape as class 2 but flagged separately since it recurred independently in 3 different sections — likely worth a shared checklist/heuristic ("any bare `T`/`{\cal T}` near a functor-representation sentence — check the scan") rather than assuming it's fully caught once. |
| 4 | Box operator □ family misread as `∏`, `⊐`(target confused with source), `⋆`/`\bigstar`, or residual `\boxed{}` | §1.3 (⊏/⊐ position swap), §2.1 (`∏x=x□`), §2.2 (`\bigstar R=\bigstar S`) | Exact-string subs; cross-check the source/target (prefix/postfix) position isn't flipped, not just the glyph family. |
| 5 | Dropped negation slash: `⊂`→`⊄`, `∈`→`∉`(or vice versa) | §1.5 (⊄→∉), §1.6 (⊂→⊄, flips a biconditional — **still needs a confirming zoom, see §1.6 finding 1**), §1.9 (∉ dropped) | Case-by-case — a negation slash is a single stroke, easy to lose in OCR, and flips meaning to near-opposite every time. Highest scrutiny per instance of any class here. |
| 6 | `f^\#`/`f^{\#\#}` (sharp) misread as `f^*`/`f^{**}` (asterisk) | §1.7 (CONFIRMED wrong — zoomed) | **Not a blanket fix.** §1.6 lines 41/45/145 legitimately mix `#` and `*` as two distinct notations in one sentence (checked at zoom, matches book p.63's genuine dual usage) — every instance needs its own scan check, this pair is genuinely ambiguous at normal render resolution. |
| 7 | τ (Greek tau, the τ-category apparatus) misread as digit "7" or letter "T" | §1.4 (§1.49–1.4(12), ~14 pages, CONFIRMED via zoom) | Section-scoped regex is safe here (unlike class 2) since τ-category is §1.4-only vocabulary — sweep `\b7-` and `\bT-(table|categor|functor|structure)` in that one file. |
| 8 | Accent scatter: one symbol rendered with `\bar`/`\breve`/`\vec`/`\hat` inconsistently | §1.7 (R̄, CONFIRMED — 4 different accents for one symbol in one proof), §2.5 (prime read as comma, related failure) | Pick the majority/first-established accent in each thread, substitute the outliers. |
| 9 | Dropped/wrong delimiters: `[X]` vs `{X}`, missing `⟨⟩`, missing `\|X\|` bars | §1.3 (`[T]`/`{T}`), §1.9 (`[B]`/`{B}`), §1.5 (missing `\|A\|`, `⟨⟩`) | Exact-string subs; usually has a same-sentence corroborating tell. |
| 10 | Dropped arrows (`X  Y` double-space, no `\to`) and citation en-dashes (`[a-b]`→`[ab]`) | Nearly every section | Lowest severity (self-evident once you look, `fix_ocr`'s existing `_DROPPED_ARROW`-style regexes catch most) — EXCEPT where the dropped connective isn't `\to` (see regression #3 above) or where it's `\leftrightarrow`/`\rightleftharpoons`. |

**Regeneration order once any `fix_ocr_<sec>.py` is edited** (per existing CLAUDE.md convention): run that
section's `fix_ocr` → `mineru_to_typst` → `typst compile` (or `regen_all.py` for everything), THEN
`combine_book.py` and `searchable_pdf.py all`. Chapters 2.1–2.5 have **no `fix_ocr_2.x.py` files yet** — one
needs to be created per section (there is no existing file to extend), following `fix_ocr_1.3.py`'s
`INFLATION_C` block as the template for scoped, auditable, exact-string subs.

**Suggested order of work**: (1) the 3 regressions above — small, isolated, high-confidence; (2) §2.1/§2.2/§2.3
class-2 wordmark tables — zero prior coverage, high raw bug count, and creates the missing `fix_ocr_2.x.py`
files the rest of Ch.2 will need anyway; (3) the `∃`/`∋` sweep in §1.3/§1.9/§2.4-remainder, given it's the
class that started this whole review and both directions of confusion are now documented; (4) everything else,
lowest-regret first (self-evident/GARBLE tier) before the lower-confidence PLAUSIBLE entries.

## §2.4 — `chapters/2.4/section-2.4.typ`  (scan: book p.235–236 = PDF p.254–255)

1. **SEMANTIC — §2.41 axiom 2, line 55.** `.typ`: `\exists _ { R } = \ \ni _ { R \square }`
   → should be `\ni _ { R } = \ \ni _ { R \square }`  (the equation is `∋_R = ∋_{R□}`, NOT `∃_R = …`).
   The LHS symbol is `∋` (epsiloff/membership), the SAME symbol as everywhere else on the line, and
   the prose immediately after the first-attempt block paraphrases it as "∋_R depends only on the
   target of R" — which is precisely `∋_R = ∋_{R□}`. The bogus `\exists` (∃) is what makes it look
   like a box-INDEXED family vs the membership; it misled a formalization analysis. SAME bug at
   **line 79 (§2.413)**: `\exists _ { R } = \ \ni _ { R \square }` → `\ni _ { R } = …`.
   (The cleaned-OCR sibling `section-2.4.fixed.md` line 6 has a related garble `\ni _ { R \odot }`
   — `\odot` should be `\square`.)

2. **§2.412 transpose definition, line 67.** `.typ`:
   `Given any R, define #mi("\mathbf { \nabla } _ { \lambda ( R ) } \textbf { \^ { n } } \frac { R } { \ni }")`
   → scan: "Given any R, define **`Λ(R)` as `R/∋`**", i.e. `\Lambda ( R ) \triangleq \frac { R } { \ni }`.
   The `\mathbf{\nabla}_{\lambda(R)} \textbf{\^{n}}` is pure OCR garbage for `Λ(R) ≜`.

3. **§2.412 chain, line 71.** `.typ`: `\boldsymbol { \varLambda } ( R ) \ni \mathsf { \textsf { C } } ( R / \ni ) \ni \mathsf { \textsf { C } } R`
   → scan: `Λ(R) ∋ ⊂ (R/∋) ∋ ⊂ R`. The `\mathsf{\textsf{C}}` is OCR for `⊂` (`\subset`). Same `C`-for-`⊂`
   garble at **line 79**: `f \ni C R` → `f \ni \subset R` (`f∋ ⊂ R`).

4. **§2.412 chain, line 73.** `.typ` has `( 1 \cap ( R / \ni \mathcal {bigr ) }` and `( R / \ni / )`
   → garbled; the scan line is `R ⊂ (Dom Λ(R))R ⊂ (1 ∩ (R/∋)(∋/R))R ⊂ ((∋/R)° ∩ (R/∋))(∋/R)R ⊂ Λ(R)∋`.
   (`\mathcal {bigr )}` and the stray `/` are OCR noise.)

5. **§2.412 conclusion, line 75 / 77.** `.typ`: `A ( R ) \ni \mathbf { \phi } = R`
   → scan: `Λ(R) ∋ = R` (no `φ`). The `\mathbf{\phi}` is spurious.

6. **§2.357-restatement, line 48.** `.typ`: `{ \frac { R } { 1 } } \left( \square \exists \atop \exists { \cal R } \right) \subset …`
   → scan (p.235): `(R/1)(□ ∋_R) ⊂ Λ((R/1) ∋_R)`. The `\square \exists \atop \exists {\cal R}` should be
   `\square \ni _ { R }` (`□ ∋_R`).

## Verified CORRECT (no bug) — for the record

- §2.41 axiom 1 (`∋_R□ = R□`) and axioms 3–4 (thick / straight): correct in the `.typ`.
- §2.431 (scan p.240): "T is thick iff **for all R such that `R□ = T□`** there exists R̂ …" — the
  box-MATCHED thickness; the `.typ`/repo `Thick` is faithful to this (NOT a bug, NOT a deviation).

NOTE: only the §2.4 region was audited (during the §2.41 power-allegory check). Other chapters likely
have similar OCR-garbled formulas; audit against the scan before trusting any `.typ` formula.

## Full-book review, 2026-06-30 — methodology

Dispatched one review agent per section (13 total) to compare `.typ` against the scan, then
INDEPENDENTLY RE-VERIFIED every SEMANTIC finding below myself (re-read the exact `.typ` line +
the scan page, sometimes at 400 DPI zoom when a glyph was ambiguous at normal resolution — see
§1.7 finding 1, where my own first-resolution read was WRONG and only the zoom caught the truth).
Only findings that survived this gate are recorded. GARBLE findings (self-evidently broken/noisy,
lower stakes) got a lighter check. Entries below are appended per-section as verification completes.

## §1.2 — `chapters/1.2/section-1.2.typ`  (scan: PDF p.26–35, book p.7–16)

All CONFIRMED against direct re-read of `.typ` + scan.

1. **SEMANTIC — curly braces instead of square brackets, line 43.** `.typ`: `\{ x y = z \}`
   → should be `[ x y = z ]` (book p.7). `[xy=z]` is the ternary composition predicate defined two
   lines earlier ("a ternary predicate denoted [xy=z]") and used correctly elsewhere in this file
   (e.g. line 35, 65, 83) — this one instance alone got curly braces.

2. **SEMANTIC — the existence-of-composition axiom's connecting text is missing, lines 49–57.**
   Book p.7: "For all A -x→ B and B -y→ C **there exists z such that** A -z→ C." (one sentence, one
   triangle diagram). `.typ` currently renders two bare disconnected formula fragments
   (`#mitex("A \xrightarrow{x} B")`, `#mitex("B \stackrel{y}{\to} C")`) with NO surrounding prose —
   the existential quantifier ("there exists z such that") is entirely absent. This is axiom 3 of
   the book's foundational category axioms; currently unstated in any readable form.

3. **SEMANTIC — "U" should be "v", line 59.** `.typ`: `"For all x, y, z, s, t, u, U, A, B, C, D"`
   → should be `"...u, v, A, B, C, D"` (book p.8). Self-confirming: the `.typ`'s own conclusion four
   lines later ("imply t = v", line 63) already uses lowercase v — so v must be in the quantifier
   list, not a second uppercase U (which would also violate this section's own stated convention
   that upper case = objects, lower case = proto-morphisms).

4. **SEMANTIC — "class of objects" script letter wrong, 3 occurrences (NEW instance of the
   documented C/G/O/E confusion, outside the §1.36–1.363 thread `fix_ocr_1.3.py` already fixes).**
   Lines 109–110 (§1.243): `.typ` has `\mathcal{G}` then, two clauses later, `\mathcal{E}` (with a
   dropped arrow) — book p.9 uses the SAME calligraphic letter 𝒞 both times ("a new class of
   objects 𝒞... a function 𝒞 → |B|"). Line 123 (§1.245): `.typ` has `\mathcal{G}` again for
   "given a class 𝒞" — book p.10 confirms 𝒞. This is the identical calligraphic-C/G/O/E OCR
   confusion CLAUDE.md documents for §1.36, recurring independently in this earlier section.

5. **SEMANTIC — "J" should be "f", 3 occurrences.** Line 120 (§1.244, book p.10): `A \stackrel{J}{\to} B`
   → `A \stackrel{f}{\to} B`. Line 167 (§1.262, book p.12): the arrow in
   `U \to X \overset{J}{\to} Y = U \overset{\theta}{\to} V \to Y` → should be labeled `f` (the
   local homeomorphism named at the very start of §1.262: "f: X → Y"). Line 174 (§1.27, book p.13):
   "for every A -J→ B in A it is the case that..." (naturality condition) → should be `f`, matching
   the diagram's own `Ff`/`Gf` labels two lines later.

6. **SEMANTIC — "E/Y" should be "ℒℋ/Y", line 167 (§1.262, book p.12).** `.typ` has bare unstyled
   text `"E/Y is the category of LAZARD SHEAVES over Y, denoted ℒℋ(Y)"` — the SUBJECT collapsed to
   a plain "E", while the section is explicitly about the category ℒℋ ("Let ℒℋ be the category...",
   opening sentence of §1.262) and the slice notation `ℒℋ/Y` matches this file's own established
   pattern (e.g. `𝒮/B` at line 162). The second symbol (`denoted ℒℋ(Y)`) is already correct and used
   consistently 3 times in the same paragraph — only the bare "E/Y" subject is wrong.

7. **SEMANTIC — missing slash, line 162 (§1.261, book p.12).** `.typ`: `\mathcal{S} B`
   → should be `\mathcal{S}/B` (slice category; book: "the objects of 𝒮/B as B-indexed families...").
   Self-confirming: the very same sentence's next clause, `\mathcal{S}/B`, already has the slash.

8. **SEMANTIC — dropped trailing symbol, line 245 (§1.283, book p.16).** `.typ` ends: "(Do not
   adjoin 1 to .)" — should be "(Do not adjoin 1 to ℰ.)" (book confirms trailing ℰ). ℰ is the
   established "class of idempotents" symbol used throughout §1.28–1.284 (e.g. line 223).

GARBLE (lower stakes, lighter-touch check — self-evident from `.typ` text alone): dropped arrows
(double-space, no `\to`) at lines 110, 218; en-dash dropped from citation ranges e.g. `[1.2–1.22]`
→ `\[1.21.22\]` (lines 89, 123) and `[1.381–1.383]` → `\[1.3811.383\]` (line 107) — cosmetic,
concatenates two section numbers into a non-existent one but doesn't change any formula's meaning.

Not promoted to confirmed bug (agent-flagged uncertain, needs a physical-book-quality check):
possible dropped arrow LABEL at line 100 (§1.241, the "∅→A" example — may originally be named);
the `\bar{y}'` at line 232 (§1.282) the existing `fix_ocr_1.2.py` comment already flags as a guess.

## §1.7 — `chapters/1.7/section-1.7.typ`  (scan: PDF p.136–156, book p.117–137)

fix_ocr_1.7.py has no rule for either bug below — both are pervasive, systemic, and CONFIRMED
(including one zoom-level check that overturned my own first-resolution misreading — see finding 1).

1. **SEMANTIC — f^# (sharp, inverse-image) misread as f^* (asterisk), pervasive across the whole
   section.** Line 33 — the section's OPENING AXIOM, the definition of LOGOS itself: `.typ`:
   `f ^ { * } ( B ^ { \prime } ) \subset A ^ { \prime } \quad iff \quad B ^ { \prime } \subset
   f ^ { * \# } ( A ^ { \prime } )` → should be `f^{\#}(B') ⊂ A' iff B' ⊂ f^{\#\#}(A')`. CONFIRMED
   at 400 DPI zoom (book p.117): the glyph is unambiguously `#` (sharp), not `*` — my own first
   read at normal page-render resolution misread it as asterisk too, exactly the correlated-error
   risk of reading a scan at insufficient zoom; only the crop resolved it. MinerU's own raw OCR
   independently shows a tell: `f^{*\#}` (a literal hybrid of both glyphs) for the second occurrence
   — evidence MinerU itself struggled with this glyph, not a clean one-way misread. Same pattern
   recurs (agent-verified against scan, not independently re-zoomed by me) at lines 45, 191, 197,
   382, 408, 466, 505, 535 — all `f^{*}`/`f^{**}` should be `f^{\#}`/`f^{\#\#}`. Contrast: §1.782–784
   (lines 525–533) already render `f^{\#}` correctly, confirming this is per-crop OCR noise, not a
   different book notation — each site needs checking individually, not a blanket substitution.

2. **SEMANTIC — Γ (capital Gamma, the "scone"/stalk functor) misread as T, I, or r, recurring
   across §1.72(10)–§1.734.** CONFIRMED against book pp.122–124 (PDF 141–143), 4 separate instances
   directly re-checked: line 199 (`\cal{T} = (1,\_)` → `\Gamma = (1,\_)`, book p.122: "the functor
   Γ=(1,_)"), line 211 (`\cal{T}\colon\hat{A}\to\mathcal{S}` → `\Gamma\colon...`, book p.123: "the
   functor Γ: Â → 𝒮"), line 215 ("I is a representation" → "Γ is a representation", book p.123),
   line 238 (`\cal{T}=(1,\_)` again → `\Gamma=(1,\_)`, book p.124), line 242 ("I is a representation"
   → "Γ is a representation", book p.124: "If 1 is projective, Γ is a representation..."). NOT part
   of this bug (agent correctly excluded, I confirmed): line 223's `T_{\mathcal{F}}` is a genuinely
   different, correctly-named functor (T, not Γ) — only its subscript needs `\mathcal{F}` not
   `\mathcal{I}`. Bonus confirm while reading the same pages: line 233's spurious
   `(A\times\mathbf{\mu}_{-})` should be plain `(A\times(\_))` — book p.124 shows no μ (μ belongs to
   the unrelated `Â/μ≃A` scone-quotient two paragraphs earlier).

3. **SEMANTIC — named operator R̄ (§1.787) rendered with three different wrong accents.** CONFIRMED
   against book p.137 (PDF 156) — the scan uses uniform R̄ (bar) throughout the entire paragraph (6
   occurrences: "RR̄⊂R̄", "R̄/R̄" ×2, "R(R̄/R̄)R̄⊂RR̄⊂R̄", "R̄⊂R̄/R̄", "R̄R̄⊂R̄"), zero variation. `.typ` line
   540: `R \bar{R} \subset \breve{R}` (bar then breve — should be bar/bar). Line 546: `\vec{R}/\bar{R}`
   (should be bar/bar) and `R(\hat{R}/\hat{R})\hat{R}\subset R\hat{R}\subset\hat{R}` (all four `\hat`
   should be `\bar`) — `.typ` scatters `\bar`/`\breve`/`\vec`/`\hat` for what the book renders as one
   consistent symbol; a grep for `\bar{R}` alone would miss 5 of the 9 occurrences in this proof.

Reported by the agent, PLAUSIBLE but not independently re-zoomed by me (lower stakes / prose-adjacent,
accepted on the agent's self-reported scan check given its strong track record on findings 1–3 above):
script 𝒟 (a topology/binary-tree space, §1.749/1.74(10)) misread as 𝒬/∅/etc. at lines 366/368/370;
arrow label ψ misread as `*` at line 327 (§1.744 BECAUSE); `\mathcal{I}` for `\mathcal{S}` at line 521.

GARBLE (lower stakes): `\mathcal{I}`-for-`\mathcal{S}`/dropped-arrow noise generally throughout;
none individually itemized further per the lighter-touch policy for this tier.

## Verification-tier note (applies to all entries below)

Recalibrated mid-review (advisor input): re-deriving every finding from a fresh PDF zoom doesn't scale and
mostly re-proves what the `.typ` already proves about itself. From here, **CONFIRMED** = independently
re-checked against the scan (zoom when the glyph pair is genuinely close, e.g. `f^#`/`f^*`, `R°°`/`R^∞`).
**CONFIRMED (self-evident)** = the `.typ` contradicts itself — the same symbol/formula appears correctly
elsewhere in the same line/sentence/paragraph, checked directly by grep/read, no PDF needed (this is at least
as strong as a scan check: it's the SAME failure mode that caught the original `∋`/`∃` bug, just spotted via
text instead of image). **PLAUSIBLE** = agent-reported with a stated scan check I did not personally re-derive
(lower stakes, or corroborating evidence was strong enough not to warrant re-spending a PDF read). Coverage
caveat: this whole pass is good at rejecting false positives, not at finding every bug — treat the absence of
an entry as "not yet audited," never as "confirmed clean," except where a section explicitly says otherwise.

## §1.3 — `chapters/1.3/section-1.3.typ`  (scan: PDF p.36–55, book p.17–36)

INFLATION_C fix (§1.36–1.363) re-verified CONFIRMED solid — but the same bug class recurs, unfixed, against
other letters throughout the rest of the section (findings 2–3 below).

1. **SEMANTIC (CONFIRMED, self-evident) — ∃ misread as digit "3", ∀ misread as letter "A", throughout the
   Q-sequence/Q-tree formalism (§1.395–1.3(10)6).** In prose (outside `#mi()`): `∃→3` at lines 338, 390, 429,
   431, 433, 459, 467, 471; `∀→A` at lines 354, 429. E.g. line 338: "where each Q_i is either ∀ of **3**"
   should be "∀ or **∃**". The `∀→A` case is the more dangerous one — "A" is the ambient category name on
   every page, so "label the root A" reads as intentional, not corrupted. Same bug class as the motivating
   §2.41 `∋`/`∃` swap.

2. **SEMANTIC (CONFIRMED, self-evident) — 𝒪(Y) (open-set lattice, §1.373–1.375) misread as `\mathcal{G}`,
   `\mathcal{Q}`, `\mathcal{C}`.** Line 186 alone self-contradicts: "let `\mathcal{G}(Y)` be the lattice of
   open subsets of Y. We regard `\mathcal{O}(Y)` as a category: the maps of `\mathcal{G}(Y)`..." — the SAME
   referent named twice as 𝒢(Y) and once, correctly, as 𝒪(Y), in one sentence. Also wrong at lines 190, 200,
   220, 228, 230, 232 (`\mathcal{G}`, 11 occurrences total) and lines 216, 230 (`\mathcal{C}`, 2 occurrences).
   **CAUTION (preserve): this is the identical INFLATION_C bug class recurring against a different letter — do
   not blanket-replace `\mathcal{G}`→`\mathcal{O}` project-wide; scope any fix to this §1.373–1.375 thread,
   the same way `fix_ocr_1.3.py`'s `INFLATION_C` list is scoped to exact strings, not a regex.**

3. **SEMANTIC (CONFIRMED, self-evident) — Γ_* (the sheafification functor, §1.373–1.374) misread as `r_*`,
   `T_*`, `{\cal T}_*`.** Line 190 uses `\Gamma_*` correctly twice; line 192, two lines later, uses `T_* g` /
   `{\cal T}_* h` for the identical functor just named — direct nearby self-contradiction. Also wrong at line
   216 (`T_*` ×2, "S is a LEFT ADJOINT of T_*" — T_* is undefined here and collides with the unrelated generic
   functor name T used pervasively in §1.36) and line 226 (`{\cal T}_* Z`). Correct at lines 194, 196, 220, 224.

4. **SEMANTIC (CONFIRMED, self-evident) — □ (source, prefix) / ⊐ (target, postfix) confused or dropped,
   multiple sites.** Line 149: `C \bar{\bigcup} = \{c\square|c\in C\}\mathcal{K}` should be `C\sqsupset =
   \{c\sqsupset|c\in C\}\mathcal{K}` — symmetric with the immediately preceding correctly-transcribed
   `\square C = \mathcal{K}\{\square c|c\in C\}`, so the target-side pair should mirror it, not reuse `\square`.
   Line 200: `y\in\sqsupset z` should be `y\in\square z` — the identical quantity is correctly `\square z`
   three more times later in the same sentence. Lines 222, 224: `\square` missing its argument `F` entirely
   ("Define `\square` as..." should be "Define `\square F` as...", domain `\square` should be domain `\square F`).
   Line 265: `x\in\sqsupset f` should be `x\in\square f`. Line 321: `\boxed{\mathbf{\nabla}}{x_i}` (a drawn box
   around a stylized nabla) should be plain `\square x_i`.

5. **SEMANTIC (CONFIRMED, self-evident) — line 74, §1.341 closing sentence is a syntactic tautology.** `.typ`:
   `Then F' = F'` — literally identical symbol both sides, which cannot be a theorem's actual conclusion (the
   sentence's own setup, "F is conjugate to an isomorphism... isomorphism `FA\to FA'` via `\theta_A`", implies
   the real content is `F' = F^\theta` — F′ equals the θ-conjugate of F).

6. **SEMANTIC (CONFIRMED, self-evident) — `[T]` (the inflation category defined earlier in §1.36) misread as
   `{T}` (curly braces), lines 82, 84.** Line 82 alone shows the pattern breaking mid-paragraph: "...functor
   `\mathbf{B}\to[T]`... `\mathbf{B}\to\{T\}\to\mathbf{B}` is the identity functor. `[T]\to\mathbf{B}\to[T]` is
   canonically conjugate..." — `[T]` correct twice, `{T}` wrong once, sandwiched between them, same referent.
   Same at line 84.

7. **GARBLE (self-evident) — spurious overline/accent hallucinated over bold letters with no scan basis**, per
   the reviewing agent (I did not re-derive each): line 46 `\bar{\mathbf{B}}` (plain B elsewhere in the same
   chain), line 55 `\overline{Fx}`, line 90 (four spurious dot-accents in the `[T]≅[T']` formula), line 132
   `\bar{\boldsymbol{A}}`, line 247 `[A\bar{B}=C]`.

PLAUSIBLE (agent-reported, not independently re-derived by me — lower stakes / prose-adjacent): `∅` misread as
Fraktur-g (line 65) and as `\vartheta` (line 196); `⇒` used for the book's isomorphism squiggle (line 72);
missing `⟨⟩` angle brackets (line 90); several dropped-arrow/dropped-subscript instances (lines 63, 118, 124,
126, 149, 315, 413, 415, 427, 437, 236, 170) — full detail in the agent's original report if the fix pass
needs it; a citation range `[1.4389]`-style garble family (lower stakes, cosmetic).

Verified correct (agent-reported, spot-checked plausible, not individually re-derived): equations at lines 133,
134, 142, 244; §1.333, §1.371–1.372, §1.332's 𝒫, §1.388's ℱ; §1.3(10)2's box-operator pair (a useful negative
control showing the □/⊐ confusion above is intermittent, not systematic).

## §1.4 — `chapters/1.4/section-1.4.typ`  (scan: PDF p.56–86, book p.37–67)

1. **SEMANTIC (CONFIRMED — regression from a well-intentioned but wrong prior fix), line 77.** `.typ`:
   "the poset of values of `\mathcal{Val}(Y)` is canonically isomorphic with the poset `\mathcal{O}(Y)` of open
   subsets of Y." `fix_ocr_1.4.py`'s own `SCRIPT_SUBS` comment (lines 68–69) documents the decision: raw OCR
   `${\mathcal{H}}(Y)}$` at this spot was deliberately rewritten to `Val(Y)`. This is backwards: "the poset of
   values of Val(Y)" is a double-application that doesn't type-check (Val always takes a category/subscript
   argument elsewhere in this book — `Val_A`, `Val_{A/B}` — never a bare space Y in parens), whereas "the poset
   of values of ℋ(Y)" is exactly the general fact `Sub_A(B)≅Val_{A/B}` proved earlier in the SAME paragraph,
   specialized to the sheaf category. **CAUTION: revert this ONE site to `\mathcal{H}(Y)` — but do NOT touch
   the OTHER `ℋ(Y)` sites (lines 75, 325) that `fix_ocr_1.4.py` deliberately, correctly, left alone** (its own
   comment: "OCR is correct for the sheaf-topos ℋ(Y)" there) — this is two different uses of the same raw OCR
   string in different contexts, already correctly disambiguated everywhere except this one line.

2. **SEMANTIC (CONFIRMED, self-evident) — `→` should be `↦` where the monic-arrow convention is defined,
   lines 53, 379.** Line 53: "we will indicate that a morphism is monic by denoting it →" — but every one of
   the ~30 subsequent invocations of this exact convention in the same file (e.g. lines 289, 293, 296, 300,
   311: `A_1\mapsto A`, `A_2\mapsto A`, ...) uses `\mapsto` (↦), not a bare `\to`. The sentence that establishes
   the notation uses a different glyph than every use of it. Same bug at line 379.

3. **SEMANTIC (τ→"7"/"T", CONFIRMED via direct scan zoom) — pervasive across §1.49–1.4(12), ~14 pages, the
   namesake symbol of the whole τ-category apparatus.** Book p.55 (PDF p.74), directly verified: "By
   assumption, the latter is a **τ-table**, hence g=1_T" — unambiguous Greek tau in the scan (visually
   nothing like the digit 7), confirmed alongside 3 more correct τ-usages on the same page ("τ-category",
   "axiom **τ**2.2", "A **τ**-category has..."). `.typ` renders this symbol as the digit "7" (lines 455, 493,
   513, 575, 609 ×2, 717, 719) or capital "T" (lines 563, 569, 591, 601, 609, 625, 627, 629, 631, 641, 721,
   733) depending on OCR pass — never as τ. Recommend a section-wide substitution table rather than one-off
   patches (many occurrences, uniform replacement).

4. **SEMANTIC (PLAUSIBLE, not independently re-derived) — composition-at-index `∘_j`/`∘_i` loses its subscript
   throughout §1.49**, e.g. line 412 (the operator's OWN defining equation), line 423 (axiom τ2.2), line 535
   (worst case: the `∘` is dropped outright, leaving a bare stranded subscript `_{n+1}` with no operator).
   Lower priority than findings 1–3 (usually recoverable from context — which index is meant is rarely
   ambiguous once the tuple lengths are read), but numerous.

5. **GARBLE (agent-reported, plausible) — spurious `\Pi` leaking into the box-operator argument, line 41**
   (`\square{\Pi x}` should be `\square{x}` — no Π anywhere on book p.37); **`Ω` spuriously inserted into an
   arrow label, line 671**; **dropped category name "no terminator in L" should be "no terminator in `ℒℋ`",
   line 104**; **calligraphic-letter cluster in §1.461 (lines 318–324)**: bare "C" should be `ℒℋ`, `\mathcal{F}`
   should be `Top`, a diagram `X_1\to Y\leftarrow X_2` lost to raw LaTeX fallback; **⊊ corrupted with a spurious
   "C_i" multiplier, line 356**. Full detail in the agent's original report.

Verified correct (agent-reported): §1.412–1.414 script-word restorations; 1.436 four-bit table crop (verified
complete, 16 rows); box-operator prefix/postfix NOT flipped anywhere checked; §1.48 rational-category `T_D`
fix verified complete (no residual `T_Z`/`T_Q`); no `∋`/`∃` confusion found anywhere in this section (§1.4
doesn't appear to use `∋` notation at all).

## §1.6 — `chapters/1.6/section-1.6.typ`  (scan: PDF p.117–135, book p.98–116)

1. **SEMANTIC (PLAUSIBLE — could not pin the exact scan sentence in my own re-check, but corroborated: the
   region uses cursive "prop"/"Ker" exactly as claimed, and the properness-via-non-containment shape matches
   the book's established pattern, e.g. §1.453) — dropped negation on ⊂, line 334.** `.typ`:
   `\operatorname{\mu}_{\mathcal{X}\mathcal{X}}(A'\subset A)\subset\mathcal{K}_{\mathcal{C}'}(T)` (i.e.
   `prop(A′⊂A) ⊂ Ker(T)`) → agent reports book p.110 shows `prop(A′⊂A) ⊄ Ker(T)` (NOT ⊂) — a dropped negation
   slash flipping a defining biconditional to near-its-opposite. Same bug class as ∋/∃: silently wrong, not
   visibly broken. Recommend a follow-up zoom check before fixing, since I did not land on the exact sentence.

2. **SEMANTIC (CONFIRMED, self-evident) — `∉` lost, line 228.** `.typ`: `0\mathcal{G}\mathcal{F}` — not a
   well-formed relation as printed; should be `0\notin\mathcal{F}` (the standard opening axiom of a pre-filter
   definition). `\notin` renders correctly 3 times elsewhere in this file (e.g. line 290: "if n+1∉A... if
   n+1∈A"), confirming MinerU can get this glyph right — it's just inconsistent.

3. **SEMANTIC (PLAUSIBLE, not independently re-derived) — script 𝒮 (Sets) misread as script I, lines 284,
   320, 405** — all swap the book's standing Sets symbol (used correctly ~30 times elsewhere in this file) for
   script I.

4. **SEMANTIC (CONFIRMED, self-evident) — script ℒℋ(Y) (sheaves on Y) misread as script M, lines 326, 462.**
   Line 324, immediately before: `\mathcal{LH}(Y)` is boolean iff Y is discrete — correct. Line 326, the
   BECAUSE clause for that SAME theorem: "If Y is discrete then `\mathcal{M}(Y) = \mathcal{M}Y`" — a proof
   explaining a claim about ℒℋ(Y) cannot suddenly be about an unrelated ℳ(Y); direct nearby self-contradiction.
   (The RHS `\mathcal{M}Y` is *also* wrong beyond the letter — repeating the LHS makes the sentence an empty
   tautology; book likely has a genuinely different second symbol, e.g. 𝒫 — power set — not re-verified.)

5. **SEMANTIC (CONFIRMED, self-evident) — subscript "1" read as roman "i", line 166.** `.typ`:
   `A_1\cap A_2=0, A_i\cup A_2=A` — the second clause introduces an unexplained `A_i` where the established
   pair from the first clause (and the identical pattern one page earlier at §1.621) is `A_1, A_2`; should be
   `A_1\cup A_2=A`.

6. **GARBLE (agent-reported, self-evident from `.typ` alone) — script-word misreads throughout §1.634–1.662,
   none caught by `fix_ocr_1.6.py`'s substitution list, ~20+ occurrences, different garble every time: "Val"**
   (e.g. lines 220, 239, 259, 330, 338), **"prop"** (line 334, three different garbles in one sentence),
   **"Ker"** (lines 332, 334, 336, 338, 350), **"Sub" as bare `\mathcal{K}(X)`** (lines 310, 492 — an exact
   string the existing fix doesn't cover), **"Rel(...)" missing its "l"** (lines 399, 405), **"Γℱ"** (lines
   330, 350, 357), **"Dom(...)"** (line 504). Recommend extending `fix_ocr_1.6.py`'s `SUB_SUBS`-style table.

**Checked, explicitly NOT flagged (important negative result — preserve this caution):** `f^\#` vs `f^*`
alternates within one sentence at §1.61 (lines 41, 45, 145) — investigated as a candidate bug, checked at high
zoom against book pp.98, 102, and (for calibration) book p.63 where §1.4 genuinely uses BOTH `#` and `*` as
distinct notations in one sentence. **The book plausibly does use both here — not flagged as a bug.** Contrast
with §1.7 finding 1 above, where the SAME glyph pair WAS confirmed wrong (§1.7's case had a clean corroborating
tell — §1.782–784 rendering `f^\#` correctly nearby — that this §1.6 instance lacks).

Verified correct: the full bar-heavy pasting-lemma chain (§1.62 BECAUSE, book pp.100–101); §1.615's asymmetric
arrows; all 18 `content_list.json` equation entries checked (16 clean); the two untypesettable diagrams
correctly routed to image crops.

## §1.7 — additional entries (see main §1.7 section above for findings 1–3)

*(no additional entries — findings 4–7 already recorded above at PLAUSIBLE tier)*

## §1.8 — `chapters/1.8/section-1.8.typ`  (scan: PDF p.157–175, book p.138–156)

1. **SEMANTIC (CONFIRMED, self-evident — regression, existing fix broke the diagram shape) — line 77.**
   `fix_ocr_1.8.py`'s `ARROW_SUBS` rewrites raw OCR (which had the right 3-object shape, `B\to A\to A^\circ`,
   just a wrong arrow label "U") into `\mathbf{B}^\circ\xrightarrow{G}\mathbf{A}` — a 2-object chain that drops
   the middle object A entirely. Consequence, directly visible in current `.typ`: the "adjoint on the right"
   and "adjoint on the left" definitions (two DIFFERENT conditions, by name) now both end in the literal
   identical clause "...is the left-adjoint of `B°\xrightarrow{G}A`" — two distinct definitions cannot have
   the same defining clause; this alone proves the collapse is wrong, independent of the scan. Should restore
   the 3-object shape: adjoint-on-the-right needs `A\to B\to B°`; adjoint-on-the-left needs `A°\to A\to B` —
   both feeding into `B°\xrightarrow{G}A` (which is what survived correctly).

2. **SEMANTIC (CONFIRMED via cross-section — regression, existing fix used wrong spelling+font) — line 226.**
   `fix_ocr_1.8.py`'s `SPL_SUBS` rewrites garbled raw OCR to `\mathbf{Spl}(\mathbf{B})` (bold roman, 3-letter
   abbreviation). But §1.2 (`chapters/1.2/section-1.2.typ`, independently read and confirmed earlier in this
   same review) uses `\mathit{Split}(\mathcal{E})` dozens of times for the identical idempotent-splitting
   operator — fully spelled "Split" (5 letters), italic/script font, never abbreviated "Spl", never bold.
   **CAUTION: the fix should change BOTH the spelling (Spl→Split) AND the font family (`\mathbf`→`\mathcal`
   or matching whatever §1.2 uses) — the bold-B argument itself is correct and should be kept.**

3. **SEMANTIC (CONFIRMED, self-evident) — Δ (diagonal functor) conflated with generic object A, line 419.**
   `.typ`: `(\mathcal{B}\times-,\mathcal{A})\simeq(\Sigma\mathcal{A}(-),\mathcal{A})\simeq(\mathcal{A}(-),
   \mathcal{A}\mathcal{A})\simeq(-,\Pi\mathcal{A}(\mathcal{A}))` — every symbol collapsed to `{\cal A}`/
   `{\cal B}`, losing the distinction between the functor Δ and the object A entirely (and wrongly making B
   calligraphic too). Line 435, same file: `\varDelta(C)` — Δ IS correctly, distinctly rendered elsewhere in
   this file, confirming line 419's `{\cal A}` soup is a corruption, not a real notational choice.

4. **SEMANTIC (CONFIRMED, self-evident) — `=` should be `≃`, line 377.** `.typ`:
   `(A_1,B^{A_2}) = (A_2\times A_1,B) \simeq (A_1\times A_2,B) \simeq (A_2,B^{A_1})` — a single chain of
   natural-equivalence steps that inexplicably starts with `=` then switches to `\simeq` twice; a chain like
   this is standardly uniform (all `\simeq`, matching the book's own three-step pattern), so the first link is
   almost certainly the same relation as the other two.

5. **SEMANTIC (PLAUSIBLE, not independently re-derived) — bold/calligraphic misapplied to plain objects (not
   categories), lines 383, 393, 448** — `B^0`, `B^1`, and a quantified object `B` all get spurious
   `\mathcal{}`/`\mathbf{}` wrapping where the surrounding equation's other terms are plain italic; risks
   conflating "the object B" with "the category B" (bold) in a formalization that tracks that distinction.

6. **GARBLE (agent-reported) — two major diagrams garbled beyond recognition (lines 70, 409), one `#raw()`
   fallback dumping literal LaTeX (line 313), lim/colim arrow-decoration lost to θ (line 114), dropped
   lowercase-vertex arrows and subscripts in §1.845's disjointness proof losing the ℓ/ϰ distinction the proof
   needs (line 311) — full detail in the agent's original report if the fix pass reaches this section.

Verified correct: §1.815, §1.836 (aside from finding 2), §1.852–1.854 elementary constructions and
associativity/distributivity chains, §1.857 exponential-ideal chain, §1.858 Lawvere-Tierney closure triple,
§1.843–1.844 relational-calculus statements, Sub/El/Sh/main-Rel(E) script-word fixes (contrast with the wrong
Split(B) fix in finding 2).

## §1.9 — `chapters/1.9/section-1.9.typ`  (scan: PDF p.176–208, book p.157–189)

1. **SEMANTIC (CONFIRMED via direct scan zoom) — ∃ for ∋, line 397 (§1.949 INTERNALLY DEFINED UNION).**
   Zoomed book p.172 (PDF p.191): the scan shows the SAME curved membership glyph ∋ (not blocky ∃) in BOTH
   occurrences of "⋊(∋∩(F×A))" in this sentence (the ⋂F direct-image and, in the parenthetical, the ⋃F
   direct-image). `.typ` has `\exists` for the first, `\ni` (correctly) for the second — the same exact
   failure mode as the motivating §2.41 bug, independently recurring here. The section's own opening line
   (line 46, "∋⊂[C]×C") and line 237 already establish ∋ as the correct symbol, both confirmed correct.

2. **SEMANTIC (CONFIRMED, self-evident) — χ (characteristic map) OCR'd as bare Latin "x", 5 sites: lines 87
   (×2), 93, 105, 354.** χ renders correctly at least 8 times elsewhere in this same file, including
   immediately adjacent lines (e.g. `\chi_{A_1},\chi_{A_2}` right next to the wrong `x_{A_i}` instances) — a
   plain subscripted variable (`x_{A_i}`) is syntactically indistinguishable from a legitimate Typst variable,
   so this is a silent, "looks plausible" trap rather than visible noise.

3. **SEMANTIC (CONFIRMED, self-evident — regression, existing fix_ocr's `_DROPPED_ARROW` regex assumed the
   wrong replacement) — Heyting double-arrow ↔ collapsed to plain →, lines 140, 144.** `fix_ocr_1.9.py`'s
   `_DROPPED_ARROW` regex (`r'(?<=[A-Z0-9}\)])  +(?=[A-Z0-9{(\\])'`) fires on ANY uppercase-preceded double-
   space and inserts `\to` unconditionally. At line 140: `(A\times V)\cap(A'\to A\times U)` is the result —
   but this is ILL-TYPED regardless of font-reading (you cannot intersect a subobject with a morphism); only
   `(A\times V)\cap(A'\leftrightarrow A\times U)`, invoking the named §1.914 Heyting double-arrow OPERATION on
   `Sub(A)`, type-checks. **CAUTION: `_DROPPED_ARROW` should not blindly assume `\to` — recommend auditing all
   of its hits in this file** (line 105 has the identical dropped-↔ gap but survived because its lowercase
   left operand didn't match the regex's uppercase-only lookbehind — still needs `\leftrightarrow` filled in
   by hand).

4. **SEMANTIC (PLAUSIBLE, not independently re-derived) — restriction operator t↾B rendered 3 different wrong
   ways (∩, ↑, incomplete harpoon), lines 749, 773, 798, 820** — all in the Peano-property proofs. "Restriction
   of t to B" vs "intersection of t and B" are semantically very different; a literal read of line 749 would
   be nonsense (t isn't a subobject to intersect).

5. **SEMANTIC (PLAUSIBLE) — `Sub(·)` functor, 3 occurrences with brace-nesting variants `fix_ocr_1.9.py`'s
   existing exact-string list doesn't match, lines 293, 407, 519** — same root cause the existing fix already
   handles elsewhere, just missed variants.

6. **SEMANTIC (CONFIRMED, self-evident) — power-object bracket `[B]` rendered as curly braces, line 56.**
   `.typ`, same sentence: "The existence of a power-object `[B]` says that `Rel(-,B)` is equivalent to the
   functor `(-,{B})`" — `[B]` correct at the start, `{B}` wrong moments later, identical referent, one
   sentence.

7–8. **SEMANTIC (PLAUSIBLE, moderate confidence per agent) — `(U,[f])` rendered `(U,(f))` at line 127; a
   mismatched coequalizer prime-count at line 777** — not independently re-derived.

9. **SEMANTIC (PLAUSIBLE) — spurious "2" appended to Ω, lines 61, 117, 148** ("traditional notation for [1] is
   Ω2" reads oddly as a compound symbol given the very next clause calls it "**a** subobject classifier",
   singular) — lower stakes, doesn't flip meaning, just adds noise.

GARBLE (agent-reported): 3 `#raw()` fallbacks (lines 154, 470, 517); a severely mangled 7-nested-arrow
coequalizer diagram (line 840); `∉` OCR'd as a yen sign + digit (line 113); spurious overbars on plain letters
(4 sites); citation en-dash dropped (line 854, "[1.986–7]"→"[1.9867]") — same pattern as the §1.2/§2.5 citation
bugs. Full detail in the agent's original report.

Verified correct: line 46/157/237 (∋ established correct, the section's own baseline); line 191 (`∃!`/`∈`
correctly distinguished from the ∋ family); §1.982–1.984 NNO recursion equations (heavily formalized,
symbol-by-symbol checked, clean); §1.915; no residual `\boxed{}`/stray `\square` anywhere (box operator isn't
a Ch.1 concept, as expected).

## §1.5 — `chapters/1.5/section-1.5.typ`  (scan: PDF p.87–116, book p.68–97)

1. **SEMANTIC (CONFIRMED, self-evident) — Γ misread as script T, Henkin-Lubkin proof, line 251.** `.typ`,
   same line: "...\underline{A}/B `\xrightarrow{\Gamma}` `\mathcal{S}`... `T_B` is a representation... hence
   `{\cal T}(\Delta B')\mapsto{\cal T}(\Delta B)` is proper." — Γ used correctly to DEFINE `T_B` earlier in
   this exact sentence, then `{\cal T}` (script T) used later in the same sentence for what must be the same
   functor (Γ, not a second thing called T — `T_B` is the whole representation being built, Γ is one factor
   of its definition). **High fix-value: `henkin_lubkin` is a live Lean declaration (§1.55).**

2. **SEMANTIC (PLAUSIBLE per agent) — missing hat on `Â`, §1.547, line 240** — "dense in A" should be "dense
   in `\hat{\mathbf{A}}`" (Â is the specific intermediate category under construction in this whole paragraph).

3. **SEMANTIC (PLAUSIBLE per agent) — ⊄ misread as ∉, §1.547, lines 238, 240 (2 instances)** — `f\square
   \notin G\square` should be `f\square\not\subset G\square` (comparing box-operator outputs via subset, not
   membership — same "clean, plausible, wrong" shape as ∋/∃). Not independently re-derived from the PDF by me,
   but the type-mismatch argument (□ produces objects/sets, not elements) is sound on inspection.

4–7. **SEMANTIC (PLAUSIBLE per agent, not independently re-derived) — §1.547 cluster**: ∅ misread as Fraktur
   g (line 234); `|A|` rendered as a bare brace (line 230, contradicts the file's own correct `|A|` usage
   elsewhere e.g. line 214); missing angle brackets (line 242); a doubled relation symbol `⊏⊂` for plain `□⊂`
   (line 242).

8. **SEMANTIC/GARBLE thread (PLAUSIBLE per agent, extensively cross-checked on their end — 11 instances) —
   "Sh(Y)" (sheaves) rendered 3 different wrong ways** (`{\mathcal{H}}(Y)`, `{\mathcal{K}}(Y)`,
   `\mathcal{M}(Y)`) across §1.521, §1.585, §1.586, §1.596 — agent reports verifying the correct `\mathcal{Sh}`
   reading independently 4 times against the scan.

9. **SEMANTIC/GARBLE thread (PLAUSIBLE per agent, 15 instances) — "Ab" (category of abelian groups) rendered
   as bare `\mathcal{A}`** (missing the "b"), §1.59–1.599. **CAUTION (preserve): bare `\mathcal{A}` is a real,
   different, correctly-used symbol elsewhere in this same file (§1.535's `\mathcal{A}B`, line 163)** — so
   this is a genuine collision risk, not just cosmetic noise; any fix must be scoped to the Ab-context
   occurrences, not a blanket rename of `\mathcal{A}`.

10–14. **GARBLE/SEMANTIC (PLAUSIBLE per agent) — §1.585/1.591/1.592 cluster**: `ℒℋ` dropped to bare "L" (line
    480); "Top" misread as `\mathcal{F}_{\mathcal{U}}` (line 484); `ℓℓ'+rr'` (composition of two named maps)
    collapsed into one garbled symbol added to itself, silently claiming two different summands are identical
    (line 570); two small matrices/column-vectors rendered as `\Sigma` with sub/superscripts instead of arrays
    (lines 574, 583).

15–19. **Lower-severity findings (PLAUSIBLE, not re-derived)**: 𝒜F(1)/𝒜|Y| rendered as script M (line 84,
    agent's own lowest-confidence item — rests on cross-reference, not a direct unambiguous glyph read); script
    C misread as script E, 6 instances (lines 188–210, inside the §1.543 CAPITALIZATION LEMMA statement
    itself — worth fixing despite being lower severity, since that declaration is heavily used by the Lean
    formalization); 3 plain dropped arrows (lines 445, 447, 758); an underline-scope nit (line 251 area); a
    spurious "U*" for "U's" plural (line 246).

**Verified correct (agent-reported):** the SPT_SUBS fix (§1.522) re-confirmed solid at high zoom. Sub/Rel/
Ker/Cok/Quot conversions spot-checked correct elsewhere. The ±_L/±_R half-additive-category proof's
interpretive reconstructions verified correct against the scan. **Not a transcription bug**: PDF p.112 has a
pre-existing arithmetic typo in the 1990 book itself ("ca" where "ad" is expected) — `.typ` faithfully
transcribes it as-is; leave alone. Agent's own assessment: **the task's premise that "no other script-letter
confusions lurk" beyond Spt was wrong for this section — §1.5 has extensive further script-letter confusion**
(findings 8, 9, 12–14, 16 above), i.e. Chapter 1's prior fix_ocr passes were not as complete as their existence
might suggest — don't assume "has a fix_ocr script" means "thoroughly audited."

## §2.2 — `chapters/2.2/section-2.2.typ`  (scan: PDF p.235–243, book p.216–224) — never audited before this pass

1. **SEMANTIC (CONFIRMED, self-evident) — □ misread as ⋆, line 53 (2.211).** `.typ`, same line: "if
   `\bigstar R = \bigstar S` and `R\square = S\square`" — the box-operator's symmetric source/target pair
   (□R=□S, R□=S□) uses TWO DIFFERENT operator families for what must be the same dual convention used
   throughout the whole book; the second half is correctly `\square`.

2. **SEMANTIC (PLAUSIBLE per agent) — dropped "=1", line 133 (2.217)** — the defining equation for a matrix
   being *entire* (`⋃_j R_{ij}R_{ji}° = 1`) loses its right-hand side entirely, leaving a dangling expression
   asserting nothing.

3. **SEMANTIC (PLAUSIBLE per agent) — dropped arrow + mangled labels, line 73 (2.214)** — `A_1\to A, A_2\to A`
   loses both arrows and both labels (`u_1`, `u_2`), though recoverable from nearby prose; the coproduct
   diagram itself is separately preserved correctly as an image.

4. **SEMANTIC (PLAUSIBLE per agent) — `∪` flattened to bare letter "U", line 30** — same failure class as the
   `∃`/`∋` bug (a plausible-looking ASCII substitute that silently type-checks as a different token); occurs
   specifically where the fragment fell outside a recognized math span.

**Pervasive cursive-wordmark decoder (self-announcing, not misleading — see full table in agent's report):**
`Map`, `Dom`, `Split`, `Cor` all garbled differently almost every occurrence, none compiling to readable
English — blocks reading/grepping rather than creating a false-but-plausible claim. Recommend a
`fix_ocr_2.2.py` substitution table on the `INFLATION_C`/§1.6 `SUB_SUBS` precedent (this section, like the
rest of Ch.2, has zero prior fix_ocr coverage).

Verified correct (agent-reported): the full `A^+` operations block, the modularity-law equation, `f^#`
distributivity, the 2.217 coreflexive-domain chain (structure correct modulo Dom-garbling), all 4 image crops.

## §2.3 — `chapters/2.3/section-2.3.typ`  (scan: PDF p.244–253, book p.225–234) — never audited before this pass

1. **SEMANTIC (CONFIRMED, self-evident — mathematically forced) — both tabulation legs labeled `ℓ`, line 95
   (2.316).** `.typ`: "let `\ell:\gamma\to\alpha, \ell:\gamma\to\beta` tabulate the maximal morphism from α to
   β" — the SAME name `ℓ` cannot denote two different morphisms (one into α, one into β) within one
   definition; agent's PDF check confirms the second should be `r` (cursive script "r", the book's standard
   ℓ/r tabulation-leg pair used throughout this chapter). Compounding: later in the same line, `ℓ` becomes
   calligraphic `\mathcal{A}` and the trailing `r°` is dropped, reattaching the reciprocal to the wrong
   morphism.

2. **SEMANTIC (PLAUSIBLE per agent) — dropped Heyting arrow, line 111 (2.32)** — `B\subset f\backslash(1\ A)/
   f^\circ` (double space) should be `1\to A`; dangerous here specifically because bare juxtaposition reads as
   a product rather than the intended Heyting implication.

3. **SEMANTIC (PLAUSIBLE per agent) — `R/R` set in the calligraphic Rel-font, line 69 (2.314)** — `{\cal
   R}/{\cal R}` should be plain `R/R`; every other occurrence on the same line/list uses plain R, and
   calligraphic R is a real, different, reserved symbol (Rel) elsewhere in the book.

4. **SEMANTIC (PLAUSIBLE per agent) — arrow-label/dropped-arrow cluster, lines 186/188 (2.34)** — three
   separate content losses in one passage: a dropped arrow into `Split(ℰ)`; an arrow label misread as `\circ`
   (reciprocal) where the scan shows `S`; a load-bearing construction label `A(R/S)B` reduced to a generic
   ellipsis placeholder.

5. **SEMANTIC (PLAUSIBLE per agent) — `S`→`s` case drops, lines 55, 61 (2.312–2.313)** — isolated
   lowercasing of the paragraph's named relation `S`, inconsistent with correct capitalization elsewhere in
   the same sentences.

6–7. **SEMANTIC (PLAUSIBLE per agent) — `∩`/`∪` flattened to bare letters "n"/"U" in plain prose**, lines 93,
   53 — same failure class as §2.2 finding 4, occurring outside recognized math spans.

**Pervasive cursive-wordmark decoder**: `Cor`, `Map`, `Split`, `Dom` — same pattern as §2.2, extends that
section's decoder table (see agent's full report for the combined table).

Verified correct (agent-reported, extensive): the ENTIRE 2.357 simple-part derivation chain (only the `Dom`
wordmark itself is garbled, not the math); 2.354's cover+straight decomposition theorem; 2.356; **the
`\frac{R}{S}` (symmetric division) vs `R/S` (ordinary division) typographic distinction — the single
highest-risk notational confusion in this section — holds up correctly throughout 2.35–2.357**; `(S\R/T)°=
T°\R°/S°`; `x(S\R)y iff ∀z(zSx⇒zRy)`; both 2.31 axiom images (pixel-verified); 2.342's matrix-division
construction.

## §2.1 — `chapters/2.1/section-2.1.typ`  (scan: PDF p.214–234, book p.195–215) — never audited before this pass

1. **SEMANTIC (CONFIRMED via direct scan zoom) — `R^∞` should be `R°°`, line 55, the ANTI-INVOLUTION
   EQUATIONS (the section's foundational axioms for reciprocation).** Zoomed book p.195 (PDF p.214): the scan
   unambiguously shows "R°° = R" (two small superscript circles — an involution, matching the "anti-involution
   equations" section title exactly), not "R^∞". My own first read at normal resolution also misread this as
   ∞ — resolved only by the zoom, same lesson as §1.7 finding 1.

2. **SEMANTIC (CONFIRMED, self-evident — mathematically forced) — wrong bound variable on join `∨`, three
   sites: lines 99, 557, 600.** Line 99: `i(RS)k = \vee_i(iRj)\wedge(jSk)` — `i` is already fixed by the LHS
   `i(RS)k`; joining over `i` again inside the summand is meaningless self-shadowing. The only free/summed
   index appearing in both factors `(iRj)` and `(jSk)` is `j` — the join must bind `j`, not `i`. Same
   structural error, same fix, at lines 557 and 600.

3. **SEMANTIC (CONFIRMED, self-evident) — `∏x = x□ = 1` should be `□x = x□ = 1`, line 108 (§2.113).** The
   equation's own two sides mismatch: LHS uses `\prod x` (big-product), RHS of the same equation uses
   `x\square` (box/target) — a defining "source=target=unit" one-object-allegory axiom needs the same operator
   family on both sides.

4. **SEMANTIC (PLAUSIBLE, strong internal tell) — `n≅0`/`n≡0` should be `n≥0`, line 338 (§2.153 ASSEMBLIES).**
   `.typ`: `\{Y_n\}_{n\cong 0}` then, same short definition, `\{Y_n\}_{n\equiv 0}` — two DIFFERENT wrong
   symbols for what must be the identical index bound; the standard reading for an unbounded sequence index is
   `n\geq 0`.

5. **SEMANTIC (PLAUSIBLE) — index/target-category letter inconsistency in the faithful-representation
   theorem, lines 371, 373** — three occurrences of one named index variable, three different (wrong)
   spellings, target category `\mathcal{G}` where `\mathcal{S}` (Sets) is meant.

6. **SEMANTIC (CONFIRMED, self-evident — real content loss, not just a typo) — dropped `Ĉ` (effective
   reflection of C), theorem statement + proof, lines 604–608 (§2.16(13)).** `.typ` has literal blank gaps
   where the symbol should be: "Hence if C is not effective then \_\_ is not..." / "Since C is full in \_\_
   and..." / "If B is projective in \_\_ then choose..." — three clauses of a load-bearing theorem statement
   losing their subject entirely (the theorem's own opening line uses `\hat{\mathbf{C}}` correctly, pinning
   down what's missing).

GARBLE (agent-reported, not individually re-derived): `⊂` dropped/misread as bare "C" in plain prose, lines
59, 162 (3 casualties in one sentence at 162 — contrast with the immediately-following BECAUSE clause, which
is `#mi()`-wrapped and correct); dropped arrows/brackets (lines 338, 555, 598, 600); a `#raw()` fallback with
"Map"→`\sin` (line 578, "reads as nonsense... a second clean instance of the ∃/∋ failure class"); stray
overbars (lines 211, 401). **SYSTEMIC, high fix-value per the agent**: calligraphic operator-abbreviation
words (𝒟om, ℳap, 𝒞or, 𝒮plit, 𝒮id) garbled almost every occurrence, dozens of sites, recommend a
`fix_ocr_2.1.py` substitution table on the `INFLATION_C` precedent — **this section has zero prior fix_ocr
coverage**, unlike Ch.1.

Verified correct (agent-reported): 2.12's core relation definitions; the 2.157 projective-plane axioms (dense
`∈` usage, all correctly distinguished from `∋`); the Desargues Horn sentence; the 2.11 axiom block text; the
n-rhombi containment and 2.16(11) derivation chain; the `□R=R□=0,...` lattice-allegory block. Note: three of
the 2.11 axioms (lines 80, 82, 84) are raw image crops (not OCR text) because MinerU produced unparseable
`\boxed{}` noise — pixel-verified faithful to the scan but **ungreppable**, worth transcribing by hand given
their foundational role.

## §2.4 — additional entries (extends the existing §2.4 section above; continues numbering from 6)

Spot-check of bugs #1–6 (existing entries): re-confirmed accurate against PDF p.254–255 directly.

7. **SEMANTIC (CONFIRMED, self-evident) — ∃ for ∋, 5 more occurrences: lines 307, 330, 368, 384, 323.** Same
   exact failure mode as booktodo bugs #1/#2 and the §1.9 finding above, recurring through the unaudited
   remainder. Line 330 is the worst: the DEFINING equation of ⊃ (the partial order used throughout §2.442–
   2.443) — `⊃ ≜ ∋/∋` ("∋ divided by itself") — is rendered `\exists/\exists`, meaningless as printed.
   **CAUTION (preserve, exact from the agent's report): NOT every `\exists` in this remainder is wrong** — line
   334 has a genuine correct existential (`\bigcup\mathcal{F}=\{x|\exists_A\, x\in A\in\mathcal{F}\}`, ordinary
   set-builder union) and must stay `\exists`. Tell: corrupted instances are the bare backward-E membership
   glyph with no bound variable of its own; the correct one explicitly quantifies a named variable (`\exists_A`).

8. **SEMANTIC (CONFIRMED, self-evident) — ∋ misread as a containment/equivalence symbol (⊇, ⊃, ≡), 5
   occurrences: lines 92, 301, 311, 313, 319.** Confirmed via the identical formula pattern
   `Λ(S)Λ°(S)=(S/∋)(∋/S)⊂S/S` appearing CORRECTLY at line 352 and WRONGLY at line 301 in the same file.

9. **SEMANTIC (CONFIRMED, self-evident) — cospan rendered as a directed chain, lines 293, 299.** Item (3) of
   the pre-positive/well-joined list needs `\alpha\xrightarrow{S_1}\gamma\xleftarrow{S_2}\beta` (both arrows
   point INTO γ, matching the well-joined cospan diagram immediately above it) — `.typ` has both arrows
   pointing the same direction, changing which object plays the mediator role.

10. **SEMANTIC (PLAUSIBLE, strong internal tell) — pre-positivity's doubled-letter products (`ℓℓ°`, `ϰϰ°`,
    `ℓϰ°`) collapsed to single-letter tokens, lines 277, 305, 446** — a different garbled spelling each time,
    confirming OCR failure on Freyd's cursive ℓ/ϰ, not real notation.

11. **SEMANTIC (root cause, CONFIRMED, self-evident) — Λ(R) (power-transpose operator) misOCR'd as plain
    `A(R)`, 23 lines: 90, 92, 94, 129, 137, 139, 141, 147, 301, 319, 327, 332, 344, 346, 348, 350, 352, 354,
    370, 374, 376, 388, 396.** Same bug as booktodo #2/#5, pervasive since Λ is the power allegory's core
    operator. Confirmed genuinely wrong (not stylistic) because the identical symbol correctly renders as
    `\varLambda`/`\Lambda` 2–4 lines away in several of these same passages.
    **CAUTION (preserve, exact from the agent's report): do NOT blanket sed-replace `A(`→`Λ(`.** Two
    exceptions found IN the remainder itself: line 279's `\mathbf{Im}(\mathcal{\boldsymbol{A}})` is a misOCR
    of **ϰ** (var-kappa), not Λ; line 370 has THREE `A`'s in one clause where only the 2nd and 3rd are
    misOCR'd Λ — the FIRST is a genuine, book-printed italic letter "A" naming a fresh coreflexive (visually
    distinct serif glyph from Λ's triangular shape). Any fix must check each occurrence's context.

12. GARBLE (agent-reported): assorted dropped/misread symbols in §2.442–2.446 (∩ read as letter "O", `∈`
    read as "e", more C-for-⊂ instances at lines 129, 368) — full detail in the agent's report if needed.

Verified correct (agent-reported, extensive — §2.414, §2.421 [contrast case, correct nearby], §2.423–2.424,
§2.431–2.438, §2.435, §2.453, and all 5 figure-image crops in §2.443 pixel-checked against the scan). Real
negative result: zero `∩`/`∪` swaps found anywhere in lines 80–514, checked visually (not just grepped, since
a swap is invisible to grep).

## §2.5 — `chapters/2.5/section-2.5.typ`  (scan: PDF p.274–283, book p.255–263) — never audited before this pass

1. **SEMANTIC (CONFIRMED via direct scan read) — dropped prime turns a proof-by-contradiction into a
   tautology, line 187 (§2.56(11) BECAUSE).** Book p.262 (PDF p.281), directly read: "...we obtain H_ht=H_h't.
   Thus H_htvR=**H_h'**tvR, that is, H_hH_g=**H_h'**H_g. This contradicts [2.56(10)]." — clear prime mark on
   the second `h` in both clauses. `.typ` literally shows a stray COMMA exactly where the prime mark was
   misread as one: `H_h,tvR` / `H_h,H_g` (not `H_{h'}`). As transcribed the displayed equation is a trivial
   tautology (`H_h X = H_h X`) instead of the proof's actual content — the assertion that two DIFFERENT
   natural transformations are equal, which is what contradicts [2.56(10)]. Highest-priority fix in this
   section: it inverts a proof's logical structure, not just a symbol.

2. **SEMANTIC (PLAUSIBLE per agent) — `\dag` for the amenable-closure operator `+`, line 70** — every other
   superscript in the same sentence (both before and after) uses plain `+`; `R^+` is §2.53's central operator,
   `\dag` has no defined meaning here.

3. **SEMANTIC (PLAUSIBLE per agent) — bound/free index collapsed, line 100** — `R_i^+\subset(\bigcup_i R_i)^+`
   should be `R_j^+\subset(\bigcup_i R_i)^+`; the surrounding prose's own "for each j" is the internal tell
   (no other `j` appears in the formula as transcribed).

4. **SEMANTIC (CONFIRMED, self-evident) — 𝒟om (Domain) misread as `\mathcal{Z}om`/`\mathcal{L}om`, lines 80,
   133 (×2).** Line 187 (finding 1's context, directly read above) already establishes `\mathcal{D}om(R)` as
   the correct spelling in THIS SAME FILE — so lines 80 (`\mathcal{Z}om`) and 133 (`\mathcal{L}om`, twice) are
   confirmed misreads of the identical calligraphic-D glyph, not alternate notation.

5. **SEMANTIC (CONFIRMED, self-evident) — 𝒮 (the category Sets) misread as script I, lines 114, 118, 143,
   165.** Line 118 alone self-contradicts: "...compute the subterminators in `\mathcal{I}^{\mathbf{A}^\circ}`.
   ... Therefore the lattice of subterminators in `\mathcal{S}^{\mathbf{A}^\circ}` consists of..." — identical
   referent, same sentence, first ℐ then (correctly) 𝒮.

6. **SEMANTIC (PLAUSIBLE per agent, quote confirmed accurate) — `Map` functor mangled, lines 90, 92** —
   `\mathcal{M}q_2(\mathbf{Q}_2)` and `\mathcal{M}\mathcal{G}/(\mathbf{Q}_1)` don't parse as anything standard;
   `Map(Q_2)`/`Map(Q_1)` fit the surrounding §2.414/2.51/2.537 context (Map(A) is used throughout this chapter
   to build the boolean topos **B** this proof constructs) far better. Telltale: the prose right after has a
   detached leading "v" of "valued" — consistent with "Map(" being swallowed into garbage upstream.

7. **SEMANTIC (PLAUSIBLE per agent) — wrong category referenced, line 161** — plain "B" where script "ℬ" is
   meant (two DIFFERENT objects in this chapter: bold **B** is the boolean topos from §2.542, script ℬ is the
   §2.562 category-of-maps construction; a formalizer grepping "B" here would silently grab the wrong one).

8. **SEMANTIC (CONFIRMED, self-evident) — citation range collapsed, line 165.** `[2.5635]` should be
   `[2.563-5]` (en-dash dropped, fusing two numbers into a non-existent section) — confirmed by the IDENTICAL
   citation correctly rendered as `[2.563-5]` later at line 191 in the same file.

9. **SEMANTIC (PLAUSIBLE per agent) — case-flip on a morphism name, line 80** — `\bar{s}\subset\bar{1}` should
   be `\bar{S}` (uppercase), matching the rest of the same proof's consistent uppercase `S`.

GARBLE (agent-reported, several with real content-loss risk since they render LIVE via `#mitex` rather than a
crop, so a wrong glyph actually shows up in the compiled book — not just in a discarded raw string): a
currency symbol for the boolean-quotient locale notation (line 40); a badly mangled closing sentence in §2.551
needing re-transcription from the scan rather than patching (line 102, agent explicitly flags low confidence
in its own reconstruction — don't trust the proposed intermediate symbols, just the "needs re-OCR" diagnosis);
Π→"IIB," (line 106); an equalizer pair's second morphism mis-accented `\ddot{s}`→`\bar{S}` (line 173, renders
live); a malformed empty-`\mathcal{}` overline (line 167); dropped arrow + spurious Δ in the NNO-in-quotient
paragraph (line 177); a doubled arrow (line 181); "vil"→"will" (line 110, compounded by actual scan
damage/fade at that spot, not pure OCR error). Full detail in the agent's original report.

Verified correct: line 76 (§2.537 BECAUSE) uses `∋` correctly at the exact spot referencing the already-fixed
§2.41 box-naming bug — confirms the earlier fix's symbol choice is being used correctly downstream. The
§2.531–2.541 monotonicity/lattice/transitive-closure chains match the scan exactly. All cropped-image
diagrams (not OCR text) visually match.
