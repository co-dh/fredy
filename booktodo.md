# booktodo.md — bugs in the Typst book transcription (vs the original scan)

Source of truth: `/home/dh/anki/categories-allegories.pdf` (the original Freyd scan), read VISUALLY
(the Read tool renders PDF pages as images). The `.typ` files under
`/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.typ` are an OCR-derived transcription and
have errors. Below are bugs found 2026-06-30 while verifying the §2.41 power-allegory definition.
Each lists: file:line — what the `.typ` has now → what the scan shows (book page / PDF page).

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
