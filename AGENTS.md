This project explain the book Categories, Allegories of Freyd.
You should should any 3+ digits sections of the book into Sa_bc.lean. e.g. section 1.123 in S1_12.lean.
The code should follow the book's terminology, wording, convension.
Write composition in diagram order, by juxtaposition: `xy` means first x then y (the book's convention).
Always prefer the book's definition over ad-hoc simplifications — even if the
book version requires more typeclasses (e.g., `Entire R := 1_A ≤ R°R` via
`compose` rather than `∃ h, h ≫ R.colA = id_A`).
If a proof used theorem from other section but not defined yet, prove them in $a_bc.lean.
Make the prove constructive: do not use atom of choice unless unavoidable.
feel free to copy ideas from Mathlib, but do not bring in them as dependency.
  STRICTLY MATHLIB-FREE, NO EXCEPTIONS. The repo has ZERO external dependencies:
  `lake-manifest.json` lists no packages and no `Fredy/*.lean` imports anything outside
  Lean 4 core (`Init`) and `Fredy.*`. The §1.543 transfinite-recursion work that once
  earmarked mathlib's ordinals was hand-built instead (`Fredy/WellOrdering.lean`, Zermelo
  from `Classical.choice`); order/lattice/Frame machinery is hand-rolled too (`Locale.lean`,
  `S1_72`). Never add a `require` and never `import Mathlib`/`Batteries`/`Aesop`/`Std` — keep
  the repo self-contained so builds stay fast and clones stay tiny.
DRY as much as possible.

## Book notation pitfalls (OCR drops bold)
- **Bold `𝐀` = the category; plain `A`, `B`, … = its objects.** The OCR loses bold, so a category
  `𝐀` shows up as plain `A`. In `𝐀/B` the `𝐀` is the *category* and `B ∈ 𝐀` is an *object* — read it
  as "the category `𝐀` sliced over the object `B`", never "object A over object B".
- **`𝐀/B` has two definitions; use the `B × A → B` one.** (a) Plain slice: objects are all arrows
  `X → B`. (b) The §1.544 redefinition: pass to the inflation `𝐀'` (objects = finite sequences,
  product = concatenation) giving strict cancellation `B×A = B×A' ⟹ A = A'`, so `𝐀 ⊆ 𝐀/B` and
  `Δ: 𝐀 → 𝐀/B`, `A ↦ (B × A → B)`, is a literal inclusion — the objects `B × A → B` are exactly the
  embedded copy of `𝐀` (the image of `Δ`). The two are equivalent categories; Freyd works with the
  `B × A → B` presentation. Factorisation: `(B×−) = Σ∘Δ`, with `Σ: 𝐀/B → 𝐀` forgetful
  (`(X→B) ↦ X`, so `Σ(B×A→B) = B×A`) and `Σ ⊣ Δ` (Σ is the *left* adjoint to base change `Δ = B×−`).

## Writing explanations / notes
Introduce a concept before its first use. Order sections, paragraphs, and figures so every term, object,
or notation is defined or explained before it appears in another argument. If a later section uses a thing
(e.g. the swap `ℤ/2`-set as a counterexample), the section that says what that thing *is* must come first.
Prefer relative cross-references ("the next subsection", "above") over hard-coded section numbers, which
break when sections are reordered. Avoid unexplained field-specific notation (e.g. `Bℤ/2`, `π₁`); spell it
out ("the one-object category of `ℤ/2`") unless the term has already been introduced.

## Searching the book text
The greppable book prose lives in `/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.typ`
(and the `section-*.fixed.md` siblings — cleaned OCR). ALWAYS grep there.
`/home/dh/repo/fredy/book-all.typ` is only a 63-line wrapper that `#include`s those chapter
files — grepping it alone finds NOTHING. To search the whole book:
`grep -rni "<term>" /home/dh/anki/typst-book/chapters/`.
