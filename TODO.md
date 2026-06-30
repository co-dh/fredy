# TODO

## 1. Rename the Σ (forgetful-functor) family `SliceForget*` → `Sigma*`

**Why.** The book calls the slice forgetful functor `Σ : 𝐀/B → 𝐀`. We cannot use the glyph as a
Lean identifier:

- `Σ` (U+03A3) is a **reserved token** — Lean's dependent-sum binder (`Σ x, …`). `def Σ… ` fails with
  `unexpected token 'Σ'; expected identifier`.
- The math-alphanumeric capital sigmas `𝚺` (U+1D6BA), `𝛴` (U+1D6F4) are **rejected by Lean's
  identifier lexer** (`expected token`) — even though `𝒞` is accepted, these codepoints are not
  whitelisted.
- Lowercase `σ` (U+03C3) *is* legal, but clashes with the book's capital `Σ` and reads like a
  morphism variable.

So the closest legal, book-faithful name is ASCII **`Sigma`** (matching `Δ`, which *is* a legal
identifier and is already used book-faithfully in `SliceDeltaCartesian.lean`).

**Rename map** (keep the rest of each name; longest-first to avoid substring corruption):

| current                                      | →  | new                              |
|----------------------------------------------|----|----------------------------------|
| `sliceForget_reflects_isPullback_terminal`   | →  | `sigma_reflects_pullback_terminal` |
| `sliceForget_reflects_isPullback`            | →  | `sigma_reflects_pullback`        |
| `sliceForget_preserves_isPullback`           | →  | `sigma_preserves_pullback`       |
| `sliceForget_term`                           | →  | `sigma_term`                     |
| `sliceForgetFunctor`                         | →  | `sigmaFunctor`                   |
| `sliceConeForget`                            | →  | `sigmaCone`                      |
| `SliceForget`                                | →  | `Sigma`                          |
| `sliceForget` (lowercase, lone)              | →  | `sigma`                          |

Note this also applies the `isPullback → pullback` book-wording cleanup (item 2) to these names.

**Scope.** 9 files. Regenerate the exact list with:
```
grep -rlE 'SliceForget|sliceForget|sliceConeForget' Fredy/*.lean
```
(Currently: `S1_44`, `S1_53`, `SliceRegular`, `SliceTopos`, `SlicePreTopos`, `SliceDeltaCartesian`,
plus the §1.53/capitalization users — confirm via the grep.)

**Procedure.**
1. Replace **longest identifiers first** (top of the table down) across the 9 files, so e.g.
   `sliceForget_reflects_isPullback` is not mangled by an earlier `sliceForget` replacement.
2. Update doc comments/`/- … -/` prose that name the identifiers too.
3. `lake build` must stay green (166 jobs).
4. Spot-check axioms unchanged: `#print axioms Freyd.sigma_reflects_pullback` (etc.) — should match
   the pre-rename `#print axioms`.
5. `grep -rn 'sorry' Fredy/` count must not increase (lowercase `sorry` only).

## 2. `isPullback` → `pullback` in lemma names (book wording)

The repo predicate is `Cone.IsPullback` (a *type* — leave it). But lemma **names** should read the
book's way: `…_preserves_isPullback` → `…_preserves_pullback`, etc. Fold this into item 1's renames;
`SliceDeltaCartesian.lean` already uses `Δ_preserves_pullback` (no `is`).

## 3. De-topos `sliceForget_reflects_isPullback` and move it to `SliceRegular`

`sliceForget_reflects_isPullback` (general base `B`) currently lives in **`SliceTopos.lean`** and so
carries a **spurious `[HasSubobjectClassifier 𝒞]`** hypothesis (a file-level topos `variable`) plus
`[HasBinaryProducts]` `[HasPullbacks]` — *its proof uses none of these* (only the over-hom triangle).

- Move it next to `sliceForget_preserves_isPullback` / `sliceForget_reflects_isPullback_terminal` in
  **`SliceRegular.lean`**, stated with no extra instances. Loosening hypotheses is safe for all callers
  (they resolve the same qualified name `Freyd.sliceForget_reflects_isPullback` via import).
- Then in **`SliceDeltaCartesian.lean`**, `Δ_preserves_pullback` can drop its **inlined** reflect
  transport (the `⟨u, uw⟩` lift) and become the one-liner
  `sliceForget_reflects_isPullback (deltaCone B c) (forget_deltaCone_isPullback B c hc)`.
- Verify `lake build` green + axioms of `Δ_preserves_pullback` still `[]` (no axioms).
