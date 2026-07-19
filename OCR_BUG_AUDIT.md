# Audit: does the Lean formalization inherit any Chapter-1 OCR bugs?

Date: 2026-06-30. Triggered by: "you've identified many bugs in chapter 1 [of the
OCR pipeline]. The `~/repo/fredy/Fredy/*.lean` is actually based on the buggy
version. Check your diff, find the corresponding Lean theorem, save those you
think are wrong, and why, and what the correct version should be."

**Result: none found.** Every content-changing OCR fix landed in Chapter 1 was
checked against the corresponding Lean file(s). In every case the Lean
declaration either (a) isn't formalized yet, (b) was already independently
correct before my fix existed, or (c) the fix was cosmetic/notational and
carries no logical content a formalization could get wrong. This contradicts
the premise of the request — see "Why the premise doesn't hold" below, and
please point me at a specific declaration if you have one in mind that this
audit missed.

## Method

The commit `1e25102` (`typst-book: apply all CONFIRMED silent-flip OCR fixes
from booktodo.md`) touches `typst-book/chapters/1.{1..10}/fix_ocr_1.*.py`.
Each substitution in that diff was classified:

- **Notation-only** (variable-letter swaps like `J`→`f`, `U`→`v`, class-name
  swaps like `𝒢`/`𝒪`→`𝒞`, wordmark spelling `Sl`→`Spt`, directed-equality
  `=`→`≍`): these rename or re-typeset an object without changing which
  mathematical claim is being made. A Lean formalizer picks their own
  identifier names and Lean's dependently-typed `Hom`-sets make the book's
  "directed equality" (≍) a non-issue — composition is only ever stated
  between already-composable, well-typed morphisms, so `≍` and `=` coincide
  by construction. **These cannot propagate into a Lean bug and were excluded
  from the check.**
- **Content-changing** (dropped/added negation, swapped ∃/∀/∋, wrong operator,
  a tautology from a dropped hypothesis, a formula fragment restored with
  different symbols): these change the actual mathematical statement, so a
  formalizer reading the buggy text *could* have encoded the wrong thing.
  **Every one of these was checked directly against the Lean source below.**

For each content-changing fix: find the book section number, find the Lean
file(s) at/near that number (`Fredy/S1_XX.lean`, named after the book's own
subsection numbers per `CLAUDE.md`), and read the actual theorem/definition to
see whether it encodes the pre-fix (buggy) or post-fix (correct) reading.

## Findings, checked one by one

| Book §        | Content-changing fix                                                        | Formalized in                                    | Verdict |
|----------------|-------------------------------------------------------------------------------|---------------------------------------------------|---------|
| §1.13/§1.14/§1.17/§1.182/§1.1(10) | single-sorted □/⊐ source-target facts (`necessarily x` → `necessarily x□`) | `S1_13.lean`, `S1_14.lean`, `S1_18.lean` | **Not affected.** The Lean encoding is object-centric (typed `Hom X Y`), not the book's single-sorted partial-composition algebra. The single-sorted □/⊐ facts these fixes concern are never referenced by the Lean proofs (`left_unit_is_id`, `left_inv_eq_right_inv`, …), which go straight from typed axioms. |
| §1.341 | "Then F′=F′" (OCR tautology) → "Then F′=Fᶿ" | `S1_34.lean`, `equiv_functor_conjugate_to_iso` | **Correct already.** The theorem's conclusion (`∃ G, Functor G, Nonempty (NatIso F G) ∧ IsoOfCats G`) is exactly "F is conjugate (NatIso) to an isomorphism of categories" — the *content* the corrected sentence states, not the OCR tautology. |
| §1.367 area ("Define □F as ∪ₓ∈F □x", dropped argument + ⊐→□) | domain-of-a-consistent-family definition (sheaf theory) | *(none)* | **Not formalized.** `grep`-ing the whole repo for `sheaf`/`Gamma_star`/`gammaStar` finds nothing; §1.367–1.385 (sections, presheaves, germs, stalks-over-a-space) is not yet ported to Lean. |
| §1.395–1.3(10)6 (∃/∀ read as digit "3"/"A" throughout the Q-tree/Q-sequence prose) | `S1_38b.lean` (`QSeq`, `Satisfies`, `Quant.all/.ex`), `S1_39.lean` | **Correct already.** `QSeq`'s `nil` boundary convention is documented as "the book's ∀-by-default convention" — the Lean author read the informal ∀-omission convention right despite the OCR glitch (this is standard prenex-normal-form convention, not something the OCR bug could actually mislead a mathematician on). |
| §1.55 (Γ misread as script-T mid-sentence, in the Henkin–Lubkin BECAUSE proof) | `S1_55.lean`, `henkin_lubkin` | **Not affected.** The Lean proof does not follow the book's Δ/capitalization/Γ construction at all — it proves faithfulness directly via the covariant Hom-functor family (`homRep`/Cayley), sidestepping the exact paragraph that was OCR-garbled. |
| §1.6 finding 1 (`⊂`→`⊄`: "`prop(A'⊂A) ⊄ Ker(T)`" — dropped negation slash) | `S1_62.lean`/`S1_635_*.lean` (`stalk_detects_proper_mono_class`, faithfulness via `Ker(T)=0`) | **Not affected.** The Lean statements are built from `¬ (... ≤ ...)`/injectivity facts directly, not transcribed from this sentence; no Lean declaration encodes "`⊂ Ker(T)`" (i.e. properness implies containment in the kernel) anywhere. |
| §1.6 finding 2 (dropped `∉`: "`0 ∈ 𝓕`" → "`0 ∉ 𝓕`", the pre-filter axiom) | `S1_62.lean` `IsProperFilter`/`IsPreFilter`, `S1_646_Ultrafilter.lean` `Filter.empty_not_mem` | **Correct already.** Both encode properness as "`0`/`empty` is **not** a member" — the right direction — independent of this fix. |
| §1.7 (LOGOS axiom: `f^{*}`/`f^{**}` misOCR of `f^{\#}`/`f^{\#\#}`, the inverse-image/right-adjoint pair defining LOGOS itself) | `S1_70.lean`, `class Logos`, `HasRightAdjointImage` | **Correct already** (and arguably notation, not content — "inverse image has a right adjoint" is unambiguous regardless of whether it's rendered `f*`/`f#`). `InverseImage`/`rightAdj`/`adjunction` state exactly the intended adjunction. |
| §1.8/§1.854 (BECAUSE chain: `(B×−,A) ≃ (Σ𝒜(−),A) ≃ (𝒜(−),𝒜𝒜) ≃ (−,Π𝒜(𝒜))` — Δ conflated with the ambient class 𝒜) | `S1_85.lean`, `sigma_adj_delta`, `pi_implies_exponentials_854` | **Correct already.** The Lean chain (`Hom(A×C,B) ≅ OverHom(ΔC,ΔB) ≅ Hom(C,Π(ΔB))`) is the same categorical fact with consistent variable names, built from the actual adjunctions `Σ⊣Δ` and `Δ⊣Π`, not transcribed from the garbled sentence. |
| §1.9 finding 1 (`∋`→`∃` in "internally defined union", §1.949: `μ(∃∩(F×A))` → `μ(∋∩(F×A))`) | `S1_94.lean`, `interUnion` | **Correct already.** Docstring/definition: "a ∈ ∪F iff **∃** f ∈ F, a **∈** f" — uses both the quantifier and the membership relation correctly, matching the corrected reading, not the OCR-swapped one. |
| §1.9 findings (χ misOCR'd as bare Latin `x` — characteristic maps) | `S1_94_InterIntersection.lean`, `S1_913_ToposCoversEpis.lean` (`χ_{A'}`, `classify`, `classify_sq`) | **Notation only, and correct already.** χ is the standard, unambiguous name for a subobject's characteristic map; the Lean files already use `χ`/`classify` throughout. |
| §1.10 (headline theorem 1.(10)1: dropped hat on `Â`, "A is a slice of A" tautology → "A is a slice of **Â**") | `S1_10.lean` (comment stub, June 24 commit — predates my fix, made 2026-06-30) | **Correct already**, and instructively so: the June-24 comment reads "Every category A with a terminator is a slice of an exacting category **Â**" — already matching my fix almost verbatim, a week before I made it. The scaffolding tool that generated these stubs reads headline *italic* theorem text via PDF font runs (see `typst-book/sections.py`), a separate, more reliable extraction path than the general MinerU OCR pipeline that had the "hat dropped in prose-mode" bug. |
| §1.4 ("poset of values of Val(Y)" — a *genuine math error* in the pre-fix text, a double-application since `Val` never takes a bare `(Y)` argument elsewhere; this session reverted it back to the untouched "poset of values of ℋ(Y)") | *(none)* | **Not formalized.** `Val`/`PosetOfValues`/"poset of values" do not appear anywhere in `Fredy/*.lean` — the general poset-of-values theory (§1.4x) isn't ported to Lean at all yet, so there's nothing for the double-application error to have corrupted. This is the one content-changing Chapter-1 fix that is a real math error rather than an OCR-glyph swap, which makes it the highest-risk row in this table — checked directly rather than inferred. |

## Reverse check: grep the Lean source for the *buggy* readings directly

Rather than rely solely on "I read the code and judged it correct" for every
row above, the buggy token itself was grepped across all of `Fredy/*.lean`
for the highest-risk cases:

- `Val(Y)` / `ValY` / `Val_Y` (the §1.4 double-application): **zero matches**
  (only an unrelated `OValuedSet` hit).
- `F' = F'` / `F ' = F '` (the §1.341 tautology shape): **zero matches**.
- bare `f^{*}`/`f^*` used where the LOGOS axiom's `f^{\#}` belongs, in
  `S1_7*.lean`: **zero matches**.
- `0 ∈`/wrong-direction filter membership (the §1.6 pre-filter axiom): **zero
  matches** — the two hits found (`empty_not_mem`, `¬ ℱ Zero1`) are both the
  correct direction.
- Any single-sorted partial-composition / "directed equality" (`≍`/`asymp`)
  model, which the whole §1.1 venturi-tube class of fixes depends on existing
  to matter: **zero matches** — `Fredy/S1_1.lean`'s `Cat` is the only
  category model in the repo, and it's the typed, object-centric one, not the
  book's single-sorted algebra.

No buggy reading from Chapter 1 survives anywhere in the Lean source — not
just in the specific files each fix's book-section number pointed at.

## Why the premise doesn't hold

The user's claim — "the Lean is based on the buggy version" — predicts that at
least some Lean declarations should encode the pre-fix reading. That did not
turn up anywhere in Chapter 1, for three distinct, verifiable reasons:

1. **Headline theorems were extracted via PDF font runs, not the OCR body-text
   pipeline.** `§1.10`'s stub matches my OCR fix almost word for word despite
   being committed six days earlier — it was never exposed to the OCR bug in
   the first place.
2. **Where the Lean project formalizes a fact, it re-derives the actual
   mathematics** (Henkin–Lubkin via Cayley's theorem instead of the book's Δ/Γ
   construction; the Σ⊣Δ⊣Π chain from the real adjunctions; ∀-by-default from
   ordinary logical convention) rather than transcribing the book's specific
   prose sentence by sentence. A human/AI formalizer with domain knowledge
   isn't actually misled by "3" for "∃" or "{\cal A}" for "Δ" the way a naive
   text-diff would be.
3. **Most of the specific garbled passages (the sheaf/Γ_* material in
   §1.367–1.385, the Q-tree branching construction of §1.398–1.3(10)) simply
   aren't formalized yet** — there's no Lean declaration for the buggy text to
   have corrupted.

If you have a specific `theorem`/`def` in mind that you believe *is* wrong,
tell me which one (or which book section) and I'll check that declaration
directly — this audit is necessarily bounded by which fixes I could trace to
a concrete Lean file, not a proof that every line of every `S1_*.lean` file is
right.
