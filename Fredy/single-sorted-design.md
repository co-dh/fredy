# Single-sorted (arrows-only) vs two-sorted `Cat` — why the repo stays two-sorted

Finding from a 2026-06-19 literature check, prompted by "can we convert the whole repo to arrow-only?"

## The repo's choice

`Cat` (`Fredy/S1_1.lean`) is **two-sorted**: objects are a type `𝒞`, `Hom X Y` is a hom-type indexed by
source and target, and `comp`/`id` are **total**. 94 files, ~61k lines build on it. This is the standard
proof-assistant design, deliberately chosen — keep it.

## What the literature says

- **Both formulations are old and known.** A *one-sorted* category (a universe of pure maps; objects =
  identities — Freyd's arrows-only style) vs a *two-sorted* one (objects prior to maps). Two-sorted is
  dominant; one-sorted appears only occasionally — Ehresmann, Street, Cockett. So single-sorted is a real
  but minority research tradition, and Freyd–Scedrov sit in it.
- **Partial composition is *the* central difficulty** of formalizing category theory in a proof assistant.
  This is the whole cost of going single-sorted.
- **Every major library uses typed Hom indexed by objects** to make composition total/well-typed
  structurally, not via side-proofs:
  - Lean/Mathlib: `X ⟶ Y` indexed by source/target; `f ≫ g` total when types align; category inferred by
    typeclass on the object type.
  - Agda/agda-categories: `Hom` is a (setoid) family indexed by the *product of objects*, composition
    defined so all compositions are well-defined — the indexing is exactly what avoids partiality. (Setoid
    enrichment is an orthogonal proof-relevance choice, not about sorting.)
  - Coq/Rocq (UniMath / HoTT / graph-rewriting) follow the same indexed-Hom pattern.
- **Even elementary/first-order diagram chasing goes many-sorted**, not single-sorted arrows-only — single
  sorted is rarely chosen even when optimizing for a first-order presentation.
- **Extra HoTT reason for indexed Hom:** it avoids ever talking about *equality of objects*, which
  misbehaves in type theory — a second motivation beyond totality.

## Conclusion

Single-sorted is mathematically equivalent and is how Freyd writes it on paper (partiality is free in prose).
In a proof assistant it trades total, type-checked composition for pervasive partiality + `dom`/`cod` side
conditions on every line — which is why essentially nobody formalizes it that way. A blanket conversion of
the repo would be a 61k-line rewrite with negative ergonomic payoff. The *point-free reasoning* style we
already use (subobject = its monic `S.arr`, `BinRel`, `image`, `∃_f` as arrow algebra, elements only as
`1 → A`) gives the arrows-only elegance without paying the partiality tax.

## Sources

- [Aspects of category theory in proof assistants (thesis)](https://theses.hal.science/tel-05229403v1)
- [A First Order Theory of Diagram Chasing](https://arxiv.org/abs/2311.01790)
- [Formalizing Category Theory in Agda (Hu & Carette)](https://www.cas.mcmaster.ca/~carette/publications/2005.07059.pdf)
- [agda-categories library](https://github.com/agda/agda-categories)
- [Mathlib category theory overview](https://leanprover-community.github.io/theories/category_theory.html)
- [Univalent categories and the Rezk completion](https://arxiv.org/pdf/1303.0584)
- [On equality of objects in categories in constructive type theory](https://arxiv.org/pdf/1708.01924)
