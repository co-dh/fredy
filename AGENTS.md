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
  EXCEPTION (capitalization project, §1.543): mathlib's *ordinal / transfinite-recursion*
  set theory (`Mathlib.SetTheory.Ordinal.*` and the order/well-founded lemmas it needs) MAY be
  used, since Freyd treats transfinite recursion as ambient set theory he never re-derives.
  All *category theory* stays hand-built on this repo's own `Cat` — never import
  `Mathlib.CategoryTheory.*` (it would clash with `Cat`). Only the ordinal-indexed iteration
  file should import mathlib; keep every other file mathlib-free so builds stay fast.
DRY as much as possible.
