# Milestone 2a spec — `Fredy/CatColimit.lean` (directed colimit of categories: objects)

Create the NEW file `Fredy/CatColimit.lean` exactly as below. It defines a directed system of **categories**
(on this repo's hand-built `Cat`), and extracts the colimit's **object type** by reusing the type-level
directed colimit from Milestone 1 (`Fredy/DirectedColimit.lean`). The hom-colimit and `Cat` instance are a
LATER milestone — do NOT attempt them here.

Reference implementation (implement exactly; adjust only if the compiler demands, never add `sorry`):

```lean
/-
  Directed (filtered) colimit of categories — Milestone 2a (objects only).

  A `CatSystem` is a directed system of categories over `(ι, D)`: a family of
  categories `A i` with transition functors `F hij : A i → A j` respecting
  identity and composition on objects.  Its colimit's OBJECT type is the
  type-level directed colimit (Milestone 1) of the object families.  The
  hom-colimit and the `Cat` instance on the colimit are Milestone 2b.

  Category theory is hand-built on this repo's `Cat`; no mathlib here.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.DirectedColimit

open Freyd

namespace Freyd.Colim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- A directed system of categories over `(ι, D)`: each `A i` is a category
    (`catA i`); for `i ≤ j` a functor `F hij : A i → A j` (`functF hij`), with
    `F` respecting identity and composition on objects. -/
structure CatSystem (ι : Type u) (D : Directed ι) where
  A : ι → Type w
  catA : ∀ i, Cat.{w} (A i)
  F : ∀ {i j}, D.le i j → A i → A j
  functF : ∀ {i j} (hij : D.le i j), @Functor (A i) (catA i) (A j) (catA j) (F hij)
  F_refl : ∀ {i} (x : A i), F (D.refl i) x = x
  F_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k) (x : A i),
    F (D.trans hij hjk) x = F hjk (F hij x)

/-- The underlying directed system of OBJECT types of a `CatSystem` (forget the
    morphisms): exactly a Milestone-1 `System`. -/
def CatSystem.objSystem (C : CatSystem ι D) : System ι D where
  X := C.A
  tr := C.F
  tr_refl := C.F_refl
  tr_trans := C.F_trans

/-- The OBJECTS of the colimit category: the type-level directed colimit of the
    object families. -/
def CatSystem.Obj (C : CatSystem ι D) : Type _ := Colimit C.objSystem

/-- The canonical inclusion of stage-`i` objects into the colimit's objects. -/
def CatSystem.objIncl (C : CatSystem ι D) (i : ι) (x : C.A i) : C.Obj :=
  incl C.objSystem i x

/-- Inclusions of objects are compatible with the transition functors. -/
theorem CatSystem.objIncl_compat (C : CatSystem ι D) {i j : ι} (hij : D.le i j) (x : C.A i) :
    C.objIncl j (C.F hij x) = C.objIncl i x :=
  incl_compat C.objSystem hij x

end Freyd.Colim
```

## Verify
`lake build Fredy.CatColimit` must exit 0 with **no** error / sorry / unsolved-goals (unused-variable
warnings are fine). Iterate on the code until it builds. Do **not** add any `sorry`. Do **not** touch any
other file. End by printing one line stating whether `lake build Fredy.CatColimit` passed.

Notes if the compiler complains:
- `functF` uses explicit instance arguments `@Functor (A i) (catA i) (A j) (catA j) (F hij)` because the `Cat`
  instances are bundled fields, not global instances — keep this form.
- If `CatSystem.objSystem`'s fields don't line up, recall `System` (in `DirectedColimit.lean`) has fields
  `X, tr, tr_refl, tr_trans` with `tr : ∀ {i j}, D.le i j → X i → X j`.
- `Colimit`, `incl`, `incl_compat` are in namespace `Freyd.Colim` in `DirectedColimit.lean`.
```
