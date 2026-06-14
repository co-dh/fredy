# M3a — terminal object of the colimit category. New file `Fredy/CatColimitRegular.lean`.

Goal: if each stage `C.A i` has a terminal and the transitions **preserve** it, then the colimit category
`C.Obj` (instance `colimitCat`) has a terminal object. Verify `lake build Fredy.CatColimitRegular` exits 0,
no `sorry`/`error`. Don't touch other files.

## File header
```lean
import Fredy.CatColimit
import Fredy.S1_42   -- HasTerminal
open Freyd
namespace Freyd.Colim
universe u w
variable {ι : Type u} {D : Directed ι}
```

## Available (from CatColimit.lean / DirectedColimit.lean / S1_42, namespace `Freyd.Colim`/`Freyd`)
- `CatSystem`, `C.Coherent`, `C.A i`, `C.F hij`, `C.functF hij`, `C.F_refl`, `C.F_trans`.
- `C.Obj`, `C.objIncl i x : C.Obj`, `C.objIncl_compat`, `colimOut C p : Σ i, C.A i`,
  `colimOut_spec C p : C.objIncl (colimOut C p).1 (colimOut C p).2 = p`.
- `colimHom C hC p q := HomColim C hC (colimOut C p).2 (colimOut C q).2`.
- `HomColim C hC x y := Colimit (homSystem C hC x y)`; `homIncl C hC x y ⟨k, hjk, hik⟩ g : HomColim C hC x y`
  where `g : C.F hjk x ⟶ C.F hik y` (the morphism at upper bound `⟨k, hjk, hik⟩ : UpperBound D i j`).
- `homIncl_compat`, `homTr`, `castHom`, `castHom_id`, `colimitCat : Cat C.Obj`.
- `HasTerminal 𝒜` (`Fredy/S1_42.lean`): fields `one : 𝒜`, `trm : (X : 𝒜) → X ⟶ one`,
  `uniq : ∀ {X} (f g : X ⟶ one), f = g`.
- `Quotient.exact : Quotient.mk _ a = Quotient.mk _ b → a ≈ b`. Note `objIncl i x = Quotient.mk _ ⟨i,x⟩` and
  `homIncl … = Quotient.mk _ ⟨ub, g⟩`. The germ relation `Rel S ⟨a,fa⟩ ⟨b,fb⟩` unfolds to
  `∃ k (hak : D.le a.1 k.1)(hbk : D.le b.1 k.1), homTr … a k hak fa = homTr … b k hbk fb` for hom-systems, and
  `∃ k (hik : D.le a.1 k)(hjk : D.le b.1 k), C.F hik a.2 = C.F hjk b.2` for `objSystem` (objects).

## Theorem
```lean
noncomputable def colimitHasTerminal (C : CatSystem ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one) :
    HasTerminal C.Obj := ...
```

## Construction
Let `i₀ := Classical.choice hne` (or `hne.some`). Terminal object `one := C.objIncl i₀ (ht i₀).one`.

Helper — pushing the preserved terminal: for `hjk : D.le j k`, `C.F hjk (ht j).one = (ht k).one` is `hpres`.
By `C.F_trans` + `hpres`, for any chain the image of a stage-terminal is the terminal at the top level.

For `trm (X : C.Obj) : colimHom C hC X one` (i.e. `HomColim C hC (colimOut C X).2 (colimOut C one).2`):
- let `jX := (colimOut C X).1`, `xX := (colimOut C X).2`, `io := (colimOut C one).1`, `o := (colimOut C one).2`.
- From `colimOut_spec C one : objIncl io o = one = objIncl i₀ (ht i₀).one`, `Quotient.exact` gives
  `∃ k₀ (hi : D.le io k₀)(hj : D.le i₀ k₀), C.F hi o = C.F hj (ht i₀).one`. With `hpres`, `C.F hj (ht i₀).one = (ht k₀).one`,
  so `C.F hi o = (ht k₀).one` — `o` becomes the terminal at level `k₀`.
- pick `k` a common bound of `jX` and `k₀` (`D.bound jX k₀`), so `hjXk : jX ≤ k`, `hk₀k : k₀ ≤ k`, and `hiok : io ≤ k`
  (= `D.trans hi hk₀k`). At `k`: `C.F hiok o = C.F hk₀k (C.F hi o) = C.F hk₀k (ht k₀).one = (ht k).one`
  (`C.F_trans` then `hpres`). Call this `hok : C.F hiok o = (ht k).one`.
- the morphism `m : C.F hjXk xX ⟶ C.F hiok o` is the terminal map re-typed:
  `m := castHom rfl hok.symm ((ht k).trm (C.F hjXk xX))`  (`(ht k).trm _ : C.F hjXk xX ⟶ (ht k).one`).
- `trm X := homIncl C hC xX o ⟨k, hjXk, hiok⟩ m`.

For `uniq {X} (f g : colimHom C hC X one)`: reduce `f, g` by `Quotient.ind` to germs `homIncl … ⟨a, fa⟩`,
`homIncl … ⟨b, gb⟩`. Show equal via `Quotient.sound`: push both to a common level `k ≥ a.1, b.1, k₀` where the
targets `C.F _ o = (ht k).one` are terminal, so `homTr`-pushed `fa` and `gb` are both maps into the terminal
`(ht k).one` (after the cast `C.F _ o = (ht k).one`), hence equal by `(ht k).uniq`. The germ relation then holds.

## Verify
`lake build Fredy.CatColimitRegular` → exit 0, no `sorry`/`error`. Print pass/fail + `grep -c sorry Fredy/CatColimitRegular.lean`.
If `uniq` proves too hard, leave ONLY `uniq` as `sorry` (everything else compiling) and say so.
```
