# M3b — binary products of the colimit category. Add to `Fredy/CatColimitRegular.lean`.

Goal: if each stage `C.A i` has binary products and the transitions **preserve** them (cast-free: the image of
a stage product cone is again a product, stated by its universal property), the colimit category `C.Obj` has
binary products. Verify `lake build Fredy.CatColimitRegular` exits 0. Don't touch other files.

This is HARD (two objects at a common stage + germ-level projections + universal property). Attempt it; if a
field is intractable after real effort, leave THAT field (e.g. `pair_uniq`) as `sorry` and report exactly which.

## Available (see existing `colimitHasTerminal` in this file for the pattern)
- `C.objIncl`, `colimOut`, `colimOut_spec`, `colimHom`, `HomColim`, `homIncl`, `homTr`, `homTr_refl`,
  `homTr_trans`, `colimComp`, `homCompRaw`, `homCompRaw_eq_compAt`, `castHom`, `colimitCat`,
  `colimitHasTerminal`, `Quotient.exact`, `Quotient.sound`, `Quotient.ind`.
- `HasBinaryProducts 𝒜` (`Fredy/S1_42.lean`): fields `prod : 𝒜→𝒜→𝒜`, `fst : prod A B ⟶ A`, `snd : prod A B ⟶ B`,
  `pair : (X⟶A)→(X⟶B)→(X⟶prod A B)`, `fst_pair`, `snd_pair`, `pair_uniq`.

## Hypotheses (cast-free preservation via universal property of the image cone)
```lean
(hp : ∀ i, HasBinaryProducts (C.A i))
(hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
    -- the image cone (F(prod a b), F fst, F snd) is monic-jointly: distinguished by the two projections
    u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
    u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
(hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
    ∃ r : z ⟶ C.F hij ((hp i).prod a b),
      r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
```
(Together these say the image of the product cone is a product of `F a, F b`. Cast-free.)

## Construction of `@HasBinaryProducts C.Obj (colimitCat C hC)`
For `X Y : C.Obj`: let `iX := (colimOut C X).1`, `x := (colimOut C X).2`, `iY := (colimOut C Y).1`,
`y := (colimOut C Y).2`. Pick `k := Classical.choose (D.bound iX iY)` with `hXk : iX ≤ k`, `hYk : iY ≤ k`.
Let `xk := C.F hXk x`, `yk := C.F hYk y`. Define
- `prod X Y := C.objIncl k ((hp k).prod xk yk)`.
- `fst : colimHom (prod X Y) X`: the germ at level `k` of `(hp k).fst : (hp k).prod xk yk ⟶ xk` — but its
  codomain must match `(colimOut (prod X Y)).2` and `(colimOut X).2`; construct via `homIncl` between the
  chosen reps, transporting along `colimOut_spec`/`Quotient.exact` exactly as `colimitHasTerminal.trm` did
  (push to a common level where both reps agree with the stage objects).
- `snd` analogously.
- `pair (f : colimHom Z X)(g : colimHom Z Y) : colimHom Z (prod X Y)`: reduce `f,g` to germ reps, push to a
  common level with `k`, apply the STAGE `(hp _).pair`, include. Well-defined by `hpres`/`hpres_pair`.
- `fst_pair`, `snd_pair`: stage `fst_pair`/`snd_pair` pushed through `colimComp`.
- `pair_uniq`: the joint-monic `hpres` pushed to a common level, then `Quotient.sound`.

NOTE: the projections/pair must land between the CHOSEN representatives (`colimHom` uses `colimOut`), so each
needs a `colimOut_spec` + `Quotient.exact` transport like `colimitHasTerminal.trm`. This is the crux friction.

## Verify
`lake build Fredy.CatColimitRegular` → exit 0. Print pass/fail, `grep -n sorry Fredy/CatColimitRegular.lean`,
and state which fields (if any) are `sorry`.
