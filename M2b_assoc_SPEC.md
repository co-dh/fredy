# M2b associativity + Cat instance — spec for `Fredy/CatColimit.lean`

Add, just before the final `end Freyd.Colim`: a proof of `colimComp_assoc`, then the `Cat` instance on
`CatSystem.Obj`. Verify `lake build Fredy.CatColimit` exits 0, NO `sorry`/`error`. Iterate. Don't touch other
files. This is the hardest proof in the file — budget many compiler iterations.

## Available (all already in the file, namespace `Freyd.Colim`)
- `homCompRaw C hC xp xq xr a f b g : HomColim C hC xp xr` (raw composition).
- `homCompRaw_eq_compAt C hC xp xq xr a f b g e hae hbe : homCompRaw … = compAt … e hae hbe`
  (`hae : D.le a.1 e`, `hbe : D.le b.1 e`). `compAt … e hae hbe` unfolds to
  `homIncl C hC xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩ (homTr C xp xq a ⟨e,…⟩ hae f ≫ homTr C xq xr b ⟨e,…⟩ hbe g)`.
- `homTr_comp C xp xq xr hpc hqc hrc hcd f g : homTr C xp xr ⟨c,hpc,hrc⟩ ⟨d,…⟩ hcd (f ≫ g)`
  `= homTr C xp xq ⟨c,hpc,hqc⟩ ⟨d,…⟩ hcd f ≫ homTr C xq xr ⟨c,hqc,hrc⟩ ⟨d,…⟩ hcd g`.
- `homTr_trans C hC x y a b c hab hbc g : homTr C x y a c (D.trans hab hbc) g = homTr C x y b c hbc (homTr C x y a b hab g)`.
- `compAt_indep C hC xp xq xr a f b g hae₁ hbe₁ hae₂ hbe₂ : compAt … e₁ … = compAt … e₂ …` (bound-independence).
- `homIncl`, `colimComp`, `colimHom`, `colimId`, `colimOut`, `colimComp_id_left`, `colimComp_id_right`.
- `Cat.assoc`, `Cat.id`, `Cat.id_comp`, `Cat.comp_id`.
- `Quotient.ind` to reduce a `colimHom` to a representative `⟨a,f⟩`.
- Proof-irrelevance: upper bounds `⟨e, p, q⟩` with `D.le`-proofs `p q` that prove the same thing are defeq;
  prefer `have : <exact term> = … := lemma …` over `rw` when matching fails; `rfl` closes defeq goals.

## Strategy for `colimComp_assoc`
Reduce both sides to `homIncl … ⟨M,…⟩ (fM ≫ gM ≫ hM)` at one common level `M`, then use `Cat.assoc`.

Key facts (prove inline or as private lemmas):
1. `colimComp ⟦(a,f)⟧ ⟦(b,g)⟧ = homCompRaw C hC xp xq xr a f b g` (definitional: `Quotient.lift₂` β-rule;
   `colimComp` is `Quotient.lift₂ …`). Likewise the outer composite: since `homCompRaw …` is a `homIncl`
   (= `Quotient.mk`), `colimComp (homCompRaw … a f b g) ⟦(c,h)⟧ = homCompRaw C hC xp xr xs ⟨e₁,…⟩ (F₁ ≫ G₁) c h`
   where `⟨e₁,…⟩` and `F₁ ≫ G₁` come from `homCompRaw … a f b g`'s `compAt` form.
2. `homCompRaw_eq_compAt` to push everything to a big common `M`, then `homTr_comp` to split
   `homTr ⟨e₁⟩→M (F₁ ≫ G₁)` into `homTr ⟨e₁⟩→M F₁ ≫ homTr ⟨e₁⟩→M G₁`, then `homTr_trans` to merge
   `homTr ⟨e₁⟩→M (homTr a→e₁ f) = homTr a→M f`.  Net: LHS `= homIncl … ⟨M⟩ ((fM ≫ gM) ≫ hM)`.
3. Symmetrically RHS `= homIncl … ⟨M'⟩ (fM' ≫ (gM' ≫ hM'))`; use `compAt_indep` to take `M = M'`.
4. `Cat.assoc fM gM hM : (fM ≫ gM) ≫ hM = fM ≫ (gM ≫ hM)` closes it.

```lean
theorem colimComp_assoc (C : CatSystem ι D) (hC : C.Coherent) {p q r s : C.Obj}
    (m : colimHom C hC p q) (n : colimHom C hC q r) (k : colimHom C hC r s) :
    colimComp C hC (colimComp C hC m n) k = colimComp C hC m (colimComp C hC n k) := by
  induction m using Quotient.ind with
  | _ rm => induction n using Quotient.ind with
    | _ rn => induction k using Quotient.ind with
      | _ rk =>
        obtain ⟨a, f⟩ := rm; obtain ⟨b, g⟩ := rn; obtain ⟨c, h⟩ := rk
        sorry  -- carry out steps 1–4
```
If the triple `Quotient.ind` is awkward, use `refine Quotient.ind (fun rm => ?_) m` nested, or
`Quotient.inductionOn₃ m n k (fun rm rn rk => ?_)` then destructure.

## The `Cat` instance
```lean
noncomputable instance colimitCat (C : CatSystem ι D) (hC : C.Coherent) : Cat.{?} (C.Obj) where
  Hom p q := colimHom C hC p q
  id p := colimId C hC p
  comp m n := colimComp C hC m n
  id_comp := colimComp_id_left C hC
  comp_id := colimComp_id_right C hC
  assoc := colimComp_assoc C hC
```
Pick the right `Cat` universe (check `Cat` in `Fredy/S1_1.lean`; `colimHom` lands in the same universe as the
`C.A i` hom-sets). The fields `id_comp`/`comp_id`/`assoc` may need their arguments reordered/eta-expanded to
match `Cat`'s field signatures — adjust as the compiler requires.

## Verify
`lake build Fredy.CatColimit` → exit 0, no `sorry`/`error`. Print pass/fail and `grep -c sorry Fredy/CatColimit.lean`.
If `colimComp_assoc` proves too hard to finish, STILL deliver everything else compiling and leave ONLY
`colimComp_assoc` as `sorry` (clearly the single remaining gap) plus the `Cat` instance using it — and say so.
