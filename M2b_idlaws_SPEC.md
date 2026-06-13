# M2b identity laws — spec for `Fredy/CatColimit.lean`

Add FOUR theorems just before the final `end Freyd.Colim` in `Fredy/CatColimit.lean`. Then verify
`lake build Fredy.CatColimit` exits 0 with NO `sorry`/`error` (unused-variable warnings OK). Iterate on the
exact proof terms until it compiles. Do NOT add `sorry`. Do NOT touch any other file.

## Context (everything below already exists in the file, namespace `Freyd.Colim`)

Key defs/lemmas you will use (signatures):
- `homCompRaw C hC xp xq xr a f b g : HomColim C hC xp xr` — raw composition; `a : UpperBound D ip iq`,
  `f : C.F a.2.1 xp ⟶ C.F a.2.2 xq`, `b : UpperBound D iq ir`, `g : C.F b.2.1 xq ⟶ C.F b.2.2 xr`.
- `homCompRaw_eq_compAt C hC xp xq xr a f b g e hae hbe : homCompRaw … = compAt C hC xp xq xr a f b g e hae hbe`
  where `hae : D.le a.1 e`, `hbe : D.le b.1 e`.
- `compAt C hC xp xq xr a f b g e hae hbe = homIncl C hC xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩`
  `(homTr C xp xq a ⟨e, D.trans a.2.1 hae, D.trans a.2.2 hae⟩ hae f ≫ homTr C xq xr b ⟨e, D.trans b.2.1 hbe, D.trans b.2.2 hbe⟩ hbe g)`
  (this is `compAt`'s definition — `unfold compAt` to expose it).
- `homIncl C hC xp xq a g : HomColim C hC xp xq` (`a : UpperBound D ip iq`, `g : C.F a.2.1 xp ⟶ C.F a.2.2 xq`).
- `homTr_refl C hC x y a g : homTr C x y a a (D.refl a.1) g = g`.
- `homTr_id C x a b hab : homTr C x x a b hab (Cat.id (C.F a.2.1 x)) = Cat.id (C.F b.2.1 x)`  (`hab : D.le a.1 b.1`).
- `homClassId C hC x : HomColim C hC x x := homIncl C hC x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (C.F (D.refl i) x))`.
- `colimHom C hC p q := HomColim C hC (colimOut C p).2 (colimOut C q).2` (`p q : C.Obj`).
- `colimId C hC p := homClassId C hC (colimOut C p).2`.
- `colimComp C hC m n := Quotient.lift₂ (fun rm rn => homCompRaw C hC … rm.1 rm.2 rn.1 rn.2) (…) m n`.
- `Cat.id_comp f : Cat.id _ ≫ f = f`,  `Cat.comp_id f : f ≫ Cat.id _ = f`.
- `HomColim C hC x y` is `Quotient`-defined; `homIncl … = Quotient.mk … ⟨a, g⟩`. Use `Quotient.ind` to
  reduce a `colimHom` to a representative `⟨a, f⟩`.

IMPORTANT — proof-irrelevance friction: `compAt` at level `e` produces upper bounds like
`⟨e, D.trans a.2.1 hae, …⟩` that are *definitionally equal* to the original `a` (when `e = a.1`,
`hae = a.2.1`) but NOT syntactically equal. So prefer `have e1 : <exact compAt term> = … := homTr_id …`
(let defeq coerce the statement) over `rw [homTr_id]` which may fail to match. Two `homIncl … g` whose
upper bounds are defeq are closed by `rfl`.

## Theorem 1 — `homCompRaw_id_left`
```lean
theorem homCompRaw_id_left (C : CatSystem ι D) (hC : C.Coherent) {ip iq : ι}
    (xp : C.A ip) (xq : C.A iq) (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq) :
    homCompRaw C hC xp xp xq ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (C.F (D.refl ip) xp)) a f
      = homIncl C hC xp xq a f := by
  rw [homCompRaw_eq_compAt C hC xp xp xq ⟨ip, D.refl ip, D.refl ip⟩
        (Cat.id (C.F (D.refl ip) xp)) a f a.1 a.2.1 (D.refl a.1)]
  unfold compAt
  -- The id-side `homTr … (Cat.id …)` equals `Cat.id …` by `homTr_id`.
  -- The f-side `homTr a ⟨a.1,…⟩ (D.refl a.1) f` equals `f` by `homTr_refl` (defeq: ⟨a.1,…⟩ ≡ a).
  -- Then `Cat.id _ ≫ f = f` (`Cat.id_comp`), and the two `homIncl`s have defeq bounds.
  sorry  -- replace: introduce `have e1 := homTr_id …`, `have e2 : … = f := homTr_refl …`,
         -- `rw [e1, e2, Cat.id_comp]`, then `rfl` (or the goal is already closed).
```

## Theorem 2 — `homCompRaw_id_right` (symmetric; identity on the SECOND argument)
```lean
theorem homCompRaw_id_right (C : CatSystem ι D) (hC : C.Coherent) {ip iq : ι}
    (xp : C.A ip) (xq : C.A iq) (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq) :
    homCompRaw C hC xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩ (Cat.id (C.F (D.refl iq) xq))
      = homIncl C hC xp xq a f := by
  rw [homCompRaw_eq_compAt C hC xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩
        (Cat.id (C.F (D.refl iq) xq)) a.1 (D.refl a.1) a.2.2]
  unfold compAt
  -- f-side `homTr a ⟨a.1,…⟩ (D.refl a.1) f = f` (homTr_refl); id-side → `Cat.id` (homTr_id);
  -- then `f ≫ Cat.id _ = f` (Cat.comp_id); defeq bounds.
  sorry
```

## Theorem 3 — `colimComp_id_left`
```lean
theorem colimComp_id_left (C : CatSystem ι D) (hC : C.Coherent) {p q : C.Obj}
    (m : colimHom C hC p q) : colimComp C hC (colimId C hC p) m = m := by
  induction m using Quotient.ind with
  | _ rm =>
    obtain ⟨a, f⟩ := rm
    -- `colimComp (colimId p) ⟦(a,f)⟧` reduces (defeq, Quotient.lift₂ β-rule) to
    -- `homCompRaw … ⟨ip,refl,refl⟩ (Cat.id …) a f`, and `m = ⟦(a,f)⟧ = homIncl … a f`.
    exact homCompRaw_id_left C hC (colimOut C p).2 (colimOut C q).2 a f
```
(If `exact` fails on a defeq mismatch, try `show homCompRaw C hC (colimOut C p).2 (colimOut C p).2
(colimOut C q).2 ⟨(colimOut C p).1, D.refl _, D.refl _⟩ (Cat.id _) a f = _ ; exact homCompRaw_id_left …`,
or `change … ; exact …`.)

## Theorem 4 — `colimComp_id_right`
```lean
theorem colimComp_id_right (C : CatSystem ι D) (hC : C.Coherent) {p q : C.Obj}
    (m : colimHom C hC p q) : colimComp C hC m (colimId C hC q) = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm
            exact homCompRaw_id_right C hC (colimOut C p).2 (colimOut C q).2 a f
```

## Verify
`lake build Fredy.CatColimit` → exit 0, no `sorry`/`error`. Print one line stating pass/fail and
`grep -c sorry Fredy/CatColimit.lean` (should be 0).
