# Simplification instructions for the `S1_*.lean` series

Scope: `Freyd/S1_1`, `S1_41`, `S1_42`, `S1_44`, `S1_45`, `S1_51`, `S1_52`, `S1_53`.
Out of scope: `S1_18.lean` (work in progress), `525.lean`, `Tau.lean`, `Basic.lean`.

Build a single file with `lake env lean Freyd/<name>.lean` (exit 0 = clean). After any
cross-file change, rebuild the changed file **and every file that imports it**. The import
DAG is: `S1_1` → {`S1_41`, `S1_44`}; `S1_41` → `S1_42`, `S1_51`, `S1_18`; `S1_42` →
`S1_45`, `S1_52`, `S1_53`; `S1_45`/`S1_51` → `S1_52`, `S1_53`; `S1_44` → `S1_53`.

Order matters: do task **A** (cross-cutting) and **B** (`mono_of_retraction`, spans
`S1_41`+`S1_42`) before the per-file items. Don't parallelize across files in separate
worktrees — the shared deps will collide. One worktree, sequential.

Verified items are marked **[verified]** (I compiled them). Others are marked
**[proposed]** — apply, then confirm on build; revert if they don't land.

---

## A. Cross-cutting — drop the redundant `open Freyd` [verified]

Every file does `open Freyd` *before* `namespace Freyd`. Nothing between those two lines
references a `Freyd.*` name (the only `variable` there mentions `Cat`, which is at root).
Once inside `namespace Freyd`, all sibling and imported `Freyd.*` names already resolve, so
the `open` is dead.

For **each** of the eight files: delete the standalone `open Freyd` line. Rebuild.

(Leave `set_option linter.unusedSectionVars false` alone — it's load-bearing in the files
that share a `variable [ht] [hp] [hpull]` line, see note in §S1_45/§S1_52.)

---

## B. Add `mono_of_retraction`, collapse `diag_mono` [verified]

A "split mono is monic" lemma is currently re-proved inline inside `S1_42.diag_mono`
(6-line tactic block) and again, verbatim, in `525.lean`. Lift it to `S1_41` (it's a §1.41
fact) and reuse.

**B1 — in `S1_41.lean`**, after `isIso_comp`, add:

```lean
/-- A split mono is monic: a map with a retraction is left-cancellable. -/
theorem mono_of_retraction {X Y : 𝒞} (m : X ⟶ Y) (r : Y ⟶ X)
    (hr : m ≫ r = Cat.id X) : Mono m := by
  intro W g h hgh
  calc g = g ≫ m ≫ r   := by rw [hr, Cat.comp_id]
    _    = (g ≫ m) ≫ r := (Cat.assoc _ _ _).symm
    _    = (h ≫ m) ≫ r := by rw [hgh]
    _    = h ≫ m ≫ r   := Cat.assoc _ _ _
    _    = h           := by rw [hr, Cat.comp_id]
```

**B2 — in `S1_42.lean`**, replace the whole `diag_mono` proof (the `by intro W f g h …`
block) with one line:

```lean
theorem diag_mono (A : 𝒞) : Mono (diag A) :=
  mono_of_retraction (diag A) fst (diag_fst A)
```

Rebuild `S1_42` and its dependents (`S1_45`, `S1_52`, `S1_53`).

---

## S1_1.lean — remove dead trailing lines [verified by inspection]

`Cat`, the `⟶`/`≫` infix, all live at **root** (before `namespace Freyd`). The file's last
three meaningful lines are dead:
- `universe v u` (line 10) is used only by…
- `variable {𝒞 : Type u} [Cat.{v} 𝒞]` (line 24), which has no declaration after it, and
- `namespace Freyd` (line 26) opens an empty namespace (nothing follows; importers open their
  own `namespace Freyd`).

Delete lines 24 and 26. Then delete `universe v u` (line 10) only if nothing else uses it
(it doesn't — `class Cat.{w,z}` binds its own universes). Rebuild `S1_1` and `S1_41`/`S1_44`.

---

## S1_41.lean

- Apply **A** (drop `open Freyd`) and **B1** (add `mono_of_retraction`).
- Nothing else; `isIso_comp` is already tight.

---

## S1_42.lean

- Apply **A** and **B2**.
- **[proposed, optional, low priority] Spurious `HasTerminal` dep.** `diag_fst`, `diag_snd`,
  `diag_mono` each carry an unused `[ht : HasTerminal 𝒞]` in their signature — instance-
  implicit section vars are greedily included in *theorems* once their deps are in scope, so
  the file-level `variable [ht : HasTerminal 𝒞]` (line 27) leaks in even though the diagonal
  is a pure product notion (`diag`, a `def`, correctly omits it). Harmless here (every model
  in this dev has all three instances), so only worth doing for hygiene. Fix by prefixing each
  of the three diagonal **theorems** with `omit ht in`, e.g. `omit ht in theorem diag_fst …`.
  Verify the three signatures lose `HasTerminal` via `#check @Freyd.diag_fst`.

---

## S1_44.lean

- Apply **A**.
- **[proposed, optional]** Tag `OverHom.ext` with `@[ext]` (it already has the right shape:
  one hypothesis `a.f = b.f`). Keeps the lemma usable as today *and* enables the `ext` tactic.
  Purely additive; skip if it doesn't simplify any call site (`S1_53` uses `OverHom.ext hpq`
  directly, which still works).
- Otherwise the file is minimal — leave it.

---

## S1_45.lean

- Apply **A**.
- **[proposed] Shorten the `mpr` calc in `monic_iff_kp_diag_iso`** (lines ~99–109). The single
  zigzag `calc x₁ = … = x₂` routes through `t` and contains a redundant `t = t ≫ Cat.id A`
  round-trip in the middle. Replace with two short `have`s and a rewrite:
  ```lean
  have hx₁ : x₁ = t := by
    rw [kp_lift_p₁ x₁ x₂ h, ht, Cat.assoc, kp_diag_p₁, Cat.comp_id]
  have hx₂ : x₂ = t := by
    rw [kp_lift_p₂ x₁ x₂ h, ht, Cat.assoc, kp_diag_p₂, Cat.comp_id]
  rw [hx₁, hx₂]
  ```
  (`ht : hpair = t ≫ kp_diag` is already in scope; `t := hpair ≫ inv`. Confirm the `rw` chains
  close — if a step misfires, fall back to per-step `calc`.) Net: ~11 lines → ~5.
- **[deferred — do NOT do without owner sign-off] Make `f` explicit** in `kp₁`/`kp₂`/`kp_diag`
  /`kp_sq`/… to kill the ~20 `(f:=f)` / `(f:=term S)` annotations across `S1_45`+`S1_52`. This
  was considered earlier and intentionally not taken: it changes the public arity of the kernel-
  pair API and ripples through every call site in `S1_52`/`S1_53`. Big, coupled, behavior-
  neutral churn — leave it unless the owner asks.
- Keep `set_option linter.unusedSectionVars false`: the shared `variable {A B X} {f}` plus
  `variable [ht][hp][hpull]` lines mean most lemmas legitimately use only a subset.

---

## S1_51.lean

- Apply **A**.
- Two-declaration file (`Cover`, `monic_cover_iso`); nothing else to simplify. (Note it
  duplicates `525.lean`'s `isIso_of_mono_cover` up to argument order — out of scope here.)

---

## S1_52.lean

- Apply **A**.
- **[verified] DRY the `Capital` hypothesis + clean the result type** of
  `capital_implies_one_projective`. It currently restates `Capital`'s definition inline and
  returns the awkward `∃ (_ : one ⟶ A), True`. Change the signature to:
  ```lean
  theorem capital_implies_one_projective
      (hcap : Capital (𝒞 := 𝒞)) (A : 𝒞) (hws : WellSupported A) :
      Nonempty (one ⟶ A) := by
  ```
  (`Capital` unfolds definitionally, so `hcap (prod A A) hwsAA` still typechecks.) Then fix the
  two witness sites: the iso branch `exact ⟨inv, trivial⟩` → `exact ⟨inv⟩`, and the final
  `exact ⟨x ≫ fst, trivial⟩` → `exact ⟨x ≫ fst⟩`. Rebuild `S1_52` (and `S1_53` — unaffected,
  but confirm). Matches the `Nonempty` convention used in `525.lean`.
- **[proposed] Shrink the iso round-trip lemmas with `simp`.** The four `kpProd*_fst/snd`
  lemmas are `@[simp]`, so the `hu_fst`/`hu_snd` helpers in `kpProdIso_inv` (and the analogous
  `rw` chains in `kpProdInv_iso`, `kp_diag_prod`) should collapse, e.g.
  `have hu_fst : u ≫ kp₁ (f:=term S) = kp₁ (f:=term S) := by simp [u, Cat.assoc]`.
  Try per lemma; keep the explicit `rw` where `simp` fails to close or loops.

---

## S1_53.lean

- Apply **A**.
- File is already tight (`pair_prod_map`, `prod_pullback`; `h_sq` already uses `simp`). No
  structural change recommended. Optional: in `prod_pullback`, the `lift_fst`/`lift_snd`/
  `lift_uniq` obligations may shrink with `simp [p₁, p₂]` given the `@[simp]` product lemmas —
  try, keep only if it compiles and is shorter.

---

## Final check

After all edits, rebuild the whole series in dependency order:

```
printf '%s\n' S1_1 S1_41 S1_42 S1_44 S1_45 S1_51 S1_52 S1_53 \
  | xargs -I {} sh -c 'echo "=== {} ==="; lake env lean Freyd/{}.lean 2>&1 | head -8'
```

All eight must exit 0 with no errors. Then confirm the axiom footprint is unchanged:
`monic_iff_kp_diag_iso` should depend on **no** axioms, and
`capital_implies_one_projective` on `[propext, Classical.choice, Quot.sound]` only — check
with `lean_verify` / `#print axioms`.
```
