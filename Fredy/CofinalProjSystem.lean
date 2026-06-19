/-
  §1.547 — a COFINAL strict `ProjSystem` over the finite-SUBSET order.

  ════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS — escaping the countability ceiling of the prefix-ordered index.
  ════════════════════════════════════════════════════════════════════════════════════════════

  The §1.547 uniform successor (`UniformCapStep.lean`) is built over a `ProjSystem ι D S` — the
  directed system of finite-product projections `∏U' ⟶ ∏U` of well-supported objects.  Its
  `proj_refl`/`proj_trans` must be ON-THE-NOSE.  The existing `WSChain`/`projSystemOfWS` index
  sidesteps the strict-coherence wall by ordering by the APPEND/PREFIX order and taking the
  projection to be the suffix forget `catForget`.  But prefix-monotone FINITE lists cannot grow
  past `ω`: a prefix chain reaches only the objects appearing in *some finite prefix*, so the index
  is cofinal over at most a COUNTABLE suffix of the well-supported objects (the ceiling documented
  at `Inflation.lean:1474-1506` and `CofinalOrdChain.lean:33-35`).  For cofinality over an
  UNCOUNTABLE carrier the successor must point EVERY well-supported object in one rung; the prefix
  index cannot.

  ════════════════════════════════════════════════════════════════════════════════════════════
  THE FIX — index by ALL finite sets of well-supported objects (SUBSET order, not prefix).
  ════════════════════════════════════════════════════════════════════════════════════════════

  Over the subset order every well-supported `B` is reached by the singleton index `{B}`, so the
  index is COFINAL with no countability restriction.  The price (RelativeCapitalization.lean's
  `ListProjFamily` "wall") is that the projection `∏U' ⟶ ∏U` for `U ⊆ U'` needs POSITIONAL
  element-matching — barred without object equality.  We pay it with `Classical.decEq S` (already in
  the §1.543 axiom set), exactly Option (a) of the brief:

    * model a "finite set of objects" as a NODUP `List S` of well-supported objects (the index
      `WSList`), ordered by `⊆`;
    * `factorProj U B (B ∈ U)` selects the U-factor at `B` by `DecidableEq` (first occurrence);
    * `selectProj U V (V ⊆ U) : ∏U ⟶ ∏V` assembles the V-factor projections by `pair`.

  The KEYSTONE is that `proj_refl`/`proj_trans` are STRICT (on-the-nose), via the recovery lemma
  `selectProj_factor : selectProj U V h ≫ factorProj V B hB = factorProj U B (h B hB)` plus the
  joint-monicity of `listProd` in its factor projections (`listProd_hom_ext`, needs NODUP).  No iso,
  no `sorry`.

  `Classical.decEq` IS permitted here (§1.543 exception); every other file stays mathlib-free.  No
  `axiom`, no `: True`, no statement-weakening; the whole file is sorry-free.

  ── RE-THREADING `uniformStep`/`FibreDensity` (the NEXT step, deliberately NOT done in this file) ──
  This file builds and verifies the index in ISOLATION (the brief: report before re-threading).
  `cofinalProjSystem : ProjSystem (WSList S) (wsDirected S) S` is a drop-in for the `projSystemOfWS`
  consumed by `UniformCapStep.lean`'s `uniformStepTarget_preRegular`/`uniformStep`; the base index is
  `⟨[], …⟩` (stage `[]`, fibre `S/1`).  Re-threading replaces `WSChain` by `WSCover` and
  `projSystemOfWS`/`projSystemOfWS_cover` by `cofinalProjSystem`/`cofinalProjSystem_cover`; the
  `terminalSliceObj`/`stageInclNil`/preservation assembly is unchanged (it only uses `pr base = 1` and
  the projection cover, both supplied here).  The COFINALITY field (`WSCover.cofinal`) is the new input
  `FibreDensity` consumes: every well-supported `B` is reached at the singleton index `{B}`.
-/
import Fredy.RelativeCapitalization
import Fredy.SliceRegular
import Fredy.Capitalization
import Fredy.CapitalizationLaxColimit
import Fredy.WellOrdering

open Freyd
open Freyd.Colim
open Freyd.LaxColim

-- Many engine lemmas hold under fewer instances than the enclosing section carries (e.g. the
-- product-only `pair_precomp` lives in a section that also has `[DecidableEq]`/`[HasEqualizers]` for
-- its neighbours); the `unusedSectionVars` linter flags those.  Disable it file-wide — restructuring
-- into micro-sections would fragment the engine for no semantic gain.
set_option linter.unusedSectionVars false

namespace Freyd.CofinalProj

universe u

/-! ## Phase 0 — mathlib-free `dedup` (for the directed `bound`)

  The repo is mathlib-free (`List.dedup` lives in mathlib), so we develop the small dedup we need:
  `dedup l` keeps first occurrences, is `Nodup`, and has the same members as `l`.  Used to make the
  append of two nodup lists nodup, so the subset index has a `bound`. -/

variable {𝒞 : Type u} [DecidableEq 𝒞]

/-- Remove duplicate occurrences (keep the first).  Mathlib-free. -/
def dedup : List 𝒞 → List 𝒞
  | [] => []
  | a :: l => if a ∈ dedup l then dedup l else a :: dedup l

theorem mem_dedup {l : List 𝒞} {a : 𝒞} : a ∈ dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons b l ih =>
    simp only [dedup, List.mem_cons]
    by_cases h : b ∈ dedup l
    · rw [if_pos h, ih]
      exact ⟨fun ha => Or.inr ha, fun hh => hh.elim (fun e => ih.1 (e ▸ h)) id⟩
    · rw [if_neg h, List.mem_cons, ih]

theorem dedup_nodup (l : List 𝒞) : (dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    simp only [dedup]
    by_cases h : a ∈ dedup l
    · rw [if_pos h]; exact ih
    · rw [if_neg h]; exact List.nodup_cons.2 ⟨h, ih⟩

/-! ## Phase 1 — the per-factor projection `factorProj` and the assembled projection `selectProj` -/

section Engine

variable [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-- The factor projection `∏U ⟶ B` at the first occurrence of `B` in `U` (head ⟹ `fst`; otherwise
    `snd` then recurse).  Positional indexing is forced (`B ∈ U` is a `Prop`, can't large-eliminate),
    so we read off the position by `DecidableEq`. -/
noncomputable def factorProj : ∀ (U : List 𝒞) (B : 𝒞), B ∈ U → (listProd (𝒞 := 𝒞) U ⟶ B)
  | C :: U', B, h =>
    if hCB : C = B then (hCB ▸ (fst : prod C (listProd U') ⟶ C))
    else (snd : prod C (listProd U') ⟶ listProd U') ≫ factorProj U' B
      ((List.mem_cons.1 h).resolve_left (fun e => hCB e.symm))
  | [], _, h => absurd h (by simp)

/-- `factorProj` at a head match is `fst`. -/
theorem factorProj_cons_head {C : 𝒞} {U' : List 𝒞} (hB : C ∈ C :: U') :
    factorProj (C :: U') C hB = (fst : prod C (listProd U') ⟶ C) := by
  rw [factorProj]; simp

/-- `factorProj` past a non-matching head is `snd` then recurse. -/
theorem factorProj_cons_ne {C B : 𝒞} {U' : List 𝒞} (hB : B ∈ C :: U') (hne : C ≠ B)
    (hB' : B ∈ U') :
    factorProj (C :: U') B hB
      = (snd : prod C (listProd U') ⟶ listProd U') ≫ factorProj U' B hB' := by
  rw [factorProj]; simp only [hne, dif_neg, not_false_iff]

/-- **`listProd` is jointly monic in its factor projections** (NODUP index).  Two maps into `∏U`
    agreeing on every `factorProj` are equal — the engine that makes `proj_refl`/`proj_trans` strict.
    NODUP is essential: a duplicate factor is reached by `factorProj` only at its first occurrence,
    leaving the later copy unconstrained, so this is FALSE without `Nodup`. -/
theorem listProd_hom_ext : ∀ {U : List 𝒞}, U.Nodup → ∀ {X : 𝒞} (p q : X ⟶ listProd (𝒞 := 𝒞) U)
    (_ : ∀ (B : 𝒞) (hB : B ∈ U), p ≫ factorProj U B hB = q ≫ factorProj U B hB), p = q
  | [], _, _, p, q, _ => term_uniq p q
  | C :: U', hnd, _, p, q, h => by
    apply fst_snd_jointly_monic
    · have hh := h C List.mem_cons_self; rwa [factorProj_cons_head] at hh
    · apply listProd_hom_ext (List.nodup_cons.1 hnd).2
      intro B hB
      have hCB : C ≠ B := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hB)
      have hh := h B (List.mem_cons.2 (Or.inr hB))
      rw [factorProj_cons_ne (List.mem_cons.2 (Or.inr hB)) hCB hB, ← Cat.assoc, ← Cat.assoc] at hh
      exact hh

/-- The assembled projection `∏U ⟶ ∏V` for `V ⊆ U`: `pair` the V-factor projections (recursion on
    `V`); `selectProj U [] = term (∏U)`. -/
noncomputable def selectProj (U : List 𝒞) : ∀ (V : List 𝒞), (∀ B ∈ V, B ∈ U) →
    (listProd (𝒞 := 𝒞) U ⟶ listProd (𝒞 := 𝒞) V)
  | [], _ => (term (listProd (𝒞 := 𝒞) U) : _ ⟶ listProd (𝒞 := 𝒞) [])
  | C :: V', h =>
    pair (factorProj U C (h C List.mem_cons_self))
         (selectProj U V' (fun B hB => h B (List.mem_cons.2 (Or.inr hB))))

/-- `g ≫ pair a b = pair (g ≫ a) (g ≫ b)`. -/
theorem pair_precomp {X Y A B : 𝒞} (g : X ⟶ Y) (a : Y ⟶ A) (b : Y ⟶ B) :
    g ≫ pair a b = pair (g ≫ a) (g ≫ b) :=
  pair_uniq (g ≫ a) (g ≫ b) (g ≫ pair a b)
    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- **Recovery — `selectProj` followed by a V-factor projection IS the U-factor projection.**  The
    keystone strict-coherence fact: positional selection composes.  By construction of `selectProj`
    (`fst_pair`/`snd_pair`). -/
theorem selectProj_factor (U : List 𝒞) :
    ∀ (V : List 𝒞) (h : ∀ B ∈ V, B ∈ U) (B : 𝒞) (hB : B ∈ V),
      selectProj U V h ≫ factorProj V B hB = factorProj U B (h B hB)
  | [], _, _, hB => absurd hB (by simp)
  | C :: V', h, B, hB => by
    rw [selectProj]
    by_cases hCB : C = B
    · subst hCB; rw [factorProj_cons_head, fst_pair]
    · have hB' : B ∈ V' := (List.mem_cons.1 hB).resolve_left (fun e => hCB e.symm)
      rw [factorProj_cons_ne hB hCB hB', ← Cat.assoc, snd_pair]
      exact selectProj_factor U V' _ B hB'

/-! ## Phase 2 — the STRICT coherence laws (the keystone)

  `selectProj_refl`/`selectProj_trans` are ON-THE-NOSE equalities, proved by `listProd_hom_ext` from
  the recovery lemma.  This is the content the brief calls for: the subset index DOES admit a strict
  `proj_trans` (with `DecidableEq` + nodup). -/

/-- **STRICT unit** — `selectProj` over the reflexive inclusion is the identity. -/
theorem selectProj_refl {U : List 𝒞} (hnd : U.Nodup) (h : ∀ B ∈ U, B ∈ U) :
    selectProj U U h = Cat.id (listProd (𝒞 := 𝒞) U) := by
  apply listProd_hom_ext hnd
  intro B hB
  rw [selectProj_factor U U h B hB, Cat.id_comp]

/-- **STRICT composition** (contravariant) — `selectProj` over a composite inclusion equals the
    composite of `selectProj`s.  Needs only the SMALLEST list `V` nodup. -/
theorem selectProj_trans {V U W : List 𝒞} (hVnd : V.Nodup)
    (hVU : ∀ B ∈ V, B ∈ U) (hUW : ∀ B ∈ U, B ∈ W) (hVW : ∀ B ∈ V, B ∈ W) :
    selectProj W V hVW = selectProj W U hUW ≫ selectProj U V hVU := by
  apply listProd_hom_ext hVnd
  intro B hB
  rw [selectProj_factor W V hVW B hB, Cat.assoc, selectProj_factor U V hVU B hB,
      selectProj_factor W U hUW B (hVU B hB)]

/-- **Reordering iso** — between two nodup lists with the same members, `selectProj` both ways are
    mutually inverse.  Lets the cover proof move the head to the front of the codomain. -/
theorem selectProj_reorder_iso {V V' : List 𝒞} (hV : V.Nodup) (hV' : V'.Nodup)
    (hVV' : ∀ B ∈ V, B ∈ V') (hV'V : ∀ B ∈ V', B ∈ V) :
    IsIso (selectProj V V' hV'V) := by
  refine ⟨selectProj V' V hVV', ?_, ?_⟩
  · apply listProd_hom_ext hV
    intro B hB
    rw [Cat.assoc, selectProj_factor V' V hVV' B hB, selectProj_factor V V' hV'V B (hVV' B hB),
        Cat.id_comp]
  · apply listProd_hom_ext hV'
    intro B hB
    rw [Cat.assoc, selectProj_factor V V' hV'V B hB, selectProj_factor V' V hVV' B (hV'V B hB),
        Cat.id_comp]

end Engine

/-! ## Phase 3 — the projection is a COVER (projection off well-supported factors)

  `selectProj U V h` is a cover when `V` is nodup and every member of `U` is well-supported.  Proof by
  induction on `U`.  Head `C ∉ V`: `selectProj` strips `C` (`selectProj_head_notin`), giving
  `snd ≫ (IH cover)`, a cover since `C` ws makes `snd` a cover.  Head `C ∈ V`: reorder the codomain to
  bring `C` to the front (`selectProj_reorder_iso`), reducing to `id_C × (IH cover)`
  (`prodLeftMap_cover`). -/

section Cover

variable [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]

/-- `snd : C×A ⟶ A` is a cover when `C` is well-supported (`prod_fst_cover` through `prodSwap`). -/
theorem prod_snd_cover {C A : 𝒞} (hC : WellSupported C) :
    Cover (snd : prod C A ⟶ A) := by
  have h : (snd : prod C A ⟶ A) = prodSwap C A ≫ (fst : prod A C ⟶ A) := by rw [prodSwap_fst]
  rw [h]
  apply cover_precomp_iso (prod_comm_iso (A := C) (B := A))
  exact prod_fst_cover (C := A) (B := C) hC

/-- A cover followed by an iso is a cover.  (Mirrors `CofinalHstage.cover_comp_iso`, re-proved here
    to avoid that file's heavier import closure; needs no `HasImages`.) -/
theorem cover_postcomp_iso {X Y Z : 𝒞} {f : X ⟶ Y} {e : Y ⟶ Z} (hf : Cover f) (he : IsIso e) :
    Cover (f ≫ e) := by
  obtain ⟨einv, hee, heinv⟩ := he
  intro C m g hm hgm
  have hmono' : Mono (m ≫ einv) := by
    intro W a b hab
    apply hm
    have hcomp : (a ≫ m ≫ einv) ≫ e = (b ≫ m ≫ einv) ≫ e := by rw [hab]
    calc a ≫ m = a ≫ m ≫ (einv ≫ e) := by rw [heinv, Cat.comp_id]
      _ = (a ≫ m ≫ einv) ≫ e := by rw [Cat.assoc, Cat.assoc]
      _ = (b ≫ m ≫ einv) ≫ e := hcomp
      _ = b ≫ m ≫ (einv ≫ e) := by rw [Cat.assoc, Cat.assoc]
      _ = b ≫ m := by rw [heinv, Cat.comp_id]
  have hfac : (g ≫ m ≫ einv) = f := by
    rw [← Cat.assoc, show g ≫ m = f ≫ e from hgm, Cat.assoc, hee, Cat.comp_id]
  obtain ⟨minv, hm1, hm2⟩ := hf (m ≫ einv) g hmono' hfac
  refine ⟨einv ≫ minv, ?_, ?_⟩
  · calc m ≫ (einv ≫ minv) = (m ≫ einv) ≫ minv := (Cat.assoc _ _ _).symm
      _ = Cat.id C := hm1
  · calc (einv ≫ minv) ≫ m = einv ≫ (minv ≫ m) := Cat.assoc _ _ _
      _ = einv ≫ (minv ≫ m) ≫ (einv ≫ e) := by rw [heinv, Cat.comp_id]
      _ = einv ≫ (minv ≫ (m ≫ einv)) ≫ e := by rw [Cat.assoc, Cat.assoc, Cat.assoc]
      _ = einv ≫ (Cat.id Y) ≫ e := by rw [hm2]
      _ = einv ≫ e := by rw [Cat.id_comp]
      _ = Cat.id Z := heinv

variable [DecidableEq 𝒞]

/-- When the head `C` of `U` is NOT in `V`, `selectProj (C::U') V` strips `C` via `snd`. -/
theorem selectProj_head_notin (C : 𝒞) (U' : List 𝒞) :
    ∀ (V : List 𝒞) (h : ∀ B ∈ V, B ∈ C :: U') (_hC : C ∉ V) (h' : ∀ B ∈ V, B ∈ U'),
      selectProj (C :: U') V h
        = (snd : prod C (listProd U') ⟶ listProd U') ≫ selectProj U' V h'
  | [], _, _, _ => by rw [selectProj, selectProj]; exact (term_uniq _ _)
  | C2 :: V', h, hC, h' => by
    rw [selectProj, selectProj, pair_precomp]
    have hC2 : C ≠ C2 := fun e => hC (e ▸ List.mem_cons_self)
    have hfp : factorProj (C :: U') C2 (h C2 List.mem_cons_self)
        = (snd : prod C (listProd U') ⟶ listProd U')
          ≫ factorProj U' C2 (h' C2 List.mem_cons_self) := by
      rw [factorProj]; simp only [hC2, dif_neg, not_false_iff]
    rw [hfp, selectProj_head_notin C U' V' (fun B hB => h B (List.mem_cons.2 (Or.inr hB)))
        (fun e => hC (List.mem_cons.2 (Or.inr e)))
        (fun B hB => h' B (List.mem_cons.2 (Or.inr hB)))]

/-- **Pull a single factor to the front (`listProd` reindexing).**  For a NODUP list `N` containing
    `A`, the reordering projection `ψ := selectProj N (A :: N.erase A)` is an ISO
    `∏N ≅ A × ∏(N.erase A)` whose first leg is the factor projection at `A`
    (`ψ ≫ fst = factorProj N A`) and whose second leg is the projection onto the remaining factors
    (`ψ ≫ snd = selectProj N (N.erase A)`).  This presents `∏N` in the binary-product shape the
    §1.546 escape (`baseChange_freshFactor_missed`) consumes, with `A` as the fresh coordinate — even
    when `A` is buried in the middle of the right-folded `∏N`.  Mathlib-free (`List.erase` is core);
    `IsIso` via `selectProj_reorder_iso`, the leg equations via `selectProj_factor`. -/
theorem listProd_pull_factor (N : List 𝒞) (A : 𝒞) (hnd : N.Nodup) (hA : A ∈ N) :
    let N' := N.erase A
    let hsub : ∀ B ∈ A :: N', B ∈ N := fun _ hB =>
      (List.mem_cons.1 hB).elim (· ▸ hA) List.mem_of_mem_erase
    let ψ : listProd (𝒞 := 𝒞) N ⟶ prod A (listProd N') := selectProj N (A :: N') hsub
    IsIso ψ ∧ ψ ≫ (fst : prod A (listProd N') ⟶ A) = factorProj N A hA ∧
      ψ ≫ (snd : prod A (listProd N') ⟶ listProd N')
        = selectProj N N' (fun _ hB => List.mem_of_mem_erase hB) := by
  intro N' hsub ψ
  have hNnd : (A :: N').Nodup := List.nodup_cons.2 ⟨List.Nodup.not_mem_erase hnd, hnd.erase A⟩
  have hsup : ∀ B ∈ N, B ∈ A :: N' := fun B hB => by
    by_cases e : B = A
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons.2 (Or.inr (List.mem_erase_of_ne e |>.2 hB))
  refine ⟨selectProj_reorder_iso hnd hNnd hsup hsub, ?_, ?_⟩
  · have : (fst : prod A (listProd N') ⟶ A) = factorProj (A :: N') A List.mem_cons_self :=
      (factorProj_cons_head _).symm
    rw [this, selectProj_factor N (A :: N') hsub A List.mem_cons_self]
  · have hsnd : (snd : prod A (listProd N') ⟶ listProd N')
        = selectProj (A :: N') N' (fun B hB => List.mem_cons.2 (Or.inr hB)) := by
      rw [selectProj_head_notin A N' N' (fun B hB => List.mem_cons.2 (Or.inr hB))
            (List.Nodup.not_mem_erase hnd) (fun B hB => hB),
          selectProj_refl (hnd.erase A) (fun B hB => hB), Cat.comp_id]
    rw [hsnd]
    show selectProj N (A :: N') hsub ≫ selectProj (A :: N') N' _ = _
    rw [← selectProj_trans (hnd.erase A) (fun B hB => List.mem_cons.2 (Or.inr hB)) hsub
          (fun _ hB => List.mem_of_mem_erase hB)]

private theorem mem_filter_ne {C x : 𝒞} {V : List 𝒞} :
    x ∈ V.filter (fun y => y ≠ C) ↔ x ∈ V ∧ x ≠ C := by
  rw [List.mem_filter]; simp

private theorem nodup_filter (p : 𝒞 → Bool) : ∀ {l : List 𝒞}, l.Nodup → (l.filter p).Nodup
  | [], _ => by simp
  | a :: t, hh => by
    rw [List.filter_cons]
    by_cases hp : p a
    · simp only [hp, if_pos]
      exact List.nodup_cons.2
        ⟨fun hc => (List.nodup_cons.1 hh).1 (List.mem_filter.1 hc).1,
          nodup_filter p (List.nodup_cons.1 hh).2⟩
    · simp only [hp, if_neg, Bool.false_eq_true, not_false_iff]
      exact nodup_filter p (List.nodup_cons.1 hh).2

private theorem frontList_nodup {C : 𝒞} {V : List 𝒞} (hV : V.Nodup) :
    (C :: V.filter (fun x => x ≠ C)).Nodup :=
  List.nodup_cons.2 ⟨fun hc => (mem_filter_ne.1 hc).2 rfl, nodup_filter _ hV⟩

private theorem frontList_mem_left {C : 𝒞} {V : List 𝒞} :
    ∀ B ∈ V, B ∈ C :: V.filter (fun x => x ≠ C) := by
  intro B hB
  by_cases hBC : B = C
  · exact hBC ▸ List.mem_cons_self
  · exact List.mem_cons.2 (Or.inr (mem_filter_ne.2 ⟨hB, hBC⟩))

private theorem frontList_mem_right {C : 𝒞} {V : List 𝒞} (hC : C ∈ V) :
    ∀ B ∈ C :: V.filter (fun x => x ≠ C), B ∈ V := by
  intro B hB
  rcases List.mem_cons.1 hB with e | hf
  · exact e ▸ hC
  · exact (mem_filter_ne.1 hf).1

/-- **`selectProj U V h` is a COVER when `V` is nodup and every member of `U` is well-supported.**
    Induction on `U` (`C ∉ V`: strip via `snd`; `C ∈ V`: reorder front + `prodLeftMap_cover`). -/
theorem selectProj_cover : ∀ (U V : List 𝒞), V.Nodup → ∀ (h : ∀ B ∈ V, B ∈ U)
    (_hws : ∀ B ∈ U, WellSupported B), Cover (selectProj U V h)
  | [], V, _, h, _ => by
    have hV : V = [] := List.eq_nil_iff_forall_not_mem.2 (fun x hx => by simpa using h x hx)
    subst hV; exact wellSupported_one
  | C :: U', V, hVnd, h, hws => by
    have hwsTail : ∀ B ∈ U', WellSupported B := fun B hB => hws B (List.mem_cons.2 (Or.inr hB))
    have hwsC : WellSupported C := hws C List.mem_cons_self
    by_cases hCV : C ∈ V
    · -- reorder `V` to `C :: V.filter (≠ C)`; over that front list `selectProj` is `id_C × …`.
      have hFnd : (C :: V.filter (fun x => x ≠ C)).Nodup := frontList_nodup hVnd
      have hVF : ∀ B ∈ V, B ∈ C :: V.filter (fun x => x ≠ C) := frontList_mem_left
      have hFV : ∀ B ∈ C :: V.filter (fun x => x ≠ C), B ∈ V := frontList_mem_right hCV
      have hFsub : ∀ B ∈ C :: V.filter (fun x => x ≠ C), B ∈ C :: U' := fun B hB => h B (hFV B hB)
      rw [selectProj_trans hVnd hVF hFsub h]
      refine cover_postcomp_iso ?_ (selectProj_reorder_iso hFnd hVnd hFV hVF)
      rw [selectProj, factorProj_cons_head]
      have hCVrem : C ∉ V.filter (fun x => x ≠ C) := fun hc => (mem_filter_ne.1 hc).2 rfl
      have hVrem' : ∀ B ∈ V.filter (fun x => x ≠ C), B ∈ U' := fun B hB =>
        (List.mem_cons.1 (h B (hFV B (List.mem_cons.2 (Or.inr hB))))).resolve_left
          (fun e => hCVrem (e ▸ hB))
      rw [selectProj_head_notin C U' (V.filter (fun x => x ≠ C)) _ hCVrem hVrem']
      apply prodLeftMap_cover
      exact selectProj_cover U' (V.filter (fun x => x ≠ C)) (nodup_filter _ hVnd) hVrem' hwsTail
    · have h' : ∀ B ∈ V, B ∈ U' := fun B hB =>
        (List.mem_cons.1 (h B hB)).resolve_left (fun e => hCV (e ▸ hB))
      rw [selectProj_head_notin C U' V h hCV h']
      exact cover_comp' (prod_snd_cover hwsC) (selectProj_cover U' V hVnd h' hwsTail)

end Cover

/-! ## Phase 4 — the cofinal directed SUBSET index and the strict `ProjSystem`

  `WSList S` = NODUP lists of WELL-SUPPORTED objects, ordered by `⊆`; `wsDirected` is its `Directed`
  (bound = `dedup` of append, still ws since both are).  `cofinalProjSystem` reads `pr`/`proj` off
  `listProd`/`selectProj`, with strict `proj_refl`/`proj_trans` from `selectProj_refl`/`selectProj_trans`. -/

section System

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S] [DecidableEq S]

/-- The index: finite SETS of WELL-SUPPORTED objects, modelled as NODUP lists. -/
def WSList (S : Type u) [Cat.{u} S] [PreRegularCategory S] :=
  {U : List S // U.Nodup ∧ ∀ B ∈ U, WellSupported B}

/-- The subset relation on the index. -/
def WSList.le (U V : WSList S) : Prop := ∀ B ∈ U.1, B ∈ V.1

/-- **The cofinal directed SUBSET index.**  `le = ⊆`; reflexive/transitive by the subset order;
    `bound = dedup (U ++ V)` (nodup, ws, contains both).  Unlike the prefix index, this is cofinal
    over the FULL object set (no countability ceiling). -/
def wsDirected (S : Type u) [Cat.{u} S] [PreRegularCategory S] [DecidableEq S] :
    Directed (WSList S) where
  le := WSList.le
  refl _ _ h := h
  trans hUV hVW x hx := hVW x (hUV x hx)
  bound U V := ⟨⟨dedup (U.1 ++ V.1), dedup_nodup _,
      fun B hB => by
        rcases List.mem_append.1 (mem_dedup.1 hB) with hl | hr
        · exact U.2.2 B hl
        · exact V.2.2 B hr⟩,
    fun x hx => mem_dedup.2 (List.mem_append.2 (Or.inl hx)),
    fun x hx => mem_dedup.2 (List.mem_append.2 (Or.inr hx))⟩

/-- **The cofinal strict `ProjSystem`.**  Stage product `pr i = ∏(i.1)`; projection `proj h =
    selectProj j.1 i.1 h` (the bigger product onto the smaller).  `proj_refl`/`proj_trans` are STRICT
    (on-the-nose) — the keystone, discharged by `selectProj_refl`/`selectProj_trans`. -/
noncomputable def cofinalProjSystem : ProjSystem (WSList S) (wsDirected S) S where
  pr i := listProd (𝒞 := S) i.1
  proj {i j} h := selectProj j.1 i.1 h
  proj_refl i := selectProj_refl i.2.1 _
  proj_trans {i _ _} hij hjk := selectProj_trans i.2.1 hij hjk _

/-- **Every projection of `cofinalProjSystem` is a cover.**  The bigger index `j` lists only
    well-supported objects (`j.2.2`) and is nodup (`i.2.1`), so `selectProj_cover` applies.  This is
    the `hpc` premise of `ratCapPreRegular_of_projCover` (and `projStage_faithful`, etc.). -/
theorem cofinalProjSystem_cover {i j : WSList S} (h : (wsDirected S).le i j) :
    Cover ((cofinalProjSystem (S := S)).proj h) := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  show Cover (selectProj j.1 i.1 h)
  exact selectProj_cover (𝒞 := S) j.1 i.1 i.2.1 h (fun B hB => j.2.2 B hB)

end System

/-! ## Phase 5 — the cofinal cover structure `WSCover` and its concrete inhabitant

  `WSCover S` bundles the directed SUBSET index (`DecidableEq S` for positional selection) together
  with the COFINALITY field: every well-supported `B` is reached at SOME index.  Over the subset order
  this is trivial — `B` is reached at the singleton `{B}` — which is exactly what removes the
  countability ceiling.  The concrete inhabitant uses `Classical.decEq S` for the index's object
  equality (the §1.543 exception); no enumeration / well-ordering of the carrier is needed (the subset
  order already dominates every finite set). -/

section Cover2

variable (S : Type u) [Cat.{u} S] [PreRegularCategory S]

/-- **The cofinal cover datum for the §1.547 uniform successor.**  It carries object equality
    (`Classical.decEq` in the inhabitant) and — the new ingredient the prefix index could not supply —
    the COFINALITY field, that every well-supported `B` is an element of some index list (hence is
    pointed by the corresponding rung).  Well-supportedness of every indexed factor is BUILT INTO the
    index `WSList` (its `.2.2` field), so the projection-cover holds unconditionally. -/
structure WSCover where
  /-- object equality, used for positional selection (`Classical.decEq` in the inhabitant). -/
  dec : DecidableEq S
  /-- **cofinality** — every well-supported object appears in SOME index (its singleton suffices). -/
  cofinal : ∀ (B : S), WellSupported B →
    ∃ (i : @WSList S _ _), B ∈ i.1

variable {S}

/-- The cofinal strict `ProjSystem` extracted from a `WSCover` (its `dec` supplies the positional
    object equality). -/
noncomputable def WSCover.projSystem (W : WSCover S) :
    letI := W.dec
    ProjSystem (@WSList S _ _) (wsDirected S) S :=
  letI := W.dec
  cofinalProjSystem

/-- The base index of a `WSCover`: the empty set `⟨[], …⟩`, whose stage product is the terminal
    (`∏[] = 1`), so the base fibre is `S/1`. -/
def WSCover.base (_ : WSCover S) : @WSList S _ _ :=
  ⟨[], List.nodup_nil, fun _ h => absurd h (by simp)⟩

theorem WSCover.base_chain (W : WSCover S) : (W.base).1 = ([] : List S) := rfl

/-- The projections of `cofinalProjSystem` are covers — re-exposed under a `WSCover` (whose `dec`
    supplies the positional object equality).  This is the `hpc` premise the §1.547 successor's
    `ratCapPreRegular_of_projCover` consumes. -/
theorem WSCover.projSystem_cover [DecidableEq S] {i j : @WSList S _ _}
    (h : (wsDirected S).le i j) :
    Cover ((cofinalProjSystem (S := S)).proj h) :=
  cofinalProjSystem_cover h

end Cover2

/-- **THE COFINAL INHABITANT.**  For every bundled pre-regular `S` there IS a `WSCover S.carrier`:
    `DecidableEq` from `Classical.decEq`; the COFINALITY witness for a well-supported `B` is its
    singleton index `⟨[B], …⟩` (nodup, and its sole member `B` is ws).  Because the index already
    ranges over ws-object lists, the projection-cover is unconditional.  THIS is what makes the §1.547
    successor UNCONDITIONAL/COFINAL — pointing EVERY well-supported object, not just a countable
    suffix. -/
noncomputable def wsCover (S : PreRegBundle.{u}) : WSCover S.carrier :=
  letI := S.cat
  letI := S.pre
  letI dec : DecidableEq S.carrier := Classical.typeDecidableEq S.carrier
  { dec := dec
    cofinal := fun B hB =>
      ⟨⟨[B], List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
        fun C hC => by rw [List.mem_singleton.1 hC]; exact hB⟩,
        List.mem_singleton.2 rfl⟩ }

end Freyd.CofinalProj
