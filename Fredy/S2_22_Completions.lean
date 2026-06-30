/-
  Freyd & Scedrov, *Categories and Allegories* — §2.221–§2.225: the completions of
  an allegory and their structural consequences.

  This file builds on `Fredy/S2_2.lean`, which already provides:

  • the classes `DistributiveAllegory`, `LocallyCompleteDistributiveAllegory` (LCDA),
    `GloballyCompleteAllegory` (with arbitrary disjoint unions);
  • §2.221/§2.222 the LOCAL COMPLETION / IDEAL ALLEGORY `Â = Downdeal 𝒜` of a
    distributive allegory, as a *full* LCDA instance
    (`instLocallyCompleteDistributiveAllegoryDowndealHom`) with a faithful
    principal-ideal embedding `R ↦ ↓R` (`DowndealHom.prin_injective`);
  • §2.224 the GLOBAL COMPLETION data `GlobalObj`/`GlobalMorphism` with a faithful
    embedding (`globalCompletionEmbed_injective`).

  We add, on top of that:

  • §2.223  An indexed DISJOINT UNION in an LCDA coincides with an (indexed)
    COPRODUCT: the injections enjoy the universal mapping property, with mediator
    `M = ⋃ᵢ Uᵢ°Rᵢ`.  This is the indexed extension of the binary §2.214 argument.
  • §2.225  In a GLOBALLY COMPLETE allegory a union of semi-simple morphisms is
    semi-simple: if `R = ⋃ᵢ Fᵢ°Gᵢ` with all `Fᵢ, Gᵢ` simple, then `R = F°G` with
    `F = ⋃ᵢ Uᵢ°Fᵢ`, `G = ⋃ᵢ Uᵢ°Gᵢ` simple — Freyd's keystone for "globally complete
    + every morphism a union of its semi-simple parts ⟹ semi-simple".
  • §2.222  Named restatement that the ideal allegory is an LCDA with a faithful
    representation (the instance already lives in `S2_2.lean`).

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, union `R ∪ S`, order `R ⊑ S`, supremum `Sup P`.  Strictly mathlib-free.
-/

import Fredy.S2_2

universe v u

namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

/-! ## Supremum bookkeeping in a locally complete distributive allegory

  Small facts about `Sup` that the §2.223/§2.225 arguments use: congruence in the
  predicate, the reciprocal of a supremum, and `R = S` from `R° = S°`. -/

section LCDAGeneral

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- An equality refines to the allegory order. -/
theorem le_of_eq' {a b : 𝒜} {R S : a ⟶ b} (h : R = S) : R ⊑ S := by
  rw [h]; exact le_refl S

/-- `Sup` depends only on the predicate up to logical equivalence. -/
theorem Sup_congr {a b : 𝒜} {P Q : (a ⟶ b) → Prop} (h : ∀ T, P T ↔ Q T) :
    Sup P = Sup Q := by
  have hPQ : P = Q := funext fun T => propext (h T)
  rw [hPQ]

/-- Reciprocation commutes with `Sup`: `(Sup P)° = Sup {R° | P R}`.  Reciprocation is
    an order-isomorphism, so it carries suprema to suprema.  (A copy of the pure-LCDA
    fact `Freyd.Alg.recip_Sup` proved in `S2_3.lean`; reproduced here to keep this
    §2.22 file independent of the §2.3 division-allegory layer.) -/
theorem recip_Sup' {a b : 𝒜} (P : (a ⟶ b) → Prop) :
    (Sup P)° = Sup (fun T : b ⟶ a => ∃ R, P R ∧ T = R°) := by
  apply le_antisymm
  · apply recip_le_iff.mpr
    apply Sup_le; intro R hR
    exact recip_le_iff.mp (le_Sup ⟨R, hR, rfl⟩)
  · apply Sup_le; rintro T ⟨R, hR, rfl⟩
    exact recip_mono (le_Sup hR)

/-- `R = S` follows from `R° = S°` (reciprocation is injective). -/
theorem recip_injective {a b : 𝒜} {R S : a ⟶ b} (h : R° = S°) : R = S := by
  have h2 : R°° = S°° := by rw [h]
  rwa [Allegory.recip_recip, Allegory.recip_recip] at h2

/-! ## §2.223  Disjoint unions coincide with coproducts

  A DISJOINT UNION of a family `{αᵢ}ᵢ` (Freyd §2.223) is an object `β` with
  injections `Uᵢ : αᵢ → β` satisfying the indexed extension of the five §2.214
  equations:

      `UᵢUᵢ° = 1`,   `UᵢUⱼ° = 0  (i ≠ j)`,   `⋃ᵢ Uᵢ°Uᵢ = 1`.

  (The disjointness `UᵢUⱼ° = 0` quantified over ordered pairs `i ≠ j` supplies both
  cross terms; the union `⋃ᵢ Uᵢ°Uᵢ = 1` is the indexed `recip_union_eq_id`.) -/

/-- A §2.223 DISJOINT UNION datum: injections `Uᵢ : αᵢ → β` with the three indexed
    coproduct equations. -/
structure IndexedDisjointUnion {I : Type u} (α : I → 𝒜) (β : 𝒜) where
  /-- The injections. -/
  U : (i : I) → α i ⟶ β
  /-- `UᵢUᵢ° = 1`. -/
  self : ∀ i, U i ≫ (U i)° = Cat.id (α i)
  /-- `UᵢUⱼ° = 0` for `i ≠ j`. -/
  cross : ∀ {i j : I}, i ≠ j → U i ≫ (U j)° = (𝟘 : α i ⟶ α j)
  /-- `⋃ᵢ Uᵢ°Uᵢ = 1`. -/
  complete : Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i) = Cat.id β

variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- **§2.223 (mediator law).**  For a disjoint union and a family `{Rᵢ : αᵢ → c}`, the
    morphism `M = ⋃ᵢ Uᵢ°Rᵢ` satisfies `Uⱼ ≫ M = Rⱼ`.  (The cross terms `UⱼUᵢ° = 0`
    vanish; the diagonal `UⱼUⱼ° = 1` survives.) -/
theorem IndexedDisjointUnion.inject_mediator (du : IndexedDisjointUnion α β)
    {c : 𝒜} (R : (i : I) → α i ⟶ c) (j : I) :
    du.U j ≫ Sup (fun T => ∃ i, T = (du.U i)° ≫ R i) = R j := by
  rw [comp_Sup_distrib]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
    by_cases hij : i = j
    · have h : du.U j ≫ ((du.U i)° ≫ R i) = R j := by
        subst hij; rw [← Cat.assoc, du.self, Cat.id_comp]
      exact le_of_eq' h
    · have h : du.U j ≫ ((du.U i)° ≫ R i) = (𝟘 : α j ⟶ c) := by
        rw [← Cat.assoc, du.cross (Ne.symm hij), DistributiveAllegory.zero_comp]
      rw [h]; exact zero_le _
  · apply le_Sup
    exact ⟨(du.U j)° ≫ R j, ⟨j, rfl⟩, by rw [← Cat.assoc, du.self, Cat.id_comp]⟩

/-- The indexed COPRODUCT universal property for injections `U : ∀ i, αᵢ → β`: every
    family `{Rᵢ : αᵢ → c}` factors uniquely through the injections (§2.223). -/
def IsIndexedCoproduct (U : (i : I) → α i ⟶ β) : Prop :=
  ∀ (c : 𝒜) (R : (i : I) → α i ⟶ c),
    ∃ M : β ⟶ c, (∀ i, U i ≫ M = R i) ∧
      (∀ M' : β ⟶ c, (∀ i, U i ≫ M' = R i) → M' = M)

/-- **§2.223.**  A disjoint union is an (indexed) coproduct: its injections enjoy the
    universal mapping property, with mediator `M = ⋃ᵢ Uᵢ°Rᵢ`.  Existence is the
    mediator law; uniqueness reciprocates and uses completeness `⋃ᵢ Uᵢ°Uᵢ = 1`. -/
theorem IndexedDisjointUnion.isCoproduct (du : IndexedDisjointUnion α β) :
    IsIndexedCoproduct du.U := by
  intro c R
  refine ⟨Sup (fun T => ∃ i, T = (du.U i)° ≫ R i), fun j => du.inject_mediator R j, ?_⟩
  intro M' hM'
  apply recip_injective
  rw [recip_Sup']
  -- M'° = ⋃ᵢ M'°(Uᵢ°Uᵢ)  (completeness `⋃ᵢ Uᵢ°Uᵢ = 1`, pushed through `M'° ≫ -`)
  have hL : Sup (fun T => ∃ S, (∃ i, S = (du.U i)° ≫ du.U i) ∧ T = M'° ≫ S) = M'° := by
    rw [← comp_Sup_distrib, du.complete, Cat.comp_id]
  rw [← hL]
  apply Sup_congr
  intro T
  constructor
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨(du.U i)° ≫ R i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, hM' i, Allegory.recip_comp, Allegory.recip_recip]⟩
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨(du.U i)° ≫ du.U i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, hM' i, Allegory.recip_comp, Allegory.recip_recip]⟩

/-- The assembled leg `F̂ = ⋃ᵢ Uᵢ°Fᵢ` of a family of SIMPLE morphisms over a disjoint
    union is itself SIMPLE.  `F̂°F̂ = ⋃ᵢ Fᵢ°Fᵢ ⊑ 1` because the cross terms `UᵢUⱼ°`
    vanish (`Uⱼ ≫ F̂ = Fⱼ`) and each `Fᵢ°Fᵢ ⊑ 1`. -/
theorem IndexedDisjointUnion.assembled_simple {a : 𝒜} (du : IndexedDisjointUnion α β)
    (F : (i : I) → α i ⟶ a) (hF : ∀ i, Simple (F i)) :
    Simple (Sup (fun T => ∃ i, T = (du.U i)° ≫ F i)) := by
  show (Sup (fun T => ∃ i, T = (du.U i)° ≫ F i))° ≫
      Sup (fun T => ∃ i, T = (du.U i)° ≫ F i) ⊑ Cat.id a
  rw [comp_Sup_distrib]
  apply Sup_le
  rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
  rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]
  exact hF i

end LCDAGeneral

/-! ## §2.225  A union of semi-simple morphisms is semi-simple

  Freyd §2.225: the local (and global) completion of a SEMI-SIMPLE allegory has the
  property that every morphism is the union of the semi-simple morphisms it contains;
  conversely a globally complete allegory with that property is itself semi-simple.
  The keystone is the following: in a globally complete allegory a union of
  semi-simple morphisms is again semi-simple.

  Given `R = ⋃ᵢ Fᵢ°Gᵢ` with all `Fᵢ : αᵢ → a`, `Gᵢ : αᵢ → b` simple, take the disjoint
  union `{Uᵢ : αᵢ → β}` and set `F = ⋃ᵢ Uᵢ°Fᵢ : β → a`, `G = ⋃ᵢ Uᵢ°Gᵢ : β → b`.  Then
  `F, G` are simple and `R = F°G`. -/

section GloballyComplete

variable {𝒜 : Type u} [GloballyCompleteAllegory 𝒜]

/-- Each `GloballyCompleteAllegory` disjoint union `disjointUnion α` is an
    `IndexedDisjointUnion` datum. -/
def GloballyCompleteAllegory.toIndexedDisjointUnion {I : Type u} (α : I → 𝒜) :
    IndexedDisjointUnion α (GloballyCompleteAllegory.disjointUnion α) where
  U := fun i => GloballyCompleteAllegory.inject (a := α) i
  self := fun i => GloballyCompleteAllegory.inject_self_comp_recip (a := α) i
  cross := fun h => GloballyCompleteAllegory.inject_comp_recip_ne (a := α) h
  complete := GloballyCompleteAllegory.complete (a := α)

/-- **§2.225.**  In a GLOBALLY COMPLETE allegory a union of semi-simple morphisms is
    semi-simple: if `R = ⋃ᵢ Fᵢ°Gᵢ` with every `Fᵢ, Gᵢ` simple, then `R` is semi-simple
    (witnessed by the assembled legs `F = ⋃ᵢ Uᵢ°Fᵢ`, `G = ⋃ᵢ Uᵢ°Gᵢ` over the disjoint
    union of the apexes). -/
theorem semiSimple_of_iSup_semiSimple {I : Type u} {a b : 𝒜} (α : I → 𝒜)
    (F : (i : I) → α i ⟶ a) (G : (i : I) → α i ⟶ b)
    (hF : ∀ i, Simple (F i)) (hG : ∀ i, Simple (G i))
    {R : a ⟶ b}
    (hR : R = Sup (fun T => ∃ i, T = (F i)° ≫ G i)) :
    SemiSimple R := by
  let du := GloballyCompleteAllegory.toIndexedDisjointUnion α
  refine ⟨GloballyCompleteAllegory.disjointUnion α,
    Sup (fun T => ∃ i, T = (du.U i)° ≫ F i),
    Sup (fun T => ∃ i, T = (du.U i)° ≫ G i),
    du.assembled_simple F hF, du.assembled_simple G hG, ?_⟩
  rw [hR]
  symm
  rw [comp_Sup_distrib]
  apply Sup_congr
  intro T
  constructor
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(du.U i)° ≫ G i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]⟩

end GloballyComplete

/-! ## §2.222  The ideal allegory is a locally complete distributive allegory

  Freyd §2.222: for a distributive allegory `A`, the allegory of IDEALS is a locally
  complete distributive allegory, and `A ↪ Â` is a faithful representation.  In this
  repository the ideal allegory is `Downdeal 𝒜` (whose homs `DowndealHom` are ideals:
  downward-closed, `𝟘`-containing, `∪`-closed), and the LCDA instance is already
  `instLocallyCompleteDistributiveAllegoryDowndealHom` in `S2_2.lean`.  We record the
  §2.222 statement explicitly. -/

/-- **§2.222.**  The ideal allegory `Â = Downdeal 𝒜` of a distributive allegory is a
    locally complete distributive allegory (the instance already lives in `S2_2.lean`;
    re-exported here under the §2.222 name). -/
def idealAllegory_locallyComplete (𝒜 : Type u) [DistributiveAllegory 𝒜] :
    LocallyCompleteDistributiveAllegory (Downdeal 𝒜) :=
  instLocallyCompleteDistributiveAllegoryDowndealHom

/-- **§2.222.**  The principal-ideal embedding `A → Â`, `R ↦ ↓R`, is faithful — so any
    distributive allegory is faithfully represented in a locally complete one. -/
theorem idealAllegory_faithful {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    {R S : a ⟶ b} (h : DowndealHom.prin R = DowndealHom.prin S) : R = S :=
  DowndealHom.prin_injective h

end Freyd.Alg
