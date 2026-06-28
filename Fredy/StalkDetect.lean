/-
  §1.635:239 — STALK DETECTION OF A PROPER SUBOBJECT.

  Freyd's collective-faithfulness step: a proper subobject `m : A' ↣ A`, probed by a class
  `x' : U.dom → A` over a complemented subterminator `U` that does NOT factor through `m`, is
  DETECTED by some ultra-filter stalk — the post-composition map `T_F̂(m)` on stalks fails to be
  surjective for some `F̂`.  The witnessing ultra-filter is the RELATIVE one
  (`exists_ultrafilter_excluding_within`) containing `U` but omitting the pushforward `Usub` of the
  inverse image of `m` along `x'`; were `T_F̂(m)` onto, the class of `x'` would lift through `m`,
  putting a member of `F̂` below `Usub`, against the construction.
-/
import Fredy.StalkFamily

namespace Freyd
open PreLogosHorn.Stalk

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]

/-- §1.635:239 — a proper subobject probed by a complemented subterminator is DETECTED by some
    ultra-filter stalk: the probe class escapes the image of `T_F̂(m)`. -/
theorem stalk_detects_proper_mono {A' A : 𝒞} (m : A' ⟶ A) (hm : Monic m)
    (U : Subobject 𝒞 one) (hUcomp : IsComplementedSub U)
    (x' : U.dom ⟶ A) (hx' : ¬ ∃ y : U.dom ⟶ A', y ≫ m = x') :
    ∃ F : StalkIndex 𝒞, ¬ Function.Surjective (TF.map F.val m) := by
  -- The subobject `m`, its inverse image along `x'`, and its pushforward into `Sub(1)`.
  let S : Subobject 𝒞 A := ⟨A', m, hm⟩
  let pb := HasPullbacks.has x' S.arr
  let P : Subobject 𝒞 U.dom := InverseImage x' S
  let Usub : Subobject 𝒞 one := pushforwardSub U.arr U.monic P
  -- `Usub ≤ U` (witnessed by `P.arr`), and `Usub` does NOT exhaust `U`.
  have hsub : Usub.le U := ⟨P.arr, rfl⟩
  have hUproper : ¬ U.le Usub := by
    rintro ⟨h, hh⟩
    -- `hh : h ≫ Usub.arr = U.arr`, and `Usub.arr ≡ pb.cone.π₁ ≫ U.arr`; cancel `U.arr`.
    have hsec : h ≫ pb.cone.π₁ = Cat.id U.dom := by
      apply U.monic
      calc (h ≫ pb.cone.π₁) ≫ U.arr = h ≫ (pb.cone.π₁ ≫ U.arr) := Cat.assoc _ _ _
        _ = h ≫ Usub.arr := rfl
        _ = U.arr := hh
        _ = Cat.id U.dom ≫ U.arr := (Cat.id_comp _).symm
    -- Then `x'` factors through `m` via `h ≫ π₂`, contradicting `hx'`.
    have hw : pb.cone.π₂ ≫ m = pb.cone.π₁ ≫ x' := pb.cone.w.symm
    refine hx' ⟨h ≫ pb.cone.π₂, ?_⟩
    calc (h ≫ pb.cone.π₂) ≫ m = h ≫ (pb.cone.π₂ ≫ m) := Cat.assoc _ _ _
      _ = h ≫ (pb.cone.π₁ ≫ x') := by rw [hw]
      _ = (h ≫ pb.cone.π₁) ≫ x' := (Cat.assoc _ _ _).symm
      _ = Cat.id U.dom ≫ x' := by rw [hsec]
      _ = x' := Cat.id_comp _
  -- The relative ultra-filter: contains `U`, omits every complemented `V ≤ Usub`.
  obtain ⟨ℱ, hUF, hUmem, hexcl⟩ :=
    exists_ultrafilter_excluding_within U hUcomp Usub hsub hUproper
  have hℱpre : IsPreFilter ℱ := hUF.1.1
  refine ⟨⟨ℱ, hUF⟩, ?_⟩
  show ¬ Function.Surjective (TF.map ℱ m)
  intro hsurj
  -- The class of `x'` in `T_ℱ(A)` is hit by some `z`; pick a representative `p` of `z`.
  obtain ⟨z, hz⟩ := hsurj (TF.mk ℱ ⟨U, hUmem, x'⟩)
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  have hz2 : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ m⟩ = TF.mk ℱ ⟨U, hUmem, x'⟩ := hz
  -- Equal `TF`-classes are `PrefRel`-related: a common refinement `W'` on which the maps agree.
  obtain ⟨W', hW', a, b, ha, hb, hab⟩ := PrefRel_of_TF_eq ℱ hℱpre hz2
  -- `b : W'.dom → U.dom` factors through `P` (the inverse image), since `b ≫ x' = (a ≫ p.map) ≫ m`.
  have hconew : b ≫ x' = (a ≫ p.map) ≫ S.arr := by
    calc b ≫ x' = a ≫ (p.map ≫ m) := hab.symm
      _ = (a ≫ p.map) ≫ m := (Cat.assoc _ _ _).symm
      _ = (a ≫ p.map) ≫ S.arr := rfl
  let cone : Cone x' S.arr := ⟨W'.dom, b, a ≫ p.map, hconew⟩
  let k : W'.dom ⟶ pb.cone.pt := pb.lift cone
  have hk : k ≫ pb.cone.π₁ = b := pb.lift_fst cone
  -- Hence `W' ≤ Usub` (witnessed by `k`), `W'` is complemented (member of an ultra-filter),
  -- so `W'` is excluded — contradicting `W' ∈ ℱ`.
  have hW'le : W'.le Usub := ⟨k, by
    show k ≫ (pb.cone.π₁ ≫ U.arr) = W'.arr
    calc k ≫ (pb.cone.π₁ ≫ U.arr) = (k ≫ pb.cone.π₁) ≫ U.arr := (Cat.assoc _ _ _).symm
      _ = b ≫ U.arr := by rw [hk]
      _ = W'.arr := hb⟩
  exact hexcl W' (hUF.2.1 W' hW') hW'le hW'

end Freyd
