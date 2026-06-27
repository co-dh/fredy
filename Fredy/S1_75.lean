/-
  Freyd & Scedrov, *Categories, Allegories* §1.75  THE STONE REPRESENTATION THEOREM

  This file formalizes the cleanly stateable, infrastructure-light part of §1.75:
  the §1.751 vocabulary of ATOMS that opens the proof of the Stone Representation
  Theorem.  The Stone theorem proper (§1.75, §1.752–§1.755) is irreducibly
  topological — it builds the Stone space 𝒮(ℬ) of the boolean algebra of
  complemented subterminators, its stalk/sheaf functor `T : A → 𝓜(X)`, and uses
  point-set facts about Cantor space / the real line (Appendix A).  None of that
  machinery (Stone spaces, ultra-filters, stalk functors, sheaves on ℝ) exists in
  this repo, so those statements are recorded MISSING below rather than faked.

  §1.751  ATOM:  an object whose unique PROPER subobject is 0.
          ATOMICALLY BASED logos:  its atoms form a basis (§1.632).
          ATOMLESS logos:  it has no atoms.
          "Atomically based ⇒ boolean."   (book theorem; PROVED below as
            `atomicallyBased_isComplementedSub`, given indexed subobject joins +
            the §1.84 frame law, packaged as `HasIndexedSubobjectJoins`.)

  This file also BUILDS the missing `HasIndexedSubobjectJoins` infrastructure (the
  indexed/small subobject join `sup` plus the frame law `invImage_preserves_sup`) and the
  atom-image disjointness machinery used to discharge the boolean property.

  REUSE (DRY):
    Subobject, Subobject.le, Subobject.IsEntire, image, Allows, Cover (S1_51)
    PreLogos, PreLogos.bottom, HasSubobjectUnions, InverseImage       (S1_60)
    minimal_subobject_of_one_is_coterminator, any_map_to_zero_is_iso  (S1_61)
    Subobject.inter, IsComplementedSub, IsBasis                       (S1_62)
    image_lift_cover, cover_pullback                                  (S1_52/S1_56)
-/

import Fredy.S1_51
import Fredy.S1_60
import Fredy.S1_61
import Fredy.S1_62
import Fredy.S1_64

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.751  Atoms -/

/-- A subobject `S ↣ A` is PROPER (§1.751) if it is not entire, i.e. its
    representing mono is not an isomorphism.  (Freyd: "proper subobject" = a
    subobject strictly below the whole object.) -/
def Subobject.IsProper {A : 𝒞} (S : Subobject 𝒞 A) : Prop :=
  ¬ S.IsEntire

/-- An object `A` is an ATOM (§1.751): "0 is its unique proper subobject."

    Unwound (Freyd's literal phrasing):
    * `0` (the bottom subobject) is itself proper — equivalently `A` is not a
      zero-object; the book stresses "the definition of atom excludes
      zero-objects";
    * every proper subobject of `A` coincides with `0`, i.e. factors through the
      bottom.  Since `bottom_min` already gives `0 ≤ S` for all `S`, demanding
      `S ≤ 0` pins `S` to `0` as a subobject.

    So: `0` is proper, and every proper subobject is `≤ 0`. -/
def IsAtom [PreLogos 𝒞] (A : 𝒞) : Prop :=
  (PreLogos.bottom A).IsProper ∧
  ∀ (S : Subobject 𝒞 A), S.IsProper → S.le (PreLogos.bottom A)

/-- A logos is ATOMICALLY BASED (§1.751) if its atoms form a basis (§1.632):
    the representable functors `Hom(A, −)` for atoms `A` are collectively faithful
    and separate proper subobjects.  Reuses `IsBasis` from §1.632. -/
def AtomicallyBased [PreLogos 𝒞] [HasPullbacks 𝒞] : Prop :=
  IsBasis (𝒞 := 𝒞) (fun A => IsAtom A)

/-- A logos is ATOMLESS (§1.751) if it has no atoms.  (Freyd: "note that the
    definition of atom excludes zero-objects", so a degenerate/zero logos is
    vacuously atomless under this reading.) -/
def Atomless [PreLogos 𝒞] : Prop :=
  ∀ (A : 𝒞), ¬ IsAtom A

/-! ## §1.75  Indexed subobject joins (+ frame law)

  Freyd's complement of `S ⊆ A` is the join of all atom-images not factoring through `S`:
      `¬S = ⊔ { image(x) | G atom, x : G → A, x ∤ S }`.
  This is an INDEXED (small) join over a family parameterized by every atom and every map
  out of it; `HasSubobjectUnions` (S1_60) gives only BINARY joins.  We package exactly the
  needed primitive: a least-upper-bound `sup` for a predicate-family of subobjects of a
  fixed object (the §1.712 `LocallyComplete` structure), together with the FRAME LAW
  `invImage_preserves_sup` (inverse image preserves arbitrary joins).  The frame law is the
  §1.84 `PullbacksPreserveArbitraryUnions` / infinite distributive law; it is NOT derivable
  from `PreLogos` (which preserves only binary unions), so it is a field of the class — the
  same shape as `locallyComplete_with_union_preserving_is_logos` (S1_70) and the Giraud
  `pullback_union` field (S1_84). -/

/-- **`HasIndexedSubobjectJoins`** (§1.712 / §1.84).  Least upper bound `sup` for a
    predicate-family of subobjects of a fixed `A`, *plus* the frame law
    `invImage_preserves_sup`.  `sup`/`sup_upper`/`sup_least` are the `LocallyComplete`
    complete-lattice fields; `invImage_preserves_sup` is the infinite distributive law
    (`PullbacksPreserveArbitraryUnions`, §1.84), which a bare `PreLogos` does not supply. -/
class HasIndexedSubobjectJoins (𝒞 : Type u) [Cat.{v} 𝒞] [PreLogos 𝒞] where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A),
    S s → Subobject.le s (sup S)
  sup_least : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ (s : Subobject 𝒞 A), S s → Subobject.le s U) → Subobject.le (sup S) U
  /-- FRAME LAW (§1.84 `PullbacksPreserveArbitraryUnions`): inverse image preserves
      arbitrary joins, `f# (⊔ S) ≤ ⊔ { f# B' | B' ∈ S }`. -/
  invImage_preserves_sup : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
    Subobject.le (InverseImage f (sup S))
      (sup (fun A' => ∃ B', S B' ∧ A' = InverseImage f B'))

open HasIndexedSubobjectJoins

/-- Maps out of `(bottom X).dom` are unique: it is a zero object (§1.61). -/
theorem botDom_map_uniq [hPL : PreLogos 𝒞] {X Y : 𝒞}
    (f g : (PreLogos.bottom X).dom ⟶ Y) : f = g := by
  let ct := minimal_subobject_of_one_is_coterminator hPL
  obtain ⟨φ, ψ, hφψ, _⟩ := hPL.bottom_dom_iso X (hPL.toHasTerminal.one)
  have hψf : ψ ≫ f = ψ ≫ g := ct.init_uniq (ψ ≫ f) (ψ ≫ g)
  calc f = (φ ≫ ψ) ≫ f := by rw [hφψ, Cat.id_comp]
    _ = φ ≫ (ψ ≫ f) := Cat.assoc _ _ _
    _ = φ ≫ (ψ ≫ g) := by rw [hψf]
    _ = (φ ≫ ψ) ≫ g := (Cat.assoc _ _ _).symm
    _ = g := by rw [hφψ, Cat.id_comp]

/-- Any morphism into `(bottom P).dom` is an isomorphism (§1.61 `any_map_to_zero_is_iso`). -/
theorem mapTo_botDom_iso [hPL : PreLogos 𝒞] {Z P : 𝒞} (j : Z ⟶ (PreLogos.bottom P).dom) :
    IsIso j := by
  obtain ⟨θ, θinv, hθ1, hθ2⟩ := hPL.bottom_dom_iso P (hPL.toHasTerminal.one)
  have hjθ : IsIso (j ≫ θ) := any_map_to_zero_is_iso hPL (j ≫ θ)
  obtain ⟨w, hw1, hw2⟩ := hjθ
  have hθmono : Monic θ := fun {W} g h hgh => by
    calc g = g ≫ (θ ≫ θinv) := by rw [hθ1, Cat.comp_id]
      _ = (g ≫ θ) ≫ θinv := (Cat.assoc _ _ _).symm
      _ = (h ≫ θ) ≫ θinv := by rw [hgh]
      _ = h ≫ (θ ≫ θinv) := Cat.assoc _ _ _
      _ = h := by rw [hθ1, Cat.comp_id]
  refine ⟨θ ≫ w, by rw [← Cat.assoc]; exact hw1, ?_⟩
  apply hθmono
  calc ((θ ≫ w) ≫ j) ≫ θ = θ ≫ (w ≫ (j ≫ θ)) := by
        rw [Cat.assoc (θ ≫ w) j θ, Cat.assoc θ w (j ≫ θ)]
    _ = θ ≫ Cat.id _ := by rw [hw2]
    _ = θ := Cat.comp_id _
    _ = Cat.id (PreLogos.bottom P).dom ≫ θ := (Cat.id_comp _).symm

/-- If `x# S` is entire (pullback of `S` along `x` is the whole source), then `x` factors
    through `S`. -/
theorem allows_of_invImage_entire [PreLogos 𝒞] {G A : 𝒞} (x : G ⟶ A) (S : Subobject 𝒞 A)
    (hent : (InverseImage x S).IsEntire) : Allows S x := by
  obtain ⟨inv, _, hinv2⟩ := hent
  let pb := HasPullbacks.has x S.arr
  refine ⟨inv ≫ pb.cone.π₂, ?_⟩
  have hw : pb.cone.π₁ ≫ x = pb.cone.π₂ ≫ S.arr := pb.cone.w
  have hi : inv ≫ pb.cone.π₁ = Cat.id G := hinv2
  calc (inv ≫ pb.cone.π₂) ≫ S.arr = inv ≫ (pb.cone.π₂ ≫ S.arr) := Cat.assoc _ _ _
    _ = inv ≫ (pb.cone.π₁ ≫ x) := by rw [hw]
    _ = (inv ≫ pb.cone.π₁) ≫ x := (Cat.assoc _ _ _).symm
    _ = Cat.id G ≫ x := by rw [hi]
    _ = x := Cat.id_comp x

/-- A cover whose source admits a map to a bottom-domain (hence is a zero object) and that
    factors through a subobject `N` forces `N ≤ 0`. -/
theorem cover_from_zero_le [PreLogos 𝒞] {P Q : 𝒞} {Z : 𝒞}
    (N : Subobject 𝒞 Q) (cfac : Z ⟶ N.dom) (hc : Cover cfac)
    (j : Z ⟶ (PreLogos.bottom P).dom) : N.le (PreLogos.bottom Q) := by
  obtain ⟨jinv, hj1, _⟩ := mapTo_botDom_iso j (P := P)
  obtain ⟨γ, _⟩ := PreLogos.bottom_dom_iso P N.dom
  let z₀ : Z ⟶ (PreLogos.bottom N.dom).dom := j ≫ γ
  have hcfac_eq : cfac = z₀ ≫ (PreLogos.bottom N.dom).arr := by
    have key : jinv ≫ cfac = jinv ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr) := botDom_map_uniq _ _
    calc cfac = (j ≫ jinv) ≫ cfac := by rw [hj1, Cat.id_comp]
      _ = j ≫ (jinv ≫ cfac) := Cat.assoc _ _ _
      _ = j ≫ (jinv ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr)) := by rw [key]
      _ = (j ≫ jinv) ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr) := (Cat.assoc _ _ _).symm
      _ = z₀ ≫ (PreLogos.bottom N.dom).arr := by rw [hj1, Cat.id_comp]
  have hbot_iso : IsIso (PreLogos.bottom N.dom).arr :=
    hc (PreLogos.bottom N.dom).arr z₀ (PreLogos.bottom N.dom).monic hcfac_eq.symm
  obtain ⟨bi, _, hbi2⟩ := hbot_iso
  obtain ⟨δ, _⟩ := PreLogos.bottom_dom_iso N.dom Q
  refine ⟨bi ≫ δ, ?_⟩
  have hbridge : δ ≫ (PreLogos.bottom Q).arr = (PreLogos.bottom N.dom).arr ≫ N.arr :=
    botDom_map_uniq _ _
  calc (bi ≫ δ) ≫ (PreLogos.bottom Q).arr = bi ≫ (δ ≫ (PreLogos.bottom Q).arr) := Cat.assoc _ _ _
    _ = bi ≫ ((PreLogos.bottom N.dom).arr ≫ N.arr) := by rw [hbridge]
    _ = (bi ≫ (PreLogos.bottom N.dom).arr) ≫ N.arr := (Cat.assoc _ _ _).symm
    _ = Cat.id N.dom ≫ N.arr := by rw [hbi2]
    _ = N.arr := Cat.id_comp _

/-- Symmetry of intersection: `S ∩ T ≤ T ∩ S`. -/
theorem inter_le_swap [PreLogos 𝒞] {A : 𝒞} (S T : Subobject 𝒞 A) :
    (Subobject.inter S T).le (Subobject.inter T S) := by
  let pbST := HasPullbacks.has S.arr T.arr
  let pbTS := HasPullbacks.has T.arr S.arr
  have hw : pbST.cone.π₂ ≫ T.arr = pbST.cone.π₁ ≫ S.arr := pbST.cone.w.symm
  let c : Cone T.arr S.arr := ⟨pbST.cone.pt, pbST.cone.π₂, pbST.cone.π₁, hw⟩
  refine ⟨pbTS.lift c, ?_⟩
  show pbTS.lift c ≫ (pbTS.cone.π₁ ≫ T.arr) = pbST.cone.π₁ ≫ S.arr
  have h1 : pbTS.lift c ≫ pbTS.cone.π₁ = pbST.cone.π₂ := pbTS.lift_fst c
  calc pbTS.lift c ≫ (pbTS.cone.π₁ ≫ T.arr)
      = (pbTS.lift c ≫ pbTS.cone.π₁) ≫ T.arr := (Cat.assoc _ _ _).symm
    _ = pbST.cone.π₂ ≫ T.arr := by rw [h1]
    _ = pbST.cone.π₁ ≫ S.arr := pbST.cone.w.symm

/-- Bridge (⇐): `S.arr# M ≤ 0` implies `S ∩ M ≤ 0`. -/
theorem inter_le_bottom_of_invImage [PreLogos 𝒞] {A : 𝒞} (S M : Subobject 𝒞 A)
    (h : (InverseImage S.arr M).le (PreLogos.bottom S.dom)) :
    (Subobject.inter S M).le (PreLogos.bottom A) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨φ, _, _, _⟩ := PreLogos.bottom_dom_iso S.dom A
  refine ⟨k ≫ φ, ?_⟩
  have hbridge : φ ≫ (PreLogos.bottom A).arr = (PreLogos.bottom S.dom).arr ≫ S.arr :=
    botDom_map_uniq _ _
  show (k ≫ φ) ≫ (PreLogos.bottom A).arr = (Subobject.inter S M).arr
  have harr : (Subobject.inter S M).arr = (InverseImage S.arr M).arr ≫ S.arr := rfl
  rw [harr, ← hk]
  calc (k ≫ φ) ≫ (PreLogos.bottom A).arr = k ≫ (φ ≫ (PreLogos.bottom A).arr) := Cat.assoc _ _ _
    _ = k ≫ ((PreLogos.bottom S.dom).arr ≫ S.arr) := by rw [hbridge]
    _ = (k ≫ (PreLogos.bottom S.dom).arr) ≫ S.arr := (Cat.assoc _ _ _).symm

/-- Bridge (⇒): `S ∩ M ≤ 0` implies `S.arr# M ≤ 0`. -/
theorem invImage_le_bottom_of_inter [PreLogos 𝒞] {A : 𝒞} (S M : Subobject 𝒞 A)
    (h : (Subobject.inter S M).le (PreLogos.bottom A)) :
    (InverseImage S.arr M).le (PreLogos.bottom S.dom) := by
  obtain ⟨hwit, _⟩ := h
  obtain ⟨hi, hhi1, _⟩ := mapTo_botDom_iso hwit (P := A)
  obtain ⟨ε, _⟩ := PreLogos.bottom_dom_iso A S.dom
  refine ⟨hwit ≫ ε, ?_⟩
  have key : hi ≫ ((hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr) = hi ≫ (InverseImage S.arr M).arr :=
    botDom_map_uniq _ _
  have hfin : (hwit ≫ hi) ≫ (InverseImage S.arr M).arr = (InverseImage S.arr M).arr := by
    rw [hhi1, Cat.id_comp]
  calc (hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr
      = ((hwit ≫ hi) ≫ (hwit ≫ ε)) ≫ (PreLogos.bottom S.dom).arr := by rw [hhi1, Cat.id_comp]
    _ = hwit ≫ (hi ≫ ((hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr)) := by rw [Cat.assoc, Cat.assoc]
    _ = hwit ≫ (hi ≫ (InverseImage S.arr M).arr) := by rw [key]
    _ = (hwit ≫ hi) ≫ (InverseImage S.arr M).arr := (Cat.assoc _ _ _).symm
    _ = (InverseImage S.arr M).arr := hfin

/-- **Atom-image disjointness** (§1.751).  For an atom `G` and `x : G → A` that does NOT
    factor through `S`, the image of `x` is disjoint from `S`: `S ∩ image(x) ≤ 0`.

    Proof: `x# S` is a subobject of the atom `G`, so by atomicity it is `0` or all of `G`;
    "all of `G`" would make `x` factor through `S`, so `x# S ≤ 0`.  Pulling this `0` up
    along the cover `image.lift x` (covers are pullback-stable, §1.52) and the bridge
    lemmas transports it to `S ∩ image(x) ≤ 0`. -/
theorem atom_image_disjoint [PreLogos 𝒞] {G A : 𝒞} (hG : IsAtom G)
    (x : G ⟶ A) (S : Subobject 𝒞 A) (hx : ¬ Allows S x) :
    (Subobject.inter S (image x)).le (PreLogos.bottom A) := by
  have h0 : (InverseImage x S).le (PreLogos.bottom G) := by
    apply hG.2; intro hent; exact hx (allows_of_invImage_entire x S hent)
  obtain ⟨jw, _⟩ := h0
  let N : Subobject 𝒞 (image x).dom := InverseImage (image x).arr S
  let il := image.lift x
  let pb1 := HasPullbacks.has il N.arr
  have hcov : Cover pb1.cone.π₂ := cover_pullback (𝒞 := 𝒞) N.arr (image_lift_cover x)
  let Npb := HasPullbacks.has (image x).arr S.arr
  have hcone_w : pb1.cone.π₁ ≫ x = (pb1.cone.π₂ ≫ Npb.cone.π₂) ≫ S.arr := by
    have e1 : pb1.cone.π₁ ≫ il = pb1.cone.π₂ ≫ N.arr := pb1.cone.w
    have e2 : Npb.cone.π₁ ≫ (image x).arr = Npb.cone.π₂ ≫ S.arr := Npb.cone.w
    calc pb1.cone.π₁ ≫ x = pb1.cone.π₁ ≫ (il ≫ (image x).arr) := by rw [image.lift_fac]
      _ = (pb1.cone.π₁ ≫ il) ≫ (image x).arr := (Cat.assoc _ _ _).symm
      _ = (pb1.cone.π₂ ≫ N.arr) ≫ (image x).arr := by rw [e1]
      _ = (pb1.cone.π₂ ≫ Npb.cone.π₁) ≫ (image x).arr := rfl
      _ = pb1.cone.π₂ ≫ (Npb.cone.π₁ ≫ (image x).arr) := Cat.assoc _ _ _
      _ = pb1.cone.π₂ ≫ (Npb.cone.π₂ ≫ S.arr) := by rw [e2]
      _ = (pb1.cone.π₂ ≫ Npb.cone.π₂) ≫ S.arr := (Cat.assoc _ _ _).symm
  let invpb := HasPullbacks.has x S.arr
  let cone_xS : Cone x S.arr := ⟨pb1.cone.pt, pb1.cone.π₁, pb1.cone.π₂ ≫ Npb.cone.π₂, hcone_w⟩
  let j : pb1.cone.pt ⟶ (PreLogos.bottom G).dom := invpb.lift cone_xS ≫ jw
  have hN_le : N.le (PreLogos.bottom (image x).dom) := cover_from_zero_le N pb1.cone.π₂ hcov j
  exact Subobject.le_trans (inter_le_swap S (image x)) (inter_le_bottom_of_invImage (image x) S hN_le)

/-! ## §1.751  Atomically based ⇒ boolean -/

/-- **§1.751**: an ATOMICALLY BASED logos with arbitrary subobject joins is BOOLEAN —
    every subobject `S ⊆ A` is complemented.

    Freyd's complement: `¬S = ⊔ { image(x) | G atom, x : G → A, x ∤ S }`, the indexed
    join (`HasIndexedSubobjectJoins.sup`) of all atom-images not factoring through `S`.

    * **(1) `S ∩ ¬S = 0`.**  By the FRAME LAW, `S.arr# (¬S) = ⊔ { S.arr# (image x) }`;
      each `image x` in the family is disjoint from `S` by `atom_image_disjoint` (atomicity
      forces `x# S = 0` since `x ∤ S`), so every joinand `S.arr# (image x) ≤ 0`, hence
      `S.arr# (¬S) ≤ 0`, hence `S ∩ ¬S ≤ 0` (bridge lemmas).
    * **(2) `S ∪ ¬S = A`.**  If `S ∪ ¬S` were proper, `IsBasis` yields an atom `G` and
      `x : G → A` not factoring through `S ∪ ¬S`.  Then `x ∤ S` (else `x` would factor
      through `S ≤ S ∪ ¬S`), so `image x` is in the family and `image x ≤ ¬S ≤ S ∪ ¬S`;
      but `x` factors through `image x`, so `x` factors through `S ∪ ¬S` — contradiction.

    **Faithful complement predicate.**  The conclusion uses `IsComplementedSub` (§1.62:
    `S ∩ ¬S ≤ 0` and `A ≤ S ∪ ¬S`), the genuine book definition — NOT the S1_64 placeholder
    `IsComplemented`, which demands NO common lower bound *including* `0` and is therefore
    unsatisfiable in any pre-logos (`bottom` is below both `S` and any `¬S`).

    **Required structure.**  Beyond `AtomicallyBased`, the proof needs
    `HasIndexedSubobjectJoins` — arbitrary small joins of subobjects PLUS the frame law
    `invImage_preserves_sup` (inverse image preserves arbitrary joins).  The frame law is
    the §1.84 `PullbacksPreserveArbitraryUnions` / infinite distributive law and is NOT
    available from `PreLogos` (which preserves only binary unions); it is supplied by the
    `HasIndexedSubobjectJoins` instance, mirroring §1.712 (`LocallyComplete` +
    union-preservation = logos) and the Giraud §1.84 `pullback_union` field. -/
theorem atomicallyBased_isComplementedSub [PreLogos 𝒞] [HasIndexedSubobjectJoins 𝒞]
    (h : AtomicallyBased (𝒞 := 𝒞)) :
    ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplementedSub S := by
  intro A S
  -- ¬S = join of all atom-images not factoring through S
  let F : Subobject 𝒞 A → Prop :=
    fun T => ∃ (G : 𝒞), IsAtom G ∧ ∃ (x : G ⟶ A), (¬ Allows S x) ∧ T = image x
  refine ⟨sup F, ?_, ?_⟩
  · -- (1) S ∩ ¬S ≤ 0, via the frame law + per-joinand disjointness.
    apply inter_le_bottom_of_invImage S (sup F)
    have hframe := invImage_preserves_sup S.arr F
    have hbound : (sup (fun A' => ∃ M, F M ∧ A' = InverseImage S.arr M)).le
        (PreLogos.bottom S.dom) := by
      apply sup_least
      rintro s ⟨M, ⟨G, hG, x, hx, rfl⟩, rfl⟩
      exact invImage_le_bottom_of_inter S (image x) (atom_image_disjoint hG x S hx)
    exact Subobject.le_trans hframe hbound
  · -- (2) A ≤ S ∪ ¬S: a missing atom-element would land in image(x) ≤ ¬S, contradiction.
    let U := HasSubobjectUnions.union S (sup F)
    apply Classical.byContradiction
    intro hcon
    have hnotiso : ¬ IsIso U.arr := by
      intro hiso
      obtain ⟨inv, _, hinv2⟩ := hiso
      exact hcon ⟨inv, by
        show inv ≫ U.arr = (Subobject.entire A).arr
        rw [hinv2]; rfl⟩
    obtain ⟨G, hG, x, hx⟩ := h.2 U.arr U.monic hnotiso
    have hxS : ¬ Allows S x := by
      rintro ⟨y, hy⟩
      obtain ⟨l, hl⟩ := HasSubobjectUnions.union_left S (sup F)
      exact hx ⟨y ≫ l, by rw [Cat.assoc, hl, hy]⟩
    have h1 : (image x).le (sup F) := sup_upper F (image x) ⟨G, hG, x, hxS, rfl⟩
    obtain ⟨r, hr⟩ := HasSubobjectUnions.union_right S (sup F)
    obtain ⟨a, ha⟩ := image_allows x
    obtain ⟨b, hb⟩ := h1
    refine hx ⟨a ≫ b ≫ r, ?_⟩
    calc (a ≫ b ≫ r) ≫ U.arr = a ≫ (b ≫ (r ≫ U.arr)) := by rw [Cat.assoc, Cat.assoc]
      _ = a ≫ (b ≫ (sup F).arr) := by rw [hr]
      _ = a ≫ (image x).arr := by rw [hb]
      _ = x := ha

/-! ## §1.751  Periodic-power / reduction-to-atomless (recorded MISSING)

  The remainder of §1.751 reduces the Stone theorem to the ATOMLESS case via the
  PERIODIC POWER `℘A` (periodic functions ℕ → A), a sublogos of `A^ℕ` with a
  faithful diagonal representation `A → ℘A` that is atomless whenever `A` is
  non-degenerate.  Faithfully stating this needs:
    * countable powers `A^ℕ` and the sublogos of periodic sequences,
    * the diagonal representation and its faithfulness,
    * preservation of "positive & capital".
  None of this infrastructure exists in the repo, so it is NOT emitted as Lean
  here (no vacuous stub).  See S1_75.md.

  §1.752–§1.755 (the Stone space 𝒮(ℬ), the stalk/sheaf functor `T : A → 𝓜(X)`,
  the two characterizing properties, and the descent to faithfulness) are likewise
  recorded MISSING in S1_75.md: they require Stone-space/ultra-filter/sheaf
  machinery outside this repo's category-theoretic core.
-/

-- BOOK §1.753: If X ⊂ B̂ is such that T: A → H(X) is faithful, then T is a faithful
-- representation of logoi.
-- (Proof: T a pre-logos repr, T faithful + basis property [1.752(2)] ⟹ T preserves
-- double-sharps, hence a logos representation.)
-- OPEN: needs (1) Stone space B̂ of the boolean algebra B of complemented subterminators
--   (not in repo: `S1_38.lean` has only an `opaque StoneSpace` placeholder), (2) the
--   stalk/sheaf functor `T : A → H(X)` for X ⊂ B̂, (3) the basis property §1.752(2)
--   (every morphism of A is detected by some stalk), (4) `H(X)` as a category of sheaves
--   on X, (5) a `LogosMap` predicate (absent — see S1_72.lean ~line 449).

-- BOOK §1.754: If X = B̂ then T is faithful [1.635] and A → H(B̂) is a representation
-- of logoi.
-- OPEN: same infra as §1.753 plus the faithfulness from §1.635 (ultra-filter stalk
--   functors, INFRA-BLOCKED in S1_62.lean §1.635 block).

end Freyd
