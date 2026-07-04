/-
  Freyd & Scedrov, *Categories and Allegories* §1.93  The slice lemma — step 2.

  SLICE POWER OBJECTS ⟹ `Topos (Over B)`.

  Step 1 (`Fredy/SliceTopos.lean`) built the slice subobject classifier `Δ(Ω)`.
  This file builds the remaining ingredient of `Topos (Over B)`:

      instance overHasPowerObject (B : 𝒞) [Topos 𝒞] (C : Over B) : HasPowerObject C

  and assembles `instance overTopos (B : 𝒞) [Topos 𝒞] : Topos (Over B)`.

  Construction (Freyd §1.93, slice lemma).  A binary relation `R : BinRel (Over B) Z C`
  is a jointly-monic slice span `Z ← T → C`.  The forgetful `Σ = SliceForget`
  carries it to a jointly-monic *base* span `Σ Z ← Σ T → Σ C` (Σ preserves joint
  monicity: §1.531, Σ faithful + preserves/reflects monos), i.e. a base relation
  `BinRel 𝒞 (Σ Z) (Σ C)`.  Conversely a base relation over `(Σ Z, Σ C)` whose
  columns respect the structure maps to `B` lifts back into the slice.  Under this
  correspondence the SLICE membership relation is the Σ-transport of the BASE
  membership `∈_{Σ C}` of the base power object `[Σ C]`, placed on the slice object
  `Δ([Σ C]) = ⟨[Σ C] × B, snd⟩`.

  The first object `Δ[Σ C]` is only WEAKLY universal — classifiers EXIST but are not
  unique (a name's cross-fibre membership is invisible to a tight slice relation).
  Freyd's §1.93 fix (this file): pass to the idempotent-split sub-object
  `[C] = slicePowObj' B C ⊆ Δ[Σ C]`, the equalizer of `1` and the fibre-restriction
  idempotent `e = pair ρ snd` (`ρ = Λ(∈ ∩ same-fibre)`).  Cross-fibre names are exactly
  those `e` kills, so on `[C]` classifiers ARE unique: `sliceMem' = ι*(sliceMem)` is
  genuinely universal (`is_universal_sliceMem'`).  Both halves reduce to BASE
  universality of `∈_{Σ C}` (the only place uniqueness genuinely holds), via the
  e-fixedness lemma `baseRho_fixes_tight` and `sigmaRel (sliceMem) ≅ baseRestrict`.

  ADDITIVE: a new file built only from base power objects + Σ-transport + the §1.429
  idempotent-split (equalizers); NO new axioms, NO Chapter-2 allegory axioms.
-/

import Fredy.S1_9
import Fredy.S1_44
import Fredy.S1_92
import Fredy.S1_53_SliceRegular
import Fredy.S1_93_SliceTopos

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

open HasSubobjectClassifier

/-- **Generic `RelHom` transitivity** over ANY category `𝒟` (no `Topos`/products
    needed).  Used for `Over B` relations while building `Topos (Over B)` (the library
    `RelHom_trans` bakes in `[Topos 𝒞]`, which would be circular here). -/
theorem relHom_trans_gen {𝒟 : Type u} [Cat.{v} 𝒟] {X Y : 𝒟} {R S T : BinRel 𝒟 X Y}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨a, haA, haB⟩ := h₁
  obtain ⟨b, hbA, hbB⟩ := h₂
  exact ⟨a ≫ b, by rw [Cat.assoc, hbA, haA], by rw [Cat.assoc, hbB, haB]⟩

/-! ## Σ-transport of binary relations

  Σ : Over B → 𝒞 preserves and reflects joint monicity of column pairs (it is
  faithful and preserves/reflects monos), so it carries a slice relation to a base
  relation on the underlying objects. -/

/-- **Σ preserves joint monicity.**  If `colA, colB : T ⟶ X, Y` are jointly monic
    in `Over B` then their underlying arrows are jointly monic in `𝒞`. -/
theorem sigma_preserves_monicPair {B : 𝒞} {T X Y : Over B}
    {colA : T ⟶ X} {colB : T ⟶ Y}
    (h : MonicPair colA colB) : MonicPair colA.f colB.f := by
  intro W p q hA hB
  -- lift p, q to slice arrows W' ⟶ T over the structure map p ≫ T.hom.
  let W' : Over B := ⟨W, p ≫ T.hom⟩
  have hqw : q ≫ T.hom = p ≫ T.hom := by
    -- p ≫ colA.f ≫ X.hom = p ≫ T.hom (colA.w), similarly q; use hA.
    have hp : p ≫ T.hom = (p ≫ colA.f) ≫ X.hom := by rw [Cat.assoc, colA.w]
    have hq : q ≫ T.hom = (q ≫ colA.f) ≫ X.hom := by rw [Cat.assoc, colA.w]
    rw [hp, hq, hA]
  let pO : OverHom W' T := ⟨p, rfl⟩
  let qO : OverHom W' T := ⟨q, hqw⟩
  have hAO : pO ⊚ colA = qO ⊚ colA := OverHom.ext hA
  have hBO : pO ⊚ colB = qO ⊚ colB := OverHom.ext hB
  exact congrArg OverHom.f (h pO qO hAO hBO)

/-- **Σ-transport of a slice relation** to a base relation on the underlying objects. -/
def sigmaRel {B : 𝒞} {Z C : Over B} (R : BinRel (Over B) Z C) :
    BinRel 𝒞 Z.dom C.dom where
  src := R.src.dom
  colA := R.colA.f
  colB := R.colB.f
  isMonicPair := sigma_preserves_monicPair R.isMonicPair

/-! ## §1.93  The slice power object `Δ([Σ C])`

  For `C : Over B`, the slice power object is `Δ([Σ C]) = ⟨[Σ C] × B, snd⟩`, where
  `[Σ C] = powerObj (C := C.dom)` is the BASE power object of the underlying object.

  The slice membership relation `∈_C^{Over B}` is the lift of the base membership
  `∈_{Σ C} : BinRel 𝒞 [Σ C] C.dom` into the slice: its source carries the structure
  map `mem.colB ≫ C.hom : mem.src → B`, the `Δ[Σ C]`-column is
  `pair mem.colA (mem.colB ≫ C.hom)`, and the `C`-column is `mem.colB`. -/

variable [Topos 𝒞]

/-- The base power object of the underlying object of `C : Over B`. -/
noncomputable def slicePowBase (B : 𝒞) (C : Over B) : 𝒞 :=
  HasPowerObject.powerObj (C := C.dom)

/-- The slice power object `Δ([Σ C]) = ⟨[Σ C] × B, snd⟩ : Over B`. -/
noncomputable def slicePowObj (B : 𝒞) (C : Over B) : Over B :=
  ⟨prod (slicePowBase B C) B, snd⟩

/-- The base membership relation of `[Σ C]`. -/
noncomputable def baseMem (B : 𝒞) (C : Over B) : BinRel 𝒞 (slicePowBase B C) C.dom :=
  HasPowerObject.mem (C := C.dom)

/-- The source slice object of the slice membership relation: the base `mem`-source,
    equipped with structure map `mem.colB ≫ C.hom : mem.src → B`. -/
noncomputable def sliceMemSrc (B : 𝒞) (C : Over B) : Over B :=
  ⟨(baseMem B C).src, (baseMem B C).colB ≫ C.hom⟩

/-- `Δ[Σ C]`-column of the slice membership relation. -/
noncomputable def sliceMemColA (B : 𝒞) (C : Over B) :
    OverHom (sliceMemSrc B C) (slicePowObj B C) :=
  ⟨pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom), by
    show pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom) ≫ snd = (baseMem B C).colB ≫ C.hom
    rw [snd_pair]⟩

/-- `C`-column of the slice membership relation. -/
noncomputable def sliceMemColB (B : 𝒞) (C : Over B) :
    OverHom (sliceMemSrc B C) C :=
  ⟨(baseMem B C).colB, rfl⟩

/-- The slice membership relation `∈_C^{Over B} : BinRel (Over B) (Δ[Σ C]) C`. -/
noncomputable def sliceMem (B : 𝒞) (C : Over B) :
    BinRel (Over B) (slicePowObj B C) C where
  src := sliceMemSrc B C
  colA := sliceMemColA B C
  colB := sliceMemColB B C
  isMonicPair := by
    -- jointly monic in Over B: reflected from base joint monicity of the columns.
    -- The base columns are `pair mem.colA (mem.colB ≫ C.hom)` and `mem.colB`; the
    -- second is already part of a base-monic pair `(mem.colA, mem.colB)`, and the
    -- first packs `mem.colA`.  So the pair is base-jointly-monic, then reflect.
    intro W p q hA hB
    apply OverHom.ext
    -- on base arrows: p.f ≫ colA.f = q.f ≫ colA.f and p.f ≫ colB.f = q.f ≫ colB.f.
    have hAf : p.f ≫ (sliceMemColA B C).f = q.f ≫ (sliceMemColA B C).f :=
      congrArg OverHom.f hA
    have hBf : p.f ≫ (sliceMemColB B C).f = q.f ≫ (sliceMemColB B C).f :=
      congrArg OverHom.f hB
    -- recover base colA agreement by post-composing with `fst`.
    have hcolA : p.f ≫ (baseMem B C).colA = q.f ≫ (baseMem B C).colA := by
      have := congrArg (· ≫ fst) hAf
      simpa [sliceMemColA, Cat.assoc, fst_pair] using this
    have hcolB : p.f ≫ (baseMem B C).colB = q.f ≫ (baseMem B C).colB := hBf
    exact (baseMem B C).isMonicPair p.f q.f hcolA hcolB

/-! ## §1.93  Universality of the slice membership relation

  The Δ–Σ adjunction: a slice map `f : A ⟶ Δ[Σ C]` is exactly `⟨pair g A.hom, …⟩`
  for a unique base map `g : A.dom ⟶ [Σ C]` (`g = f.f ≫ fst`).  Under this
  correspondence, `relPullback_{Over B} f (sliceMem B C)` Σ-transports to
  `relPullback_{𝒞} g (baseMem B C)`, and a slice `RelHom` is a base `RelHom`
  respecting the structure maps; so slice universality of `sliceMem` reduces to
  base universality of `baseMem` (`Topos.has_pow`). -/

/-- The base classifying map extracted from a slice map into `Δ[Σ C]`. -/
noncomputable def deSigmaClassify {B : 𝒞} {A C : Over B}
    (f : OverHom A (slicePowObj B C)) : A.dom ⟶ slicePowBase B C :=
  f.f ≫ fst

/-- **Σ commutes with `relPullback`.**  Σ-transporting the slice pullback of a
    relation `U` along `f` gives the base pullback of `Σ U` along `Σ f = f.f`.
    Both sides are the same base relation on the nose (Σ preserves the chosen
    pullback, `sigma_preserves_pullback_*`). -/
theorem sigmaRel_relPullback {B : 𝒞} {P C A : Over B}
    (f : A ⟶ P) (U : BinRel (Over B) P C) :
    sigmaRel (relPullback f U) = relPullback f.f (sigmaRel U) := rfl

/-- **Σ on RelHoms (covariant).**  A slice `RelHom R S` yields a base
    `RelHom (sigmaRel R) (sigmaRel S)` by taking the witness's underlying arrow. -/
theorem sigmaRel_relHom {B : 𝒞} {Z C : Over B} {R S : BinRel (Over B) Z C}
    (h : RelHom R S) : RelHom (sigmaRel R) (sigmaRel S) := by
  obtain ⟨k, hA, hB⟩ := h
  exact ⟨k.f, congrArg OverHom.f hA, congrArg OverHom.f hB⟩

/-- The base relation `sigmaRel (sliceMem B C)`: source `mem.src`, A-column
    `pair mem.colA (mem.colB ≫ C.hom) : mem.src ⟶ [Σ C] × B`, B-column `mem.colB`. -/
theorem sigmaRel_sliceMem_colA (B : 𝒞) (C : Over B) :
    (sigmaRel (sliceMem B C)).colA
      = pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom) := rfl

theorem sigmaRel_sliceMem_colB (B : 𝒞) (C : Over B) :
    (sigmaRel (sliceMem B C)).colB = (baseMem B C).colB := rfl

/-- **Forgetful bridge (easy direction).**  The Σ-transport of the slice pullback
    `relPullback f (sliceMem)` maps (as a base relation) into the base pullback
    `relPullback (f.f ≫ fst) (baseMem)`: a slice-membership point already satisfies
    the looser base-membership constraint (`fst` of the `pair`-cospan).  Hence any
    base `RelHom S (sigmaRel (relPullback f (sliceMem)))` composes into a base
    `RelHom S (relPullback (f.f ≫ fst) (baseMem))`. -/
theorem relHom_baseMem_of_sigmaRel_sliceMem {B : 𝒞} {A C : Over B}
    (f : OverHom A (slicePowObj B C)) :
    RelHom (sigmaRel (relPullback f (sliceMem B C)))
      (relPullback (f.f ≫ fst) (baseMem B C)) := by
  -- sigmaRel (relPullback f (sliceMem)) = relPullback f.f (sigmaRel (sliceMem))  (rfl).
  -- Its source is the base pullback of  f.f  and  pair mem.colA (mem.colB ≫ C.hom).
  -- The target is the base pullback of  f.f ≫ fst  and  mem.colA.
  -- A point of the former satisfies  aleg ≫ f.f = mleg ≫ pair mem.colA (mem.colB≫hom);
  -- post-compose fst:  aleg ≫ (f.f ≫ fst) = mleg ≫ mem.colA, giving the looser cone,
  -- whose lift is the witness.
  -- the source pullback cone (of f.f and pair mem.colA (mem.colB ≫ C.hom))
  let pb1 := HasPullbacks.has f.f (sigmaRel (sliceMem B C)).colA
  let pb2 := HasPullbacks.has (f.f ≫ fst) (baseMem B C).colA
  -- cone over (f.f ≫ fst, mem.colA) with apex pb1.pt, legs π₁, π₂.
  have hw : pb1.cone.π₁ ≫ (f.f ≫ fst) = pb1.cone.π₂ ≫ (baseMem B C).colA := by
    have := congrArg (· ≫ fst) pb1.cone.w
    -- this : (π₁ ≫ f.f) ≫ fst = (π₂ ≫ pair mem.colA (mem.colB≫hom)) ≫ fst
    simpa [sigmaRel_sliceMem_colA, Cat.assoc, fst_pair] using this
  let cone1 : Cone (f.f ≫ fst) (baseMem B C).colA := ⟨pb1.cone.pt, pb1.cone.π₁, pb1.cone.π₂, hw⟩
  refine ⟨pb2.lift cone1, ?_, ?_⟩
  · -- colA: witness ≫ pb2.π₁ = pb1.π₁
    exact pb2.lift_fst cone1
  · -- colB: witness ≫ (pb2.π₂ ≫ mem.colB) = pb1.π₂ ≫ mem.colB
    show pb2.lift cone1 ≫ (pb2.cone.π₂ ≫ (baseMem B C).colB)
        = pb1.cone.π₂ ≫ (baseMem B C).colB
    rw [← Cat.assoc, pb2.lift_snd cone1]

/-- **Naturality / structure-tight bridge (hard direction).**  For a slice relation
    `R : BinRel (Over B) A C` and a base RelHom `j : sigmaRel R ⟶ relPullback g (baseMem)`
    (with `g : A.dom ⟶ [Σ C]`), the B-leg constraint of the *tight* slice pullback is
    automatic: every point of `sigmaRel R` satisfies
    `colA ≫ A.hom = colB ≫ C.hom` because `R`'s columns are over-homs
    (`R.colA.w`, `R.colB.w` both equal `R.src.hom`).  This is what makes
    `relPullback g (baseMem)` and the Σ-image of the slice pullback agree on the
    image of `R`, i.e. supplies the §1.93 second isomorphism on the relevant subobject. -/
theorem sigmaRel_struct {B : 𝒞} {A C : Over B} (R : BinRel (Over B) A C) :
    R.colA.f ≫ A.hom = R.colB.f ≫ C.hom := by
  rw [R.colA.w, R.colB.w]


/-- **Σ is full on relations.**  A base `RelHom (sigmaRel S) (sigmaRel R)` lifts to a
    slice `RelHom S R`: its witness `w` is automatically a slice over-hom because
    `w ≫ R.src.hom = w ≫ R.colA.f ≫ A.hom = S.colA.f ≫ A.hom = S.src.hom`
    (over-hom laws `R.colA.w`, `S.colA.w`). -/
theorem sliceRelHom_of_sigmaRel {B : 𝒞} {A C : Over B} {S R : BinRel (Over B) A C}
    (j : RelHom (sigmaRel S) (sigmaRel R)) : RelHom S R := by
  obtain ⟨w, hA, hB⟩ := j
  have hA' : w ≫ R.colA.f = S.colA.f := hA
  have hw : w ≫ R.src.hom = S.src.hom := by
    rw [← R.colA.w, ← Cat.assoc, hA', S.colA.w]
  exact ⟨⟨w, hw⟩, OverHom.ext hA, OverHom.ext hB⟩

/-- The slice classifier built from a base map `g : A.dom ⟶ [Σ C]`. -/
noncomputable def sliceClassifyOf {B : 𝒞} (A C : Over B) (g : A.dom ⟶ slicePowBase B C) :
    OverHom A (slicePowObj B C) :=
  ⟨pair g A.hom, by
    show pair g A.hom ≫ snd = A.hom
    rw [snd_pair]⟩

@[simp] theorem sliceClassifyOf_fst {B : 𝒞} (A C : Over B) (g : A.dom ⟶ slicePowBase B C) :
    (sliceClassifyOf A C g).f ≫ fst = g := by
  show pair g A.hom ≫ fst = g; rw [fst_pair]

/-- **The §1.93 lift (hard reusable direction).**  Given two slice relations
    `R, S : BinRel (Over B) A C` over the same `A, C`, with `S`'s Σ-image carrying a
    base RelHom `j : sigmaRel R ⟶ relPullback g (baseMem)` AND the structure
    compatibility `S.colA.f ≫ A.hom = S.colB.f ≫ C.hom` recoverable, the
    base witness lifts to the slice.

  We use it with `S := relPullback (sliceClassifyOf A C g) (sliceMem B C)`.  Concretely:
  given a base RelHom `j : sigmaRel R ⟶ relPullback g (baseMem B C)`, produce a slice
  RelHom `R ⟶ relPullback (sliceClassifyOf A C g) (sliceMem B C)`.  The slice pullback
  source's underlying object is the base pullback of `pair g A.hom` and
  `pair mem.colA (mem.colB ≫ C.hom)`; the cone legs are `R.colA.f` and `j ≫ π₂`, whose
  B-leg agreement is `sigmaRel_struct R`. -/
theorem sliceRelHom_of_baseRelHom {B : 𝒞} {A C : Over B}
    (R : BinRel (Over B) A C) (g : A.dom ⟶ slicePowBase B C)
    (j : RelHom (sigmaRel R) (relPullback g (baseMem B C))) :
    RelHom R (relPullback (sliceClassifyOf A C g) (sliceMem B C)) := by
  obtain ⟨jw, hjA, hjB⟩ := j
  let f := sliceClassifyOf A C g
  -- base pullback of g and mem.colA (the target relation's source).
  let pbg := HasPullbacks.has g (baseMem B C).colA
  -- jw : R.src.dom ⟶ pbg.cone.pt, with jw ≫ π₁ = R.colA.f, jw ≫ (π₂ ≫ mem.colB) = R.colB.f.
  have hjA' : jw ≫ pbg.cone.π₁ = R.colA.f := hjA
  have hjB' : jw ≫ (pbg.cone.π₂ ≫ (baseMem B C).colB) = R.colB.f := hjB
  -- the slice mem-source map `mlift : R.src ⟶ sliceMemSrc B C`, underlying `jw ≫ π₂`.
  -- R.colA.f ≫ g = (jw ≫ π₂) ≫ mem.colA  (fst-component of the cone square).
  have hfst : R.colA.f ≫ g = (jw ≫ pbg.cone.π₂) ≫ (baseMem B C).colA := by
    rw [← hjA', Cat.assoc, Cat.assoc, pbg.cone.w]
  -- R.colA.f ≫ A.hom = (jw ≫ π₂) ≫ (mem.colB ≫ C.hom)  (snd-component).
  have hsnd : R.colA.f ≫ A.hom = (jw ≫ pbg.cone.π₂) ≫ ((baseMem B C).colB ≫ C.hom) := by
    rw [sigmaRel_struct R, Cat.assoc, ← Cat.assoc pbg.cone.π₂, ← Cat.assoc jw, hjB']
  have hmw : (jw ≫ pbg.cone.π₂) ≫ ((baseMem B C).colB ≫ C.hom) = R.src.hom := by
    rw [← hsnd, R.colA.w]
  let mlift : OverHom R.src (sliceMemSrc B C) := ⟨jw ≫ pbg.cone.π₂, hmw⟩
  -- the cone square in Over B: R.colA ⊚ f = mlift ⊚ sliceMemColA.
  have hsq : R.colA ⊚ f = mlift ⊚ sliceMemColA B C := by
    apply OverHom.ext
    -- base: R.colA.f ≫ pair g A.hom = (jw ≫ π₂) ≫ pair mem.colA (mem.colB ≫ C.hom).
    show R.colA.f ≫ pair g A.hom
        = (jw ≫ pbg.cone.π₂) ≫ pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom)
    have hL : R.colA.f ≫ pair g A.hom = pair (R.colA.f ≫ g) (R.colA.f ≫ A.hom) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have hR : (jw ≫ pbg.cone.π₂) ≫ pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom)
        = pair ((jw ≫ pbg.cone.π₂) ≫ (baseMem B C).colA)
              ((jw ≫ pbg.cone.π₂) ≫ ((baseMem B C).colB ≫ C.hom)) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    rw [hL, hR, hfst, hsnd]
  -- the slice lift k : R.src ⟶ relPullback f (sliceMem) .src.
  let k := overPullbackLift f (sliceMem B C).colA R.colA mlift hsq
  refine ⟨k, ?_, ?_⟩
  · -- colA: k ⊚ overPullbackπ₁ = R.colA.
    exact OverHom.ext ((HasPullbacks.has f.f ((sliceMem B C).colA).f).lift_fst _)
  · -- colB: k ⊚ (overPullbackπ₂ ⊚ sliceMem.colB) = R.colB.
    apply OverHom.ext
    -- on base: k.f ≫ (overPullbackπ₂.f ≫ sliceMem.colB.f) = R.colB.f.
    show k.f ≫ ((overPullbackπ₂ f (sliceMem B C).colA).f ≫ (sliceMem B C).colB.f) = R.colB.f
    have hk₂ : k ⊚ overPullbackπ₂ f (sliceMem B C).colA = mlift :=
      OverHom.ext ((HasPullbacks.has f.f ((sliceMem B C).colA).f).lift_snd _)
    have hk₂f : k.f ≫ (overPullbackπ₂ f (sliceMem B C).colA).f = jw ≫ pbg.cone.π₂ :=
      congrArg OverHom.f hk₂
    rw [← Cat.assoc, hk₂f]
    show (jw ≫ pbg.cone.π₂) ≫ (baseMem B C).colB = R.colB.f
    rw [Cat.assoc]; exact hjB'

/-! ## §1.93 universality — existence against the weak `Δ[ΣC]`

  The weak slice membership `sliceMem B C` on `Δ[ΣC]` is universal for EXISTENCE but
  NOT uniqueness (uniqueness is genuinely FALSE for a general `C`: a name's
  cross-fibre membership is invisible to a tight slice relation, so two names agreeing
  on the same-fibre part but differing cross-fibre classify the same `R`).  Freyd's
  fix (§1.93) restricts to the idempotent-split subobject `[C] ⊆ Δ[ΣC]`; we build that
  below (`slicePowObj'`/`sliceMem'`/`is_universal_sliceMem'`) and wire `Topos (Over B)`
  to it.  The weak `sliceMem` survives only as the reusable existence engine
  `sliceMem_classify_of`. -/

/-- **Reusable existence half (against `Δ[ΣC]`).**  For any base map
    `g : A.dom ⟶ [ΣC]` whose membership-pullback `relPullback g (baseMem)`
    re-presents `sigmaRel R`, the slice classifier `sliceClassifyOf A C g`
    presents `R` against the weak slice membership `sliceMem`. -/
theorem sliceMem_classify_of {B : 𝒞} {A C : Over B} (R : BinRel (Over B) A C)
    (g : A.dom ⟶ slicePowBase B C)
    (hgf : RelHom (sigmaRel R) (relPullback g (baseMem B C)))
    (hgr : RelHom (relPullback g (baseMem B C)) (sigmaRel R)) :
    RelHom R (relPullback (sliceClassifyOf A C g) (sliceMem B C)) ∧
    RelHom (relPullback (sliceClassifyOf A C g) (sliceMem B C)) R := by
  refine ⟨sliceRelHom_of_baseRelHom R g hgf, ?_⟩
  apply sliceRelHom_of_sigmaRel
  have hgr' : RelHom (relPullback ((sliceClassifyOf A C g).f ≫ fst) (baseMem B C))
      (sigmaRel R) := by rw [sliceClassifyOf_fst]; exact hgr
  exact RelHom_trans (relHom_baseMem_of_sigmaRel_sliceMem (sliceClassifyOf A C g)) hgr'

/-! ## §1.93  The genuine slice power object via idempotent split -/

variable {B : 𝒞}

/-- The "membership" base relation `fst*(∈_{ΣC}) : ([ΣC]×B) → C.dom`:
    `((P,b),c)` with `(P,c) ∈ ∈_{ΣC}` (ignoring `b`). -/
noncomputable def baseMemPB (B : 𝒞) (C : Over B) :
    BinRel 𝒞 (prod (slicePowBase B C) B) C.dom :=
  relPullback (fst : prod (slicePowBase B C) B ⟶ slicePowBase B C) (baseMem B C)

/-- The "same-fibre" base relation `R_fib : ([ΣC]×B) → C.dom`: `((P,b),c)` with
    `b = C.hom c`.  Tabulated by the pullback of `snd` and `C.hom`; its projection
    legs are jointly monic (pullback uniqueness). -/
noncomputable def baseFib (B : 𝒞) (C : Over B) :
    BinRel 𝒞 (prod (slicePowBase B C) B) C.dom where
  src  := (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).cone.pt
  colA := (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).cone.π₁
  colB := (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).cone.π₂
  isMonicPair := by
    intro W f g hA hB
    let pb := HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom
    have hw : (f ≫ pb.cone.π₁) ≫ snd = (f ≫ pb.cone.π₂) ≫ C.hom := by
      rw [Cat.assoc, Cat.assoc, pb.cone.w]
    have h1 : f = pb.lift ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw⟩ :=
      pb.lift_uniq ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw⟩ f rfl rfl
    have h2 : g = pb.lift ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw⟩ :=
      pb.lift_uniq ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw⟩ g hA.symm hB.symm
    rw [h1, h2]

/-- Base-level "restricted membership": `((P,b),c)` with `(P,c) ∈ ∈_{ΣC}` AND
    `b = C.hom c` (same B-fibre).  `= fst*(∈_{ΣC}) ⊓ R_fib`. -/
noncomputable def baseRestrict (B : 𝒞) (C : Over B) :
    BinRel 𝒞 (prod (slicePowBase B C) B) C.dom :=
  baseMemPB B C ⊓ baseFib B C

/-- Base universality of `∈_{ΣC}`. -/
noncomputable def hbase (B : 𝒞) (C : Over B) : IsUniversalRel (baseMem B C) :=
  HasPowerObject.is_universal (C := C.dom)

/-- The fibre-restriction map `ρ : [ΣC]×B → [ΣC]`: classifies `baseRestrict`. -/
noncomputable def baseRho (B : 𝒞) (C : Over B) :
    prod (slicePowBase B C) B ⟶ slicePowBase B C :=
  univClassify (hbase B C) (baseRestrict B C)

/-- The base idempotent `ē = pair ρ snd : [ΣC]×B → [ΣC]×B`. -/
noncomputable def baseIdem (B : 𝒞) (C : Over B) :
    prod (slicePowBase B C) B ⟶ prod (slicePowBase B C) B :=
  pair (baseRho B C) snd

/-- `baseRestrict ≅ relPullback ρ (baseMem)` (the defining universal property of ρ). -/
theorem baseRestrict_iso_pullback (B : 𝒞) (C : Over B) :
    RelHom (baseRestrict B C) (relPullback (baseRho B C) (baseMem B C)) ∧
    RelHom (relPullback (baseRho B C) (baseMem B C)) (baseRestrict B C) :=
  univClassify_spec (hbase B C) (baseRestrict B C)

/-- Universal property of `relPullback` over `⊓`: if `T` lands in both `f*R` and
    `f*S` then it lands in `f*(R ⊓ S)`. -/
theorem le_relPullback_intersect {X A C : 𝒞} (f : X ⟶ A) {R S : BinRel 𝒞 A C}
    {T : BinRel 𝒞 X C}
    (hR : RelHom T (relPullback f R)) (hS : RelHom T (relPullback f S)) :
    RelHom T (relPullback f (R ⊓ S)) := by
  obtain ⟨wR, hwRA, hwRB⟩ := hR
  obtain ⟨wS, hwSA, hwSB⟩ := hS
  let PR := HasPullbacks.has f R.colA
  let PS := HasPullbacks.has f S.colA
  let PI := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  let PRS := HasPullbacks.has f (R ⊓ S).colA
  -- wR : T.src → PR.pt with wR≫π₁ = T.colA, wR≫(π₂≫R.colB) = T.colB.
  have hwRA' : wR ≫ PR.cone.π₁ = T.colA := hwRA
  have hwRB' : wR ≫ (PR.cone.π₂ ≫ R.colB) = T.colB := hwRB
  have hwSA' : wS ≫ PS.cone.π₁ = T.colA := hwSA
  have hwSB' : wS ≫ (PS.cone.π₂ ≫ S.colB) = T.colB := hwSB
  -- Build a cone into the meet table PI: legs (wR≫π₂ : T.src→R.src, wS≫π₂ : T.src→S.src).
  -- It is a valid cone over (pair R.colA R.colB, pair S.colA S.colB) because both encode
  -- the same (T.colA-image, T.colB) point.
  have hmeet : (wR ≫ PR.cone.π₂) ≫ pair R.colA R.colB
             = (wS ≫ PS.cone.π₂) ≫ pair S.colA S.colB := by
    -- both equal pair (wR≫π₁≫f) T.colB  via the cone squares and R,S.colA legs.
    have hRcolA : (wR ≫ PR.cone.π₂) ≫ R.colA = (wS ≫ PS.cone.π₂) ≫ S.colA := by
      -- = wR≫π₁≫f and wS≫π₁≫f, both = T.colA ≫ f.
      have e1 : (wR ≫ PR.cone.π₂) ≫ R.colA = wR ≫ PR.cone.π₁ ≫ f := by
        rw [Cat.assoc, ← PR.cone.w, ← Cat.assoc]
      have e2 : (wS ≫ PS.cone.π₂) ≫ S.colA = wS ≫ PS.cone.π₁ ≫ f := by
        rw [Cat.assoc, ← PS.cone.w, ← Cat.assoc]
      rw [e1, e2, ← Cat.assoc, ← Cat.assoc, hwRA', hwSA']
    have hRcolB : (wR ≫ PR.cone.π₂) ≫ R.colB = (wS ≫ PS.cone.π₂) ≫ S.colB := by
      rw [Cat.assoc, Cat.assoc, hwRB', hwSB']
    calc (wR ≫ PR.cone.π₂) ≫ pair R.colA R.colB
        = pair ((wR ≫ PR.cone.π₂) ≫ R.colA) ((wR ≫ PR.cone.π₂) ≫ R.colB) :=
          pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
      _ = pair ((wS ≫ PS.cone.π₂) ≫ S.colA) ((wS ≫ PS.cone.π₂) ≫ S.colB) := by
          rw [hRcolA, hRcolB]
      _ = (wS ≫ PS.cone.π₂) ≫ pair S.colA S.colB :=
          (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])).symm
  let cI : Cone (pair R.colA R.colB) (pair S.colA S.colB) :=
    ⟨T.src, wR ≫ PR.cone.π₂, wS ≫ PS.cone.π₂, hmeet⟩
  let m : T.src ⟶ PI.cone.pt := PI.lift cI
  -- m ≫ π₁ = wR≫π₂.  (R⊓S).colA = π₁ ≫ R.colA, .colB = π₁ ≫ R.colB.
  have hm1 : m ≫ PI.cone.π₁ = wR ≫ PR.cone.π₂ := PI.lift_fst cI
  -- Now build a cone over (f, (R⊓S).colA) with apex T.src: legs (T.colA, m).
  have hconeW : T.colA ≫ f = m ≫ (R ⊓ S).colA := by
    -- (R⊓S).colA = PI.π₁ ≫ R.colA.  m ≫ PI.π₁ ≫ R.colA = (wR≫π₂)≫R.colA = wR≫π₁≫f = T.colA≫f.
    show T.colA ≫ f = m ≫ (PI.cone.π₁ ≫ R.colA)
    rw [← Cat.assoc, hm1, Cat.assoc, ← PR.cone.w, ← Cat.assoc, hwRA']
  let cRS : Cone f (R ⊓ S).colA := ⟨T.src, T.colA, m, hconeW⟩
  refine ⟨PRS.lift cRS, PRS.lift_fst cRS, ?_⟩
  -- colB: lift ≫ (π₂ ≫ (R⊓S).colB) = T.colB.  (R⊓S).colB = PI.π₁ ≫ R.colB.
  show PRS.lift cRS ≫ (PRS.cone.π₂ ≫ (R ⊓ S).colB) = T.colB
  rw [← Cat.assoc, PRS.lift_snd cRS]
  show m ≫ (PI.cone.π₁ ≫ R.colB) = T.colB
  rw [← Cat.assoc, hm1, Cat.assoc, hwRB']

/-- `relPullback ē (fst*∈) ≅ baseRestrict` (both directions): pulling membership back
    along `ē = pair ρ snd` re-classifies it as `relPullback ρ ∈ ≅ baseRestrict`. -/
theorem relPullback_idem_memPB (B : 𝒞) (C : Over B) :
    RelHom (relPullback (baseIdem B C) (baseMemPB B C)) (baseRestrict B C) ∧
    RelHom (baseRestrict B C) (relPullback (baseIdem B C) (baseMemPB B C)) := by
  -- relPullback ē (relPullback fst baseMem) ≅ relPullback (ē ≫ fst) baseMem.
  obtain ⟨hc1, hc2⟩ := relPullback_comp (baseIdem B C)
    (fst : prod (slicePowBase B C) B ⟶ slicePowBase B C) (baseMem B C)
  -- ē ≫ fst = ρ, so relPullback (ē≫fst) baseMem = relPullback ρ baseMem.
  rw [show baseIdem B C ≫ fst = baseRho B C from fst_pair _ _] at hc1 hc2
  obtain ⟨hs1, hs2⟩ := baseRestrict_iso_pullback B C
  exact ⟨RelHom_trans hc1 hs2, RelHom_trans hs1 hc2⟩

/-- The fibre square of `R_fib`: `colA ≫ snd = colB ≫ C.hom`. -/
theorem baseFib_sq (B : 𝒞) (C : Over B) :
    (baseFib B C).colA ≫ snd = (baseFib B C).colB ≫ C.hom :=
  (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).cone.w

/-- Lift any cone `(a : T → [ΣC]×B, b : T → C.dom)` with `a ≫ snd = b ≫ C.hom`
    into `R_fib.src`. -/
noncomputable def baseFibLift {B : 𝒞} {C : Over B} {T : 𝒞}
    (a : T ⟶ prod (slicePowBase B C) B) (b : T ⟶ C.dom) (h : a ≫ snd = b ≫ C.hom) :
    T ⟶ (baseFib B C).src :=
  (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).lift ⟨T, a, b, h⟩

theorem baseFibLift_A {B : 𝒞} {C : Over B} {T : 𝒞}
    (a : T ⟶ prod (slicePowBase B C) B) (b : T ⟶ C.dom) (h : a ≫ snd = b ≫ C.hom) :
    baseFibLift a b h ≫ (baseFib B C).colA = a :=
  (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).lift_fst _

theorem baseFibLift_B {B : 𝒞} {C : Over B} {T : 𝒞}
    (a : T ⟶ prod (slicePowBase B C) B) (b : T ⟶ C.dom) (h : a ≫ snd = b ≫ C.hom) :
    baseFibLift a b h ≫ (baseFib B C).colB = b :=
  (HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom).lift_snd _

/-- `baseRestrict ⊂ relPullback ē (R_fib)`: the fibre constraint survives pullback
    along `ē` because `ē ≫ snd = snd` keeps the B-coordinate. -/
theorem baseRestrict_le_idem_fib (B : 𝒞) (C : Over B) :
    RelHom (baseRestrict B C) (relPullback (baseIdem B C) (baseFib B C)) := by
  -- baseRestrict ⊂ baseFib gives k with k≫colA = colA_R, k≫colB = colB_R.
  obtain ⟨⟨k, hkA, hkB⟩⟩ := intersect_le_right (baseMemPB B C) (baseFib B C)
  have hkA' : k ≫ (baseFib B C).colA = (baseRestrict B C).colA := hkA
  have hkB' : k ≫ (baseFib B C).colB = (baseRestrict B C).colB := hkB
  let P := HasPullbacks.has (baseIdem B C) (baseFib B C).colA
  -- the fibre point at the ē-image: (baseRestrict.colA ≫ ē, baseRestrict.colB).
  -- fibre square: (colA_R ≫ ē) ≫ snd = colA_R ≫ snd = colB_R ≫ C.hom.
  have hcfib : ((baseRestrict B C).colA ≫ baseIdem B C) ≫ snd
             = (baseRestrict B C).colB ≫ C.hom := by
    have h1 : (baseRestrict B C).colA ≫ snd = (baseRestrict B C).colB ≫ C.hom := by
      rw [← hkA', Cat.assoc, baseFib_sq, ← Cat.assoc, hkB']
    rw [Cat.assoc, show baseIdem B C ≫ snd = snd from snd_pair _ _]; exact h1
  let kfib := baseFibLift ((baseRestrict B C).colA ≫ baseIdem B C) (baseRestrict B C).colB hcfib
  have hkfibA : kfib ≫ (baseFib B C).colA = (baseRestrict B C).colA ≫ baseIdem B C :=
    baseFibLift_A _ _ _
  have hkfibB : kfib ≫ (baseFib B C).colB = (baseRestrict B C).colB :=
    baseFibLift_B _ _ _
  have hPw : (baseRestrict B C).colA ≫ baseIdem B C = kfib ≫ (baseFib B C).colA :=
    hkfibA.symm
  refine ⟨P.lift ⟨(baseRestrict B C).src, (baseRestrict B C).colA, kfib, hPw⟩,
    P.lift_fst _, ?_⟩
  show P.lift ⟨(baseRestrict B C).src, (baseRestrict B C).colA, kfib, hPw⟩
      ≫ (P.cone.π₂ ≫ (baseFib B C).colB) = (baseRestrict B C).colB
  rw [← Cat.assoc, P.lift_snd, hkfibB]

/-- **§1.93 idempotence**: `relPullback ē (baseRestrict) ≅ baseRestrict`. -/
theorem baseRestrict_idem_iso (B : 𝒞) (C : Over B) :
    RelHom (relPullback (baseIdem B C) (baseRestrict B C)) (baseRestrict B C) ∧
    RelHom (baseRestrict B C) (relPullback (baseIdem B C) (baseRestrict B C)) := by
  constructor
  · -- relPullback ē baseRestrict ⊂ relPullback ē baseMemPB ≅ baseRestrict.
    obtain ⟨hle⟩ := intersect_le_left (baseMemPB B C) (baseFib B C)
    have hmono : RelHom (relPullback (baseIdem B C) (baseRestrict B C))
        (relPullback (baseIdem B C) (baseMemPB B C)) :=
      relHom_pullback923 (baseIdem B C) hle
    exact RelHom_trans hmono (relPullback_idem_memPB B C).1
  · -- baseRestrict ⊂ relPullback ē baseMemPB  AND  ⊂ relPullback ē baseFib; combine.
    exact le_relPullback_intersect (baseIdem B C)
      (relPullback_idem_memPB B C).2 (baseRestrict_le_idem_fib B C)

/-- The base idempotent is idempotent: `ē ≫ ē = ē` (equivalently `ē ≫ ρ = ρ`). -/
theorem baseIdem_idem (B : 𝒞) (C : Over B) :
    baseIdem B C ≫ baseIdem B C = baseIdem B C := by
  -- ē ≫ ē = pair (ē ≫ ρ) (ē ≫ snd) = pair (ē ≫ ρ) snd; need ē ≫ ρ = ρ.
  have hρ : baseIdem B C ≫ baseRho B C = baseRho B C := by
    -- ē ≫ ρ = univClassify (relPullback ē baseRestrict) = univClassify baseRestrict = ρ.
    have hnat : univClassify (hbase B C) (relPullback (baseIdem B C) (baseRestrict B C))
              = baseIdem B C ≫ baseRho B C :=
      univClassify_natural (hbase B C) (baseRestrict B C) (baseIdem B C)
    have hsame : univClassify (hbase B C) (relPullback (baseIdem B C) (baseRestrict B C))
               = univClassify (hbase B C) (baseRestrict B C) :=
      (hbase B C).classify_unique _ _ _ _
        (univClassify_spec (hbase B C) _)
        ⟨RelHom_trans (baseRestrict_idem_iso B C).1 (univClassify_spec (hbase B C) (baseRestrict B C)).1,
         RelHom_trans (univClassify_spec (hbase B C) (baseRestrict B C)).2 (baseRestrict_idem_iso B C).2⟩
    rw [← hnat, hsame]; rfl
  -- conclude via pair calculus.
  show pair (baseRho B C) snd ≫ pair (baseRho B C) snd = pair (baseRho B C) snd
  rw [pair_uniq _ _ (pair (baseRho B C) snd ≫ pair (baseRho B C) snd) rfl rfl]
  congr 1
  · rw [Cat.assoc, fst_pair]; exact hρ
  · rw [Cat.assoc, snd_pair, snd_pair]

/-- The slice idempotent `e = ⟨ē, …⟩ : slicePowObj ⟶ slicePowObj` in `Over B`
    (`ē` preserves the structure map `snd`). -/
noncomputable def sliceIdem (B : 𝒞) (C : Over B) :
    slicePowObj B C ⟶ slicePowObj B C :=
  ⟨baseIdem B C, by show baseIdem B C ≫ snd = snd; exact snd_pair _ _⟩

theorem sliceIdem_idem (B : 𝒞) (C : Over B) :
    sliceIdem B C ≫ sliceIdem B C = sliceIdem B C :=
  OverHom.ext (baseIdem_idem B C)

/-! ## §1.93  The genuine slice power object `[C] = split(e) ⊆ Δ[ΣC]` -/

/-- The genuine slice power object `[C]`: the equalizer of `e` and `id` in `Over B`
    (the split image of the idempotent `e`). -/
noncomputable def slicePowObj' (B : 𝒞) (C : Over B) : Over B :=
  eqObj (sliceIdem B C) (Cat.id (slicePowObj B C))

/-- The mono `ι : [C] ⟶ Δ[ΣC]` (the equalizer map / idempotent section). -/
noncomputable def sliceIota (B : 𝒞) (C : Over B) : slicePowObj' B C ⟶ slicePowObj B C :=
  eqMap (sliceIdem B C) (Cat.id (slicePowObj B C))

/-- `ι ≫ e = ι` (the equalizer equation, since `ι` equalizes `e` and `id`). -/
theorem sliceIota_idem (B : 𝒞) (C : Over B) :
    sliceIota B C ≫ sliceIdem B C = sliceIota B C := by
  have h : sliceIota B C ≫ sliceIdem B C = sliceIota B C ≫ Cat.id (slicePowObj B C) :=
    eqMap_eq (sliceIdem B C) (Cat.id (slicePowObj B C))
  rw [h, Cat.comp_id]

/-- The retraction `r : Δ[ΣC] ⟶ [C]` (the idempotent factorization). -/
noncomputable def sliceRetr (B : 𝒞) (C : Over B) : slicePowObj B C ⟶ slicePowObj' B C :=
  eqLift (sliceIdem B C) (Cat.id (slicePowObj B C)) (sliceIdem B C)
    (by rw [Cat.comp_id]; exact sliceIdem_idem B C)

/-- `r ≫ ι = e`. -/
theorem sliceRetr_iota (B : 𝒞) (C : Over B) :
    sliceRetr B C ≫ sliceIota B C = sliceIdem B C :=
  eqLift_fac (sliceIdem B C) (Cat.id (slicePowObj B C)) (sliceIdem B C)
    (by rw [Cat.comp_id]; exact sliceIdem_idem B C)

/-- `ι ≫ r = id_{[C]}` (the split: `ι` is a section of `r`). -/
theorem sliceIota_retr (B : 𝒞) (C : Over B) :
    sliceIota B C ≫ sliceRetr B C = Cat.id (slicePowObj' B C) := by
  -- both (ι≫r) and id satisfy `? ≫ ι = ι`, by equalizer uniqueness.
  have hy : sliceIota B C ≫ sliceIdem B C = sliceIota B C ≫ Cat.id (slicePowObj B C) :=
    eqMap_eq (sliceIdem B C) (Cat.id (slicePowObj B C))
  have hfac : (sliceIota B C ≫ sliceRetr B C) ≫ sliceIota B C = sliceIota B C := by
    rw [Cat.assoc, sliceRetr_iota, sliceIota_idem]
  have hid : Cat.id (slicePowObj' B C) ≫ sliceIota B C = sliceIota B C := Cat.id_comp _
  have h1 : sliceIota B C ≫ sliceRetr B C
      = eqLift (sliceIdem B C) (Cat.id (slicePowObj B C)) (sliceIota B C) hy :=
    eqLift_uniq _ _ _ hy _ hfac
  have h2 : Cat.id (slicePowObj' B C)
      = eqLift (sliceIdem B C) (Cat.id (slicePowObj B C)) (sliceIota B C) hy :=
    eqLift_uniq _ _ _ hy _ hid
  rw [h1, ← h2]

/-- The genuine slice membership relation `∈_C^{[C]} = ι*(sliceMem) : BinRel [C] C`. -/
noncomputable def sliceMem' (B : 𝒞) (C : Over B) : BinRel (Over B) (slicePowObj' B C) C :=
  relPullback (sliceIota B C) (sliceMem B C)

/-! ## §1.93  e-fixedness of tight classifiers (the key to existence against `[C]`) -/

/-- `sigmaRel R ⊂ relPullback (pair g A.hom) (R_fib)` for any `g`: a fibre-compatible
    base relation `sigmaRel R` lands in the fibre constraint at structure map `A.hom`,
    because `R.colA.f ≫ A.hom = R.colB.f ≫ C.hom` (`sigmaRel_struct`). -/
theorem sigmaRel_le_pullback_fib {A C : Over B} (R : BinRel (Over B) A C)
    (g : A.dom ⟶ slicePowBase B C) :
    RelHom (sigmaRel R) (relPullback (pair g A.hom) (baseFib B C)) := by
  let P := HasPullbacks.has (pair g A.hom) (baseFib B C).colA
  -- fibre point: cone over (snd, C.hom) with apex R.src.dom, legs
  --   (R.colA.f ≫ pair g A.hom, R.colB.f), square = sigmaRel_struct.
  have hsq : (R.colA.f ≫ pair g A.hom) ≫ snd = R.colB.f ≫ C.hom := by
    rw [Cat.assoc, snd_pair]; exact sigmaRel_struct R
  let kfib := baseFibLift (R.colA.f ≫ pair g A.hom) R.colB.f hsq
  -- cone over (pair g A.hom, baseFib.colA): legs (R.colA.f, kfib).
  have hPw : (sigmaRel R).colA ≫ pair g A.hom = kfib ≫ (baseFib B C).colA :=
    (baseFibLift_A _ _ _).symm
  refine ⟨P.lift ⟨(sigmaRel R).src, (sigmaRel R).colA, kfib, hPw⟩, P.lift_fst _, ?_⟩
  show P.lift ⟨(sigmaRel R).src, (sigmaRel R).colA, kfib, hPw⟩
      ≫ (P.cone.π₂ ≫ (baseFib B C).colB) = (sigmaRel R).colB
  rw [← Cat.assoc, P.lift_snd]
  exact baseFibLift_B _ _ _

/-- `relPullback (pair g h) (fst*∈) ≅ relPullback g (∈)`: the `B`-coordinate `h` is
    irrelevant to membership, which only reads the `[ΣC]`-coordinate `g`. -/
theorem relPullback_pair_memPB (C : Over B) {A : 𝒞} (g : A ⟶ slicePowBase B C) (h : A ⟶ B) :
    RelHom (relPullback (pair g h) (baseMemPB B C)) (relPullback g (baseMem B C)) ∧
    RelHom (relPullback g (baseMem B C)) (relPullback (pair g h) (baseMemPB B C)) := by
  obtain ⟨hc1, hc2⟩ := relPullback_comp (pair g h)
    (fst : prod (slicePowBase B C) B ⟶ slicePowBase B C) (baseMem B C)
  rw [fst_pair] at hc1 hc2
  exact ⟨hc1, hc2⟩

/-- **Tight classifiers are e-fixed.**  For `g = Λ(sigmaRel R)` the base map
    `pair g A.hom ≫ ē = pair g A.hom`, i.e. the slice classifier of a tight relation
    already lands in `[C]`.  (Restricting a fibre-compatible name to its own fibre
    is a no-op.) -/
theorem baseRho_fixes_tight {A C : Over B} (R : BinRel (Over B) A C) :
    pair (univClassify (hbase B C) (sigmaRel R)) A.hom ≫ baseIdem B C
      = pair (univClassify (hbase B C) (sigmaRel R)) A.hom := by
  let g := univClassify (hbase B C) (sigmaRel R)
  -- suffices: pair g A.hom ≫ ρ = g  (then pair-eta gives the result).
  have hρ : pair g A.hom ≫ baseRho B C = g := by
    -- pair g A.hom ≫ ρ = Λ(relPullback (pair g A.hom) baseRestrict);
    -- g = Λ(sigmaRel R); classify_unique after the iso.
    have hnat : univClassify (hbase B C) (relPullback (pair g A.hom) (baseRestrict B C))
              = pair g A.hom ≫ baseRho B C :=
      univClassify_natural (hbase B C) (baseRestrict B C) (pair g A.hom)
    -- the iso  relPullback (pair g A.hom) baseRestrict ≅ sigmaRel R.
    have hgspec := univClassify_spec (hbase B C) (sigmaRel R)  -- sigmaRel R ≅ relPullback g baseMem
    obtain ⟨hmemF, hmemB⟩ := relPullback_pair_memPB C g A.hom
    -- forward: sigmaRel R ⊂ relPullback (pair g A.hom) baseRestrict.
    have hfwd : RelHom (sigmaRel R) (relPullback (pair g A.hom) (baseRestrict B C)) := by
      apply le_relPullback_intersect
      · exact RelHom_trans hgspec.1 hmemB
      · exact sigmaRel_le_pullback_fib R g
    -- reverse: relPullback (pair g A.hom) baseRestrict ⊂ sigmaRel R.
    have hrev : RelHom (relPullback (pair g A.hom) (baseRestrict B C)) (sigmaRel R) := by
      obtain ⟨hle⟩ := intersect_le_left (baseMemPB B C) (baseFib B C)
      exact RelHom_trans (RelHom_trans (relHom_pullback923 (pair g A.hom) hle) hmemF) hgspec.2
    have hsame : univClassify (hbase B C) (relPullback (pair g A.hom) (baseRestrict B C))
               = univClassify (hbase B C) (sigmaRel R) :=
      (hbase B C).classify_unique _ (relPullback (pair g A.hom) (baseRestrict B C)) _ _
        (univClassify_spec (hbase B C) _)
        ⟨RelHom_trans hrev hgspec.1, RelHom_trans hgspec.2 hfwd⟩
    rw [← hnat, hsame]
  -- pair g A.hom ≫ ē = pair (pair g A.hom ≫ ρ) (pair g A.hom ≫ snd) = pair g A.hom.
  show pair g A.hom ≫ pair (baseRho B C) snd = pair g A.hom
  rw [pair_uniq _ _ (pair g A.hom ≫ pair (baseRho B C) snd) rfl rfl]
  congr 1
  · rw [Cat.assoc, fst_pair]; exact hρ
  · rw [Cat.assoc, snd_pair, snd_pair]

/-- **e-fixed names re-present base membership.**  If `pair k A.hom ≫ ρ = k`
    (the name `k` is fixed by the fibre-restriction), then `relPullback k (∈_{ΣC})`
    coincides with `relPullback (pair k A.hom) (baseRestrict)`: an e-fixed name has no
    cross-fibre slack, so its membership IS its fibre-restricted membership. -/
theorem efixed_restrict_iso {A : 𝒞} (C : Over B) (k : A ⟶ slicePowBase B C) (h : A ⟶ B)
    (hk : pair k h ≫ baseRho B C = k) :
    RelHom (relPullback (pair k h) (baseRestrict B C)) (relPullback k (baseMem B C)) ∧
    RelHom (relPullback k (baseMem B C)) (relPullback (pair k h) (baseRestrict B C)) := by
  have hnat : univClassify (hbase B C) (relPullback (pair k h) (baseRestrict B C))
            = pair k h ≫ baseRho B C :=
    univClassify_natural (hbase B C) (baseRestrict B C) (pair k h)
  rw [hk] at hnat
  -- relPullback (pair k h) baseRestrict ≅ relPullback (univClassify …) baseMem = relPullback k baseMem.
  have hspec := univClassify_spec (hbase B C) (relPullback (pair k h) (baseRestrict B C))
  rw [hnat] at hspec
  exact ⟨hspec.1, hspec.2⟩

/-! ## §1.93 universality of `sliceMem'` -/

/-- e-fixedness of any slice map factoring through `[C]`: `(f' ≫ ι) ≫ e = f' ≫ ι`. -/
theorem comp_iota_efixed {A : Over B} {C : Over B} (f' : A ⟶ slicePowObj' B C) :
    (f' ≫ sliceIota B C) ≫ sliceIdem B C = f' ≫ sliceIota B C := by
  rw [Cat.assoc, sliceIota_idem]

/-- **Existence for `[C]`.**  `Λ'(R) := Λ(R) ≫ r` classifies `R` against
    `sliceMem' = ι*(sliceMem)`.  Uses `f ≫ e = f` (`baseRho_fixes_tight`) so that
    `(f ≫ r) ≫ ι = f ≫ e = f`. -/
theorem sliceMem'_classify_exists {A C : Over B} (R : BinRel (Over B) A C) :
    ∃ f' : A ⟶ slicePowObj' B C,
      RelHom R (relPullback f' (sliceMem' B C)) ∧ RelHom (relPullback f' (sliceMem' B C)) R := by
  -- weak classifier f against sliceMem.
  let g := univClassify (hbase B C) (sigmaRel R)
  have hgspec := univClassify_spec (hbase B C) (sigmaRel R)
  let f := sliceClassifyOf A C g
  obtain ⟨hRf, hfR⟩ := sliceMem_classify_of R g hgspec.1 hgspec.2
  -- f ≫ e = f, hence (f ≫ r) ≫ ι = f.
  have hfe : f ≫ sliceIdem B C = f := by
    apply OverHom.ext
    show f.f ≫ baseIdem B C = f.f
    show pair g A.hom ≫ baseIdem B C = pair g A.hom
    exact baseRho_fixes_tight R
  have hfri : (f ≫ sliceRetr B C) ≫ sliceIota B C = f := by
    rw [Cat.assoc, sliceRetr_iota, hfe]
  -- relPullback (f ≫ r) sliceMem' ≅ relPullback ((f≫r)≫ι) sliceMem = relPullback f sliceMem ≅ R.
  obtain ⟨hc1, hc2⟩ := relPullback_comp (f ≫ sliceRetr B C) (sliceIota B C) (sliceMem B C)
  rw [hfri] at hc1 hc2
  refine ⟨f ≫ sliceRetr B C, ?_, ?_⟩
  · exact relHom_trans_gen hRf hc2
  · exact relHom_trans_gen hc1 hfR

/-- `sigmaRel (sliceMem) ≅ baseRestrict`: the Σ-image of the slice membership IS the
    fibre-restricted base membership (both tabulate `{((P,b),c) : (P,c)∈∈, b=C.hom c}`). -/
theorem sigmaRel_sliceMem_iso_baseRestrict (C : Over B) :
    RelHom (sigmaRel (sliceMem B C)) (baseRestrict B C) ∧
    RelHom (baseRestrict B C) (sigmaRel (sliceMem B C)) := by
  -- abbreviations for the two source pullbacks.
  let PM := HasPullbacks.has (fst : prod (slicePowBase B C) B ⟶ slicePowBase B C) (baseMem B C).colA
  let PF := HasPullbacks.has (snd : prod (slicePowBase B C) B ⟶ B) C.hom
  -- sigmaRel sliceMem : src = baseMem.src, colA = pair mem.colA (mem.colB≫hom), colB = mem.colB.
  have hσA : (sigmaRel (sliceMem B C)).colA
      = pair (baseMem B C).colA ((baseMem B C).colB ≫ C.hom) := rfl
  have hσB : (sigmaRel (sliceMem B C)).colB = (baseMem B C).colB := rfl
  constructor
  · -- forward: sigmaRel sliceMem ⊂ baseMemPB  and  ⊂ baseFib, then le_intersect's witness.
    have hmem : RelHom (sigmaRel (sliceMem B C)) (baseMemPB B C) := by
      -- witness into PM: cone over (fst, mem.colA) with legs
      --   (pair mem.colA (mem.colB≫hom) : → [ΣC]×B,  mem.src-id : → mem.src).
      have hw : (sigmaRel (sliceMem B C)).colA ≫ fst = (baseMem B C).colA := by
        rw [hσA, fst_pair]
      have hcw : (sigmaRel (sliceMem B C)).colA ≫ fst
          = Cat.id (baseMem B C).src ≫ (baseMem B C).colA := by rw [hw, Cat.id_comp]
      let cM : Cone (fst : prod (slicePowBase B C) B ⟶ slicePowBase B C) (baseMem B C).colA :=
        ⟨(sigmaRel (sliceMem B C)).src, (sigmaRel (sliceMem B C)).colA,
          Cat.id (baseMem B C).src, hcw⟩
      refine ⟨PM.lift cM, PM.lift_fst cM, ?_⟩
      show PM.lift cM ≫ (PM.cone.π₂ ≫ (baseMem B C).colB) = (sigmaRel (sliceMem B C)).colB
      rw [← Cat.assoc, PM.lift_snd cM]
      show Cat.id (baseMem B C).src ≫ (baseMem B C).colB = (sigmaRel (sliceMem B C)).colB
      rw [Cat.id_comp, hσB]
    have hfib : RelHom (sigmaRel (sliceMem B C)) (baseFib B C) := by
      -- witness into PF: cone over (snd, C.hom) with legs (colA, colB).
      have hw : (sigmaRel (sliceMem B C)).colA ≫ snd = (sigmaRel (sliceMem B C)).colB ≫ C.hom := by
        rw [hσA, hσB, snd_pair]
      let cF : Cone (snd : prod (slicePowBase B C) B ⟶ B) C.hom :=
        ⟨(sigmaRel (sliceMem B C)).src, (sigmaRel (sliceMem B C)).colA,
          (sigmaRel (sliceMem B C)).colB, hw⟩
      exact ⟨PF.lift cF, PF.lift_fst cF, PF.lift_snd cF⟩
    obtain ⟨w⟩ := le_intersect ⟨hmem⟩ ⟨hfib⟩
    exact w
  · -- reverse: baseRestrict ⊂ sigmaRel sliceMem.  Witness: k ≫ PM.π₂ : baseRestrict.src → mem.src.
    obtain ⟨⟨k, hkA, hkB⟩⟩ := intersect_le_left (baseMemPB B C) (baseFib B C)
    have hkA' : k ≫ PM.cone.π₁ = (baseRestrict B C).colA := hkA
    have hkB' : k ≫ (PM.cone.π₂ ≫ (baseMem B C).colB) = (baseRestrict B C).colB := hkB
    -- fibre square at baseRestrict: colA ≫ snd = colB ≫ C.hom.
    have hfibsq : (baseRestrict B C).colA ≫ snd = (baseRestrict B C).colB ≫ C.hom := by
      obtain ⟨⟨kf, hkfA, hkfB⟩⟩ := intersect_le_right (baseMemPB B C) (baseFib B C)
      have hkfA' : kf ≫ (baseFib B C).colA = (baseRestrict B C).colA := hkfA
      have hkfB' : kf ≫ (baseFib B C).colB = (baseRestrict B C).colB := hkfB
      rw [← hkfA', ← hkfB', Cat.assoc, Cat.assoc, baseFib_sq]
    refine ⟨k ≫ PM.cone.π₂, ?_, ?_⟩
    · -- (k ≫ PM.π₂) ≫ (sigmaRel sliceMem).colA = baseRestrict.colA, via fst/snd joint monicity.
      rw [hσA]
      apply fst_snd_jointly_monic
      · -- ≫ fst : (k≫PM.π₂)≫pair … ≫fst = (k≫PM.π₂)≫mem.colA = k≫PM.π₁≫fst = baseRestrict.colA≫fst.
        rw [Cat.assoc, fst_pair, Cat.assoc, ← PM.cone.w, ← Cat.assoc, hkA']
      · -- ≫ snd : (k≫PM.π₂)≫pair … ≫snd = (k≫PM.π₂)≫(mem.colB≫hom) = baseRestrict.colB≫hom
        --        = baseRestrict.colA≫snd  (fibre square).
        rw [Cat.assoc, snd_pair, ← Cat.assoc, Cat.assoc k, hkB', ← hfibsq]
    · -- (k ≫ PM.π₂) ≫ (sigmaRel sliceMem).colB = baseRestrict.colB.
      rw [hσB, Cat.assoc]; exact hkB'

/-- **Base bridge for e-fixed slice classifiers.**  If `h : A ⟶ Δ[ΣC]` is e-fixed
    (`h ≫ e = h`) and `relPullback h sliceMem ≅ R`, then the base name `h.f ≫ fst`
    classifies `sigmaRel R`: `relPullback (h.f ≫ fst) baseMem ≅ sigmaRel R`. -/
theorem efixed_base_classifies {A C : Over B} (R : BinRel (Over B) A C)
    (h : A ⟶ slicePowObj B C) (hfix : h ≫ sliceIdem B C = h)
    (hhR : RelHom R (relPullback h (sliceMem B C)))
    (hRh : RelHom (relPullback h (sliceMem B C)) R) :
    RelHom (sigmaRel R) (relPullback (h.f ≫ fst) (baseMem B C)) ∧
    RelHom (relPullback (h.f ≫ fst) (baseMem B C)) (sigmaRel R) := by
  -- base name k := h.f ≫ fst, fibre-fixed because h is e-fixed.
  have hkfix : pair (h.f ≫ fst) A.hom ≫ baseRho B C = h.f ≫ fst := by
    -- h.f ≫ baseIdem = h.f  (from hfix);  h.f = pair (h.f≫fst) A.hom (eta).
    have hbase_fix : h.f ≫ baseIdem B C = h.f := congrArg OverHom.f hfix
    have heta : h.f = pair (h.f ≫ fst) A.hom := pair_uniq (h.f ≫ fst) A.hom h.f rfl h.w
    -- (pair k A.hom) ≫ ρ = (pair k A.hom) ≫ baseIdem ≫ fst = h.f ≫ baseIdem ≫ fst = h.f ≫ fst = k.
    calc pair (h.f ≫ fst) A.hom ≫ baseRho B C
        = pair (h.f ≫ fst) A.hom ≫ (baseIdem B C ≫ fst) := by
          rw [show baseIdem B C ≫ fst = baseRho B C from fst_pair _ _]
      _ = (pair (h.f ≫ fst) A.hom ≫ baseIdem B C) ≫ fst := (Cat.assoc _ _ _).symm
      _ = (h.f ≫ baseIdem B C) ≫ fst := by rw [← heta]
      _ = h.f ≫ fst := by rw [hbase_fix]
  -- iso: relPullback (pair k A.hom) baseRestrict ≅ relPullback k baseMem.
  obtain ⟨_, hrI2⟩ := efixed_restrict_iso C (h.f ≫ fst) A.hom hkfix
  -- Σ-image of  relPullback h sliceMem ≅ R.
  have hσR : RelHom (sigmaRel (relPullback h (sliceMem B C))) (sigmaRel R) := sigmaRel_relHom hRh
  have hRσ : RelHom (sigmaRel R) (sigmaRel (relPullback h (sliceMem B C))) := sigmaRel_relHom hhR
  -- easy forgetful bridge:  sigmaRel(relPullback h sliceMem) ⊂ relPullback (h.f≫fst) baseMem.
  have hbridge : RelHom (sigmaRel (relPullback h (sliceMem B C)))
      (relPullback (h.f ≫ fst) (baseMem B C)) := relHom_baseMem_of_sigmaRel_sliceMem h
  constructor
  · -- forward: sigmaRel R ⊂ sigmaRel(relPullback h sliceMem) ⊂ relPullback k baseMem.
    exact RelHom_trans hRσ hbridge
  · -- reverse: relPullback k baseMem ⊂ relPullback (pair k A.hom) baseRestrict (hrI2)
    --   = relPullback h.f baseRestrict ⊂ relPullback h.f (sigmaRel sliceMem)
    --   = sigmaRel(relPullback h sliceMem) ⊂ sigmaRel R.
    have hk_eq : pair (h.f ≫ fst) A.hom = h.f := (pair_uniq (h.f ≫ fst) A.hom h.f rfl h.w).symm
    -- baseRestrict ⊂ sigmaRel sliceMem (iso reverse), monotone along h.f.
    obtain ⟨_, hbr⟩ := sigmaRel_sliceMem_iso_baseRestrict C
    have hmono : RelHom (relPullback h.f (baseRestrict B C))
        (relPullback h.f (sigmaRel (sliceMem B C))) := relHom_pullback923 h.f hbr
    -- relPullback (pair k A.hom) baseRestrict = relPullback h.f baseRestrict (rewrite pair k A.hom = h.f).
    have hrI2' : RelHom (relPullback (h.f ≫ fst) (baseMem B C))
        (relPullback h.f (baseRestrict B C)) := by
      have := hrI2; rw [hk_eq] at this; exact this
    -- sigmaRel(relPullback h sliceMem) = relPullback h.f (sigmaRel sliceMem)  (rfl).
    have hrfl : RelHom (relPullback h.f (sigmaRel (sliceMem B C)))
        (sigmaRel (relPullback h (sliceMem B C))) := by
      rw [sigmaRel_relPullback]; exact ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩
    exact RelHom_trans (RelHom_trans (RelHom_trans hrI2' hmono) hrfl) hσR

/-! ## §1.93  Universality of `sliceMem'` and `Topos (Over B)` -/

/-- **§1.93 universality of `[C]`.**  The genuine slice membership `sliceMem' B C` on
    the idempotent-split sub-object `[C]` is universal targeted at `C`. -/
theorem is_universal_sliceMem' (B : 𝒞) (C : Over B) :
    IsUniversalRel (sliceMem' B C) := by
  constructor
  · exact fun A R => sliceMem'_classify_exists R
  · -- UNIQUENESS.  Two classifiers f₁' f₂' : A ⟶ [C].  Post-compose ι; both are
    -- e-fixed (factor through [C]) and classify R against sliceMem, so their base
    -- names agree by base classify_unique; ι split-mono ⇒ f₁' = f₂'.
    intro A R f₁ f₂ hf₁ hf₂
    -- iso  relPullback fᵢ sliceMem' ≅ relPullback (fᵢ≫ι) sliceMem  (relPullback_comp).
    have hcomp : ∀ f : A ⟶ slicePowObj' B C,
        RelHom (relPullback (f ≫ sliceIota B C) (sliceMem B C)) (relPullback f (sliceMem' B C)) ∧
        RelHom (relPullback f (sliceMem' B C)) (relPullback (f ≫ sliceIota B C) (sliceMem B C)) := by
      intro f
      obtain ⟨hc1, hc2⟩ := relPullback_comp f (sliceIota B C) (sliceMem B C)
      exact ⟨hc2, hc1⟩
    -- each fᵢ≫ι classifies R against sliceMem; and is e-fixed.
    have hclassify : ∀ f : A ⟶ slicePowObj' B C,
        (RelHom R (relPullback f (sliceMem' B C)) ∧ RelHom (relPullback f (sliceMem' B C)) R) →
        (RelHom (sigmaRel R) (relPullback ((f ≫ sliceIota B C).f ≫ fst) (baseMem B C)) ∧
         RelHom (relPullback ((f ≫ sliceIota B C).f ≫ fst) (baseMem B C)) (sigmaRel R)) := by
      intro f hf
      have hhR : RelHom R (relPullback (f ≫ sliceIota B C) (sliceMem B C)) :=
        relHom_trans_gen hf.1 (hcomp f).2
      have hRh : RelHom (relPullback (f ≫ sliceIota B C) (sliceMem B C)) R :=
        relHom_trans_gen (hcomp f).1 hf.2
      exact efixed_base_classifies R (f ≫ sliceIota B C) (comp_iota_efixed f) hhR hRh
    -- base names agree by base classify_unique.
    have hbn : ((f₁ ≫ sliceIota B C).f ≫ fst) = ((f₂ ≫ sliceIota B C).f ≫ fst) :=
      (hbase B C).classify_unique A.dom (sigmaRel R) _ _
        (hclassify f₁ hf₁) (hclassify f₂ hf₂)
    -- reconstruct fᵢ≫ι via pair-eta (snd-leg = A.hom), so (f₁≫ι).f = (f₂≫ι).f.
    have hfι : (f₁ ≫ sliceIota B C).f = (f₂ ≫ sliceIota B C).f := by
      rw [show (f₁ ≫ sliceIota B C).f = pair ((f₁ ≫ sliceIota B C).f ≫ fst) A.hom from
            pair_uniq ((f₁ ≫ sliceIota B C).f ≫ fst) A.hom (f₁ ≫ sliceIota B C).f rfl
              (f₁ ≫ sliceIota B C).w,
          show (f₂ ≫ sliceIota B C).f = pair ((f₂ ≫ sliceIota B C).f ≫ fst) A.hom from
            pair_uniq ((f₂ ≫ sliceIota B C).f ≫ fst) A.hom (f₂ ≫ sliceIota B C).f rfl
              (f₂ ≫ sliceIota B C).w,
          hbn]
    have hfιeq : f₁ ≫ sliceIota B C = f₂ ≫ sliceIota B C := OverHom.ext hfι
    -- ι is split mono (ι ≫ r = id), so cancel ι.
    have : (f₁ ≫ sliceIota B C) ≫ sliceRetr B C = (f₂ ≫ sliceIota B C) ≫ sliceRetr B C := by
      rw [hfιeq]
    rw [Cat.assoc, Cat.assoc, sliceIota_retr, Cat.comp_id, Cat.comp_id] at this
    exact this

noncomputable instance overHasPowerObject (B : 𝒞) (C : Over B) :
    HasPowerObject C where
  powerObj := slicePowObj' B C
  mem := sliceMem' B C
  is_universal := is_universal_sliceMem' B C

/-! ## §1.93  `Topos (Over B)` -/

noncomputable instance overTopos (B : 𝒞) : Topos (Over B) where
  toHasSubobjectClassifier := overHasSubobjectClassifier B
  toHasBinaryProducts := overHasBinaryProducts B
  has_pow C := overHasPowerObject B C

end Freyd
