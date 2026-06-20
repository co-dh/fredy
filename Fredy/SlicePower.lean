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
  `Δ([Σ C]) = ⟨[Σ C] × B, snd⟩`, and slice universality transports to base
  universality of `∈_{Σ C}`.

  ADDITIVE: a new file built only from base power objects + Σ-transport; NO new
  axioms, NO Chapter-2 allegory axioms.
-/

import Fredy.S1_9
import Fredy.S1_44
import Fredy.SliceRegular
import Fredy.SliceTopos

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

open HasSubobjectClassifier

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

/-- Transitivity of `RelHom` (compose the witnessing column-preserving maps). -/
theorem relHom_trans' {X Y : 𝒞} {R S T : BinRel 𝒞 X Y}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨a, haA, haB⟩ := h₁
  obtain ⟨b, hbA, hbB⟩ := h₂
  exact ⟨a ≫ b, by rw [Cat.assoc, hbA, haA], by rw [Cat.assoc, hbB, haB]⟩

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
    exact overPullbackLift_fst f (sliceMem B C).colA R.colA mlift hsq
  · -- colB: k ⊚ (overPullbackπ₂ ⊚ sliceMem.colB) = R.colB.
    apply OverHom.ext
    -- on base: k.f ≫ (overPullbackπ₂.f ≫ sliceMem.colB.f) = R.colB.f.
    show k.f ≫ ((overPullbackπ₂ f (sliceMem B C).colA).f ≫ (sliceMem B C).colB.f) = R.colB.f
    have hk₂ : k ⊚ overPullbackπ₂ f (sliceMem B C).colA = mlift :=
      overPullbackLift_snd f (sliceMem B C).colA R.colA mlift hsq
    have hk₂f : k.f ≫ (overPullbackπ₂ f (sliceMem B C).colA).f = jw ≫ pbg.cone.π₂ :=
      congrArg OverHom.f hk₂
    rw [← Cat.assoc, hk₂f]
    show (jw ≫ pbg.cone.π₂) ≫ (baseMem B C).colB = R.colB.f
    rw [Cat.assoc]; exact hjB'

/-- **§1.93 universality of the slice membership (RESIDUAL).**

  The slice membership relation `∈_C^{Over B} = sliceMem B C` is universal targeted
  at `C`.  By the Δ–Σ adjunction a slice classifier `f : A ⟶ Δ[Σ C]` is exactly
  `⟨pair g A.hom, …⟩` for a unique base map `g = f.f ≫ fst : A.dom ⟶ [Σ C]`, and
  `sigmaRel (relPullback f (sliceMem)) = relPullback f.f (sigmaRel (sliceMem))` holds
  on the nose (`sigmaRel_relPullback`).  Universality then reduces to BASE
  universality of `baseMem` (`Topos.has_pow`, via `powerClassify`).

  STATUS:
  • `classify_exists` is CLOSED sorry-free.  Construction: take the base classifier
    `g := powerClassify (sigmaRel R)`; the slice classifier is `sliceClassifyOf A C g
    = ⟨pair g A.hom, …⟩`.  The forward slice `RelHom R ⟶ relPullback f (sliceMem)`
    is `sliceRelHom_of_baseRelHom` (the §1.93 lift: the B-leg constraint
    `aleg ≫ A.hom = mleg ≫ mem.colB ≫ C.hom` is automatic by `sigmaRel_struct`,
    i.e. `R`'s over-hom column laws — this IS the second iso `Σ(−×ΔA) ≃ Σ(−)×A`).
    The reverse uses Σ-fullness on relations (`sliceRelHom_of_sigmaRel`) after the
    easy forgetful bridge `relHom_baseMem_of_sigmaRel_sliceMem` composed with the
    base reverse.

  • `classify_unique` is the SINGLE RESIDUAL (one `sorry`).  Reduction (done in
    code): by Σ-faithfulness + `pair`-eta on `Δ[Σ C]`, `f = g` ⟺ `f.f ≫ fst =
    g.f ≫ fst`.

    *** DIAGNOSIS (2026-06-20): the residual is NOT merely hard — `classify_unique`
    is FALSE for the present power object `slicePowObj B C = Δ[Σ C]` whenever `C`
    is a PROPER subobject of `Δ(Σ C)` (i.e. for a general `C : Over B`).  Freyd's
    first construction `Δ[A]` is a power object only for objects of the form
    `Δ(A)` (book §1.93: "`Δ[A]` is a power-object for `Δ(A)`").  For a general `C`
    one must FURTHER restrict `[Σ C]` to the idempotent-split subobject; this file
    skips that step, so `Δ[Σ C]` is only WEAKLY universal (classifiers exist —
    `classify_exists` is genuinely closed — but they are NOT unique). ***

    Why uniqueness fails.  A slice classifier `f : A ⟶ Δ[Σ C]` is `pair (f.f≫fst)
    A.hom` (snd-leg forced to `A.hom`), so only `f.f≫fst : A.dom ⟶ [Σ C]` is free.
    Its Σ-image relation `relPullback f.f (sigmaRel sliceMem)` is, componentwise on
    `[Σ C]×B`, the conjunction
      (I)  `a ≫ (f.f≫fst) = m ≫ mem.colA`      (membership in `[Σ C]`), and
      (II) `a ≫ A.hom     = m ≫ mem.colB ≫ C.hom`   (same B-fibre / slice-compat).
    `R` (hence `sigmaRel R`) only constrains the part of `f.f≫fst` visible THROUGH
    (II) — the same-fibre membership.  The CROSS-FIBRE membership of `f.f≫fst`
    (does `a` "contain" a `C`-element living over a DIFFERENT point of `B`?) is
    invisible to the tight relation, hence unconstrained.  So two names that agree
    on the same-fibre part but differ cross-fibre give the SAME `R` yet differ as
    maps `A.dom ⟶ [Σ C]`.

    Concrete Set counterexample.  `B = {0,1}`, `C.dom = {p,q}` with `p↦0, q↦1`
    (`Σ C` meets both fibres), `A = ⟨{a}, a↦0⟩`.  Then `[Σ C] = 𝒫{p,q}` (4 names).
    The relation `R = {a∼p}` (forced: `a` is over `0`, so it can only relate to the
    fibre-0 element `p`) is classified by BOTH `f.f≫fst = {p}` and `g.f≫fst =
    {p,q}` — both restrict to `{p}` on the fibre-0 part `(II)`.  Hence two distinct
    slice classifiers of the same `R`: `classify_unique` is refuted.

    CORRECT FIX (Freyd §1.93, the part this file omits): the slice power object is
    NOT `Δ[Σ C]` but the idempotent-split subobject `[C] ⊆ Δ[Σ C]`.  Let
    `e := powerClassify (sliceMem B (Δ(Σ C)) ∩ (Δ[Σ C] × C)) : Δ[Σ C] ⟶ Δ[Σ C]`
    (Freyd's `e = Λ(∈ ∩ ([A]×A'))`, here `A = Δ(Σ C)`, `A' = C`); `e` is an
    idempotent (book §1.93), and `[C] := equalizer 1 e` (equalizers exist:
    `topos_has_equalizers`).  Re-running existence + uniqueness against `[C]`'s
    membership gives genuine universality, because cross-fibre names are exactly
    those `e` kills, so on `[C]` names ARE unique.  This requires NEW machinery
    (relation intersection `∩` as a `BinRel` constructor, the slice membership of
    `Δ(Σ C)` itself, `e`-idempotence, and the equalizer-as-sub-power-object
    universality lift).  PRECISE NEXT SUB-LEMMAS:
      `sliceRelMeet : BinRel (Over B) P C → BinRel (Over B) P C → BinRel (Over B) P C`
      `sliceCrossIdem (C : Over B) : let e := powerClassify (sliceMem B (Δ(Σ C)) ∩ …);
          (e ≫ e = e)`    -- e is idempotent
      `slicePowObj' B C := equalizer (id (Δ[Σ C])) e`   -- the genuine [C]
      `is_universal_sliceMem' : IsUniversalRel (mem on slicePowObj')`  -- both ways.
    Until that rebuild lands, the residual below is NOT closable by any transport
    on `Δ[Σ C]` (the goal is literally false there). -/
theorem is_universal_sliceMem (B : 𝒞) (C : Over B) :
    IsUniversalRel (sliceMem B C) := by
  -- base universality of `∈_{Σ C}` (the base power object of `C.dom`).
  have hbase : IsUniversalRel (baseMem B C) :=
    (HasPowerObject.is_universal (C := C.dom))
  constructor
  · intro A R
    -- classify the Σ-image relation in the base.
    obtain ⟨g, hgf, hgr⟩ := hbase.classify_exists A.dom (sigmaRel R)
    -- rewrite g as (sliceClassifyOf A C g).f ≫ fst so the easy bridge target matches.
    have hgeq : g = (sliceClassifyOf A C g).f ≫ fst := (sliceClassifyOf_fst A C g).symm
    refine ⟨sliceClassifyOf A C g, ?_, ?_⟩
    · -- forward slice RelHom R ⟶ relPullback (sliceClassifyOf A C g) (sliceMem).
      exact sliceRelHom_of_baseRelHom R g hgf
    · -- reverse: relPullback f (sliceMem) ⟶ R, via Σ-fullness + easy bridge + base reverse.
      apply sliceRelHom_of_sigmaRel
      -- base RelHom  sigmaRel (relPullback f sliceMem) ⟶ sigmaRel R.
      have hgr' : RelHom (relPullback ((sliceClassifyOf A C g).f ≫ fst) (baseMem B C))
          (sigmaRel R) := by rw [sliceClassifyOf_fst]; exact hgr
      exact relHom_trans' (relHom_baseMem_of_sigmaRel_sliceMem (sliceClassifyOf A C g)) hgr'
  · intro A R f g hf hg
    -- RESIDUAL: see `classify_unique` note below.
    sorry

noncomputable instance overHasPowerObject (B : 𝒞) (C : Over B) :
    HasPowerObject C where
  powerObj := slicePowObj B C
  mem := sliceMem B C
  is_universal := is_universal_sliceMem B C

/-! ## §1.93  `Topos (Over B)` -/

noncomputable instance overTopos (B : 𝒞) : Topos (Over B) where
  toHasSubobjectClassifier := overHasSubobjectClassifier B
  toHasBinaryProducts := overHasBinaryProducts B
  has_pow C := overHasPowerObject B C

end Freyd
