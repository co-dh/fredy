/-
  Freyd & Scedrov, *Categories and Allegories* §1.9  Topoi.

  §1.9   TOPOS: Cartesian + every object has a power-object.
         UNIVERSAL RELATION targeted at C; POWER-OBJECT [C].
  §1.912 SUBOBJECT CLASSIFIER Ω, universal subobject t:1→Ω,
         with characteristic-map axioms (classify_sq / classify_pullback /
         classify_unique).
  §1.913 All subobjects are equalizers; covers = epics.
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_56


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.9  Universal relation and power-object

  A relation from A to C is a jointly-monic span A ←— T —→ C (`BinRel 𝒞 A C`).
  Book §1.9: given a map f : A' → A and a relation U : BinRel 𝒞 A C, define
  `f ≫_rel U` (written `fU` in the book) as the pullback of U along f, which
  gives a relation A' ← (pullback) → C.

  A relation U : BinRel 𝒞 P C is UNIVERSAL (targeted at C) if for every A
  and every relation R : BinRel 𝒞 A C there exists a unique f : A → P such
  that R ≅ fU (the pullback of U along f).

  A POWER-OBJECT [C] is an object P together with a universal relation ∈_C
  targeted at C.  The classifying map Λ(R) : A → [C] is often written A_R. -/

/-- §1.9: The pullback of a relation `U : BinRel 𝒞 P C` along a map `f : A → P`
    gives a relation from A to C (when pullbacks exist).  Its source is the
    pullback of `f : A → P` and `U.colA : U.src → P`.  -/
noncomputable def relPullback [HasPullbacks 𝒞] {P C A : 𝒞}
    (f : A ⟶ P) (U : BinRel 𝒞 P C) : BinRel 𝒞 A C :=
  let pb := HasPullbacks.has f U.colA   -- HasPullback f U.colA
  { src  := pb.cone.pt
    colA := pb.cone.π₁         -- pb.pt → A
    colB := pb.cone.π₂ ≫ U.colB  -- pb.pt → U.src → C
    isMonicPair := by
      -- jointly-monic: if h₁, h₂ : W → pb.pt agree on both legs,
      -- they agree on π₁ and π₂ ≫ U.colA (via the pullback), so h₁ = h₂.
      intro W g h hA hB
      -- hA : g ≫ π₁ = h ≫ π₁   (agreement on A-leg)
      -- hB : g ≫ (π₂ ≫ U.colB) = h ≫ (π₂ ≫ U.colB)  (agreement on C-leg)
      -- We need g = h.  Use that U.isMonicPair and pb uniqueness together force it.
      -- From pb uniqueness: if g ≫ π₁ = h ≫ π₁ and g ≫ π₂ = h ≫ π₂ then g = h.
      -- We have agreement on π₁ from hA.  Need agreement on π₂.
      -- From hB: g ≫ π₂ ≫ U.colB = h ≫ π₂ ≫ U.colB.
      -- Rewrite: (g ≫ π₂) ≫ U.colB = (h ≫ π₂) ≫ U.colB.
      -- Since U.isMonicPair concerns both legs, and we also need agreement on U.colA.
      -- Note g ≫ π₂ ≫ U.colA = g ≫ π₁ ≫ f (pullback square: π₂ ≫ U.colA = π₁ ≫ f)
      -- so agreement on U.colA follows from hA.
      -- Hence U.isMonicPair applied to (g ≫ π₂) and (h ≫ π₂) gives g ≫ π₂ = h ≫ π₂.
      -- Full argument: from hA get π₁ agreement; from hB + pullback-square + U.isMonicPair
      -- get π₂ agreement; then pullback uniqueness gives g = h.
      -- Step 1: reassociate hB to get (g ≫ π₂) ≫ U.colB = (h ≫ π₂) ≫ U.colB
      have hB' : (g ≫ pb.cone.π₂) ≫ U.colB = (h ≫ pb.cone.π₂) ≫ U.colB := by
        rw [Cat.assoc, Cat.assoc]; exact hB
      -- Step 2: from hA + pullback square, get (g ≫ π₂) ≫ U.colA = (h ≫ π₂) ≫ U.colA
      -- cone.w : π₁ ≫ f = π₂ ≫ U.colA; reassociate to match rewrite pattern
      have hA' : (g ≫ pb.cone.π₂) ≫ U.colA = (h ≫ pb.cone.π₂) ≫ U.colA := by
        have sq := pb.cone.w  -- π₁ ≫ f = π₂ ≫ U.colA
        have hg : (g ≫ pb.cone.π₁) ≫ f = (g ≫ pb.cone.π₂) ≫ U.colA := by
          rw [Cat.assoc, Cat.assoc, sq]
        have hh : (h ≫ pb.cone.π₁) ≫ f = (h ≫ pb.cone.π₂) ≫ U.colA := by
          rw [Cat.assoc, Cat.assoc, sq]
        rw [← hg, ← hh, hA]
      -- Step 3: U.isMonicPair gives g ≫ π₂ = h ≫ π₂
      have hπ₂ : g ≫ pb.cone.π₂ = h ≫ pb.cone.π₂ := U.isMonicPair _ _ hA' hB'
      -- Step 4: pullback lift_uniq gives g = h
      have hw : (g ≫ pb.cone.π₁) ≫ f = (g ≫ pb.cone.π₂) ≫ U.colA := by
        rw [Cat.assoc, Cat.assoc, pb.cone.w]
      exact (pb.lift_uniq ⟨W, g ≫ pb.cone.π₁, g ≫ pb.cone.π₂, hw⟩ g rfl rfl).trans
        (pb.lift_uniq ⟨W, g ≫ pb.cone.π₁, g ≫ pb.cone.π₂, hw⟩ h hA.symm hπ₂.symm).symm }

/-- §1.9: A relation U : BinRel 𝒞 P C is UNIVERSAL targeted at C if every
    relation R : BinRel 𝒞 A C is uniquely isomorphic to `relPullback f U` for
    some f : A → P. -/
structure IsUniversalRel [HasPullbacks 𝒞] {P C : 𝒞} (U : BinRel 𝒞 P C) : Prop where
  /-- For each A and R : BinRel A C there is a unique Λ(R) : A → P such that
      R is isomorphic (as relations) to the pullback of U along Λ(R). -/
  classify_exists : ∀ (A : 𝒞) (R : BinRel 𝒞 A C), ∃ f : A ⟶ P,
    RelHom R (relPullback f U) ∧ RelHom (relPullback f U) R
  classify_unique  : ∀ (A : 𝒞) (R : BinRel 𝒞 A C) (f g : A ⟶ P),
    (RelHom R (relPullback f U) ∧ RelHom (relPullback f U) R) →
    (RelHom R (relPullback g U) ∧ RelHom (relPullback g U) R) →
    f = g

/-- §1.9: A POWER-OBJECT for C: an object [C] with a universal relation ∈_C.
    In the book's notation, [C] appears as the source of ∈_C ⊆ [C] × C;
    Λ(R) : A → [C] is the unique classifying map for R : BinRel A C. -/
class HasPowerObject [HasPullbacks 𝒞] (C : 𝒞) where
  /-- The power-object [C] (written in the book as [C]). -/
  powerObj : 𝒞
  /-- The universal relation ∈_C : BinRel 𝒞 [C] C. -/
  mem      : BinRel 𝒞 powerObj C
  /-- ∈_C is universal targeted at C. -/
  is_universal : IsUniversalRel mem

/-- §1.9: The classifying map Λ(R) : A → [C] for a relation R : BinRel A C.
    Written A_R in the book.  Extracted from the universality witness. -/
noncomputable def powerClassify [HasPullbacks 𝒞] {C : 𝒞} [HasPowerObject C]
    {A : 𝒞} (R : BinRel 𝒞 A C) : A ⟶ HasPowerObject.powerObj (C := C) :=
  (HasPowerObject.is_universal.classify_exists A R).choose

/-! ## §1.912  Subobject classifier

  Relations from A to 1 correspond bijectively to subobjects of A (§1.912).
  The traditional name for [1] is Ω — the SUBOBJECT CLASSIFIER.
  The universal relation ∈_1 corresponds to the UNIVERSAL SUBOBJECT t : 1 → Ω.

  Reformulation entirely in terms of subobjects (monics):
  t : 1 → Ω is universal if for every monic m : A' → A there is a UNIQUE
  characteristic map χ_m : A → Ω making the square

      A' ----term A'----> 1
      |                   |
      m                   t
      v                   v
      A ------χ_m-------> Ω

  a pullback. -/

/-- A SUBOBJECT CLASSIFIER Ω with universal monic t : 1 → Ω (§1.912).
    For each monic m : A' → A, there is a unique characteristic map χ_m : A → Ω
    such that the square (m, term A', χ_m, true) is a pullback.

    Fields:
    - `classify`          : produces χ_m from a monic m
    - `classify_sq`       : m ≫ χ_m = term A' ≫ true  (square commutes)
    - `classify_pullback` : the cone is a pullback
    - `classify_unique`   : χ_m is the unique such map -/
class HasSubobjectClassifier (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasPullbacks 𝒞 where
  omega      : 𝒞
  true       : one ⟶ omega
  true_monic : Mono true
  /-- The characteristic map of a monic m : A' → A. -/
  classify {A A' : 𝒞} (m : A' ⟶ A) : Mono m → (A ⟶ omega)
  /-- The classifying square commutes: `m ≫ χ_m = (A'→1) ≫ t`. -/
  classify_sq : ∀ {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m), m ≫ classify m hm = term A' ≫ true
  /-- **Universal property**: `m` is the pullback of `t` along `χ_m`. -/
  classify_pullback : ∀ {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m),
    Cone.IsPullback (⟨A', m, term A', classify_sq m hm⟩ : Cone (classify m hm) true)
  /-- `χ_m` is the UNIQUE map making `m` the pullback of `t`. -/
  classify_unique : ∀ {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m) (χ : A ⟶ omega)
    (hsq : m ≫ χ = term A' ≫ true),
    Cone.IsPullback (⟨A', m, term A', hsq⟩ : Cone χ true) → χ = classify m hm

/-- A TOPOS (§1.9, book p.9091): Cartesian category in which each object has a
    power-object.  Freyd's primary definition is the power-object one; the
    subobject classifier `Ω = [1]` is then a derived consequence (§1.912).  We
    bundle BOTH: the classifier presentation (`HasSubobjectClassifier`, the
    working interface for §1.91's Heyting layer) AND the power objects
    (`has_pow`), since recovering power objects from the bare classifier is
    Paré's theorem, which Freyd does not prove and this development does not need.
    Bundling `has_pow` is faithful to the book definition and supplies the
    `∀ C, HasPowerObject C` that §1.92's exponentials (`topos_has_exponentials`,
    §1.923) and §1.95's quotient covers rest on. -/
class Topos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasSubobjectClassifier 𝒞 where
  /-- §1.9: every object `C` has a power-object `[C]` with universal `∈_C`. -/
  has_pow : ∀ C : 𝒞, HasPowerObject C

/-- §1.9: expose a topos's power objects to instance search, so the established
    `[∀ C, HasPowerObject C]` hypotheses (S1_91/S1_92) are auto-satisfied under
    `[Topos 𝒞]`.  Low priority to avoid pre-empting any locally-supplied power
    object. -/
instance (priority := 100) Topos.hasPowerObject {𝒞 : Type u} [Cat.{v} 𝒞]
    [Topos 𝒞] (C : 𝒞) : HasPowerObject C := Topos.has_pow C

/-! ## §1.912  Derived facts -/

/-- §1.912: The universal subobject t : 1 → Ω is monic. -/
theorem true_monic [HasSubobjectClassifier 𝒞] :
    Mono (HasSubobjectClassifier.true (𝒞 := 𝒞)) :=
  HasSubobjectClassifier.true_monic

/-- §1.912: The characteristic map is unique: if χ makes the pullback square,
    then χ = classify m hm.  This follows directly from `classify_unique`. -/
theorem classify_eq_of_pullback [HasSubobjectClassifier 𝒞]
    {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m)
    (χ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (sq : m ≫ χ = term A' ≫ HasSubobjectClassifier.true)
    (pb : (Cone.mk (f := χ) (g := HasSubobjectClassifier.true)
        (pt := A') (π₁ := m) (π₂ := term A') (w := sq)).IsPullback) :
    χ = HasSubobjectClassifier.classify m hm :=
  HasSubobjectClassifier.classify_unique m hm χ sq pb

/-- §1.912: The characteristic map does not depend on the proof of monicity. -/
theorem classify_congr [HasSubobjectClassifier 𝒞]
    {A A' : 𝒞} (m : A' ⟶ A) (hm hm' : Mono m) :
    HasSubobjectClassifier.classify m hm = HasSubobjectClassifier.classify m hm' :=
  HasSubobjectClassifier.classify_unique m hm _
    (HasSubobjectClassifier.classify_sq m hm')
    (HasSubobjectClassifier.classify_pullback m hm')

end Freyd
