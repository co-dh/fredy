/-
  Freyd & Scedrov, *Categories and Allegories* §1.923.

  CONDITIONAL theorem: in a category with terminal, binary products, pullbacks,
  equalizers, AND a power object `[C]` for EVERY object `C`, every object `B` is
  BASEABLE (i.e. the exponential `B^A` exists for every `A`).

  This is the "Kock" half of §1.921/§1.923: exponentiation follows from power
  objects.  The exponential `B^A` is constructed as the subobject of
  `[A × B] = powerObj (A × B)` cut out by the FUNCTIONAL relations — those
  `R ⊆ X × (A × B)` (equivalently `R ⊆ (A × X) → B`) that are graphs of maps
  `A → B`.

  STATUS.  This file keeps the HONEST §1.923 statement.  It builds the genuinely
  power-object-only infrastructure (the relation/classifier correspondence
  `Hom(X,[C]) ≅ BinRel(X,C)` as a bijection, packaged below) and reduces the main
  theorem to TWO precisely-typed sub-lemmas, both of which are real §1.912/§1.923
  content not yet available sorry-free in this repo:

    (D1) `power_object_gives_subobject_classifier` :
            from `[1] = powerObj one` build a `HasSubobjectClassifier 𝒞`.
         Signature (target):  `Nonempty (HasSubobjectClassifier 𝒞)`
         (Freyd §1.912.  The repo's `HasSubobjectClassifier` is only ever
          *assumed* via `[Topos 𝒞]`; deriving it from `HasPowerObject one`
          is unformalized.)

    (D2) `functional_subobject_is_exponential` :
            given a subobject classifier, cut out the functional relations of
            `[A × B]` (the §1.923 pullback `B^A → [A×B] ⇉ [A]`) and equip it with
            `ev` + curry + uniqueness, i.e. exactly `Baseable B` for that `A`.
         (The repo HAS this construction in `S1_92 :: expSubobj` /
          `graph_classifies`, but only relative to the sorry-contaminated `exp`
          instance `topos_has_exponentials`; redoing it on the power-object `E`
          with NO `exp` dependency is the remaining work.)

  (D1) is the NEXT DOMINO: it unlocks the existing §1.92 graph/classifier
  machinery (`graph_classifies`, `classRel_classify`, `monic_is_equalizer`) on
  *our* hypotheses, after which (D2) is the (S1_92-style) curry/eval bookkeeping.

  NO new axioms or hypotheses are introduced; the only gaps are the two sorries
  named above, each pinned to its exact signature.

  ⚠ SCOPE / RELATION TO THE KEYSTONE `S1_92 :: topos_has_exponentials`.
  This theorem is CONDITIONAL on `[∀ C, HasPowerObject C]`, which the repo's
  `Topos` class does NOT bundle (it provides only a subobject classifier
  `Ω = [1]`).  So even once (D1)+(D2) are closed, this does NOT directly discharge
  the keystone: that would additionally require building `∀ C, HasPowerObject C`
  FROM a bare subobject classifier — the converse of (D1) — which is the genuine
  open obstacle (constructing `[C] = Ω^C` from `Ω` alone is itself exponentiation,
  hence circular under the minimal `Topos` presentation).  This file is therefore
  scaffolding for the *power-object → exponential* direction (Kock's half) plus
  reusable, axiom-clean power-object correspondence lemmas; it is intentionally
  NOT imported by `S1_92`, so it adds no `sorryAx` to the main line.
-/

import Fredy.S1_91
import Fredy.S1_85

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section Baseable923

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
variable [∀ C : 𝒞, HasPowerObject C] [HasEqualizers 𝒞]

/-! ## Power-object correspondence as a bijection (genuine, power-object-only)

  For any `Z, C`, the universality of `∈_C` (`HasPowerObject.is_universal`) makes
  `powerClassify : BinRel 𝒞 Z C → (Z ⟶ [C])` and `f ↦ relPullback f ∈_C` mutually
  inverse up to `RelHom`.  These lemmas are exactly what `(D2)` needs, proved here
  with NO dependence on `exp`/`Topos`. -/

/-- `powerClassify` classifies `R` up to relation iso.  Stated directly from the
    universality field `classify_exists` (NOT via the `[Topos 𝒞]`-contaminated
    `S1_91 :: powerClassify_spec`), so it depends only on power objects. -/
theorem powerClassify_pullback_iso {C Z : 𝒞} (R : BinRel 𝒞 Z C) :
    RelHom R (relPullback (powerClassify R) HasPowerObject.mem) ∧
    RelHom (relPullback (powerClassify R) HasPowerObject.mem) R :=
  (HasPowerObject.is_universal.classify_exists Z R).choose_spec

/-- **Uniqueness of the classifying map** (universality `classify_unique`). -/
theorem powerClassify_unique {C Z : 𝒞} (R : BinRel 𝒞 Z C)
    (f g : Z ⟶ HasPowerObject.powerObj (C := C))
    (hf : RelHom R (relPullback f HasPowerObject.mem) ∧ RelHom (relPullback f HasPowerObject.mem) R)
    (hg : RelHom R (relPullback g HasPowerObject.mem) ∧ RelHom (relPullback g HasPowerObject.mem) R) :
    f = g :=
  HasPowerObject.is_universal.classify_unique Z R f g hf hg

/-- **Maps into `[C]` are determined by their relation**: if `f g : Z ⟶ [C]` pull
    `∈_C` back to iso relations, they are equal. -/
theorem powerObj_hom_ext {C Z : 𝒞} (f g : Z ⟶ HasPowerObject.powerObj (C := C))
    (h : RelHom (relPullback f HasPowerObject.mem) (relPullback g HasPowerObject.mem) ∧
         RelHom (relPullback g HasPowerObject.mem) (relPullback f HasPowerObject.mem)) :
    f = g :=
  HasPowerObject.is_universal.classify_unique Z (relPullback f HasPowerObject.mem) f g
    ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
     ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩
    ⟨h.1, h.2⟩

/-! ## §1.923 missing dominoes (honest sorries, pinned signatures) -/

/-- **(D1)** §1.912: a power object for the terminal object is a subobject
    classifier.  `Ω := powerObj one`, `true := Λ(graph (term 1))`, and
    `classify m := Λ` of the relation `m : A' ↣ A → 1`.  Freyd §1.912; not yet
    formalized (the repo only *assumes* `HasSubobjectClassifier` via `[Topos 𝒞]`).

    NEXT DOMINO: closing this unlocks the existing `S1_92` graph/classifier
    machinery on the present hypotheses. -/
theorem power_object_gives_subobject_classifier :
    Nonempty (HasSubobjectClassifier 𝒞) :=
  sorry

/-- **(D2)** §1.923: given a subobject classifier, the FUNCTIONAL-relation
    subobject of `[A × B]` is the exponential `B^A`, yielding for each `A` the
    object `E`, evaluation `ev : A × E → B`, and the curry/eval bijection that is
    exactly `Baseable B` at `A`.

    The §1.923 pullback `E → [A×B] ⇉ [A]` (functionality = "domain is all of A");
    the repo realizes it in `S1_92 :: expSubobj` / `graph_classifies`, but only
    over the sorry-contaminated `exp` instance.  Reproving it on the power-object
    `E` with no `exp` dependency is the remaining work. -/
theorem functional_subobject_is_exponential
    (_hΩ : HasSubobjectClassifier 𝒞) (B A : 𝒞) :
    ∃ (E : 𝒞) (ev : prod A E ⟶ B),
      ∀ (X : 𝒞) (f : prod A X ⟶ B),
        ∃ (g : X ⟶ E), prodMap A X E g ≫ ev = f ∧
          ∀ (g' : X ⟶ E), prodMap A X E g' ≫ ev = f → g' = g :=
  sorry

/-- **§1.923**: GIVEN a power object for every object, every object is baseable.
    Reduces to `(D1)` (power object of `1` is a subobject classifier) and `(D2)`
    (functional-relation subobject of `[A×B]` is the exponential). -/
theorem power_objects_imply_all_baseable :
    ∀ B : 𝒞, Baseable B := by
  intro B A
  obtain ⟨hΩ⟩ := power_object_gives_subobject_classifier (𝒞 := 𝒞)
  exact functional_subobject_is_exponential hΩ B A

end Baseable923

end Freyd
