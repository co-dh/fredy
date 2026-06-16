/-
  Freyd & Scedrov, *Categories and Allegories* §1.65  Pre-topoi.

  This file collects the functor-theoretic content of §1.65 not yet
  captured by the class/instance definitions in S1_64:

  §1.655  BICARTESIAN REPRESENTATION CRITERION: a functor T : A → B between
          pre-topoi that preserves 0 (coterminator), pushouts, finite products
          and monics is a bicartesian representation.
          Key steps (Freyd's proof):
            (i)   T preserves pullbacks of monics (amalgamation §1.651 + pasting §1.62).
            (ii)  T preserves equalizers (from products, §1.434 style).
            (iii) T preserves covers (= coequalizers §1.652; T preserves pushouts and 0).
          Requires the `PreToposFunctor` concept (new to this file).

  §1.656  For functors between abelian categories the analogous theorem holds:
          preservation of cocartesian structure and monics ⟹ preservation of
          Cartesian structure.  And dually.  Non-formalizable without abelian
          infrastructure.

  Cross-references:
    `PreTopos`, `amalgamation_lemma`  — S1_64
    `PushoutCocone`, `HasPushout`     — S1_56
    `PreservesBinaryProducts`, `PreservesTerminal`, `CartesianFunctor` — S1_43
    `PreservesMono`                   — S1_18
    `HasBinaryCoproducts`             — S1_58
-/


import Fredy.S1_64

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.655 Functor predicates for pre-topos maps -/

section PreToposFunctors

variable {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]

/-- A functor F : 𝒜 → ℬ PRESERVES PUSHOUTS if for every pushout square
    `f : C → A`, `g : C → B` in 𝒜, the F-images of the cocone legs
    present a pushout in ℬ. -/
def PreservesPushouts (F : 𝒜 → ℬ) [hF : Functor F] : Prop :=
  ∀ {A B C : 𝒜} (f : C ⟶ A) (g : C ⟶ B) [h : HasPushout f g],
    ∀ (c : PushoutCocone (hF.map f) (hF.map g)),
      ∃ u : F h.cocone.pt ⟶ c.pt,
        hF.map h.cocone.ι₁ ≫ u = c.ι₁ ∧ hF.map h.cocone.ι₂ ≫ u = c.ι₂
        ∧ ∀ v : F h.cocone.pt ⟶ c.pt,
            hF.map h.cocone.ι₁ ≫ v = c.ι₁ → hF.map h.cocone.ι₂ ≫ v = c.ι₂ → v = u

/-- A functor F : 𝒜 → ℬ PRESERVES THE INITIAL OBJECT if `F(0_𝒜)` is initial in ℬ.
    (In Freyd's notation: F preserves 0.) -/
def PreservesInitial (F : 𝒜 → ℬ) [Functor F]
    [h𝒜 : HasCoterminator 𝒜] [HasCoterminator ℬ] : Prop :=
  ∀ {X : ℬ} (f g : F h𝒜.zero ⟶ X), f = g

/-- A PRE-TOPOS FUNCTOR T : A → B (Freyd §1.655): preserves
    - monics (`PreservesMono`),
    - the initial object 0 (`PreservesInitial`),
    - pushouts (`PreservesPushouts`),
    - terminal object (`PreservesTerminal`), and
    - binary products (`PreservesBinaryProducts`). -/
structure PreToposFunctor
    [h𝒜 : PreTopos 𝒜] [hℬ : PreTopos ℬ]
    [HasCoterminator 𝒜] [HasCoterminator ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F] : Prop where
  pres_mono     : PreservesMono F
  pres_initial  : PreservesInitial F
  pres_pushouts : PreservesPushouts F
  pres_terminal : PreservesTerminal F
  pres_products : PreservesBinaryProducts F

end PreToposFunctors

/-! ## §1.655 Bicartesian Representation Criterion

A pre-topos functor T : A → B is a bicartesian representation.  Freyd
proves this in three steps:
  (i)   T preserves pullbacks of monics — using §1.651 (amalgamation) and
        §1.62 (pasting lemma for squares in ℬ).
  (ii)  T preserves equalizers — from binary products via §1.434 style.
  (iii) T preserves covers — covers = coequalizers (§1.652 + §1.566 kernel pair),
        and T preserves pushouts and 0, hence T preserves coequalizers.

Each sub-theorem below has an honest sorry documented with its precise blocker. -/

section BiCartRepr

variable {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
variable [PreTopos 𝒜] [PreTopos ℬ] [HasCoterminator 𝒜] [HasCoterminator ℬ]
variable {F : 𝒜 → ℬ} [hF : Functor F]

/-- **§1.655 step (i)**: a pre-topos functor preserves pullbacks of monics.
    Proof sketch: given monics x : A ↣ B, y : A ↣ C, §1.651 gives a pushout
    B ↣ D, C ↣ D in 𝒜.  T preserves pushouts and monics, so T-images form a
    pushout in ℬ.  The pasting lemma (§1.62) identifies this pushout as the
    pullback of T(x), T(y) in ℬ.
    Honest sorry: `amalgamation_lemma` is itself sorry in S1_64, and the
    §1.62 pasting for ℬ needs the pasting-lemma from S1_62 applied there. -/
theorem preTopos_functor_preserves_monic_pullbacks (hptf : PreToposFunctor F)
    {A₁ A₂ A : 𝒜} (m : A₁ ⟶ A) (hm : Mono m) (n : A₂ ⟶ A) (hn : Mono n)
    (pb : HasPullback m n) :
    -- F maps the pullback of the two monics to a pullback in ℬ:
    ∀ (c : Cone (hF.map m) (hF.map n)),
      ∃ u : c.pt ⟶ F pb.cone.pt,
        u ≫ hF.map pb.cone.π₁ = c.π₁ ∧ u ≫ hF.map pb.cone.π₂ = c.π₂
        ∧ ∀ v : c.pt ⟶ F pb.cone.pt,
            v ≫ hF.map pb.cone.π₁ = c.π₁ → v ≫ hF.map pb.cone.π₂ = c.π₂ → v = u := by
  sorry

/-- **§1.655 step (ii)**: a pre-topos functor preserves equalizers.
    Proof: T preserves binary products by hypothesis.  Equalizers are built
    from products and pullbacks of the diagonal (§1.434 style): the equalizer
    of f, g : A → B is the pullback of ⟨1_A, f⟩ and ⟨1_A, g⟩ in A × B.
    T preserves this pullback by step (i) (the diagonal is monic, §1.42).
    Honest sorry: step (i) is sorry; the equalizer-via-products derivation
    also needs the full §1.434 construction for ℬ. -/
theorem preTopos_functor_preserves_equalizers (hptf : PreToposFunctor F)
    {A B : 𝒜} (f g : A ⟶ B) (heq : HasEqualizer f g) :
    ∀ (c : EqualizerCone (hF.map f) (hF.map g)),
      ∃ u : c.dom ⟶ F heq.cone.dom,
        u ≫ hF.map heq.cone.map = c.map
        ∧ ∀ v : c.dom ⟶ F heq.cone.dom, v ≫ hF.map heq.cone.map = c.map → v = u := by
  sorry

/-- **§1.655 step (iii)**: a pre-topos functor preserves covers.
    Proof: in a pre-topos, every cover f : A ↠ B is a coequalizer of its kernel
    pair (§1.566 + §1.652: epics = covers).  T preserves pushouts and 0, so T
    preserves coequalizers.  Then `bicart_repr_preserves_covers` (§1.581) gives
    the result.
    Honest sorry: the pushout-preservation → coequalizer-preservation bridge
    is not yet a lemma in this repo. -/
theorem preTopos_functor_preserves_covers (hptf : PreToposFunctor F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) : Cover (hF.map f) := by
  sorry

/-- **§1.655 (main theorem)**: A pre-topos functor T : A → B is a bicartesian
    representation — it preserves pullbacks, equalizers, covers, and coproducts.
    Statement is faithful to Freyd §1.655.  The proof reduces to steps (i–iii);
    each step is an honest sorry documented above.

    Blockers:
    - step (i): `amalgamation_lemma` (sorry in S1_64) + §1.62 pasting for ℬ.
    - step (ii): §1.434 equalizer-via-products construction, unpacked for ℬ.
    - step (iii): pushout-preservation → coequalizer-preservation bridge. -/
theorem preTopos_functor_is_bicartesian_repr (hptf : PreToposFunctor F)
    [HasBinaryCoproducts 𝒜] [HasCoequalizers 𝒜]
    [HasBinaryCoproducts ℬ] [HasCoequalizers ℬ] :
    -- (a) F preserves covers:
    (∀ {A B : 𝒜} (f : A ⟶ B), Cover f → Cover (hF.map f))
    -- (b) F preserves equalizers:
    ∧ (∀ {A B : 𝒜} (f g : A ⟶ B) (heq : HasEqualizer f g)
         (c : EqualizerCone (hF.map f) (hF.map g)),
         ∃ u : c.dom ⟶ F heq.cone.dom,
           u ≫ hF.map heq.cone.map = c.map
           ∧ ∀ v : c.dom ⟶ F heq.cone.dom, v ≫ hF.map heq.cone.map = c.map → v = u)
    -- (c) F preserves binary coproducts: canonical map coprod(FA,FB) → F(coprod A B) is iso:
    ∧ (∀ (A B : 𝒜),
         IsIso (HasBinaryCoproducts.case
                  (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
                  (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) :
                HasBinaryCoproducts.coprod (F A) (F B) ⟶ F (HasBinaryCoproducts.coprod A B))) :=
  ⟨fun f hf => preTopos_functor_preserves_covers hptf f hf,
   fun f g heq c => preTopos_functor_preserves_equalizers hptf f g heq c,
   fun _A _B => by sorry⟩

end BiCartRepr

/-! ## §1.656 Remark on abelian categories (non-formalizable)

For functors between abelian categories, the analogous theorem holds:
preservation of the cocartesian structure and monics implies preservation of
the Cartesian structure (and its dual).  This is strictly stronger than for
pre-topoi, where only one direction transfers.

Non-formalizable in the current repo: requires the abelian category
infrastructure of §1.59 (zero object, half-additive structure, middle-two
interchange). -/

-- §1.656 (note): Not formalized; abelian infrastructure (§1.59) required.

end Freyd
