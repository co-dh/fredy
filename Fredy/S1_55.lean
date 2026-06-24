/-
  Freyd & Scedrov, *Categories and Allegories* §1.55
  Henkin-Lubkin representation theorem.

  Every small (pre-)regular category is faithfully represented in a power of the
  category of sets.  We model the category of sets 𝒮 as `Type w` with functions
  as morphisms, and a power 𝒮^I as I-indexed families of sets with pointwise
  families of functions.

  The faithful representation is the covariant hom-functor (Cayley, §1.272)
  family `i ↦ Hom(i, -)`: the product functor `𝒞 → 𝒮^|𝒞|`, `A ↦ (i ↦ (i ⟶ A))`,
  separates morphisms because `id_A` distinguishes `f` from `g` (`cayley_faithful`).
  This is constructive and choice-free, so it holds for ANY small category — the
  regularity hypothesis is carried for fidelity to the book but is not used.

  NOTE on scope: this establishes the *faithful* representation of §1.55.  The
  book's construction is additionally *exact* (preserves products, images and
  covers), which is what powers the §1.551 Horn-sentence metatheorem; the
  covariant-hom representation preserves limits but NOT images, so exactness is
  not established here.  An exact faithful representation needs the §1.543
  Capitalization Lemma — now PROVEN Sorry-free as
  `Fredy.capitalization_lemma` (`Fredy/CapDataWiring.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`).  Only the wiring that APPLIES it
  to upgrade this representation to an exact one remains to be done here.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_27
import Fredy.S1_31
import Fredy.S1_42
import Fredy.S1_52


open Freyd

universe w u v

namespace Freyd

/-! ## §1.55 The category of sets and its powers -/

/-- §1.55  The CATEGORY OF SETS 𝒮: objects are types, morphisms are functions. -/
instance setCat : Cat.{w} (Type w) where
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- §1.55  A POWER 𝒮^I of the category of sets: objects are I-indexed families
    of sets, morphisms are I-indexed families of functions, composed pointwise. -/
instance powerCat (I : Type w) : Cat.{w} (I → Type w) where
  Hom X Y := ∀ i, X i → Y i
  id _ := fun _ a => a
  comp f g := fun i a => g i (f i a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## §1.55 The product functor into a power, and its faithfulness -/

section
variable {𝒞 : Type u} [Cat.{w} 𝒞]

/-- The PRODUCT FUNCTOR of an I-indexed family of functors `F i : 𝒞 → 𝒮`,
    sending `A ↦ (i ↦ F i A)` into the power 𝒮^I. -/
def familyFunctor {I : Type w} (F : I → (𝒞 → Type w)) : 𝒞 → (I → Type w) :=
  fun A i => F i A

instance familyFunctorFunctor {I : Type w} (F : I → (𝒞 → Type w))
    [hF : ∀ i, Functor (F i)] : Functor (familyFunctor F) where
  map f := fun i => (hF i).map f
  map_id A := by funext i; exact (hF i).map_id A
  map_comp f g := by funext i; exact (hF i).map_comp f g

/-- §1.55 REDUCTION: if a family of functors `F i` COLLECTIVELY separates
    morphisms — agreeing on all `i` forces equality — then the product functor
    `familyFunctor F : 𝒞 → 𝒮^I` separates maps. -/
theorem familyFunctor_separates {I : Type w} (F : I → (𝒞 → Type w))
    [hF : ∀ i, Functor (F i)]
    (hsep : ∀ {A B : 𝒞} {f g : A ⟶ B}, (∀ i, (hF i).map f = (hF i).map g) → f = g) :
    SeparatesMaps (familyFunctor F) := by
  intro A B f g h
  exact hsep (fun i => congrFun h i)

end

/-! ## §1.55 The hom-functor representation and its exactness (limit side) -/

section HomRep

/-- The covariant hom-functor `Hom(i, -) : 𝒞 → 𝒮`, `f ↦ (h ↦ h ≫ f)` (§1.272). -/
instance homFunctor {𝒞 : Type u} [Cat.{w} 𝒞] (i : 𝒞) : Functor (fun A : 𝒞 => (i ⟶ A)) where
  map f := fun h => h ≫ f
  map_id A := by funext h; exact Cat.comp_id h
  map_comp f g := by funext h; exact (Cat.assoc h f g).symm

/-- The **Henkin–Lubkin representation** `T : 𝒞 → 𝒮^|𝒞|`, `A ↦ (i ↦ Hom(i, A))` —
    the witness used by `henkin_lubkin`, here named so its exactness can be stated. -/
def homRep (𝒞 : Type u) [Cat.{u} 𝒞] : 𝒞 → (𝒞 → Type u) := familyFunctor (fun i A => (i ⟶ A))

instance homRepFunctor (𝒞 : Type u) [Cat.{u} 𝒞] : Functor (homRep 𝒞) :=
  familyFunctorFunctor (fun i A => (i ⟶ A))

/-- The Henkin–Lubkin representation `homRep` SEPARATES MAPS (re-derives the
    faithfulness of `henkin_lubkin` for the explicit witness). -/
theorem homRep_separates (𝒞 : Type u) [Cat.{u} 𝒞] : SeparatesMaps (homRep 𝒞) := by
  intro A B f g h
  exact cayley_faithful f g (fun {X} hX => congrFun (congrFun h X) hX)

/-- **Exactness, limit side (i):** `homRep` PRESERVES monos.  `Hom(i, f)` is
    injective for every `i` precisely because `f` is left-cancellable, so the
    induced family of functions is a mono in the power `𝒮^|𝒞|`. -/
theorem homRep_preserves_mono (𝒞 : Type u) [Cat.{u} 𝒞] : PreservesMono (homRep 𝒞) := by
  intro X Y f hf W p q h
  funext i a
  exact hf (p i a) (q i a) (congrFun (congrFun h i) a)

/-- **Exactness, limit side (ii):** `homRep` REFLECTS monos.  Probe `Monic (T f)`
    with the representable at `W`: `k ↦ k ≫ g` and `k ↦ k ≫ h` agree after `T f`
    when `g ≫ f = h ≫ f`, so they are equal; evaluating at `id_W` gives `g = h`. -/
theorem homRep_reflects_mono (𝒞 : Type u) [Cat.{u} 𝒞] : ReflectsMono (homRep 𝒞) := by
  intro X Y f hf W g h hgh
  let p : (fun i => (i ⟶ W)) ⟶ homRep 𝒞 X := fun i k => k ≫ g
  let q : (fun i => (i ⟶ W)) ⟶ homRep 𝒞 X := fun i k => k ≫ h
  have hpq : p ≫ (homRepFunctor 𝒞).map f = q ≫ (homRepFunctor 𝒞).map f := by
    funext i k; show (k ≫ g) ≫ f = (k ≫ h) ≫ f
    rw [Cat.assoc, hgh, ← Cat.assoc]
  have hpq' : p = q := hf p q hpq
  simpa [p, q, Cat.id_comp] using congrFun (congrFun hpq' W) (Cat.id W)

/-- **Exactness, cover side (conditional):** in a regular category, if `i` is
    PROJECTIVE then `Hom(i, -)` carries a cover `f` to a surjection — every
    `h : i → Y` lifts through `f`.  Pull `f` back along `h`; the leg over `i` is a
    cover (`cover_pullback`), and projectivity splits it, giving the lift.
    (`hi` is `Projective i` of §1.57 written out; projectivity is precisely what
    the §1.543 capitalization supplies — now proven Sorry-free as
    `Fredy.capitalization_lemma` — so this pinpoints the remaining work for an
    *exact* Henkin–Lubkin representation as WIRING that proven lemma in.) -/
theorem hom_lifts_cover_of_projective {𝒞 : Type u} [Cat.{w} 𝒞] [HasPullbacks 𝒞]
    [PullbacksTransferCovers 𝒞] {i X Y : 𝒞}
    (hi : ∀ {P : 𝒞} (e : P ⟶ i), Cover e → ∃ s : i ⟶ P, s ≫ e = Cat.id i)
    {f : X ⟶ Y} (hf : Cover f) (h : i ⟶ Y) : ∃ h' : i ⟶ X, h' ≫ f = h := by
  let pb := HasPullbacks.has f h
  obtain ⟨s, hs⟩ := hi pb.cone.π₂ (cover_pullback h hf)
  refine ⟨s ≫ pb.cone.π₁, ?_⟩
  calc (s ≫ pb.cone.π₁) ≫ f = s ≫ (pb.cone.π₁ ≫ f) := Cat.assoc _ _ _
    _ = s ≫ (pb.cone.π₂ ≫ h) := by rw [pb.cone.w]
    _ = (s ≫ pb.cone.π₂) ≫ h := (Cat.assoc _ _ _).symm
    _ = h := by rw [hs, Cat.id_comp]

/-- **Exact Henkin–Lubkin, given capitalization:** if every object of the
    regular category `𝒞` is projective (a *capital* category — what §1.543
    delivers, now proven Sorry-free as `Fredy.capitalization_lemma`), then
    `homRep` preserves covers componentwise: `Hom(i, f)` is surjective at every
    index `i` for a cover `f`.  Combined with
    `homRep_preserves_mono`/`_reflects_mono`, this is the full exactness of the
    representation; the projectivity hypothesis is taken as `hproj` here, to be
    discharged by applying the (proven) capitalization lemma. -/
theorem homRep_preserves_cover_pointwise {𝒞 : Type u} [Cat.{u} 𝒞] [HasPullbacks 𝒞]
    [PullbacksTransferCovers 𝒞]
    (hproj : ∀ C : 𝒞, ∀ {P : 𝒞} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) (i : 𝒞) (h : homRep 𝒞 Y i) :
    ∃ h' : homRep 𝒞 X i, (homRepFunctor 𝒞).map f i h' = h :=
  hom_lifts_cover_of_projective (hproj i) hf h

end HomRep

/-! ## §1.55 The points functor 𝒞 → 𝒮 -/

section Points
variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞]

/-- §1.55  The POINTS (global-sections) functor `𝒞 → 𝒮`, `A ↦ (1 ⟶ A)`,
    `f ↦ (x ↦ x ≫ f)`.  (The points functor underlies the deferred *exact*
    representation; the faithful representation below uses the hom-functors.) -/
def Pts (A : 𝒞) : Type v := one ⟶ A

instance ptsFunctor : Functor (Pts (𝒞 := 𝒞)) where
  map f := fun x => x ≫ f
  map_id A := by funext x; exact Cat.comp_id x
  map_comp f g := by funext x; exact (Cat.assoc x f g).symm

end Points

/-! ## §1.55 Henkin-Lubkin representation theorem -/

/-- A `|𝒞|`-indexed family of functors into `𝒮` that COLLECTIVELY separate
    morphisms.  The family is the covariant hom-functor (Cayley/§1.272)
    representation `i ↦ Hom(i, -)`, `f ↦ (h ↦ h ≫ f)`; collective separation is
    `cayley_faithful` (taking `i = A`, `h = id_A`).  Constructive and choice-free,
    valid for ANY small category — the regularity hypothesis is not used here. -/
theorem exists_separating_family (𝒞 : Type u) [Cat.{u} 𝒞] [PreRegularCategory 𝒞] :
    ∃ (F : 𝒞 → (𝒞 → Type u)) (hF : ∀ i, Functor (F i)),
      ∀ {A B : 𝒞} {f g : A ⟶ B}, (∀ i, (hF i).map f = (hF i).map g) → f = g := by
  refine ⟨fun i A => (i ⟶ A), fun i => ⟨fun {_ _} f h => h ≫ f, ?_, ?_⟩, ?_⟩
  · intro A; funext h; exact Cat.comp_id h
  · intro A B C f g; funext h; exact (Cat.assoc h f g).symm
  · intro A B f g hsep
    exact cayley_faithful f g (fun {X} hX => congrFun (hsep X) hX)

/-- **§1.55 Henkin-Lubkin.**  Every small pre-regular category `𝒞` is faithfully
    represented in the power `𝒮^|𝒞|`: there is a functor `T : 𝒞 → 𝒮^𝒞` that
    separates morphisms.  The witness is the covariant hom-functor representation;
    the proof is Sorry-free and choice-free (depends only on `Quot.sound`, via
    `funext`).  See the file header for the faithful-vs-exact scope note. -/
theorem henkin_lubkin (𝒞 : Type u) [Cat.{u} 𝒞] [PreRegularCategory 𝒞] :
    ∃ (T : 𝒞 → (𝒞 → Type u)) (_ : Functor T), SeparatesMaps T := by
  obtain ⟨F, hF, hsep⟩ := exists_separating_family 𝒞
  letI : ∀ i, Functor (F i) := hF
  exact ⟨familyFunctor F, inferInstance, familyFunctor_separates F hsep⟩

/-! ## §1.551 Corollary: Horn sentence preservation  — DEFERRED (not stated here)

  §1.551: every Horn sentence in the predicates of regular categories true for the
  category of sets is true for every regular category.  This follows from the
  *exact* form of Henkin-Lubkin, which in turn needs the capitalization lemma
  (`Fredy.capitalization_lemma`, §1.543) — now PROVEN Sorry-free in
  `Fredy/CapDataWiring.lean`.  What remains for §1.551 is the exactness wiring,
  not the capitalization lemma itself.

  It is NOT stated as a theorem here: a faithful statement requires the Horn-sentence
  machinery (`HornSentence`/`HoldsIn`), which lives in `Fredy/S1_56.lean` — and S1_56
  imports this file, so referencing it here would be circular.  The faithful Horn
  reflection statement therefore lives downstream in S1_56
  (`horn_sentence_reflected_by_faithful`, §1.563), proven Sorry-free there as the
  honest content-bearing faithful version.  Per the integrity rule we do NOT emit a
  vacuous `: True` stub for §1.551 here. -/

end Freyd
