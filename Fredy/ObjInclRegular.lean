/-
  §2.218 R3 plumbing — the colimit stage inclusion `objIncl i : A_i → Ā` is a `RegularFunctor`
  that REFLECTS ISOS, and `RegularFunctor` is closed under composition / contains the identity.

  These are the reusable pieces needed to expose the capitalization embedding `Map 𝒜 ↪ Ā`
  (= `objIncl i₀ ∘ base`, `base = id`) as a regular, iso-reflecting functor — the "step 3" crux
  of the STALK route to §2.218 (`Fredy/S2_218_Tabular.lean`).

  Mathlib-free: only `Fredy.*`.  All preservation/reflection facts for `objIncl` already live in
  `Capitalization`/`CatColimitRegular`; here we (a) lift the specific-cone `objIncl_preserves_pullbacks`
  to the generic `PreservesPullbacks` predicate, (b) prove the generic `PreservesImages` predicate by
  the cover∘mono argument (mirroring `homRep_preserves_images`, using only `objIncl_preservesCover`),
  and (c) package the five `RegularFunctor` fields.
-/
import Fredy.RelCat
import Fredy.Capitalization
import Fredy.CatColimitRegular

open Freyd
open Freyd.Colim
open Freyd.RelFunctor

namespace Freyd

universe v u

/-! ## `Subobject.map` composes -/

/-- Pushing a subobject through `F` then `G` is the same as pushing it through `G ∘ F`. -/
theorem Subobject.map_comp {C D E : Type u} [Cat.{u} C] [Cat.{u} D] [Cat.{u} E]
    {F : C → D} {G : D → E} [hF : Functor F] [hG : Functor G]
    (hpmF : PreservesMono F) (hpmG : PreservesMono G)
    {B : C} (S : Subobject C B) :
    Subobject.map (G ∘ F) (fun hm => hpmG (hpmF hm)) S
      = Subobject.map G hpmG (Subobject.map F hpmF S) := rfl

/-! ## `RegularFunctor` is closed under identity and composition -/

/-- The identity functor is regular. -/
theorem regularFunctor_id {C : Type u} [Cat.{u} C] [RegularCategory C] :
    RegularFunctor (fun X : C => X) where
  pres_prod := by
    intro A B
    -- comparison `pair (id fst) (id snd) = pair fst snd = id`, hence iso.
    show IsIso (pair (fst (A := A) (B := B)) snd)
    have h : pair (fst (A := A) (B := B)) snd = Cat.id (prod A B) :=
      (pair_uniq _ _ _ (Cat.id_comp _) (Cat.id_comp _)).symm
    rw [h]; exact ⟨Cat.id _, Cat.id_comp _, Cat.id_comp _⟩
  pres_pullback := fun _ _ _ hc => hc
  pres_covers := fun _ hf => hf
  pres_mono := fun hm => hm
  pres_image := fun _ _ hI => hI

/-- `RegularFunctor` composes: `pres_prod` via `preservesBinaryProducts_comp`; the other four fields
    compose directly (they are instance-free `∀`-statements), `pres_image` using `Subobject.map_comp`. -/
theorem regularFunctor_comp {C D E : Type u} [Cat.{u} C] [Cat.{u} D] [Cat.{u} E]
    [RegularCategory C] [RegularCategory D] [RegularCategory E]
    {F : C → D} {G : D → E} [hF : Functor F] [hG : Functor G]
    (hrF : RegularFunctor F) (hrG : RegularFunctor G) :
    RegularFunctor (G ∘ F) := by
  have pm : PreservesMono (G ∘ F) := fun hm => hrG.pres_mono (hrF.pres_mono hm)
  refine
    { pres_prod := preservesBinaryProducts_comp F G hrF.pres_prod hrG.pres_prod
      pres_pullback := fun f g c hc => hrG.pres_pullback _ _ _ (hrF.pres_pullback f g c hc)
      pres_covers := fun f hf => hrG.pres_covers _ (hrF.pres_covers f hf)
      pres_mono := pm
      pres_image := ?_ }
  intro A B f I hI
  -- `Subobject.map (G∘F) pm I = Subobject.map G hrG.pres_mono (Subobject.map F hrF.pres_mono I)`.
  rw [show (Subobject.map (G ∘ F) pm I)
        = Subobject.map G hrG.pres_mono (Subobject.map F hrF.pres_mono I) from rfl]
  exact hrG.pres_image _ _ (hrF.pres_image f I hI)

/-! ## The colimit stage inclusion `objIncl i` is a regular, iso-reflecting functor -/

/-- **(D) The stage inclusion reflects isos.**  Reformulates `homInclObj_isIso_reflects`
    against `stageInclFunctor` (whose `.map` is `homInclObj`), given conservative transitions
    `hcons`. -/
theorem objIncl_reflectsIso {ι : Type u} {D : Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    ∀ {x y : C.A i} (g : x ⟶ y),
      @IsIso C.Obj (colimitCat C hC) _ _ ((stageInclFunctor C hC i).map g) → IsIso g :=
  fun {_ _} g hiso => homInclObj_isIso_reflects C hC hcons g hiso

/-- **(B) The stage inclusion preserves images** (generic `PreservesImages`).  Mirrors
    `homRep_preserves_images`: a stage image `I` of `f` factors `f = ℓ ≫ I.arr` with `ℓ` a cover;
    `objIncl i` preserves the cover (`objIncl_preservesCover`) and the mono (`objIncl_preservesMono`),
    and a cover-then-mono factorization IS an image (`coverMono_isImage`).  The factorization map
    `ℓ` onto an image `I` is a cover by the elementary minimality argument (`S = ⟨·, m ≫ I.arr⟩`
    allows `f`, so `I ≤ S` retracts the mono `m`) — needing no per-stage `HasImages`/products,
    only `HasPullbacks C.Obj` (for `coverMono_isImage`). -/
theorem objIncl_preservesImages_generic {ι : Type u} {D : Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Cover φ → Cover ((C.functF hij).map φ))
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic ((C.functF hij).map φ))
    [hpull : @HasPullbacks C.Obj (colimitCat C hC)]
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    @PreservesImages (C.A i) C.Obj (C.catA i) (colimitCat C hC) (C.objIncl i)
      (stageInclFunctor C hC i) (objIncl_preservesMono C hC hmono i) := by
  letI : Cat C.Obj := colimitCat C hC
  intro A B f I hI
  -- `ℓ ≫ I.arr = f`; `ℓ` is a cover because `I` is the image of `f` (minimality retracts any mono).
  obtain ⟨ℓ, hℓ⟩ := hI.1
  have hℓcov : Cover ℓ := by
    intro Cc m g hm hgm
    -- `S = ⟨Cc, m ≫ I.arr⟩` allows `f`; minimality of `I` gives a retraction `d` of `m`.
    have hSmono : Monic (m ≫ I.arr) := by
      intro W a b hab; apply hm; apply I.monic; rw [Cat.assoc, Cat.assoc]; exact hab
    have hallows : Allows (Subobject.mk Cc (m ≫ I.arr) hSmono) f :=
      ⟨g, by show g ≫ (m ≫ I.arr) = f; rw [← Cat.assoc, hgm, hℓ]⟩
    obtain ⟨d, hd⟩ := hI.2 (Subobject.mk Cc (m ≫ I.arr) hSmono) hallows
    have hdm : d ≫ m = Cat.id I.dom := by
      apply I.monic; rw [Cat.id_comp, Cat.assoc, hd]
    exact ⟨d, by apply hm; rw [Cat.assoc, hdm, Cat.comp_id, Cat.id_comp], hdm⟩
  -- push the cover and the factorization through `objIncl i`.
  have hcov : @Cover C.Obj (colimitCat C hC) _ _ ((stageInclFunctor C hC i).map ℓ) :=
    objIncl_preservesCover C hC hfaith hcovpres ℓ hℓcov
  have hfac : (stageInclFunctor C hC i).map ℓ ≫ (stageInclFunctor C hC i).map I.arr
      = (stageInclFunctor C hC i).map f := by
    rw [← (stageInclFunctor C hC i).map_comp, hℓ]
  exact coverMono_isImage (objIncl_preservesMono C hC hmono i I.monic) hcov hfac

set_option maxHeartbeats 1000000 in
/-- **(A) The stage inclusion preserves pullbacks** (generic `PreservesPullbacks`).  For an
    arbitrary pullback cone `cone` over `(f, g)`, compare it to the §1.432 canonical pullback
    `K = products_equalizers_implies_pullbacks f g`: the comparison `u : cone.pt ⟶ K.cone.pt` is an
    iso (`isIso_of_two_pullbacks`).  `objIncl i` sends `K.cone` to a pullback
    (`objIncl_preserves_pullbacks`), and the functor image of an iso is an iso, so transporting the
    apex along `objIncl i u` (`isPullback_of_iso_apex`) makes `objIncl i cone` a pullback too; the
    legs agree by `← map_comp` on `u ≫ K.cone.πₖ = cone.πₖ`. -/
theorem objIncl_preservesPullbacks_generic {ι : Type u} {D : Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    @PreservesPullbacks (C.A i) C.Obj (C.catA i) (colimitCat C hC) (C.objIncl i)
      (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal (C.A i) := ht i
  letI : HasBinaryProducts (C.A i) := hp i
  letI : HasEqualizers (C.A i) := he i
  intro a b cc f g cone hcone
  -- the §1.432 canonical pullback `K` of `(f, g)` and the comparison `u` from `cone`.
  obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ := (products_equalizers_implies_pullbacks f g).cone_isPullback cone
  have huiso : IsIso u :=
    isIso_of_two_pullbacks hcone ((products_equalizers_implies_pullbacks f g).cone_isPullback) u hu₁ hu₂
  obtain ⟨u', huu', hu'u⟩ := huiso
  -- `objIncl i K.cone` is a pullback of `(homInclObj f, homInclObj g)`.
  have hImK := objIncl_preserves_pullbacks C hC ht htpres hp hpres hpres_pair he hepres hepres_lift i f g
  -- `map u`/`map u'` are mutually inverse (functor of an iso is an iso).
  have hij : (stageInclFunctor C hC i).map u ≫ (stageInclFunctor C hC i).map u'
      = Cat.id (C.objIncl i cone.pt) := by
    rw [← (stageInclFunctor C hC i).map_comp, huu', (stageInclFunctor C hC i).map_id]
  have hji : (stageInclFunctor C hC i).map u' ≫ (stageInclFunctor C hC i).map u
      = Cat.id (C.objIncl i (products_equalizers_implies_pullbacks f g).cone.pt) := by
    rw [← (stageInclFunctor C hC i).map_comp, hu'u, (stageInclFunctor C hC i).map_id]
  -- the leg equalities `map u ≫ homInclObj K.cone.πₖ = map cone.πₖ`.
  have e₁ : (stageInclFunctor C hC i).map u
        ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₁
      = (stageInclFunctor C hC i).map cone.π₁ := by
    have h := (stageInclFunctor C hC i).map_comp u (products_equalizers_implies_pullbacks f g).cone.π₁
    rw [hu₁] at h; exact h.symm
  have e₂ : (stageInclFunctor C hC i).map u
        ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₂
      = (stageInclFunctor C hC i).map cone.π₂ := by
    have h := (stageInclFunctor C hC i).map_comp u (products_equalizers_implies_pullbacks f g).cone.π₂
    rw [hu₂] at h; exact h.symm
  -- the transported cone (apex `objIncl cone.pt`) is a pullback.
  have w : ((stageInclFunctor C hC i).map u
        ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₁)
        ≫ (stageInclFunctor C hC i).map f
      = ((stageInclFunctor C hC i).map u
        ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₂)
        ≫ (stageInclFunctor C hC i).map g := by
    rw [e₁, e₂, ← (stageInclFunctor C hC i).map_comp, ← (stageInclFunctor C hC i).map_comp, cone.w]
  have hres := isPullback_of_iso_apex hImK ((stageInclFunctor C hC i).map u)
    ((stageInclFunctor C hC i).map u') hij hji w
  -- transport `hres` to the target cone (legs `map cone.πₖ`) via `e₁`, `e₂`.
  intro d
  obtain ⟨v, ⟨hv₁, hv₂⟩, huniq⟩ := hres d
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · show v ≫ (stageInclFunctor C hC i).map cone.π₁ = d.π₁
    rw [← e₁]; exact hv₁
  · show v ≫ (stageInclFunctor C hC i).map cone.π₂ = d.π₂
    rw [← e₂]; exact hv₂
  · intro v' hv'₁ hv'₂
    refine huniq v' ?_ ?_
    · show v' ≫ ((stageInclFunctor C hC i).map u
          ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₁) = d.π₁
      rw [e₁]
      exact (show v' ≫ (stageInclFunctor C hC i).map cone.π₁ = d.π₁ from hv'₁)
    · show v' ≫ ((stageInclFunctor C hC i).map u
          ≫ homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₂) = d.π₂
      rw [e₂]
      exact (show v' ≫ (stageInclFunctor C hC i).map cone.π₂ = d.π₂ from hv'₂)

set_option maxHeartbeats 1000000 in
/-- **(C) The stage inclusion is a regular functor.**  Packages (A) `pres_pullback`, (B)
    `pres_image`, `objIncl_preservesBinaryProducts` (`pres_prod`), `objIncl_preservesCover`
    (`pres_covers`) and `objIncl_preservesMono` (`pres_mono`) into a `RegularFunctor` record.

    `RegularFunctor`'s `pres_prod` field references the ambient `RegularCategory.toHasBinaryProducts`;
    the preservation proof only holds for the COLIMIT-canonical products (`hp i` /
    `colimitHasBinaryProducts …`).  So the two `RegularCategory` instances cannot be received as
    abstract arguments (the comparison `@fst … (hp i)` is not defeq to `@fst … hRA.toHasBinaryProducts`
    for an abstract `hRA`); they are PRODUCED here from the colimit data, mirroring
    `capitalization_of_capData_regular_of_covers`: the stage one from `ht/hp/he/hi/hstagePTC`, the
    colimit one as `colimitPreRegular` + `colimitHasImages` (image-preservation derived from
    `hcovpres`+`hmono` via `transitions_preserve_images`).  Hence the existential over the two
    instances. -/
theorem objIncl_regularFunctor {ι : Type u} {D : Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic ((C.functF hij).map φ))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Cover φ → Cover ((C.functF hij).map φ))
    (hi : ∀ i, HasImages (C.A i))
    (hstagePTC : ∀ (i : ι), letI : HasTerminal (C.A i) := ht i;
        letI : HasBinaryProducts (C.A i) := hp i; letI : HasEqualizers (C.A i) := he i;
        letI : HasPullbacks (C.A i) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩;
        PullbacksTransferCovers (C.A i))
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hpres hpres_pair he hepres hepres_lift
        ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    ∃ (hRA : @RegularCategory (C.A i) (C.catA i)) (hRC : @RegularCategory C.Obj (colimitCat C hC)),
      @RelFunctor.RegularFunctor (C.A i) C.Obj (C.catA i) (colimitCat C hC)
        (C.objIncl i) (stageInclFunctor C hC i) hRA hRC := by
  letI : Cat C.Obj := colimitCat C hC
  -- the stage `RegularCategory` (canonical products `hp i`, pullbacks from §1.432).
  letI iT : HasTerminal (C.A i) := ht i
  letI iP : HasBinaryProducts (C.A i) := hp i
  letI iE : HasEqualizers (C.A i) := he i
  letI iPB : HasPullbacks (C.A i) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  letI iIm : HasImages (C.A i) := hi i
  letI iPTC : PullbacksTransferCovers (C.A i) := hstagePTC i
  letI regA : @RegularCategory (C.A i) (C.catA i) :=
    { toHasTerminal := iT, toHasBinaryProducts := iP, toHasPullbacks := iPB,
      toHasImages := iIm, toPullbacksTransferCovers := iPTC }
  -- the colimit `RegularCategory`: pre-regular (`colimitPreRegular`) + images (`colimitHasImages`).
  letI hPre : @PreRegularCategory C.Obj (colimitCat C hC) :=
    colimitPreRegular C hC ht htpres hp hpres hpres_pair he hepres hepres_lift hcanon
  have himgpres : ∀ {a b : ι} (hab : D.le a b) {X Y : C.A a} (f : X ⟶ Y),
      IsImage ((C.functF hab).map f)
        (@Subobject.map _ _ (C.catA a) (C.catA b) (C.F hab) (C.functF hab)
          (fun {_ _} {φ} hφ => hmono hab φ hφ) _ (@image _ (C.catA a) (hi a) _ _ f)) := by
    intro a b hab X Y f
    letI : HasImages (C.A a) := hi a
    letI : HasBinaryProducts (C.A b) := hp b
    letI : HasEqualizers (C.A b) := he b
    letI : HasPullbacks (C.A b) := ⟨fun p q => products_equalizers_implies_pullbacks p q⟩
    exact Colim.transitions_preserve_images (C.F hab) (hF := C.functF hab)
      (fun {_ _} {φ} hφ => hmono hab φ hφ) (fun {_ _} φ hφ => hcovpres hab φ hφ) f
  letI hImg : @HasImages C.Obj (colimitCat C hC) :=
    Colim.colimitHasImages C hC hi hfaith (fun {_ _} hab {_ _} {φ} hφ => hmono hab φ hφ) himgpres
  letI regC : @RegularCategory C.Obj (colimitCat C hC) := { hPre with toHasImages := hImg }
  refine ⟨regA, regC, ?_⟩
  letI : @Functor (C.A i) (C.catA i) C.Obj (colimitCat C hC) (C.objIncl i) := stageInclFunctor C hC i
  exact
    { pres_prod := objIncl_preservesBinaryProducts C hC hp hpres hpres_pair i
      pres_pullback :=
        objIncl_preservesPullbacks_generic C hC ht htpres hp hpres hpres_pair he hepres hepres_lift i
      pres_covers := fun {_ _} φ hφ => objIncl_preservesCover C hC hfaith hcovpres φ hφ
      pres_mono := objIncl_preservesMono C hC hmono i
      pres_image := objIncl_preservesImages_generic C hC hfaith hcovpres hmono i }

end Freyd
