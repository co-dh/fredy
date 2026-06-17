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

/-- The binary coproduct A+B is the pushout of the two initial maps 0→A and 0→B.
    Any PushoutCocone (init A) (init B) automatically commutes (both composites go
    from 0 to c.pt, and the initial object has a unique map to every object). -/
private def coprod_is_pushout_of_init [HasBinaryCoproducts 𝒜]
    (A B : 𝒜) : HasPushout (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) where
  cocone := { pt := HasBinaryCoproducts.coprod A B
              ι₁ := HasBinaryCoproducts.inl
              ι₂ := HasBinaryCoproducts.inr
              w  := HasCoterminator.init_uniq _ _ }
  desc  := fun c => HasBinaryCoproducts.case c.ι₁ c.ι₂
  fac₁  := fun c => HasBinaryCoproducts.case_inl c.ι₁ c.ι₂
  fac₂  := fun c => HasBinaryCoproducts.case_inr c.ι₁ c.ι₂
  uniq  := fun c h h1 h2 => HasBinaryCoproducts.case_uniq c.ι₁ c.ι₂ h h1 h2

/-- **§1.655 step (i)**: a pre-topos functor preserves pullbacks of monics.
    Proof sketch (Freyd): the pullback (intersection) square of two monic
    subobjects `m, n` is bicartesian — also a PUSHOUT (this is the content of
    §1.651 amalgamation: the intersection legs `π₁, π₂` and the inclusions into
    the union present a pushout, and over the cospan `(m, n)` the square is
    simultaneously a pullback because the legs are monic with intersection apex).
    `T` preserves pushouts and monics, so the `T`-image is a pushout of two
    monics in ℬ, which (by the same amalgamation/effectiveness run in ℬ) is again
    the pullback of `T m, T n`.

    BLOCKED — genuine residual.  The bicartesian-square fact reduces to
    `amalgamation_lemma` (S1_64), whose two LEG-MONICITY obligations (`Mono u`,
    `Mono v`) are themselves `sorry`: they need the §1.543 effective-quotient
    zigzag/path-length descent over the generated equivalence relation, a
    closure-induction principle the `HasReflTransClosure` abstraction does not
    expose.  No bicartesian-of-monics lemma exists elsewhere in the repo.  Until
    that descent lands, step (i) cannot be closed without itself introducing a
    sorry.  Once it is closed, step (ii) (below) is already wired to it. -/
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

/-- **§1.655 step (ii)**: a pre-topos functor preserves equalizers — a genuine
    reduction to step (i), with NO independent obligation of its own.

    Proof (Freyd §1.434 + §1.655): the equalizer `m := heq.cone.map : E → A` of
    `f, g : A → B` is, by `isEqualizer_iff_isPullback`, the pullback in 𝒜 of the
    two graph maps `u := ⟨1_A, f⟩`, `v := ⟨1_A, g⟩ : A → A × B`.  Both graph maps
    are SPLIT monic (retraction `fst`), so step (i)
    (`preTopos_functor_preserves_monic_pullbacks`) applies: `F` carries that
    pullback to a pullback of `(F u, F v)` in ℬ.  Post-composing the cospan with
    the product-comparison iso `φ = ⟨F fst, F snd⟩` (iso by `pres_products`)
    rewrites it as the pullback of `⟨1_{FA}, F f⟩`, `⟨1_{FA}, F g⟩`
    (`isPullback_of_iso_cospan`), and `isEqualizer_iff_isPullback` run backwards
    in ℬ identifies `(F E, F m)` as the equalizer of `(F f, F g)`.

    The only residual is step (i)'s sorry; step (ii) itself is sorry-free. -/
theorem preTopos_functor_preserves_equalizers (hptf : PreToposFunctor F)
    {A B : 𝒜} (f g : A ⟶ B) (heq : HasEqualizer f g) :
    ∀ (c : EqualizerCone (hF.map f) (hF.map g)),
      ∃ u : c.dom ⟶ F heq.cone.dom,
        u ≫ hF.map heq.cone.map = c.map
        ∧ ∀ v : c.dom ⟶ F heq.cone.dom, v ≫ hF.map heq.cone.map = c.map → v = u := by
  -- `m : E → A` is the chosen equalizer of `f, g`; `heqUP` is its universal property.
  let E := heq.cone.dom
  let m : E ⟶ A := heq.cone.map
  have hmeq : m ≫ f = m ≫ g := heq.cone.eq
  have heqUP : (EqualizerCone.mk E m hmeq).IsEqualizer := fun d =>
    ⟨heq.lift d, heq.fac d, fun w hw => heq.uniq d w hw⟩
  -- Graph maps `u = ⟨1,f⟩`, `v = ⟨1,g⟩ : A → A×B`; both split monic (retraction `fst`).
  let u : A ⟶ prod A B := pair (Cat.id A) f
  let v : A ⟶ prod A B := pair (Cat.id A) g
  have humono : Mono u := mono_of_retraction u fst (fst_pair _ _)
  have hvmono : Mono v := mono_of_retraction v fst (fst_pair _ _)
  -- The equalizer cone `(E, m, m)` is a pullback of `(u, v)` in 𝒜 (§1.434).
  have hwUV : m ≫ u = m ≫ v := by
    show m ≫ pair (Cat.id A) f = m ≫ pair (Cat.id A) g
    rw [pair_uniq (m ≫ Cat.id A) (m ≫ f) (m ≫ pair (Cat.id A) f)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]),
        pair_uniq (m ≫ Cat.id A) (m ≫ g) (m ≫ pair (Cat.id A) g)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]), hmeq]
  let eqCone : Cone u v := Cone.mk E m m hwUV
  have hEqPB : eqCone.IsPullback :=
    (isEqualizer_iff_isPullback m hmeq).mp heqUP
  -- Package as a `HasPullback u v` whose distinguished cone is exactly `eqCone`,
  -- so step (i) yields the F-image universal property *for that very cone*.
  let pbUV : HasPullback u v :=
    { cone := eqCone
      lift := fun c => (hEqPB c).choose
      lift_fst := fun c => (hEqPB c).choose_spec.1.1
      lift_snd := fun c => (hEqPB c).choose_spec.1.2
      lift_uniq := fun c w h₁ h₂ => (hEqPB c).choose_spec.2 w h₁ h₂ }
  -- Step (i): `F` preserves the pullback `pbUV`; its image is a pullback of `(F u, F v)`.
  have hFpb := preTopos_functor_preserves_monic_pullbacks hptf u humono v hvmono pbUV
  have hFeqPB_uv : (Cone.mk (f := hF.map u) (g := hF.map v) (F E)
      (hF.map m) (hF.map m)
      (by rw [← hF.map_comp, ← hF.map_comp, hwUV])).IsPullback := by
    intro d
    obtain ⟨w, hw₁, hw₂, huniq⟩ := hFpb d
    exact ⟨w, ⟨hw₁, hw₂⟩, fun y hy₁ hy₂ => huniq y hy₁ hy₂⟩
  -- Product-comparison iso `φ = ⟨F fst, F snd⟩ : F(A×B) → FA×FB`; `F u ≫ φ = ⟨1,Ff⟩`.
  obtain ⟨φ', hφφ', _⟩ := hptf.pres_products (A := A) (B := B)
  have hFu_φ : hF.map u ≫ pair (hF.map (fst (A := A) (B := B))) (hF.map snd)
      = pair (Cat.id (F A)) (hF.map f) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← hF.map_comp]
      show hF.map (pair (Cat.id A) f ≫ fst) = Cat.id (F A); rw [fst_pair, hF.map_id]
    · rw [Cat.assoc, snd_pair, ← hF.map_comp]
      show hF.map (pair (Cat.id A) f ≫ snd) = hF.map f; rw [snd_pair]
  have hFv_φ : hF.map v ≫ pair (hF.map (fst (A := A) (B := B))) (hF.map snd)
      = pair (Cat.id (F A)) (hF.map g) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← hF.map_comp]
      show hF.map (pair (Cat.id A) g ≫ fst) = Cat.id (F A); rw [fst_pair, hF.map_id]
    · rw [Cat.assoc, snd_pair, ← hF.map_comp]
      show hF.map (pair (Cat.id A) g ≫ snd) = hF.map g; rw [snd_pair]
  -- Transport the cospan `(F u, F v)` to `(⟨1,Ff⟩, ⟨1,Fg⟩)` along the iso `φ`.
  have hFeqPB : (Cone.mk (f := pair (Cat.id (F A)) (hF.map f))
      (g := pair (Cat.id (F A)) (hF.map g)) (F E) (hF.map m) (hF.map m)
      (by rw [← hFu_φ, ← hFv_φ]; simp only [← Cat.assoc, ← hF.map_comp]; rw [hwUV])).IsPullback := by
    have key := isPullback_of_iso_cospan hFeqPB_uv
      (pair (hF.map (fst (A := A) (B := B))) (hF.map snd)) φ' hφφ'
      (by simp only [← Cat.assoc, ← hF.map_comp]; rw [hwUV])
    intro d
    have hdw' : d.π₁ ≫ (hF.map u ≫ pair (hF.map (fst (A := A) (B := B))) (hF.map snd))
        = d.π₂ ≫ (hF.map v ≫ pair (hF.map (fst (A := A) (B := B))) (hF.map snd)) := by
      rw [hFu_φ, hFv_φ]; exact d.w
    obtain ⟨z, ⟨hz₁, hz₂⟩, huniq⟩ := key (Cone.mk d.pt d.π₁ d.π₂ hdw')
    exact ⟨z, ⟨hz₁, hz₂⟩, fun y hy₁ hy₂ => huniq y hy₁ hy₂⟩
  -- Backwards `isEqualizer_iff_isPullback` in ℬ: `(F E, F m)` is the equalizer of `(Ff, Fg)`.
  have hFmeq : hF.map m ≫ hF.map f = hF.map m ≫ hF.map g := by
    rw [← hF.map_comp, ← hF.map_comp, hmeq]
  have hFeq_isEq : (EqualizerCone.mk (F E) (hF.map m) hFmeq).IsEqualizer :=
    (isEqualizer_iff_isPullback (hF.map m) hFmeq).mpr hFeqPB
  exact hFeq_isEq

/-- **§1.655 step (iii)**: a pre-topos functor preserves covers.
    Proof: in a pre-topos, every cover `f : A ↠ B` is the coequalizer of its
    kernel pair (`cover_is_coequalizer_of_level`, §1.566).  `T` preserves
    pushouts and `0`, so it preserves coequalizers; the image coequalizer is a
    cover by `bicart_repr_preserves_covers` (§1.581).

    BLOCKED — genuine residual.  The missing link is a
    `PreservesPushouts → preserves-coequalizers` bridge: a coequalizer is NOT a
    pushout of the parallel pair (wrong cocone shape), so `pres_pushouts` does
    not apply directly.  Reconstructing coequalizer-preservation from pushout-
    and `0`-preservation requires the §1.652 cover-quotient analysis specialised
    to `T`, which is not yet a lemma in this repo.  No shortcut via
    `PreservesMono` alone (a functor preserving monics need not preserve
    covers). -/
theorem preTopos_functor_preserves_covers (hptf : PreToposFunctor F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) : Cover (hF.map f) := by
  sorry

/-- **§1.655 (main theorem)**: A pre-topos functor T : A → B is a bicartesian
    representation — it preserves pullbacks, equalizers, covers, and coproducts.
    Statement is faithful to Freyd §1.655.  Part (c) (coproducts) and part (b)
    (equalizers, via step (ii)) are PROVED; part (a) (covers) reduces to step
    (iii).

    Residual blockers (only steps (i)/(iii) carry a sorry):
    - step (i): bicartesian-of-monics ⇒ `amalgamation_lemma` leg-monicity
      (§1.543 effective-quotient descent), sorry in S1_64.
    - step (iii): `PreservesPushouts → preserves-coequalizers` bridge (§1.652),
      not yet a lemma.
    Step (ii) is sorry-free: it is a real reduction to step (i) via
    `isEqualizer_iff_isPullback` + `pres_products` (so closing (i) closes (b)). -/
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
   fun A B => by
     -- F(coprod A B) is the pushout of F(init A) and F(init B) in ℬ.
     -- F(0) is initial in ℬ; uniqueness of maps from F(0) gives cocone commutativity.
     -- The inverse of case(F inl, F inr) comes from the pushout UMP.
     -- Let hpb : HasPushout (init A) (init B) be the coproduct, built explicitly.
     let hpb := coprod_is_pushout_of_init (𝒜 := 𝒜) A B
     -- Target cocone in ℬ: coprod(FA,FB) with inl_ℬ, inr_ℬ.
     -- Commutativity: F(init A) ≫ inl_ℬ and F(init B) ≫ inr_ℬ are both maps from F(0),
     -- equal by PreservesInitial.
     let tgt : PushoutCocone (hF.map (HasCoterminator.init (𝒞 := 𝒜) A))
                             (hF.map (HasCoterminator.init (𝒞 := 𝒜) B)) :=
       { pt := HasBinaryCoproducts.coprod (F A) (F B)
         ι₁ := HasBinaryCoproducts.inl
         ι₂ := HasBinaryCoproducts.inr
         w  := hptf.pres_initial
                 (hF.map (HasCoterminator.init (𝒞 := 𝒜) A) ≫ HasBinaryCoproducts.inl)
                 (hF.map (HasCoterminator.init (𝒞 := 𝒜) B) ≫ HasBinaryCoproducts.inr) }
     -- Apply PreservesPushouts with explicit instance hpb to obtain the inverse map.
     -- Type of inv: F hpb.cocone.pt ⟶ tgt.pt = F (coprod A B) ⟶ coprod(FA,FB) (by def of hpb).
     -- We use show/change to expose this definitional equality to Lean.
     suffices h : IsIso (HasBinaryCoproducts.case
         (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
         (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) :
       HasBinaryCoproducts.coprod (F A) (F B) ⟶ F hpb.cocone.pt) from h
     obtain ⟨inv, hinv1, hinv2, hinv_uniq⟩ := hptf.pres_pushouts
       (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) (h := hpb) tgt
     -- inv : F hpb.cocone.pt ⟶ tgt.pt = F (coprod A B) ⟶ coprod(FA,FB)
     -- hinv1 : hF.map hpb.cocone.ι₁ ≫ inv = tgt.ι₁
     --       i.e. hF.map inl ≫ inv = inl_ℬ  (since hpb.cocone.ι₁ = inl by definition)
     -- hinv2 : hF.map hpb.cocone.ι₂ ≫ inv = tgt.ι₂  i.e. hF.map inr ≫ inv = inr_ℬ
     refine ⟨inv, ?_, ?_⟩
     · -- case(F inl, F inr) ≫ inv = id_{coprod(FA,FB)}.
       -- By case_uniq, any h with inl ≫ h = inl, inr ≫ h = inr equals case(inl, inr).
       -- inl ≫ case(F inl, F inr) ≫ inv = F(inl) ≫ inv = inl_ℬ (hinv1 + case_inl).
       -- inl ≫ id = inl (comp_id).  So both equal case(inl, inr).
       -- case(inl, inr) = id by case_uniq.
       have hcase_id : HasBinaryCoproducts.case
           (HasBinaryCoproducts.inl (A := F A) (B := F B))
           (HasBinaryCoproducts.inr (A := F A) (B := F B)) = Cat.id _ :=
         (HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
       rw [← hcase_id]
       apply HasBinaryCoproducts.case_uniq
       · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hinv1
       · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact hinv2
     · -- inv ≫ case(F inl, F inr) = id_{F(coprod A B)}.
       -- Use uniqueness: both id and inv ≫ fwd are mediating maps to the self-cocone.
       let self_c : PushoutCocone (hF.map (HasCoterminator.init (𝒞 := 𝒜) A))
                                  (hF.map (HasCoterminator.init (𝒞 := 𝒜) B)) :=
         { pt := F hpb.cocone.pt
           ι₁ := hF.map (HasBinaryCoproducts.inl (A := A) (B := B))
           ι₂ := hF.map (HasBinaryCoproducts.inr (A := A) (B := B))
           w  := hptf.pres_initial _ _ }
       obtain ⟨mid, _hmid1, _hmid2, hmid_uniq⟩ := hptf.pres_pushouts
         (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) (h := hpb) self_c
       have heq_id : mid = Cat.id _ := (hmid_uniq (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
       have heq_cmp : mid = inv ≫ HasBinaryCoproducts.case
           (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
           (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) :=
         (hmid_uniq _ (by rw [← Cat.assoc, hinv1, HasBinaryCoproducts.case_inl])
                      (by rw [← Cat.assoc, hinv2, HasBinaryCoproducts.case_inr])).symm
       exact heq_cmp.symm.trans heq_id⟩

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
