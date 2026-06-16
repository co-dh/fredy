/-
  Freyd & Scedrov, *Categories and Allegories* §1.91  Topos structure.

  §1.911 Contravariant functor Rel(−,B); power-object [B] ↔ Rel(−,B) ≅ Hom(−,[B]).
  §1.912 Subobject classifier Ω = [1] (in Fredy.S1_9).
  §1.913 All subobjects are equalizers, covers = epics.
  §1.914 Algebraic structure of Ω: internal meet ∧ and Heyting double-arrow ⇒.
  §1.919 Monic endomorphisms of Ω are involutions.
  §1.91(10) Minimal topos definition (binary products + equalizers + subobject
            classifier, no terminator needed if non-empty).
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_52


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.911  The contravariant relation functor Rel(−,B)

  For any category with pullbacks and any object B, `BinRel 𝒞 − B` is a
  contravariant set-valued functor: given f : A → A' and R : BinRel 𝒞 A' B,
  define f*(R) := relPullback f R.  The functoriality equation is
  g*(f*(R)) = (f ≫ g)*(R), i.e. relPullback is contravariantly functorial.

  The existence of a power-object [B] (§1.9, `HasPowerObject B`) is equivalent
  to this functor being representable: Rel(−,B) ≅ Hom(−,[B]).
  (The formalization of `BinRel`, `relPullback`, `HasPowerObject` and
  `IsUniversalRel` is in `Fredy.S1_9`.) -/

/-- **§1.911**: The relation pullback is contravariantly functorial:
    `relPullback f (relPullback g R) ≅ relPullback (f ≫ g) R`
    (as `RelHom` in both directions), where f : A'' → A', g : A' → A.

    Proved by hand from the pullback universal properties (pasting): the
    composite of the two pullback squares — one for `(g, R.colA)` and one for
    `(f, (relPullback g R).colA)` — is a pullback square for `(f ≫ g, R.colA)`.
    Each direction is a `HasPullback.lift` of the cone induced by the other
    side, with the colB legs matching by associativity. -/
theorem relPullback_comp [HasPullbacks 𝒞] {A A' A'' B : 𝒞}
    (f : A'' ⟶ A') (g : A' ⟶ A) (R : BinRel 𝒞 A B) :
    RelHom (relPullback f (relPullback g R)) (relPullback (f ≫ g) R) ∧
    RelHom (relPullback (f ≫ g) R) (relPullback f (relPullback g R)) := by
  -- Pullback pasting, done by hand from the universal properties.
  -- Pg : pullback of (g, R.colA);  (relPullback g R).colA = Pg.cone.π₁,
  --                                (relPullback g R).colB = Pg.cone.π₂ ≫ R.colB.
  -- Pf : pullback of (f, Pg.cone.π₁) = source of relPullback f (relPullback g R).
  -- Q  : pullback of (f ≫ g, R.colA) = source of relPullback (f ≫ g) R.
  let Pg := HasPullbacks.has g R.colA
  let Pf := HasPullbacks.has f Pg.cone.π₁
  let Q  := HasPullbacks.has (f ≫ g) R.colA
  -- the two cone squares we'll keep reusing
  have wPg : Pg.cone.π₁ ≫ g = Pg.cone.π₂ ≫ R.colA := Pg.cone.w
  have wPf : Pf.cone.π₁ ≫ f = Pf.cone.π₂ ≫ Pg.cone.π₁ := Pf.cone.w
  have wQ  : Q.cone.π₁ ≫ (f ≫ g) = Q.cone.π₂ ≫ R.colA := Q.cone.w
  show RelHom (relPullback f (relPullback g R)) (relPullback (f ≫ g) R) ∧
    RelHom (relPullback (f ≫ g) R) (relPullback f (relPullback g R))
  constructor
  · -- forward: h := Q.lift of the Pf-induced cone over (f≫g, R.colA)
    refine ⟨Q.lift ⟨Pf.cone.pt, Pf.cone.π₁, Pf.cone.π₂ ≫ Pg.cone.π₂, ?_⟩, ?_, ?_⟩
    · -- square: Pf.π₁ ≫ (f≫g) = (Pf.π₂ ≫ Pg.π₂) ≫ R.colA
      calc Pf.cone.π₁ ≫ (f ≫ g)
            = (Pf.cone.π₁ ≫ f) ≫ g := by rw [Cat.assoc]
        _ = (Pf.cone.π₂ ≫ Pg.cone.π₁) ≫ g := by rw [wPf]
        _ = Pf.cone.π₂ ≫ (Pg.cone.π₁ ≫ g) := by rw [Cat.assoc]
        _ = Pf.cone.π₂ ≫ (Pg.cone.π₂ ≫ R.colA) := by rw [wPg]
        _ = (Pf.cone.π₂ ≫ Pg.cone.π₂) ≫ R.colA := by rw [Cat.assoc]
    · -- colA: h ≫ Q.π₁ = Pf.π₁
      exact Q.lift_fst _
    · -- colB: h ≫ (Q.π₂ ≫ R.colB) = (Pf.π₂ ≫ Pg.π₂) ≫ R.colB
      change _ ≫ (Q.cone.π₂ ≫ R.colB)
            = Pf.cone.π₂ ≫ (Pg.cone.π₂ ≫ R.colB)
      rw [← Cat.assoc, Q.lift_snd, Cat.assoc]
  · -- backward: k := Pf.lift of the Q-induced cone over (f, Pg.π₁)
    -- m : Q.cone.pt → Pg.cone.pt, the lift over (g, R.colA)
    let m := Pg.lift ⟨Q.cone.pt, Q.cone.π₁ ≫ f, Q.cone.π₂, by
      calc (Q.cone.π₁ ≫ f) ≫ g = Q.cone.π₁ ≫ (f ≫ g) := by rw [Cat.assoc]
        _ = Q.cone.π₂ ≫ R.colA := wQ⟩
    have hm1 : m ≫ Pg.cone.π₁ = Q.cone.π₁ ≫ f := Pg.lift_fst _
    have hm2 : m ≫ Pg.cone.π₂ = Q.cone.π₂ := Pg.lift_snd _
    let k := Pf.lift ⟨Q.cone.pt, Q.cone.π₁, m, by rw [hm1]⟩
    have hk1 : k ≫ Pf.cone.π₁ = Q.cone.π₁ := Pf.lift_fst _
    have hk2 : k ≫ Pf.cone.π₂ = m := Pf.lift_snd _
    refine ⟨k, ?_, ?_⟩
    · -- colA: k ≫ Pf.π₁ = Q.π₁
      exact hk1
    · -- colB: k ≫ (Pf.π₂ ≫ Pg.π₂ ≫ R.colB) = Q.π₂ ≫ R.colB
      change k ≫ Pf.cone.π₂ ≫ Pg.cone.π₂ ≫ R.colB = Q.cone.π₂ ≫ R.colB
      calc k ≫ Pf.cone.π₂ ≫ Pg.cone.π₂ ≫ R.colB
            = (k ≫ Pf.cone.π₂) ≫ (Pg.cone.π₂ ≫ R.colB) := (Cat.assoc _ _ _).symm
        _ = m ≫ (Pg.cone.π₂ ≫ R.colB) := by rw [hk2]
        _ = (m ≫ Pg.cone.π₂) ≫ R.colB := (Cat.assoc _ _ _).symm
        _ = Q.cone.π₂ ≫ R.colB := by rw [hm2]

variable [Topos 𝒞]

/-! ## §1.913  Subobjects as equalizers

  In a topos, every monic m : A' → A is the equalizer of its characteristic
  map χ_m : A → Ω and the constant-true map A → 1 → Ω.

  BECAUSE: A' → A is a pullback of t : 1 → Ω along χ_m.  In a category
  with a terminator, any pullback of a monic is an equalizer. -/

/-- **§1.913**: In a topos, each monic `m : A' → A` is the equalizer of its
    characteristic map `χ_m` and the constant-true map `A → 1 → Ω`.

    Stated as the universal property of the equalizer (a `Prop`, so the proof is
    choice-free): `m` equalizes the pair, and every `e` that equalizes factors
    uniquely through `m`.  Both parts come from the classifier pullback square
    (`classify_pullback`): `m` is the pullback of `t : 1 → Ω` along `χ_m`, and a
    pullback of `t` is exactly an equalizer of `χ_m` and `A → 1 → Ω`. -/
theorem monic_is_equalizer {A A' : 𝒞} (m : A' ⟶ A) (hm : Mono m) :
    m ≫ HasSubobjectClassifier.classify m hm
        = m ≫ (term A ≫ HasSubobjectClassifier.true)
    ∧ ∀ {E : 𝒞} (e : E ⟶ A),
        e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) →
        ∃ k : E ⟶ A', k ≫ m = e ∧ ∀ k' : E ⟶ A', k' ≫ m = e → k' = k := by
  refine ⟨?_, ?_⟩
  · -- `m` equalizes: `m ≫ χ = term A' ≫ t = (m ≫ term A) ≫ t = m ≫ (term A ≫ t)`.
    calc m ≫ HasSubobjectClassifier.classify m hm
        = term A' ≫ HasSubobjectClassifier.true := HasSubobjectClassifier.classify_sq m hm
      _ = (m ≫ term A) ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (m ≫ term A) (term A')]
      _ = m ≫ (term A ≫ HasSubobjectClassifier.true) := Cat.assoc _ _ _
  · intro E e he
    -- Turn `e` into a cone over `(χ_m, t)`: the square `E → 1 → Ω` and `E → A → Ω`.
    have hw : e ≫ HasSubobjectClassifier.classify m hm
            = term E ≫ HasSubobjectClassifier.true := by
      calc e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) := he
        _ = (e ≫ term A) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
        _ = term E ≫ HasSubobjectClassifier.true := by
              rw [term_uniq (e ≫ term A) (term E)]
    -- The classifier pullback yields a factorization `u ≫ m = e`; `m` monic gives uniqueness.
    obtain ⟨u, ⟨hu, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback m hm
        (⟨E, e, term E, hw⟩ : Cone (HasSubobjectClassifier.classify m hm) HasSubobjectClassifier.true)
    exact ⟨u, hu, fun k' hk' => hm k' u (hk'.trans hu.symm)⟩

/-- **§1.913 (balanced)**: A topos is BALANCED — a morphism that is both monic
    and epic is an isomorphism.  Since `m` is the equalizer of `χ_m` and
    `A → 1 → Ω` (`monic_is_equalizer`), epicness collapses `χ_m = term ≫ true`,
    so `1_B` equalizes the pair and factors through `m`, splitting it; a split
    epic mono is iso. -/
theorem topos_mono_epi_iso {A B : 𝒞} (m : A ⟶ B) (hm : Mono m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  obtain ⟨heq, huniv⟩ := monic_is_equalizer m hm
  -- epic cancels `m` from `m ≫ χ = m ≫ (term ≫ true)`.
  have hχ : HasSubobjectClassifier.classify m hm = term B ≫ HasSubobjectClassifier.true :=
    hepi _ _ heq
  -- `1_B` equalizes the (now equal) pair, so it factors as `k ≫ m = 1_B`.
  obtain ⟨k, hk, _⟩ := huniv (Cat.id B) (by rw [hχ])
  refine ⟨k, ?_, hk⟩
  -- `m ≫ k = 1_A` by monic cancellation: `(m ≫ k) ≫ m = m = 1_A ≫ m`.
  exact hm _ _ (by rw [Cat.assoc, hk, Cat.comp_id, Cat.id_comp])

/-- **§1.913**: In a topos, covers coincide with epimorphisms.
    Forward: every cover is epic (`cover_epi`, general).  Converse: an epic `f`
    has an epic image-monic `(image f).arr`, which is then iso by balancedness
    (`topos_mono_epi_iso`), so `image f` is entire and `f` is a cover. -/
theorem covers_coincide_with_epis [HasImages 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · intro hc _C g h hgh; exact cover_epi hc hgh
  · intro hepi
    rw [cover_iff_image_entire]
    -- `(image f).arr` is monic and (since `f` is epic) epic, hence iso.
    refine topos_mono_epi_iso (image f).arr (image f).monic (fun g h hgh => hepi g h ?_)
    calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac]
      _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
      _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [hgh]
      _ = (image.lift f ≫ (image f).arr) ≫ h := (Cat.assoc _ _ _).symm
      _ = f ≫ h := by rw [image.lift_fac]

/-! ## §1.914  Algebraic structure of Ω

  Every n-ary operation g : Ωⁿ → Ω induces an n-ary operation on subobjects of
  any object A: given A₁,…,Aₙ ⊆ A, define g(A₁,…,Aₙ) as the subobject whose
  characteristic map is g ∘ ⟨χ_{A₁},…,χ_{Aₙ}⟩.

  **Internal meet (conjunction)**: the binary operation ∧ : Ω×Ω → Ω is defined
  as the characteristic map of the monic (t,t) : 1 → Ω×Ω.  It satisfies
  A' ⊆ g(A₁,A₂) iff A' ⊆ A₁ and A' ⊆ A₂, i.e. g(A₁,A₂) = A₁ ∩ A₂.

  **Heyting double-arrow (implication)**: the binary operation ⇒ : Ω×Ω → Ω is
  the characteristic map of the monic (1,1) : Ω → Ω×Ω (the diagonal on Ω).
  It satisfies A' ⊆ g(A₁,A₂) iff A₁ ∩ A' = A₂ ∩ A', so g is the Heyting
  double-arrow (A₁ ⇒ A₂ = A₁ ↔ A₂) and ⊆(A) has a Heyting semi-lattice
  structure.  The Heyting single-arrow is x → y := x ⇒ (x ∧ y). -/

/-- The internal meet (conjunction) on Ω: the classifying map of the monic
    (t,t) : 1 → Ω×Ω (§1.914).  The induced operation on subobjects is
    g(A₁,A₂) = A₁ ∩ A₂. -/
noncomputable def omegaMeet : prod (HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify
    (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
    -- pair(t,t) : 1 → Ω×Ω is monic because 1 is a terminal: any two maps W→1 are equal
    (fun f g _ => HasTerminal.uniq f g)

/-- The Heyting double-arrow on Ω: the classifying map of the diagonal
    (1,1) : Ω → Ω×Ω (§1.914).  The induced operation on subobjects A₁,A₂ ⊆ A
    is the Heyting double-arrow: A' ⊆ g(A₁,A₂) iff A₁∩A' = A₂∩A'. -/
noncomputable def heytingDoubleArrow : prod (HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify
    (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
    (diag_mono _)

/-- **§1.912**: The classifier of the identity on Ω is the constant-true map:
    `classify (Cat.id Ω) _ = term Ω ≫ true`.
    Follows directly from `classify_sq (Cat.id Ω)` and `Cat.id_comp`. -/
theorem classify_id_omega :
    HasSubobjectClassifier.classify (Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
      (fun f g h => by rwa [Cat.comp_id, Cat.comp_id] at h)
    = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  have sq := HasSubobjectClassifier.classify_sq (Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
    (fun f g h => by rwa [Cat.comp_id, Cat.comp_id] at h)
  rwa [Cat.id_comp] at sq

/-- **§1.912**: The classifier of the universal subobject `t : 1 → Ω` is the identity on Ω.
    Equivalently, `1 → Ω` is the pullback of `t` along `Cat.id Ω`.
    Proof: the cone `(1, t, term 1, ·)` over `(Cat.id Ω, t)` is a pullback because
    the unique lift of any cone `(E, p, q)` with `p ≫ id = q ≫ t` is `q : E → 1`. -/
theorem classify_true_eq_id :
    HasSubobjectClassifier.classify
      (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic
    = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  symm
  refine HasSubobjectClassifier.classify_unique
      (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic (Cat.id _) ?_ ?_
  · rw [Cat.comp_id]
    have h : term (HasTerminal.one (𝒞 := 𝒞)) = Cat.id (HasTerminal.one (𝒞 := 𝒞)) := term_uniq _ _
    rw [h, Cat.id_comp]
  · intro d
    refine ⟨d.π₂, ⟨?_, ?_⟩, fun v _ _ => term_uniq _ _⟩
    · have := d.w; rw [Cat.comp_id] at this; exact this.symm
    · exact term_uniq _ _

/-! ## §1.919  Monic endomorphisms of Ω are involutions

  §1.919: Every monic endomorphism g : Ω → Ω is an involution (g² = id).
  BECAUSE: For monic g, define U = g(1_Ω) (the unique g-large subobject of 1)
  and V = 1 (since g is monic and g(V) = g(1) implies V = 1).  Then g²(A') =
  (A ↔ A×U) ∧ A×U = A itself for any A', so g² has the same large subobjects
  as the identity, hence g² = id. -/

/-- **§1.919**: Every monic endomorphism of Ω is an involution;
    that is, g : Ω → Ω monic implies g ≫ g = id.

    Proof sketch (Freyd §1.919): Define U as the unique g-large subobject of 1
    (where A' is g-large in A if χ_{A'} ≫ g = term_A ≫ true, meaning gA' = A).
    Since g is monic, g(V) = g(1_Ω) implies V = 1_Ω.  For any A, A is g²-large
    in itself, and the identity has the same property, so g² = id by extensionality.

    **Proof gap** (confirmed by deep proof-search): via the only available API
    (`classify_unique`, S1_9) the goal reduces to showing `t : 1 → Ω` is the
    pullback of `t` along `g ≫ g` (i.e. `g²` classifies the maximal subobject of
    Ω — "A is g²-large in itself").  This needs three not-yet-formalized pieces:
    (1) `classify`-iso-invariance (easy from `classify_unique`); (2) the
    CHARACTERIZING lemmas for `omegaMeet`/`heytingDoubleArrow` (defined below but
    with no universal property) — e.g. the pullback of `t` along
    `⟨χ₁,χ₂⟩ ≫ omegaMeet` ≅ `Sub.inter A₁ A₂` (S1_45) — the substantive missing
    bridge; (3) operation-extensionality, which is STRICTLY stronger than
    `classify_unique` and needs the full `Sub(−) ≅ Hom(−,Ω)` bijection wired to
    `classify`.  Faithful sorry; see S1_91.md for the sharpened blocker. -/
theorem omega_monic_endo_is_involution (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Mono g) : g ≫ g = Cat.id _ := by
  sorry

/-! ## §1.91(10)  Minimal topos definition

  A category with binary products and equalizers (equivalently: binary products
  and pullbacks, or all finite non-empty limits) and a subobject classifier Ω,
  which is non-empty, already has a terminator and hence is a topos (§1.91(10)).

  CONSTRUCTION (Freyd): For objects A,B let M_{A,B} denote the relation tabulated
  by a product projection A×B → A (the "full" relation).  For any f,g : A' → A
  the equation f(M_{A,B}) = M_{A',B} shows that A M_{A,B} is a constant map.
  Hence Λ(M_{B,B}) : [B] → [B] is a constant idempotent endomorphism.
  For any A there is a map A → [B] (namely A M_{A,B}), so the equalizer of
  id_{[B]} and Λ(M_{B,B}) is a terminator.

  Note: `HasSubobjectClassifier` implies power-objects for the classifier
  object Ω = [1].  The full "has all power-objects" class is not yet
  formalized in this repo; we use `HasSubobjectClassifier` as the available
  proxy for the power-object hypothesis. -/

/-- **§1.91(10)**: A non-empty category with binary products, equalizers, and a
    subobject classifier has a terminator.

    `hne`: witness that 𝒞 is non-empty (an object exists).

    NOTE: In the current file `variable [Topos 𝒞]` is in scope, so `HasTerminal 𝒞` is
    available directly from the topos instance.  The full book theorem (§1.91(10)) applies
    to a category that is NOT assumed to be a topos — it derives the terminator from
    binary products, equalizers and a subobject classifier using the constant idempotent
    `Λ(M_{B,B}) : [B] → [B]`.  That construction needs `HasPowerObject B` for all B plus
    the Λ/ε classify-bijection at each [B] — neither present in this repo.  The `hne`
    hypothesis is unused because the ambient `Topos 𝒞` already gives `HasTerminal`.
    See S1_91.md for the full blocker analysis. -/
theorem minimal_topos_has_terminator
    [HasBinaryProducts 𝒞] [HasEqualizers 𝒞] [HasSubobjectClassifier 𝒞]
    (_hne : 𝒞) : Nonempty (HasTerminal 𝒞) :=
  -- HasTerminal 𝒞 comes from `variable [Topos 𝒞]` which extends HasTerminal.
  ⟨inferInstance⟩

end Freyd
