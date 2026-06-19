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

/-- **§1.912 (bijection, surjective half)**: `classify` is SURJECTIVE onto
    `Hom(A, Ω)` — every map `χ : A → Ω` is the characteristic map of some monic,
    namely the pullback projection `π₁ : P → A` of the universal subobject
    `t : 1 → Ω` along `χ`.

    Together with `classify_unique` (which is the injective half: two monics with
    the same `classify` are isomorphic-as-subobjects via the common pullback of
    `t`) this is the full subobject classifier bijection `Sub(A) ≅ Hom(A, Ω)`.

    Proof: `P := pullback (χ, t)`.  Its `π₁` is monic because `t` is monic
    (`mono_pullback`), the cone square gives `π₁ ≫ χ = π₂ ≫ t = term P ≫ t`
    (using `term_uniq` to replace `π₂ : P → 1` by `term P`), and that very square
    is a pullback of `t` along `χ`, so `classify_unique` forces `χ = classify π₁`. -/
theorem classify_surjective {A : 𝒞}
    (χ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    ∃ (P : 𝒞) (m : P ⟶ A) (hm : Mono m), HasSubobjectClassifier.classify m hm = χ := by
  -- P = pullback of (χ, t); π₁ : P → A is the monic subobject classified by χ.
  let Pb := HasPullbacks.has χ HasSubobjectClassifier.true
  have hmono : Mono Pb.cone.π₁ :=
    mono_pullback χ HasSubobjectClassifier.true HasSubobjectClassifier.true_monic Pb
  refine ⟨Pb.cone.pt, Pb.cone.π₁, hmono, ?_⟩
  -- the cone square, with π₂ : P → 1 replaced by the canonical term P.
  have hsq : Pb.cone.π₁ ≫ χ = term Pb.cone.pt ≫ HasSubobjectClassifier.true := by
    rw [Pb.cone.w, term_uniq Pb.cone.π₂ (term Pb.cone.pt)]
  -- χ classifies π₁: the chosen pullback IS the classifying pullback of t along χ.
  symm
  refine HasSubobjectClassifier.classify_unique Pb.cone.π₁ hmono χ hsq ?_
  -- the square (P, π₁, term P, hsq) over (χ, t) is a pullback — same data as Pb.cone.
  intro d
  refine ⟨Pb.lift ⟨d.pt, d.π₁, d.π₂, d.w⟩, ⟨Pb.lift_fst _, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  exact Pb.lift_uniq ⟨d.pt, d.π₁, d.π₂, d.w⟩ v hv₁ (term_uniq _ _)

/-- **§1.912 (classify naturality under pullback)**: the characteristic map of an
    inverse image `f# S` is `f ≫ χ_S`.  Equivalently, `Sub(−) ≅ Hom(−,Ω)` is
    natural: pulling a subobject back along `f` precomposes its classifier with `f`.

    Proof by pullback pasting against `classify_unique`.  The pasted square (the
    `f`-pullback square of `S.arr` stacked on the classifier square of `S`) is a
    pullback of `t` along `f ≫ χ_S`, whose left leg is `(f# S).arr = π₁`. -/
theorem classify_invImg {A B : 𝒞} (f : B ⟶ A) (S : Subobject 𝒞 A)
    (hp : HasPullback f S.arr) :
    HasSubobjectClassifier.classify (invImg f S hp).arr (invImg f S hp).monic
      = f ≫ HasSubobjectClassifier.classify S.arr S.monic := by
  let χ := HasSubobjectClassifier.classify S.arr S.monic
  show HasSubobjectClassifier.classify (invImg f S hp).arr (invImg f S hp).monic = f ≫ χ
  have sqS : S.arr ≫ χ = term S.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S.arr S.monic
  -- the pasted commuting square over (f ≫ χ, true).
  have hsq : (invImg f S hp).arr ≫ (f ≫ χ)
      = term (invImg f S hp).dom ≫ HasSubobjectClassifier.true := by
    show hp.cone.π₁ ≫ (f ≫ χ) = term hp.cone.pt ≫ HasSubobjectClassifier.true
    calc hp.cone.π₁ ≫ (f ≫ χ)
        = (hp.cone.π₁ ≫ f) ≫ χ := (Cat.assoc _ _ _).symm
      _ = (hp.cone.π₂ ≫ S.arr) ≫ χ := by rw [hp.cone.w]
      _ = hp.cone.π₂ ≫ (S.arr ≫ χ) := Cat.assoc _ _ _
      _ = hp.cone.π₂ ≫ (term S.dom ≫ HasSubobjectClassifier.true) := by rw [sqS]
      _ = (hp.cone.π₂ ≫ term S.dom) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term hp.cone.pt ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (hp.cone.π₂ ≫ term S.dom) (term hp.cone.pt)]
  symm
  refine HasSubobjectClassifier.classify_unique (invImg f S hp).arr (invImg f S hp).monic _ hsq ?_
  intro d
  -- d : cone over (f ≫ χ, true).  (d.π₁ ≫ f, d.π₂) is a cone over (χ, true).
  have hcS : (d.π₁ ≫ f) ≫ χ = d.π₂ ≫ HasSubobjectClassifier.true := by
    rw [Cat.assoc]; exact d.w
  obtain ⟨e, ⟨he₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S.arr S.monic
      ⟨d.pt, d.π₁ ≫ f, d.π₂, hcS⟩
  -- he₁ : e ≫ S.arr = d.π₁ ≫ f.  So (d.π₁, e) is a cone over (f, S.arr); lift into hp.
  have hw : d.π₁ ≫ f = e ≫ S.arr := he₁.symm
  refine ⟨hp.lift ⟨d.pt, d.π₁, e, hw⟩, ⟨hp.lift_fst _, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  -- v ≫ π₂ = e by cancelling the monic S.arr: both compose with S.arr to d.π₁ ≫ f.
  have hv₁' : v ≫ hp.cone.π₁ = d.π₁ := hv₁
  refine hp.lift_uniq ⟨d.pt, d.π₁, e, hw⟩ v hv₁ (S.monic _ _ ?_)
  show (v ≫ hp.cone.π₂) ≫ S.arr = e ≫ S.arr
  calc (v ≫ hp.cone.π₂) ≫ S.arr
      = v ≫ (hp.cone.π₂ ≫ S.arr) := Cat.assoc _ _ _
    _ = v ≫ (hp.cone.π₁ ≫ f) := congrArg (v ≫ ·) hp.cone.w.symm
    _ = (v ≫ hp.cone.π₁) ≫ f := (Cat.assoc _ _ _).symm
    _ = d.π₁ ≫ f := congrArg (· ≫ f) hv₁'
    _ = e ≫ S.arr := hw

/-- **§1.914 (internal-meet universal property)**: the classifying map
    `⟨χ_{S₁}, χ_{S₂}⟩ ≫ omegaMeet : A → Ω` of the pair of characteristic maps
    classifies the intersection `S₁ ∩ S₂` (`Sub.inter`, §1.452).

    This is the bridge that turns the bare classifying-map definition of
    `omegaMeet` into the subobject operation `g(A₁,A₂) = A₁ ∩ A₂` (§1.914).

    Proof by pullback pasting against `classify_unique`.  The commuting square
    `inter.arr ≫ (⟨χ₁,χ₂⟩ ≫ omegaMeet) = term ≫ t` holds because along `inter.arr`
    both `χ₁` and `χ₂` collapse to `term ≫ t` (classifier squares), so
    `inter.arr ≫ ⟨χ₁,χ₂⟩ = term ≫ ⟨t,t⟩`, and `⟨t,t⟩ ≫ omegaMeet = t` by the
    classifier square of `omegaMeet`.  For the pullback property: any cone whose
    apex `E` maps by `d.π₁` with `d.π₁ ≫ ⟨χ₁,χ₂⟩ ≫ omegaMeet = term ≫ t` makes
    `⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ : E → Ω×Ω` factor through `⟨t,t⟩` (the `omegaMeet`
    classifier pullback), i.e. `d.π₁ ≫ χ₁ = term ≫ t = d.π₁ ≫ χ₂`; each of these,
    via the classifier pullbacks of `χ₁`/`χ₂`, factors `d.π₁` through `m₁`/`m₂`;
    the pullback `hp` of `m₁,m₂` then yields the unique factorization through
    `inter.dom`. -/
theorem omegaMeet_classifies_inter {A : 𝒞} (S₁ S₂ : Subobject 𝒞 A)
    (hp : HasPullback S₁.arr S₂.arr) :
    pair (HasSubobjectClassifier.classify S₁.arr S₁.monic)
         (HasSubobjectClassifier.classify S₂.arr S₂.monic) ≫ omegaMeet
      = HasSubobjectClassifier.classify (Sub.inter S₁ S₂ hp).arr
          (Sub.inter S₁ S₂ hp).monic := by
  let χ₁ := HasSubobjectClassifier.classify S₁.arr S₁.monic
  let χ₂ := HasSubobjectClassifier.classify S₂.arr S₂.monic
  let I := Sub.inter S₁ S₂ hp
  show pair χ₁ χ₂ ≫ omegaMeet = HasSubobjectClassifier.classify I.arr I.monic
  -- The two classifier squares for m₁, m₂.
  have sq₁ : S₁.arr ≫ χ₁ = term S₁.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S₁.arr S₁.monic
  have sq₂ : S₂.arr ≫ χ₂ = term S₂.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S₂.arr S₂.monic
  -- omegaMeet classifier square: (t,t) ≫ omegaMeet = term 1 ≫ t = t.
  have sqM : pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet
      = term (HasTerminal.one (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq
      (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
      (fun f g _ => HasTerminal.uniq f g)
  -- I.arr = hp.cone.π₁ ≫ S₁.arr; also I.arr = hp.cone.π₂ ≫ S₂.arr (cone.w).
  have hIarr₁ : I.arr = hp.cone.π₁ ≫ S₁.arr := rfl
  have hIarr₂ : I.arr = hp.cone.π₂ ≫ S₂.arr := by
    rw [hIarr₁]; exact hp.cone.w
  -- Commuting square: I.arr ≫ (⟨χ₁,χ₂⟩ ≫ omegaMeet) = term I.dom ≫ t.
  have hsq : I.arr ≫ (pair χ₁ χ₂ ≫ omegaMeet)
      = term I.dom ≫ HasSubobjectClassifier.true := by
    -- I.arr ≫ ⟨χ₁,χ₂⟩ = ⟨I.arr≫χ₁, I.arr≫χ₂⟩ = ⟨term≫t, term≫t⟩ = term ≫ ⟨t,t⟩.
    have e1 : I.arr ≫ χ₁ = term I.dom ≫ HasSubobjectClassifier.true := by
      rw [hIarr₁, Cat.assoc, sq₁, ← Cat.assoc, term_uniq (hp.cone.π₁ ≫ term S₁.dom) (term I.dom)]
    have e2 : I.arr ≫ χ₂ = term I.dom ≫ HasSubobjectClassifier.true := by
      rw [hIarr₂, Cat.assoc, sq₂, ← Cat.assoc, term_uniq (hp.cone.π₂ ≫ term S₂.dom) (term I.dom)]
    have hpair : I.arr ≫ pair χ₁ χ₂
        = term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true := by
      have hL : I.arr ≫ pair χ₁ χ₂
          = pair (term I.dom ≫ HasSubobjectClassifier.true)
                 (term I.dom ≫ HasSubobjectClassifier.true) := by
        refine pair_uniq _ _ (I.arr ≫ pair χ₁ χ₂) ?_ ?_
        · rw [Cat.assoc, fst_pair]; exact e1
        · rw [Cat.assoc, snd_pair]; exact e2
      have hR : term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true
          = pair (term I.dom ≫ HasSubobjectClassifier.true)
                 (term I.dom ≫ HasSubobjectClassifier.true) := by
        refine pair_uniq _ _ _ ?_ ?_
        · rw [Cat.assoc, fst_pair]
        · rw [Cat.assoc, snd_pair]
      rw [hL, hR]
    calc I.arr ≫ (pair χ₁ χ₂ ≫ omegaMeet)
        = (I.arr ≫ pair χ₁ χ₂) ≫ omegaMeet := (Cat.assoc _ _ _).symm
      _ = (term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true) ≫ omegaMeet :=
            by rw [hpair]
      _ = term I.dom ≫ (pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet) :=
            Cat.assoc _ _ _
      _ = term I.dom ≫ (term HasTerminal.one ≫ HasSubobjectClassifier.true) := by rw [sqM]
      _ = (term I.dom ≫ term HasTerminal.one) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term I.dom ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (term I.dom ≫ term HasTerminal.one) (term I.dom)]
  -- Now show the square is a pullback, then conclude by classify_unique.
  refine HasSubobjectClassifier.classify_unique I.arr I.monic _ hsq ?_
  intro d
  -- d : Cone (⟨χ₁,χ₂⟩ ≫ omegaMeet) t, apex E = d.pt.
  -- Step A: ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ ≫ omegaMeet = term ≫ t  (from d.w).
  have hk : pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂) ≫ omegaMeet
      = term d.pt ≫ HasSubobjectClassifier.true := by
    have : pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂) = d.π₁ ≫ pair χ₁ χ₂ := by
      refine (pair_uniq _ _ _ ?_ ?_).symm <;> rw [Cat.assoc]
      · rw [fst_pair]
      · rw [snd_pair]
    rw [this, Cat.assoc, d.w, term_uniq d.π₂ (term d.pt)]
  -- Step B: factor ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ through (t,t) via omegaMeet's pullback.
  obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback
      (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
      (fun f g _ => HasTerminal.uniq f g)
      ⟨d.pt, pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂), term d.pt, hk⟩
  -- hw₁ : w ≫ (t,t) = ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩.  Read off the two components.
  have hcomp₁ : d.π₁ ≫ χ₁ = term d.pt ≫ HasSubobjectClassifier.true := by
    have := congrArg (· ≫ fst) hw₁
    simp only [Cat.assoc, fst_pair] at this
    rw [← this, term_uniq w (term d.pt)]
  have hcomp₂ : d.π₁ ≫ χ₂ = term d.pt ≫ HasSubobjectClassifier.true := by
    have := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc, snd_pair] at this
    rw [← this, term_uniq w (term d.pt)]
  -- Step C: each component factors d.π₁ through m₁ / m₂ (classifier pullbacks).
  obtain ⟨u₁, ⟨hu₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S₁.arr S₁.monic
      ⟨d.pt, d.π₁, term d.pt, by rw [hcomp₁]⟩
  obtain ⟨u₂, ⟨hu₂, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S₂.arr S₂.monic
      ⟨d.pt, d.π₁, term d.pt, by rw [hcomp₂]⟩
  -- hu₁ : u₁ ≫ S₁.arr = d.π₁;  hu₂ : u₂ ≫ S₂.arr = d.π₁.
  -- Step D: lift into the pullback hp to land in I.dom.
  have hpw : u₁ ≫ S₁.arr = u₂ ≫ S₂.arr := by rw [hu₁, hu₂]
  refine ⟨hp.lift ⟨d.pt, u₁, u₂, hpw⟩, ⟨?_, term_uniq _ _⟩, ?_⟩
  · -- (lift) ≫ I.arr = (lift) ≫ π₁ ≫ S₁.arr = u₁ ≫ S₁.arr = d.π₁.
    show hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ I.arr = d.π₁
    calc hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ I.arr
        = hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ (hp.cone.π₁ ≫ S₁.arr) := by rw [hIarr₁]
      _ = (hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ hp.cone.π₁) ≫ S₁.arr := (Cat.assoc _ _ _).symm
      _ = u₁ ≫ S₁.arr := by rw [hp.lift_fst]
      _ = d.π₁ := hu₁
  · -- uniqueness of the lift among maps into I.dom.
    intro v hv₁ _
    refine hp.lift_uniq ⟨d.pt, u₁, u₂, hpw⟩ v ?_ ?_
    · -- v ≫ π₁ = u₁: cancel the monic S₁.arr; (v ≫ π₁) ≫ S₁.arr = v ≫ I.arr = d.π₁ = u₁ ≫ S₁.arr.
      refine S₁.monic _ _ ?_
      rw [Cat.assoc, ← hIarr₁, hv₁, hu₁]
    · -- v ≫ π₂ = u₂: cancel the monic S₂.arr; (v ≫ π₂) ≫ S₂.arr = v ≫ I.arr = d.π₁ = u₂ ≫ S₂.arr.
      refine S₂.monic _ _ ?_
      rw [Cat.assoc, ← hIarr₂, hv₁, hu₂]

/-- **§1.914 (heyting double-arrow universal property)**: if `e : E → A` is a
    monic that EQUALIZES `χ₁, χ₂ : A → Ω` (`e ≫ χ₁ = e ≫ χ₂`) and is universal
    among such (every `k` with `k ≫ χ₁ = k ≫ χ₂` factors uniquely through `e`),
    then the classifying map `⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow : A → Ω` of the pair
    classifies that subobject `e`.  This is the bridge turning the bare diagonal
    definition of `heytingDoubleArrow` into the subobject operation
    "the largest subobject on which `χ₁ = χ₂`" (equivalently `A₁ ∩ A' = A₂ ∩ A'`).

    Proof by pullback pasting against `classify_unique`, exactly parallel to
    `omegaMeet_classifies_inter`.  The commuting square holds because along `e`,
    `χ₁ = χ₂` so `e ≫ ⟨χ₁,χ₂⟩ = (e ≫ χ₁) ≫ diag`, and `diag ≫ heytingDoubleArrow
    = term ≫ true` is the diagonal's classifier square.  For the pullback: a cone
    `d` whose apex maps by `d.π₁` with the composite collapsing to `term ≫ true`
    makes `d.π₁ ≫ ⟨χ₁,χ₂⟩` factor through `diag` (diag's classifier pullback), so
    `d.π₁ ≫ χ₁ = d.π₁ ≫ χ₂`; the equalizer universal property of `e` then yields
    the unique factorization through `E`. -/
theorem heytingDoubleArrow_classifies_eq {A E : 𝒞} (χ₁ χ₂ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (e : E ⟶ A) (he : Mono e) (heq : e ≫ χ₁ = e ≫ χ₂)
    (huniv : ∀ {W : 𝒞} (k : W ⟶ A), k ≫ χ₁ = k ≫ χ₂ →
      ∃ u : W ⟶ E, u ≫ e = k ∧ ∀ u' : W ⟶ E, u' ≫ e = k → u' = u) :
    pair χ₁ χ₂ ≫ heytingDoubleArrow = HasSubobjectClassifier.classify e he := by
  -- diagonal classifier square: diag ≫ heytingDoubleArrow = term Ω ≫ true.
  have sqD : diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow
      = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq _ (diag_mono _)
  -- e ≫ ⟨χ₁,χ₂⟩ = (e ≫ χ₁) ≫ diag  (since e ≫ χ₁ = e ≫ χ₂).
  have hpairE : e ≫ pair χ₁ χ₂ = (e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
    have hL : e ≫ pair χ₁ χ₂ = pair (e ≫ χ₁) (e ≫ χ₂) :=
      pair_uniq (e ≫ χ₁) (e ≫ χ₂) (e ≫ pair χ₁ χ₂)
        (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have hR : (e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))
        = pair (e ≫ χ₁) (e ≫ χ₂) :=
      pair_uniq (e ≫ χ₁) (e ≫ χ₂) _
        (by rw [Cat.assoc, diag_fst, Cat.comp_id])
        (by rw [Cat.assoc, diag_snd, Cat.comp_id, heq])
    rw [hL, hR]
  -- Commuting square: e ≫ (⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow) = term E ≫ true.
  have hsq : e ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow)
      = term E ≫ HasSubobjectClassifier.true := by
    calc e ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow)
        = (e ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow := (Cat.assoc _ _ _).symm
      _ = ((e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ heytingDoubleArrow := by
            rw [hpairE]
      _ = (e ≫ χ₁) ≫ (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow) :=
            Cat.assoc _ _ _
      _ = (e ≫ χ₁) ≫ (term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true) := by
            rw [sqD]
      _ = ((e ≫ χ₁) ≫ term (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ HasSubobjectClassifier.true :=
            (Cat.assoc _ _ _).symm
      _ = term E ≫ HasSubobjectClassifier.true := by
            rw [term_uniq ((e ≫ χ₁) ≫ term _) (term E)]
  refine HasSubobjectClassifier.classify_unique e he _ hsq ?_
  intro d
  -- d.π₁ ≫ (⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow) = term ≫ true  (from d.w).
  have hk : (d.π₁ ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow
      = term d.pt ≫ HasSubobjectClassifier.true := by
    rw [Cat.assoc, d.w, term_uniq d.π₂ (term d.pt)]
  -- factor d.π₁ ≫ ⟨χ₁,χ₂⟩ through diag via diag's classifier pullback.
  obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback
      (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) (diag_mono _)
      ⟨d.pt, d.π₁ ≫ pair χ₁ χ₂, term d.pt, hk⟩
  -- hw₁ : w ≫ diag = d.π₁ ≫ ⟨χ₁,χ₂⟩.  Read off the two components → χ₁ = χ₂ along d.π₁.
  have hcomp : d.π₁ ≫ χ₁ = d.π₁ ≫ χ₂ := by
    have e1 := congrArg (· ≫ fst) hw₁
    have e2 := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc, diag_fst, diag_snd, fst_pair, snd_pair, Cat.comp_id] at e1 e2
    rw [← e1, ← e2]
  -- equalizer universal property of e factors d.π₁ through E.
  obtain ⟨u, hu, huu⟩ := huniv d.π₁ hcomp
  refine ⟨u, ⟨hu, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  exact huu v hv₁

/-- **§1.919 (reduction)**: an endomorphism `h : Ω → Ω` equals the identity as
    soon as `t : 1 → Ω` is a pullback of `t` along `h` — i.e. `Ω` is "`h`-large in
    itself" (`h` classifies the maximal subobject `t : 1 → Ω`).

    Proof: the hypotheses are exactly the data making `h` the characteristic map of
    `t`, so `classify_unique` gives `h = classify t = id` (`classify_true_eq_id`). -/
theorem omega_endo_eq_id_of_classifies_true
    (h : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (hsq : HasSubobjectClassifier.true (𝒞 := 𝒞) ≫ h
      = term (HasTerminal.one (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true)
    (hpb : (Cone.mk (f := h) (g := HasSubobjectClassifier.true)
        (pt := HasTerminal.one) (π₁ := HasSubobjectClassifier.true)
        (π₂ := term HasTerminal.one) (w := hsq)).IsPullback) :
    h = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  rw [← classify_true_eq_id]
  exact HasSubobjectClassifier.classify_unique
    (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic h hsq hpb

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

    **Proof gap** (sharpened).  Via the available API the goal reduces to showing
    `t : 1 → Ω` is the pullback of `t` along `g ≫ g` (i.e. `g²` classifies the
    maximal subobject of Ω — "A is g²-large in itself").  Freyd's argument needs
    FOUR pieces; THREE are now available in this file:
    (1) the full `Sub(−) ≅ Hom(−,Ω)` bijection: `classify_unique` (injective half)
        + `classify_surjective` (surjective half, above);
    (2a) the internal-MEET universal property: `omegaMeet_classifies_inter` (above)
        proves `⟨χ_{A₁},χ_{A₂}⟩ ≫ omegaMeet` classifies `Sub.inter A₁ A₂` (S1_45),
        so `omegaMeet` realises the subobject operation `g(A₁,A₂) = A₁ ∩ A₂`;
    (3) operation-extensionality then follows from (1).
    The REMAINING blocker is (2b): the universal property of `heytingDoubleArrow`
    (defined below as a bare classifying map of the diagonal) — concretely that
    `⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow` classifies the subobject on which `χ₁ = χ₂`,
    equivalently `A₁ ∩ A' = A₂ ∩ A'` — TOGETHER WITH the internal-Heyting identity
    `(A ↔ A×U) ∧ (A×U) = A`.  The latter needs Sub(A) to be developed as a Heyting
    semilattice (the g-large-subobject correspondence `A'∈g-large ↔ char factors
    through gᵐ(t)`, and the operation `A' ↦ (A ↔ A×U) ∧ A×U`), none of which is
    formalised here — this is a multi-lemma development of internal Heyting algebra
    on subobjects, not a single bridge lemma.  Faithful sorry; the meet-bridge
    `omegaMeet_classifies_inter` is now in place, residual = Heyting-arrow UMP +
    Sub(A)-Heyting-algebra infra.  See S1_91.md. -/
theorem omega_monic_endo_is_involution (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Mono g) : g ≫ g = Cat.id _ := by
  sorry

/-! ## §1.91(10)  Minimal topos definition

  A category with binary products and equalizers (equivalently: binary products
  and pullbacks, or all finite non-empty limits) and power-objects for every
  object, which is non-empty, already has a terminator and hence is a topos
  (§1.91(10)).  Crucially the hypotheses here do NOT presuppose a terminator —
  power-objects are taken via `HasPowerObject`, which (unlike
  `HasSubobjectClassifier`, that `extends HasTerminal`) needs only pullbacks.

  CONSTRUCTION (Freyd): For objects A,B let M_{A,B} denote the "full" relation
  tabulated by the product projection A×B → A (its table is A×B with the two
  projections).  For any f : A' → A the equation f(M_{A,B}) = M_{A',B} holds, so
  AM_{A,B} := Λ(M_{A,B}) is a CONSTANT map: f(AM_{A,B}) = g(AM_{A,B}) for all
  f,g : A' → A.  Hence Λ(M_{B,B}) : [B] → [B] is a constant idempotent
  endomorphism.  For any A there is a map A → [B] (namely AM_{A,B}), so the
  equalizer T of id_{[B]} and Λ(M_{B,B}) is a terminator. -/

section MinimalTopos
variable [HasPullbacks 𝒞] [HasBinaryProducts 𝒞]

/-- §1.91(10): The "full" relation `M_{A,C} : A → C`, tabulated by the product
    projection — its table is `A×C` with the two product projections as columns.
    Jointly monic because `pair fst snd = id`. -/
noncomputable def fullRel (A C : 𝒞) : BinRel 𝒞 A C where
  src  := prod A C
  colA := fst
  colB := snd
  isMonicPair := fst_snd_jointly_monic

/-- §1.91(10): `f(M_{A,C}) = M_{A',C}` — pulling the full relation back along
    `f : A' → A` gives the full relation again.  The pullback of `fst : A×C → A`
    along `f` is `A'×C` (via `pair`), realizing the iso of tables in both
    directions. -/
theorem fullRel_pullback {A A' C : 𝒞} (f : A' ⟶ A) :
    RelHom (relPullback f (fullRel A C)) (fullRel A' C) ∧
    RelHom (fullRel A' C) (relPullback f (fullRel A C)) := by
  let pb := HasPullbacks.has f (fullRel A C).colA
  -- relPullback f (fullRel A C) has table pb.pt, colA = π₁, colB = π₂ ≫ snd.
  -- Abbreviate the two projections at the two arities to pin down their types.
  let sA  : prod A C  ⟶ C := snd
  let sA' : prod A' C ⟶ C := snd
  -- backward cone over (f, fst) with apex A'×C: (fst, pair (fst≫f) snd).
  have hbw : (fst : prod A' C ⟶ A') ≫ f = pair (fst ≫ f) sA' ≫ (fullRel A C).colA := by
    show (fst : prod A' C ⟶ A') ≫ f = pair (fst ≫ f) sA' ≫ fst
    rw [fst_pair]
  let cbw : Cone f (fullRel A C).colA := ⟨prod A' C, fst, pair (fst ≫ f) sA', hbw⟩
  refine ⟨⟨pair pb.cone.π₁ (pb.cone.π₂ ≫ sA), fst_pair _ _, ?_⟩,
          ⟨pb.lift cbw, pb.lift_fst cbw, ?_⟩⟩
  · -- forward colB: pair π₁ (π₂≫snd) ≫ snd = π₂ ≫ snd.
    show pair pb.cone.π₁ (pb.cone.π₂ ≫ sA) ≫ sA' = pb.cone.π₂ ≫ sA
    exact snd_pair _ _
  · -- backward colB: (pb.lift cbw) ≫ (π₂ ≫ snd) = snd.
    show pb.lift cbw ≫ (pb.cone.π₂ ≫ sA) = sA'
    calc pb.lift cbw ≫ (pb.cone.π₂ ≫ sA)
        = (pb.lift cbw ≫ pb.cone.π₂) ≫ sA := (Cat.assoc _ _ _).symm
      _ = pair (fst ≫ f) sA' ≫ sA := congrArg (· ≫ sA) (pb.lift_snd cbw)
      _ = sA' := snd_pair _ _

variable [∀ C : 𝒞, HasPowerObject C]

/-- The classifying map `Λ(M_{A,B}) = AM_{A,B} : A → [B]` of the full relation. -/
noncomputable def fullClassify (A B : 𝒞) : A ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (fullRel A B)

/-- `R ≅ relPullback (Λ R) ∈_C`: the defining property of `powerClassify`. -/
theorem powerClassify_spec {C A : 𝒞} (R : BinRel 𝒞 A C) :
    RelHom R (relPullback (powerClassify R) HasPowerObject.mem) ∧
    RelHom (relPullback (powerClassify R) HasPowerObject.mem) R :=
  (HasPowerObject.is_universal.classify_exists A R).choose_spec

/-- Transitivity of `RelHom` (local copy; the S1_92 version depends on S1_91). -/
theorem relHom_trans {A C : 𝒞} {R S T : BinRel 𝒞 A C}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨h, hA, hB⟩ := h₁; obtain ⟨k, kA, kB⟩ := h₂
  exact ⟨h ≫ k, by rw [Cat.assoc, kA, hA], by rw [Cat.assoc, kB, hB]⟩

/-- `RelHom` is preserved by pulling back along a fixed `g`, obtained by lifting
    one table into the pullback of the other. -/
theorem relHom_pullback {A C X : 𝒞} (g : X ⟶ A) {R S : BinRel 𝒞 A C}
    (h : RelHom R S) : RelHom (relPullback g R) (relPullback g S) := by
  obtain ⟨w, hwA, hwB⟩ := h
  let P  := HasPullbacks.has g R.colA
  let P' := HasPullbacks.has g S.colA
  -- cone over (g, S.colA) with apex P.pt: (π₁, π₂ ≫ w).
  have hsq : P.cone.π₁ ≫ g = (P.cone.π₂ ≫ w) ≫ S.colA :=
    calc P.cone.π₁ ≫ g = P.cone.π₂ ≫ R.colA := P.cone.w
      _ = P.cone.π₂ ≫ (w ≫ S.colA) := congrArg (P.cone.π₂ ≫ ·) hwA.symm
      _ = (P.cone.π₂ ≫ w) ≫ S.colA := (Cat.assoc P.cone.π₂ w S.colA).symm
  let c : Cone g S.colA := ⟨P.cone.pt, P.cone.π₁, P.cone.π₂ ≫ w, hsq⟩
  refine ⟨P'.lift c, P'.lift_fst c, ?_⟩
  -- colB: (P'.lift c) ≫ (π₂' ≫ S.colB) = π₂ ≫ R.colB.
  show P'.lift c ≫ (P'.cone.π₂ ≫ S.colB) = P.cone.π₂ ≫ R.colB
  calc P'.lift c ≫ (P'.cone.π₂ ≫ S.colB)
      = (P'.lift c ≫ P'.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
    _ = (P.cone.π₂ ≫ w) ≫ S.colB := congrArg (· ≫ S.colB) (P'.lift_snd c)
    _ = P.cone.π₂ ≫ (w ≫ S.colB) := Cat.assoc _ _ _
    _ = P.cone.π₂ ≫ R.colB := congrArg (P.cone.π₂ ≫ ·) hwB

/-- **§1.91(10), naturality of `Λ`**: `Λ(relPullback g R) = g ≫ Λ(R)`.
    Both classify `relPullback g R` (via `relPullback_comp`), so universality's
    `classify_unique` forces them equal.  (Local; S1_92's `univClassify_natural`
    depends on S1_91.) -/
theorem powerClassify_natural {C A X : 𝒞} (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    powerClassify (relPullback g R) = g ≫ powerClassify R := by
  have hR := powerClassify_spec R
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (powerClassify R) HasPowerObject.mem
  have hf : RelHom (relPullback g R)
              (relPullback (g ≫ powerClassify R) HasPowerObject.mem) ∧
            RelHom (relPullback (g ≫ powerClassify R) HasPowerObject.mem)
              (relPullback g R) :=
    ⟨relHom_trans (relHom_pullback g hR.1) hc1,
     relHom_trans hc2 (relHom_pullback g hR.2)⟩
  exact HasPowerObject.is_universal.classify_unique X (relPullback g R) _ _
    (powerClassify_spec (relPullback g R)) hf

/-- **§1.91(10), constancy**: `g ≫ Λ(M_{A,B})` does not depend on `g : X → A` —
    it equals `Λ(M_{X,B})`.  By naturality `g ≫ Λ(M_{A,B}) = Λ(g(M_{A,B}))` and
    `g(M_{A,B}) ≅ M_{X,B}` (`fullRel_pullback`). -/
theorem fullClassify_const {A B X : 𝒞} (g : X ⟶ A) :
    g ≫ fullClassify A B = fullClassify X B := by
  rw [fullClassify, ← powerClassify_natural (fullRel A B) g]
  exact HasPowerObject.is_universal.classify_unique X _ _ _
    (powerClassify_spec _)
    ⟨relHom_trans (fullRel_pullback g).1 (powerClassify_spec (fullRel X B)).1,
     relHom_trans (powerClassify_spec (fullRel X B)).2 (fullRel_pullback g).2⟩

variable [HasEqualizers 𝒞]

/-- **§1.91(10)**: A non-empty category with binary products, equalizers, pullbacks,
    and power objects FOR EVERY OBJECT (but NOT assumed to have a terminator) already
    has a terminator.  `B` witnesses non-emptiness.

    This is the faithful statement of Freyd's §1.91(10): the hypotheses are exactly
    the data of his construction and DO NOT bundle a terminator (unlike
    `HasSubobjectClassifier`, which `extends HasTerminal` and would make the
    conclusion free).

    CONSTRUCTION.  `e := Λ(M_{[B],B}) : [B] → [B]` is a constant map
    (`fullClassify_const`).  Take `T := equalizer (id_{[B]}, e)`.
    - Existence of `A → T`: `Λ(M_{A,B})` equalizes `id` and `e`
      (`Λ(M_{A,B}) ≫ e = Λ(M_{A,B})` by constancy), so it factors through `T`.
    - Uniqueness: any `u, v : A → T` have `u ≫ eqMap`, `v ≫ eqMap : A → [B]`;
      constancy gives `(u ≫ eqMap) ≫ e = (v ≫ eqMap) ≫ e`, and `eqMap ≫ e = eqMap`
      (the equalizer relation), so `u ≫ eqMap = v ≫ eqMap`; `eqMap` is monic
      (equalizer map), hence `u = v`. -/
theorem minimal_topos_has_terminator (B : 𝒞) : Nonempty (HasTerminal 𝒞) := by
  let Pb := HasPowerObject.powerObj (C := B)
  let e : Pb ⟶ Pb := fullClassify Pb B
  -- e is constant: any two maps into Pb agree after `≫ e`.
  have hconst : ∀ {X : 𝒞} (p q : X ⟶ Pb), p ≫ e = q ≫ e := fun p q => by
    rw [fullClassify_const p, fullClassify_const q]
  -- the equalizer relation `eqMap ≫ id = eqMap ≫ e`, i.e. `eqMap ≫ e = eqMap`.
  have hEqMap : eqMap (Cat.id Pb) e ≫ e = eqMap (Cat.id Pb) e := by
    have := eqMap_eq (Cat.id Pb) e; rw [Cat.comp_id] at this; exact this.symm
  refine ⟨{ one := eqObj (Cat.id Pb) e, trm := fun A => ?_, uniq := fun {A} u v => ?_ }⟩
  · -- A → T: Λ(M_{A,B}) equalizes id and e (constancy: Λ(M_{A,B}) ≫ e = Λ(M_{A,B})).
    refine eqLift (Cat.id Pb) e (fullClassify A B) ?_
    rw [Cat.comp_id]
    exact (fullClassify_const (fullClassify A B)).symm
  · -- uniqueness: cancel the monic `eqMap` after showing `u ≫ eqMap = v ≫ eqMap`.
    have hmono : Mono (eqMap (Cat.id Pb) e) := by
      intro W f g hfg
      exact (eqLift_uniq (Cat.id Pb) e (f ≫ eqMap (Cat.id Pb) e)
              (by rw [Cat.assoc, eqMap_eq, Cat.assoc]) f rfl).trans
            (eqLift_uniq (Cat.id Pb) e (f ≫ eqMap (Cat.id Pb) e)
              (by rw [Cat.assoc, eqMap_eq, Cat.assoc]) g hfg.symm).symm
    apply hmono
    -- u ≫ eqMap = v ≫ eqMap: postcompose hconst with `≫ e` collapses via hEqMap.
    calc u ≫ eqMap (Cat.id Pb) e
        = (u ≫ eqMap (Cat.id Pb) e) ≫ e := by rw [Cat.assoc, hEqMap]
      _ = (v ≫ eqMap (Cat.id Pb) e) ≫ e := hconst _ _
      _ = v ≫ eqMap (Cat.id Pb) e := by rw [Cat.assoc, hEqMap]

end MinimalTopos

end Freyd
