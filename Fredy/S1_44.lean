/-
  Freyd & Scedrov, *Categories and Allegories* §1.44  The slice category A/B.

  §1.44  Σ : A/B → A forgetful functor.  A/B has a distinguished terminator
         ⟨B, id_B⟩, carried by Σ to B.  Σ does not preserve terminators unless
         B is a terminator in A (in which case Σ is an isomorphism).

  §1.441 If A has pullbacks then A/B is Cartesian and Σ preserves pullbacks
         and equalizers.  Σ is faithful.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_26
import Fredy.S1_42
import Fredy.S1_45


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.44  The forgetful functor Σ : A/B → A -/

/-- The forgetful functor Σ : A/B → A (§1.44).  Sends ⟨X, h:X→B⟩ to X,
    and a slice morphism to its underlying arrow (`.f`). -/
def SliceForget (B : 𝒞) : Over B → 𝒞 := λ X => X.dom

/-! ### Distinguished terminator in A/B -/

/-- **§1.44**: The identity `id_B : B → B` is the distinguished terminator in A/B.
    For any Over object X = ⟨X, h:X→B⟩, the unique map to ⟨B, id_B⟩ is h itself. -/
def overTerm (B : 𝒞) : Over B := ⟨B, Cat.id B⟩

instance overHasTerminal (B : 𝒞) : HasTerminal (Over B) where
  one := overTerm B
  trm X := ⟨X.hom, by simpa [overTerm] using (Cat.comp_id X.hom)⟩
  uniq {X} f g := OverHom.ext (by
    have hf : f.f = X.hom := by simpa [overTerm, Cat.comp_id] using f.w
    have hg : g.f = X.hom := by simpa [overTerm, Cat.comp_id] using g.w
    rw [hf, hg])

/-- Σ carries the slice terminator to B.  Σ does NOT preserve terminators unless
    B itself is a terminator in A.  (If B ≅ 1_A then Σ is an isomorphism.) -/
theorem sliceForget_term (B : 𝒞) : SliceForget B (overTerm B) = B := rfl

/-! ## §1.441  Pullbacks in A/B; Σ preserves pullbacks -/

variable [hpull : HasPullbacks 𝒞]

section overPullback

variable {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z)

/-- The underlying pullback in A of `m.f` and `n.f`. -/
private def _pb : HasPullback m.f n.f := hpull.has m.f n.f

private theorem _pb_hom_eq :
    (_pb m n).cone.π₂ ≫ Y.hom = (_pb m n).cone.π₁ ≫ X.hom := by
  calc
    (_pb m n).cone.π₂ ≫ Y.hom   = (_pb m n).cone.π₂ ≫ (n.f ≫ Z.hom) := by rw [← n.w]
    _ = ((_pb m n).cone.π₂ ≫ n.f) ≫ Z.hom := by rw [Cat.assoc]
    _ = ((_pb m n).cone.π₁ ≫ m.f) ≫ Z.hom := by rw [(_pb m n).cone.w]
    _ = (_pb m n).cone.π₁ ≫ (m.f ≫ Z.hom) := by rw [← Cat.assoc]
    _ = (_pb m n).cone.π₁ ≫ X.hom         := by rw [m.w]

/-- **§1.441**: The pullback object in A/B.  The point is the pullback point in A,
    with structure map `π₁ ≫ X.hom` (= `π₂ ≫ Y.hom`). -/
def overPullbackPt : Over B :=
  ⟨(_pb m n).cone.pt, (_pb m n).cone.π₁ ≫ X.hom⟩

/-- First projection of the overPullback. -/
def overPullbackπ₁ : OverHom (overPullbackPt m n) X :=
  ⟨(_pb m n).cone.π₁, rfl⟩

/-- Second projection of the overPullback. -/
def overPullbackπ₂ : OverHom (overPullbackPt m n) Y :=
  ⟨(_pb m n).cone.π₂, _pb_hom_eq m n⟩

/-- The pullback square commutes in A/B. -/
theorem overPullback_sq : overPullbackπ₁ m n ⊚ m = overPullbackπ₂ m n ⊚ n :=
  OverHom.ext ((_pb m n).cone.w)

/-- The universal lift for the overPullback.  Given a cone in A/B, the lift
    in A also respects the Over structure. -/
def overPullbackLift {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n) :
    OverHom W (overPullbackPt m n) :=
  let h_base := congrArg OverHom.f h
  let c : Cone m.f n.f := ⟨W.dom, a.f, b.f, h_base⟩
  let u := (_pb m n).lift c
  ⟨u, by
    dsimp [overPullbackPt, u]
    calc u ≫ ((_pb m n).cone.π₁ ≫ X.hom) = (u ≫ (_pb m n).cone.π₁) ≫ X.hom := by rw [Cat.assoc]
      _ = a.f ≫ X.hom := by rw [(_pb m n).lift_fst c]
      _ = W.hom      := a.w⟩

theorem overPullbackLift_fst {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n) :
    overPullbackLift m n a b h ⊚ overPullbackπ₁ m n = a :=
  OverHom.ext ((_pb m n).lift_fst _)

theorem overPullbackLift_snd {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n) :
    overPullbackLift m n a b h ⊚ overPullbackπ₂ m n = b :=
  OverHom.ext ((_pb m n).lift_snd _)

theorem overPullbackLift_uniq {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n)
    (u : OverHom W (overPullbackPt m n))
    (hu₁ : u ⊚ overPullbackπ₁ m n = a) (hu₂ : u ⊚ overPullbackπ₂ m n = b) :
    u = overPullbackLift m n a b h :=
  OverHom.ext ((_pb m n).lift_uniq ⟨W.dom, a.f, b.f, congrArg OverHom.f h⟩ u.f
    (congrArg OverHom.f hu₁) (congrArg OverHom.f hu₂))

end overPullback

/-! ## Σ preserves pullbacks (§1.441) -/

/-- **§1.441**: Σ preserves pullbacks.  Applying Σ to the pullback in A/B
    recovers the pullback in A. -/
theorem sigma_preserves_pullback_pt {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    SliceForget B (overPullbackPt m n) = (_pb m n).cone.pt := rfl

/-- **§1.441**: Σ preserves pullbacks — first projection. -/
theorem sigma_preserves_pullback_π₁ {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    (overPullbackπ₁ m n).f = (_pb m n).cone.π₁ := rfl

/-- **§1.441**: Σ preserves pullbacks — second projection. -/
theorem sigma_preserves_pullback_π₂ {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    (overPullbackπ₂ m n).f = (_pb m n).cone.π₂ := rfl

/-! ## Σ is faithful (§1.442) -/

/-- **§1.442**: Σ is faithful.  Two slice morphisms are equal iff their underlying
    A-arrows are equal (this is exactly `OverHom.ext`). -/
theorem sigma_faithful {B : 𝒞} {X Y : Over B} (f g : OverHom X Y)
    (h : f.f = g.f) : f = g := OverHom.ext h

/-! ## §1.44  Universal property of Σ : A/B → A

  Freyd §1.44: Σ is universal among functors T : 𝒞 → A that carry the designated
  terminator of 𝒞 to B.  Given T with T(1) = B, there is a unique T' : 𝒞 → A/B
  with T'(1) = id_B (the slice terminator) and Σ ∘ T' = T.
  Construction: T'(C) = ⟨T C, hB ▸ T.map(term_C)⟩. -/

/-- **§1.44**: The LIFT of T : 𝒞 → A along Σ.  Given T(1) = B, defines
    T'(C) = ⟨T C, T(term_C) : T C → T(1) = B⟩. -/
def sliceLift {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B) :
    𝒞 → Over B :=
  fun C => ⟨T C, hB ▸ hT.map (term C)⟩

instance sliceLift_isFunctor {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B) :
    Functor (sliceLift T hB) where
  map {C D} f := ⟨hT.map f, by
    simp only [sliceLift]; cases hB
    rw [← hT.map_comp]; congr 1; exact term_uniq _ _⟩
  map_id C := OverHom.ext (hT.map_id C)
  map_comp f g := OverHom.ext (hT.map_comp f g)

/-- **§1.44 — existence (terminator)**: T' carries the terminator of 𝒞 to the slice
    terminator ⟨B, id_B⟩. -/
theorem sliceLift_term {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B) :
    sliceLift T hB (one (𝒞 := 𝒞)) = overTerm B := by
  simp only [sliceLift, overTerm]
  cases hB
  congr 1
  simp [term_uniq (term (one (𝒞 := 𝒞))) (Cat.id _), hT.map_id]

/-- **§1.44 — existence (Σ ∘ T' = T)**: Composing the lift with Σ recovers T. -/
theorem sliceLift_comp_sigma {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B) :
    SliceForget B ∘ sliceLift T hB = T := rfl

/-- **§1.44 — existence (underlying maps)**: The underlying map of T'(f) is T(f). -/
theorem sliceLift_map_eq {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B)
    {C D : 𝒞} (f : C ⟶ D) :
    ((sliceLift_isFunctor T hB).map f).f = hT.map f := rfl

/-- HEq congruence for composition across object identifications: if the three
    objects match (`X=X'`, `Y=Y'`, `Z=Z'`) and the arrows match up to HEq, then
    the composites match up to HEq.  Used to transport `OverHom.w` through the
    domain identification in `sliceLift_unique`. -/
private theorem comp_heq_congr {𝒜 : Type u} [Cat.{v} 𝒜] {X Y Z X' Y' Z' : 𝒜}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : f ≍ f') (hg : g ≍ g') : f ≫ g ≍ f' ≫ g' := by
  subst hX hY hZ; rw [eq_of_heq hf, eq_of_heq hg]

/-- A pair of `.symm ▸` object-transports on an arrow is HEq-trivial.  Strips the
    domain identifications produced by `h_map` in `sliceLift_unique`. -/
private theorem eqRec_symm_symm_heq {𝒜 : Type u} [Cat.{v} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    (hX.symm ▸ hY.symm ▸ f : X ⟶ Y) ≍ f := by
  subst hX; subst hY; rfl

/-- **§1.44 — uniqueness**: Any functor T'' : 𝒞 → A/B satisfying
    (1) T''(1_𝒞) = overTerm B  (terminator condition), and
    (2) for each morphism f, the underlying A-map of T''(f) equals hT.map(f)
        up to the domain identification (Σ ∘ T'' = T on maps),
    equals the lift T'.

    We express (2) via a cast-free condition: `(hT''.map f).f = (h_obj C) ▸ (h_obj D) ▸ hT.map f`
    where `h_obj` gives the domain equality.

    Proof: OverHom.w on hT''.map(term_C) gives
      (hT''.map(term_C)).f ≫ (T''(1)).hom = (T'' C).hom.
    With T''(1) = ⟨B, id_B⟩: (hT''.map(term_C)).f = (T'' C).hom.
    The domain identification + h_map show both equal hB ▸ hT.map(term_C).  □ -/
theorem sliceLift_unique {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : 𝒞 → 𝒜) [hT : Functor T] (hB : T (one (𝒞 := 𝒞)) = B)
    (T'' : 𝒞 → Over B) [hT'' : Functor T'']
    -- (1) T''(1_𝒞) = overTerm B
    (h_term : T'' (one (𝒞 := 𝒞)) = overTerm B)
    -- (2) Domain equality: Σ ∘ T'' = T on objects.
    (h_obj  : ∀ C, (T'' C).dom = T C)
    -- (3) Map equality after domain identification: Σ ∘ T'' = T on morphisms.
    --     (hT''.map f).f has type (T'' C).dom → (T'' D).dom;
    --     after the domain identification it equals hT.map f : T C → T D.
    (h_map  : ∀ {C D : 𝒞} (f : C ⟶ D),
        (hT''.map f).f = (h_obj C).symm ▸ (h_obj D).symm ▸ hT.map f) :
    ∀ C, T'' C = sliceLift T hB C := by
  -- Eliminate B by substituting T one = B. After subst, B disappears,
  -- overTerm (T one) = ⟨T one, Cat.id (T one)⟩, sliceLift T rfl C = ⟨T C, hT.map(term C)⟩.
  subst hB
  -- Decompose h_term via Over.mk.injEq to get HEq on the hom field, then unfold
  -- overTerm so the resulting equalities mention `T one` / `Cat.id (T one)`.
  rw [Over.mk.injEq] at h_term
  obtain ⟨h_one_dom, h_one_hom⟩ := h_term
  simp only [overTerm] at h_one_dom h_one_hom
  -- h_one_dom : (T'' one).dom = T one
  -- h_one_hom : (T'' one).hom ≍ Cat.id (T one)
  intro C
  -- Goal: T'' C = sliceLift T rfl C = ⟨T C, hT.map(term C)⟩.
  -- Prove via Over.mk.injEq: dom-equality (h_obj C) + HEq on homs.
  rw [Over.mk.injEq]
  refine ⟨h_obj C, ?_⟩
  -- Goal: (T'' C).hom ≍ hT.map (term C).
  -- OverHom.w on hT''.map(term C): (hT''.map (term C)).f ≫ (T'' one).hom = (T'' C).hom.
  have hw : (hT''.map (term C)).f ≫ (T'' (one (𝒞 := 𝒞))).hom = (T'' C).hom :=
    (hT''.map (term C)).w
  -- The underlying map of T''(term C) agrees with hT.map(term C) up to HEq: the two
  -- ▸ transports in h_map are HEq-trivial (eqRec_heq).
  have hf_heq : (hT''.map (term C)).f ≍ hT.map (term C) := by
    rw [h_map (term C)]; exact eqRec_symm_symm_heq (h_obj C) (h_obj _) _
  -- Rewrite the goal using hw, then absorb the identity on the rhs and apply the
  -- composition HEq-congruence (objects matched by h_obj C, h_one_dom, rfl).
  rw [← hw]
  refine HEq.trans ?_ (heq_of_eq (Cat.comp_id (hT.map (term C))))
  exact comp_heq_congr (h_obj C) h_one_dom rfl hf_heq h_one_hom

/-! ## §1.464  Yoneda representation preserves/reflects cartesian predicates

  Freyd §1.464: The covariant embedding H : A → 𝒮^(A°), B ↦ H_B = (-, B),
  is a full embedding (the YONEDA REPRESENTATION).  It preserves and reflects the
  cartesian predicates.

  The embedding `YonedaEmbedding B : 𝒞 → Type v := fun A => A ⟶ B` is defined
  in S1_47.lean.  A full Yoneda-into-functor-category statement requires:
  (a) `setCat : Cat (Type v)` — in Horn.lean (not imported here);
  (b) `FunctorCategory.lean` for the functor-category structure on `𝒮^(A°)`.

  We state the key content that is accessible from the current imports:
  the Yoneda embedding sends TERMINATORS, PRODUCTS, and PULLBACKS to the
  corresponding structures in the hom-set sense.

  The full functor-category statement is a TODO pending `setCat` import. -/

-- BOOK §1.464: TODO — full Yoneda-embedding statement:
--   H : 𝒞 → FunctorObj (OppCat 𝒞) (Type v) (B ↦ H_B = fun A => A ⟶ B)
--   is a full embedding that preserves and reflects cartesian predicates.
--   Proof sketch:
--   (i)  H_B is a functor (OppCat 𝒞 → Type v): it maps f : X ←ᵒᵖ Y (= f : Y → X in 𝒞)
--        to (f ≫ -) : (Y ⟶ B) → (X ⟶ B) (precomposition).
--   (ii) H is faithful: H_B ≅ H_C (nat. iso.) ⟹ B ≅ C  (Yoneda lemma: take A=B, track id_B).
--   (iii) H preserves terminators: H_1(A) = (A ⟶ 1) is a singleton (term_uniq).
--   (iv)  H preserves products: H_{B×C}(A) ≅ H_B(A) × H_C(A)  (universal property of ×).
--   (v)   H preserves pullbacks: H_P(A) ≅ pullback of H_f(A) and H_g(A)  (U.P. of pb).
--   Infrastructure needed: Cat (Type v) (setCat in Horn.lean, not imported here).
-- END TODO

/-! ## §1.531  Σ as a `Functor`; preservation / reflection of monos

  `Σ : A/B → A` is genuinely cross-universe (`Over B : Type (max u v)`,
  `A : Type u`), so it uses the `Monic`-specific `PreservesMono`/`ReflectsMono`
  (where `Monic` is applied directly, hence universe-clean) rather than the generic
  single-universe `Preserves`/`Reflects`. -/

/-- Σ : A/B → A is a functor; its action on arrows is the underlying arrow `.f`. -/
instance sliceForgetFunctor (B : 𝒞) : Functor (SliceForget B) where
  map f := f.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **§1.531**: Σ preserves monos.  If `m` is mono in A/B then `m.f` (= Σ m) is mono in A.
    This is the non-trivial direction of the Slice Lemma. -/
theorem sigma_preserves_mono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y)
    (hm : OverMono m) : Monic m.f := by
  intro D p q hpq
  have wq : q ≫ Z.hom = p ≫ Z.hom := by
    rw [← m.w, ← Cat.assoc, ← Cat.assoc, hpq]
  let W : Over B := ⟨D, p ≫ Z.hom⟩
  let pp : OverHom W Z := ⟨p, rfl⟩
  let qq : OverHom W Z := ⟨q, wq⟩
  have h_eq : pp ⊚ m = qq ⊚ m := OverHom.ext hpq
  exact congrArg OverHom.f (hm pp qq h_eq)

/-- **§1.531**: Σ reflects monos.  If `m.f` is mono in A then `m` is mono in A/B.
    This direction follows from the definition. -/
theorem sigma_reflects_mono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y)
    (hmMono : Monic m.f) : OverMono m := by
  intro W g h h_eq
  apply OverHom.ext
  apply hmMono
  exact congrArg OverHom.f h_eq

/-- **§1.531** in the preservation vocabulary: Σ preserves monos. -/
theorem slice_preservesMono (B : 𝒞) : PreservesMono (SliceForget B) := by
  intro Z Y m hm
  exact sigma_preserves_mono m hm

/-- **§1.531** in the reflection vocabulary: Σ reflects monos. -/
theorem slice_reflectsMono (B : 𝒞) : ReflectsMono (SliceForget B) := by
  intro Z Y m hm
  exact sigma_reflects_mono m hm

end Freyd
