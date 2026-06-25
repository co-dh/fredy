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

  Freyd §1.44: Σ is universal among functors C → A that send the designated
  terminator of C to B.  Concretely: if C has a designated terminator 1 and
  T : C → A is a functor with T(1) = B, then there exists a unique functor
  T' : C → A/B with T'(1_C) = ⟨B, id_B⟩ and T = T' ; Σ.

  A special case: any functor A → A sending each object X to B × X factors
  as Δ : A → A/B followed by Σ.  Here Δ is the DIAGONAL functor.
-/

-- BOOK §1.44: Let C be a category with a designated terminator 1, and let
-- T : C → A be a functor such that T(1) = B.  There exists a unique
-- T' : C → A/B such that T'(1) = id_B and T = T' ≫ Σ.
-- (Construct T' by T'(C) = T(C) → T(1) = B via the terminator map.)

/-! ## §1.464  Yoneda representation preserves/reflects cartesian predicates -/

-- BOOK §1.464 (Yoneda): The embedding A → S^{A°} preserves and reflects
-- the cartesian predicates.

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
