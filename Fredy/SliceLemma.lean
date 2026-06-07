/-
  Freyd & Scedrov, *Categories and Allegories* §1.53 The SLICE LEMMA.

  Imports Fredy.Capital for Cat, Mono, IsIso, Cover, HasTerminal,
  HasBinaryProducts, HasPullbacks, Cone, HasPullback.

  Defines the slice category A/B (Over, OverHom) and proves:
  §1.531  Σ : A/B → A reflects monos and covers.
  §1.532  The square
               B×A₁ —pair fst (snd≫x)—→ B×A₂
                |                       |
               snd                     snd
                v                       v
               A₁  ————x——————→       A₂
          is a pullback in any category with binary products.  Hence in a
          pre-regular category (pullbacks transfer covers), x cover ⇒
          pair fst (snd≫x) cover.  Therefore Δ preserves covers.
-/

import Fredy.Capital

set_option linter.unusedSectionVars false

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## The slice category A/B (§1.44) -/

structure Over (B : 𝒞) where
  dom : 𝒞
  hom : dom ⟶ B

/-- A morphism of A/B. -/
structure OverHom {B : 𝒞} (X Y : Over B) where
  f : X.dom ⟶ Y.dom
  w : f ≫ Y.hom = X.hom

theorem OverHom.ext {B : 𝒞} {X Y : Over B} {a b : OverHom X Y} (h : a.f = b.f) : a = b := by
  obtain ⟨af, aw⟩ := a; obtain ⟨bf, bw⟩ := b; subst h; rfl

/-- Composition in A/B (explicit, bypasses Cat instance). -/
def OverHom.comp {B : 𝒞} {X Y Z : Over B} (h : OverHom X Y) (k : OverHom Y Z) : OverHom X Z :=
  ⟨h.f ≫ k.f, by rw [Cat.assoc, k.w, h.w]⟩

infixr:80 " ⊚ " => OverHom.comp

/-- Mono in A/B (explicit, avoids `Cat` instance for `Over B`). -/
def OverMono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y) : Prop :=
  ∀ {W : Over B} (g h : OverHom W Z), g ⊚ m = h ⊚ m → g = h

/-!
## §1.531  Σ : A/B → A preserves and reflects covers
-/

/-- **§1.531**: Σ reflects monos. -/
theorem sigma_reflects_mono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y)
    (hm : OverMono m) : Mono m.f := by
  intro D p q hpq
  have wq : q ≫ Z.hom = p ≫ Z.hom := by
    rw [← m.w, ← Cat.assoc, ← Cat.assoc, hpq]
  let W : Over B := ⟨D, p ≫ Z.hom⟩
  let pp : OverHom W Z := ⟨p, rfl⟩
  let qq : OverHom W Z := ⟨q, wq⟩
  have h_eq : pp ⊚ m = qq ⊚ m := OverHom.ext hpq
  exact congrArg OverHom.f (hm pp qq h_eq)

/-- **§1.531**: Σ reflects covers.  If u.f is a cover in A, and u factors
    through a monic m in A/B (via g ⊚ m = u), then m.f is iso in A. -/
theorem sigma_reflects_cover {B : 𝒞} {X Y Z : Over B} (u : OverHom X Y) (m : OverHom Z Y)
    (g : OverHom X Z) (hu : Cover u.f) (hmMono : OverMono m) (hgm : g ⊚ m = u) : IsIso m.f := by
  have hgmA : g.f ≫ m.f = u.f := congrArg OverHom.f hgm
  have hmA : Mono m.f := sigma_reflects_mono m hmMono
  exact hu m.f g.f hmA hgmA

/-!
## §1.532  The pullback square for Δ

  In any category with binary products:

       B×A₁ —pair fst (snd≫x)—→ B×A₂
        |                       |
       snd                     snd
        v                       v
       A₁  ————x——————→       A₂

  is a pullback.
-/

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-- Helper: `pair a b ⊚ pair fst (snd ≫ x) = pair a (b ≫ x)`. (Here ⊚ is just ≫ in 𝒞.) -/
theorem pair_prod_map {X B A₁ A₂ : 𝒞} (a : X ⟶ B) (b : X ⟶ A₁) (x : A₁ ⟶ A₂) :
    pair a b ≫ pair fst (snd ≫ x) = pair a (b ≫ x) := by
  apply pair_uniq _ _ (pair a b ≫ pair fst (snd ≫ x))
  · rw [Cat.assoc, fst_pair, fst_pair]
  · calc
      (pair a b ≫ pair fst (snd ≫ x)) ≫ snd = pair a b ≫ (pair fst (snd ≫ x) ≫ snd) := by rw [Cat.assoc]
      _ = pair a b ≫ (snd ≫ x) := by rw [snd_pair]
      _ = (pair a b ≫ snd) ≫ x := by rw [← Cat.assoc]
      _ = b ≫ x := by rw [snd_pair]

/-- **§1.532 pullback square**. -/
def prod_pullback (B A₁ A₂ : 𝒞) (x : A₁ ⟶ A₂) : HasPullback (snd (A:=B) (B:=A₂)) x := by
  let P : 𝒞 := prod B A₁
  let p₁ : P ⟶ prod B A₂ := pair fst (snd ≫ x)
  let p₂ : P ⟶ A₁ := snd
  have h_sq : p₁ ≫ snd = p₂ ≫ x := by
    simp [p₁, p₂, snd_pair]
  refine {
    cone := { pt := P, π₁ := p₁, π₂ := p₂, w := h_sq }
    lift := λ c => pair (c.π₁ ≫ fst) c.π₂
    lift_fst := λ c => ?_
    lift_snd := λ c => ?_
    lift_uniq := λ c u hu₁ hu₂ => ?_
  }
  · -- lift_fst: pair (c.π₁ ≫ fst) c.π₂ ≫ p₁ = c.π₁
    dsimp [p₁]
    rw [pair_prod_map (c.π₁ ≫ fst) c.π₂ x, ← c.w]
    exact (pair_uniq (c.π₁ ≫ fst) (c.π₁ ≫ snd) c.π₁ rfl rfl).symm
  · -- lift_snd: pair (c.π₁ ≫ fst) c.π₂ ≫ p₂ = c.π₂
    dsimp [p₂]; simp [snd_pair]
  · -- lift_uniq
    apply pair_uniq _ _ u
    · dsimp [p₁] at hu₁; rw [← hu₁, Cat.assoc, fst_pair]
    · dsimp [p₂] at hu₂; rw [← hu₂]

end Freyd
