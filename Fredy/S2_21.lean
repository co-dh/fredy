/-
  Freyd & Scedrov, *Categories and Allegories* — splitting symmetric idempotents.

  This is the allegory-internal "split-idempotent" (Cauchy / systemic) completion
  of an allegory, the construction `𝒮𝓅𝓁` of §2.164–§2.167 (the book writes it
  `𝒮ℳ𝒶𝓅(g)` for a class `g` of symmetric idempotents; here we split *all*
  symmetric idempotents).

  §2.12   A COREFLEXIVE is symmetric idempotent; a SYMMETRIC IDEMPOTENT `e = e° = ee`
          is a "partial equivalence relation".
  §2.162  If `R, S` splits a symmetric idempotent `T` then `S = R°`.
  §2.163  A coreflexive `A` splits iff it is tabular; an equivalence `E` splits iff
          it is effective.
  §2.164  For a class `g` of symmetric idempotents the splitting category
          `𝒮ℳ𝒶𝓅(g)` carries a natural allegory structure with
            (e ⟶_R f)° = (f ⟶_{R°} e),    (e ⟶_R f) ∩ (e ⟶_S f) = (e ⟶_{R∩S} f);
          and the full inclusion `A ↪ 𝒮ℳ𝒶𝓅(g)` is a faithful representation of
          allegories.  In `𝒮ℳ𝒶𝓅(g)` every idempotent in `g` splits.

  We build the completion `Spl 𝒜` (splitting *all* symmetric idempotents of `𝒜`),
  prove it is an `Allegory`, exhibit the faithful full embedding `𝒜 ↪ Spl 𝒜`, and
  prove that the relevant idempotents split in `Spl 𝒜`.

  Conventions follow the repo: diagram-order composition `R ≫ S` (first `R`, then
  `S`), reciprocation `R°`, intersection `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/

import Fredy.S2_1

universe v u

namespace Freyd.Alg

open Cat

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## Symmetric idempotents -/

/-- `R` is a SYMMETRIC IDEMPOTENT (§2.12): `R° = R` and `RR = R`.  Such a morphism
    is a "partial equivalence relation".  Both coreflexives and equivalence
    relations are symmetric idempotents (§2.163). -/
structure SymIdem (a : 𝒜) where
  /-- The underlying endomorphism `e : a ⟶ a`. -/
  e : a ⟶ a
  /-- SYMMETRIC: `e° = e`. -/
  sym : e° = e
  /-- IDEMPOTENT: `e ≫ e = e`. -/
  idem : e ≫ e = e

namespace SymIdem

variable {a : 𝒜}

/-- A symmetric idempotent is symmetric in the sense of §2.12 (`e° ⊑ e`). -/
theorem symmetric (E : SymIdem a) : Symmetric E.e := by
  dsimp [Symmetric]; rw [E.sym]; exact le_refl _

end SymIdem

/-! ## §2.164  The splitting completion `Spl 𝒜`

  Objects are symmetric idempotents `e : a ⟶ a` of `𝒜` (paired with their carrier
  object).  A morphism `e ⟶ f` is a morphism `R : a ⟶ b` of `𝒜` *split-typed* by
  the condition `e ≫ R ≫ f = R` (the book's `eRf = R`).  Composition,
  reciprocation and intersection are inherited from `𝒜`; the identity on `e` is
  `e` itself. -/

/-- An object of the splitting completion: a symmetric idempotent of `𝒜`. -/
structure SplObj (𝒜 : Type u) [Allegory 𝒜] where
  /-- The carrier object of `𝒜`. -/
  carrier : 𝒜
  /-- The symmetric idempotent that this object *is*. -/
  idem : SymIdem carrier

/-- A morphism `e ⟶ f` of the splitting completion: a morphism `R` of `𝒜` that is
    fixed by pre/post-composition with the two idempotents, `e ≫ R ≫ f = R`. -/
structure SplHom (E F : SplObj 𝒜) where
  /-- The underlying morphism of `𝒜`. -/
  R : E.carrier ⟶ F.carrier
  /-- The split-typing condition `e ≫ R ≫ f = R` (the book's `eRf = R`). -/
  fixed : E.idem.e ≫ R ≫ F.idem.e = R

namespace SplHom

variable {E F G : SplObj 𝒜}

/-- Two split-homs are equal iff their underlying morphisms are equal. -/
@[ext] theorem ext {R S : SplHom E F} (h : R.R = S.R) : R = S := by
  cases R; cases S; cases h; rfl

/-- One-sided absorption on the left: `e ≫ R = R`. -/
theorem fixed_left (R : SplHom E F) : E.idem.e ≫ R.R = R.R := by
  calc E.idem.e ≫ R.R
      = E.idem.e ≫ (E.idem.e ≫ R.R ≫ F.idem.e) := by rw [R.fixed]
    _ = (E.idem.e ≫ E.idem.e) ≫ (R.R ≫ F.idem.e) := by rw [← Cat.assoc]
    _ = E.idem.e ≫ (R.R ≫ F.idem.e) := by rw [E.idem.idem]
    _ = R.R := R.fixed

/-- One-sided absorption on the right: `R ≫ f = R`. -/
theorem fixed_right (R : SplHom E F) : R.R ≫ F.idem.e = R.R := by
  calc R.R ≫ F.idem.e
      = (E.idem.e ≫ (R.R ≫ F.idem.e)) ≫ F.idem.e := by rw [R.fixed]
    _ = E.idem.e ≫ (R.R ≫ (F.idem.e ≫ F.idem.e)) := by rw [Cat.assoc, Cat.assoc]
    _ = E.idem.e ≫ (R.R ≫ F.idem.e) := by rw [F.idem.idem]
    _ = R.R := R.fixed

end SplHom

/-! ### The category structure -/

/-- Identity split-hom on `e`: the idempotent `e` itself (`e ≫ e ≫ e = e`). -/
def splId (E : SplObj 𝒜) : SplHom E E :=
  ⟨E.idem.e, by rw [E.idem.idem, E.idem.idem]⟩

/-- Composition of split-homs is the underlying `≫`; the fixed condition is
    preserved because `e (RS) g = (eR)(Sg) = RS` (left-absorption of `R`,
    right-absorption of `S`). -/
def splComp {E F G : SplObj 𝒜} (R : SplHom E F) (S : SplHom F G) : SplHom E G :=
  ⟨R.R ≫ S.R, by
    calc E.idem.e ≫ (R.R ≫ S.R) ≫ G.idem.e
        = (E.idem.e ≫ R.R) ≫ (S.R ≫ G.idem.e) := by rw [Cat.assoc, Cat.assoc]
      _ = R.R ≫ S.R := by rw [R.fixed_left, S.fixed_right]⟩

/-- The splitting completion is a category: identity `splId`, composition
    `splComp`; the three category laws hold on underlying morphisms. -/
instance instCatSpl : Cat.{v} (SplObj 𝒜) where
  Hom E F := SplHom E F
  id E := splId E
  comp R S := splComp R S
  id_comp R := by
    apply SplHom.ext; show (splId _).R ≫ R.R = R.R
    exact R.fixed_left
  comp_id R := by
    apply SplHom.ext; show R.R ≫ (splId _).R = R.R
    exact R.fixed_right
  assoc R S T := by
    apply SplHom.ext; show (R.R ≫ S.R) ≫ T.R = R.R ≫ (S.R ≫ T.R)
    exact Cat.assoc _ _ _

/-! ### Reciprocation and intersection -/

/-- Reciprocation of a split-hom: `R° : f ⟶ e`.  The fixed condition transports by
    `f R° e = (e R f)° = R°` using symmetry of `e` and `f`. -/
def splRecip {E F : SplObj 𝒜} (R : SplHom E F) : SplHom F E :=
  ⟨R.R°, by
    calc F.idem.e ≫ R.R° ≫ E.idem.e
        = (E.idem.e ≫ R.R ≫ F.idem.e)° := by
            simp only [Allegory.recip_comp, E.idem.sym, F.idem.sym, Cat.assoc]
      _ = R.R° := by rw [R.fixed]⟩

/-- Intersection of two parallel split-homs: `R ∩ S : e ⟶ f`.  The fixed condition
    is preserved: `e (R∩S) f = (eRf) ∩ (eSf) = R ∩ S`. -/
def splInter {E F : SplObj 𝒜} (R S : SplHom E F) : SplHom E F :=
  ⟨R.R ∩ S.R, by
    -- `e (R∩S) f = R ∩ S`.  We show both `⊑` directions.
    apply le_antisymm
    · -- `e (R∩S) f ⊑ eRf ∩ eSf = R ∩ S`.  The map `X ↦ e X f` is monotone.
      have hmono : ∀ {X Y : E.carrier ⟶ F.carrier}, X ⊑ Y →
          E.idem.e ≫ X ≫ F.idem.e ⊑ E.idem.e ≫ Y ≫ F.idem.e :=
        fun hXY => comp_mono_left _ (comp_mono_right hXY _)
      have hR : E.idem.e ≫ (R.R ∩ S.R) ≫ F.idem.e ⊑ R.R := by
        have := hmono (inter_lb_left R.R S.R); rw [R.fixed] at this; exact this
      have hS : E.idem.e ≫ (R.R ∩ S.R) ≫ F.idem.e ⊑ S.R := by
        have := hmono (inter_lb_right R.R S.R); rw [S.fixed] at this; exact this
      exact le_inter hR hS
    · -- `R ∩ S ⊑ e (R∩S) f`.  Insert `e` on the left and `f` on the right by the
      -- dual modular law, using `M ⊑ R = eRf`.  Write `e = E.e`, `f = F.e`,
      -- `M = R.R ∩ S.R`.
      -- DUAL MODULAR (reciprocal of `modular_le`):  e≫X ∩ T ⊑ e≫(X ∩ e°≫T).
      have dual_modular : ∀ {b : 𝒜} (X : E.carrier ⟶ b) (T : E.carrier ⟶ b),
          (E.idem.e ≫ X) ∩ T ⊑ E.idem.e ≫ (X ∩ E.idem.e° ≫ T) := by
        intro b X T
        have hr := recip_mono (modular_le X° E.idem.e° T°)
        rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip] at hr
        rw [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_comp,
            Allegory.recip_recip, Allegory.recip_recip] at hr
        rw [Allegory.recip_recip] at hr
        exact hr
      have hMR_eq : R.R ∩ (R.R ∩ S.R) = R.R ∩ S.R := by
        rw [Allegory.inter_assoc, Allegory.inter_idem]
      -- M ⊑ e≫M.   Dual modular with X=R, T=M:  R∩M ⊑ e≫(R ∩ e°≫M);  R∩M = M;
      --            RHS ⊑ e≫(e°≫M) = e≫(e≫M) = e≫M.
      have hMleeM : R.R ∩ S.R ⊑ E.idem.e ≫ (R.R ∩ S.R) := by
        have h1 := dual_modular R.R (R.R ∩ S.R)
        rw [R.fixed_left, hMR_eq] at h1
        refine le_trans h1 ?_
        refine le_trans (comp_mono_left _ (inter_lb_right R.R (E.idem.e° ≫ (R.R ∩ S.R)))) ?_
        rw [E.idem.sym, ← Cat.assoc, E.idem.idem]
        exact le_refl _
      -- M ⊑ M≫f.   Right modular (`modular_le`) with X=R, T=M:
      --            (R≫f)∩M ⊑ (R ∩ M≫f°)≫f;  (R≫f)∩M = M;
      --            RHS ⊑ (M≫f°)≫f = M≫(f≫f) = M≫f.
      have hMlefM : R.R ∩ S.R ⊑ (R.R ∩ S.R) ≫ F.idem.e := by
        have h1 := modular_le R.R F.idem.e (R.R ∩ S.R)
        rw [R.fixed_right, hMR_eq] at h1
        refine le_trans h1 ?_
        refine le_trans (comp_mono_right (inter_lb_right R.R ((R.R ∩ S.R) ≫ F.idem.e°)) _) ?_
        rw [Cat.assoc, F.idem.sym, F.idem.idem]
        exact le_refl _
      -- Combine: M ⊑ e≫M ⊑ e≫(M≫f) = e≫M≫f.
      refine le_trans hMleeM ?_
      exact comp_mono_left _ hMlefM⟩

/-! ### `Spl 𝒜` is an allegory -/

instance instAllegorySpl : Allegory.{v} (SplObj 𝒜) where
  recip R := splRecip R
  inter R S := splInter R S
  recip_recip R := by
    apply SplHom.ext; show R.R°° = R.R; exact Allegory.recip_recip _
  recip_comp R S := by
    apply SplHom.ext; show (R.R ≫ S.R)° = S.R° ≫ R.R°; exact Allegory.recip_comp _ _
  recip_inter R S := by
    apply SplHom.ext; show (R.R ∩ S.R)° = R.R° ∩ S.R°; exact Allegory.recip_inter _ _
  inter_idem R := by
    apply SplHom.ext; show R.R ∩ R.R = R.R; exact Allegory.inter_idem _
  inter_comm R S := by
    apply SplHom.ext; show R.R ∩ S.R = S.R ∩ R.R; exact Allegory.inter_comm _ _
  inter_assoc R S T := by
    apply SplHom.ext; show R.R ∩ (S.R ∩ T.R) = (R.R ∩ S.R) ∩ T.R
    exact Allegory.inter_assoc _ _ _
  semidistrib R S T := by
    apply SplHom.ext
    show R.R ≫ (S.R ∩ T.R) = ((R.R ≫ S.R) ∩ (R.R ≫ (S.R ∩ T.R))) ∩ (R.R ≫ T.R)
    exact Allegory.semidistrib _ _ _
  modular R S T := by
    apply SplHom.ext
    show (R.R ≫ S.R) ∩ T.R
        = ((R.R ≫ S.R) ∩ T.R) ∩ ((R.R ∩ (T.R ≫ S.R°)) ≫ S.R)
    exact Allegory.modular _ _ _

/-! ## §2.164  The faithful full embedding `𝒜 ↪ Spl 𝒜`

  On objects, `a ↦ (a, 1_a)` (the identity is a symmetric idempotent).
  On morphisms, `R : a ⟶ b` maps to itself, since `1_a ≫ R ≫ 1_b = R`.  This is a
  representation of allegories: it preserves identities, composition, reciprocation
  and intersection.  It is faithful (injective on hom-sets) and full (every
  split-hom between embedded objects comes from a unique `R`). -/

/-- The identity `1_a` is a symmetric idempotent. -/
def idSymIdem (a : 𝒜) : SymIdem a :=
  ⟨Cat.id a, recip_id, Cat.id_comp _⟩

/-- The embedding on objects: `a ↦ (a, 1_a)`. -/
def embObj (a : 𝒜) : SplObj 𝒜 := ⟨a, idSymIdem a⟩

/-- The embedding on morphisms: `R ↦ R`, with witness `1 ≫ R ≫ 1 = R`. -/
def embHom {a b : 𝒜} (R : a ⟶ b) : SplHom (embObj a) (embObj b) :=
  ⟨R, by show Cat.id a ≫ R ≫ Cat.id b = R; rw [Cat.comp_id, Cat.id_comp]⟩

@[simp] theorem embHom_R {a b : 𝒜} (R : a ⟶ b) : (embHom R).R = R := rfl

/-- The embedding is FAITHFUL: injective on hom-sets. -/
theorem embHom_injective {a b : 𝒜} {R S : a ⟶ b} (h : embHom R = embHom S) : R = S :=
  congrArg SplHom.R h

/-- The embedding is FULL: every split-hom between embedded objects is `embHom R`
    for a unique `R` (namely its underlying morphism). -/
theorem embHom_full {a b : 𝒜} (φ : SplHom (embObj a) (embObj b)) :
    embHom φ.R = φ := by
  apply SplHom.ext; rfl

/-- The embedding preserves identities: `embHom 1_a = 1_{(a,1)}`. -/
theorem embHom_id (a : 𝒜) : embHom (Cat.id a) = Cat.id (embObj a) := by
  apply SplHom.ext; rfl

/-- The embedding preserves composition. -/
theorem embHom_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    (embHom (R ≫ S) : embObj a ⟶ embObj c)
      = splComp (embHom R) (embHom S) := by
  apply SplHom.ext; rfl

/-- The embedding preserves reciprocation. -/
theorem embHom_recip {a b : 𝒜} (R : a ⟶ b) :
    (embHom (R°) : embObj b ⟶ embObj a) = splRecip (embHom R) := by
  apply SplHom.ext; rfl

/-- The embedding preserves intersection. -/
theorem embHom_inter {a b : 𝒜} (R S : a ⟶ b) :
    (embHom (R ∩ S) : embObj a ⟶ embObj b) = splInter (embHom R) (embHom S) := by
  apply SplHom.ext; rfl

/-! ## §2.164  Idempotents split in the completion

  We follow the book's notion of a splitting (§1.281): `(x, y)` splits an idempotent
  `e : A ⟶ A` if `x ≫ y = e` and `y ≫ x = 1`.  We show every symmetric idempotent
  `E.e` of `𝒜`, embedded as the endomorphism `embHom E.e : (a,1) ⟶ (a,1)`, splits
  in `Spl 𝒜` through the new object `(a, E)`. -/

/-- The "down" leg `(a,1) ⟶ (a,E)` of the splitting: underlying `E.e`. -/
def splDown {a : 𝒜} (E : SymIdem a) : SplHom (embObj a) ⟨a, E⟩ :=
  ⟨E.e, by show Cat.id a ≫ E.e ≫ E.e = E.e; rw [Cat.id_comp, E.idem]⟩

/-- The "up" leg `(a,E) ⟶ (a,1)` of the splitting: underlying `E.e`. -/
def splUp {a : 𝒜} (E : SymIdem a) : SplHom (⟨a, E⟩ : SplObj 𝒜) (embObj a) :=
  ⟨E.e, by show E.e ≫ E.e ≫ Cat.id a = E.e; rw [Cat.comp_id, E.idem]⟩

/-- `(splDown E, splUp E)` SPLITS the embedded idempotent: `down ≫ up = embHom E.e`. -/
theorem splDown_up {a : 𝒜} (E : SymIdem a) :
    splComp (splDown E) (splUp E) = embHom E.e := by
  apply SplHom.ext; show E.e ≫ E.e = E.e; exact E.idem

/-- `(splDown E, splUp E)` SPLITS: `up ≫ down = 1_{(a,E)}` (the identity on `(a,E)`,
    whose underlying morphism is `E.e`). -/
theorem splUp_down {a : 𝒜} (E : SymIdem a) :
    splComp (splUp E) (splDown E) = splId (⟨a, E⟩ : SplObj 𝒜) := by
  apply SplHom.ext; show E.e ≫ E.e = E.e; exact E.idem

/-- §2.164: every symmetric idempotent of `𝒜` splits in `Spl 𝒜`.  The embedded
    idempotent `embHom E.e` factors as `down ≫ up` with `up ≫ down = 1`, where
    `splComp` is composition and `splId` the identity of `Spl 𝒜`. -/
theorem embHom_idem_splits {a : 𝒜} (E : SymIdem a) :
    splComp (splDown E) (splUp E) = embHom E.e ∧
    splComp (splUp E) (splDown E) = splId (⟨a, E⟩ : SplObj 𝒜) :=
  ⟨splDown_up E, splUp_down E⟩

/-! ## §2.162  A splitting of a symmetric idempotent is reciprocal: `S = R°`

  If `R ≫ S = T` (symmetric idempotent) and `S ≫ R = 1`, then `S = R°`. -/

/-- §2.162: if `(R, S)` splits a symmetric idempotent `T = R ≫ S` (so `S ≫ R = 1`
    and `(R ≫ S)° = R ≫ S`), then `S = R°`.

    Book proof (§2.162), every step a containment using `SR = 1`, `(RS)° = RS`,
    and the basic identity `X ⊑ X X° X` (`le_comp_codom`/modular):
      `R° = (SR)R° ⊑ SS°(SR)R° ⊑ SS°R° ⊑ S(RS)° ⊑ (SR)S ⊑ S`,
      `S° ⊑ S°(SR) ⊑ S°(SR)(R°R) ⊑ S°R°R ⊑ (RS)°R ⊑ R(SR) ⊑ R`  (so `S ⊑ R°`). -/
theorem splitting_recip {a b : 𝒜} {R : a ⟶ b} {S : b ⟶ a}
    (hSR : S ≫ R = Cat.id b) (hsym : (R ≫ S)° = R ≫ S) : S = R° := by
  -- Basic identity used twice:  `X ⊑ X ≫ X° ≫ X`.
  -- Proof: `X° ⊑ (1 ∩ X°X)≫X°` by modular law (with `R=1, S=X°, T=X°`);
  -- reciprocate and weaken `(1 ∩ X°X) ⊑ X°X`.
  have codom : ∀ {x y : 𝒜} (X : x ⟶ y), X ⊑ X ≫ X° ≫ X := by
    intro x y X
    have hm := modular_le (Cat.id y) (X°) (X°)
    rw [Cat.id_comp, Allegory.inter_idem, Allegory.recip_recip] at hm
    -- hm : X° ⊑ (1 ∩ X°≫X) ≫ X°
    have hr := recip_mono hm
    rw [Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_inter, recip_id,
        Allegory.recip_comp, Allegory.recip_recip] at hr
    -- hr : X ⊑ X ≫ (1 ∩ X°≫X)
    refine le_trans hr ?_
    exact comp_mono_left X (inter_lb_right (Cat.id y) (X° ≫ X))
  -- `1_b ⊑ S S°`:   `1_b = S ≫ R ⊑ (S ≫ S° ≫ S) ≫ R = S ≫ S° ≫ (S ≫ R) = S ≫ S°`.
  have h1_le_SSr : Cat.id b ⊑ S ≫ S° := by
    have h : S ≫ R ⊑ (S ≫ S° ≫ S) ≫ R := comp_mono_right (codom S) R
    rw [hSR] at h
    calc Cat.id b ⊑ (S ≫ S° ≫ S) ≫ R := h
      _ = S ≫ S° ≫ (S ≫ R) := by rw [Cat.assoc, Cat.assoc]
      _ = S ≫ S° := by rw [hSR, Cat.comp_id]
  -- `R° ⊑ S`:   `R° = 1_b ≫ R° ⊑ (S S°) R° = S (S° R°) = S (R S)° = S (R S) = (S R) S = S`.
  have hRrecip_le_S : R° ⊑ S := by
    calc R° = Cat.id b ≫ R° := by rw [Cat.id_comp]
      _ ⊑ (S ≫ S°) ≫ R° := comp_mono_right h1_le_SSr R°
      _ = S ≫ (R ≫ S)° := by rw [Cat.assoc, Allegory.recip_comp]
      _ = S ≫ (R ≫ S) := by rw [hsym]
      _ = (S ≫ R) ≫ S := by rw [Cat.assoc]
      _ = S := by rw [hSR, Cat.id_comp]
  -- `S° ⊑ R`:   `S° = S° (S R) ⊑ S° (S R) (R° R) = S° R° R = (R S)° R = (R S) R = R (S R) = R`.
  have hSrecip_le_R : S° ⊑ R := by
    -- `S R ⊑ (S R)(R° R)`  from  `R ⊑ R R° R`  (post-compose `R° R`, pre-compose `S`).
    have hStep : S ≫ R ⊑ (S ≫ R) ≫ (R° ≫ R) := by
      have h : S ≫ R ⊑ S ≫ (R ≫ R° ≫ R) := comp_mono_left S (codom R)
      calc S ≫ R ⊑ S ≫ (R ≫ R° ≫ R) := h
        _ = (S ≫ R) ≫ (R° ≫ R) := (Cat.assoc S R (R° ≫ R)).symm
    calc S° = S° ≫ (S ≫ R) := by rw [hSR, Cat.comp_id]
      _ ⊑ S° ≫ ((S ≫ R) ≫ (R° ≫ R)) := comp_mono_left S° hStep
      _ = S° ≫ R° ≫ R := by rw [hSR, Cat.id_comp]
      _ = (S° ≫ R°) ≫ R := (Cat.assoc S° R° R).symm
      _ = (R ≫ S)° ≫ R := by rw [Allegory.recip_comp]
      _ = (R ≫ S) ≫ R := by rw [hsym]
      _ = R ≫ (S ≫ R) := by rw [Cat.assoc]
      _ = R := by rw [hSR, Cat.comp_id]
  -- Combine: `S ⊑ R°` (recip of `S° ⊑ R`) and `R° ⊑ S`.
  have hS_le_Rrecip : S ⊑ R° := by
    have := recip_mono hSrecip_le_R; rwa [Allegory.recip_recip] at this
  exact le_antisymm hS_le_Rrecip hRrecip_le_S

/-! ## §2.212  Maps of a tabular unitary distributive allegory form a pre-logos

  "If A is a tabular unitary distributive allegory, then Mon_U(A) is a pre-logos."
  [§2.212, proof: §2.154 gives regular; subobjects = coreflexives; finite unions exist.]

  Partial progress in `Fredy/MapCat.lean`:
  - `mapHasTerminal` PROVED: unit object is terminal in Map(A).
  - Remaining (HasImages, HasPullbacks, HasBinaryProducts, PullbacksTransferCovers,
    HasSubobjectUnions, PreLogos) are TODO comments in MapCat.lean.  Their §2.147 UMPs
    (`tab_pullback_UMP`, `tab_equalizer_UMP`) are now PROVED under the source-apex
    `Tabulates`; what remains is only the typeclass-instance packaging. -/

-- BOOK §2.212: If A is a tabular unitary distributive allegory, then Mon_U(A) is a pre-logos.
-- Partial: mapHasTerminal proved in Fredy/MapCat.lean; rest TODO (UMPs proved, packaging left).

/-! ## §2.214  Pre-logos positive iff Rel(C) has finite coproducts

  "A pre-logos C is positive iff Rel(C) has finite coproducts."
  [§2.214, uses §2.215 duality coproduct ↔ product via reciprocation.]

  Requires: the `Rel(C)` construction sending `[PreLogos 𝒞]` to a `DistributiveAllegory`
  (Ch1→Ch2 bridge).  The left-to-right direction was proved in the §2.214 text above
  (coproduct → five equations via `coproduct_five_eqs_to_universal`).  Not yet typed. -/

-- BOOK §2.214: A pre-logos C is positive iff Rel(C) has finite coproducts.

/-! ## §2.217  Faithful representation in a positive pre-logos / pre-topos

  "A pre-logos may be faithfully represented in a positive pre-logos."
  [§2.217, proof: start with pre-logos C, take maps of the positive reflection
  of the allegory of relations.  The two §2.217 propositions:
    (1) every pre-logos embeds faithfully in a positive pre-logos;
    (2) every pre-logos embeds faithfully in a pre-topos.]

  Both require the Ch1↔Ch2 Rel(-)/Maps(-) adjunction (not constructed).  -/

-- BOOK §2.217 (1): A pre-logos may be faithfully represented in a positive pre-logos.
-- BOOK §2.217 (2): A pre-logos may be faithfully represented in a pre-topos.

/-! ## §2.218  Faithful representation in a power of the allegory of sets

  "A small pre-tabular or semi-simple unitary distributive allegory may be faithfully
  represented in a power of the allegory of sets." [§2.218, from §2.167, §2.16(10),
  §2.213, §2.217, §1.635 — complex cross-chapter assembly.] -/

-- BOOK §2.218: A small pre-tabular or semi-simple unitary distributive allegory may be
-- faithfully represented in a power of the allegory of sets.

/-! ## §2.219  Semi-simplicity criterion for positive allegories

  "A positive allegory is semi-simple iff for every S such that S° = S and Dom(S) ⊆ S
  there exists R such that S = R°R."

  Within the allegory world: `PositiveAllegory`, `SemiSimpleAllegory`, `dom`.
  The book's `Dom(S)` is the *domain* coreflexive, but the §2.219 condition is
  about `Dom S ⊑ S`, i.e. `1 ∩ SS° ⊑ S`, which for a symmetric morphism means
  `S ≫ S ⊑ S` (see §2.219 proof sketch: apply to the matrix (1,T;T°,1)).

  The proof of ⇐ constructs `R = (F ∪ G) ≫ Dom(S)` from a semi-simple factoring
  `S = F°G`; the ⇒ direction uses the matrix argument.  Signature not yet typed
  because `dom` in this repo is `1 ∩ R ≫ R°` but the §2.219 condition needs careful
  alignment with the distributive-allegory zero. -/

-- BOOK §2.219: A positive allegory is semi-simple iff for every S with S° = S and
-- Dom(S) ⊆ S there exists R such that S = R° ≫ R.

end Freyd.Alg
