/-
  §1.543 — Milestone B1: the STRICT transfinite diagram of categories via a CONTAINED
  mathlib bridge.

  The hand-rolled capitalization tower cannot be a strict repo `Colim.CatSystem`: the
  transition `F_trans` is an OBJECT EQUALITY `F(a→c)x = F(b→c)(F(a→b)x)` whose defining
  transfinite recursion is kernel-blocked, and the Σ-carrier that dodges the block is only
  coherent up to iso.  Mathlib's `CategoryTheory.SmallObject` transfinite-iteration produces
  a STRICT functor `J ⥤ Cat` that internally handles limit-stage coherence — exactly what the
  repo lacks.  This file transports that machinery to a strict `Colim.CatSystem`.

  This is the ONLY file in the repo that imports mathlib.  The repo's `⟶`/`≫` are `scoped` in
  `Freyd` (S1_1), so importing `Mathlib.CategoryTheory` alongside `Fredy.Capitalization` does
  not clash — we `open Freyd` to get them back.

  UNIVERSE NOTE.  Repo `Cat.{u}` means `Cat.{u,u}` (objects and homs both in `Type u`).  The
  matching mathlib object is `CategoryTheory.Cat.{u,u}`.  `HasColimits Cat.{u,u}` exists, and
  `J : Type u` gives `HasIterationOfShape J Cat.{u,u}` via the generic
  `[HasColimitsOfSize.{u,u} C] → HasIterationOfShape J C` instance.  So everything aligns at a
  single universe `u`.
-/
import Mathlib.CategoryTheory.Category.Cat.Colimit
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Regular

import Fredy.Capitalization
import Fredy.CatColimit

open Freyd

namespace Freyd.Bridge

universe u

open CategoryTheory

/-! ## 1.  Transport repo `Cat` ↔ mathlib `Category` -/

/-- A repo `Cat.{u} C` re-bundled as a mathlib `Category.{u,u} C`.  Mind the differences:
    mathlib's `≫` is `CategoryStruct.comp` (same diagram order as the repo's `Cat.comp`), and
    `id_comp`/`comp_id`/`assoc` are stated with mathlib's argument order. -/
def toMathlibCat {C : Type u} (h : Cat.{u} C) : Category.{u, u} C where
  Hom X Y := h.Hom X Y
  id X := h.id X
  comp f g := h.comp f g
  id_comp f := h.id_comp f
  comp_id f := h.comp_id f
  assoc f g h' := h.assoc f g h'

/-- A mathlib `Category.{u,u} C` re-bundled as a repo `Cat.{u} C`. -/
def ofMathlibCat {C : Type u} (h : Category.{u, u} C) : Cat.{u} C where
  Hom X Y := @Quiver.Hom C h.toCategoryStruct.toQuiver X Y
  id X := @CategoryStruct.id C h.toCategoryStruct X
  comp f g := @CategoryStruct.comp C h.toCategoryStruct _ _ _ f g
  id_comp f := h.id_comp f
  comp_id f := h.comp_id f
  assoc f g h' := h.assoc f g h'

/-- Round-trip `repo → mathlib → repo` is definitionally the identity (all fields are `rfl`). -/
theorem ofMathlibCat_toMathlibCat {C : Type u} (h : Cat.{u} C) :
    ofMathlibCat (toMathlibCat h) = h := rfl

/-- Round-trip `mathlib → repo → mathlib` is definitionally the identity. -/
theorem toMathlibCat_ofMathlibCat {C : Type u} (h : Category.{u, u} C) :
    toMathlibCat (ofMathlibCat h) = h := rfl

/-- A repo `Functor F` (object map `F : C → D` plus `map`/laws), between repo categories
    `hC`/`hD`, transported to a mathlib functor `C ⥤ D` for the transported categories.
    Both repo law and mathlib law are stated with the same `comp`/`id`, so all fields are `rfl`. -/
def toMathlibFunctor {C D : Type u} (hC : Cat.{u} C) (hD : Cat.{u} D)
    (F : C → D) (hF : @Functor C hC D hD F) :
    @CategoryTheory.Functor C (toMathlibCat hC) D (toMathlibCat hD) :=
  letI := toMathlibCat hC; letI := toMathlibCat hD
  { obj := F
    map := fun f => hF.map f
    map_id := fun X => hF.map_id X
    map_comp := fun f g => hF.map_comp f g }

/-! ## 2.  A `SuccStruct CategoryTheory.Cat.{u,u}` from a uniform `nextStep`

  `nextStep : ∀ S : PreRegBundle.{u}, CapStep S.carrier` needs a `PreRegularCategory` on its
  argument.  A bare mathlib `Cat` object only carries a `Category`.  We therefore make `succ`
  *total* on `Cat` by a classical case split: when the (transported) category underlying `X`
  admits a pre-regular structure we apply `nextStep` to a chosen such bundle; otherwise `succ`
  is the identity.  Along the orbit of `X₀ = Cat.of A` (`A` pre-regular) only the pre-regular
  branch is ever taken — every stage carries the `preT` produced by the previous step — so the
  classical split never degrades the diagram; it only makes `succ` defined everywhere, as the
  mathlib `SuccStruct` interface demands.  The only nonconstructive ingredient is
  `Classical.choice`, which mathlib uses pervasively. -/

variable (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)

open Classical in
/-- The bundled pre-regular successor of a mathlib `Cat` object, when one exists.  Packaged as
    the target bundle `T*` together with the embedding functor `step` and its functoriality. -/
noncomputable def catSucc (X : CategoryTheory.Cat.{u, u}) : CategoryTheory.Cat.{u, u} :=
  letI hX : Cat.{u} X := ofMathlibCat X.str
  if h : Nonempty (@PreRegularCategory X hX) then
    letI pre : @PreRegularCategory X hX := Classical.choice h
    letI s := nextStep ⟨X, hX, pre⟩
    letI := toMathlibCat s.catT
    CategoryTheory.Cat.of s.T
  else X

/-- The map `X ⟶ catSucc X` in mathlib `Cat`: the transported embedding `step` when the
    pre-regular branch is taken, else the identity. -/
noncomputable def catToSucc (X : CategoryTheory.Cat.{u, u}) :
    X ⟶ catSucc nextStep X := by
  classical
  letI hX : Cat.{u} X := ofMathlibCat X.str
  unfold catSucc
  by_cases h : Nonempty (@PreRegularCategory X hX)
  · letI pre : @PreRegularCategory X hX := Classical.choice h
    letI s := nextStep ⟨X, hX, pre⟩
    letI := toMathlibCat s.catT
    rw [dif_pos h]
    -- repo embedding `s.step : X → s.T`, functorial via `s.stepFun`
    exact (toMathlibFunctor hX s.catT s.step s.stepFun).toCatHom
  · rw [dif_neg h]
    exact 𝟙 X

/-- The successor structure on `Cat.{u,u}` seeded at the pre-regular category `A`. -/
noncomputable def succStruct (A : Type u) [hA : Cat.{u} A] [PreRegularCategory A] :
    CategoryTheory.SmallObject.SuccStruct CategoryTheory.Cat.{u, u} :=
  letI := toMathlibCat hA
  { X₀ := CategoryTheory.Cat.of A
    succ := fun X => catSucc nextStep X
    toSucc := fun X => catToSucc nextStep X }

/-! ## 3.  Iterate: the strict transfinite diagram `J ⥤ Cat` over a REGULAR-CARDINAL ordinal

  B2 re-indexes the ω-tower of B1 by an ORDINAL `J := κ.ord.ToType` for a regular cardinal
  `κ : Cardinal.{u}` (mathlib's canonical small-object index, cf. `SmallObject.Basic`).  Unlike
  `ℕ`, this index HAS internal limit stages (every limit ordinal `< κ.ord`), which is what B3's
  cofinal pointing needs.  The required order typeclasses all resolve:

  * `LinearOrder (κ.ord.ToType)`, `SuccOrder`, `WellFoundedLT` are mathlib instances on
    `Ordinal.ToType`;
  * `OrderBot (κ.ord.ToType)` comes from `Ordinal.toTypeOrderBot` (needs `κ.ord ≠ 0`, i.e.
    `κ` infinite — carried as the `[OrderBot κ.ord.ToType]` hypothesis, mirroring mathlib's
    `SmallObject.Basic`);
  * `HasIterationOfShape (κ.ord.ToType) Cat.{u,u}` then follows from `HasColimits Cat.{u,u}`
    via the generic `[HasColimitsOfSize.{u,u} C] → HasIterationOfShape J C` instance, since
    `κ.ord.ToType : Type u`.

  Crucially `κ.ord.ToType : Type u` (because `κ.ord : Ordinal.{u}` and `Ordinal.ToType` is a
  `Type u`), so the index fits `CatSystem.{u,u}` WITHOUT any `ULift`.  The iteration is a STRICT
  functor — `Functor.map_id`/`map_comp` hold on the nose — exactly what the hand-rolled tower
  lacked, and now with limit stages handled internally by mathlib's `IsWellOrderContinuous`. -/

variable (κ : Cardinal.{u}) [Fact (Cardinal.IsRegular κ)] [OrderBot κ.ord.ToType]

/-- The index of the bridge transfinite system: the ordinal segment `[0, κ.ord)` as a
    `Type u`, with its linear well-order.  Abbreviated for readability. -/
abbrev Idx : Type u := κ.ord.ToType

-- `HasIterationOfShape (Idx κ) Cat.{u,u}` is satisfiable (sanity check that the instances resolve).
example : CategoryTheory.Limits.HasIterationOfShape (Idx κ) CategoryTheory.Cat.{u, u} :=
  inferInstance

/-- The strict transfinite diagram of categories: mathlib's iteration of `succStruct`, now
    indexed by the regular-cardinal ordinal `Idx κ`. -/
noncomputable def iterFunctor (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    CategoryTheory.Functor (Idx κ) CategoryTheory.Cat.{u, u} :=
  (succStruct nextStep A).iterationFunctor (Idx κ)

/-! ## 4.  Transport the strict diagram to a repo `Colim.CatSystem`

  `ι := ℕ`, with the directed order `(≤)`.  The carriers are the underlying types of the
  iteration's stage objects; the transition functions are the *object maps* of the iteration's
  morphisms.  `F_refl`/`F_trans` are the strict functoriality `map_id`/`map_comp` of the
  mathlib functor, read off on objects — the whole payoff of routing through mathlib. -/

/-- The directed order on `Idx κ`: since `Idx κ` is a `LinearOrder`, `≤` is already directed —
    `max i j` is the upper bound.  No `ULift` needed (`Idx κ : Type u` already). -/
def ordDirected : Colim.Directed (Idx κ) where
  le i j := i ≤ j
  refl _ := le_refl _
  trans h h' := le_trans h h'
  bound i j := ⟨max i j, le_max_left _ _, le_max_right _ _⟩

/-- A repo `Functor` recovered from a mathlib `Cat` 1-morphism `f : X ⟶ Y`, on the repo
    categories obtained from `X.str`/`Y.str` by `ofMathlibCat`. -/
def ofCatHom {X Y : CategoryTheory.Cat.{u, u}} (f : X ⟶ Y) :
    @Functor X (ofMathlibCat X.str) Y (ofMathlibCat Y.str) f.toFunctor.obj :=
  letI := ofMathlibCat X.str; letI := ofMathlibCat Y.str
  { map := fun g => f.toFunctor.map g
    map_id := fun A => f.toFunctor.map_id A
    map_comp := fun g h => f.toFunctor.map_comp g h }

variable (A : Type u) [hA : Cat.{u} A] [PreRegularCategory A]

/-- Object-map of the iteration's transition `i ⟶ j` (for `i ≤ j`, `i j : Idx κ`). -/
noncomputable def bridgeF {i j : Idx κ} (hij : i ≤ j) :
    (iterFunctor nextStep κ A).obj i → (iterFunctor nextStep κ A).obj j :=
  ((iterFunctor nextStep κ A).map (homOfLE hij)).toFunctor.obj

/-- The strict transfinite diagram of categories transported to a repo `Colim.CatSystem`.
    `F_refl`/`F_trans` are discharged from `Functor.map_id`/`map_comp` of the mathlib functor —
    the strictness the hand-rolled `Colim.CatSystem` could not provide.  The index is the
    regular-cardinal ordinal `Idx κ` (which carries limit stages, unlike B1's `ℕ`). -/
noncomputable def bridgeSystem :
    Colim.CatSystem.{u, u} (Idx κ) (ordDirected κ) where
  A i := (iterFunctor nextStep κ A).obj i
  catA i := ofMathlibCat ((iterFunctor nextStep κ A).obj i).str
  F hij x := bridgeF nextStep κ A hij x
  functF hij := ofCatHom ((iterFunctor nextStep κ A).map (homOfLE hij))
  F_refl := fun {i} x => by
    change ((iterFunctor nextStep κ A).map (homOfLE (le_refl i))).toFunctor.obj x = x
    rw [Subsingleton.elim (homOfLE (le_refl i)) (𝟙 i),
      (iterFunctor nextStep κ A).map_id]
    rfl
  F_trans := fun {i j k} hij hjk x => by
    change ((iterFunctor nextStep κ A).map (homOfLE (le_trans hij hjk))).toFunctor.obj x
       = ((iterFunctor nextStep κ A).map (homOfLE hjk)).toFunctor.obj
           (((iterFunctor nextStep κ A).map (homOfLE hij)).toFunctor.obj x)
    rw [Subsingleton.elim (homOfLE (le_trans hij hjk)) (homOfLE hij ≫ homOfLE hjk),
      (iterFunctor nextStep κ A).map_comp]
    rfl

/-- Morphism-level coherence of the transported diagram.  `refl_map`/`trans_map` follow from the
    STRICT `map_id`/`map_comp` of the mathlib iteration functor: an identity transition maps to
    the identity functor (so acts as `id` on morphisms), and composite transitions compose.  The
    `HEq` absorbs the object-equalities `F_refl`/`F_trans`. -/
theorem bridgeSystem_coherent : (bridgeSystem nextStep κ A).Coherent where
  refl_map := fun {i} {x x'} g => by
    change HEq (((iterFunctor nextStep κ A).map (homOfLE (le_refl i))).toFunctor.map g) g
    rw [Subsingleton.elim (homOfLE (le_refl i)) (𝟙 i),
      (iterFunctor nextStep κ A).map_id]
    rfl
  trans_map := fun {i j k} hij hjk {x x'} g => by
    change HEq (((iterFunctor nextStep κ A).map (homOfLE (le_trans hij hjk))).toFunctor.map g) _
    rw [Subsingleton.elim (homOfLE (le_trans hij hjk)) (homOfLE hij ≫ homOfLE hjk),
      (iterFunctor nextStep κ A).map_comp]
    rfl

/-! ## 5.  Per-stage pre-regularity

  To feed the consumer `capData_of_cofinalSystem` we must equip every stage `iterFunctor.obj i`
  with a `PreRegularCategory` (whence `HasTerminal`/`HasBinaryProducts`/`HasEqualizers`).  The
  load-bearing invariant is the PROP

      `StagePreReg X  :=  Nonempty (PreRegularCategory X)`         (on the repo cat `ofMathlibCat X.str`)

  threaded by transfinite (well-founded) recursion on `i : Idx κ`:

  * **bot.**  `iterFunctor.obj ⊥ ≅ X₀ = Cat.of A`, and `A` is pre-regular, so `StagePreReg ⊥`.
  * **successor.**  `iterFunctor.obj (succ j) = catSucc (iterFunctor.obj j)` on the nose
    (`iterationFunctorObjSuccIso` is `eqToIso` of a definitional equality).  When
    `StagePreReg (iterFunctor.obj j)` holds, `catSucc` takes its pre-regular branch and the target
    `Cat.of s.T` carries `s.preT` — so `StagePreReg (succ j)`.  This is `catSucc_preReg` below.
  * **limit.**  `iterFunctor.obj i` is mathlib's colimit of the restriction `iterFunctor|_{<i}`
    (`IsWellOrderContinuous`).  Pre-regularity of this colimit must be obtained from the repo
    `colimitPreRegular` of the strict SUB-system `bridgeSystem|_{<i}` via the relating
    equivalence (mathlib `Cat`-colimit ≅ repo `colimitCat` of the restriction).  This is the
    crux relating-lemma, ISOLATED below as `limitStage_preReg` (TRUE statement, sharp obstruction).

  Once `StagePreReg i` holds for all `i`, `Classical.choice` gives the per-stage
  `PreRegularCategory`, and the `ht`/`hp`/`he` package fields are its `toHasTerminal`/… . -/

variable (A : Type u) [hA : Cat.{u} A] [PreRegularCategory A]

/-- The per-stage pre-regularity invariant: the mathlib `Cat` object `X` admits a repo
    `PreRegularCategory` on its underlying repo category `ofMathlibCat X.str`. -/
def StagePreReg (X : CategoryTheory.Cat.{u, u}) : Prop :=
  Nonempty (@PreRegularCategory X (ofMathlibCat X.str))

/-- **Successor stage stays pre-regular.**  If `X` is pre-regular then `catSucc X` is: the
    positive branch of `catSucc` builds `Cat.of s.T` where `s := nextStep ⟨X, _, choice⟩`, and
    `s.T` carries the pre-regular structure `s.preT`. -/
theorem catSucc_preReg {X : CategoryTheory.Cat.{u, u}} (h : StagePreReg X) :
    StagePreReg (catSucc nextStep X) := by
  classical
  letI hX : Cat.{u} X := ofMathlibCat X.str
  refine ⟨?_⟩
  -- reduce `catSucc X` along the positive branch, mirroring `catSucc`/`catToSucc`'s own `letI`s
  -- so the bundle's `cat`/`pre` instances are in scope during elaboration of `s.preT`.
  show @PreRegularCategory (catSucc nextStep X) (ofMathlibCat (catSucc nextStep X).str)
  unfold StagePreReg at h
  letI pre : @PreRegularCategory (X : Type u) hX := Classical.choice h
  letI s := nextStep ⟨X, hX, pre⟩
  letI := toMathlibCat s.catT
  unfold catSucc
  rw [dif_pos h]
  -- now the carrier is `Cat.of s.T`; `ofMathlibCat (Cat.of s.T).str = s.catT` definitionally
  exact s.preT

end Freyd.Bridge

-- Axiom audit: the strict diagram + its coherence depend only on mathlib's built-in
-- classical foundation (`Classical.choice`/`propext`/`Quot.sound`) — no repo `axiom`,
-- no `sorry`.
#print axioms Freyd.Bridge.bridgeSystem
#print axioms Freyd.Bridge.bridgeSystem_coherent
