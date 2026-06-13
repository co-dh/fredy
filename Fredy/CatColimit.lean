/-
  Directed (filtered) colimit of categories — Milestone 2a (objects only).

  A `CatSystem` is a directed system of categories over `(ι, D)`: a family of
  categories `A i` with transition functors `F hij : A i → A j` respecting
  identity and composition on objects.  Its colimit's OBJECT type is the
  type-level directed colimit (Milestone 1) of the object families.  The
  hom-colimit and the `Cat` instance on the colimit are Milestone 2b.

  Category theory is hand-built on this repo's `Cat`; no mathlib here.
-/

import Fredy.S1_1
import Fredy.S1_18
import Fredy.DirectedColimit

open Freyd

namespace Freyd.Colim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- A directed system of categories over `(ι, D)`: each `A i` is a category
    (`catA i`); for `i ≤ j` a functor `F hij : A i → A j` (`functF hij`), with
    `F` respecting identity and composition on objects. -/
structure CatSystem (ι : Type u) (D : Directed ι) where
  A : ι → Type w
  catA : ∀ i, Cat.{w} (A i)
  F : ∀ {i j}, D.le i j → A i → A j
  functF : ∀ {i j} (hij : D.le i j), @Functor (A i) (catA i) (A j) (catA j) (F hij)
  F_refl : ∀ {i} (x : A i), F (D.refl i) x = x
  F_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k) (x : A i),
    F (D.trans hij hjk) x = F hjk (F hij x)

attribute [instance] CatSystem.catA

/-- Morphism-level coherence of the transition functors: an identity transition
    acts as the identity functor and composite transitions compose, on *morphisms*
    (up to the object-equalities `F_refl`/`F_trans`, hence stated with `HEq`).
    Together with the object coherence this makes `C` a genuine functor
    `(ι, ≤) → Cat`. -/
structure CatSystem.Coherent (C : CatSystem ι D) : Prop where
  refl_map : ∀ {i : ι} {x x' : C.A i} (g : x ⟶ x'),
    HEq ((C.functF (D.refl i)).map g) g
  trans_map : ∀ {i j k : ι} (hij : D.le i j) (hjk : D.le j k) {x x' : C.A i} (g : x ⟶ x'),
    HEq ((C.functF (D.trans hij hjk)).map g) ((C.functF hjk).map ((C.functF hij).map g))

/-- The underlying directed system of OBJECT types of a `CatSystem` (forget the
    morphisms): exactly a Milestone-1 `System`. -/
def CatSystem.objSystem (C : CatSystem ι D) : System ι D where
  X := C.A
  tr := C.F
  tr_refl := C.F_refl
  tr_trans := C.F_trans

/-- The OBJECTS of the colimit category: the type-level directed colimit of the
    object families. -/
def CatSystem.Obj (C : CatSystem ι D) : Type _ := Colimit C.objSystem

/-- The canonical inclusion of stage-`i` objects into the colimit's objects. -/
def CatSystem.objIncl (C : CatSystem ι D) (i : ι) (x : C.A i) : C.Obj :=
  incl C.objSystem i x

/-- Inclusions of objects are compatible with the transition functors. -/
theorem CatSystem.objIncl_compat (C : CatSystem ι D) {i j : ι} (hij : D.le i j) (x : C.A i) :
    C.objIncl j (C.F hij x) = C.objIncl i x :=
  incl_compat C.objSystem hij x

/-! ## Milestone 2b — the index of the hom-colimit

  A morphism `[⟨i,x⟩] → [⟨j,y⟩]` in the colimit will be a class in the directed
  colimit, over the common upper bounds `k` of `i` and `j`, of `Hom_{A k}(F x, F y)`.
  The first ingredient is that those upper bounds form a directed set. -/

/-- The common upper bounds of `i` and `j` in a directed preorder. -/
def UpperBound (D : Directed ι) (i j : ι) : Type u := {k : ι // D.le i k ∧ D.le j k}

/-- The common upper bounds of `i, j` are themselves a directed preorder (order
    inherited from `D`); this is the index set of the hom-colimit. -/
def upperDirected (D : Directed ι) (i j : ι) : Directed (UpperBound D i j) where
  le a b := D.le a.1 b.1
  refl a := D.refl a.1
  trans hab hbc := D.trans hab hbc
  bound a b :=
    let ⟨m, ham, hbm⟩ := D.bound a.1 b.1
    ⟨⟨m, D.trans a.2.1 ham, D.trans a.2.2 ham⟩, ham, hbm⟩

/-! ## Milestone 2b — transporting morphisms along object equalities

  The hom-colimit's transition map applies a transition functor and then re-types
  the result along the object equalities of `F_refl`/`F_trans`.  `castHom` is that
  re-typing; `castHom_of_heq` says a `HEq`-equal morphism transports to its partner,
  which is exactly what the colimit laws need to cancel the casts. -/

/-- Transport a morphism `m : X ⟶ Y` to `X' ⟶ Y'` along object equalities. -/
def castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y')
    (m : X ⟶ Y) : X' ⟶ Y' := hX ▸ hY ▸ m

@[simp] theorem castHom_rfl {𝒜 : Type w} [Cat.{w} 𝒜] {X Y : 𝒜} (m : X ⟶ Y) :
    castHom rfl rfl m = m := rfl

/-- A morphism heterogeneously equal to `g` transports (along the matching object
    equalities) exactly to `g`. -/
theorem castHom_of_heq {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') {m : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq m g) :
    castHom hX hY m = g := by
  subst hX; subst hY; simpa [castHom] using h

/-- Transports compose. -/
theorem castHom_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' X'' Y'' : 𝒜}
    (h1X : X = X') (h1Y : Y = Y') (h2X : X' = X'') (h2Y : Y' = Y'') (m : X ⟶ Y) :
    castHom h2X h2Y (castHom h1X h1Y m) = castHom (h1X.trans h2X) (h1Y.trans h2Y) m := by
  subst h1X; subst h1Y; subst h2X; subst h2Y; rfl

/-- Transport distributes over composition. -/
theorem castHom_comp {𝒜 : Type w} [Cat.{w} 𝒜] {X Y Z X' Y' Z' : 𝒜}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (m : X ⟶ Y) (n : Y ⟶ Z) :
    castHom hX hY m ≫ castHom hY hZ n = castHom hX hZ (m ≫ n) := by
  subst hX; subst hY; subst hZ; rfl

/-- A functor commutes with transport: mapping a transported morphism equals
    transporting the mapped morphism (along the image object-equalities). -/
theorem map_castHom {𝒜 𝒝 : Type w} [Cat.{w} 𝒜] [Cat.{w} 𝒝] (T : 𝒜 → 𝒝) [hT : Functor T]
    {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) :
    hT.map (castHom hX hY m) = castHom (congrArg T hX) (congrArg T hY) (hT.map m) := by
  subst hX; subst hY; rfl

/-- A transport is heterogeneously equal to the morphism it transports. -/
theorem heq_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y')
    (m : X ⟶ Y) : HEq (castHom hX hY m) m := by
  subst hX; subst hY; exact HEq.rfl

/-- Two transports of heterogeneously-equal morphisms onto the *same* objects are
    equal.  This is the cancellation the hom-colimit's `tr_trans` needs. -/
theorem castHom_heq_congr {𝒜 : Type w} [Cat.{w} 𝒜] {X1 Y1 X2 Y2 X' Y' : 𝒜}
    (h1X : X1 = X') (h1Y : Y1 = Y') (h2X : X2 = X') (h2Y : Y2 = Y')
    {m1 : X1 ⟶ Y1} {m2 : X2 ⟶ Y2} (h : HEq m1 m2) :
    castHom h1X h1Y m1 = castHom h2X h2Y m2 :=
  castHom_of_heq h1X h1Y (h.trans (heq_castHom h2X h2Y m2).symm)

/-! ## Milestone 2b — the hom-colimit for fixed representatives

  For `x : C.A i`, `y : C.A j`, a morphism in the colimit is a class in the
  directed colimit of `Hom_{A k}(F x, F y)` over common upper bounds `k`.  The
  transition `homTr` applies the transition functor and re-types along `F_trans`;
  its colimit laws hold by coherence (`refl_map`/`trans_map`) modulo the casts. -/

/-- Transition of the hom-colimit: push a morphism `F x ⟶ F y` (at upper bound `a`)
    to upper bound `b` by applying `F hab` and re-typing along `F_trans`. -/
def homTr (C : CatSystem ι D) {i j : ι} (x : C.A i) (y : C.A j) (a b : UpperBound D i j)
    (hab : D.le a.1 b.1) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) : C.F b.2.1 x ⟶ C.F b.2.2 y :=
  castHom (C.F_trans a.2.1 hab x).symm (C.F_trans a.2.2 hab y).symm ((C.functF hab).map g)

theorem homTr_refl (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a : UpperBound D i j) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homTr C x y a a (D.refl a.1) g = g := by
  unfold homTr
  exact castHom_of_heq _ _ (hC.refl_map g)

theorem homTr_trans (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a b c : UpperBound D i j) (hab : D.le a.1 b.1) (hbc : D.le b.1 c.1)
    (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homTr C x y a c (D.trans hab hbc) g = homTr C x y b c hbc (homTr C x y a b hab g) := by
  unfold homTr
  rw [map_castHom (C.F hbc) (hT := C.functF hbc), castHom_castHom]
  exact castHom_heq_congr _ _ _ _ (hC.trans_map hab hbc g)

/-- The hom-colimit system for fixed representatives `x : C.A i`, `y : C.A j`. -/
def homSystem (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j) :
    System (UpperBound D i j) (upperDirected D i j) where
  X a := C.F a.2.1 x ⟶ C.F a.2.2 y
  tr {a b} hab g := homTr C x y a b hab g
  tr_refl {a} g := homTr_refl C hC x y a g
  tr_trans {a b c} hab hbc g := homTr_trans C hC x y a b c hab hbc g

/-- Morphisms `[⟨i,x⟩] → [⟨j,y⟩]` in the colimit category (for these
    representatives): the directed colimit of `Hom_{A k}(F x, F y)` over the common
    upper bounds `k`. -/
def HomColim (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j) : Type _ :=
  Colimit (homSystem C hC x y)

/-- Include a stage-`a` morphism into the hom-colimit. -/
def homIncl (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a : UpperBound D i j) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) : HomColim C hC x y :=
  incl (homSystem C hC x y) a g

/-- The identity germ at `x : C.A i`: `id` included at the trivial upper bound. -/
def homClassId (C : CatSystem ι D) (hC : C.Coherent) {i : ι} (x : C.A i) : HomColim C hC x x :=
  homIncl C hC x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (C.F (D.refl i) x))

/-- Including a germ pushed to a higher level equals including it at the lower
    level: the hom-colimit absorbs the transition (`incl_compat` for `homSystem`).
    A building block for composition's well-definedness. -/
theorem homIncl_compat (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    {a b : UpperBound D i j} (hab : D.le a.1 b.1) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homIncl C hC x y b (homTr C x y a b hab g) = homIncl C hC x y a g :=
  incl_compat (homSystem C hC x y) hab g

/-! ## Milestone 2b — the colimit category's Hom (via chosen representatives)

  We pick a representative of each colimit object with `Quotient.out` and define a
  morphism as the hom-colimit between the chosen representatives.  This uses choice
  (acceptable: the §1.543 iteration is transfinite and uses choice anyway; a
  choice-free two-sided-germ construction is possible but far longer). -/

/-- A chosen representative `⟨i, x⟩` of a colimit object (via `Quotient.exists_rep`
    + choice; core Lean has no `Quotient.out`). -/
noncomputable def colimOut (C : CatSystem ι D) (p : C.Obj) : Σ i, C.A i :=
  Classical.choose (Quotient.exists_rep p)

/-- The chosen representative includes back to the object. -/
theorem colimOut_spec (C : CatSystem ι D) (p : C.Obj) :
    C.objIncl (colimOut C p).1 (colimOut C p).2 = p :=
  Classical.choose_spec (Quotient.exists_rep p)

/-- A morphism of the colimit category: the hom-colimit between the chosen
    representatives of the two objects. -/
noncomputable def colimHom (C : CatSystem ι D) (hC : C.Coherent) (p q : C.Obj) : Type _ :=
  HomColim C hC (colimOut C p).2 (colimOut C q).2

/-- The identity morphism of the colimit category. -/
noncomputable def colimId (C : CatSystem ι D) (hC : C.Coherent) (p : C.Obj) : colimHom C hC p p :=
  homClassId C hC (colimOut C p).2

/-- Raw composition of germs: push representatives `f` (level `a`) and `g` (level
    `b`) to a common level `c`, compose in `A c`, and include.  The middle objects
    match (both `F·xq` over a proof `iq ≤ c`, identified by proof-irrelevance). -/
noncomputable def homCompRaw (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr) : HomColim C hC xp xr :=
  let c := Classical.choose (D.bound a.1 b.1)
  let hac : D.le a.1 c := (Classical.choose_spec (D.bound a.1 b.1)).1
  let hbc : D.le b.1 c := (Classical.choose_spec (D.bound a.1 b.1)).2
  let aC : UpperBound D ip iq := ⟨c, D.trans a.2.1 hac, D.trans a.2.2 hac⟩
  let bC : UpperBound D iq ir := ⟨c, D.trans b.2.1 hbc, D.trans b.2.2 hbc⟩
  homIncl C hC xp xr ⟨c, D.trans a.2.1 hac, D.trans b.2.2 hbc⟩
    (homTr C xp xq a aC hac f ≫ homTr C xq xr b bC hbc g)

/-- Pushing a composite to a higher level = composing the pushed pieces.  The
    transition `F hcd` is a functor (`map_comp`), and transport distributes over
    composition (`castHom_comp`). -/
theorem homTr_comp (C : CatSystem ι D) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir) {c d : ι}
    (hpc : D.le ip c) (hqc : D.le iq c) (hrc : D.le ir c) (hcd : D.le c d)
    (f : C.F hpc xp ⟶ C.F hqc xq) (g : C.F hqc xq ⟶ C.F hrc xr) :
    homTr C xp xr ⟨c, hpc, hrc⟩ ⟨d, D.trans hpc hcd, D.trans hrc hcd⟩ hcd (f ≫ g)
      = homTr C xp xq ⟨c, hpc, hqc⟩ ⟨d, D.trans hpc hcd, D.trans hqc hcd⟩ hcd f
        ≫ homTr C xq xr ⟨c, hqc, hrc⟩ ⟨d, D.trans hqc hcd, D.trans hrc hcd⟩ hcd g := by
  unfold homTr
  dsimp only
  rw [castHom_comp, ← (C.functF hcd).map_comp]

/-- Compose germs `f` (level `a`) and `g` (level `b`) at an explicit common bound
    `e`: push both to `e` and compose there.  `homCompRaw` is this at the chosen
    bound. -/
noncomputable def compAt (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) : HomColim C hC xp xr :=
  homIncl C hC xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩
    (homTr C xp xq a ⟨e, D.trans a.2.1 hae, D.trans a.2.2 hae⟩ hae f
     ≫ homTr C xq xr b ⟨e, D.trans b.2.1 hbe, D.trans b.2.2 hbe⟩ hbe g)

/-- Composing at level `e` equals composing at any higher level `d`: push the
    whole composite up (`homTr_comp` + `homTr_trans`), then `homIncl_compat`. -/
theorem compAt_mono (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    {e d : ι} (hae : D.le a.1 e) (hbe : D.le b.1 e) (hed : D.le e d) :
    compAt C hC xp xq xr a f b g e hae hbe
      = compAt C hC xp xq xr a f b g d (D.trans hae hed) (D.trans hbe hed) := by
  have hpe : D.le ip e := D.trans a.2.1 hae
  have hqe : D.le iq e := D.trans a.2.2 hae
  have hre : D.le ir e := D.trans b.2.2 hbe
  symm
  unfold compAt
  rw [homTr_trans C hC xp xq a ⟨e, hpe, hqe⟩
        ⟨d, D.trans a.2.1 (D.trans hae hed), D.trans a.2.2 (D.trans hae hed)⟩ hae hed f,
      homTr_trans C hC xq xr b ⟨e, hqe, hre⟩
        ⟨d, D.trans b.2.1 (D.trans hbe hed), D.trans b.2.2 (D.trans hbe hed)⟩ hbe hed g,
      ← homTr_comp C xp xq xr hpe hqe hre hed
        (homTr C xp xq a ⟨e, hpe, hqe⟩ hae f) (homTr C xq xr b ⟨e, hqe, hre⟩ hbe g),
      homIncl_compat]

end Freyd.Colim
