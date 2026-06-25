/-
  Freyd & Scedrov, *Categories and Allegories* §1.723, §2.227, §2.331.

  FRAME / LOCALE foundation.

  A FRAME (= complete Heyting algebra) is a complete lattice in which finite
  meets distribute over arbitrary joins.  Every frame is a Heyting algebra
  (§1.723): define  a → b := sSup {c | a ⊓ c ≤ b}  and prove the adjunction
  c ≤ a → b ↔ a ⊓ c ≤ b.

  The canonical example: for a topological space X, the lattice O(X) of open
  sets (modelled here as a predicate  IsOpen : (X → Prop) → Prop) is a frame
  (arbitrary unions and finite intersections of opens are open).

  A frame homomorphism preserves finite meets and arbitrary joins.

  The sheaf / O(X)-valued-set content of §2.227/§2.331 requires sheaf
  infrastructure not yet in the repo; those goals are recorded as
  precise  -- BOOK §  TODO comments below.

  Build target: lake build Fredy.Locale
  Axioms (post-build): propext, Classical.choice, Quot.sound only.
-/

import Fredy.S1_72   -- HeytingPoset, HeytingAlgebra, Locale (subobject-based)

open Freyd

universe u

namespace Freyd

/-! ## §1.723 Frame (self-contained, not subobject-based)

  A FRAME is a complete lattice with finite-meet / arbitrary-join
  distributivity.  We give it its own bundled structure (not the
  Subobject-based `Locale` of S1_72) so that concrete carriers such
  as `Opens X` can instantiate it directly. -/

/-- A FRAME: complete lattice in which `a ⊓ (⨆ S) = ⨆ {a ⊓ s | s ∈ S}`. -/
structure Frame where
  /-- Carrier set. -/
  carrier  : Type u
  /-- Partial order. -/
  le       : carrier → carrier → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- Anti-symmetry (needed to state equalities like `a = b` from `a ≤ b ∧ b ≤ a`). -/
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- Top element. -/
  top   : carrier
  le_top : ∀ a, le a top
  /-- Bottom element. -/
  bot   : carrier
  bot_le : ∀ a, le bot a
  /-- Binary meet (∧). -/
  meet          : carrier → carrier → carrier
  meet_le_left  : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet       : ∀ {a b c}, le c a → le c b → le c (meet a b)
  /-- Arbitrary join (⨆). -/
  sSup   : (carrier → Prop) → carrier
  le_sSup : ∀ (S : carrier → Prop) a, S a → le a (sSup S)
  sSup_le : ∀ (S : carrier → Prop) b, (∀ a, S a → le a b) → le (sSup S) b
  /-- **Frame distributivity**: `a ⊓ (⨆ S) = ⨆ {a ⊓ s | s ∈ S}`. -/
  meet_sSup_distrib : ∀ (a : carrier) (S : carrier → Prop),
    meet a (sSup S) = sSup (fun x => ∃ s, S s ∧ x = meet a s)

namespace Frame

variable (F : Frame.{u})

/-! ### Basic order facts -/

theorem le_refl' (a : F.carrier) : F.le a a := F.le_refl a

theorem le_antisymm' {a b : F.carrier} (h1 : F.le a b) (h2 : F.le b a) : a = b :=
  F.le_antisymm h1 h2

/-- `sSup ∅ = bot` (join of empty family = bottom). -/
theorem sSup_empty : F.sSup (fun _ => False) = F.bot :=
  F.le_antisymm
    (F.sSup_le _ _ (fun _ h => h.elim))
    (F.bot_le _)

/-- `sSup {a} = a`. -/
theorem sSup_singleton (a : F.carrier) : F.sSup (fun x => x = a) = a :=
  F.le_antisymm
    (F.sSup_le _ _ (fun _ h => h ▸ F.le_refl _))
    (F.le_sSup _ a rfl)

/-- Binary join via sSup. -/
def join (a b : F.carrier) : F.carrier :=
  F.sSup (fun x => x = a ∨ x = b)

theorem le_join_left (a b : F.carrier) : F.le a (F.join a b) :=
  F.le_sSup _ a (Or.inl rfl)

theorem le_join_right (a b : F.carrier) : F.le b (F.join a b) :=
  F.le_sSup _ b (Or.inr rfl)

theorem join_le {a b c : F.carrier} (ha : F.le a c) (hb : F.le b c) : F.le (F.join a b) c :=
  F.sSup_le _ c (fun _ h => h.elim (· ▸ ha) (· ▸ hb))

/-! ### Derived meets: top and meet are correct -/

/-- `meet a top = a`. -/
theorem meet_top (a : F.carrier) : F.meet a F.top = a :=
  F.le_antisymm (F.meet_le_left a F.top)
    (F.le_meet (F.le_refl _) (F.le_top _))

/-- `meet a bot = bot`. -/
theorem meet_bot (a : F.carrier) : F.meet a F.bot = F.bot :=
  F.le_antisymm (F.meet_le_right a F.bot) (F.bot_le _)

/-- `sSup` of the whole carrier = top. -/
theorem sSup_univ : F.sSup (fun _ => True) = F.top :=
  F.le_antisymm (F.sSup_le _ _ (fun _ _ => F.le_top _))
    (F.le_sSup _ F.top trivial)

/-! ### §1.723 Frame ⟹ Heyting algebra

  Define `a → b := sSup {c | a ⊓ c ≤ b}` and prove the adjunction
  `c ≤ a → b ↔ a ⊓ c ≤ b`. -/

/-- Heyting implication derived from frame structure: `a → b = ⨆ {c | a ⊓ c ≤ b}`. -/
noncomputable def himp (a b : F.carrier) : F.carrier :=
  F.sSup (fun c => F.le (F.meet a c) b)

/-- **Adjunction** `c ≤ (a → b) ↔ a ⊓ c ≤ b`  (§1.723). -/
theorem himp_adjunction (a b c : F.carrier) :
    F.le c (F.himp a b) ↔ F.le (F.meet a c) b := by
  constructor
  · -- c ≤ ⨆{z | a⊓z ≤ b} → a ⊓ c ≤ b
    -- By distributivity: a ⊓ (⨆{z | a⊓z≤b}) = ⨆{a⊓z | a⊓z≤b} ≤ b
    intro hc
    -- a ⊓ c ≤ a ⊓ (⨆{z | a⊓z≤b})
    have hmono : F.le (F.meet a c) (F.meet a (F.himp a b)) :=
      F.le_meet (F.meet_le_left a c)
        (F.le_trans (F.meet_le_right a c) hc)
    -- By distributivity a ⊓ (⨆{z | a⊓z≤b}) = ⨆{a⊓z | a⊓z≤b}
    have hdist := F.meet_sSup_distrib a (fun c => F.le (F.meet a c) b)
    -- ⨆{a⊓z | a⊓z≤b} ≤ b: each generator a⊓z satisfies a⊓z ≤ b
    have hle : F.le (F.sSup (fun x => ∃ s, F.le (F.meet a s) b ∧ x = F.meet a s)) b :=
      F.sSup_le _ b (fun x ⟨s, hs, hx⟩ => hx ▸ hs)
    exact F.le_trans hmono (hdist ▸ hle)
  · -- a ⊓ c ≤ b → c ≤ ⨆{z | a⊓z≤b}  (c itself is a witness)
    intro hac
    exact F.le_sSup (fun z => F.le (F.meet a z) b) c hac

/-- Modus ponens: `a ⊓ (a → b) ≤ b`. -/
theorem himp_mp (a b : F.carrier) : F.le (F.meet a (F.himp a b)) b :=
  (F.himp_adjunction a b (F.himp a b)).mp (F.le_refl _)

/-- `a → b` is covariant in `b`. -/
theorem himp_mono_right {a b c : F.carrier} (h : F.le b c) :
    F.le (F.himp a b) (F.himp a c) :=
  (F.himp_adjunction a c _).mpr (F.le_trans (F.himp_mp a b) h)

/-- `a → b` is contravariant in `a`. -/
theorem himp_mono_left_contra {a a' b : F.carrier} (h : F.le a' a) :
    F.le (F.himp a b) (F.himp a' b) :=
  (F.himp_adjunction a' b _).mpr
    (F.le_trans (F.le_meet
      (F.le_trans (F.meet_le_left _ _) h)
      (F.meet_le_right _ _))
      (F.himp_mp a b))

/-! ### Frame as HeytingPoset

  Every Frame gives a `HeytingPoset` (S1_72 definition), bridging to the
  existing Heyting algebra development. -/

/-- Every Frame (at universe 0) gives a `HeytingPoset`. -/
noncomputable def toHeytingPoset (F : Frame.{0}) : HeytingPoset where
  carrier       := F.carrier
  le            := F.le
  le_refl       := F.le_refl
  le_trans      := @F.le_trans
  top           := F.top
  top_le        := F.le_top
  bot           := F.bot
  bot_le        := F.bot_le
  meet          := F.meet
  meet_le_left  := F.meet_le_left
  meet_le_right := F.meet_le_right
  le_meet       := @F.le_meet
  join          := F.join
  le_join_left  := F.le_join_left
  le_join_right := F.le_join_right
  join_le       := @F.join_le
  imp           := F.himp
  imp_adj       := F.himp_adjunction

end Frame

/-! ## Frame homomorphisms

  A FRAME HOMOMORPHISM f : F → G preserves:
  - finite meets: top and binary meet,
  - arbitrary joins: `sSup`.
  These are the morphisms of the category of frames / locales. -/

/-- A FRAME HOMOMORPHISM between two frames. -/
structure FrameHom (F G : Frame.{u}) where
  map : F.carrier → G.carrier
  /-- Preserves top. -/
  map_top : map F.top = G.top
  /-- Preserves binary meet. -/
  map_meet : ∀ a b, map (F.meet a b) = G.meet (map a) (map b)
  /-- Preserves arbitrary joins. -/
  map_sSup : ∀ (S : F.carrier → Prop),
    map (F.sSup S) = G.sSup (fun y => ∃ x, S x ∧ y = map x)

namespace FrameHom

variable {F G H : Frame.{u}}

/-- A frame hom is order-preserving. -/
theorem map_mono (f : FrameHom F G) {a b : F.carrier} (h : F.le a b) :
    G.le (f.map a) (f.map b) := by
  -- a ≤ b iff a = a ⊓ b (in the frame order)
  -- f(a) = f(a⊓b) = f(a)⊓f(b) ≤ f(b)
  have hab : F.meet a b = a :=
    F.le_antisymm (F.meet_le_left a b) (F.le_meet (F.le_refl _) h)
  have : G.meet (f.map a) (f.map b) = f.map a := by
    rw [← f.map_meet, hab]
  exact this ▸ G.meet_le_right (f.map a) (f.map b)

/-- Preserves bottom (= sSup of empty family). -/
theorem map_bot (f : FrameHom F G) : f.map F.bot = G.bot := by
  have h1 : F.bot = F.sSup (fun _ : F.carrier => False) :=
    (Frame.sSup_empty F).symm
  rw [h1, f.map_sSup]
  -- G.sSup (fun y => ∃ x, False ∧ y = f(x)) = G.sSup (fun _ => False) = G.bot
  have : (fun y : G.carrier => ∃ x : F.carrier, False ∧ y = f.map x) = (fun _ => False) :=
    funext (fun _ => propext ⟨fun ⟨_, h, _⟩ => h, False.elim⟩)
  rw [this, Frame.sSup_empty]

/-- Identity frame hom. -/
def id (F : Frame.{u}) : FrameHom F F where
  map := fun x => x
  map_top := rfl
  map_meet := fun _ _ => rfl
  map_sSup := fun S => by
    apply F.le_antisymm
    · exact F.sSup_le _ _ (fun x hx => F.le_sSup _ x ⟨x, hx, rfl⟩)
    · exact F.sSup_le _ _ (fun _ ⟨x, hx, hyx⟩ => hyx ▸ F.le_sSup _ x hx)

/-- Composition of frame homs. -/
def comp (g : FrameHom G H) (f : FrameHom F G) : FrameHom F H where
  map := g.map ∘ f.map
  map_top := by simp [Function.comp, f.map_top, g.map_top]
  map_meet := fun a b => by simp [Function.comp, f.map_meet, g.map_meet]
  map_sSup := fun S => by
    simp only [Function.comp]
    -- expand g(f(sSup S)) step by step
    rw [f.map_sSup]
    -- now: g.map (G.sSup (fun y => ∃ x, S x ∧ y = f.map x))
    rw [g.map_sSup]
    -- now: H.sSup (fun y => ∃ z, (∃ x, S x ∧ z = f.map x) ∧ y = g.map z)
    -- = H.sSup (fun y => ∃ x, S x ∧ y = g.map (f.map x))
    apply H.le_antisymm
    · apply H.sSup_le
      intro y ⟨z, ⟨x, hx, hzx⟩, hyz⟩
      exact H.le_sSup _ y ⟨x, hx, hyz ▸ hzx ▸ rfl⟩
    · apply H.sSup_le
      intro y ⟨x, hx, hyx⟩
      exact H.le_sSup _ y ⟨f.map x, ⟨x, hx, rfl⟩, hyx⟩

end FrameHom

/-! ## Opens X: the frame of open sets of a topological space

  We model a topology on `X` as a predicate
    `IsOpen : (X → Prop) → Prop`
  satisfying the usual axioms.  The opens form a frame O(X).

  Note: we use `(X → Prop)` as the type of subsets of X (characteristic
  functions), which is definitionally the powerset `Set X`. -/

/-- A TOPOLOGY on X: a predicate on subsets specifying which are open.
    Axioms follow Freyd's convention: unary/binary are the special cases of
    the arbitrary ones. -/
structure Topology (X : Type u) where
  /-- Predicate: which subsets of X are open. -/
  IsOpen     : (X → Prop) → Prop
  /-- Whole space is open. -/
  isOpen_top : IsOpen (fun _ => True)
  /-- Empty set is open. -/
  isOpen_bot : IsOpen (fun _ => False)
  /-- Arbitrary unions of opens are open:
      if every member of a family is open, so is their union. -/
  isOpen_sUnion : ∀ (F : (X → Prop) → Prop),
    (∀ U, F U → IsOpen U) → IsOpen (fun x => ∃ U, F U ∧ U x)
  /-- Binary intersection of opens is open. -/
  isOpen_inter : ∀ {U V : X → Prop}, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)

namespace Topology

variable {X : Type u} (τ : Topology X)

/-- An open set of `(X, τ)`: a subset `U : X → Prop` with `τ.IsOpen U`. -/
def Opens := { U : X → Prop // τ.IsOpen U }

namespace Opens

variable {τ : Topology X}

/-- Underlying set of an open. -/
def set (U : τ.Opens) : X → Prop := U.val

/-- Subset order on opens: `U ≤ V` iff `U ⊆ V`. -/
def le (U V : τ.Opens) : Prop := ∀ x, U.val x → V.val x

theorem le_refl (U : τ.Opens) : le U U := fun _ hx => hx

theorem le_trans {U V W : τ.Opens} (h1 : le U V) (h2 : le V W) : le U W :=
  fun x hx => h2 x (h1 x hx)

theorem le_antisymm {U V : τ.Opens} (h1 : le U V) (h2 : le V U) : U = V :=
  Subtype.ext (funext (fun x => propext ⟨h1 x, h2 x⟩))

/-- Top open: the whole space. -/
def top : τ.Opens := ⟨fun _ => True, τ.isOpen_top⟩

/-- Bottom open: the empty set. -/
def bot : τ.Opens := ⟨fun _ => False, τ.isOpen_bot⟩

theorem le_top (U : τ.Opens) : le U top := fun _ _ => trivial

theorem bot_le (U : τ.Opens) : le bot U := fun _ h => h.elim

/-- Binary meet: intersection of two opens. -/
def meet (U V : τ.Opens) : τ.Opens :=
  ⟨fun x => U.val x ∧ V.val x, τ.isOpen_inter U.property V.property⟩

theorem meet_le_left (U V : τ.Opens) : le (meet U V) U := fun _ ⟨hu, _⟩ => hu

theorem meet_le_right (U V : τ.Opens) : le (meet U V) V := fun _ ⟨_, hv⟩ => hv

theorem le_meet {U V W : τ.Opens} (h1 : le W U) (h2 : le W V) : le W (meet U V) :=
  fun x hx => ⟨h1 x hx, h2 x hx⟩

/-- Arbitrary join: union of a family of opens.
    The union of an arbitrary family of opens is open by `isOpen_sUnion`. -/
def sSup (S : τ.Opens → Prop) : τ.Opens :=
  ⟨fun x => ∃ U : τ.Opens, S U ∧ U.val x,
   by
     -- rewrite as a union over the set-valued family indexed by (V.val | S V)
     have : (fun x => ∃ U : τ.Opens, S U ∧ U.val x) =
            (fun x => ∃ U : X → Prop, (∃ V : τ.Opens, S V ∧ U = V.val) ∧ U x) :=
       funext (fun x => propext
         ⟨fun ⟨V, hV, hvx⟩ => ⟨V.val, ⟨V, hV, rfl⟩, hvx⟩,
          fun ⟨U, ⟨V, hV, hUV⟩, hux⟩ => ⟨V, hV, hUV ▸ hux⟩⟩)
     rw [this]
     exact τ.isOpen_sUnion _ (fun U ⟨V, _, hUV⟩ => hUV ▸ V.property)⟩

theorem le_sSup (S : τ.Opens → Prop) (U : τ.Opens) (hU : S U) :
    le U (sSup S) := fun x hx => ⟨U, hU, hx⟩

theorem sSup_le (S : τ.Opens → Prop) (V : τ.Opens) (h : ∀ U, S U → le U V) :
    le (sSup S) V := fun x ⟨U, hU, hx⟩ => h U hU x hx

/-- Frame distributivity: `meet U (sSup S) = sSup {meet U V | V ∈ S}`.
    Proof: pointwise propositional logic (each side is `U x ∧ (∃ V ∈ S, V x)`
    vs `∃ V ∈ S, U x ∧ V x`), which are logically equivalent. -/
theorem meet_sSup_distrib (U : τ.Opens) (S : τ.Opens → Prop) :
    meet U (sSup S) = sSup (fun W => ∃ V, S V ∧ W = meet U V) := by
  apply le_antisymm
  · intro x ⟨hux, W, hW, hwx⟩
    exact ⟨meet U W, ⟨W, hW, rfl⟩, hux, hwx⟩
  · intro x ⟨W, ⟨V, hV, hWV⟩, hwx⟩
    exact ⟨hWV ▸ hwx |>.1, V, hV, hWV ▸ hwx |>.2⟩

end Opens

/-- **O(X) is a Frame** (§1.723 / book §2.227 context).
    The frame of opens of a topological space. -/
def opensFrame (τ : Topology X) : Frame.{u} where
  carrier := τ.Opens
  le      := Opens.le
  le_refl := Opens.le_refl
  le_trans := @Opens.le_trans X τ
  le_antisymm := @Opens.le_antisymm X τ
  top    := Opens.top
  le_top := Opens.le_top
  bot    := Opens.bot
  bot_le := Opens.bot_le
  meet   := Opens.meet
  meet_le_left  := Opens.meet_le_left
  meet_le_right := Opens.meet_le_right
  le_meet := @Opens.le_meet X τ
  sSup   := Opens.sSup
  le_sSup := Opens.le_sSup
  sSup_le := Opens.sSup_le
  meet_sSup_distrib := Opens.meet_sSup_distrib

end Topology

/-! ## Continuous maps induce frame homomorphisms O(Y) → O(X)

  A map `f : X → Y` is continuous (w.r.t. topologies τX, τY) if preimages
  of opens are open.  It induces a frame hom `f* : O(Y) → O(X)` by pullback:
  `f*(V) = f⁻¹(V) = {x | f(x) ∈ V}`.  Frame homs go in the OPPOSITE direction
  to continuous maps — this is the (contravariant) functor O : Top^op → Frame. -/

/-- Continuity: preimage of every open is open. -/
def IsContinuous {X Y : Type u} (τX : Topology X) (τY : Topology Y)
    (f : X → Y) : Prop :=
  ∀ V : τY.Opens, τX.IsOpen (fun x => V.val (f x))

/-- Pullback frame hom `f* : O(Y) → O(X)` induced by a continuous map `f : X → Y`. -/
def continuousMapFrameHom {X Y : Type u} {τX : Topology X} {τY : Topology Y}
    (f : X → Y) (hf : IsContinuous τX τY f) :
    FrameHom (τY.opensFrame) (τX.opensFrame) where
  map V := ⟨fun x => V.val (f x), hf V⟩
  map_top := by
    apply Subtype.ext; ext x; exact Iff.rfl
  map_meet := fun U V => by
    apply Subtype.ext; ext x; exact Iff.rfl
  map_sSup := fun S => by
    -- Goal: map (τY.opensFrame.sSup S) = τX.opensFrame.sSup (fun W => ∃ V, S V ∧ W = map V)
    -- Both sides are τX.Opens; compare their val predicates.
    apply Subtype.ext; ext x
    -- LHS.val x = (τY.opensFrame.sSup S).val (f x) = ∃ V ∈ S, V.val (f x)
    -- RHS.val x = ∃ W : τX.Opens, (∃ V ∈ S, W = map V) ∧ W.val x
    simp only [Topology.opensFrame, Topology.Opens.sSup]
    constructor
    · -- ∃ V ∈ S, V.val (f x)  →  ∃ W, (∃ V ∈ S, W = ⟨·(f·), _⟩) ∧ W.val x
      intro ⟨V, hVS, hVfx⟩
      exact ⟨⟨fun z => V.val (f z), hf V⟩, ⟨V, hVS, rfl⟩, hVfx⟩
    · -- ∃ W, (∃ V ∈ S, W = ⟨·(f·), _⟩) ∧ W.val x  →  ∃ V ∈ S, V.val (f x)
      intro ⟨W, ⟨V, hVS, hWV⟩, hWx⟩
      -- hWV : W = ⟨fun z => V.val (f z), hf V⟩; so W.val x = V.val (f x)
      have : W.val x = V.val (f x) := congrFun (congrArg Subtype.val hWV) x
      exact ⟨V, hVS, this ▸ hWx⟩

/-! ## Points of a locale / frame

  A POINT of a frame F is a frame homomorphism `p : F → Ω` where `Ω` is the
  two-element frame {⊥, ⊤} (= Prop / truth values).  Equivalently, a point is
  a completely-prime filter in F: a proper filter P such that
  `a ⊔ b ∈ P → a ∈ P ∨ b ∈ P`.

  In the representation theorem §2.227, the "points" of O(X) correspond exactly
  to the points of X (for sober spaces X).

  BOOK §2.227 TODO: The full representation theorem needs:
    (1) The sobriety condition on X (every completely prime filter is the
        neighbourhood filter of a unique point).
    (2) The locale of points Pt(F) for an abstract frame F.
    (3) The adjunction between Top (topological spaces) and Locale (frames^op).
  These require more set-theoretic infrastructure (filtersets, adjunction
  framework); we leave them as a precise TODO. -/

/-- A POINT of a frame `F`: a completely-prime filter.
    Concretely: a predicate `p : F.carrier → Prop` that is:
    - proper: `¬ p F.bot`,
    - upward-closed: `p a → F.le a b → p b`,
    - finite-meet-closed: `p F.top` and `p a → p b → p (F.meet a b)`,
    - completely-prime: `p (F.sSup S) → ∃ a, S a ∧ p a`. -/
structure FramePoint (F : Frame.{u}) where
  mem       : F.carrier → Prop
  mem_top   : mem F.top
  mem_up    : ∀ {a b}, mem a → F.le a b → mem b
  mem_meet  : ∀ {a b}, mem a → mem b → mem (F.meet a b)
  not_bot   : ¬ mem F.bot
  prime     : ∀ (S : F.carrier → Prop), mem (F.sSup S) → ∃ a, S a ∧ mem a

/-- The point of `O(X)` associated to `x : X` (principal ultrafilter at x):
    `U ∈ p_x ↔ x ∈ U`. -/
def Topology.principalPoint {X : Type u} (τ : Topology X) (x : X) :
    FramePoint (τ.opensFrame) where
  mem U := U.val x
  mem_top := trivial
  mem_up hUx hle := hle x hUx
  mem_meet hUx hVx := ⟨hUx, hVx⟩
  not_bot := id
  prime S hSx := let ⟨U, hUS, hUx⟩ := hSx; ⟨U, hUS, hUx⟩

-- BOOK §2.227: Representation theorem for locales / sober spaces.
-- For a SOBER topological space X, every point of the frame O(X)
-- (= every completely-prime filter) is of the form p_x for a unique x : X.
-- This gives a bijection  Pt(O(X)) ≅ X  and an embedding Top_sober ↪ Locale^op.
-- Stating this faithfully needs:
--   (a) a definition of sobriety: every irred. closed set has a generic point,
--   (b) the bijection Pt(O(X)) → X (uses Classical.choice to pick the point),
--   (c) the topology on Pt(F) for a general frame F (= Pt-construction).
-- These are left as a precise TODO; no sorry-bearing stubs are emitted.

-- BOOK §2.331: O(X)-valued sets (sheaves on O(X)).
-- The category of sheaves Sh(O(X)) = Set^{O(X)^op} satisfying the
-- sheaf condition (matching families glue uniquely) is a logos.
-- Stating this faithfully needs:
--   (a) the presheaf category Psh(F) = F^op → Set,
--   (b) the sheaf condition: every matching family has a unique amalgamation,
--   (c) `Sh(O(X))` is a logos (localic topos).
-- This depends on the general sheaf/presheaf infrastructure not yet in the repo.
-- Left as a precise TODO.

-- BOOK §1.74x: Representation theorems via opens.
-- §1.741: Every logos can be embedded in a logos of the form Sh(O(X)).
-- §1.742: Countable logos embeds in Sh(O(ℝ)).
-- These require the focal representation + sheaf machinery; left as TODO.

end Freyd
