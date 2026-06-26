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
def IsContinuousMap {X Y : Type u} (τX : Topology X) (τY : Topology Y)
    (f : X → Y) : Prop :=
  ∀ V : τY.Opens, τX.IsOpen (fun x => V.val (f x))

/-- Pullback frame hom `f* : O(Y) → O(X)` induced by a continuous map `f : X → Y`. -/
def continuousMapFrameHom {X Y : Type u} {τX : Topology X} {τY : Topology Y}
    (f : X → Y) (hf : IsContinuousMap τX τY f) :
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

/-! ## §2.16(12) F-valued sets (Ω-sets over a frame)

  Freyd §2.16(12): the allegory obtained by splitting the symmetric idempotents
  of the Z-valued-relation allegory.  An **F-valued set** is a pair `⟨I, E⟩`
  where `E : I × I → F` is:
  - symmetric:   `E i j = E j i`
  - transitive:  `E i j ∧ E j k ≤ E i k`

  These are the objects of the **allegory of F-valued sets** OSet(F).
  A **morphism** `T : ⟨I,E⟩ → ⟨J,S⟩` is an `I×J`-matrix `T : I → J → F`
  satisfying (Freyd §2.16(12)):
  - domain bound:    `T i j ≤ E i i ∧ S j j`
  - naturality:      `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`

  Identity on `⟨I,E⟩` is `E` itself. Composition via the join:
    `(T ⊚ U) i k = ⨆ { T i j ∧ U j k | j : J }`. -/

/-- An **F-valued set** (Freyd §2.16(12)): a carrier `I` with an `F`-valued
    "equality" `E` that is symmetric and transitive. -/
structure OValuedSet (F : Frame.{u}) where
  /-- Carrier (index) set. -/
  carrier : Type u
  /-- F-valued equality: `E i j` = "extent to which i and j are equal". -/
  E : carrier → carrier → F.carrier
  /-- Symmetry: `E i j = E j i`. -/
  symm : ∀ i j, E i j = E j i
  /-- Transitivity: `E i j ∧ E j k ≤ E i k`. -/
  trans : ∀ i j k, F.le (F.meet (E i j) (E j k)) (E i k)

namespace OValuedSet

variable {F : Frame.{u}}

/-- The **extent** of `i`: `E i i`.  (Like Dom in an allegory.) -/
def extent (A : OValuedSet F) (i : A.carrier) : F.carrier := A.E i i

/-- Reflexivity of E: `E i i` is greatest lower bound of `E i j` and `E j i`. -/
theorem extent_le_self (A : OValuedSet F) (i j : A.carrier) :
    F.le (F.meet (A.E i j) (A.E j i)) (A.extent i) := by
  -- E i j ∧ E j i ≤ E i i via transitivity (j plays the middle role)
  have h := A.trans i j i
  -- meet(E i j, E j i) ≤ meet(E i j, E j i) — but we need to use symm too
  -- Actually: meet(E i j, E j i) ≤ E i i = extent i
  -- by transitivity with j: E i j ∧ E j i ≤ E i i
  have hsym : A.E j i = A.E i j := (A.symm j i).symm ▸ (A.symm i j)
  -- trans gives: meet(E i j, E j i) ≤ meet(E i j, E j i) ... actually use trans directly
  -- E i j ∧ E j i ≤ E i i via trans i j i
  exact h

/-- `E i j ≤ E i i` (domain bound): the extent of i bounds E i j. -/
theorem E_le_extent_left (A : OValuedSet F) (i j : A.carrier) :
    F.le (A.E i j) (A.extent i) := by
  -- E i j ≤ E i j ∧ E j i ≤ E i i (since E j i ≤ top trivially... need another route)
  -- Better: E i j = E j i (by symm), so E i j ∧ E j j ≤ E i j by meet_le_left,
  -- and then E i j ∧ E j j ≤ E i i hmm, let's just use trans directly:
  -- E i j ≤ meet(E i j, E j i) is NOT true in general since meet is GLB.
  -- We need: E i j ≤ E i i.
  -- Trick: by trans i j i: meet(E i j, E j i) ≤ E i i
  -- and E i j = E j i (symm), so meet(E i j, E i j) = E i j ≤ E i i
  have hmeet_self : F.meet (A.E i j) (A.E i j) = A.E i j :=
    F.le_antisymm (F.meet_le_left _ _)
      (F.le_meet (F.le_refl _) (F.le_refl _))
  have hsym : A.E j i = A.E i j := by rw [A.symm]
  have htrans := A.trans i j i
  rw [hsym] at htrans
  -- htrans : meet(E i j, E i j) ≤ E i i
  rw [hmeet_self] at htrans
  exact htrans

/-- `E i j ≤ E j j` (codomain bound). -/
theorem E_le_extent_right (A : OValuedSet F) (i j : A.carrier) :
    F.le (A.E i j) (A.extent j) := by
  have := A.E_le_extent_left j i
  rw [A.symm j i] at this
  exact this

end OValuedSet

/-- A **morphism of F-valued sets** `T : ⟨I,E⟩ → ⟨J,S⟩` is an `I×J`-matrix
    of F-values satisfying the source-target predicate of Freyd §2.16(12):
    (i)  `T i j ≤ E i i ∧ S j j`  (bounded by extents),
    (ii) `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`  (naturality / equivariance). -/
@[ext]
structure OSetHom {F : Frame.{u}} (A B : OValuedSet F) where
  /-- The underlying F-valued relation. -/
  rel : A.carrier → B.carrier → F.carrier
  /-- Domain bound: `T i j ≤ E i i`. -/
  dom_bound : ∀ i j, F.le (rel i j) (A.E i i)
  /-- Codomain bound: `T i j ≤ S j j`. -/
  cod_bound : ∀ i j, F.le (rel i j) (B.E j j)
  /-- Naturality: `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`. -/
  natural : ∀ i i' j j',
    F.le (F.meet (F.meet (A.E i i') (B.E j j')) (rel i j)) (rel i' j')

namespace OSetHom

variable {F : Frame.{u}} {A B C : OValuedSet F}

/-- Combine the two bound conditions. -/
theorem bound (f : OSetHom A B) (i : A.carrier) (j : B.carrier) :
    F.le (f.rel i j) (F.meet (A.E i i) (B.E j j)) :=
  F.le_meet (f.dom_bound i j) (f.cod_bound i j)

/-- **Identity morphism** on A: `id_A i j = E_A i j`.
    Domain bound: `E i j ≤ E i i` (by OValuedSet.E_le_extent_left).
    Codomain bound: `E i j ≤ E j j` (by E_le_extent_right).
    Naturality: `E i i' ∧ E j j' ∧ E i j ≤ E i' j'`
    — via transitivity twice (i—i'—j' and i—j—j'). -/
def id (A : OValuedSet F) : OSetHom A A where
  rel    := A.E
  dom_bound := A.E_le_extent_left
  cod_bound := A.E_le_extent_right
  natural := fun i i' j j' => by
    -- Goal: meet(meet(E i i', E j j'), E i j) ≤ E i' j'
    -- Strategy: use transitivity twice
    -- E i i' ∧ E i j → (use trans) ≤ E i' j (via symmetric: E i' i ∧ E i j ≤ E i' j)
    -- Actually easier: meet(E i i', E j j') ∧ E i j
    --   ≤ E i i' ∧ E i j ≤ ... hmm need associativity
    -- Use: meet(A, B) ∧ C ≤ A; and separately ≤ B
    -- We want: E i i' ∧ E i j ≤ E i' j  (via sym+trans: E i' i ∧ E i j ≤ E i' j)
    -- then: E i' j ∧ E j j' ≤ E i' j'   (direct from trans)
    -- So: meet(meet(E i i', E j j'), E i j)
    --   ≤ E i i' ∧ E i j  and  ≤ E j j' ∧ E i' j  ... need to chain
    -- Full chain: let's extract components
    have hEij_i : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E i i') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    have hEij_j : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E j j') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _)
    have hEij_ij : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E i j) :=
      F.meet_le_right _ _
    -- Step 1: E i i' ∧ E i j ≤ E i' j
    --   = E i' i (by symm) ... trans: E i' i ∧ E i j ≤ E i' j
    have step1 : F.le (F.meet (A.E i i') (A.E i j)) (A.E i' j) := by
      have hsym : A.E i i' = A.E i' i := A.symm i i'
      rw [hsym]
      exact A.trans i' i j
    -- Step 2: E i' j ∧ E j j' ≤ E i' j'
    have step2 : F.le (F.meet (A.E i' j) (A.E j j')) (A.E i' j') :=
      A.trans i' j j'
    -- Chain: our term ≤ E i' j (via step1 from components)
    have hstep1_app : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j))
        (A.E i' j) := by
      apply F.le_trans _ step1
      exact F.le_meet hEij_i hEij_ij
    -- and ≤ E j j'
    have hstep2_app : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j))
        (A.E i' j') := by
      apply F.le_trans _ step2
      exact F.le_meet hstep1_app hEij_j
    exact hstep2_app

/-- **Composition** of OSetHom: `(f ⊚ g) i k = ⨆ { f i j ∧ g j k | j : B }`. -/
def comp (f : OSetHom A B) (g : OSetHom B C) : OSetHom A C where
  rel i k := F.sSup (fun v => ∃ j : B.carrier, v = F.meet (f.rel i j) (g.rel j k))
  dom_bound i k := by
    apply F.sSup_le
    intro v ⟨j, hv⟩
    rw [hv]
    exact F.le_trans (F.meet_le_left _ _) (f.dom_bound i j)
  cod_bound i k := by
    apply F.sSup_le
    intro v ⟨j, hv⟩
    rw [hv]
    exact F.le_trans (F.meet_le_right _ _) (g.cod_bound j k)
  natural i i' k k' := by
    -- Goal: meet(meet(A.E i i', C.E k k'), sSup{f(i,j)∧g(j,k) | j}) ≤ sSup{f(i',j)∧g(j,k') | j}
    -- Use meet_sSup_distrib to push meet inside the sup, then apply naturality of f and g
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨j, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    -- v = meet(meet(A.E i i', C.E k k'), meet(f.rel i j, g.rel j k))
    -- Need: ≤ sSup{f(i',j')∧g(j',k') | j'}
    -- Use naturality of f at (i,i',j,j) and of g at (j,j,k,k')
    -- First: meet(A.E i i', f.rel i j) ≤ f.rel i' j
    --   from f.natural i i' j j with B.E j j ≥ f.rel i j (cod_bound)
    -- Exploit: meet(A.E i i', C.E k k') ∧ meet(f.rel i j, g.rel j k)
    --        ≤ f.rel i' j ∧ g.rel j k'  then ≤ sSup via le_sSup with witness j
    have hAii' : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (A.E i i') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    have hCkk' : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (C.E k k') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _)
    have hfij : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (f.rel i j) :=
      F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _)
    have hgjk : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (g.rel j k) :=
      F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _)
    -- Apply f.natural i i' j j: meet(meet(A.E i i', B.E j j), f.rel i j) ≤ f.rel i' j
    -- We have B.E j j ≥ f.rel i j (cod_bound), so meet(A.E i i', f.rel i j) ≤ f.rel i' j
    have hfnat : F.le (F.meet (F.meet (A.E i i') (B.E j j)) (f.rel i j)) (f.rel i' j) :=
      f.natural i i' j j
    -- Our term → meet(A.E i i', f.rel i j): need to get B.E j j in there
    have hBjj_f : F.le (f.rel i j) (B.E j j) := f.cod_bound i j
    have hf_app : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (f.rel i' j) := by
      apply F.le_trans _ hfnat
      exact F.le_meet (F.le_meet hAii' (F.le_trans hfij hBjj_f)) hfij
    -- Apply g.natural j j k k': meet(meet(B.E j j, C.E k k'), g.rel j k) ≤ g.rel j k'
    have hgnat : F.le (F.meet (F.meet (B.E j j) (C.E k k')) (g.rel j k)) (g.rel j k') :=
      g.natural j j k k'
    -- B.E j j ≥ g.rel j k (dom_bound)
    have hBjj_g : F.le (g.rel j k) (B.E j j) := g.dom_bound j k
    have hg_app : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (g.rel j k') := by
      apply F.le_trans _ hgnat
      exact F.le_meet (F.le_meet (F.le_trans hgjk hBjj_g) hCkk') hgjk
    -- Combine: term ≤ f.rel i' j ∧ g.rel j k' ≤ sSup{f(i',j')∧g(j',k')|j'}
    apply F.le_trans (F.le_meet hf_app hg_app)
    exact F.le_sSup _ _ ⟨j, rfl⟩

end OSetHom

/-! ### The category OSet(F)

  Objects: OValuedSet F.
  Morphisms: OSetHom A B.
  Identity and composition are defined above; associativity holds because
  ⨆ of a ⨆ over j equals ⨆ over the combined index. -/

/-- OSet(F) identity morphism. -/
def oset_id {F : Frame.{u}} (A : OValuedSet F) : OSetHom A A := OSetHom.id A

/-- OSet(F) composition. -/
def oset_comp {F : Frame.{u}} {A B C : OValuedSet F}
    (f : OSetHom A B) (g : OSetHom B C) : OSetHom A C := OSetHom.comp f g

/-- Identity is left unit: `id ⊚ f = f`.
    Proof: `(id ⊚ f) i k = ⨆ { E i j ∧ f j k | j } = f i k`. -/
theorem oset_id_comp {F : Frame.{u}} {A B : OValuedSet F} (f : OSetHom A B) :
    oset_comp (oset_id A) f = f := by
  ext i k  -- structural equality on OSetHom is via rel
  simp only [oset_comp, oset_id, OSetHom.comp, OSetHom.id]
  -- Goal: F.sSup (fun v => ∃ j, v = F.meet (A.E i j) (f.rel j k)) = f.rel i k
  apply F.le_antisymm
  · -- ⊢ sSup{E i j ∧ f j k | j} ≤ f i k
    apply F.sSup_le
    intro v ⟨j, hv⟩; rw [hv]
    -- E i j ∧ f j k ≤ f i k  by naturality of f at (j, i, k, k)
    -- f.natural j i k k: meet(meet(A.E j i, B.E k k), f.rel j k) ≤ f.rel i k
    have hnat := f.natural j i k k
    -- A.E j i = A.E i j by symm
    -- B.E k k ≥ f.rel j k by cod_bound
    have hBkk : F.le (f.rel j k) (B.E k k) := f.cod_bound j k
    have hsym : A.E j i = A.E i j := A.symm j i
    apply F.le_trans _ hnat
    rw [← hsym]
    exact F.le_meet (F.le_meet (F.meet_le_left _ _)
      (F.le_trans (F.meet_le_right _ _) hBkk))
      (F.meet_le_right _ _)
  · -- ⊢ f i k ≤ sSup{E i j ∧ f j k | j}
    -- witness j = i: E i i ∧ f i k ≥ f i k  (since f i k ≤ E i i by dom_bound)
    apply F.le_trans _ (F.le_sSup _ _ ⟨i, rfl⟩)
    -- ⊢ f.rel i k ≤ F.meet (A.E i i) (f.rel i k)
    exact F.le_meet (f.dom_bound i k) (F.le_refl _)

/-- Identity is right unit: `f ⊚ id = f`. -/
theorem oset_comp_id {F : Frame.{u}} {A B : OValuedSet F} (f : OSetHom A B) :
    oset_comp f (oset_id B) = f := by
  ext i k
  simp only [oset_comp, oset_id, OSetHom.comp, OSetHom.id]
  apply F.le_antisymm
  · apply F.sSup_le
    intro v ⟨j, hv⟩; rw [hv]
    -- f i j ∧ E j k ≤ f i k  by naturality of f at (i, i, j, k)
    -- f.natural i i j k: meet(meet(A.E i i, B.E j k), f.rel i j) ≤ f.rel i k
    have hnat := f.natural i i j k
    have hAii : F.le (f.rel i j) (A.E i i) := f.dom_bound i j
    apply F.le_trans _ hnat
    exact F.le_meet (F.le_meet (F.le_trans (F.meet_le_left _ _) hAii)
      (F.meet_le_right _ _))
      (F.meet_le_left _ _)
  · apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
    -- goal: f.rel i k ≤ meet (f.rel i k) (B.E k k)
    exact F.le_meet (F.le_refl _) (f.cod_bound i k)

/-- Auxiliary: `sSup S ∧ a = a ∧ sSup S` (meet commutativity for sSup).
    We need this for the associativity proof because `meet_sSup_distrib` is
    `a ∧ sSup S = ...` but composition gives `sSup S ∧ h`. -/
private theorem Frame.sSup_meet_comm {F : Frame.{u}} (a : F.carrier)
    (S : F.carrier → Prop) :
    F.meet (F.sSup S) a = F.meet a (F.sSup S) :=
  F.le_antisymm
    (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
    (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))

/-- Auxiliary: meet distributes over sSup on the right. -/
private theorem Frame.sSup_meet_distrib {F : Frame.{u}} (S : F.carrier → Prop) (b : F.carrier) :
    F.meet (F.sSup S) b = F.sSup (fun x => ∃ s, S s ∧ x = F.meet s b) := by
  rw [Frame.sSup_meet_comm, F.meet_sSup_distrib]
  -- now: sSup{b ∧ s | s ∈ S} = sSup{x | ∃ s ∈ S, x = meet s b}
  apply F.le_antisymm
  · apply F.sSup_le; intro x ⟨s, hs, hx⟩
    -- hx : x = meet b s; need: ∃ s', S s' ∧ x = meet s' b
    exact F.le_sSup _ _ ⟨s, hs, hx ▸ F.le_antisymm
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))⟩
  · apply F.sSup_le; intro x ⟨s, hs, hx⟩
    -- hx : x = meet s b; need: ∃ s', S s' ∧ x = meet b s'
    exact F.le_sSup _ _ ⟨s, hs, hx ▸ F.le_antisymm
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))⟩

/-- Composition is associative: `(f ⊚ g) ⊚ h = f ⊚ (g ⊚ h)`.
    Both sides equal `⨆_{j,k} { f i j ∧ g j k ∧ h k l }`. -/
theorem oset_comp_assoc {F : Frame.{u}} {A B C D : OValuedSet F}
    (f : OSetHom A B) (g : OSetHom B C) (h : OSetHom C D) :
    oset_comp (oset_comp f g) h = oset_comp f (oset_comp g h) := by
  ext i l
  simp only [oset_comp, OSetHom.comp]
  -- LHS: sSup_k { meet(sSup_j{f i j ∧ g j k}, h k l) }
  -- RHS: sSup_j { meet(f i j, sSup_k{g j k ∧ h k l}) }
  apply F.le_antisymm
  · -- LHS ≤ RHS
    apply F.sSup_le; intro v ⟨k, hvk⟩; rw [hvk]
    -- Goal: meet(sSup_j{f i j ∧ g j k}, h k l) ≤ sSup_j{f i j ∧ sSup_k{g j k' ∧ h k' l}}
    -- Use sSup_meet_distrib to unpack the left factor
    rw [Frame.sSup_meet_distrib]
    apply F.sSup_le; intro w ⟨u, ⟨j, huj⟩, hwu⟩; rw [huj] at hwu; rw [hwu]
    -- w = meet(f i j ∧ g j k, h k l)
    apply F.le_trans _ (F.le_sSup _ _ ⟨j, rfl⟩)
    apply F.le_meet
    · exact F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    · apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
      exact F.le_meet
        (F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _))
        (F.meet_le_right _ _)
  · -- RHS ≤ LHS
    apply F.sSup_le; intro v ⟨j, hvj⟩; rw [hvj]
    -- Goal: meet(f i j, sSup_k{g j k ∧ h k l}) ≤ sSup_k{meet(sSup_j'{f i j' ∧ g j' k}, h k l)}
    rw [F.meet_sSup_distrib]
    apply F.sSup_le; intro w ⟨u, ⟨k, huk⟩, hwu⟩; rw [huk] at hwu; rw [hwu]
    -- w = meet(f i j, g j k ∧ h k l)
    apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
    apply F.le_meet
    · apply F.le_trans _ (F.le_sSup _ _ ⟨j, rfl⟩)
      exact F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))
    · exact F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _)

/-! ## The category OSet(F)

  Package the id / comp / unit / assoc proofs above into a `Cat` instance
  so that `OValuedSet F` becomes a first-class category in the repo's `Cat`
  typeclass. -/

instance osetCat (F : Frame.{u}) : Cat.{u} (OValuedSet F) where
  Hom    := OSetHom
  id     := OSetHom.id
  comp   := OSetHom.comp
  id_comp := oset_id_comp
  comp_id := oset_comp_id
  assoc  := oset_comp_assoc

/-! ## Terminal F-valued set

  The terminal object of OSet(F) is the singleton carrier `PUnit` with
  equality `E () () = F.top` (everything is "equal to itself completely").
  Any morphism into it is forced: `T i () = A.E i i` (the extent of i). -/

/-- The terminal F-valued set: carrier = `PUnit`, `E () () = F.top`.
    Transitivity: `F.top ∧ F.top ≤ F.top` by `meet_le_left`. -/
def OSetTerminal (F : Frame.{u}) : OValuedSet F where
  carrier := PUnit
  E _ _   := F.top
  symm _ _ := rfl
  trans _ _ _ := F.meet_le_left F.top F.top

/-! ## F-valued predicates (§2.227 H(Y) ingredient)

  For an F-valued set `A`, an **F-valued predicate** on `A` is a function
  `p : A.carrier → F.carrier` satisfying:
    (i)  `p i ≤ A.E i i`   (domain bound),
    (ii) `A.E i j ∧ p i ≤ p j`  (naturality / equivariance).

  The collection `OPred F A` of all such predicates is ordered pointwise:
    `p ≤ q ↔ ∀ i, F.le (p.val i) (q.val i)`.

  This is a FRAME under the pointwise frame operations of F.  The Heyting
  implication is therefore also available (F is a frame ⟹ Heyting algebra).

  In the special case A = OSetTerminal F and F = O(Y), the frame OPred F A
  recovers F itself (Prop: `osetTerminal_pred_iso_frame`).  This is the
  H(Y) of §2.227. -/

/-- An F-valued predicate on an F-valued set A. -/
structure OPred {F : Frame.{u}} (A : OValuedSet F) where
  /-- The predicate. -/
  val : A.carrier → F.carrier
  /-- Domain bound: `p i ≤ A.E i i`. -/
  dom_bound : ∀ i, F.le (val i) (A.E i i)
  /-- Naturality: `A.E i j ∧ p i ≤ p j`. -/
  natural : ∀ i j, F.le (F.meet (A.E i j) (val i)) (val j)

namespace OPred

variable {F : Frame.{u}} {A : OValuedSet F}

/-- Pointwise order on predicates. -/
def le (p q : OPred A) : Prop := ∀ i, F.le (p.val i) (q.val i)

theorem le_refl (p : OPred A) : le p p := fun i => F.le_refl _

theorem le_trans {p q r : OPred A} (hpq : le p q) (hqr : le q r) : le p r :=
  fun i => F.le_trans (hpq i) (hqr i)

theorem le_antisymm {p q : OPred A} (hpq : le p q) (hqp : le q p) : p = q := by
  cases p; cases q
  congr 1
  funext i
  exact F.le_antisymm (hpq i) (hqp i)

/-- The top predicate: `p i = A.E i i` (maximal extent). -/
def top (A : OValuedSet F) : OPred A where
  val i := A.E i i
  dom_bound i := F.le_refl _
  -- need: F.le (F.meet (A.E i j) (A.E i i)) (A.E j j)
  -- meet (E i j) (E i i) ≤ E i j ≤ E j j
  natural i j := F.le_trans (F.meet_le_left _ _) (A.E_le_extent_right i j)

/-- Bottom predicate: `p i = F.bot`. -/
def bot (A : OValuedSet F) : OPred A where
  val _ := F.bot
  dom_bound _ := F.bot_le _
  natural _ _ := F.le_trans (F.meet_le_right _ _) (F.bot_le _)

theorem le_top (p : OPred A) : le p (top A) := fun i => p.dom_bound i

theorem bot_le (p : OPred A) : le (bot A) p := fun i => F.bot_le _

/-- Pointwise meet of two predicates. -/
def meet (p q : OPred A) : OPred A where
  val i := F.meet (p.val i) (q.val i)
  dom_bound i := F.le_trans (F.meet_le_left _ _) (p.dom_bound i)
  natural i j := by
    -- A.E i j ∧ (p i ∧ q i) ≤ p j ∧ q j
    -- reorganise: (A.E i j ∧ p i) ≤ p j and (A.E i j ∧ q i) ≤ q j
    apply F.le_meet
    · exact F.le_trans (F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))) (p.natural i j)
    · exact F.le_trans (F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _))) (q.natural i j)

theorem meet_le_left (p q : OPred A) : le (meet p q) p :=
  fun i => F.meet_le_left _ _

theorem meet_le_right (p q : OPred A) : le (meet p q) q :=
  fun i => F.meet_le_right _ _

theorem le_meet {p q r : OPred A} (hpr : le r p) (hqr : le r q) : le r (meet p q) :=
  fun i => F.le_meet (hpr i) (hqr i)

/-- Pointwise arbitrary join of a family of predicates.

    For `sSup S` to be equivariant we need:
    `A.E i j ∧ (⨆_{p∈S} p i) ≤ ⨆_{p∈S} p j`.
    By frame distributivity: `A.E i j ∧ (⨆ p i) = ⨆{A.E i j ∧ p i | p∈S} ≤ ⨆{p j | p∈S}`,
    using equivariance of each `p`. -/
def sSup (S : OPred A → Prop) : OPred A where
  val i := F.sSup (fun v => ∃ p, S p ∧ v = p.val i)
  dom_bound i := F.sSup_le _ _ (fun v ⟨p, _, hv⟩ => hv ▸ p.dom_bound i)
  natural i j := by
    -- LHS: A.E i j ∧ sSup{p i | p∈S}
    -- By distributivity: = sSup{A.E i j ∧ p i | p∈S}
    -- ≤ sSup{p j | p∈S}  since each A.E i j ∧ p i ≤ p j
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨p, hpS, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    -- v = A.E i j ∧ p i; need v ≤ sSup{p j | ...}
    apply F.le_trans (p.natural i j)
    exact F.le_sSup _ _ ⟨p, hpS, rfl⟩

theorem le_sSup (S : OPred A → Prop) (p : OPred A) (hpS : S p) : le p (sSup S) :=
  fun i => F.le_sSup _ _ ⟨p, hpS, rfl⟩

theorem sSup_le (S : OPred A → Prop) (q : OPred A) (h : ∀ p, S p → le p q) :
    le (sSup S) q :=
  fun i => F.sSup_le _ _ (fun v ⟨p, hpS, hv⟩ => hv ▸ h p hpS i)

/-- Frame distributivity: `meet p (sSup S) = sSup {meet p q | q ∈ S}`. -/
theorem meet_sSup_distrib (p : OPred A) (S : OPred A → Prop) :
    meet p (sSup S) = sSup (fun r => ∃ q, S q ∧ r = meet p q) := by
  apply le_antisymm
  · intro i
    -- (meet p (sSup S)).val i = F.meet (p.val i) (sSup{q.val i | q∈S})
    -- By F.meet_sSup_distrib: = sSup{p.val i ∧ q.val i | q∈S}
    -- = sSup{(meet p q).val i | q∈S}
    simp only [meet, sSup]
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨q, hqS, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    exact F.le_sSup _ _ ⟨meet p q, ⟨q, hqS, rfl⟩, rfl⟩
  · intro i
    simp only [sSup, meet]
    apply F.sSup_le
    intro v ⟨r, ⟨q, hqS, hrpq⟩, hv⟩
    rw [hrpq] at hv; rw [hv]
    -- v = F.meet (p.val i) (q.val i); need ≤ F.meet (p.val i) (sSup{q'.val i | q'∈S})
    apply F.le_meet
    · exact F.meet_le_left _ _
    · exact F.le_trans (F.meet_le_right _ _) (F.le_sSup _ _ ⟨q, hqS, rfl⟩)

end OPred

/-- **OPred(F, A) is a Frame** (pointwise operations from F, equivariance preserved).
    This is the "H(Y)" of §2.227 when A is an O(Y)-valued set. -/
def opredFrame {F : Frame.{u}} (A : OValuedSet F) : Frame.{u} where
  carrier := OPred A
  le      := OPred.le
  le_refl := OPred.le_refl
  le_trans := @OPred.le_trans F A
  le_antisymm := @OPred.le_antisymm F A
  top     := OPred.top A
  le_top  := OPred.le_top
  bot     := OPred.bot A
  bot_le  := OPred.bot_le
  meet    := OPred.meet
  meet_le_left  := OPred.meet_le_left
  meet_le_right := OPred.meet_le_right
  le_meet := @OPred.le_meet F A
  sSup    := OPred.sSup
  le_sSup := OPred.le_sSup
  sSup_le := OPred.sSup_le
  meet_sSup_distrib := OPred.meet_sSup_distrib

/-! ### H(Y): OPred on the terminal F-valued set recovers F

  In §2.227, H(Y) is the frame of F-valued predicates on the terminal
  F-valued set (carrier = PUnit, equality = F.top).  A predicate here
  is just a function `PUnit → F.carrier`, which is the same as picking
  a single element of F (subject to bounds that are trivially satisfied).
  This gives an isomorphism of frames `OPred F (OSetTerminal F) ≅ F`.

  We make this explicit by two order-preserving maps and show they are
  inverse isomorphisms of frames. -/

/-- The isomorphism H(terminal) ≅ F:
    forward direction — evaluate at the unique point `PUnit.unit`. -/
def hTerminal_toFrame {F : Frame.{u}} (p : OPred (OSetTerminal F)) : F.carrier :=
  p.val PUnit.unit

/-- Backward direction: constant predicate `fun _ => a`. -/
def hTerminal_ofFrame {F : Frame.{u}} (a : F.carrier) : OPred (OSetTerminal F) where
  val _ := a
  dom_bound _ := F.le_top _   -- a ≤ F.top = E () ()
  natural _ _ := F.meet_le_right _ _  -- F.top ∧ a ≤ a

/-- `hTerminal_ofFrame` is a left inverse: `ofFrame (toFrame p) = p`. -/
theorem hTerminal_leftInv {F : Frame.{u}} (p : OPred (OSetTerminal F)) :
    hTerminal_ofFrame (hTerminal_toFrame p) = p := by
  cases p with
  | mk val db nat =>
    simp only [hTerminal_ofFrame, hTerminal_toFrame]
    -- congr 1 closes: the val fields are both `fun _ => val PUnit.unit`, equal by PUnit
    -- uniqueness; dom_bound/natural equal by proof irrelevance.
    congr 1

/-- `hTerminal_ofFrame` is a right inverse: `toFrame (ofFrame a) = a`. -/
theorem hTerminal_rightInv {F : Frame.{u}} (a : F.carrier) :
    hTerminal_toFrame (hTerminal_ofFrame a : OPred (OSetTerminal F)) = a := rfl

/-- The two maps are order-preserving in both directions, confirming
    `opredFrame (OSetTerminal F) ≅ F` as frames.

    Forward: `p ≤ q ↔ p PUnit.unit ≤ q PUnit.unit`. -/
theorem hTerminal_mono {F : Frame.{u}} {p q : OPred (OSetTerminal F)}
    (h : OPred.le p q) : F.le (hTerminal_toFrame p) (hTerminal_toFrame q) :=
  h PUnit.unit

theorem hTerminal_mono' {F : Frame.{u}} {a b : F.carrier}
    (h : F.le a b) : OPred.le (hTerminal_ofFrame a : OPred (OSetTerminal F))
      (hTerminal_ofFrame b) :=
  fun _ => h

-- BOOK §2.227: The full equivalence  Map(O(Y)-valued sets) ≃ H(Y)  states that
-- the category OSet(O(Y)) of O(Y)-valued sets is equivalent to the category of
-- sheaves on Y (= H(Y) in Freyd's notation), where H(Y) is the topos of
-- O(Y)-valued sets whose "maps" are the local sections.
--
-- The above establishes:
--   • OSet(F) is a category  (osetCat instance),
--   • for each F-valued set A, OPred(F, A) is a Frame / Heyting algebra
--     (opredFrame instance), giving the subobject lattice,
--   • OPred(F, OSetTerminal F) ≅ F as frames
--     (hTerminal_leftInv / hTerminal_rightInv).
--
-- The full equivalence functor OSet(O(Y)) ≃ Sh(Y) requires:
--   (a) sheaf / presheaf infrastructure (compatible families, gluing),
--   (b) the "irredundant" / separated notion on O(Y)-valued sets,
--   (c) the associated-sheaf functor and unit/counit natural transformations.
-- These need the presheaf framework not yet in the repo; left as a precise TODO.

-- BOOK §2.331: O(X)-valued sets and the geometric representation theorem.
-- Any countable tabular unitary division allegory embeds in (O(X)-valued sets)^ω
-- for a suitable locale O(X). This uses §2.227 + §1.74 (focal representation).
-- Requires: tabular/division allegory infrastructure (§2.1), focal representation
-- theorem (§1.741–§1.742), and the sheaf/locale machinery above.
-- Left as a precise TODO.

-- BOOK §1.74x: Representation theorems via opens.
-- §1.741: Every logos can be embedded in a logos of the form Sh(O(X)).
-- §1.742: Countable logos embeds in Sh(O(ℝ)).
-- These require the focal representation + sheaf machinery; left as TODO.

end Freyd
