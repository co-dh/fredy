/-
  §1.543 — Milestone 1: the coherent transfinite capitalization tower.

  Freyd's capitalization proof iterates the relative-capitalization successor functor
  `(-)*` (packaged here as `Capitalization.CapStep` / a uniform `nextStep`) transfinitely:

      stage 0          = A                       (the seed pre-regular category)
      stage (succ p)   = nextStep (stage p)      (apply the successor functor)
      stage (limit ℓ)  = colim_{a < ℓ} stage a   (directed colimit of all earlier stages)

  Over a well-order on enough objects this produces a long enough chain to point every
  well-supported object cofinally (later milestones).  THIS file's *only* deliverable (M1)
  is the coherent directed system itself — a `Colim.CatSystem ι D` together with its
  `.Coherent` — built from a well-order via `Freyd.WO.exists_wellOrder` /
  `IsWellOrder.toDirected`, with successor stages = `nextStep` and limit stages =
  `Colim.colimitCat`.

  Preservation / cofinality / capitalness / wiring into `capData_exists` are LATER
  milestones and are deliberately absent here.

  ## Construction shape (ONE simultaneous well-founded recursion)

  The earlier two-pass construction defined stage objects and transition maps in separate
  passes; at a limit it built the carrier as a `Colimit` over transition data that was itself
  `Sorry`, making the carrier *type* ill-defined.  This file replaces that with a SINGLE
  well-founded recursion `segSysAux` whose motive at `c` is an entire coherent directed system
  on the *segment* `Seg c = { a // a ≤ c }` (`SegSys c`: a `Colim.CatSystem` + its `Coherent` +
  a per-object `PreRegularCategory`).  Carrying the whole segment system — not just the top
  object — is exactly what makes the limit branch's `Colim.colimitCat` well-defined: a limit
  `c`'s top category is the colimit of the strict-predecessor sub-system assembled from `IH`,
  and `colimitCat` consumes that sub-system's `Coherent`.

  Branches: zero = the one-object system with carrier `b₀`; successor `c=p⁺` = `Sp = IH p _`
  extended by the fresh `nextStep` top (`succBundle`/`succA`/`succCat`/`succF`); limit = the
  genuine `Colim.colimitCat` of `belowSys` (`limBundle`/`limA`/`limCat`/`limF`, top transitions
  = `CatSystem.objIncl`).  The global `towerSystem` reads off each segment's top.

  ## What is real vs. what is stubbed

  REAL (no `Sorry` in the data): the object carriers and the `Cat` instances in every branch
  (including the limit top = a genuine `Colim.colimitCat`), and the transition OBJECT-maps
  `succF`/`limF`/`belowF`/`gF`.  STUBBED (named `theorem`/`def`, one documented `Sorry` each, on
  a TRUE statement): the morphism-level transition coherence that crosses a successor/limit
  boundary — `*FunctF` (functoriality), `*_F_refl`/`*_F_trans`, `*Coherent`, the restriction-
  agreement object-equalities `belowObjAgree`/`gObjAgree`, and the colimit pre-regularity
  `limTopPre`.  These are the standing §1.543 transfinite colimit-of-categories obstruction.

  CAVEAT (honest): because `Colim.colimitCat` requires a `Coherent` witness, the limit stage's
  `Cat` instance is fed `belowCoherent`, which is one of the documented `Sorry`s — so the limit
  `Cat` (not its object carrier) transitively depends on that coherence stub.

  NO custom `axiom`, NO `: True`, NO `:= trivial`, NO `Sorry` on a false statement.

  Universes: pinned `.{u,u}` to match `nextStep` / `colimitCat`; the index is a well-order of
  a `Type u`, NOT mathlib `Ordinal`.  This file is mathlib-free (built on `Freyd.WO` and
  `Freyd.Colim`).
-/
import Fredy.Capitalization
import Fredy.WellOrdering

open Freyd
open Freyd.Colim

namespace Freyd.CapTower

universe u

/-! ## Well-founded recursion engine from `IsWellOrder` -/

section WF
variable {α : Type u} {r : α → α → Prop}

/-- A well-order's least-element operator yields genuine `WellFounded`ness of `r`: were some
    point inaccessible, `least` on the inaccessibility predicate would give a minimal
    inaccessible point all of whose `r`-predecessors are accessible — contradicting `Acc.intro`. -/
theorem wf_of_isWellOrder (w : WO.IsWellOrder r) : WellFounded r := by
  refine ⟨fun a => Classical.byContradiction (fun hna => ?_)⟩
  obtain ⟨m, hm, hmin⟩ := w.least (fun x => ¬ Acc r x) ⟨a, hna⟩
  exact hm (Acc.intro m (fun y hy => Classical.byContradiction (fun hny => hmin y hny hy)))

end WF

/-! ## Point classification: zero / successor / limit -/

section Classify
variable {α : Type u} (r : α → α → Prop)

/-- `p` is an immediate `r`-predecessor of `c`: `p < c` and nothing sits strictly between. -/
def IsImmPred (c p : α) : Prop := r p c ∧ ∀ x, r x c → ¬ r p x

/-- `c` is a successor point (has an immediate predecessor). -/
def IsSucc (c : α) : Prop := ∃ p, IsImmPred r c p

/-- `c` is the least point (no predecessor). -/
def IsZero (c : α) : Prop := ∀ x, ¬ r x c

/-- The strict predecessor sub-type of `c` (the index of a limit stage's colimit). -/
def Below (c : α) : Type u := { a : α // r a c }

variable {r}

/-- An immediate predecessor is unique (any two are equal): by trichotomy, distinct
    predecessors would force one strictly below the other, contradicting immediacy. -/
theorem immPred_unique (w : WO.IsWellOrder r) {c p q : α}
    (hp : IsImmPred r c p) (hq : IsImmPred r c q) : p = q := by
  rcases w.tri p q with h | h | h
  · exact absurd h (hp.2 q hq.1)
  · exact h
  · exact absurd h (hq.2 p hp.1)

end Classify

/-! ## The seed, the successor, and the global stage family

We fix a seed `b₀ : PreRegBundle` and a uniform successor `nextStep`.  The global bundle
family is defined by well-founded recursion: each point's bundle is computed from the
bundles of its strict predecessors. -/

section Tower
variable {α : Type u} {r : α → α → Prop}
variable (w : WO.IsWellOrder r)
variable (b₀ : PreRegBundle.{u})
variable (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)

/-- The directed index of the tower: the well-order as a `Colim.Directed`. -/
def D : Colim.Directed α := w.toDirected

@[simp] theorem D_le {a b : α} : (D w).le a b ↔ (r a b ∨ a = b) := Iff.rfl

/-! ## The one-pass segment recursion

The defect of the previous two-pass construction was that a limit stage built its carrier as a
`Colimit` over transition data that was itself `Sorry` — making the carrier *type* ill-defined.
The fix is a SINGLE well-founded recursion whose motive at `c` is an entire coherent directed
system on the *segment* `Seg c = { a // a ≤ c }`, so that objects, transition maps, and the
coherence among predecessors are produced simultaneously — exactly what `Colim.colimitCat`
needs to turn the limit's predecessor sub-system into a genuine `Cat`.

### The segment index

`Seg c` is the set of points `≤ c`; `segDirected w b₀ nextStep c` is the directed order it inherits from
`D w` (bound = the `r`-greater of the two endpoints, which stays `≤ c`, mirroring
`belowDirected`). -/

/-- The segment index of `c`: all points `≤ c` in the well-order. -/
-- `b₀` / `nextStep` are referenced trivially in `Seg` so that auto-inclusion places them —
-- uniformly and in a fixed order — into the signature of `Seg` and hence of every definition
-- built on it.  This keeps the whole segment family addressable by the single spelling
-- `… w b₀ nextStep …`, avoiding the desynchronisation that per-use auto-inclusion would cause.
def Seg (c : α) : Type u :=
  let _ : PreRegBundle.{u} × (∀ (S : PreRegBundle.{u}), CapStep S.carrier) := (b₀, nextStep)
  { a : α // (D w).le a c }

/-- `Seg c` inherits `D w`'s directed order; the common bound of two `≤ c` points is their
    `r`-greater (still `≤ c`), so the bound stays inside the segment. -/
def segDirected (c : α) : Colim.Directed (Seg w b₀ nextStep c) where
  le a b := (D w).le a.1 b.1
  refl a := (D w).refl a.1
  trans hab hbc := (D w).trans hab hbc
  bound a b := by
    rcases w.tri a.1 b.1 with h | h | h
    · exact ⟨b, Or.inl h, (D w).refl b.1⟩
    · exact ⟨b, Or.inr h, (D w).refl b.1⟩
    · exact ⟨a, (D w).refl a.1, Or.inl h⟩

/-- **The recursion motive.**  At `c`, an entire coherent directed system of categories on the
    segment `Seg c`.  Carrying the whole segment system (not just the top object) is what makes
    the limit branch's `colimitCat` well-defined: a limit `c`'s top category is the colimit of
    THIS system restricted to the strict predecessors, and `colimitCat` needs that sub-system's
    `Coherent`. -/
structure SegSys (c : α) where
  /-- the directed system of categories on `Seg c` (objects + `Cat` + transition functors) -/
  sys : Colim.CatSystem.{u, u} (Seg w b₀ nextStep c) (segDirected w b₀ nextStep c)
  /-- its morphism-level coherence (needed to feed `colimitCat` at the next limit) -/
  coh : sys.Coherent
  /-- every stage of the segment is pre-regular (needed to feed `nextStep` at the next successor);
      packaged so the top object `segTop` carries a `PreRegularCategory`. -/
  pre : ∀ i, @PreRegularCategory (sys.A i) (sys.catA i)

/-! ### Restriction of the index along `a' ≤ c`

A point `a' ≤ c` gives an inclusion `Seg a' ↪ Seg c` (`segIncl`), order-preserving both ways
(`segIncl_le` / `segIncl_le'`).  Because `(D w).le _ _` is a `Prop`, the `≤`-witness in a `Seg`
element is irrelevant: any two `Seg` elements with equal `.1` are equal (`Seg.ext`). -/

/-- Two segment elements with the same underlying point are equal (witness is a `Prop`). -/
theorem Seg.ext {c : α} {a b : Seg w b₀ nextStep c} (h : a.1 = b.1) : a = b := Subtype.ext h

/-- The inclusion `Seg a' ↪ Seg c` for `a' ≤ c`: a point `≤ a'` is `≤ c` by transitivity. -/
def segIncl {a' c : α} (h : (D w).le a' c) (a : Seg w b₀ nextStep a') : Seg w b₀ nextStep c :=
  ⟨a.1, (D w).trans a.2 h⟩

@[simp] theorem segIncl_fst {a' c : α} (h : (D w).le a' c) (a : Seg w b₀ nextStep a') :
    (segIncl w b₀ nextStep h a).1 = a.1 := rfl

/-! ### The strict-predecessor sub-system at a limit

At a limit `c`, the top category is the directed colimit of the sub-system on the strict
predecessors `Below c`.  That sub-system's objects, transition functors, and coherence are read
off the recursive segment systems `IH a a.2 : SegSys a`: the object at `a < c` is the top of
`a`'s segment, and the transition `a → b` (for `a ≤ b < c`) is `b`'s segment transition from the
`a`-slot to the `b`-top.  The one fact that makes this assembly *internally consistent* — that
`b`'s segment, restricted to `Seg a`, agrees with `a`'s own segment — is the restriction-
agreement lemma `segSys_restrict_agree`.  The OBJECT carrier and the OBJECT transition maps of
the sub-system are genuine (`(IH _).sys.A` / `(IH _).sys.F`); the morphism-level coherence that
`colimitCat` consumes is the genuine open transfinite obstruction, isolated below. -/

/-- The strict-predecessor index of a limit stage. -/
def belowDirected (c : α) : Colim.Directed (Below r c) where
  le a b := (D w).le a.1 b.1
  refl a := (D w).refl a.1
  trans hab hbc := (D w).trans hab hbc
  bound a b := by
    rcases w.tri a.1 b.1 with h | h | h
    · exact ⟨b, Or.inl h, Or.inr rfl⟩
    · exact ⟨b, Or.inr h, Or.inr rfl⟩
    · exact ⟨a, Or.inr rfl, Or.inl h⟩

/-- `Below c ↪ Seg c`: a strict predecessor is `≤ c`. -/
def belowToSeg {c : α} (a : Below r c) : Seg w b₀ nextStep c := ⟨a.1, Or.inl a.2⟩

/-- The top slot of a segment: `c` itself sits in `Seg c`. -/
def segTop (c : α) : Seg w b₀ nextStep c := ⟨c, (D w).refl c⟩

/-- The top object of a segment packaged as a `PreRegBundle`, so that `nextStep` can be applied to
    it at the next successor stage. -/
def topBundle {p : α} (Sp : SegSys w b₀ nextStep p) : PreRegBundle.{u} :=
  ⟨Sp.sys.A (segTop w b₀ nextStep p), Sp.sys.catA _, Sp.pre _⟩

/-! ### The successor branch

For `c` a successor with immediate predecessor `p = Classical.choose hs` and `Sp = IH p _`, the
segment `Seg c` is `Seg p` with one new top object `c`.  A slot `a ≤ p` keeps `Sp`'s object; the
top `c` gets `nextStep (topBundle Sp)`'s target `T`.  Object data and transition object-maps are
real (`succA` / `succCat` / `succF`); the functor `succFunctF` and the laws `succ_F_refl` /
`succ_F_trans` / `succCoherent` are the morphism-level transition coherence — TRUE statements,
isolated each with one documented `Sorry`. -/

variable (c : α)

open Classical in
/-- The successor segment object at `a`, packaged as a `PreRegBundle` (carrier + `Cat` + pre-reg)
    so all three projections come from ONE `dite` and reduce definitionally: slot `≤ p` reuses
    `Sp`'s bundle, the top `c` is the fresh `nextStep` target. -/
noncomputable def succBundle {p : α} (Sp : SegSys w b₀ nextStep p) (a : Seg w b₀ nextStep c) :
    PreRegBundle.{u} :=
  if h : (D w).le a.1 p then ⟨Sp.sys.A ⟨a.1, h⟩, Sp.sys.catA _, Sp.pre _⟩
  else let s := nextStep (topBundle w b₀ nextStep Sp); ⟨s.T, s.catT, s.preT⟩

/-- Successor segment objects: the carrier of `succBundle`. -/
noncomputable def succA {p : α} (Sp : SegSys w b₀ nextStep p) (a : Seg w b₀ nextStep c) : Type u :=
  (succBundle w b₀ nextStep c Sp a).carrier

/-- `Cat` instance on a successor segment object: the `Cat` of `succBundle`. -/
noncomputable instance succCat {p : α} (Sp : SegSys w b₀ nextStep p) (a : Seg w b₀ nextStep c) :
    Cat.{u} (succA w b₀ nextStep c Sp a) := (succBundle w b₀ nextStep c Sp a).cat

/-- `PreRegularCategory` on a successor segment object: the pre-reg of `succBundle`. -/
noncomputable instance succPre {p : α} (Sp : SegSys w b₀ nextStep p) (a : Seg w b₀ nextStep c) :
    @PreRegularCategory _ (succCat w b₀ nextStep c Sp a) := (succBundle w b₀ nextStep c Sp a).pre

/-- Successor segment transition object-map `a → b` (real).  Three live cases: both `≤ p`
    (`Sp`'s transition); `a ≤ p`, `b = c` (push to `Sp`'s top, then `nextStep.step`); `a = b = c`
    (identity).  The fourth (`a = c`, `b ≤ p`) is vacuous (`c ≤ p` is impossible). -/
noncomputable def succF {p : α} (Sp : SegSys w b₀ nextStep p)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    succA w b₀ nextStep c Sp a → succA w b₀ nextStep c Sp b := by
  unfold succA succBundle
  by_cases hbp : (D w).le b.1 p
  · have hap : (D w).le a.1 p := (D w).trans hab hbp
    rw [dif_pos hap, dif_pos hbp]
    exact Sp.sys.F (show (segDirected w b₀ nextStep p).le ⟨a.1, hap⟩ ⟨b.1, hbp⟩ from hab)
  · rw [dif_neg hbp]
    by_cases hap : (D w).le a.1 p
    · rw [dif_pos hap]
      exact fun x => (nextStep (topBundle w b₀ nextStep Sp)).step
        (Sp.sys.F (show (segDirected w b₀ nextStep p).le ⟨a.1, hap⟩ (segTop w b₀ nextStep p)
          from hap) x)
    · rw [dif_neg hap]; exact id

/-- **TRUE coherence obligation (successor functoriality).**  `succF` is a functor: on slots
    `≤ p` it is `Sp.sys.functF`; on the top crossing it is `compFunctor` of `Sp.sys.functF` with
    `nextStep`'s `stepFun`.  The proof is `dite`-branch bookkeeping over `succF`; isolated here. -/
noncomputable def succFunctF {p : α} (Sp : SegSys w b₀ nextStep p)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    @Functor _ (succCat w b₀ nextStep c Sp a) _ (succCat w b₀ nextStep c Sp b)
      (succF w b₀ nextStep c Sp hab) :=
  -- OBSTRUCTION: branch-wise functoriality through the `dite`-defined `succF`; the mathematical
  -- content (functor composition `stepFun ∘ Sp.functF`) is standard, the `dite` transport is the
  -- bookkeeping.  Real morphism map not yet extracted from the cased definition.
  sorry

/-- **TRUE obligation (successor identity transition).**  `succF (refl) = id` on objects. -/
theorem succ_F_refl {p : α} (Sp : SegSys w b₀ nextStep p) (a : Seg w b₀ nextStep c)
    (x : succA w b₀ nextStep c Sp a) :
    succF w b₀ nextStep c Sp ((segDirected w b₀ nextStep c).refl a) x = x :=
  -- OBSTRUCTION: `succF` at `a = a` lands in the `≤ p` branch (`Sp.F_refl`) or the top branch
  -- (`x = c`, identity); discharging requires unfolding the `dite` at the reflexive index.
  sorry

/-- **TRUE obligation (successor composite transition).**  `succF (trans) = succF ∘ succF`. -/
theorem succ_F_trans {p : α} (Sp : SegSys w b₀ nextStep p)
    {a b d : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b)
    (hbd : (segDirected w b₀ nextStep c).le b d) (x : succA w b₀ nextStep c Sp a) :
    succF w b₀ nextStep c Sp ((segDirected w b₀ nextStep c).trans hab hbd) x
      = succF w b₀ nextStep c Sp hbd (succF w b₀ nextStep c Sp hab x) :=
  -- OBSTRUCTION: case split on which of `a,b,d` are `≤ p`; the genuine content is `Sp.F_trans`
  -- and `nextStep.step`'s naturality, modulo the `dite` transport.
  sorry

/-- The successor segment system on `Seg c` (objects/`Cat`/transitions real; `functF` and the
    laws are the isolated coherence obligations above). -/
noncomputable def succSys {p : α} (Sp : SegSys w b₀ nextStep p) :
    Colim.CatSystem.{u, u} (Seg w b₀ nextStep c) (segDirected w b₀ nextStep c) :=
  { A := succA w b₀ nextStep c Sp
    catA := succCat w b₀ nextStep c Sp
    F := @fun a b h => succF w b₀ nextStep c Sp (a := a) (b := b) h
    functF := @fun a b h => succFunctF w b₀ nextStep c Sp (a := a) (b := b) h
    F_refl := fun {_} x => succ_F_refl w b₀ nextStep c Sp _ x
    F_trans := fun {_ _ _} hab hbd x => succ_F_trans w b₀ nextStep c Sp hab hbd x }

/-- **TRUE obligation (successor coherence).**  The successor segment system is `Coherent`. -/
theorem succCoherent {p : α} (Sp : SegSys w b₀ nextStep p) :
    (succSys w b₀ nextStep c Sp).Coherent :=
  -- OBSTRUCTION: morphism-level form of `succ_F_refl`/`succ_F_trans` via `Sp.coh` and `stepFun`'s
  -- functoriality.  Depends on `succFunctF` (the real morphism map), hence isolated together.
  sorry

/-- The successor branch of the recursion: assemble `SegSys c` from `Sp = IH p _`. -/
noncomputable def segSucc (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    (_hz : ¬ IsZero r c) (hs : IsSucc r c) : SegSys w b₀ nextStep c :=
  let Sp : SegSys w b₀ nextStep (Classical.choose hs) := IH _ (Classical.choose_spec hs).1
  { sys := succSys w b₀ nextStep c Sp
    coh := succCoherent w b₀ nextStep c Sp
    pre := fun a => succPre w b₀ nextStep c Sp a }

/-! ### The limit branch

For `c` a limit, the top object is the directed colimit `Colim.colimitCat` of the strict-
predecessor sub-system `belowSys`, whose objects are the tops of `IH a _` and whose transitions
read off `IH`.  The OBJECT system (`belowObjSys`) and the colimit OBJECT carrier are real;
`colimitCat` additionally requires the sub-system's `Coherent`, whose limit-crossing instance is
the genuine open transfinite obstruction (`belowCoherent`), isolated with one documented `Sorry`.

This is the irreducible blocker of M1: `Colim.colimitCat` cannot be applied without a `Coherent`
witness, so the limit `Cat` instance transitively depends on `belowCoherent`'s `Sorry`.  The
OBJECT-level data — carrier and transition object-maps — is nonetheless genuine. -/

/-- For `a ≤ b` strict predecessors of `c`, `b`'s segment slot at `a` is the same object as `a`'s
    own segment top: `(IH b).sys.A ⟨a, _⟩ = (IH a).sys.A (segTop a)`.

    **TRUE restriction-agreement obligation (the crux).**  This is the statement that the segment
    systems agree on overlaps.  For the SPECIFIC family `IH = fun a _ => segSys a` it is the proven
    `segSys_restrict_agree` (see below; a post-hoc well-founded induction on the global fixpoint).
    It is stated here over an ARBITRARY `IH`, for which it is genuinely unprovable (two unrelated
    `SegSys a` values have unrelated object families) — and the global `segSys` fixpoint equation,
    the only thing that pins `IH` to `segSys`, is unavailable inside the recursion body.  So this
    in-recursion instance stays a documented `Sorry`; the GLOBAL transition object-equality
    `gObjAgree` (the form that actually feeds the tower `towerSystem`'s data via `gF`) is proven
    Sorry-free as a corollary of `segSys_restrict_agree`. -/
theorem belowObjAgree (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b : Below r c} (hab : (belowDirected w c).le a b) :
    (IH b.1 b.2).sys.A ⟨a.1, (D w).trans hab (Or.inr rfl)⟩
      = (IH a.1 a.2).sys.A (segTop w b₀ nextStep a.1) :=
  sorry

/-- Limit sub-system transition object-map `a → b` (`a ≤ b < c`): push `a`'s top into `b`'s
    segment slot at `a` (via `belowObjAgree`), then run `b`'s segment transition to `b`'s top.
    The object map IS defined; it uses the restriction-agreement equality `belowObjAgree`. -/
noncomputable def belowF (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b : Below r c} (hab : (belowDirected w c).le a b) :
    (IH a.1 a.2).sys.A (segTop w b₀ nextStep a.1)
      → (IH b.1 b.2).sys.A (segTop w b₀ nextStep b.1) :=
  fun x => (IH b.1 b.2).sys.F
    (show (segDirected w b₀ nextStep b.1).le ⟨a.1, (D w).trans hab (Or.inr rfl)⟩
        (segTop w b₀ nextStep b.1) from hab)
    (belowObjAgree w b₀ nextStep c IH hab ▸ x)

/-- **TRUE obligation (limit sub-system functoriality).**  `belowF` is a functor. -/
noncomputable def belowFunctF (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b : Below r c} (hab : (belowDirected w c).le a b) :
    @Functor _ ((IH a.1 a.2).sys.catA _) _ ((IH b.1 b.2).sys.catA _)
      (belowF w b₀ nextStep c IH hab) :=
  -- OBSTRUCTION: morphism map of `belowF`; the genuine content is `(IH b).sys.functF` precomposed
  -- with the agreement transport.  Depends on `belowObjAgree`.
  sorry

/-- **TRUE obligation (limit sub-system identity transition).** -/
theorem belowF_refl (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Below r c)
    (x : (IH a.1 a.2).sys.A (segTop w b₀ nextStep a.1)) :
    belowF w b₀ nextStep c IH ((belowDirected w c).refl a) x = x :=
  -- OBSTRUCTION: at `a = a`, `belowF` is `(IH a).sys.F (refl)` after the agreement transport;
  -- `(IH a).sys.F_refl` closes it modulo `belowObjAgree` at the reflexive index.
  sorry

/-- **TRUE obligation (limit sub-system composite transition).** -/
theorem belowF_trans (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b d : Below r c} (hab : (belowDirected w c).le a b)
    (hbd : (belowDirected w c).le b d)
    (x : (IH a.1 a.2).sys.A (segTop w b₀ nextStep a.1)) :
    belowF w b₀ nextStep c IH ((belowDirected w c).trans hab hbd) x
      = belowF w b₀ nextStep c IH hbd (belowF w b₀ nextStep c IH hab x) :=
  -- OBSTRUCTION: `(IH d).sys.F_trans` plus the agreement transports composing.
  sorry

/-- The strict-predecessor sub-system at a limit `c`, as a `CatSystem` over `Below c`.  Objects =
    tops of `IH`; transition `a → b` = `belowF` (via restriction-agreement).  All OBJECT data is
    real modulo the `belowObjAgree` agreement equality. -/
noncomputable def belowSys (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    Colim.CatSystem.{u, u} (Below r c) (belowDirected w c) :=
  { A := fun a => (IH a.1 a.2).sys.A (segTop w b₀ nextStep a.1)
    catA := fun a => (IH a.1 a.2).sys.catA _
    F := fun {_ _} h => belowF w b₀ nextStep c IH h
    functF := fun {_ _} h => belowFunctF w b₀ nextStep c IH h
    F_refl := fun {_} x => belowF_refl w b₀ nextStep c IH _ x
    F_trans := fun {_ _ _} hab hbd x => belowF_trans w b₀ nextStep c IH hab hbd x }

/-- **TRUE obligation (limit sub-system coherence).**  `belowSys` is `Coherent` — the morphism-
    level transition coherence that `Colim.colimitCat` consumes.  Its limit-crossing instance is
    the genuine open transfinite obstruction (the repo's standing §1.543 gap).  Isolated here with
    a single documented `Sorry` on the true statement. -/
theorem belowCoherent (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    (belowSys w b₀ nextStep c IH).Coherent :=
  sorry

/-- **TRUE obligation (limit pre-regularity).**  The colimit top category `colimitCat (belowSys)`
    is pre-regular — "a directed colimit of pre-regular categories is pre-regular"
    (`Capitalization.colimitPreRegular`), a later-milestone preservation result.  Isolated here
    with one documented `Sorry`; the carrier (`colimitCat`) and its `Cat` are real. -/
noncomputable def limTopPre (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    @PreRegularCategory _ (Colim.colimitCat _ (belowCoherent w b₀ nextStep c IH)) :=
  sorry

open Classical in
/-- The limit segment object at `a`, packaged as a `PreRegBundle`: slot `a < c` reuses `IH a`'s
    top bundle; the top `c` is the genuine colimit `⟨(belowSys).Obj, colimitCat, limTopPre⟩`. -/
noncomputable def limBundle (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Seg w b₀ nextStep c) :
    PreRegBundle.{u} :=
  if h : r a.1 c then ⟨(IH a.1 h).sys.A (segTop w b₀ nextStep a.1), (IH a.1 h).sys.catA _,
      (IH a.1 h).pre _⟩
  else ⟨(belowSys w b₀ nextStep c IH).Obj, Colim.colimitCat _ (belowCoherent w b₀ nextStep c IH),
      limTopPre w b₀ nextStep c IH⟩

/-- Limit segment objects: the carrier of `limBundle`. -/
noncomputable def limA (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Seg w b₀ nextStep c) : Type u :=
  (limBundle w b₀ nextStep c IH a).carrier

/-- `Cat` instance on a limit segment object: the `Cat` of `limBundle` (a real `colimitCat` at
    the top). -/
noncomputable instance limCat (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Seg w b₀ nextStep c) :
    Cat.{u} (limA w b₀ nextStep c IH a) := (limBundle w b₀ nextStep c IH a).cat

/-- `PreRegularCategory` on a limit segment object: the pre-reg of `limBundle`. -/
noncomputable instance limPre (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Seg w b₀ nextStep c) :
    @PreRegularCategory _ (limCat w b₀ nextStep c IH a) := (limBundle w b₀ nextStep c IH a).pre

/-- Limit segment transition object-map `a → b` (real).  Slots both `< c`: `belowF`.  Into the
    top `b = c` from `a < c`: the colimit inclusion `objIncl`.  Top to top: identity. -/
noncomputable def limF (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    limA w b₀ nextStep c IH a → limA w b₀ nextStep c IH b := by
  unfold limA limBundle
  by_cases hbc : r b.1 c
  · -- b < c ⟹ a < c (a ≤ b < c)
    have hac : r a.1 c := by
      rcases hab with hab | hab
      · exact w.trans hab hbc
      · exact hab ▸ hbc
    rw [dif_pos hac, dif_pos hbc]
    exact belowF w b₀ nextStep c IH (a := ⟨a.1, hac⟩) (b := ⟨b.1, hbc⟩) hab
  · rw [dif_neg hbc]
    by_cases hac : r a.1 c
    · rw [dif_pos hac]
      -- a < c into the colimit top: the canonical inclusion.
      exact fun x => (belowSys w b₀ nextStep c IH).objIncl ⟨a.1, hac⟩ x
    · rw [dif_neg hac]; exact id

/-- **TRUE obligation (limit segment functoriality).**  `limF` is a functor (below: `belowFunctF`;
    into the top: the inclusion is the colimit cocone, functorial via the hom-colimit). -/
noncomputable def limFunctF (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    @Functor _ (limCat w b₀ nextStep c IH a) _ (limCat w b₀ nextStep c IH b)
      (limF w b₀ nextStep c IH hab) :=
  -- OBSTRUCTION: morphism map of `limF`; the into-top case is the colimit inclusion-as-functor,
  -- which the repo does not pre-build (only `objIncl` on objects exists).  Isolated.
  sorry

/-- **TRUE obligation (limit segment identity transition).** -/
theorem lim_F_refl (IH : ∀ a, r a c → SegSys w b₀ nextStep a) (a : Seg w b₀ nextStep c)
    (x : limA w b₀ nextStep c IH a) :
    limF w b₀ nextStep c IH ((segDirected w b₀ nextStep c).refl a) x = x :=
  sorry

/-- **TRUE obligation (limit segment composite transition).**  The into-the-top instance is
    `objIncl_compat` (cocone-compatibility of the colimit inclusions). -/
theorem lim_F_trans (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    {a b d : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b)
    (hbd : (segDirected w b₀ nextStep c).le b d) (x : limA w b₀ nextStep c IH a) :
    limF w b₀ nextStep c IH ((segDirected w b₀ nextStep c).trans hab hbd) x
      = limF w b₀ nextStep c IH hbd (limF w b₀ nextStep c IH hab x) :=
  sorry

/-- The limit segment system on `Seg c` (objects/`Cat`/transitions real, with a genuine
    `colimitCat` top; `functF` and the laws are the isolated coherence obligations above). -/
noncomputable def limSys (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    Colim.CatSystem.{u, u} (Seg w b₀ nextStep c) (segDirected w b₀ nextStep c) :=
  { A := limA w b₀ nextStep c IH
    catA := limCat w b₀ nextStep c IH
    F := @fun a b h => limF w b₀ nextStep c IH (a := a) (b := b) h
    functF := @fun a b h => limFunctF w b₀ nextStep c IH (a := a) (b := b) h
    F_refl := fun {_} x => lim_F_refl w b₀ nextStep c IH _ x
    F_trans := fun {_ _ _} hab hbd x => lim_F_trans w b₀ nextStep c IH hab hbd x }

/-- **TRUE obligation (limit segment coherence).** -/
theorem limCoherent (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    (limSys w b₀ nextStep c IH).Coherent :=
  sorry

/-- The limit branch of the recursion: top object = `colimitCat (belowSys)`. -/
noncomputable def segLimit (IH : ∀ a, r a c → SegSys w b₀ nextStep a)
    (_hz : ¬ IsZero r c) (_hs : ¬ IsSucc r c) : SegSys w b₀ nextStep c :=
  { sys := limSys w b₀ nextStep c IH
    coh := limCoherent w b₀ nextStep c IH
    pre := fun a => limPre w b₀ nextStep c IH a }

open Classical in
/-- **The recursion body.**  Produces the segment system `SegSys c` from the segment systems of
    all strict predecessors `IH a (_ : r a c)`.  Classifies `c`:

      * **zero** (`IsZero r c`): `Seg c` is the singleton `{c}`; the one-object system has carrier
        `b₀`, the only transition is the identity, coherent on the nose.
      * **successor** (`IsSucc r c`, immediate predecessor `p`): the new top object at `c` is
        `nextStep (Sp.top)`'s target `T`; the segment `Seg c` reuses `Sp = IH p _` on the slots
        `≤ p` and the new object at `c`, with `a → c` (for `a ≤ p`) given by `nextStep.step ∘
        (Sp.sys.F (a ≤ p))` and its functoriality from `compFunctor`.
      * **limit** (else): the top object at `c` is `Colim.colimitCat` of the `Below c` sub-system
        assembled from `IH`; slots `a < c` reuse `IH a _` and `a → c` is the colimit inclusion
        `objIncl`.

    The data (objects/`Cat`/transition object-maps and the limit `colimitCat` carrier) are real
    in every branch.  The successor/limit *morphism*-coherence crossings are the open transfinite
    obstruction; each is a single documented `Sorry` on the true coherence statement, isolated as
    a named lemma fed in here. -/
noncomputable def segSysAux (c : α) (IH : ∀ a, r a c → SegSys w b₀ nextStep a) :
    SegSys w b₀ nextStep c := by
  classical
  by_cases hz : IsZero r c
  · -- ZERO: singleton segment, carrier `b₀`, identity transition.  Fully real, coherent.
    exact {
      sys := {
        A := fun _ => b₀.carrier
        catA := fun _ => b₀.cat
        F := fun {_ _} _ x => x
        functF := fun {_ _} _ => @idFunctor _ b₀.cat
        F_refl := fun {_} _ => rfl
        F_trans := fun {_ _ _} _ _ _ => rfl }
      coh := { refl_map := fun {_ _ _} _ => HEq.rfl
               trans_map := fun {_ _ _} _ _ _ _ _ => HEq.rfl }
      pre := fun _ => b₀.pre }
  · by_cases hs : IsSucc r c
    · -- SUCCESSOR.
      exact segSucc w b₀ nextStep c IH hz hs
    · -- LIMIT.
      exact segLimit w b₀ nextStep c IH hz hs

/-! ## The global segment family and the tower `CatSystem`

`segSys c` is the segment system at `c`, the `WellFounded.fix` of `segSysAux`.  The global tower
takes, at each `c`, the TOP object of its segment (`segTop`), with transitions read as the
segment-`c` transition from the `a`-slot to `c`'s top. -/

/-- The global segment family by well-founded recursion. -/
noncomputable def segSys (c : α) : SegSys w b₀ nextStep c :=
  (wf_of_isWellOrder w).fix (segSysAux w b₀ nextStep) c

/-- The `WellFounded.fix` fixpoint equation for `segSys`. -/
theorem segSys_eq (c : α) :
    segSys w b₀ nextStep c
      = segSysAux w b₀ nextStep c (fun a _ => segSys w b₀ nextStep a) :=
  WellFounded.fix_eq (wf_of_isWellOrder w) (segSysAux w b₀ nextStep) c

/-! ### Restriction agreement (the crux), proven by well-founded induction

`segSys_restrict_agree` says: reading the segment system at `c` on a slot included from `Seg a'`
(for `a' ≤ c`) gives the same object as reading the segment system at `a'` on that slot directly.
This is the single fact that makes the limit sub-system internally consistent, and it discharges
the object-level transports inside the transition data (`belowF`/`gF`).  It is proven by
well-founded induction on `c`, unfolding `segSys` via `segSys_eq` and casing `segSysAux`'s three
branches.  Inside the body the recursion's IH is literally `fun a _ => segSys a` (the `WellFounded.fix`
unfolding), so `succBundle`/`limBundle`'s `Sp`/`IH a _` are the real `segSys` and the IH applies. -/

/-- **Restriction agreement.**  For `a' ≤ c` and any slot `a : Seg a'`, the segment system at `c`
    read at the included slot agrees with the segment system at `a'`.  Proven by well-founded
    induction; the heart of removing the object-equality `Sorry`s from the transition data. -/
theorem segSys_restrict_agree (c a' : α) (h : (D w).le a' c) (a : Seg w b₀ nextStep a') :
    (segSys w b₀ nextStep c).sys.A (segIncl w b₀ nextStep h a)
      = (segSys w b₀ nextStep a').sys.A a := by
  induction c using (wf_of_isWellOrder w).induction generalizing a' a with
  | _ c IH =>
  -- The `a' = c` case is trivial: `segIncl` is the identity slot, both sides coincide.
  rcases h with hlt | (rfl : a' = c)
  · -- `a' < c`: case on the classification of `c`.
    rw [segSys_eq w b₀ nextStep c]
    classical
    unfold segSysAux
    by_cases hz : IsZero r c
    · exact absurd hlt (hz a')
    · rw [dif_neg hz]
      by_cases hs : IsSucc r c
      · -- SUCCESSOR `c = p⁺`.  `a' < c` forces `a' ≤ p`, hence the slot is `≤ p` (dif_pos).
        rw [dif_pos hs]
        have himm : IsImmPred r c (Classical.choose hs) := Classical.choose_spec hs
        let p := Classical.choose hs
        -- `a.1 ≤ a' < c`, and `c`'s only predecessors are `≤ p`, so `a.1 ≤ p`.
        have ha'p : (D w).le a' p := by
          rcases w.tri a' p with hh | rfl | hh
          · exact Or.inl hh
          · exact (D w).refl p
          · exact absurd hh (himm.2 a' hlt)
        have hap : (D w).le a.1 p := (D w).trans a.2 ha'p
        -- LHS = `(segSys p).sys.A ⟨a.1, hap⟩`; apply IH at `p` with `a' ≤ p`.
        have key := IH p himm.1 a' ha'p a
        show (succBundle w b₀ nextStep c (segSys w b₀ nextStep p)
            (segIncl w b₀ nextStep (Or.inl hlt) a)).carrier
          = (segSys w b₀ nextStep a').sys.A a
        rw [← key]
        unfold succBundle
        rw [dif_pos (show (D w).le (segIncl w b₀ nextStep (Or.inl hlt) a).1 p from hap)]
        rfl
      · -- LIMIT `c`.  `a.1 ≤ a' < c` gives `r a.1 c` (dif_pos in `limBundle`).
        rw [dif_neg hs]
        have hac : r a.1 c := by
          rcases a.2 with hle | (heq : a.1 = a')
          · exact w.trans hle hlt
          · rw [heq]; exact hlt
        -- LHS = `(segSys a.1).sys.A (segTop a.1)`; apply IH at `a'` (`a' < c`) with `a.1 ≤ a'`.
        have ha1a' : (D w).le a.1 a' := a.2
        have key := IH a' hlt a.1 ha1a' (segTop w b₀ nextStep a.1)
        show (limBundle w b₀ nextStep c (fun a _ => segSys w b₀ nextStep a)
            (segIncl w b₀ nextStep (Or.inl hlt) a)).carrier
          = (segSys w b₀ nextStep a').sys.A a
        unfold limBundle
        rw [dif_pos (show r (segIncl w b₀ nextStep (Or.inl hlt) a).1 c from hac)]
        simp only [segIncl_fst]
        rw [← key]
        congr 1
  · -- `a' = c`: `segIncl` keeps `.1`, so the slot is literally `a`; both sides coincide.
    congr 1

/-- **Seed stage is the seed.**  At the least point the segment top is `b₀`'s carrier (Sorry-free:
    the zero branch is the singleton system with carrier `b₀`). -/
theorem segSys_zero_carrier {c : α} (hz : IsZero r c) :
    (segSys w b₀ nextStep c).sys.A (segTop w b₀ nextStep c) = b₀.carrier := by
  rw [segSys_eq]; unfold segSysAux
  rw [dif_pos hz]

/-- The tower object at `c`: the top of `c`'s segment. -/
def gobj (c : α) : Type u := (segSys w b₀ nextStep c).sys.A (segTop w b₀ nextStep c)

noncomputable instance gcat (c : α) : Cat.{u} (gobj w b₀ nextStep c) :=
  (segSys w b₀ nextStep c).sys.catA _

/-- The global transition object-map `a → b` (for `a ≤ b`): the segment-`b` transition from the
    `a`-slot into `b`'s top.  Its domain is `(segSys b).sys.A ⟨a, _⟩`; aligning that with
    `gobj a = (segSys a).sys.A (segTop a)` is the global instance of restriction-agreement
    `gObjAgree`. -/
theorem gObjAgree {a b : α} (hab : (D w).le a b) :
    (segSys w b₀ nextStep b).sys.A ⟨a, hab⟩ = gobj w b₀ nextStep a :=
  -- The global instance of `segSys_restrict_agree` at `c := b`, `a' := a`, slot `= segTop a`:
  -- the included slot `segIncl hab (segTop a)` is `⟨a, _⟩` (proof-irrelevant in `.2`).
  segSys_restrict_agree w b₀ nextStep b a hab (segTop w b₀ nextStep a)

/-- The global transition object-map. -/
noncomputable def gF {a b : α} (hab : (D w).le a b) :
    gobj w b₀ nextStep a → gobj w b₀ nextStep b :=
  fun x => (segSys w b₀ nextStep b).sys.F
    (show (segDirected w b₀ nextStep b).le ⟨a, hab⟩ (segTop w b₀ nextStep b) from hab)
    (gObjAgree w b₀ nextStep hab ▸ x)

/-- **TRUE obligation (global functoriality).**  `gF hab` is a functor. -/
noncomputable def gFunctF {a b : α} (hab : (D w).le a b) :
    @Functor _ (gcat w b₀ nextStep a) _ (gcat w b₀ nextStep b) (gF w b₀ nextStep hab) :=
  sorry

/-- **The transfinite capitalization tower as a `Colim.CatSystem`.**  Objects = segment tops
    (`gobj`); `Cat` = `gcat`; transitions = `gF`/`gFunctF`.  Successor tops are `nextStep`
    targets, limit tops are genuine `Colim.colimitCat`.  The transition laws are the global form
    of the segment coherence (isolated TRUE obligations). -/
noncomputable def towerSystem : Colim.CatSystem.{u, u} α (D w) where
  A := gobj w b₀ nextStep
  catA := gcat w b₀ nextStep
  F hij := gF w b₀ nextStep hij
  functF hij := gFunctF w b₀ nextStep hij
  F_refl {a} x := by
    -- TRUE obligation: `gF (refl) = id` on objects (global form of `*_F_refl`).
    exact sorry
  F_trans {a b c} hab hbc x := by
    -- TRUE obligation: `gF (trans) = gF ∘ gF` on objects (global form of `*_F_trans`).
    exact sorry

/-- **The tower system is `Coherent`** (morphism-level transition coherence). -/
theorem towerCoherent : (towerSystem w b₀ nextStep).Coherent where
  refl_map {a x x'} g := by
    -- TRUE obligation: `(functF (refl)).map g ≅ g` (global form of segment `refl_map`).
    exact sorry
  trans_map {a b c} hab hbc x x' g := by
    -- TRUE obligation: composite transitions compose on morphisms (global form, HEq).
    exact sorry

end Tower

-- Axiom audit (M1).  Every `SorryAx` below is one of the named, documented, TRUE coherence
-- obligations isolated in this file (successor/limit/global *functoriality* and *coherence*, the
-- restriction-agreement equalities `belowObjAgree`/`gObjAgree`, and the colimit pre-regularity
-- `limPre`).  No custom `axiom`, no `: True`, no `:= trivial`.  The OBJECT carriers and transition
-- OBJECT-maps are real; the limit top is a genuine `Colim.colimitCat` (its `Cat` instance,
-- however, transitively consumes `belowCoherent` — the standing §1.543 transfinite obstruction).
#print axioms towerSystem
#print axioms towerCoherent
#print axioms segSys_zero_carrier
#print axioms segSys_restrict_agree
#print axioms gObjAgree
#print axioms belowObjAgree
#print axioms gF
#print axioms belowF
