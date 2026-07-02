/-
  Freyd & Scedrov, *Categories and Allegories* §2.157:
  PROJECTIVE PLANES, the associated modular lattice, and the DESARGUES Horn sentence.

  "A projective plane is a model of a certain two-sorted theory: the two sorts are
   points and lines; the unique predicate is an incidence relation which will be
   denoted as x ∈ A where it is understood that lower-case italics refer to points
   and upper-case to lines; the axioms are:
     · for all x, y there exists A such that x ∈ A and y ∈ A;
     · for all A, B there exists x such that x ∈ A and x ∈ B;
     · x ∈ A, x ∈ B, y ∈ A, y ∈ B imply x = y or A = B.
   An interesting projective plane is one such that each point is incident to at
   least three lines and each line is incident to at least three points.

   For every projective plane there is an associated modular lattice (hence an
   associated allegory): let 𝓛 be the disjoint union of the points and lines
   together with two new elements called 0 and 1.  We partially order 𝓛 by taking
   0 as the minimum, 1 as the maximum and using the incidence relation in between.

   The theorem of Desargues says that if two triangles are 'in perspective' then
   their corresponding sides meet on a line.  (That is, given p, a₁, a₂, b₁, b₂,
   c₁, c₂, u, v, w such that the triples ⟨p,a₁,a₂⟩, ⟨p,b₁,b₂⟩, ⟨p,c₁,c₂⟩,
   ⟨a₁,c₁,u⟩, ⟨a₂,c₂,u⟩, ⟨b₁,c₁,v⟩, ⟨b₂,c₂,v⟩, ⟨a₁,b₁,w⟩, ⟨a₂,b₂,w⟩ are colinear,
   then ⟨u,v,w⟩ is colinear.)

   Consider, now, the following Horn sentence for allegories:
       (A₁A₂ ∩ B₁B₂) ⊂ C₁C₂   implies
       (A₁°B₁ ∩ A₂B₂°) ⊂ (A₁°C₁ ∩ A₂C₂°)(C₁°B₁ ∩ C₂B₂°).
   It is easily verified for Rel(S).  Starting with a projective plane, writing
   a₁, a₂, b₁, … as A₁, A₂, B₁, …, passing to the associated modular lattice,
   viewing such as an allegory, one will see that this Horn sentence is equivalent
   with the theorem of Desargues.  (Note that Desargues implies modularity: given
   R, S, and T let A₁ = R°, A₂ = T, B₁ = S, B₂ = 1, C₁ = 1, C₂ = S.)"

  Formalised here:
  · `ProjectivePlane`, `ProjectivePlane.Interesting`, and the derived uniqueness
    facts (`lineThrough_unique`, `meetPoint_unique`).
  · `PElem P` — the associated lattice 𝓛 — with a `ModularLattice` instance
    (EVERY projective plane's lattice is modular; interestingness is NOT needed),
    hence via §2.156/§2.113 `Allegory (LMonObj (PElem P))`: the associated allegory.
  · `DesarguesHorn` — the displayed Horn sentence for allegories;
    `desarguesHorn_binRel` — its verification for concrete binary relations
    (the "easily verified for Rel(S)"); `desarguesHorn_implies_modular` — the
    book's parenthetical, over a bare lattice-with-bottom (`BotLattice`).
  · `Desargues P` — the book's ten-point formulation — and
    `desarguesHorn_implies_desargues_nondeg`: the Horn sentence in the associated
    allegory forces Desargues for nondegenerate configurations.
-/
import Fredy.S2_156_PartitionRep

universe v u

namespace Freyd.Alg

/-! ## §2.157  The two-sorted theory of projective planes -/

/-- A PROJECTIVE PLANE (§2.157): a model of the two-sorted theory whose sorts are
    points and lines, whose unique predicate is incidence `x ∈ A`, with the three
    displayed axioms. -/
structure ProjectivePlane : Type (u + 1) where
  /-- The sort of POINTS (lower-case italics in the book). -/
  Point : Type u
  /-- The sort of LINES (upper-case in the book). -/
  Line : Type u
  /-- The INCIDENCE relation `x ∈ A`. -/
  incid : Point → Line → Prop
  /-- Axiom 1: "for all x, y there exists A such that x ∈ A and y ∈ A". -/
  join_exists : ∀ x y : Point, ∃ A : Line, incid x A ∧ incid y A
  /-- Axiom 2: "for all A, B there exists x such that x ∈ A and x ∈ B". -/
  meet_exists : ∀ A B : Line, ∃ x : Point, incid x A ∧ incid x B
  /-- Axiom 3: "x ∈ A, x ∈ B, y ∈ A, y ∈ B imply x = y or A = B". -/
  unique : ∀ {x y : Point} {A B : Line},
    incid x A → incid x B → incid y A → incid y B → x = y ∨ A = B

namespace ProjectivePlane

variable (P : ProjectivePlane.{u})

/-- An INTERESTING projective plane (§2.157): each point is incident to at least
    three lines and each line is incident to at least three points ("at least
    three" = a pairwise-distinct triple). -/
def Interesting : Prop :=
  (∀ x : P.Point, ∃ A B C : P.Line, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      P.incid x A ∧ P.incid x B ∧ P.incid x C) ∧
  (∀ A : P.Line, ∃ x y z : P.Point, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      P.incid x A ∧ P.incid y A ∧ P.incid z A)

/-! ### Derived uniqueness: axiom 3 splits the two existence axioms into
    unique existence, once the given pair is distinct. -/

variable {P}

/-- Two DISTINCT points lie on a UNIQUE common line (axioms 1 + 3). -/
theorem lineThrough_unique {x y : P.Point} (hxy : x ≠ y) :
    ∃ A : P.Line, (P.incid x A ∧ P.incid y A) ∧
      ∀ B : P.Line, P.incid x B ∧ P.incid y B → B = A := by
  obtain ⟨A, hA⟩ := P.join_exists x y
  exact ⟨A, hA, fun B hB => (P.unique hB.1 hA.1 hB.2 hA.2).resolve_left hxy⟩

/-- Two DISTINCT lines meet in a UNIQUE point (axioms 2 + 3). -/
theorem meetPoint_unique {A B : P.Line} (hAB : A ≠ B) :
    ∃ x : P.Point, (P.incid x A ∧ P.incid x B) ∧
      ∀ y : P.Point, P.incid y A ∧ P.incid y B → y = x := by
  obtain ⟨x, hx⟩ := P.meet_exists A B
  exact ⟨x, hx, fun y hy => (P.unique hy.1 hy.2 hx.1 hx.2).resolve_right hAB⟩

variable (P)

/-- A chosen common line of two points (axiom 1 via choice); for `x ≠ y` it is THE
    line through them (`lineThrough_eq`). -/
noncomputable def lineThrough (x y : P.Point) : P.Line :=
  Classical.choose (P.join_exists x y)

theorem lineThrough_incid_left (x y : P.Point) :
    P.incid x (P.lineThrough x y) :=
  (Classical.choose_spec (P.join_exists x y)).1

theorem lineThrough_incid_right (x y : P.Point) :
    P.incid y (P.lineThrough x y) :=
  (Classical.choose_spec (P.join_exists x y)).2

/-- A chosen common point of two lines (axiom 2 via choice); for `A ≠ B` it is THE
    meet point (`meetPoint_eq`). -/
noncomputable def meetPoint (A B : P.Line) : P.Point :=
  Classical.choose (P.meet_exists A B)

theorem meetPoint_incid_left (A B : P.Line) :
    P.incid (P.meetPoint A B) A :=
  (Classical.choose_spec (P.meet_exists A B)).1

theorem meetPoint_incid_right (A B : P.Line) :
    P.incid (P.meetPoint A B) B :=
  (Classical.choose_spec (P.meet_exists A B)).2

variable {P}

/-- Any line through two DISTINCT points is `lineThrough` (uniqueness, axiom 3). -/
theorem lineThrough_eq {x y : P.Point} (hxy : x ≠ y) {A : P.Line}
    (hx : P.incid x A) (hy : P.incid y A) : A = P.lineThrough x y :=
  (P.unique hx (P.lineThrough_incid_left x y) hy
    (P.lineThrough_incid_right x y)).resolve_left hxy

/-- Any common point of two DISTINCT lines is `meetPoint` (uniqueness, axiom 3). -/
theorem meetPoint_eq {A B : P.Line} (hAB : A ≠ B) {x : P.Point}
    (hA : P.incid x A) (hB : P.incid x B) : x = P.meetPoint A B :=
  (P.unique hA hB (P.meetPoint_incid_left A B)
    (P.meetPoint_incid_right A B)).resolve_right hAB

end ProjectivePlane

/-! ## The associated lattice 𝓛(P) (§2.157)

  "let 𝓛 be the disjoint union of the points and lines together with two new
   elements called 0 and 1.  We partially order 𝓛 by taking 0 as the minimum,
   1 as the maximum and using the incidence relation in between." -/

/-- 𝓛: disjoint union of points and lines plus `0` (`bot`) and `1` (`top`). -/
inductive PElem (P : ProjectivePlane.{u}) : Type u where
  | bot : PElem P
  | pt (x : P.Point) : PElem P
  | ln (A : P.Line) : PElem P
  | top : PElem P

namespace PElem

variable {P : ProjectivePlane.{u}}

/-- The partial order on 𝓛: `0` minimum, `1` maximum, incidence in between
    (points and lines are otherwise incomparable; each rank is discrete). -/
def le : PElem P → PElem P → Prop
  | bot, _ => True
  | pt _, bot => False
  | pt x, pt y => x = y
  | pt x, ln A => P.incid x A
  | pt _, top => True
  | ln _, bot => False
  | ln _, pt _ => False
  | ln A, ln B => A = B
  | ln _, top => True
  | top, bot => False
  | top, pt _ => False
  | top, ln _ => False
  | top, top => True

theorem le_refl : ∀ a : PElem P, a.le a
  | bot => trivial
  | pt _ => rfl
  | ln _ => rfl
  | top => trivial

theorem le_trans {a b c : PElem P} (hab : a.le b) (hbc : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;> simp_all [le]

theorem le_antisymm {a b : PElem P} (hab : a.le b) (hba : b.le a) : a = b := by
  cases a <;> cases b <;> simp_all [le]

theorem bot_le (a : PElem P) : (bot : PElem P).le a := trivial

theorem le_top : ∀ a : PElem P, a.le top
  | bot => trivial
  | pt _ => trivial
  | ln _ => trivial
  | top => trivial

theorem eq_top_of_top_le {a : PElem P} (h : (top : PElem P).le a) : a = top := by
  cases a <;> simp_all [le]

/-! ### Meet and join

  Total functions by case analysis; the witnesses for the geometric cases are
  chosen via `lineThrough`/`meetPoint` (axioms 1 and 2 through `Classical.choice`)
  and the distinctness splits use classical decidability. -/

open Classical in
/-- Lattice JOIN on 𝓛.  Cases: `⊥` is a unit and `⊤` absorbs; two points join to
    the line through them (or the point itself, if equal); a point and a line join
    to the line when incident, else to `⊤`; two distinct lines join to `⊤`. -/
noncomputable def join : PElem P → PElem P → PElem P
  | bot, b => b
  | pt x, bot => pt x
  | pt x, pt y => if x = y then pt x else ln (P.lineThrough x y)
  | pt x, ln A => if P.incid x A then ln A else top
  | pt _, top => top
  | ln A, bot => ln A
  | ln A, pt y => if P.incid y A then ln A else top
  | ln A, ln B => if A = B then ln A else top
  | ln _, top => top
  | top, _ => top

open Classical in
/-- Lattice MEET on 𝓛, dual to `join`: two distinct points meet in `⊥`; a point
    and a line meet in the point when incident, else `⊥`; two distinct lines meet
    in their common point (axiom 2). -/
noncomputable def meet : PElem P → PElem P → PElem P
  | bot, _ => bot
  | pt _, bot => bot
  | pt x, pt y => if x = y then pt x else bot
  | pt x, ln A => if P.incid x A then pt x else bot
  | pt x, top => pt x
  | ln _, bot => bot
  | ln A, pt y => if P.incid y A then pt y else bot
  | ln A, ln B => if A = B then ln A else pt (P.meetPoint A B)
  | ln A, top => ln A
  | top, b => b

/-! ### Evaluation lemmas (one per `if`-case; the constructor cases are `rfl`) -/

theorem join_bot_right : ∀ a : PElem P, a.join bot = a
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

theorem join_top_left (b : PElem P) : (top : PElem P).join b = top := rfl

theorem join_top_right : ∀ a : PElem P, a.join top = top
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

theorem join_pt_pt_self (x : P.Point) : (pt x).join (pt x) = pt x := by
  simp [join]

theorem join_pt_pt_ne {x y : P.Point} (h : x ≠ y) :
    (pt x).join (pt y) = ln (P.lineThrough x y) := by
  simp [join, h]

theorem join_pt_ln_incid {x : P.Point} {A : P.Line} (h : P.incid x A) :
    (pt x).join (ln A) = ln A := by
  simp [join, h]

theorem join_pt_ln_not {x : P.Point} {A : P.Line} (h : ¬P.incid x A) :
    (pt x).join (ln A) = top := by
  simp [join, h]

theorem join_ln_pt_incid {A : P.Line} {y : P.Point} (h : P.incid y A) :
    (ln A).join (pt y) = ln A := by
  simp [join, h]

theorem join_ln_pt_not {A : P.Line} {y : P.Point} (h : ¬P.incid y A) :
    (ln A).join (pt y) = top := by
  simp [join, h]

theorem join_ln_ln_self (A : P.Line) : (ln A).join (ln A) = ln A := by
  simp [join]

theorem join_ln_ln_ne {A B : P.Line} (h : A ≠ B) : (ln A).join (ln B) = top := by
  simp [join, h]

theorem meet_top_left (b : PElem P) : (top : PElem P).meet b = b := rfl

theorem meet_top_right : ∀ a : PElem P, a.meet top = a
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

theorem meet_pt_pt_self (x : P.Point) : (pt x).meet (pt x) = pt x := by
  simp [meet]

theorem meet_pt_pt_ne {x y : P.Point} (h : x ≠ y) :
    (pt x).meet (pt y) = bot := by
  simp [meet, h]

theorem meet_pt_ln_incid {x : P.Point} {A : P.Line} (h : P.incid x A) :
    (pt x).meet (ln A) = pt x := by
  simp [meet, h]

theorem meet_pt_ln_not {x : P.Point} {A : P.Line} (h : ¬P.incid x A) :
    (pt x).meet (ln A) = bot := by
  simp [meet, h]

theorem meet_ln_pt_incid {A : P.Line} {y : P.Point} (h : P.incid y A) :
    (ln A).meet (pt y) = pt y := by
  simp [meet, h]

theorem meet_ln_pt_not {A : P.Line} {y : P.Point} (h : ¬P.incid y A) :
    (ln A).meet (pt y) = bot := by
  simp [meet, h]

theorem meet_ln_ln_self (A : P.Line) : (ln A).meet (ln A) = ln A := by
  simp [meet]

theorem meet_ln_ln_ne {A B : P.Line} (h : A ≠ B) :
    (ln A).meet (ln B) = pt (P.meetPoint A B) := by
  simp [meet, h]

/-! ### Order characterisations: `join` is the lub, `meet` is the glb

  Everything equational below follows from these two case analyses ONCE,
  generically.  Axiom 3 (via `lineThrough_eq`/`meetPoint_eq`) is what makes
  the geometric cases work. -/

/-- `a ⊔ b ⩽ c ↔ a ⩽ c ∧ b ⩽ c`: `join` is the least upper bound. -/
theorem join_le_iff {a b c : PElem P} : (a.join b).le c ↔ a.le c ∧ b.le c := by
  cases a with
  | bot => simp [le, join]
  | top =>
    -- `⊤ ⊔ b = ⊤`; forward direction forces `c = ⊤`, whence `b ⩽ c` trivially.
    exact ⟨fun h => ⟨h, by rw [eq_top_of_top_le h]; exact le_top b⟩, fun ⟨h1, _⟩ => h1⟩
  | pt x =>
    cases b with
    | bot => simp [le, join]
    | top => cases c <;> simp [le, join]
    | pt y =>
      by_cases hxy : x = y
      · subst hxy; rw [join_pt_pt_self]; simp
      · rw [join_pt_pt_ne hxy]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxy (h1.trans h2.symm)⟩
        | ln C =>
          simp only [le]
          exact ⟨fun h => h ▸ ⟨P.lineThrough_incid_left x y, P.lineThrough_incid_right x y⟩,
                 fun ⟨h1, h2⟩ => (ProjectivePlane.lineThrough_eq hxy h1 h2).symm⟩
    | ln A =>
      by_cases hxA : P.incid x A
      · rw [join_pt_ln_incid hxA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨fun h => ⟨h ▸ hxA, h⟩, And.right⟩
      · rw [join_pt_ln_not hxA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxA (h2.symm ▸ h1)⟩
  | ln A =>
    cases b with
    | bot => simp [le, join]
    | top => cases c <;> simp [le, join]
    | pt y =>
      by_cases hyA : P.incid y A
      · rw [join_ln_pt_incid hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨fun h => ⟨h, h ▸ hyA⟩, And.left⟩
      · rw [join_ln_pt_not hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hyA (h1.symm ▸ h2)⟩
    | ln B =>
      by_cases hAB : A = B
      · subst hAB; rw [join_ln_ln_self]; simp
      · rw [join_ln_ln_ne hAB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hAB (h1.trans h2.symm)⟩

/-- `c ⩽ a ⊓ b ↔ c ⩽ a ∧ c ⩽ b`: `meet` is the greatest lower bound. -/
theorem le_meet_iff {a b c : PElem P} : c.le (a.meet b) ↔ c.le a ∧ c.le b := by
  cases a with
  | bot => cases c <;> simp [le, meet]
  | top => cases c <;> simp [le, meet]
  | pt x =>
    cases b with
    | bot => cases c <;> simp [le, meet]
    | top => cases c <;> simp [le, meet]
    | pt y =>
      by_cases hxy : x = y
      · subst hxy; rw [meet_pt_pt_self]; simp
      · rw [meet_pt_pt_ne hxy]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxy (h1.symm.trans h2)⟩
    | ln B =>
      by_cases hxB : P.incid x B
      · rw [meet_pt_ln_incid hxB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h, h.symm ▸ hxB⟩, And.left⟩
      · rw [meet_pt_ln_not hxB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxB (h1 ▸ h2)⟩
  | ln A =>
    cases b with
    | bot => cases c <;> simp [le, meet]
    | top => cases c <;> simp [le, meet]
    | pt y =>
      by_cases hyA : P.incid y A
      · rw [meet_ln_pt_incid hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h.symm ▸ hyA, h⟩, And.right⟩
      · rw [meet_ln_pt_not hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hyA (h2 ▸ h1)⟩
    | ln B =>
      by_cases hAB : A = B
      · subst hAB; rw [meet_ln_ln_self]
        exact ⟨fun h => ⟨h, h⟩, And.left⟩
      · rw [meet_ln_ln_ne hAB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hAB (h1.symm.trans h2)⟩
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h.symm ▸ P.meetPoint_incid_left A B,
                           h.symm ▸ P.meetPoint_incid_right A B⟩,
                 fun ⟨h1, h2⟩ => ProjectivePlane.meetPoint_eq hAB h1 h2⟩

/-! ### Derived lub/glb API (from the two characterisations, generically) -/

theorem le_join_left (a b : PElem P) : a.le (a.join b) :=
  (join_le_iff.mp (le_refl _)).1

theorem le_join_right (a b : PElem P) : b.le (a.join b) :=
  (join_le_iff.mp (le_refl _)).2

theorem join_le {a b c : PElem P} (h1 : a.le c) (h2 : b.le c) : (a.join b).le c :=
  join_le_iff.mpr ⟨h1, h2⟩

theorem meet_le_left (a b : PElem P) : (a.meet b).le a :=
  (le_meet_iff.mp (le_refl _)).1

theorem meet_le_right (a b : PElem P) : (a.meet b).le b :=
  (le_meet_iff.mp (le_refl _)).2

theorem le_meet {a b c : PElem P} (h1 : c.le a) (h2 : c.le b) : c.le (a.meet b) :=
  le_meet_iff.mpr ⟨h1, h2⟩

/-- The `ModularLattice` order (`a ⊓ b = a`) coincides with `le`. -/
theorem le_iff_meet_eq {a b : PElem P} : a.le b ↔ a.meet b = a :=
  ⟨fun h => le_antisymm (meet_le_left a b) (le_meet (le_refl a) h),
   fun h => h ▸ meet_le_right a b⟩

/-! ### The equational lattice laws (each once, from lub/glb + antisymmetry) -/

theorem meet_idem (a : PElem P) : a.meet a = a :=
  le_antisymm (meet_le_left a a) (le_meet (le_refl a) (le_refl a))

theorem meet_comm (a b : PElem P) : a.meet b = b.meet a :=
  le_antisymm (le_meet (meet_le_right a b) (meet_le_left a b))
    (le_meet (meet_le_right b a) (meet_le_left b a))

theorem meet_assoc (a b c : PElem P) : a.meet (b.meet c) = (a.meet b).meet c :=
  le_antisymm
    (le_meet
      (le_meet (meet_le_left a _) (le_trans (meet_le_right a _) (meet_le_left b c)))
      (le_trans (meet_le_right a _) (meet_le_right b c)))
    (le_meet (le_trans (meet_le_left _ c) (meet_le_left a b))
      (le_meet (le_trans (meet_le_left _ c) (meet_le_right a b)) (meet_le_right _ c)))

theorem join_idem (a : PElem P) : a.join a = a :=
  le_antisymm (join_le (le_refl a) (le_refl a)) (le_join_left a a)

theorem join_comm (a b : PElem P) : a.join b = b.join a :=
  le_antisymm (join_le (le_join_right b a) (le_join_left b a))
    (join_le (le_join_right a b) (le_join_left a b))

theorem join_assoc (a b c : PElem P) : a.join (b.join c) = (a.join b).join c :=
  le_antisymm
    (join_le (le_trans (le_join_left a b) (le_join_left _ c))
      (join_le (le_trans (le_join_right a b) (le_join_left _ c)) (le_join_right _ c)))
    (join_le
      (join_le (le_join_left a _) (le_trans (le_join_left b c) (le_join_right a _)))
      (le_trans (le_join_right b c) (le_join_right a _)))

theorem meet_absorb (a b : PElem P) : a.meet (a.join b) = a :=
  le_antisymm (meet_le_left _ _) (le_meet (le_refl a) (le_join_left a b))

theorem join_absorb (a b : PElem P) : a.join (a.meet b) = a :=
  le_antisymm (join_le (le_refl a) (meet_le_left a b)) (le_join_left _ _)

theorem bot_join (a : PElem P) : (bot : PElem P).join a = a := rfl

/-! ### MODULARITY (§2.157 headline)

  `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c`.  The `⊒` half holds in any lattice; the
  `⊑` half is the case analysis below.  Since 𝓛 has height 4, once the trivial
  ranks (`⊥`, `⊤`, `c = a`) are dispatched generically, the only case with
  content is `c = pt y ⩽ a = ln A`, and THE GEOMETRY ENTERS in exactly two
  spots, both instances of axiom 3:
  · `b = pt x` with `x ≠ y`, `A ≠ (line through x, y)`: the two lines meet in
    the unique point `y` (`meetPoint_eq`), so the meet is already below `c`;
  · `b = ln B` with `y ∉ B`: `z := meetPoint A B` and `y` are two distinct
    points of `A`, so `A` IS the line through them (`lineThrough_eq`), i.e.
    `(a ⊓ b) ⊔ c = a`.
  Interestingness is NOT needed: EVERY projective plane's lattice is modular. -/

/-- The trivial `c = a` instance of the modular inequality. -/
theorem modular_self (a b : PElem P) : (a.meet (b.join a)).le ((a.meet b).join a) :=
  le_trans (meet_le_left _ _) (le_join_right _ _)

/-- The hard modular inequality `c ⩽ a → a ⊓ (b ⊔ c) ⩽ (a ⊓ b) ⊔ c`. -/
theorem modular_hard {a b c : PElem P} (hca : c.le a) :
    (a.meet (b.join c)).le ((a.meet b).join c) := by
  cases c with
  | bot => rw [join_bot_right]; exact le_join_left _ _
  | top =>
    cases a with
    | top => exact le_trans (le_top _) (le_join_right _ _)
    | bot => simp [le] at hca
    | pt x => simp [le] at hca
    | ln A => simp [le] at hca
  | pt y =>
    cases a with
    | bot => simp [le] at hca
    | top => rw [meet_top_left, meet_top_left]; exact le_refl _
    | pt x =>
      have h : y = x := hca
      subst h
      exact modular_self _ _
    | ln A =>
      have hyA : P.incid y A := hca
      cases b with
      | bot => exact le_trans (meet_le_right _ _) (le_join_right _ _)
      | top => rw [join_top_left, meet_top_right]; exact le_join_left _ _
      | pt x =>
        by_cases hxy : x = y
        · subst hxy; rw [join_pt_pt_self]; exact le_join_left _ _
        · rw [join_pt_pt_ne hxy]
          by_cases hAL : A = P.lineThrough x y
          · -- `A` IS the line through `x, y`; both sides collapse to `ln A`.
            have hxA : P.incid x A := by rw [hAL]; exact P.lineThrough_incid_left x y
            rw [meet_ln_pt_incid hxA, join_pt_pt_ne hxy, ← hAL, meet_ln_ln_self]
            exact le_refl _
          · -- GEOMETRY: `A` and the line through `x, y` meet in the unique
            -- common point, which is `y` (axiom 3) — so the meet is `c` itself.
            have hy : y = P.meetPoint A (P.lineThrough x y) :=
              ProjectivePlane.meetPoint_eq hAL hyA (P.lineThrough_incid_right x y)
            rw [meet_ln_ln_ne hAL, ← hy]
            exact le_join_right _ _
      | ln B =>
        by_cases hyB : P.incid y B
        · rw [join_ln_pt_incid hyB]; exact le_join_left _ _
        · -- GEOMETRY: `z := meetPoint A B` and `y` are distinct points of `A`
          -- (`y ∉ B` but `z ∈ B`), so `A` is the line through `z, y` (axiom 3).
          have hAB : A ≠ B := fun h => hyB (h ▸ hyA)
          have hz : P.incid (P.meetPoint A B) A := P.meetPoint_incid_left A B
          have hzy : P.meetPoint A B ≠ y :=
            fun h => hyB (h ▸ P.meetPoint_incid_right A B)
          rw [join_ln_pt_not hyB, meet_top_right, meet_ln_ln_ne hAB,
            join_pt_pt_ne hzy]
          exact (ProjectivePlane.lineThrough_eq hzy hz hyA :
            A = P.lineThrough (P.meetPoint A B) y)
  | ln A' =>
    cases a with
    | bot => simp [le] at hca
    | pt x => simp [le] at hca
    | top => rw [meet_top_left, meet_top_left]; exact le_refl _
    | ln A =>
      have h : A' = A := hca
      subst h
      exact modular_self _ _

/-- **𝓛(P) is modular** (§2.157): `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c`. -/
theorem modular_eq {a b c : PElem P} (hca : c.le a) :
    a.meet (b.join c) = (a.meet b).join c :=
  le_antisymm (modular_hard hca)
    (le_meet (join_le (meet_le_left a b) hca)
      (join_le (le_trans (meet_le_right a b) (le_join_left b c)) (le_join_right b c)))

end PElem

/-- **§2.157, "for every projective plane there is an associated modular
    lattice"** — the `ModularLattice` (§2.156) instance on 𝓛(P). -/
noncomputable instance instModularLatticePElem (P : ProjectivePlane.{u}) :
    ModularLattice (PElem P) where
  meet := PElem.meet
  join := PElem.join
  bot := PElem.bot
  meet_idem := PElem.meet_idem
  meet_comm := PElem.meet_comm
  meet_assoc := PElem.meet_assoc
  join_idem := PElem.join_idem
  join_comm := PElem.join_comm
  join_assoc := PElem.join_assoc
  meet_absorb := PElem.meet_absorb
  join_absorb := PElem.join_absorb
  bot_join := PElem.bot_join
  modular := fun _ _ _ h =>
    PElem.modular_eq (PElem.le_iff_meet_eq.mpr h)

/-- "(hence an associated allegory)": the §2.156/§2.113 bridge fires on 𝓛(P). -/
noncomputable example (P : ProjectivePlane.{u}) :
    Allegory (LMonObj (PElem P)) := inferInstance

end Freyd.Alg
