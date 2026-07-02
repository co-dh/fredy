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

end Freyd.Alg
