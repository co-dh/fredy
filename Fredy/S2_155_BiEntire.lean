/-
  Freyd & Scedrov, *Categories and Allegories* §2.155

  INDEPENDENCE OF THE MODULAR IDENTITY.

  Book (§2.155, verbatim): "Let B be the subcategory of Rel(S) defined by
  (A →R B) ∈ B iff either R = ∅ or both R and R° are entire.  B is not a
  suballegory of Rel(S): it is closed with respect to composition and
  reciprocation but not with respect to intersection.  Nonetheless, each
  hom-set of B is easily seen to be a semi-lattice.  All axioms for
  allegories hold except for the modular identity.

  B is tabular (a tabulation that works in Rel(S) works in B).  Hence the
  modular identity is not a consequence of tabularity.  Map(B) is not a
  regular category: it has equalizers and a terminator but it does not
  have products."

  We work at the plain binary-relation level: a Rel(S)-morphism A → B is a
  matrix `A → B → Prop`, composition is diagram-order relational composition
  (`xy` = first x then y), the identity is `Eq`, reciprocation is
  transposition.  The B-INTERSECTION — the semi-lattice meet of the hom-sets
  of B — is the pointwise intersection GUARDED by the proposition that it is
  bi-entire (`interB`); no decidability is needed because bi-entirety is
  upward closed, so any nonzero lower bound in B already forces the guard.
-/

import Fredy.S2_1

universe u

namespace Freyd.Alg

/-! ## §2.155 (i)  Relations of B: `∅` or bi-entire

  Relation-level layer: everything is proved for plain matrices
  `A → B → Prop` first; the hom-level statements below are thin wrappers. -/

/-- `R` and `R°` are both ENTIRE (§2.155): every `a` is related to some `b`
    and every `b` to some `a`.  (Named `BiEntire` to avoid clashing with the
    allegory-level `Entire` of §2.13.) -/
@[reducible] def BiEntire {A B : Type u} (R : A → B → Prop) : Prop :=
  (∀ a, ∃ b, R a b) ∧ (∀ b, ∃ a, R a b)

/-- Membership in B (§2.155): `R = ∅` or `R` is bi-entire. -/
@[reducible] def IsB {A B : Type u} (R : A → B → Prop) : Prop :=
  (∀ a b, ¬ R a b) ∨ BiEntire R

/-- Pointwise intersection — the intersection of Rel(S), which B is NOT
    closed under (§2.155). -/
@[reducible] def pInter {A B : Type u} (R S : A → B → Prop) : A → B → Prop :=
  fun a b => R a b ∧ S a b

/-- Diagram-order relational composition: `bComp R S a c` iff some `b` has
    `R a b` and `S b c` (first `R`, then `S`). -/
@[reducible] def bComp {A B C : Type u} (R : A → B → Prop) (S : B → C → Prop) :
    A → C → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

/-- Reciprocation (transposition): `R° b a` iff `R a b`. -/
@[reducible] def bRecip {A B : Type u} (R : A → B → Prop) : B → A → Prop :=
  fun b a => R a b

/-- The B-INTERSECTION: the pointwise intersection guarded by the (undecided)
    proposition that it is bi-entire.  If the guard holds this IS `R ∩ S`;
    otherwise it is `∅`.  This is the semi-lattice meet of the hom-sets of B
    (§2.155: "each hom-set of B is easily seen to be a semi-lattice"). -/
@[reducible] def interB {A B : Type u} (R S : A → B → Prop) : A → B → Prop :=
  fun a b => R a b ∧ S a b ∧ BiEntire (pInter R S)

/-- Bi-entirety is UPWARD CLOSED — the engine behind every guard argument. -/
theorem biEntire_mono {A B : Type u} {R S : A → B → Prop}
    (hsub : ∀ a b, R a b → S a b) (h : BiEntire R) : BiEntire S :=
  ⟨fun a => (h.1 a).elim fun b hb => ⟨b, hsub a b hb⟩,
   fun b => (h.2 b).elim fun a ha => ⟨a, hsub a b ha⟩⟩

/-- The identity relation is bi-entire. -/
theorem biEntire_eq {A : Type u} : BiEntire (Eq : A → A → Prop) :=
  ⟨fun a => ⟨a, rfl⟩, fun a => ⟨a, rfl⟩⟩

/-- Bi-entire relations compose to bi-entire relations. -/
theorem biEntire_comp {A B C : Type u} {R : A → B → Prop} {S : B → C → Prop}
    (hR : BiEntire R) (hS : BiEntire S) : BiEntire (bComp R S) :=
  ⟨fun a => (hR.1 a).elim fun b hb => (hS.1 b).elim fun c hc => ⟨c, b, hb, hc⟩,
   fun c => (hS.2 c).elim fun b hb => (hR.2 b).elim fun a ha => ⟨a, b, ha, hb⟩⟩

/-- A relation is bi-entire iff its reciprocal is (definitional swap). -/
theorem biEntire_recip {A B : Type u} {R : A → B → Prop} (h : BiEntire R) :
    BiEntire (bRecip R) :=
  ⟨h.2, h.1⟩

/-! ### Closure of B under the categorical structure (§2.155: "it is closed
  with respect to composition and reciprocation") -/

/-- The identity is in B. -/
theorem isB_eq {A : Type u} : IsB (Eq : A → A → Prop) := Or.inr biEntire_eq

/-- B is closed under composition: bi-entire ∘ bi-entire is bi-entire, and
    anything composed with `∅` is `∅`. -/
theorem isB_comp {A B C : Type u} {R : A → B → Prop} {S : B → C → Prop}
    (hR : IsB R) (hS : IsB S) : IsB (bComp R S) := by
  rcases hR with hR | hR
  · exact Or.inl fun a c h => h.elim fun b hb => hR a b hb.1
  rcases hS with hS | hS
  · exact Or.inl fun a c h => h.elim fun b hb => hS b c hb.2
  · exact Or.inr (biEntire_comp hR hS)

/-- B is closed under reciprocation. -/
theorem isB_recip {A B : Type u} {R : A → B → Prop} (h : IsB R) : IsB (bRecip R) :=
  h.elim (fun he => Or.inl fun b a hba => he a b hba)
    (fun hb => Or.inr (biEntire_recip hb))

/-- The guarded intersection is in B: if the guard holds it IS the pointwise
    intersection (hence bi-entire); if not, it is `∅`. -/
theorem isB_interB {A B : Type u} (R S : A → B → Prop) : IsB (interB R S) :=
  (Classical.em (BiEntire (pInter R S))).elim
    (fun hg => Or.inr (biEntire_mono (fun _ _ h => ⟨h.1, h.2, hg⟩) hg))
    (fun hg => Or.inl fun _ _ h => hg h.2.2)

/-! ### `interB` is the greatest lower bound in B

  KEY LEMMA: since bi-entirety is upward closed, a NONZERO lower bound
  `T ∈ B` of `R` and `S` forces the pointwise intersection to be bi-entire —
  so the guard costs nothing on any nonzero lower bound. -/

/-- KEY LEMMA (upward closure): if `T ∈ B`, `T ⊆ R`, `T ⊆ S` and `T` is
    nonzero, then `R ∩ S` (pointwise) is bi-entire. -/
theorem guard_of_lowerBound {A B : Type u} {T R S : A → B → Prop} (hT : IsB T)
    (hTR : ∀ a b, T a b → R a b) (hTS : ∀ a b, T a b → S a b)
    {a : A} {b : B} (hab : T a b) : BiEntire (pInter R S) :=
  hT.elim (fun he => absurd hab (he a b))
    (fun hbe => biEntire_mono (fun x y h => ⟨hTR x y h, hTS x y h⟩) hbe)

/-- `interB R S` is a lower bound of `R`. -/
theorem interB_le_left {A B : Type u} (R S : A → B → Prop) :
    ∀ a b, interB R S a b → R a b := fun _ _ h => h.1

/-- `interB R S` is a lower bound of `S`. -/
theorem interB_le_right {A B : Type u} (R S : A → B → Prop) :
    ∀ a b, interB R S a b → S a b := fun _ _ h => h.2.1

/-- `interB` is the GREATEST lower bound among B-relations: any `T ∈ B` below
    `R` and `S` is below `interB R S` (its nonzero points force the guard). -/
theorem interB_glb {A B : Type u} {T R S : A → B → Prop} (hT : IsB T)
    (hTR : ∀ a b, T a b → R a b) (hTS : ∀ a b, T a b → S a b) :
    ∀ a b, T a b → interB R S a b :=
  fun a b h => ⟨hTR a b h, hTS a b h, guard_of_lowerBound hT hTR hTS h⟩

/-- The B-order collapses to pointwise inclusion: for `X ∈ B`,
    `interB X Y = X` (i.e. `X ⊑ Y` in B) iff `X ⊆ Y` pointwise. -/
theorem interB_eq_left {A B : Type u} {X Y : A → B → Prop} (hX : IsB X)
    (hsub : ∀ a b, X a b → Y a b) (a : A) (b : B) : interB X Y a b ↔ X a b :=
  ⟨fun h => h.1, fun h => ⟨h, hsub a b h, guard_of_lowerBound hX (fun _ _ => id) hsub h⟩⟩

/-! ## §2.155 (ii)  The category B -/

/-- Objects of B: the objects of Rel(S), i.e. sets. -/
def BObj : Type (u + 1) := Type u

/-- View a set as an object of B. -/
abbrev BObj.of (A : Type u) : BObj.{u} := A

/-- Hom-sets of B (§2.155): relations that are `∅` or bi-entire. -/
def BHom (A B : Type u) : Type u := { R : A → B → Prop // IsB R }

/-- Hom extensionality: B-morphisms are equal iff pointwise equivalent. -/
theorem BHom.ext {A B : Type u} {R S : BHom A B} (h : ∀ a b, R.val a b ↔ S.val a b) :
    R = S :=
  Subtype.ext (funext fun a => funext fun b => propext (h a b))

/-- Pointwise reading of an equality of B-morphisms. -/
theorem BHom.congr {A B : Type u} {R S : BHom A B} (h : R = S) (a : A) (b : B) :
    R.val a b ↔ S.val a b := by rw [h]

/-- Identity of B: the identity relation. -/
@[reducible] def BHom.id (A : Type u) : BHom A A := ⟨Eq, isB_eq⟩

/-- Composition of B (diagram order). -/
@[reducible] def BHom.comp {A B C : Type u} (R : BHom A B) (S : BHom B C) : BHom A C :=
  ⟨bComp R.val S.val, isB_comp R.property S.property⟩

/-- Reciprocation of B. -/
@[reducible] def BHom.recip {A B : Type u} (R : BHom A B) : BHom B A :=
  ⟨bRecip R.val, isB_recip R.property⟩

/-- The semi-lattice meet of the hom-sets of B. -/
@[reducible] def BHom.inter {A B : Type u} (R S : BHom A B) : BHom A B :=
  ⟨interB R.val S.val, isB_interB R.val S.val⟩

/-- `1 ≫ R = R` at the relation level. -/
theorem bComp_eq_left {A B : Type u} (R : A → B → Prop) (a : A) (b : B) :
    bComp Eq R a b ↔ R a b :=
  ⟨fun h => by obtain ⟨x, rfl, hx⟩ := h; exact hx, fun h => ⟨a, rfl, h⟩⟩

/-- `R ≫ 1 = R` at the relation level. -/
theorem bComp_eq_right {A B : Type u} (R : A → B → Prop) (a : A) (b : B) :
    bComp R Eq a b ↔ R a b :=
  ⟨fun h => by obtain ⟨x, hx, rfl⟩ := h; exact hx, fun h => ⟨b, h, rfl⟩⟩

/-- Associativity of relational composition. -/
theorem bComp_assoc {A B C D : Type u} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (a : A) (d : D) :
    bComp (bComp R S) T a d ↔ bComp R (bComp S T) a d :=
  ⟨fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩,
   fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩⟩

/-- §2.155: B is a category ("the subcategory of Rel(S) defined by
    (A →R B) ∈ B iff either R = ∅ or both R and R° are entire"). -/
instance instCatB : Cat.{u, u + 1} BObj.{u} where
  Hom A B := BHom A B
  id A := BHom.id A
  comp R S := BHom.comp R S
  id_comp R := BHom.ext fun a b => bComp_eq_left R.val a b
  comp_id R := BHom.ext fun a b => bComp_eq_right R.val a b
  assoc R S T := BHom.ext fun a d => bComp_assoc R.val S.val T.val a d

/-! ## §2.155 (iii)  B is NOT closed under the intersection of Rel(S)

  Witness: `wR : Two → Three` relates `e0↦e0, e1↦e1, e1↦e2`; `wS : Three → Two`
  relates `e0↦e0, e1↦e1, e2↦e0`.  Both `wR` and `wS°` are bi-entire, but the
  pointwise intersection `wR ∩ wS° = {(e0,e0),(e1,e1)}` misses `e2 : Three`,
  so it is entire but not CO-entire — and it is nonzero, so it is not in B. -/

/-- Two-element carrier for the §2.155 counterexamples. -/
inductive Two : Type where
  | e0 | e1

/-- Three-element carrier for the §2.155 counterexamples. -/
inductive Three : Type where
  | e0 | e1 | e2

/-- The relation `{(e0,e0), (e1,e1), (e1,e2)} : Two → Three`. -/
@[reducible] def wR : Two → Three → Prop := fun a b =>
  (a = .e0 ∧ b = .e0) ∨ (a = .e1 ∧ b = .e1) ∨ (a = .e1 ∧ b = .e2)

/-- The relation `{(e0,e0), (e1,e1), (e2,e0)} : Three → Two`. -/
@[reducible] def wS : Three → Two → Prop := fun b c =>
  (b = .e0 ∧ c = .e0) ∨ (b = .e1 ∧ c = .e1) ∨ (b = .e2 ∧ c = .e0)

theorem wR_biEntire : BiEntire wR :=
  ⟨fun a => match a with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
   fun b => match b with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | .e2 => ⟨.e1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩

theorem wS_biEntire : BiEntire wS :=
  ⟨fun b => match b with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | .e2 => ⟨.e0, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩,
   fun c => match c with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩

/-- The pointwise intersection `wR ∩ wS°` is not bi-entire: nothing is related
    to `e2 : Three` (`wR · e2` forces `e1`, `wS e2 ·` forces `e0`). -/
theorem wRSo_not_biEntire : ¬ BiEntire (pInter wR (bRecip wS)) := fun h => by
  obtain ⟨a, hR, hS⟩ := h.2 Three.e2
  rcases hR with ⟨-, h0⟩ | ⟨-, h0⟩ | ⟨ha, -⟩
  · exact nomatch h0
  · exact nomatch h0
  · rcases hS with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ha'⟩
    · exact nomatch h0
    · exact nomatch h0
    · subst ha; exact nomatch ha'

/-- `wR ∩ wS°` is nonzero (it contains `(e0, e0)`) yet not bi-entire — so it
    is not in B. -/
theorem wRSo_not_isB : ¬ IsB (pInter wR (bRecip wS)) := fun h =>
  h.elim (fun he => he Two.e0 Three.e0 ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩)
    wRSo_not_biEntire

/-- §2.155: "B is not a suballegory of Rel(S): it is … not closed with respect
    to intersection."  Both `wR` and `wS°` are in B; their pointwise
    intersection is not. -/
theorem b_not_closed_inter :
    ∃ (A B : Type) (R S : A → B → Prop), IsB R ∧ IsB S ∧ ¬ IsB (pInter R S) :=
  ⟨Two, Three, wR, bRecip wS, Or.inr wR_biEntire,
   isB_recip (Or.inr wS_biEntire), wRSo_not_isB⟩

/-! ## §2.155 (iv)  Each hom-set of B is a semi-lattice

  `interB` is idempotent, commutative and associative on B-morphisms.
  Associativity rides on the upward-closure argument: both nestings are
  pointwise the triple intersection guarded by ITS bi-entirety (if an inner
  guard fails, the triple guard fails too, and both sides collapse to `∅`). -/

/-- Right-nested characterization: `R ∩ (S ∩ T)` is the guarded triple. -/
theorem interB_assoc_char {A B : Type u} (R S T : A → B → Prop) (a : A) (b : B) :
    interB R (interB S T) a b ↔
      (R a b ∧ S a b ∧ T a b) ∧ BiEntire (pInter R (pInter S T)) := by
  constructor
  · rintro ⟨hR, ⟨hS, hT, -⟩, gOut⟩
    exact ⟨⟨hR, hS, hT⟩, biEntire_mono (fun x y h => ⟨h.1, h.2.1, h.2.2.1⟩) gOut⟩
  · rintro ⟨⟨hR, hS, hT⟩, g3⟩
    have gST : BiEntire (pInter S T) := biEntire_mono (fun x y h => ⟨h.2.1, h.2.2⟩) g3
    exact ⟨hR, ⟨hS, hT, gST⟩, biEntire_mono (fun x y h => ⟨h.1, h.2.1, h.2.2, gST⟩) g3⟩

/-- Left-nested characterization: `(R ∩ S) ∩ T` is the same guarded triple. -/
theorem interB_assoc_char' {A B : Type u} (R S T : A → B → Prop) (a : A) (b : B) :
    interB (interB R S) T a b ↔
      (R a b ∧ S a b ∧ T a b) ∧ BiEntire (pInter R (pInter S T)) := by
  constructor
  · rintro ⟨⟨hR, hS, -⟩, hT, gOut⟩
    exact ⟨⟨hR, hS, hT⟩, biEntire_mono (fun x y h => ⟨h.1.1, h.1.2.1, h.2⟩) gOut⟩
  · rintro ⟨⟨hR, hS, hT⟩, g3⟩
    have gRS : BiEntire (pInter R S) := biEntire_mono (fun x y h => ⟨h.1, h.2.1⟩) g3
    exact ⟨⟨hR, hS, gRS⟩, hT, biEntire_mono (fun x y h => ⟨⟨h.1, h.2.1, gRS⟩, h.2.2⟩) g3⟩

/-- `R ∩ R = R` in B (`inter_idem` of §2.11): a nonzero point of `R` forces
    the guard because `R ∈ B` is then bi-entire. -/
theorem b_inter_idem {a b : BObj.{u}} (R : a ⟶ b) : BHom.inter R R = R :=
  BHom.ext fun _ _ =>
    ⟨fun h => h.1,
     fun h => ⟨h, h, guard_of_lowerBound R.property (fun _ _ => id) (fun _ _ => id) h⟩⟩

/-- `R ∩ S = S ∩ R` in B (`inter_comm` of §2.11). -/
theorem b_inter_comm {a b : BObj.{u}} (R S : a ⟶ b) :
    BHom.inter R S = BHom.inter S R :=
  BHom.ext fun _ _ =>
    ⟨fun h => ⟨h.2.1, h.1, biEntire_mono (fun _ _ hh => ⟨hh.2, hh.1⟩) h.2.2⟩,
     fun h => ⟨h.2.1, h.1, biEntire_mono (fun _ _ hh => ⟨hh.2, hh.1⟩) h.2.2⟩⟩

/-- `R ∩ (S ∩ T) = (R ∩ S) ∩ T` in B (`inter_assoc` of §2.11). -/
theorem b_inter_assoc {a b : BObj.{u}} (R S T : a ⟶ b) :
    BHom.inter R (BHom.inter S T) = BHom.inter (BHom.inter R S) T :=
  BHom.ext fun x y =>
    (interB_assoc_char R.val S.val T.val x y).trans
      (interB_assoc_char' R.val S.val T.val x y).symm

/-- Hom-level form of `interB_eq_left`: `X ∩ Y = X` (i.e. `X ⊑ Y` in the
    B-order) whenever `X ⊆ Y` pointwise. -/
theorem binter_eq_left {a b : BObj.{u}} {X Y : a ⟶ b}
    (hsub : ∀ p q, X.val p q → Y.val p q) : BHom.inter X Y = X :=
  BHom.ext fun p q => interB_eq_left X.property hsub p q

end Freyd.Alg
