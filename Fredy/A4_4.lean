/-
  Bird & de Moor, *Algebra of Programming* §4.4  Locally complete allegories.

  All statements are in Fredy conventions: diagram-order composition `R ≫ S` (first R then S),
  converse `R°`, meet `∩`, order `⊑`, union `R ∪ S`, zero `𝟘`.  We build on `Fredy.S2_3`
  (`DistributiveAllegory`/`DivisionAllegory`/`LocallyCompleteDistributiveAllegory`, division)
  and `Fredy.S2_147_MapCat` (`dom_union`, `dom_zero`, the `TabularUnitary*` classes).

  Contents:
  §A  Meets as joins (`Inf`, Ex 4.28).
  §B  The top of a hom-set (`topHom`).
  §C  Implication `R ⇨ S` (p.97, Ex 4.32/4.33).
  §D  `Sup`/zero interaction (`dom_Sup`, Ex 4.29/4.31).
  §E  Lexicographic composition `R ⨾ S` (p.98, Ex 4.34).
  §F  Division map-laws (Ex 4.35).
  §G  Galois connections (Ex 4.36–4.40).
-/

import Fredy.S2_3
import Fredy.S2_147_MapCat

universe v u

namespace Freyd.Alg

/-! ## Allegory-level utilities and cross-agent private helpers

  These need only `[Allegory 𝒜]`.  `modular_sym`/`map_shunt_right`/`map_shunt_left` are
  duplicated here as `private` because other agents are concurrently building the canonical
  copies in `A4_1`/`A4_2`, which this file cannot import; the collector should dedupe. -/

section AllegoryLevel

variable {𝒜 : Type u} [Allegory 𝒜]

/-- `∩` is monotone in both arguments (a basic `Allegory` fact missing from `S2_1`, used
    throughout this file). -/
theorem inter_mono {a b : 𝒜} {R R' S S' : a ⟶ b} (hR : R ⊑ R') (hS : S ⊑ S') :
    R ∩ S ⊑ R' ∩ S' :=
  le_inter (le_trans (inter_lb_left R S) hR) (le_trans (inter_lb_right R S) hS)

/-- Poset extensionality via principal down-sets: if `X ⊑ A ↔ X ⊑ B` for every `X`, then
    `A = B`.  The standard technique for proving equalities of `Sup`-defined operators without
    chasing elements of the `Sup` directly. -/
theorem antisymm_of_le_iff {a b : 𝒜} {A B : a ⟶ b} (h : ∀ X, X ⊑ A ↔ X ⊑ B) : A = B :=
  le_antisymm ((h A).mp (le_refl A)) ((h B).mpr (le_refl B))

/-- **private**: general-`Allegory` copy of `S2_3`'s `modular_le'` (which is over-scoped
    there, declared under `[TabularUnitaryDivisionAllegory 𝒜]` even though its proof only uses
    `modular_le` and reciprocation).  Dual modular law: `(R≫S)∩T ⊑ R≫(S ∩ R°≫T)`. -/
private theorem modular_le_flip {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have h := modular_le (S°) (R°) (T°)
  have hr := recip_mono h
  rw [Allegory.recip_inter, ← Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip] at hr
  simpa [Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_inter] using hr

/-- **private**: canonical copy lands in A4_1/A4_2 (dedupe at collection).
    The SYMMETRIC MODULAR LAW (B&dM 4.8): `RS ∩ T ⊑ (R ∩ TS°)(S ∩ R°T)`.  Proved by two
    applications of the (asymmetric) modular law `modular_le`/`modular_le_flip`. -/
private theorem modular_sym {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ (R ∩ (T ≫ S°)) ≫ (S ∩ (R° ≫ T)) := by
  have hXU : (R ≫ S) ∩ T ⊑ (R ∩ (T ≫ S°)) ≫ S := modular_le R S T
  have hUX : ((R ∩ (T ≫ S°)) ≫ S) ∩ ((R ≫ S) ∩ T) = (R ≫ S) ∩ T :=
    (Allegory.inter_comm _ _).trans (inter_eq_left hXU)
  have hmod' := modular_le_flip (R ∩ (T ≫ S°)) S ((R ≫ S) ∩ T)
  rw [hUX] at hmod'
  have hUR : R ∩ (T ≫ S°) ⊑ R := inter_lb_left _ _
  have hXT : (R ≫ S) ∩ T ⊑ T := inter_lb_right _ _
  have hcomp : (R ∩ (T ≫ S°))° ≫ ((R ≫ S) ∩ T) ⊑ R° ≫ T :=
    le_trans (comp_mono_right (recip_mono hUR) _) (comp_mono_left R° hXT)
  have hinter : S ∩ ((R ∩ (T ≫ S°))° ≫ ((R ≫ S) ∩ T)) ⊑ S ∩ (R° ≫ T) :=
    le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hcomp)
  exact le_trans hmod' (comp_mono_left _ hinter)

/-- **private**: canonical copy lands in A4_1/A4_2 (dedupe at collection).
    `Entire f → 1 ⊑ f≫f°` (restating `S2_3`'s file-private `map_entire_le` for this file). -/
private theorem entire_le_comp_recip {a b : 𝒜} {f : a ⟶ b} (hf : Entire f) :
    Cat.id a ⊑ f ≫ f° := by
  have h := hf
  dsimp only [Entire, dom] at h
  exact h ▸ inter_lb_right _ _

/-- **private**: canonical copy lands in A4_1/A4_2 (dedupe at collection).
    RIGHT map-shunting: `Map f → (R≫f ⊑ S ↔ R ⊑ S≫f°)`. -/
private theorem map_shunt_right {a b c : 𝒜} {f : b ⟶ c} (hf : Map f) (R : a ⟶ b) (S : a ⟶ c) :
    (R ≫ f ⊑ S) ↔ (R ⊑ S ≫ f°) := by
  constructor
  · intro h
    have hE := entire_le_comp_recip hf.1
    have h1 : R ⊑ R ≫ (f ≫ f°) := by
      have := comp_mono_left R hE
      rwa [Cat.comp_id] at this
    rw [← Cat.assoc] at h1
    exact le_trans h1 (comp_mono_right h f°)
  · intro h
    have hS : f° ≫ f ⊑ Cat.id c := hf.2
    have h1 : R ≫ f ⊑ (S ≫ f°) ≫ f := comp_mono_right h f
    rw [Cat.assoc] at h1
    have h2 : S ≫ (f° ≫ f) ⊑ S ≫ Cat.id c := comp_mono_left S hS
    rw [Cat.comp_id] at h2
    exact le_trans h1 h2

/-- **private**: canonical copy lands in A4_1/A4_2 (dedupe at collection).
    LEFT map-shunting: `Map f → (f°≫R ⊑ S ↔ R ⊑ f≫S)`. -/
private theorem map_shunt_left {a b c : 𝒜} {f : b ⟶ a} (hf : Map f) (R : b ⟶ c) (S : a ⟶ c) :
    (f° ≫ R ⊑ S) ↔ (R ⊑ f ≫ S) := by
  constructor
  · intro h
    have hE := entire_le_comp_recip hf.1
    have h1 : R ⊑ (f ≫ f°) ≫ R := by
      have := comp_mono_right hE R
      rwa [Cat.id_comp] at this
    rw [Cat.assoc] at h1
    exact le_trans h1 (comp_mono_left f h)
  · intro h
    have hS : f° ≫ f ⊑ Cat.id a := hf.2
    have h1 : f° ≫ R ⊑ f° ≫ (f ≫ S) := comp_mono_left f° h
    rw [← Cat.assoc] at h1
    have h2 : (f° ≫ f) ≫ S ⊑ Cat.id a ≫ S := comp_mono_right hS S
    rw [Cat.id_comp] at h2
    exact le_trans h1 h2

/-- **private**: the mirror of `S2_1`'s `simple_dist_inter` for RIGHT composition:
    `(A∩B)≫g° = (A≫g°)∩(B≫g°)` when `g` is simple.  Derived by reciprocating
    `simple_dist_inter (Simple g) A° B°`. -/
private theorem simple_dist_inter_recip {a b c : 𝒜} {g : c ⟶ b} (hg : Simple g) (A B : a ⟶ b) :
    (A ∩ B) ≫ g° = (A ≫ g°) ∩ (B ≫ g°) := by
  have h := simple_dist_inter hg (A°) (B°)
  have hr := congrArg Allegory.recip h
  simp only [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_recip] at hr
  exact hr

/-! ### Galois connections (B&dM Ex 4.36–4.39, hom-set level)

  Galois connections are the engine of program calculation (thinning/greedy theorems later
  in B&dM); we record the definition and the monotonicity of both legs here (needs only
  `[Allegory 𝒜]`), and the join-preservation facts in the `LocallyCompleteDistributiveAllegory`
  section below. -/

/-- A GALOIS CONNECTION between hom-sets `(a,b)` and `(c,d)`: `f X ⊑ Y ↔ X ⊑ g Y`
    (`f` left adjoint, `g` right adjoint). -/
def GaloisConn {a b c d : 𝒜} (f : (a ⟶ b) → (c ⟶ d)) (g : (c ⟶ d) → (a ⟶ b)) : Prop :=
  ∀ X Y, (f X ⊑ Y) ↔ (X ⊑ g Y)

/-- The lower (left-adjoint) leg of a Galois connection is monotone. -/
theorem GaloisConn.mono_lower {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConn f g) {X X' : a ⟶ b} (hX : X ⊑ X') : f X ⊑ f X' :=
  (h X (f X')).mpr (le_trans hX ((h X' (f X')).mp (le_refl _)))

/-- The upper (right-adjoint) leg of a Galois connection is monotone. -/
theorem GaloisConn.mono_upper {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConn f g) {Y Y' : c ⟶ d} (hY : Y ⊑ Y') : g Y ⊑ g Y' :=
  (h (g Y) Y').mp (le_trans ((h (g Y) Y).mpr (le_refl _)) hY)

end AllegoryLevel

/-! ## Locally complete distributive allegories -/

section LCDA

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

-- (`Sup_congr` comes from S2_22, which is in scope via S2_147_MapCat.)

/-! ### §A  Meets as joins (B&dM Ex 4.28) -/

/-- Meets as joins: `Inf P := ⊔ { S | S is a lower bound of every R with P R }`. -/
def Inf {a b : 𝒜} (P : (a ⟶ b) → Prop) : a ⟶ b := Sup (fun S => ∀ R, P R → S ⊑ R)

theorem Inf_le {a b : 𝒜} {P : (a ⟶ b) → Prop} {R : a ⟶ b} (h : P R) : Inf P ⊑ R :=
  Sup_le (fun _S hS => hS R h)

theorem le_Inf {a b : 𝒜} {P : (a ⟶ b) → Prop} {T : a ⟶ b} (h : ∀ R, P R → T ⊑ R) : T ⊑ Inf P :=
  le_Sup h

/-! ### §B  The top of a hom-set (B&dM p.97)

  In a locally complete distributive allegory each hom-set `(a,b)` has a top element: the
  join of everything. -/

/-- The top of the hom-set `(a,b)`. -/
def topHom (a b : 𝒜) : a ⟶ b := Sup (fun _ => True)

theorem le_topHom {a b : 𝒜} (R : a ⟶ b) : R ⊑ topHom a b := le_Sup trivial

theorem recip_topHom {a b : 𝒜} : (topHom a b)° = topHom b a := by
  apply le_antisymm
  · exact le_topHom _
  · exact recip_le_iff.mp (le_topHom _)

/-! ### §C  Implication (B&dM §4.4 p.97, Ex 4.32/4.33) -/

/-- Implication `R ⇨ S := ⊔ { X | X∩R ⊑ S }`, the right adjoint to `_ ∩ R`. -/
def impl {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b := Sup (fun X => X ∩ R ⊑ S)

/-- Implication notation `R ⇨ S` (B&dM §4.4 p.97). -/
infixr:58 (name := implNotation) " ⇨ " => impl

/-- The universal property of implication: `X ⊑ R⇨S ↔ X∩R ⊑ S`. -/
theorem le_impl_iff {a b : 𝒜} (X R S : a ⟶ b) : (X ⊑ R ⇨ S) ↔ (X ∩ R ⊑ S) := by
  constructor
  · intro h
    have h1 : X ∩ R ⊑ (R ⇨ S) ∩ R := inter_mono h (le_refl R)
    rw [Allegory.inter_comm (R ⇨ S) R] at h1
    have h2 : R ∩ (R ⇨ S) = Sup (fun Y => ∃ Z, (Z ∩ R ⊑ S) ∧ Y = R ∩ Z) := by
      dsimp only [impl]; exact inter_Sup_distrib R (fun Z => Z ∩ R ⊑ S)
    rw [h2] at h1
    refine le_trans h1 (Sup_le ?_)
    rintro Y ⟨Z, hZ, rfl⟩
    rw [Allegory.inter_comm R Z]
    exact hZ
  · intro h; exact le_Sup h

theorem impl_cancel {a b : 𝒜} (R S : a ⟶ b) : (R ⇨ S) ∩ R ⊑ S :=
  (le_impl_iff (R ⇨ S) R S).mp (le_refl _)

theorem impl_mono_right {a b : 𝒜} {R S S' : a ⟶ b} (h : S ⊑ S') : (R ⇨ S) ⊑ (R ⇨ S') := by
  dsimp only [impl]
  apply Sup_le
  intro X hX
  exact le_Sup (le_trans hX h)

theorem impl_antitone_left {a b : 𝒜} {R R' S : a ⟶ b} (h : R ⊑ R') : (R' ⇨ S) ⊑ (R ⇨ S) := by
  dsimp only [impl]
  apply Sup_le
  intro X hX
  exact le_Sup (le_trans (inter_mono (le_refl X) h) hX)

/-- Implication into the top is the top: `R ⇨ ⊤ = ⊤`. -/
theorem impl_topHom {a b : 𝒜} (R : a ⟶ b) : (R ⇨ (topHom a b)) = topHom a b :=
  le_antisymm (le_topHom _) ((le_impl_iff _ _ _).mpr (le_topHom _))

/-- The top implies anything it dominates trivially: `⊤ ⇨ S = S`. -/
theorem topHom_impl {a b : 𝒜} (R : a ⟶ b) : (topHom a b ⇨ R) = R := by
  apply antisymm_of_le_iff
  intro X
  rw [le_impl_iff, inter_eq_left (le_topHom X)]

/-- Currying: `R ⇨ (S ⇨ T) = (R∩S) ⇨ T` (Ex 4.32). -/
theorem impl_curry {a b : 𝒜} (R S T : a ⟶ b) : (R ⇨ (S ⇨ T)) = ((R ∩ S) ⇨ T) := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ R ⇨ (S ⇨ T) ↔ X ∩ R ⊑ S ⇨ T := le_impl_iff X R (S ⇨ T)
    _ ↔ (X ∩ R) ∩ S ⊑ T := le_impl_iff (X ∩ R) S T
    _ ↔ X ∩ (R ∩ S) ⊑ T := by rw [Allegory.inter_assoc]
    _ ↔ X ⊑ (R ∩ S) ⇨ T := (le_impl_iff X (R ∩ S) T).symm

/-- `(R∪S) ⇨ T = (R⇨T) ∩ (S⇨T)` (Ex 4.32). -/
theorem union_impl {a b : 𝒜} (R S T : a ⟶ b) : ((R ∪ S) ⇨ T) = ((R ⇨ T) ∩ (S ⇨ T)) := by
  apply le_antisymm
  · exact le_inter (impl_antitone_left (le_union_left R S)) (impl_antitone_left (le_union_right R S))
  · apply (le_impl_iff _ _ _).mpr
    rw [DistributiveAllegory.inter_union_distrib]
    apply union_lub
    · exact le_trans (inter_mono (inter_lb_left (R ⇨ T) (S ⇨ T)) (le_refl R)) (impl_cancel R T)
    · exact le_trans (inter_mono (inter_lb_right (R ⇨ T) (S ⇨ T)) (le_refl S)) (impl_cancel S T)

/-- `R ⇨ (S∩T) = (R⇨S) ∩ (R⇨T)` (Ex 4.32). -/
theorem impl_inter {a b : 𝒜} (R S T : a ⟶ b) : (R ⇨ (S ∩ T)) = ((R ⇨ S) ∩ (R ⇨ T)) := by
  apply le_antisymm
  · exact le_inter (impl_mono_right (inter_lb_left S T)) (impl_mono_right (inter_lb_right S T))
  · apply (le_impl_iff _ _ _).mpr
    apply le_inter
    · exact le_trans (inter_mono (inter_lb_left (R ⇨ S) (R ⇨ T)) (le_refl R)) (impl_cancel R S)
    · exact le_trans (inter_mono (inter_lb_right (R ⇨ S) (R ⇨ T)) (le_refl R)) (impl_cancel R T)

/-- `R ∩ (R⇨S) = R∩S` (Ex 4.32). -/
theorem inter_impl_absorb {a b : 𝒜} (R S : a ⟶ b) : (R ∩ (R ⇨ S)) = (R ∩ S) := by
  apply le_antisymm
  · apply le_inter (inter_lb_left R (R ⇨ S))
    rw [Allegory.inter_comm R (R ⇨ S)]
    exact impl_cancel R S
  · apply le_inter (inter_lb_left R S)
    apply (le_impl_iff _ _ _).mpr
    exact le_trans (inter_lb_left (R ∩ S) R) (inter_lb_right R S)

/-- **B&dM Ex 4.33** (one direction): conjugation by maps preserves `⇨` in the `⊑` direction.

    The reverse containment (which would upgrade this to the book's stated equality
    `f≫(R⇨S)≫g° = (f≫R≫g°) ⇨ (f≫S≫g°)`) resists a general LCDA proof.  Unwinding it via
    `map_shunt_left`/`map_shunt_right`/`le_impl_iff` reduces to: for arbitrary `X : c⟶d`
    (with `M := f≫R≫g°`, `N := f≫S≫g°`), `X∩M ⊑ N → (f°≫X≫g)∩R ⊑ S`.  This needs
    `R ⊑ f°≫M≫g`, but only the OPPOSITE containment `f°≫M≫g ⊑ R` follows from `Simple f`,
    `Simple g` (`f°≫M≫g = (f°f)≫R≫(g°g)`, and `Map` only gives `f°f ⊑ 1`, `g°g ⊑ 1` — an
    upper, never a lower, bound).  Recovering `R` needs `f`, `g` to ALSO be co-simple
    (injective), which a bare `Map` does not provide.  A powerset (`Rel`) check with `f`
    non-surjective confirms the full equality nonetheless holds THERE, via "preimage commutes
    with Boolean complement" — i.e. the reverse direction is a genuinely BOOLEAN fact (§4.5),
    not a general-LCDA one. -/
theorem map_conj_impl_le {a b c d : 𝒜} {f : c ⟶ a} {g : d ⟶ b} (hf : Map f) (hg : Map g)
    (R S : a ⟶ b) :
    f ≫ (R ⇨ S) ≫ g° ⊑ (f ≫ R ≫ g°) ⇨ (f ≫ S ≫ g°) := by
  apply (le_impl_iff _ _ _).mpr
  have e1 : f ≫ (R ⇨ S) ≫ g° = (f ≫ (R ⇨ S)) ≫ g° := (Cat.assoc f (R ⇨ S) g°).symm
  have e2 : f ≫ R ≫ g° = (f ≫ R) ≫ g° := (Cat.assoc f R g°).symm
  have e3 : f ≫ S ≫ g° = (f ≫ S) ≫ g° := (Cat.assoc f S g°).symm
  rw [e1, e2, e3, ← simple_dist_inter_recip hg.2, ← simple_dist_inter hf.2]
  exact comp_mono_right (comp_mono_left f (impl_cancel R S)) g°

/-! ### §D  `Sup`/zero interaction (B&dM Ex 4.29, 4.31) -/

/-- `dom` distributes over `Sup`: `dom (⊔ P) = ⊔ { dom R | P R }` (Ex 4.29). -/
theorem dom_Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) :
    dom (Sup P) = Sup (fun D => ∃ R, P R ∧ D = dom R) := by
  apply le_antisymm
  · have h1 : (Sup P)° = Sup (fun T : b ⟶ a => ∃ R, P R ∧ T = R°) := recip_Sup P
    have h2 : Sup P ≫ (Sup P)° = Sup (fun U : a ⟶ a => ∃ R, P R ∧ U = Sup P ≫ R°) := by
      rw [h1, comp_Sup_distrib]
      apply Sup_congr
      intro U
      constructor
      · rintro ⟨T, ⟨R, hR, rfl⟩, hU⟩; exact ⟨R, hR, hU⟩
      · rintro ⟨R, hR, hU⟩; exact ⟨R°, ⟨R, hR, rfl⟩, hU⟩
    have h3 : Cat.id a ∩ (Sup P ≫ (Sup P)°)
        = Sup (fun D => ∃ R, P R ∧ D = Cat.id a ∩ (Sup P ≫ R°)) := by
      rw [h2, inter_Sup_distrib]
      apply Sup_congr
      intro D
      constructor
      · rintro ⟨U, ⟨R, hR, rfl⟩, hD⟩; exact ⟨R, hR, hD⟩
      · rintro ⟨R, hR, hD⟩; exact ⟨Sup P ≫ R°, ⟨R, hR, rfl⟩, hD⟩
    show Cat.id a ∩ (Sup P ≫ (Sup P)°) ⊑ _
    rw [h3]
    apply Sup_le
    rintro D ⟨R, hR, rfl⟩
    have hD : Cat.id a ∩ (Sup P ≫ R°) = dom (R ∩ Sup P) := (dom_inter R (Sup P)).symm
    rw [hD, inter_eq_left (le_Sup hR)]
    exact le_Sup ⟨R, hR, rfl⟩
  · apply Sup_le
    rintro D ⟨R, hR, rfl⟩
    exact dom_mono_of_le (le_Sup hR)

/-- A morphism is zero iff its domain is zero (Ex 4.31). -/
theorem eq_zero_iff_dom_zero {a b : 𝒜} (R : a ⟶ b) : R = (𝟘 : a ⟶ b) ↔ dom R = (𝟘 : a ⟶ a) := by
  constructor
  · intro h; rw [h]; exact dom_zero
  · intro h
    calc R = dom R ≫ R := (dom_comp_eq R).symm
      _ = (𝟘 : a ⟶ a) ≫ R := by rw [h]
      _ = 𝟘 := DistributiveAllegory.zero_comp R

/-- `(R≫S)∩T = 0 ↔ R∩(T≫S°) = 0` (Ex 4.31). -/
theorem comp_inter_zero_iff {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    ((R ≫ S) ∩ T = (𝟘 : a ⟶ c)) ↔ (R ∩ (T ≫ S°) = (𝟘 : a ⟶ b)) := by
  constructor
  · intro h
    have hmod := modular_le T (S°) R
    rw [Allegory.recip_recip] at hmod
    rw [(Allegory.inter_comm T (R ≫ S)).trans h, DistributiveAllegory.zero_comp] at hmod
    rw [Allegory.inter_comm R (T ≫ S°)]
    exact le_antisymm hmod (zero_le _)
  · intro h
    have hmod := modular_le R S T
    rw [h, DistributiveAllegory.zero_comp] at hmod
    exact le_antisymm hmod (zero_le _)

/-! ### §E  Lexicographic composition (B&dM p.98, Ex 4.34)

  `R ⨾ S` compares by `R` first, breaking ties by `S`: the lexicographic ordering built from
  `(fst-projected leq) ⨾ (snd-projected leq)`. -/

/-- `R ⨾ S := R ∩ (R°⇨S)` — B&dM's `R;S`: compare by `R`, break ties by `S`. -/
def thenRel {a : 𝒜} (R S : a ⟶ a) : a ⟶ a := R ∩ (R° ⇨ S)

/-- Lexicographic-composition notation `R ⨾ S`. -/
infixl:62 (name := thenRelNotation) " ⨾ " => thenRel

theorem thenRel_reflexive {a : 𝒜} {R S : a ⟶ a} (hR : Reflexive R) (hS : Reflexive S) :
    Reflexive (R ⨾ S) := by
  apply le_inter hR
  apply (le_impl_iff _ _ _).mpr
  exact le_trans (inter_lb_left (Cat.id a) (R°)) hS

/-- **B&dM Ex 4.34**: `R ⨾ S` is transitive when `R`, `S` are (uses the symmetric modular law,
    per the book's hint). -/
theorem thenRel_transitive {a : 𝒜} {R S : a ⟶ a} (_hR : Reflexive R)
    (hRt : Transitive R) (hSt : Transitive S) : Transitive (R ⨾ S) := by
  have hMR : (R ⨾ S) ⊑ R := inter_lb_left R (R° ⇨ S)
  have hMS : (R ⨾ S) ∩ R° ⊑ S := (le_impl_iff (R ⨾ S) (R°) S).mp (inter_lb_right R (R° ⇨ S))
  have hRR : R° ≫ R° ⊑ R° := by
    have h := recip_mono hRt
    rwa [Allegory.recip_comp] at h
  have hM'R' : (R ⨾ S)° ≫ R° ⊑ R° :=
    le_trans (comp_mono_right (recip_mono hMR) R°) hRR
  have hR'M' : R° ≫ (R ⨾ S)° ⊑ R° :=
    le_trans (comp_mono_left R° (recip_mono hMR)) hRR
  have hfac1 : (R ⨾ S) ∩ (R° ≫ (R ⨾ S)°) ⊑ S :=
    le_trans (inter_mono (le_refl (R ⨾ S)) hR'M') hMS
  have hfac2 : (R ⨾ S) ∩ ((R ⨾ S)° ≫ R°) ⊑ S :=
    le_trans (inter_mono (le_refl (R ⨾ S)) hM'R') hMS
  have hms := modular_sym (R ⨾ S) (R ⨾ S) (R°)
  have hfinal : ((R ⨾ S) ≫ (R ⨾ S)) ∩ R° ⊑ S :=
    le_trans hms (le_trans (comp_mono_right hfac1 _) (le_trans (comp_mono_left S hfac2) hSt))
  apply le_inter
  · exact le_trans (comp_mono_right hMR (R ⨾ S)) (le_trans (comp_mono_left R hMR) hRt)
  · exact (le_impl_iff _ (R°) S).mpr hfinal

theorem topHom_thenRel {a : 𝒜} (R : a ⟶ a) : (topHom a a) ⨾ R = R := by
  show topHom a a ∩ ((topHom a a)° ⇨ R) = R
  rw [recip_topHom, topHom_impl, Allegory.inter_comm, inter_eq_left (le_topHom R)]

theorem thenRel_topHom {a : 𝒜} (R : a ⟶ a) : R ⨾ (topHom a a) = R := by
  show R ∩ (R° ⇨ topHom a a) = R
  rw [impl_topHom, inter_eq_left (le_topHom R)]

-- BOOK Ex 4.34: `(R⨾S)⨾T = R⨾(S⨾T)` (associativity of lexicographic composition).
-- STATUS: DROPPED after genuine attempt — semantic check first, as instructed.
-- Expanding both sides with `impl_inter`/`impl_curry` gives
--   `R⨾(S⨾T) = (R⨾S) ∩ ((R°∩S°)⇨T)`
-- while directly
--   `(R⨾S)⨾T = (R⨾S) ∩ ((R⨾S)°⇨T)`.
-- These agree for every `T` iff `(R⨾S)°⇨T = (R°∩S°)⇨T` for every `T`, which (`impl` being
-- antitone in its left argument but not order-REFLECTING in general) would need
-- `(R⨾S)° = R°∩S°` outright.  But `(R⨾S)° = R° ∩ (R°⇨S)°`, and `(R°⇨S)° = S°` fails in
-- general (`⇨` is not self-dual under reciprocation) — e.g. `(R°⇨S)° ⊒ S°` is the only
-- direction that follows from `impl_cancel` + reciprocation.  Associativity therefore
-- genuinely needs extra hypotheses beyond the bare `impl`/`thenRel` laws (plausibly `R`, `S`
-- both preorders plus a further compatibility fact); dropped here rather than guessing at
-- the missing hypothesis.

/-! ### §G  Galois connections, LCDA part (B&dM Ex 4.36–4.40) -/

/-- A left adjoint preserves every existing join (Ex 4.39/4.40 direction). -/
theorem GaloisConn.lower_Sup {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConn f g) (P : (a ⟶ b) → Prop) :
    f (Sup P) = Sup (fun Y => ∃ X, P X ∧ Y = f X) := by
  apply le_antisymm
  · apply (h (Sup P) _).mpr
    apply Sup_le
    intro R hR
    apply (h R _).mp
    exact le_Sup ⟨R, hR, rfl⟩
  · apply Sup_le
    rintro Y ⟨X, hX, rfl⟩
    exact h.mono_lower (le_Sup hX)

/-- The right adjoint is the join of everything mapped below the target (Ex 4.40). -/
theorem GaloisConn.upper_eq {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConn f g) (Y : c ⟶ d) : g Y = Sup (fun X => f X ⊑ Y) := by
  apply le_antisymm
  · exact le_Sup ((h (g Y) Y).mpr (le_refl _))
  · apply Sup_le
    intro X hX
    exact (h X Y).mp hX

/-- `(_∩R) ⊣ (R⇨_)` is a Galois connection (instance of Ex 4.36–4.40). -/
theorem gc_inter_impl {a b : 𝒜} (R : a ⟶ b) : GaloisConn (fun X : a ⟶ b => X ∩ R) (fun Y => R ⇨ Y) :=
  fun X Y => (le_impl_iff X R Y).symm

end LCDA

/-! ## Division allegories -/

section DivAllegory

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### §F  Division map-laws (B&dM Ex 4.35) -/

theorem map_comp_div {a b c d : 𝒜} {f : d ⟶ a} (hf : Map f) (R : a ⟶ c) (S : b ⟶ c) :
    f ≫ (R / S) = (f ≫ R) / S := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ f ≫ (R / S) ↔ f° ≫ X ⊑ R / S := (map_shunt_left hf X (R / S)).symm
    _ ↔ (f° ≫ X) ≫ S ⊑ R := le_div_iff _ _ _
    _ ↔ f° ≫ (X ≫ S) ⊑ R := by rw [Cat.assoc]
    _ ↔ X ≫ S ⊑ f ≫ R := map_shunt_left hf (X ≫ S) R
    _ ↔ X ⊑ (f ≫ R) / S := (le_div_iff _ _ _).symm

theorem div_comp_recip_map {a b c d : 𝒜} {f : d ⟶ b} (hf : Map f) (R : a ⟶ c) (S : b ⟶ c) :
    R / (f ≫ S) = (R / S) ≫ f° := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ R / (f ≫ S) ↔ X ≫ (f ≫ S) ⊑ R := le_div_iff _ _ _
    _ ↔ (X ≫ f) ≫ S ⊑ R := by rw [← Cat.assoc]
    _ ↔ X ≫ f ⊑ R / S := (le_div_iff _ _ _).symm
    _ ↔ X ⊑ (R / S) ≫ f° := map_shunt_right hf X (R / S)

/-! ### §G  Galois connections, division part -/

/-- `(_≫S) ⊣ (_/S)` is a Galois connection (Ex 4.36). -/
theorem gc_comp_div {a b c : 𝒜} (S : b ⟶ c) :
    GaloisConn (fun X : a ⟶ b => X ≫ S) (fun Y : a ⟶ c => Y / S) :=
  fun X Y => (le_div_iff X Y S).symm

/-- `(S≫_) ⊣ (S\_)` is a Galois connection (Ex 4.36, left-division form). -/
theorem gc_comp_leftDiv {a b c : 𝒜} (S : a ⟶ b) :
    GaloisConn (fun X : b ⟶ c => S ≫ X) (fun Y => leftDiv S Y) :=
  fun X Y => (le_leftDiv_iff X S Y).symm

end DivAllegory

end Freyd.Alg
