/-
  Bird & de Moor, *Algebra of Programming* §4.2  Special properties of arrows.

  Order-theoretic properties of endo-relations (preorder, partial order), closure of
  those properties under `°`/`∩`, coreflexive absorption laws, the domain shunting rule,
  the entire/simple/simple-modular identities, the map shunting rules (the workhorses of
  relational program calculation), Prop 4.1 (a jointly-inverse pair of inequations forces
  a map), and Exercises 4.14/4.15/4.19.
-/

import Fredy.A4_1

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## §4.2  Preorders and partial orders on an object (B&dM p.86)

  Freyd already has `Reflexive`, `Symmetric`, `Transitive`, `Coreflexive` (§2.12) and
  `EquivalenceRel` (§2.163); only the preorder/antisymmetry/partial-order bundles are new. -/

/-- A PREORDER on `a`: reflexive and transitive (B&dM p.86).  (Named `IsPreorder`, not
    `Preorder`, to avoid clashing with an unrelated core/order name.) -/
def IsPreorder {a : 𝒜} (R : a ⟶ a) : Prop := Reflexive R ∧ Transitive R

/-- ANTISYMMETRIC: `R ∩ R° ⊑ id` (B&dM p.86). -/
def AntiSymmetric {a : 𝒜} (R : a ⟶ a) : Prop := R ∩ R° ⊑ Cat.id a

/-- A PARTIAL ORDER on `a`: a preorder that is also antisymmetric (B&dM p.86). -/
def IsPartialOrder {a : 𝒜} (R : a ⟶ a) : Prop := IsPreorder R ∧ AntiSymmetric R

/-! ### Closure of preorders/symmetric relations under `°` and `∩` -/

/-- A preorder's reciprocal is a preorder (B&dM p.86). -/
theorem isPreorder_recip {a : 𝒜} {R : a ⟶ a} (hR : IsPreorder R) : IsPreorder R° := by
  obtain ⟨hRefl, hTrans⟩ := hR
  refine ⟨?_, ?_⟩
  · have h := recip_mono hRefl; rwa [recip_id] at h
  · have h := recip_mono hTrans; rwa [Allegory.recip_comp] at h

/-- The intersection of two preorders is a preorder (B&dM p.86). -/
theorem isPreorder_inter {a : 𝒜} {R S : a ⟶ a} (hR : IsPreorder R) (hS : IsPreorder S) :
    IsPreorder (R ∩ S) := by
  obtain ⟨hRRefl, hRTrans⟩ := hR
  obtain ⟨hSRefl, hSTrans⟩ := hS
  refine ⟨le_inter hRRefl hSRefl, ?_⟩
  have h1 : (R ∩ S) ≫ (R ∩ S) ⊑ R ≫ R :=
    le_trans (comp_mono_right (inter_lb_left R S) (R ∩ S)) (comp_mono_left R (inter_lb_left R S))
  have h2 : (R ∩ S) ≫ (R ∩ S) ⊑ S ≫ S :=
    le_trans (comp_mono_right (inter_lb_right R S) (R ∩ S)) (comp_mono_left S (inter_lb_right R S))
  exact le_inter (le_trans h1 hRTrans) (le_trans h2 hSTrans)

/-- The intersection of two symmetric relations is symmetric (B&dM p.86). -/
theorem symmetric_inter {a : 𝒜} {R S : a ⟶ a} (hR : Symmetric R) (hS : Symmetric S) :
    Symmetric (R ∩ S) := by
  dsimp only [Symmetric]
  rw [Allegory.recip_inter]
  exact le_inter (le_trans (inter_lb_left R° S°) hR) (le_trans (inter_lb_right R° S°) hS)

/-- **B&dM p.86**: if `R` is a preorder then `R ∩ R°` is an equivalence relation
    (the equivalence induced by the preorder). -/
theorem equivalence_inter_recip {a : 𝒜} {R : a ⟶ a} (hR : IsPreorder R) :
    EquivalenceRel (R ∩ R°) := by
  obtain ⟨hRefl, hTrans⟩ := hR
  obtain ⟨hReflRecip, hTransRecip⟩ := isPreorder_recip ⟨hRefl, hTrans⟩
  refine ⟨le_inter hRefl hReflRecip, ?_, ?_⟩
  · show (R ∩ R°)° ⊑ R ∩ R°
    rw [Allegory.recip_inter, Allegory.recip_recip, Allegory.inter_comm R° R]
    exact le_refl _
  · have h1 : (R ∩ R°) ≫ (R ∩ R°) ⊑ R ≫ R :=
      le_trans (comp_mono_right (inter_lb_left R R°) _) (comp_mono_left R (inter_lb_left R R°))
    have h2 : (R ∩ R°) ≫ (R ∩ R°) ⊑ R° ≫ R° :=
      le_trans (comp_mono_right (inter_lb_right R R°) _) (comp_mono_left R° (inter_lb_right R R°))
    exact le_inter (le_trans h1 hTrans) (le_trans h2 hTransRecip)

/-! ## §4.2  Coreflexive exercises -/

/-- **Ex 4.8**: a coreflexive morphism is transitive (immediate from
    `coreflexive_symmetric_idempotent`'s idempotence half). -/
theorem coreflexive_transitive {a : 𝒜} {C : a ⟶ a} (hC : Coreflexive C) : Transitive C := by
  show C ≫ C ⊑ C
  rw [(coreflexive_symmetric_idempotent hC).2]
  exact le_refl C

/-- **Ex 4.10**: for coreflexive `C : a ⟶ a` and `R S : b ⟶ a`, `(R≫C)∩S = (R∩S)≫C`. -/
theorem coreflexive_comp_inter {a b : 𝒜} {C : a ⟶ a} (hC : Coreflexive C) (R S : b ⟶ a) :
    (R ≫ C) ∩ S = (R ∩ S) ≫ C := by
  apply le_antisymm
  · have hCrecip : Coreflexive C° := by
      have h := recip_mono hC; rwa [recip_id] at h
    have h1 : (R ≫ C) ∩ S ⊑ (R ∩ S ≫ C°) ≫ C := modular_le R C S
    have h2 : S ≫ C° ⊑ S := by
      have h2a := comp_mono_left S hCrecip; rwa [Cat.comp_id] at h2a
    have h3 : R ∩ (S ≫ C°) ⊑ R ∩ S :=
      le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h2)
    exact le_trans h1 (comp_mono_right h3 C)
  · have h1 : (R ∩ S) ≫ C ⊑ R ≫ C := comp_mono_right (inter_lb_left R S) C
    have h2 : (R ∩ S) ≫ C ⊑ S := by
      have h2a : (R ∩ S) ≫ C ⊑ (R ∩ S) ≫ Cat.id a := comp_mono_left (R ∩ S) hC
      rw [Cat.comp_id] at h2a
      exact le_trans h2a (inter_lb_right R S)
    exact le_inter h1 h2

/-- Mirror of `coreflexive_comp_inter` with `C` on the left: for coreflexive `C : a ⟶ a`
    and `R S : a ⟶ b`, `(C≫R)∩S = C≫(R∩S)`.  (Used to reach both Ex 4.11 identities.) -/
theorem coreflexive_comp_inter_left {a b : 𝒜} {C : a ⟶ a} (hC : Coreflexive C) (R S : a ⟶ b) :
    (C ≫ R) ∩ S = C ≫ (R ∩ S) := by
  apply le_antisymm
  · have hCsymm : C° = C := symmetric_eq (coreflexive_symmetric_idempotent hC).1
    have h1 : (C ≫ R) ∩ S ⊑ C ≫ (R ∩ C° ≫ S) := modular_le_right C R S
    have h2 : C ≫ S ⊑ S := by
      have h2a := comp_mono_right hC S; rwa [Cat.id_comp] at h2a
    have h3 : R ∩ (C° ≫ S) ⊑ R ∩ S := by
      rw [hCsymm]; exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h2)
    exact le_trans h1 (comp_mono_left C h3)
  · have h1 : C ≫ (R ∩ S) ⊑ C ≫ R := comp_mono_left C (inter_lb_left R S)
    have h2 : C ≫ (R ∩ S) ⊑ S := by
      have h2a : C ≫ (R ∩ S) ⊑ Cat.id a ≫ (R ∩ S) := comp_mono_right hC (R ∩ S)
      rw [Cat.id_comp] at h2a
      exact le_trans h2a (inter_lb_right R S)
    exact le_inter h1 h2

/-- **Ex 4.11** (second identity): for coreflexive `C` and `X : a ⟶ a`,
    `(X≫C)∩id = C≫(X∩id)`.  `X∩id` is automatically coreflexive, so `coreflexive_comp_inter`
    and `coreflexive_comp_eq_inter` (§2.121) collapse both sides to `(X∩id)∩C`. -/
theorem coreflexive_shunt_inter {a : 𝒜} {C : a ⟶ a} (hC : Coreflexive C) (X : a ⟶ a) :
    (X ≫ C) ∩ Cat.id a = C ≫ (X ∩ Cat.id a) := by
  have hD : Coreflexive (X ∩ Cat.id a) := inter_lb_right X (Cat.id a)
  calc (X ≫ C) ∩ Cat.id a = (X ∩ Cat.id a) ≫ C := coreflexive_comp_inter hC X (Cat.id a)
    _ = (X ∩ Cat.id a) ∩ C := coreflexive_comp_eq_inter hD hC
    _ = C ∩ (X ∩ Cat.id a) := Allegory.inter_comm _ _
    _ = C ≫ (X ∩ Cat.id a) := (coreflexive_comp_eq_inter hC hD).symm

/-- **Ex 4.11** (first identity): for coreflexive `C` and `X : a ⟶ a`, `(X≫C)∩id = (C≫X)∩id`. -/
theorem coreflexive_shunt_left {a : 𝒜} {C : a ⟶ a} (hC : Coreflexive C) (X : a ⟶ a) :
    (X ≫ C) ∩ Cat.id a = (C ≫ X) ∩ Cat.id a := by
  rw [coreflexive_shunt_inter hC X, coreflexive_comp_inter_left hC X (Cat.id a)]

/-! ## §4.2  Domain shunting (B&dM 4.11, mirrored to `dom`)

  `dom_mono_of_le`/`dom_comp_le` (already in §2.1/§2.123) give a route shorter than the
  book's modular-law chain: `dom R ⊑ dom(X≫R) ⊑ dom X ⊑ X`. -/

/-- **B&dM 4.11** (mirrored to `dom`): for coreflexive `X : a ⟶ a`, `dom R ⊑ X ↔ R ⊑ X≫R`. -/
theorem dom_UP {a b : 𝒜} {R : a ⟶ b} {X : a ⟶ a} (hX : Coreflexive X) :
    dom R ⊑ X ↔ R ⊑ X ≫ R := by
  constructor
  · intro h
    exact le_trans (le_dom_comp R) (comp_mono_right h R)
  · intro h
    have h1 : dom R ⊑ dom (X ≫ R) := dom_mono_of_le h
    have h2 : dom (X ≫ R) ⊑ dom X := dom_comp_le X R
    have h3 : dom X ⊑ X := by
      have hXrecip : X° ⊑ Cat.id a := by
        have hr := recip_mono hX; rwa [recip_id] at hr
      have hstep : X ≫ X° ⊑ X ≫ Cat.id a := comp_mono_left X hXrecip
      rw [Cat.comp_id] at hstep
      exact le_trans (inter_lb_right (Cat.id a) (X ≫ X°)) hstep
    exact le_trans h1 (le_trans h2 h3)

/-! ## §4.2  Domain of a composite through the intervening domain (B&dM 4.14) -/

/-- `dom R ≫ R = R` (mirrors `S2_3.dom_comp_self`, re-derived here since `S2_3` is out
    of this file's import scope): one half is `le_dom_comp`, the other is `dom R ⊑ id`. -/
private theorem dom_comp_self_eq {a b : 𝒜} (S : a ⟶ b) : dom S ≫ S = S := by
  apply le_antisymm
  · have h := comp_mono_right (dom_coreflexive S) S; rwa [Cat.id_comp] at h
  · exact le_dom_comp S

/-- **B&dM 4.14** (mirrored to `dom`): `dom(R≫S) = dom(R≫dom S)`. -/
theorem dom_comp_dom {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    dom (R ≫ S) = dom (R ≫ dom S) := by
  apply le_antisymm
  · have heq : R ≫ S = (R ≫ dom S) ≫ S := by rw [Cat.assoc, dom_comp_self_eq S]
    rw [heq]; exact dom_comp_le (R ≫ dom S) S
  · have hle : R ≫ dom S ⊑ (R ≫ S) ≫ S° := by
      have h1 : R ≫ dom S ⊑ R ≫ (S ≫ S°) :=
        comp_mono_left R (inter_lb_right (Cat.id b) (S ≫ S°))
      rwa [← Cat.assoc] at h1
    exact le_trans (dom_mono_of_le hle) (dom_comp_le (R ≫ S) S°)

/-! ## §4.2  Entireness of an intersection (B&dM 4.18) -/

/-- **B&dM 4.18**: `Entire (R∩S) ↔ id ⊑ S≫R°` (immediate from `dom_inter`, §2.124). -/
theorem entire_inter_iff {a b : 𝒜} (R S : a ⟶ b) :
    Entire (R ∩ S) ↔ Cat.id a ⊑ S ≫ R° := by
  show dom (R ∩ S) = Cat.id a ↔ Cat.id a ⊑ S ≫ R°
  rw [dom_inter]
  exact Iff.rfl

/-! ## §4.2  Simple modular law (B&dM 4.16) -/

/-- **B&dM 4.16**: `Simple S → (R∩T≫S°)≫S = (R≫S)∩T`.
    `⊒` is `modular_le`; `⊑` uses `inter_comp_le` (A4_1) plus `Simple S`. -/
theorem simple_modular_eq {a b c : 𝒜} {S : b ⟶ c} (hS : Simple S) (R : a ⟶ b) (T : a ⟶ c) :
    (R ∩ T ≫ S°) ≫ S = (R ≫ S) ∩ T := by
  apply le_antisymm
  · have h1 : (R ∩ T ≫ S°) ≫ S ⊑ (R ≫ S) ∩ ((T ≫ S°) ≫ S) := inter_comp_le R (T ≫ S°) S
    have h2 : (T ≫ S°) ≫ S ⊑ T := by
      rw [Cat.assoc]
      have h := comp_mono_left T hS; rwa [Cat.comp_id] at h
    exact le_trans h1 (le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h2))
  · exact modular_le R S T

/-- Mirror of S2_1's `simple_dist_inter` for postcomposition with the converse of a simple
    arrow: `(X ∩ Y) ≫ g° = (X ≫ g°) ∩ (Y ≫ g°)` (B&dM 4.17 mirrored via reciprocation). -/
theorem simple_dist_inter_recip {a b c : 𝒜} {g : c ⟶ b} (hg : Simple g) (X Y : a ⟶ b) :
    (X ∩ Y) ≫ g° = (X ≫ g°) ∩ (Y ≫ g°) := by
  have hr := congrArg Allegory.recip (simple_dist_inter hg (X°) (Y°))
  simp only [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_recip] at hr
  exact hr

/-! ## §4.2  Map shunting rules (B&dM 4.19, 4.20)

  The workhorses of relational program calculation: composing with a total function on
  one side of an inequality is equivalent to composing with its converse on the other. -/

/-- An entire arrow satisfies `1 ⊑ R≫R°` (the other half of `dom R = 1 ∩ R≫R°` collapsing).
    Canonical public home of a fact several files re-derived inline (A4_3, A4_4, S2_1 proofs). -/
theorem entire_id_le {a b : 𝒜} {R : a ⟶ b} (h : Entire R) : Cat.id a ⊑ R ≫ R° := by
  dsimp [Entire, dom] at h
  rw [← h]; exact inter_lb_right _ _

/-- **B&dM 4.19**: for a map `f`, `R≫f ⊑ S ↔ R ⊑ S≫f°`. -/
theorem map_shunt_right {a b c : 𝒜} {f : b ⟶ c} (hf : Map f) (R : a ⟶ b) (S : a ⟶ c) :
    R ≫ f ⊑ S ↔ R ⊑ S ≫ f° := by
  constructor
  · intro h
    have hent : Cat.id b ⊑ f ≫ f° := entire_id_le hf.1
    have h1 : R ⊑ R ≫ (f ≫ f°) := by
      have h1a := comp_mono_left R hent; rwa [Cat.comp_id] at h1a
    have h2 : R ≫ (f ≫ f°) ⊑ S ≫ f° := by
      rw [← Cat.assoc]; exact comp_mono_right h f°
    exact le_trans h1 h2
  · intro h
    have h1 : R ≫ f ⊑ (S ≫ f°) ≫ f := comp_mono_right h f
    have h2 : (S ≫ f°) ≫ f ⊑ S := by
      rw [Cat.assoc]
      have h2a := comp_mono_left S hf.2; rwa [Cat.comp_id] at h2a
    exact le_trans h1 h2

/-- **B&dM 4.20**: for a map `f`, `f°≫R ⊑ S ↔ R ⊑ f≫S`. -/
theorem map_shunt_left {a b c : 𝒜} {f : b ⟶ a} (hf : Map f) (R : b ⟶ c) (S : a ⟶ c) :
    f° ≫ R ⊑ S ↔ R ⊑ f ≫ S := by
  constructor
  · intro h
    have hent : Cat.id b ⊑ f ≫ f° := entire_id_le hf.1
    have h1 : R ⊑ (f ≫ f°) ≫ R := by
      have h1a := comp_mono_right hent R; rwa [Cat.id_comp] at h1a
    have h2 : (f ≫ f°) ≫ R ⊑ f ≫ S := by
      rw [Cat.assoc]; exact comp_mono_left f h
    exact le_trans h1 h2
  · intro h
    have h1 : f° ≫ R ⊑ f° ≫ (f ≫ S) := comp_mono_left f° h
    have h2 : f° ≫ (f ≫ S) ⊑ S := by
      rw [← Cat.assoc]
      have h2a := comp_mono_right hf.2 S; rwa [Cat.id_comp] at h2a
    exact le_trans h1 h2

/-! ## §4.2  Proposition 4.1

  A pair of inequations in opposite directions forces the two arrows to be converse maps.
  `shunt_recip_le` is the common half of the argument, applied twice (once directly, once
  to the reciprocated pair) to get both `S ⊑ R°` and `R° ⊑ S`. -/

/-- If `id ⊑ X` (for `X : a ⟶ a`) then `X` is entire: `dom X` sandwiches between `id`
    (always, `dom_coreflexive`) and `dom X` itself (via `dom_mono_of_le` from `id ⊑ X`
    and `dom (id) = id`). -/
private theorem entire_of_id_le {a : 𝒜} {X : a ⟶ a} (h : Cat.id a ⊑ X) : Entire X := by
  have hdomid : dom (Cat.id a) = Cat.id a := by
    dsimp [dom]; rw [recip_id, Cat.comp_id, Allegory.inter_idem]
  have h1 : dom (Cat.id a) ⊑ dom X := dom_mono_of_le h
  rw [hdomid] at h1
  exact le_antisymm (dom_coreflexive X) h1

/-- Common half of Prop 4.1's argument: `id_p ⊑ R≫S` and `S≫R ⊑ id_q` force `S ⊑ R°`.
    (`R` is entire by `entire_of_id_le`+`entire_of_comp_entire`, giving `id_p ⊑ R≫R°`;
    then `S ⊑ S≫(R≫R°) = (S≫R)≫R° ⊑ id_q≫R° = R°`.) -/
private theorem shunt_recip_le {p q : 𝒜} {R : p ⟶ q} {S : q ⟶ p}
    (h1 : Cat.id p ⊑ R ≫ S) (h2 : S ≫ R ⊑ Cat.id q) : S ⊑ R° := by
  have hR_entire : Entire R := entire_of_comp_entire (entire_of_id_le h1)
  have hRR : Cat.id p ⊑ R ≫ R° := by
    dsimp [Entire, dom] at hR_entire
    rw [← hR_entire]; exact inter_lb_right _ _
  have step1 : S ⊑ S ≫ (R ≫ R°) := by
    have h1a := comp_mono_left S hRR; rwa [Cat.comp_id] at h1a
  have step2 : S ≫ (R ≫ R°) ⊑ Cat.id q ≫ R° := by
    rw [← Cat.assoc]; exact comp_mono_right h2 R°
  rw [Cat.id_comp] at step2
  exact le_trans step1 step2

/-- **Prop 4.1**: if `id_a ⊑ R≫S` and `S≫R ⊑ id_b` then `S = R°` and `R` is a map. -/
theorem recip_of_comp_id {a b : 𝒜} {R : a ⟶ b} {S : b ⟶ a}
    (h1 : Cat.id a ⊑ R ≫ S) (h2 : S ≫ R ⊑ Cat.id b) : S = R° ∧ Map R := by
  have hSR : S ⊑ R° := shunt_recip_le h1 h2
  have h1'' : Cat.id a ⊑ S° ≫ R° := by
    have hr := recip_mono h1; rwa [recip_id, Allegory.recip_comp] at hr
  have h2'' : R° ≫ S° ⊑ Cat.id b := by
    have hr := recip_mono h2; rwa [Allegory.recip_comp, recip_id] at hr
  have hRS : R° ⊑ S := by
    have h := shunt_recip_le h1'' h2''; rwa [Allegory.recip_recip] at h
  have hEq : S = R° := le_antisymm hSR hRS
  have hEnt : Entire R := entire_of_comp_entire (entire_of_id_le h1)
  have hSim : Simple R := by
    show R° ≫ R ⊑ Cat.id b
    rw [← hEq]; exact h2
  exact ⟨hEq, hEnt, hSim⟩

/-! ## §4.2  Symmetric-transitive characterization (Ex 4.14) -/

/-- **Ex 4.14**: `Symmetric R ∧ Transitive R ↔ R = R≫R°`. -/
theorem symmetric_transitive_iff_comp_recip {a : 𝒜} {R : a ⟶ a} :
    (Symmetric R ∧ Transitive R) ↔ R ≫ R° = R := by
  constructor
  · rintro ⟨hSym, hTrans⟩
    have hEq : R° = R := symmetric_eq hSym
    apply le_antisymm
    · rw [hEq]; exact hTrans
    · have h1 : R ⊑ (R ≫ R°) ≫ R := le_comp_recip_comp R
      rw [hEq] at h1
      have h2 : (R ≫ R) ≫ R ⊑ R ≫ R := comp_mono_right hTrans R
      have h3 : R ⊑ R ≫ R := le_trans h1 h2
      rwa [hEq]
  · intro hEq
    have hEqR : R° = R := by
      have step : (R ≫ R°)° = R ≫ R° := by rw [Allegory.recip_comp, Allegory.recip_recip]
      calc R° = (R ≫ R°)° := (congrArg Allegory.recip hEq).symm
        _ = R ≫ R° := step
        _ = R := hEq
    refine ⟨(symmetric_iff R).mpr hEqR, ?_⟩
    show R ≫ R ⊑ R
    have heq2 : R ≫ R = R := by
      calc R ≫ R = R ≫ R° := by rw [hEqR]
        _ = R := hEq
    rw [heq2]
    exact le_refl R

/-! ## §4.2  Simple morphisms and their reciprocal-composite (Ex 4.15) -/

/-- **Ex 4.15**: `Simple S → S = S≫S°≫S`. -/
theorem simple_comp_recip_comp {a b : 𝒜} {S : a ⟶ b} (hS : Simple S) : S = (S ≫ S°) ≫ S := by
  apply le_antisymm
  · exact le_comp_recip_comp S
  · have h := comp_mono_left S hS
    rw [Cat.comp_id] at h
    rwa [← Cat.assoc] at h

/-! ## §4.2  Monic maps (Ex 4.19)

  The `←` half (`m≫m°=id → jointly cancellable`) is pure rewriting.  The `→` half needs
  a separating pair of maps into the (arbitrary) test object `c`, which in a bare
  allegory requires `c` to be tabular/have enough maps — dropped here (see report);
  only the trivial standalone half `id ⊑ m≫m°` (entireness) is kept alongside it. -/

/-- **Ex 4.19** (`⊒` half): if `m≫m° = id_a` for a map `m` then `m` is jointly
    cancellable among maps into its source. -/
theorem map_monic_of_comp_recip {a b : 𝒜} {m : a ⟶ b} (hmm : m ≫ m° = Cat.id a)
    {c : 𝒜} (f g : c ⟶ a) (h : f ≫ m = g ≫ m) : f = g := by
  calc f = f ≫ (m ≫ m°) := by rw [hmm, Cat.comp_id]
    _ = (f ≫ m) ≫ m° := by rw [Cat.assoc]
    _ = (g ≫ m) ≫ m° := by rw [h]
    _ = g ≫ (m ≫ m°) := by rw [Cat.assoc]
    _ = g := by rw [hmm, Cat.comp_id]

/-- **Ex 4.19**: for any map `m`, `id_a ⊑ m≫m°` (entireness in inequality form). -/
theorem id_le_comp_recip_of_map {a b : 𝒜} {m : a ⟶ b} (hm : Map m) : Cat.id a ⊑ m ≫ m° := by
  have h := hm.1
  dsimp [Entire, dom] at h
  rw [← h]; exact inter_lb_right _ _

end Freyd.Alg
