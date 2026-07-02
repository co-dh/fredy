/-
  Bird & de Moor, *Algebra of Programming* §9.1  Dynamic programming: theory (book pp. 219-224)
  — CORE (Theorem 9.1).

  The optimisation problem is `min R · Λ(⦇h⦈·⦇T⦈°)` (mirrored: `A H ≫ minRel R` with
  `H := (relCata I T)° ≫ relCata I h`): unfold the input through the coalgebra `T°`, refold
  through the F-algebra `h` (a function), and take an `R`-minimum over all results.  DYNAMIC
  PROGRAMMING is the recursion that decomposes the input in ALL possible ways, solves the
  subproblems recursively, and assembles an optimum from the partial results (the principle of
  optimality) — the least fixed point `μX. min R · P(h·FX) · ΛT°`.  **Theorem 9.1**: if `h` is
  monotonic on `R` (and `R` transitive), the recursion refines the specification.

  MIRRORING (diagram order, B&dM `X·Y` = Fredy `Y ≫ X`; B&dM `R/S` = Fredy `leftDiv S R`):
  - B&dM `H = ⦇h⦈·⦇T⦈°` is `(relCata I T)° ≫ relCata I h : b ⟶ a` (`h : F.obj a ⟶ a`,
    `T : F.obj b ⟶ b`); the fixed-point equation `H = h·FH·T°` is `Fredy.A6_3`'s `hylo_fixed`:
    `T° ≫ F.map H ≫ h = H`.
  - B&dM `M = min R·ΛH` is `A H ≫ minRel R`.
  - the recursion body `min R · P(h·FX) · ΛT°` is
    `A (T°) ≫ powerRel (F.map X ≫ h) ≫ minRel R`.
  - rule (9.4) `min R·PX ⊆ (X·∈) ∩ ((R·X)/∋)` is `Fredy.A7_1`'s `powerRel_comp_minRel_le`;
    `ΛT°·T ⊆ ∋` is `Fredy.A8_1`'s `recip_comp_A_le_recip_eps` at `T°`.

  Setting: `UnguardedPowerLCDA` (`Fredy.A6_2`), continuing chapters 7 and 8.
-/
import Fredy.A7_2
import Fredy.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-! ## Theorem 9.1 (B&dM pp. 220-221) -/

/-- **Core of Theorem 9.1**: `M = min R·ΛH` (mirrored `A H ≫ minRel R`) is a PREFIXED point of
    the dynamic-programming body, for ANY `H` satisfying the hylomorphism fixed-point equation
    `H = h·FH·T°` (mirrored `T° ≫ F.map H ≫ h = H`) — Theorems 9.1/9.2 and the exercise
    variants all instantiate `H := ⦇h⦈·⦇T⦈°`.  The two inclusions (9.2) and (9.3) of the book's
    proof are exactly the components of `min`'s universal property (`le_A_comp_minRel_iff`). -/
theorem dp_prefixed (hFr : F.PreservesRecip) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b}
    {R : a ⟶ a} {H : b ⟶ a} (hh : Map h) (hmono : MonotonicAlg h R)
    (htrans : R ≫ R ⊑ R) (hHfix : T° ≫ F.map H ≫ h = H) :
    A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R ⊑ A H ≫ minRel R := by
  -- the two min-UP components of `M ⊑ min R·ΛH`: `M ⊑ H` and `M·H° ⊑ R` (mirrored)
  obtain ⟨hMH, hHMR⟩ := le_A_comp_minRel_iff.mp (le_refl (A H ≫ minRel R))
  -- rule (9.4) at `X := h·FM`
  have h94 := powerRel_comp_minRel_le (F.map (A H ≫ minRel R) ≫ h) R
  apply le_A_comp_minRel_iff.mpr
  constructor
  · -- (9.2): `min R·P(h·FM)·ΛT° ⊆ H`
    have s1 : A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        ⊑ A (T°) ≫ ∋ (F.obj b) ≫ F.map (A H ≫ minRel R) ≫ h :=
      comp_mono_left _ (le_trans h94 (inter_lb_left _ _))
    -- Λ cancellation: `∈·ΛT° = T°`
    have s2 : A (T°) ≫ ∋ (F.obj b) ≫ F.map (A H ≫ minRel R) ≫ h
        = T° ≫ F.map (A H ≫ minRel R) ≫ h := by
      rw [← Cat.assoc (A (T°)) (∋ (F.obj b)) _, A_eps_eq']
    -- `M ⊑ H`, then the fixed-point equation
    have s3 : T° ≫ F.map (A H ≫ minRel R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [s2] at s1
    rw [hHfix] at s3
    exact le_trans s1 s3
  · -- (9.3): `min R·P(h·FM)·ΛT°·H° ⊆ R`
    -- the lower-bound component of (9.4)
    have hL : powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        ⊑ leftDiv ((∋ (F.obj b))°) ((F.map (A H ≫ minRel R) ≫ h) ≫ R) :=
      le_trans h94 (inter_lb_right _ _)
    -- `ΛT°·T ⊆ ∋` mirrored
    have hTA : T ≫ A (T°) ⊑ (∋ (F.obj b))° := by
      have h0 := recip_comp_A_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    -- `H° = T·FH°·h°` conversed to diagram order: `H° = h° ≫ F.map H° ≫ T`
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H,
          Cat.assoc]
      rw [← h1, hHfix]
    -- the tail after peeling `h° ≫ F.map H°`: division cancels against `∋`
    have htail : T ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        ⊑ (F.map (A H ≫ minRel R) ≫ h) ≫ R := by
      have t1 : T ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
          ⊑ T ≫ A (T°) ≫ leftDiv ((∋ (F.obj b))°) ((F.map (A H ≫ minRel R) ≫ h) ≫ R) :=
        comp_mono_left _ (comp_mono_left _ hL)
      have t2 : T ≫ A (T°) ≫ leftDiv ((∋ (F.obj b))°) ((F.map (A H ≫ minRel R) ≫ h) ≫ R)
          ⊑ (∋ (F.obj b))° ≫ leftDiv ((∋ (F.obj b))°) ((F.map (A H ≫ minRel R) ≫ h) ≫ R) := by
        rw [← Cat.assoc T (A (T°)) _]
        exact comp_mono_right hTA _
      exact le_trans t1 (le_trans t2 (leftDiv_comp_le _ _))
    -- split `H°` in front and reassociate
    have c1 : H° ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        = (h° ≫ F.map (H°) ≫ T)
            ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T)
          ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        = (h° ≫ F.map (H°))
            ≫ T ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°))
          ≫ T ≫ A (T°) ≫ powerRel (F.map (A H ≫ minRel R) ≫ h) ≫ minRel R
        ⊑ (h° ≫ F.map (H°)) ≫ (F.map (A H ≫ minRel R) ≫ h) ≫ R :=
      comp_mono_left _ htail
    -- collapse: `F(M·H°) ⊆ FR` then conjugated monotonicity and transitivity
    have hcollapse : (h° ≫ F.map (H°)) ≫ (F.map (A H ≫ minRel R) ≫ h) ≫ R ⊑ R ≫ R := by
      have hFRM : F.map (H°) ≫ F.map (A H ≫ minRel R) ⊑ F.map R := by
        rw [← F.map_comp]
        exact F.map_mono hHMR
      have hinner : h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h ⊑ R := by
        have hx : h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h ⊑ h° ≫ F.map R ≫ h := by
          rw [← Cat.assoc (F.map (H°)) (F.map (A H ≫ minRel R)) h]
          exact comp_mono_left _ (comp_mono_right hFRM h)
        exact le_trans hx ((monotonicAlg_iff_conj hh).mp hmono)
      have hre : (h° ≫ F.map (H°)) ≫ (F.map (A H ≫ minRel R) ≫ h) ≫ R
          = (h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h) ≫ R := by
        simp only [Cat.assoc]
      rw [hre]
      exact comp_mono_right hinner R
    rw [c1, c2]
    exact le_trans (le_trans hbound hcollapse) htrans

/-- **Theorem 9.1 (B&dM p.220)**, the basic theorem of DYNAMIC PROGRAMMING:
    `(μX : min R·P(h·FX)·ΛT°) ⊆ min R·ΛH` for `H = ⦇h⦈·⦇T⦈°`, mirrored — if the algebra `h`
    is monotonic on the transitive `R`, then decomposing the input in all possible ways
    (`ΛT°`), solving subproblems recursively (`P(h·FX)`) and keeping an optimum of the partial
    results (`min R`) refines "generate everything, then pick a global optimum".
    By Knaster–Tarski (`mu_le_of_prefixed`) via `dp_prefixed`. -/
theorem dynamic_programming (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R) (htrans : R ≫ R ⊑ R) :
    mu (fun X : b ⟶ a => A (T°) ≫ powerRel (F.map X ≫ h) ≫ minRel R)
      ⊑ A ((relCata I T)° ≫ relCata I h) ≫ minRel R :=
  mu_le_of_prefixed (dp_prefixed hFr hh hmono htrans (hylo_fixed hFr I h T))

end Freyd.Alg
