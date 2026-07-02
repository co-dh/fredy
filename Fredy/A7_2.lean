/-
  Bird & de Moor, *Algebra of Programming* §7.2  Monotonic algebras and the GREEDY THEOREM
  (book pp. 172-175).

  A DYNAMIC-PROGRAMMING / GREEDY-ALGORITHM problem is a hylomorphism `⦇min R⦈·ΛS` (mirrored
  `relCata I (A S ≫ minRel R)`): unfold via a coalgebra `S`, then at every step keep only the
  `R`-minimal choices.  Theorem 7.2 (the GREEDY THEOREM) gives conditions under which this
  "keep minima at every step" strategy is safe to postpone to the very end: if `S` is
  MONOTONIC on the preorder `R°`, then greedily filtering at each unfold step refines the
  same computation done by filtering only once, at the end, on the plain catamorphism `⦇S⦈`.

  MIRRORING (diagram order, B&dM `X·Y` = Fredy `Y ≫ X`):
  - B&dM `S·FR ⊆ R·S` (monotonicity of the algebra `S` w.r.t. `R`) mirrors to
    `F.map R ≫ S ⊑ S ≫ R`.
  - B&dM `f·FR·f° ⊆ R` mirrors to `f° ≫ F.map R ≫ f ⊑ R`; B&dM `FR ⊆ f°·R·f` mirrors to
    `F.map R ⊑ f ≫ R ≫ f°`.
  - B&dM `f·F(min R) ⊆ min R·Λ(f·F∈)` (Distributes, `f` DISTRIBUTES over `min R`) mirrors to
    `F.map (minRel R) ≫ f ⊑ A (F.map (∋ a) ≫ f) ≫ minRel R`.
  - B&dM `⦇min R·ΛS⦈ ⊆ min R·Λ⦇S⦈` (the Greedy Theorem) mirrors to
    `relCata I (A S ≫ minRel R) ⊑ A (relCata I S) ≫ minRel R`.

  Setting: `UnguardedPowerLCDA` (`Fredy.A6_2`), plus `Fredy.A6_3`'s hylomorphism theorem
  (`hylo_le_of_prefixed`) and `Fredy.A7_1`'s `minRel`/`maxRel` core.
-/
import Fredy.A7_1
import Fredy.A6_3

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-! ## Monotonic algebras (B&dM p.172) -/

section MonotonicAlg

variable {R : a ⟶ a} {S f : F.obj a ⟶ a}

/-- **B&dM p.172**: `S` is MONOTONIC on `R` when `S·FR ⊆ R·S`, mirrored `F.map R ≫ S ⊑ S ≫ R`.
    (An algebra `S` "does not care" whether `R`-related recursive results are computed before
    or after applying `S`.) -/
def MonotonicAlg (S : F.obj a ⟶ a) (R : a ⟶ a) : Prop := F.map R ≫ S ⊑ S ≫ R

/-- Function form (conjugation), for `f` a MAP: `f·FR·f° ⊆ R`, mirrored. -/
theorem monotonicAlg_iff_conj (hf : Map f) : MonotonicAlg f R ↔ f° ≫ F.map R ≫ f ⊑ R :=
  (map_shunt_left hf (F.map R ≫ f) R).symm

/-- Function form (sandwich), for `f` a MAP: `FR ⊆ f°·R·f`, mirrored. -/
theorem monotonicAlg_iff_sandwich (hf : Map f) : MonotonicAlg f R ↔ F.map R ⊑ f ≫ R ≫ f° := by
  rw [← Cat.assoc]
  exact map_shunt_right hf (F.map R) (f ≫ R)

/-- `f` is monotonic on `R` iff it is monotonic on `R°` — conjugation is preserved by converse,
    using `hFr` to push `F.map` through `°`. -/
theorem monotonicAlg_recip_iff (hf : Map f) (hFr : F.PreservesRecip) :
    MonotonicAlg f R ↔ MonotonicAlg f R° := by
  rw [monotonicAlg_iff_conj hf, monotonicAlg_iff_conj hf]
  have hconj : ∀ T : a ⟶ a, (f° ≫ F.map T ≫ f)° = f° ≫ F.map T° ≫ f := fun T => by
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, ← hFr T]
  constructor
  · intro h
    have h2 := recip_mono h
    rwa [hconj R] at h2
  · intro h
    have h2 := recip_mono h
    rw [hconj R°, Allegory.recip_recip] at h2
    exact h2

end MonotonicAlg

/-! ## Distributivity and Theorem 7.1 (B&dM p.172-173)

  `f` DISTRIBUTES over `min R` when postponing the minimum-taking past `f` (on the `F`-image
  side) agrees with taking it first: `f·F(min R) ⊆ min R·Λ(f·F∈)`.  Theorem 7.1 relates this
  to `f` being monotonic on `R`. -/

section Distributes

variable {R : a ⟶ a} {f : F.obj a ⟶ a}

/-- **B&dM p.172**: `f` DISTRIBUTES over `min R`: `f·F(min R) ⊆ min R·Λ(f·F∈)`, mirrored. -/
def Distributes (f : F.obj a ⟶ a) (R : a ⟶ a) : Prop :=
  F.map (minRel R) ≫ f ⊑ A (F.map (∋ a) ≫ f) ≫ minRel R

/-- **Theorem 7.1 (B&dM p.172), unconditional half**: monotonicity of `f` on `R` implies `f`
    distributes over `min R`. -/
theorem distributes_of_monotonicAlg (hf : Map f) (hFr : F.PreservesRecip)
    (hmono : MonotonicAlg f R) : Distributes f R := by
  unfold Distributes
  apply le_A_comp_minRel_iff.mpr
  refine ⟨comp_mono_right (F.map_mono (minRel_le_eps R)) f, ?_⟩
  have step1 : (F.map (∋ a) ≫ f)° = f° ≫ F.map ((∋ a)°) := by
    rw [Allegory.recip_comp, ← hFr (∋ a)]
  have step2 : F.map ((∋ a)°) ≫ F.map (minRel R) = F.map ((∋ a)° ≫ minRel R) :=
    (F.map_comp _ _).symm
  have step3 : (∋ a)° ≫ minRel R ⊑ R :=
    le_trans (comp_mono_left _ (minRel_le_lb R)) (leftDiv_comp_le _ R)
  have step4 : F.map ((∋ a)° ≫ minRel R) ⊑ F.map R := F.map_mono step3
  have heq : (F.map (∋ a) ≫ f)° ≫ (F.map (minRel R) ≫ f)
      = f° ≫ F.map ((∋ a)° ≫ minRel R) ≫ f := by
    rw [step1, Cat.assoc, ← Cat.assoc (F.map ((∋ a)°)) (F.map (minRel R)) f, step2]
  rw [heq]
  exact le_trans (comp_mono_left _ (comp_mono_right step4 f)) ((monotonicAlg_iff_conj hf).mp hmono)

/-- **Theorem 7.1 (B&dM p.172), converse half**: given `R = min R·∋` (B&dM Ex 7.9, taken here
    as a hypothesis — its `⊒` half needs TABULATIONS, via Ex 7.8's pairing, not otherwise
    available in this setting), distributivity of `f` over `min R` implies `f` is monotonic
    on `R`. -/
theorem monotonicAlg_of_distributes (hf : Map f) (hFr : F.PreservesRecip)
    (hpair : R ⊑ (∋ a)° ≫ minRel R) (hdist : Distributes f R) : MonotonicAlg f R := by
  apply (monotonicAlg_iff_conj hf).mpr
  have hdist' : F.map (minRel R) ≫ f ⊑ A (F.map (∋ a) ≫ f) ≫ minRel R := hdist
  have hXrecip : (F.map (∋ a) ≫ f)° = f° ≫ F.map ((∋ a)°) := by
    rw [Allegory.recip_comp, ← hFr (∋ a)]
  have hXA : (F.map (∋ a) ≫ f)° ≫ A (F.map (∋ a) ≫ f) ⊑ (∋ a)° := by
    have hrecip : (F.map (∋ a) ≫ f)° = (∋ a)° ≫ (A (F.map (∋ a) ≫ f))° :=
      calc (F.map (∋ a) ≫ f)°
          = (A (F.map (∋ a) ≫ f) ≫ ∋ a)° := by rw [A_eps_eq']
        _ = (∋ a)° ≫ (A (F.map (∋ a) ≫ f))° := Allegory.recip_comp _ _
    calc (F.map (∋ a) ≫ f)° ≫ A (F.map (∋ a) ≫ f)
        = ((∋ a)° ≫ (A (F.map (∋ a) ≫ f))°) ≫ A (F.map (∋ a) ≫ f) := by rw [hrecip]
      _ = (∋ a)° ≫ ((A (F.map (∋ a) ≫ f))° ≫ A (F.map (∋ a) ≫ f)) := Cat.assoc _ _ _
      _ ⊑ (∋ a)° ≫ Cat.id _ := comp_mono_left _ (A_is_map' (F.map (∋ a) ≫ f)).2
      _ = (∋ a)° := Cat.comp_id _
  have h1 : F.map R ⊑ F.map ((∋ a)° ≫ minRel R) := F.map_mono hpair
  have hmapcomp : F.map ((∋ a)° ≫ minRel R) = F.map ((∋ a)°) ≫ F.map (minRel R) := F.map_comp _ _
  have hUP : (∋ a)° ≫ minRel R ⊑ R :=
    le_trans (comp_mono_left _ (minRel_le_lb R)) (leftDiv_comp_le _ R)
  have hregroup : f° ≫ F.map ((∋ a)° ≫ minRel R) ≫ f
      = (F.map (∋ a) ≫ f)° ≫ (F.map (minRel R) ≫ f) := by
    rw [hmapcomp, hXrecip]; simp only [Cat.assoc]
  have hA : f° ≫ F.map R ≫ f ⊑ f° ≫ F.map ((∋ a)° ≫ minRel R) ≫ f :=
    comp_mono_left _ (comp_mono_right h1 f)
  rw [hregroup] at hA
  have hC : (F.map (∋ a) ≫ f)° ≫ (F.map (minRel R) ≫ f)
      ⊑ (F.map (∋ a) ≫ f)° ≫ (A (F.map (∋ a) ≫ f) ≫ minRel R) := comp_mono_left _ hdist'
  have hA2 := le_trans hA hC
  rw [← Cat.assoc (F.map (∋ a) ≫ f)° (A (F.map (∋ a) ≫ f)) (minRel R)] at hA2
  have hE : ((F.map (∋ a) ≫ f)° ≫ A (F.map (∋ a) ≫ f)) ≫ minRel R ⊑ (∋ a)° ≫ minRel R :=
    comp_mono_right hXA _
  exact le_trans (le_trans hA2 hE) hUP

end Distributes

/-! ## Theorem 7.2 — THE GREEDY THEOREM (B&dM p.173)

  If `S` is monotonic on the preorder `R°`, greedily filtering `R`-minima at every unfold
  step (`⦇min R·ΛS⦈`) refines filtering once, on the plain catamorphism (`min R·Λ⦇S⦈`).
  Only TRANSITIVITY of `R` is used. -/

section Greedy

variable {R : a ⟶ a} {S : F.obj a ⟶ a}

/-- **Theorem 7.2 (THE GREEDY THEOREM, B&dM p.173)**: `⦇min R·ΛS⦈ ⊆ min R·Λ⦇S⦈` if `S` is
    monotonic on the preorder `R°`, mirrored. -/
theorem greedy (hFr : F.PreservesRecip) (I : InitialAlgebra F) {R : a ⟶ a} {S : F.obj a ⟶ a}
    (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg S R°) :
    relCata I (A S ≫ minRel R) ⊑ A (relCata I S) ≫ minRel R := by
  apply le_A_comp_minRel_iff.mpr
  refine ⟨?_, ?_⟩
  · have hi : A S ≫ minRel R ⊑ S := by
      have h := comp_mono_left (A S) (minRel_le_eps R)
      rwa [A_eps_eq'] at h
    exact relCata_mono I hi
  · have step1 : S° ≫ F.map R ⊑ R ≫ S° := by
      have h := recip_mono hmono
      have heqL : (F.map R° ≫ S)° = S° ≫ F.map R := by
        rw [Allegory.recip_comp, hFr R, Allegory.recip_recip]
      have heqR : (S ≫ R°)° = R ≫ S° := by
        rw [Allegory.recip_comp, Allegory.recip_recip]
      rwa [heqL, heqR] at h
    have step2 : A S ≫ minRel R ⊑ leftDiv S° R := by
      rw [A_comp_minRel]; exact inter_lb_right _ _
    have hprefixed : S° ≫ F.map R ≫ (A S ≫ minRel R) ⊑ R := by
      have hB : (S° ≫ F.map R) ≫ (A S ≫ minRel R) ⊑ (R ≫ S°) ≫ (A S ≫ minRel R) :=
        comp_mono_right step1 _
      rw [Cat.assoc S° (F.map R) (A S ≫ minRel R), Cat.assoc R S° (A S ≫ minRel R)] at hB
      have hC : R ≫ (S° ≫ (A S ≫ minRel R)) ⊑ R ≫ (S° ≫ leftDiv S° R) :=
        comp_mono_left _ (comp_mono_left _ step2)
      have hD : R ≫ (S° ≫ leftDiv S° R) ⊑ R ≫ R := comp_mono_left _ (leftDiv_comp_le _ _)
      exact le_trans hB (le_trans hC (le_trans hD htrans))
    exact hylo_le_of_prefixed hFr I hprefixed

/-- Max-form corollary: `greedy` at `R°` (`maxRel R = minRel R°`), with `S` now assumed
    monotonic on `R` directly.  Transitivity of `R°` and the needed `MonotonicAlg S (R°)°`
    both reduce to the given hypotheses via `recip_mono`/`Allegory.recip_recip`. -/
theorem greedy_max (hFr : F.PreservesRecip) (I : InitialAlgebra F) {R : a ⟶ a} {S : F.obj a ⟶ a}
    (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg S R) :
    relCata I (A S ≫ maxRel R) ⊑ A (relCata I S) ≫ maxRel R := by
  have htrans' : R° ≫ R° ⊑ R° := by
    have h := recip_mono htrans
    rwa [Allegory.recip_comp] at h
  have hmono' : MonotonicAlg S (R°)° := by
    show F.map ((R°)°) ≫ S ⊑ S ≫ (R°)°
    rw [Allegory.recip_recip]; exact hmono
  exact greedy hFr I htrans' hmono'

end Greedy

/-! ## Exercises 7.34 and 7.37 -/

section Exercises

variable {R : a ⟶ a} {S f : F.obj a ⟶ a}

/-- **Ex 7.34**: an algebra monotonic on `R` w.r.t. its own initial algebra structure map
    forces `R` to be reflexive — `⦇α⦈ = id ⊆ R` follows from `α` being the least prefixed
    point of the `R`-recursion. -/
theorem reflexive_of_alpha_monotonicAlg (I : InitialAlgebra F) {R : I.t ⟶ I.t}
    (hmono : MonotonicAlg I.α R) : Cat.id I.t ⊑ R := by
  rw [← relCata_alpha I]
  apply relCata_le_of_prefixed
  have h2 := comp_mono_left I.α° hmono
  rwa [← Cat.assoc I.α° I.α R, I.recip_alpha_alpha, Cat.id_comp] at h2

/-- **Ex 7.37 variant**: if `f` (an arbitrary algebra, monotonic on `R`) REFINES a greedy
    candidate `A S ≫ minRel R`, its catamorphism already lands inside `min R·Λ⦇S⦈` — a
    one-hypothesis strengthening of `greedy` that does not require `f` itself to be of the
    form `A S ≫ minRel R` up to equality. -/
theorem greedy_of_refinement (hFr : F.PreservesRecip) (I : InitialAlgebra F) {R : a ⟶ a}
    {S : F.obj a ⟶ a} {f : F.obj a ⟶ a} (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg f R)
    (href : f ⊑ A S ≫ minRel R) : relCata I f ⊑ A (relCata I S) ≫ minRel R := by
  obtain ⟨hfS, hSf⟩ := le_A_comp_minRel_iff.mp href
  apply le_A_comp_minRel_iff.mpr
  refine ⟨relCata_mono I hfS, ?_⟩
  apply hylo_le_of_prefixed hFr I
  have hA : S° ≫ (F.map R ≫ f) ⊑ S° ≫ (f ≫ R) := comp_mono_left _ hmono
  rw [← Cat.assoc S° f R] at hA
  have hB : (S° ≫ f) ≫ R ⊑ R ≫ R := comp_mono_right hSf _
  exact le_trans hA (le_trans hB htrans)

/- **Ex 7.38** (`min R·ΛS·min(FR) ⊆ min R·ES` mirrored:
   `minRel (F.map R) ≫ A S ≫ minRel R ⊑ existsImage S ≫ minRel R` for `MonotonicAlg S R°`):
   DROPPED.  Unlike Ex 7.34/7.37, which reduce directly to `relCata_le_of_prefixed` /
   `hylo_le_of_prefixed` plus the algebra calculus already on hand, this inequality is about
   `minRel` commuting past the EXISTENTIAL IMAGE `existsImage` — a genuinely new absorption
   law (`A W ≫ minRel R` vs. `existsImage S ≫ minRel R` with `W := ∋ (F.obj a) ≫ S`) not
   derivable from `A_comp_minRel`/`le_A_comp_minRel_iff` alone: the left-hand side
   `minRel (F.map R) ≫ A S ≫ minRel R` is not of the `A _ ≫ minRel R` shape the universal
   property needs, and no absorption lemma connecting `minRel` with `existsImage` (the B&dM
   p.105 `A`/`E` calculus of `Fredy.A4_6`) exists in this file's API.  Left as a documented
   gap; nothing downstream in this file depends on it. -/

/- **Ex 7.33** (pointwise translation of the greedy theorem into a componentwise/relational
   idiom): SKIP — the book's exercise here is a restatement in pointwise notation with no
   additional formal content beyond `greedy` itself in this point-free setting. -/

end Exercises

end Freyd.Alg
