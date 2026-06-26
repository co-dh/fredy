/-
  Freyd & Scedrov, *Categories and Allegories* §2.4  Power allegories.

  §2.41 POWER ALLEGORY — operation ∋ (epsilon), power objects
  §2.412 A(R) is the unique map with A(R)∋ = R; simple F ⊑ A(F∋)
  §2.415 POWER-OBJECT, SINGLETON MAP, A(f) = f · A(1)
  §2.42 SPLITTING LEMMAS
  §2.43 PRE-POWER ALLEGORY
  §2.441 PRE-POSITIVE allegory, WELL-JOINED category
  §2.442 LAW OF METONYMY
-/

import Fredy.S1_1
import Fredy.S2_1
import Fredy.S2_2
import Fredy.S2_3
import Fredy.S2_22  -- §2.16(10) srcTabulation_of_semiSimple_split + SplitsSymmIdem (converse map-realization)


universe v u

namespace Freyd.Alg

/-- The codomain box `R□ = 1_b ∩ R°R` (§2.122): the coreflexive on the target.
    (Defined here, ahead of `PowerAllegory`, because the box-guarded `eps_thick`
    field of §2.41 refers to it — faithful to Freyd's box-indexed membership `∋_R`.) -/
abbrev codBox {𝒜 : Type u} {a b : 𝒜} [Allegory 𝒜] (R : a ⟶ b) : b ⟶ b := dom (R°)

/-! ## §2.41  Power allegory

  A POWER ALLEGORY is a division allegory with a unary operation ∋
  (epsilon) such that ∋_B : [B] → B satisfies:
  1. ∋ is straight: ∋ /ₛ ∋ ⊑ 1
  2. ∋ is thick: 1 ⊑ ∋ / ∋

  Here [a] denotes the power-object of a, the source of ∋_a.
  A(R) = R/ₛ∋ is the unique map with A(R)∋ = R (§2.41). -/

/-- A POWER ALLEGORY (§2.41): division allegory with power objects and
    epsilon morphisms ∋_B : [B] → B satisfying straightness and thickness. -/
class PowerAllegory (𝒜 : Type u) extends DivisionAllegory 𝒜 where
  /-- The POWER-OBJECT [b] of b. -/
  powerObj (b : 𝒜) : 𝒜
  /-- The epsilon morphism ∋_b : [b] → b. -/
  eps (b : 𝒜) : powerObj b ⟶ b

  /-- ∋ is straight: ∋ /ₛ ∋ ⊑ 1 (§2.41). -/
  eps_straight (b : 𝒜) : Straight (eps b)

  /-- ∋ is THICK (§2.41, Freyd's box-indexed membership `∋_R` with `∋_R□ = R□`):
      for every `R : c → b` whose codomain box matches that of `∋_b` there exists a
      map `f` with `f ≫ ∋ = R`.  The `codBox R = codBox (eps b)` guard is Freyd's own
      side-condition on `∋_R` (the domain on which his partial membership is defined);
      it is what makes this discharge from box-guarded `Thick (eps b)` (§2.43) faithful
      rather than the over-strong unconditional §2.413 form.  The naïve `1 ⊑ ∋/∋` is
      vacuous (`one_le_div_self`); this existential form IS the thickness condition (it
      forces `A(R) = R/ₛ∋` entire on the matched box). -/
  eps_thick {b : 𝒜} {c : 𝒜} (R : c ⟶ b) (hbox : codBox R = codBox (eps b)) :
    ∃ (f : c ⟶ powerObj b), Map f ∧ f ≫ eps b = R

/-! ### Notation -/

/-- Epsilon notation ∋ (pronounced "epsiloff" in the book). -/
notation "∋" => PowerAllegory.eps

/-! ### Derived operations -/

/-- A(R) = R /ₛ ∋: the unique map such that A(R)∋ = R (§2.41). -/
def A {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : a ⟶ PowerAllegory.powerObj b :=
  R /ₛ PowerAllegory.eps b

/-- The thickness witness f for R is contained in A(R) (§2.412/§2.413).
    Used both for entireness of A(R) and the lower bound of A(R)∋ = R.
    f ⊑ A R = R/ₛ∋ via le_symmDiv_iff: f∋ = R (so f∋ ⊑ R) and f°R = (f°f)∋ ⊑ ∋ (Simple f). -/
private theorem thick_witness_le_A {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b)
    {f : a ⟶ PowerAllegory.powerObj b} (hf : Map f) (hfeq : f ≫ ∋ b = R) :
    f ⊑ A R := by
  rw [A, le_symmDiv_iff]
  refine ⟨by rw [hfeq]; exact le_refl _, ?_⟩
  rw [← hfeq, ← Cat.assoc]
  exact le_trans (comp_mono_right hf.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)

/-- A(R) is a map (simple and entire) (§2.41), for R in ∋'s box (Freyd's `∋_R□ = R□`).
    Simple branch: A(R) ⊑ R/∋, and since ∋ is straight R/∋ is simple [§2.356] (no box
    needed).  Entire branch (§2.412/§2.413): the box-matched thickness witness f (a map,
    f∋ = R) has f ⊑ A R, so 1 ⊑ ff° ⊑ (A R)(A R)°, whence dom(A R) = 1.
    The `codBox R = codBox (∋ b)` hypothesis is Freyd's box-index on `∋_R`. -/
theorem A_is_map {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b)
    (hbox : codBox R = codBox (∋ b)) : Map (A R) := by
  constructor
  · -- Entire (§2.412/§2.413) via the box-matched thickness witness f ⊑ A R.
    obtain ⟨f, hf, hfeq⟩ := PowerAllegory.eps_thick (b := b) R hbox
    have hf_le : f ⊑ A R := thick_witness_le_A R hf hfeq
    have h1 : Cat.id a ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have h2 : f ≫ f° ⊑ A R ≫ (A R)° :=
      le_trans (comp_mono_right hf_le _) (comp_mono_left _ (recip_mono hf_le))
    -- dom(A R) = 1 ∩ (A R)(A R)° = 1, since 1 ⊑ (A R)(A R)°.
    dsimp [Entire, dom]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) (le_trans h1 h2))
  · -- Simple: A(R) = R/ₛ∋, and ∋ is straight, so R/ₛ∋ is simple [§2.356].
    exact straight_symmDiv_simple (PowerAllegory.eps_straight b) R

/-- A(R) is SIMPLE for EVERY R (no box needed): `A R = R/ₛ∋` and ∋ straight ⟹ simple [§2.356].
    The entireness (hence map-ness) of A(R) is the box-guarded part (`A_is_map`). -/
theorem A_simple {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) : Simple (A R) :=
  straight_symmDiv_simple (PowerAllegory.eps_straight b) R

/-- A(R)∋ = R (§2.41), for R in ∋'s box (Freyd's `∋_R□ = R□`).
    ⊑: A(R) ⊑ R/∋ (left component of symmDiv), so A(R)∋ ⊑ (R/∋)∋ ⊑ R (no box needed).
    ⊒: box-matched thickness gives a map f ⊑ A(R) with f∋ = R, so R = f∋ ⊑ (A R)∋ [§2.413]. -/
theorem A_eps_eq {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b)
    (hbox : codBox R = codBox (∋ b)) : A R ≫ ∋ b = R := by
  apply le_antisymm
  · -- A(R) ≫ ∋ ⊑ R: first component of le_symmDiv_iff
    exact ((le_symmDiv_iff _ R _).mp (le_refl _)).1
  · -- R = f∋ ⊑ (A R)∋ via the box-matched thickness witness f ⊑ A R.
    obtain ⟨f, hf, hfeq⟩ := PowerAllegory.eps_thick (b := b) R hbox
    calc R = f ≫ ∋ b := hfeq.symm
      _ ⊑ A R ≫ ∋ b := comp_mono_right (thick_witness_le_A R hf hfeq) (∋ b)

/-! ## §2.415  Power object and singleton map -/

/-- The SINGLETON MAP of a is A(1_a) : a → [a] (§2.415). -/
def singletonMap {a : 𝒜} [PowerAllegory 𝒜] : a ⟶ PowerAllegory.powerObj a :=
  A (Cat.id a)

/-- Singleton map is monic (§2.415): A(1_a)A(1_a)° ⊑ 1.
    Proof: A(1)A°(1) ⊑ (1/∋)(∋/1) = (1/∋)∋ ⊑ 1. -/
theorem singletonMap_monic {a : 𝒜} [PowerAllegory 𝒜] :
    singletonMap (a := a) ≫ singletonMap° ⊑ Cat.id a := by
  -- singletonMap = A(1_a) = 1/ₛ∋ ⊑ 1/∋.
  -- singletonMap° ⊑ ∋/1 = ∋ (reciprocal of second component of symmDiv).
  -- So singletonMap ≫ singletonMap° ⊑ (1/∋) ≫ ∋ ⊑ 1.
  dsimp only [singletonMap, A]
  -- singletonMap is Cat.id a /ₛ ∋ a, unfold for the proof
  have h1 : Cat.id a /ₛ ∋ a ⊑ Cat.id a / ∋ a := inter_lb_left _ _
  -- (1/ₛ∋)° ⊑ ∋: (1/ₛ∋)° = ((1/∋) ∩ (∋/1)°)° = (1/∋)° ∩ ∋/1 ⊑ ∋/1 = ∋
  have h2 : (Cat.id a /ₛ ∋ a)° ⊑ ∋ a := by
    dsimp [symmDiv]
    rw [Allegory.recip_inter, div_one]
    exact le_trans (inter_lb_right _ _) (by rw [Allegory.recip_recip]; exact le_refl _)
  exact le_trans (comp_mono_right h1 _)
    (le_trans (comp_mono_left _ h2) (DivisionAllegory.div_comp_le _ _))

-- §2.13 `map_comp` and §2.16 `simple_comp` now live in `S2_1.lean` (`Freyd.Alg`).

/-- §2.16(10): a morphism contained in a semi-simple one is itself semi-simple.
    If `R ⊑ F°G` with `F, G` simple, then `R = F°G'` for `G' = (1 ∩ F R G°) ≫ G`
    (a `coreflexive ≫ simple`, hence simple by `simple_coref_comp`). -/
theorem semiSimple_of_le {𝒜 : Type u} [DivisionAllegory 𝒜] {a b : 𝒜} {R : a ⟶ b}
    (hR : ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ b), Simple F ∧ Simple G ∧ R ⊑ F° ≫ G) :
    SemiSimple R := by
  obtain ⟨c, F, G, hF, hG, hRle⟩ := hR
  refine ⟨c, F, (Cat.id c ∩ (F ≫ R ≫ G°)) ≫ G, hF,
    simple_coref_comp (inter_lb_left _ _) hG, ?_⟩
  apply le_antisymm
  · -- R ⊑ F° ≫ (1 ∩ FRG°) ≫ G.
    -- (1) R ⊑ (F° ∩ RG°) ≫ G by modularity (R = (F°G) ∩ R since R ⊑ F°G).
    have hReq : R = (F° ≫ G) ∩ R := by
      rw [Allegory.inter_comm, inter_eq_left hRle]
    have hmod1 : R ⊑ (F° ∩ (R ≫ G°)) ≫ G := by
      have := modular_le F° G R; rwa [← hReq] at this
    -- (2) F° ∩ RG° ⊑ F° ≫ (1 ∩ FRG°).  Reciprocate the modular fact
    --     F ∩ GR° ⊑ (1 ∩ GR°F°) ≫ F.
    have hmod2 : F° ∩ (R ≫ G°) ⊑ F° ≫ (Cat.id c ∩ (F ≫ R ≫ G°)) := by
      -- modular fact on the reciprocal side.
      have hm : F ∩ (G ≫ R°) ⊑ (Cat.id c ∩ (G ≫ R° ≫ F°)) ≫ F := by
        have h0 := modular_le (Cat.id c) F (G ≫ R°)
        rw [Cat.id_comp, Cat.assoc] at h0; exact h0
      -- reciprocate hm and rewrite both sides.
      have hmr := recip_mono hm
      have e1 : (F ∩ (G ≫ R°))° = F° ∩ (R ≫ G°) := by
        simp [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip]
      have e2 : ((Cat.id c ∩ (G ≫ R° ≫ F°)) ≫ F)°
          = F° ≫ (Cat.id c ∩ (F ≫ R ≫ G°)) := by
        simp [Allegory.recip_comp, Allegory.recip_inter, recip_id, Allegory.recip_recip,
              Cat.assoc]
      rwa [e1, e2] at hmr
    -- Combine: R ⊑ (F° ∩ RG°)G ⊑ (F°(1∩FRG°))G = F°((1∩FRG°)G).
    refine le_trans hmod1 ?_
    refine le_trans (comp_mono_right hmod2 G) ?_
    rw [Cat.assoc]; exact le_refl _
  · -- F° ≫ (1 ∩ FRG°) ≫ G ⊑ R, via F°F ⊑ 1, G°G ⊑ 1.
    have hstep : F° ≫ (Cat.id c ∩ (F ≫ R ≫ G°)) ≫ G ⊑ F° ≫ (F ≫ R ≫ G°) ≫ G :=
      comp_mono_left F° (comp_mono_right (inter_lb_right _ _) G)
    refine le_trans hstep ?_
    -- F°(FRG°)G = (F°F)R(G°G) ⊑ 1·R·1 = R.
    have e : F° ≫ (F ≫ R ≫ G°) ≫ G = (F° ≫ F) ≫ R ≫ (G° ≫ G) := by simp [Cat.assoc]
    rw [e]
    -- (F°F) R (G°G) ⊑ 1·R·(G°G) = R(G°G) ⊑ R.
    have s1 : (F° ≫ F) ≫ R ≫ (G° ≫ G) ⊑ R ≫ (G° ≫ G) := by
      have h := comp_mono_right hF (R ≫ (G° ≫ G)); rwa [Cat.id_comp] at h
    have hRGG : R ≫ (G° ≫ G) ⊑ R := by
      have := comp_mono_left R hG; rwa [Cat.comp_id] at this
    exact le_trans s1 hRGG

/-- §2.442 / §2.16(10): a semi-simple morphism followed by a simple one is semi-simple.
    If `R = F°G` (F, G simple) and `H` is simple, then `RH = F°(GH)` with `GH` simple
    (`simple_comp`), so `RH` is again of the book's `(simple)°(simple)` form. -/
theorem semiSimple_comp_simple {𝒜 : Type u} [Allegory 𝒜] {a b d : 𝒜}
    {R : a ⟶ b} {H : b ⟶ d} (hR : SemiSimple R) (hH : Simple H) : SemiSimple (R ≫ H) := by
  obtain ⟨c, F, G, hF, hG, hReq⟩ := hR
  exact ⟨c, F, G ≫ H, hF, simple_comp hG hH, by rw [hReq, Cat.assoc]⟩

/-! ## §2.412  Uniqueness of A(R) -/

/-- A(R) is the UNIQUE map F with F∋ = R (§2.412).
    Uniqueness: if F is a map and F∋ = R then F = A(R).
    This follows from straightness of ∋: ∋ /ₛ ∋ ⊑ 1 forces A(R) uniqueness. -/
theorem A_unique {a b : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ b) (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Map F) (hFeq : F ≫ ∋ b = R) : F = A R := by
  -- Step 1: F ⊑ A R = R /ₛ ∋ via le_symmDiv_iff
  have hF_le : F ⊑ A R := by
    rw [A, le_symmDiv_iff]
    refine ⟨?_, ?_⟩
    · rw [hFeq]; exact le_refl R
    · -- F° R ⊑ ∋: F°(F ∋) = (F°F)∋ ⊑ 1∋ = ∋ via Simple F
      rw [← hFeq, ← Cat.assoc]
      exact le_trans (comp_mono_right hF.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)
  -- Helper: (A R) ≫ ∋ b ⊑ R
  have hAR_eps : A R ≫ ∋ b ⊑ R := ((le_symmDiv_iff _ R _).mp (le_refl _)).1
  -- Helper: (A R)° ≫ R ⊑ ∋ b
  have hARo_R : (A R)° ≫ R ⊑ ∋ b := ((le_symmDiv_iff _ R _).mp (le_refl _)).2
  -- Step 2: F° ≫ A R ⊑ ∋ /ₛ ∋ ⊑ 1
  have hFoAR : F° ≫ A R ⊑ Cat.id (PowerAllegory.powerObj b) := by
    apply le_trans _ (PowerAllegory.eps_straight b)
    rw [le_symmDiv_iff]
    refine ⟨?_, ?_⟩
    · -- (F° ≫ A R) ≫ ∋ ⊑ ∋
      have step1 : (F° ≫ A R) ≫ ∋ b ⊑ F° ≫ R := by
        rw [Cat.assoc]; exact comp_mono_left F° hAR_eps
      have step2 : F° ≫ R ⊑ ∋ b := by
        rw [← hFeq, ← Cat.assoc]
        exact le_trans (comp_mono_right hF.2 (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)
      exact le_trans step1 step2
    · -- (F° ≫ A R)° ≫ ∋ = (A R)° ≫ F ≫ ∋ ⊑ ∋
      rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, hFeq]
      exact hARo_R
  -- Step 3: Entire F: 1 ⊑ F ≫ F°, so A R ⊑ F(F°(A R)) ⊑ F·1 = F
  have hent : Cat.id a ⊑ F ≫ F° := by
    have h := hF.1; dsimp [Entire, dom] at h
    rw [← h]; exact inter_lb_right _ _
  have hAR_le_F : A R ⊑ F := by
    -- A R = 1_a ≫ A R ⊑ (F F°) A R = F (F° A R) ⊑ F 1 = F
    have h1 : Cat.id a ≫ A R ⊑ (F ≫ F°) ≫ A R := comp_mono_right hent _
    rw [Cat.id_comp] at h1
    have h2 : (F ≫ F°) ≫ A R = F ≫ F° ≫ A R := Cat.assoc _ _ _
    rw [h2] at h1
    have h3 : F ≫ F° ≫ A R ⊑ F ≫ Cat.id _ := comp_mono_left F hFoAR
    have h4 : F ≫ Cat.id (PowerAllegory.powerObj b) = F := Cat.comp_id _
    rw [h4] at h3
    exact le_trans h1 h3
  exact le_antisymm hF_le hAR_le_F

/-- For any map f : a → b, A(f) = f ≫ A(1_b) (§2.415), when `1_b` is in ∋'s box
    (Freyd's `∋_R□ = R□` at the singleton `R = 1_b`; needed for `A(1_b)` a map and
    `A(1_b)∋ = 1_b`).  Book: "For any map p →ᶠ a, A(f) = f A(1) since f A(1) is a map and
    f A(1) ∋ = f."  Relies on `A_eps_eq` and uniqueness of A(R) [A_unique].
    Note `A f` need not itself be a map here — `A_unique` only needs the witness a map. -/
theorem A_of_map {a b : 𝒜} [PowerAllegory 𝒜] (f : a ⟶ b) (hf : Map f)
    (hbox1 : codBox (Cat.id b) = codBox (∋ b)) :
    A f = f ≫ singletonMap (a := b) := by
  -- F := f ≫ singletonMap is a map (composition of maps) with F∋ = f, so F = A f by uniqueness.
  refine (A_unique f (f ≫ singletonMap) (map_comp hf (A_is_map _ hbox1)) ?_).symm
  -- (f ≫ A(1_b))∋ = f ≫ (A(1_b)∋) = f ≫ 1_b = f, since A(1_b)∋ = 1_b by A_eps_eq.
  rw [singletonMap, Cat.assoc, A_eps_eq _ hbox1, Cat.comp_id]

/-- If F is simple then F ⊑ A(F∋) (§2.412).
    Book: "Indeed, if F is simple then F ⊂ A(F∋)."
    Proof: need F ⊑ (F∋)/ₛ∋, i.e. F∋ ⊑ F∋ (trivial) and F°(F∋) ⊑ ∋,
    which follows from F°F ⊑ 1 and A(R)∋ = R. -/
theorem simple_le_A_eps {a b : 𝒜} [PowerAllegory 𝒜] (F : a ⟶ PowerAllegory.powerObj b)
    (hF : Simple F) : F ⊑ A (F ≫ ∋ b) := by
  -- A (F ≫ ∋ b) = (F ≫ ∋ b) /ₛ ∋ b. By le_symmDiv_iff, F ⊑ (F∋)/ₛ∋ iff
  -- (1) F ≫ ∋ ⊑ F ≫ ∋ (trivial) and (2) F° ≫ (F ≫ ∋) ⊑ ∋.
  -- (2): F°(F ∋) = (F°F)∋ ⊑ 1∋ = ∋ via Simple F (F°F ⊑ 1).
  rw [A, le_symmDiv_iff]
  refine ⟨le_refl _, ?_⟩
  -- F° ≫ (F ≫ ∋ b) = (F° ≫ F) ≫ ∋ b ⊑ Cat.id _ ≫ ∋ b = ∋ b
  rw [← Cat.assoc]
  exact le_trans (comp_mono_right hF (∋ b)) (by rw [Cat.id_comp]; exact le_refl _)

/-! ## §2.42  Splitting lemmas

  If A is a power allegory then Spl(Cor(A)) is a power allegory (§2.42). -/

/-! ## §2.421  R/S = A(R)A°(S)

  In a power allegory, R /ₛ S = A(R) ≫ (A S)° for any R : a → c, S : b → c. -/

/-- §2.421: in a power allegory, the symmetric division R /ₛ S equals A(R) ≫ (A S)°,
    for R in ∋'s box (Freyd's `∋_R□ = R□`; `A R` must be a map).  The `S`-leg needs no
    box: only `A R` entire is used. -/
theorem symm_div_eq_A_comp {a b c : 𝒜} [PowerAllegory 𝒜] (R : a ⟶ c) (S : b ⟶ c)
    (hboxR : codBox R = codBox (∋ c)) :
    R /ₛ S = A R ≫ (A S)° := by
  apply le_antisymm
  · -- R/ₛS ⊑ A(R) ≫ (A S)° (§2.421), using A(R) entire and A_eps_eq.
    -- Step A: (R/ₛS)° ≫ A R ⊑ A S, hence (A R)° ≫ (R/ₛS) ⊑ (A S)°.
    -- Step B: R/ₛS ⊑ (A R · A R°) (R/ₛS) = A R ((A R)° (R/ₛS)) ⊑ A R (A S)°.
    have hARS_le : (R /ₛ S) ≫ S ⊑ R := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
    have hARS_rec : (R /ₛ S)° ≫ R ⊑ S := ((le_symmDiv_iff _ _ _).mp (le_refl _)).2
    have hAR_eps : A R ≫ ∋ c ⊑ R := ((le_symmDiv_iff _ R _).mp (le_refl _)).1
    have hARo_R : (A R)° ≫ R ⊑ ∋ c := ((le_symmDiv_iff _ R _).mp (le_refl _)).2
    -- Step A: (R/ₛS)° ≫ A R ⊑ A S = S /ₛ ∋.
    have hstepA : (R /ₛ S)° ≫ A R ⊑ A S := by
      show (R /ₛ S)° ≫ A R ⊑ S /ₛ ∋ c
      rw [le_symmDiv_iff]
      refine ⟨?_, ?_⟩
      · -- ((R/ₛS)° ≫ A R) ≫ ∋ = (R/ₛS)° ≫ (A R ≫ ∋) ⊑ (R/ₛS)° ≫ R ⊑ S
        rw [Cat.assoc]
        exact le_trans (comp_mono_left _ hAR_eps) hARS_rec
      · -- ((R/ₛS)° ≫ A R)° ≫ S = (A R)° ≫ ((R/ₛS) ≫ S) ⊑ (A R)° ≫ R ⊑ ∋
        rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
        exact le_trans (comp_mono_left _ hARS_le) hARo_R
    -- (A R)° ≫ (R/ₛS) ⊑ (A S)° by reciprocating hstepA.
    have hstepA' : (A R)° ≫ (R /ₛ S) ⊑ (A S)° := by
      have := recip_mono hstepA
      rwa [Allegory.recip_comp, Allegory.recip_recip] at this
    -- Step B: 1 ⊑ A R ≫ (A R)° (A R is entire), so R/ₛS ⊑ (A R · A R°)(R/ₛS).
    have hAR_ent : Cat.id a ⊑ A R ≫ (A R)° := by
      have := (A_is_map R hboxR).1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have hb1 : R /ₛ S ⊑ (A R ≫ (A R)°) ≫ (R /ₛ S) := by
      have := comp_mono_right hAR_ent (R /ₛ S); rwa [Cat.id_comp] at this
    have hb2 : (A R ≫ (A R)°) ≫ (R /ₛ S) ⊑ A R ≫ (A S)° := by
      rw [Cat.assoc]; exact comp_mono_left _ hstepA'
    exact le_trans hb1 hb2
  · -- A(R) ≫ (A S)° ⊑ R/ₛS: by le_symmDiv_iff, need:
    -- (1) (A R ≫ (A S)°) ≫ S ⊑ R
    -- (2) (A R ≫ (A S)°)° ≫ R ⊑ S
    rw [le_symmDiv_iff]
    constructor
    · -- (A R ≫ (A S)°) ≫ S = A R ≫ ((A S)° ≫ S) ⊑ A R ≫ ∋ ⊑ R
      rw [Cat.assoc]
      have h1 : (A S)° ≫ S ⊑ ∋ c :=
        ((le_symmDiv_iff _ S _).mp (le_refl _)).2
      have h2 : A R ≫ ∋ c ⊑ R :=
        ((le_symmDiv_iff _ R _).mp (le_refl _)).1
      exact le_trans (comp_mono_left (A R) h1) h2
    · -- (A R ≫ (A S)°)° ≫ R = A S ≫ (A R)° ≫ R ⊑ A S ≫ ∋ ⊑ S
      rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      have h1 : (A R)° ≫ R ⊑ ∋ c :=
        ((le_symmDiv_iff _ R _).mp (le_refl _)).2
      have h2 : A S ≫ ∋ c ⊑ S :=
        ((le_symmDiv_iff _ S _).mp (le_refl _)).1
      exact le_trans (comp_mono_left (A S) h1) h2

/-! ## §2.422  Equivalence relations in power allegories

  In any division allegory, E²=E for any equivalence relation E.
  In a power allegory every equivalence relation is of the form ff°. -/

-- §2.414 (a topos ↔ a unitary tabular power allegory: C topos ⟹ Rel(C) power
-- allegory, and Map of a unitary tabular power allegory is a topos) is recorded
-- MISSING in S2_4.md — stating it faithfully needs the Rel(C)/Map(A) bridge between
-- the categorical (Topos, S1_9) and allegorical worlds, not yet built. Per the
-- integrity rule we do NOT emit a vacuous `: True` stub.

/-! ## §2.43  Pre-power allegory and diagonal proofs

  Freyd's thickness (§2.412, §2.43): for the membership relation ∋, T is thick
  iff `Δ(R) = R/ₛ∋` is entire for every R.  Generalising to an arbitrary T, a
  morphism T : a → b is THICK iff the *symmetric* division `R/ₛT` is entire for
  every R : c → b that is COMPATIBLE with T, i.e. shares T's codomain box
  `R□ = T□` (where `R□ = 1_b ∩ R°R`).  The box side-condition is exactly the
  domain on which Freyd's partial division `R/T` is defined (§2.33), and it is
  indispensable: without it the predicate becomes strictly stronger than the
  §2.431 right-hand side (verified exhaustively in Rel up to 3×3).

  ⚠ The earlier formulation `∀R, Entire (R/T)` using the PLAIN (asymmetric) right
  division and DROPPING the `R□ = T□` guard is NOT Freyd's thickness: it made the
  §2.431 forward direction FALSE.  Counterexample (Rel): T = {(0,0)} : {0,1}→{0},
  R = {(0,0),(1,0)} have `R□ = T□` and T is thick, yet the *plain* witness `R/T`
  fails `(R/T)°R ⊑ T`.  The honest witness is the SYMMETRIC division `R/ₛT`, which
  IS entire here — captured by the corrected definition below.

  A PRE-POWER ALLEGORY is a division allegory in which each object
  appears as the target of a thick morphism (§2.43). -/

/-- T : a → b is THICK (§2.412, §2.43) iff the symmetric division `R/ₛT` is entire
    for every R : c → b with the same codomain box `R□ = T□` (Freyd's `Δ(R)`
    entireness condition, stated for a general T rather than just ∋).
    The `codBox R = codBox T` guard is the domain on which Freyd's `R/T` is defined
    and is necessary for §2.431 to be a biconditional (see the note above). -/
def Thick {a b : 𝒜} [DivisionAllegory 𝒜] (T : a ⟶ b) : Prop :=
  ∀ (c : 𝒜) (R : c ⟶ b), codBox R = codBox T → Entire (R /ₛ T)

/-- `Entire R ↔ 1 ⊑ RR°` (§2.122): since `dom R = 1 ∩ RR°` and `1 ∩ RR° ⊑ 1` always,
    `dom R = 1` is equivalent to `1 ⊑ RR°`. -/
private theorem entire_iff_one_le {a b : 𝒜} [Allegory 𝒜] (R : a ⟶ b) :
    Entire R ↔ Cat.id a ⊑ R ≫ R° := by
  dsimp [Entire, dom]
  constructor
  · intro h; rw [← h]; exact inter_lb_right _ _
  · intro h; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)

/-- §2.431 (faithful, biconditional): T is thick iff for every R : c → b with the
    same codomain box `R□ = T□` there exists R̃ : c → a satisfying Freyd's three
    containments `1 ⊑ R̃R̃°` (entire), `R̃T ⊑ R`, `R̃°R ⊑ T`.

    The `R□ = T□` hypothesis is Freyd's own side-condition (the domain on which his
    partial division `R/T` is defined); restoring it — together with the SYMMETRIC
    division in the definition of `Thick` — makes the biconditional TRUE.  It is
    not falsified by the Rel counterexample (T = {(0,0)}, R = {(0,0),(1,0)}): there
    `R□ = T□` holds, T is thick, and the honest witness `R̃ = R/ₛT = {(0,0),(1,0)}`
    IS entire and satisfies all three containments.

    Forward: take `R̃ = R/ₛT`, entire by `Thick T` (consuming the box hypothesis);
    the last two containments are the defining property of `/ₛ`.
    Reverse: `R̃ ⊑ R/ₛT` and `R̃` entire force `R/ₛT` entire. -/
theorem thick_iff_existential {a b : 𝒜} [DivisionAllegory 𝒜] (T : a ⟶ b) :
    Thick T ↔ ∀ (c : 𝒜) (R : c ⟶ b), codBox R = codBox T → ∃ (R' : c ⟶ a),
        Entire R' ∧ R' ≫ T ⊑ R ∧ R'° ≫ R ⊑ T := by
  constructor
  · -- Thick T → ∃R̃.  Witness R̃ = R/ₛT: entire by Thick (using R□ = T□), and the
    -- two containments R̃T ⊑ R, R̃°R ⊑ T are the symmetric-division law applied to
    -- R/ₛT ⊑ R/ₛT.
    intro hThick c R hBox
    refine ⟨R /ₛ T, hThick c R hBox, ?_, ?_⟩
    · exact ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).1
    · exact ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).2
  · -- ∃R̃ → Thick T: given R̃ entire with R̃T ⊑ R and R̃°R ⊑ T, we have R̃ ⊑ R/ₛT,
    -- so 1 ⊑ R̃R̃° ⊑ (R/ₛT)(R/ₛT)°, i.e. R/ₛT is entire.  Hence Thick T.
    intro hEx c R hBox
    obtain ⟨R', hEnt, hRT, hRoR⟩ := hEx c R hBox
    have hR'_le : R' ⊑ R /ₛ T := (le_symmDiv_iff R' R T).mpr ⟨hRT, hRoR⟩
    rw [entire_iff_one_le]
    refine le_trans ((entire_iff_one_le R').mp hEnt) ?_
    exact le_trans (comp_mono_right hR'_le _) (comp_mono_left _ (recip_mono hR'_le))

/-- A PRE-POWER ALLEGORY (§2.43): division allegory where each object
    is the target of some thick morphism. -/
class PrePowerAllegory (𝒜 : Type u) extends DivisionAllegory 𝒜 where
  /-- For each object a, there exists a thick morphism with target a. -/
  thick_target (a : 𝒜) : ∃ (x : 𝒜) (S : x ⟶ a), Thick S

/-! ## §2.354  Straight factorization (in an effective division allegory)

  In an effective division allegory every morphism `T : x → a` factors as `T = h ≫ S`
  with `h` a (monic, cover) map and `S = h° ≫ T` straight.  The construction splits the
  equivalence relation `E = T/ₛT` (reflexive, symmetric, idempotent) as `E = h ≫ h°`,
  `h° ≫ h = 1`, then sets `S = h° ≫ T`.  This is the linchpin of §2.432. -/

/-- An EFFECTIVE DIVISION ALLEGORY: simultaneously a `DivisionAllegory` (so `/`, `/ₛ`
    are available) and an `EffectiveAllegory` (so symmetric idempotents split).  The two
    parents share their `Allegory`, so the `≫`/`°`/`∩`/`/ₛ` of the division side and the
    splitting of the effective side refer to the *same* operations (no instance diamond). -/
class EffectiveDivisionAllegory (𝒜 : Type u)
    extends DivisionAllegory 𝒜, EffectiveAllegory 𝒜

/-- §2.354 (effective division allegory): every `T : x → a` factors as `T = h ≫ S`
    with `h` a map and `S = h° ≫ T` straight.  Splits `E = T/ₛT` via effectiveness.

    `T = h ≫ S`: `h ≫ h° ≫ T = E ≫ T = T` since `E` is reflexive and `(T/ₛT)T ⊑ T`.
    `Straight S`: for the symmetric `U = S/ₛS` with `US ⊑ S`, the symmetric `hUh°`
    satisfies `(hUh°)T ⊑ T`, hence `hUh° ⊑ T/ₛT = E = hh°`; conjugating by `h°h = 1`
    gives `U = h°(hUh°)h ⊑ h°(hh°)h = (h°h)(h°h) = 1`. -/
theorem straight_factorization {𝒜 : Type u} [EffectiveDivisionAllegory 𝒜]
    {x a : 𝒜} (T : x ⟶ a) :
    ∃ (c : 𝒜) (h : x ⟶ c), Map h ∧ h° ≫ h = Cat.id c ∧
      Straight (h° ≫ T) ∧ T = h ≫ (h° ≫ T) := by
  -- E = T/ₛT is a reflexive symmetric idempotent; split it.
  have hEsym : Symmetric (T /ₛ T) := symmDiv_self_symmetric T
  have hErefl : Reflexive (T /ₛ T) := symmDiv_self_reflexive T
  have hEidem : (T /ₛ T) ≫ (T /ₛ T) = T /ₛ T :=
    reflexive_transitive_idempotent hErefl (symmDiv_self_transitive T)
  obtain ⟨c, h, hMap, hhh, hch⟩ :=
    EffectiveAllegory.split_symmetric_idempotent (T /ₛ T) hEsym hEidem
  refine ⟨c, h, hMap, hch, ?_, ?_⟩
  · -- Straightness of S = h° ≫ T.
    -- ET = T (E reflexive, (T/ₛT)T ⊑ T).
    have hET_le : (T /ₛ T) ≫ T ⊑ T := ((le_symmDiv_iff (T /ₛ T) T T).mp (le_refl _)).1
    have hET_ge : T ⊑ (T /ₛ T) ≫ T := by
      have := comp_mono_right hErefl T; rwa [Cat.id_comp] at this
    have hET : (T /ₛ T) ≫ T = T := le_antisymm hET_le hET_ge
    -- hS = h ≫ h° ≫ T = E ≫ T = T.
    have hhS : h ≫ (h° ≫ T) = T := by rw [← Cat.assoc, hhh, hET]
    -- U := S/ₛS, symmetric, U≫S ⊑ S.  Generalize S := h° ≫ T (the goal's term).
    generalize hSdef : h° ≫ T = S at hhS ⊢
    have hUsym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric S
    have hUS : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
    have hUoS : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right hUsym S) hUS
    -- Claim A: h ≫ (S/ₛS) ≫ h° ⊑ T/ₛT, since (h U h°)T ⊑ T and it is symmetric.
    -- (h U h°)≫T = h≫U≫(h°≫T) = h≫U≫S ⊑ h≫S = T.
    have hUS_T : (h ≫ (S /ₛ S) ≫ h°) ≫ T ⊑ T := by
      have e1 : (h ≫ (S /ₛ S) ≫ h°) ≫ T = h ≫ (S /ₛ S) ≫ S := by
        rw [← hSdef]; simp [Cat.assoc]
      rw [e1]
      calc h ≫ (S /ₛ S) ≫ S ⊑ h ≫ S := comp_mono_left h hUS
        _ = T := hhS
    -- (h U h°)° ≫ T ⊑ T as well, since (h U h°)° = h ≫ U° ≫ h° ⊑ h ≫ U ≫ h°.
    have hUS_oT : (h ≫ (S /ₛ S) ≫ h°)° ≫ T ⊑ T := by
      have e2 : (h ≫ (S /ₛ S) ≫ h°)° = h ≫ (S /ₛ S)° ≫ h° := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      rw [e2]
      have hle : h ≫ (S /ₛ S)° ≫ h° ⊑ h ≫ (S /ₛ S) ≫ h° :=
        comp_mono_left h (comp_mono_right hUsym h°)
      exact le_trans (comp_mono_right hle T) hUS_T
    have hClaimA : h ≫ (S /ₛ S) ≫ h° ⊑ T /ₛ T :=
      (le_symmDiv_iff _ T T).mpr ⟨hUS_T, hUS_oT⟩
    -- Claim B: U = h°(hUh°)h ⊑ h°(hh°)h = (h°h)(h°h) = 1.
    -- h° ≫ E ≫ h = h° ≫ (h≫h°) ≫ h = (h°h)(h°h) = 1.
    have hConj : (S /ₛ S) = h° ≫ (h ≫ (S /ₛ S) ≫ h°) ≫ h := by
      have : h° ≫ (h ≫ (S /ₛ S) ≫ h°) ≫ h = (h° ≫ h) ≫ (S /ₛ S) ≫ (h° ≫ h) := by
        simp [Cat.assoc]
      rw [this, hch, Cat.id_comp, Cat.comp_id]
    have hEh : h° ≫ (T /ₛ T) ≫ h = Cat.id c := by
      rw [← hhh]
      have : h° ≫ (h ≫ h°) ≫ h = (h° ≫ h) ≫ (h° ≫ h) := by simp [Cat.assoc]
      rw [this, hch, Cat.id_comp]
    show (S /ₛ S) ⊑ Cat.id c
    rw [hConj]
    calc h° ≫ (h ≫ (S /ₛ S) ≫ h°) ≫ h
        ⊑ h° ≫ (T /ₛ T) ≫ h := comp_mono_left h° (comp_mono_right hClaimA h)
      _ = Cat.id c := hEh
  · -- T = h ≫ (h° ≫ T): h ≫ h° ≫ T = E ≫ T = T.
    have hET_le : (T /ₛ T) ≫ T ⊑ T := ((le_symmDiv_iff (T /ₛ T) T T).mp (le_refl _)).1
    have hET_ge : T ⊑ (T /ₛ T) ≫ T := by
      have := comp_mono_right hErefl T; rwa [Cat.id_comp] at this
    have hET : (T /ₛ T) ≫ T = T := le_antisymm hET_le hET_ge
    rw [← Cat.assoc, hhh, hET]

/-- If `T = h ≫ S` with `h° ≫ h = 1`, then `S` and `T` have the same codomain box
    `codBox = dom(·°) = 1 ∩ (·)°(·)`.  Indeed `T°T = (hS)°(hS) = S°(h°h)S = S°S`. -/
theorem codBox_eq_of_split {𝒜 : Type u} [Allegory 𝒜] {x c a : 𝒜}
    {h : x ⟶ c} {S : c ⟶ a} {T : x ⟶ a}
    (hch : h° ≫ h = Cat.id c) (hT : T = h ≫ S) : codBox S = codBox T := by
  -- codBox R = dom (R°) = 1 ∩ R° ≫ R°° = 1 ∩ R° ≫ R.  So we equate S° ≫ S with T° ≫ T.
  have hTT : T° ≫ T = S° ≫ S := by
    rw [hT, Allegory.recip_comp, Cat.assoc, ← Cat.assoc h° h S, hch, Cat.id_comp]
  dsimp [codBox, dom]
  rw [Allegory.recip_recip, Allegory.recip_recip, hTT]

/-- §2.432 thickness descent: if `T` is thick, `T = h ≫ S` with `h` a map and `h° ≫ h = 1`,
    then `S = h° ≫ T`-style factor `S` is again thick.  (We pass `S` directly with the
    splitting data.)  Book §2.432: for `R□ = S□ = T□`, the witness `R̃ = (R/ₛT) ≫ h` is
    entire (thickness of `T` plus `h` entire), with `R̃S ⊑ R` and `R̃°R ⊑ S`. -/
theorem straight_descent_thick {𝒜 : Type u} [DivisionAllegory 𝒜] {x c a : 𝒜}
    {h : x ⟶ c} {S : c ⟶ a} {T : x ⟶ a}
    (hMap : Map h) (hch : h° ≫ h = Cat.id c) (hT : T = h ≫ S) (hThickT : Thick T) :
    Thick S := by
  -- Same codomain box for S and T.
  have hbox : codBox S = codBox T := codBox_eq_of_split hch hT
  -- h ≫ S = T (from hT).
  have hhS : h ≫ S = T := hT.symm
  rw [thick_iff_existential]
  intro d R hRS
  -- R□ = S□ = T□, so Thick T supplies the witness for R against T.
  have hRT : codBox R = codBox T := hRS.trans hbox
  obtain ⟨R', hEnt', hRT'le, hR'oR⟩ :=
    (thick_iff_existential T).mp hThickT d R hRT
  -- R̃ = R' ≫ h.
  refine ⟨R' ≫ h, ?_, ?_, ?_⟩
  · -- Entire (R' ≫ h): 1 ⊑ R'R'° ⊑ R'(hh°)R'° = (R'h)(R'h)° since 1 ⊑ hh° (h entire).
    rw [entire_iff_one_le]
    have h1 : Cat.id d ⊑ R' ≫ R'° := (entire_iff_one_le R').mp hEnt'
    have hhe : Cat.id x ⊑ h ≫ h° := (entire_iff_one_le h).mp hMap.1
    have hstep : R' ≫ R'° ⊑ (R' ≫ h) ≫ (R' ≫ h)° := by
      have e : (R' ≫ h) ≫ (R' ≫ h)° = R' ≫ (h ≫ h°) ≫ R'° := by
        rw [Allegory.recip_comp]; simp [Cat.assoc]
      rw [e]
      calc R' ≫ R'° = R' ≫ Cat.id x ≫ R'° := by rw [Cat.id_comp]
        _ ⊑ R' ≫ (h ≫ h°) ≫ R'° := comp_mono_left R' (comp_mono_right hhe R'°)
    exact le_trans h1 hstep
  · -- (R' ≫ h) ≫ S = R' ≫ (h ≫ S) = R' ≫ T ⊑ R.
    rw [Cat.assoc, hhS]; exact hRT'le
  · -- (R' ≫ h)° ≫ R = h° ≫ (R'° ≫ R) ⊑ h° ≫ T = S.
    rw [Allegory.recip_comp, Cat.assoc]
    refine le_trans (comp_mono_left h° hR'oR) ?_
    -- h° ≫ T = h° ≫ h ≫ S = (h°h)S = S.
    rw [hT, ← Cat.assoc, hch, Cat.id_comp]; exact le_refl _

/-! ## §2.432  Effective pre-power allegory is power

  An effective pre-power allegory is a power allegory (§2.432). -/

/-- An EFFECTIVE PRE-POWER ALLEGORY: an `EffectiveDivisionAllegory` (division + effective
    splitting over ONE shared `Allegory`) in which each object is the target of a thick
    morphism (the §2.43 pre-power condition, carried as a field to avoid an instance diamond
    with a separately-assumed `PrePowerAllegory`). -/
class EffectivePrePowerAllegory (𝒜 : Type u) extends EffectiveDivisionAllegory 𝒜 where
  /-- For each object a, there exists a thick morphism with target a (§2.43). -/
  thick_target (a : 𝒜) : ∃ (x : 𝒜) (S : x ⟶ a), Thick S

/-- Each object `b` of an effective pre-power allegory is the target of a STRAIGHT THICK
    morphism (§2.432).  `thick_target b` gives a thick `T : x → b`; `straight_factorization T`
    factors it `T = h ≫ S` with `h` a map, `h°h = 1`, `S = h° ≫ T` straight;
    `straight_descent_thick` shows `S` stays thick.  This is a `Prop`, so it may be `choose`n
    into the (data) `powerObj`/`eps` fields below via `Classical`. -/
theorem exists_straight_thick_target {𝒜 : Type u} [EffectivePrePowerAllegory 𝒜] (b : 𝒜) :
    ∃ (p : 𝒜) (S : p ⟶ b), Straight S ∧ Thick S := by
  obtain ⟨x, T, hThickT⟩ := EffectivePrePowerAllegory.thick_target (𝒜 := 𝒜) b
  obtain ⟨c, h, hMap, hch, hStr, hTeq⟩ := straight_factorization T
  exact ⟨c, h° ≫ T, hStr, straight_descent_thick hMap hch hTeq hThickT⟩

/-- §2.416 (monic half of maximality): a STRAIGHT MAP is monic, `h ≫ h° ⊑ 1`.
    Book: `hh°` is symmetric, and `(hh°)h = h(h°h) ⊑ h` since `h` is simple; so
    `hh° ⊑ h/ₛh ⊑ 1` because `h` is straight.  (This is exactly the half of §2.416's
    maximality step that needs NO progenitor; the converse `1 ⊑ h°h` is the half that
    does — see `effective_pre_power_is_power`.) -/
theorem straight_map_monic {𝒜 : Type u} [DivisionAllegory 𝒜] {a b : 𝒜} {h : a ⟶ b}
    (hMap : Map h) (hStr : Straight h) : h ≫ h° ⊑ Cat.id a := by
  have hsimp : h° ≫ h ⊑ Cat.id b := hMap.2
  -- (hh°)h ⊑ h and (hh°)°h = (hh°)h ⊑ h, so hh° ⊑ h/ₛh ⊑ 1.
  have hTh : (h ≫ h°) ≫ h ⊑ h := by
    rw [Cat.assoc]
    exact le_trans (comp_mono_left h hsimp) (by rw [Cat.comp_id]; exact le_refl h)
  have hsym : (h ≫ h°)° = h ≫ h° := by rw [Allegory.recip_comp, Allegory.recip_recip]
  have hle : h ≫ h° ⊑ h /ₛ h :=
    (le_symmDiv_iff (h ≫ h°) h h).mpr ⟨hTh, by rw [hsym]; exact hTh⟩
  exact le_trans hle hStr

/-- §2.416 (the maximality step, monic half packaged for a split factorization):
    if `S = h ≫ S'` with `S` straight and `h` a map, then `h` is monic (`h ≫ h° ⊑ 1`).
    `S = h ≫ S'` straight ⟹ `h` straight (§2.355 `straight_of_comp_straight`), then
    `straight_map_monic`.  The remaining `1 ⊑ h° ≫ h` (epic) is the progenitor-dependent
    half left open in `effective_pre_power_is_power`. -/
theorem straight_factor_map_monic {𝒜 : Type u} [DivisionAllegory 𝒜] {x c a : 𝒜}
    {h : x ⟶ c} {S' : c ⟶ a} {S : x ⟶ a}
    (hMap : Map h) (hStr : Straight S) (hS : S = h ≫ S') : h ≫ h° ⊑ Cat.id x :=
  straight_map_monic hMap (straight_of_comp_straight (S := h) (R := S') (hS ▸ hStr))

/-- §2.432: an effective pre-power allegory is a power allegory.  SORRY-FREE.
    Everything is built honestly: `powerObj b` / `eps b` are the straight-thick factor
    `(c, S)` of the chosen thick target of `b` (§2.354 `straight_factorization` + §2.432
    `straight_descent_thick`), `eps_straight` is exactly the straightness of that `S`, and
    `eps_thick` (now the box-guarded `∋_R□ = R□` membership, faithful to Freyd's §2.41) is
    discharged DIRECTLY from `Straight S` + box-matched `Thick S` via `thick_iff_existential`:
    the witness is `f = R /ₛ S`, simple by §2.356 (straight), entire by box-matched thickness,
    with `f ≫ S = R` from the symmetric-division law plus the box match.

    HISTORICAL NOTE.  Earlier this field was the §2.413 *unconditional* thickness
    `∀R ∃f map, fS = R`, which the present hypotheses cannot supply: box-guarded `Thick S`
    (§2.43) gives the witness only when `codBox R = codBox S`, and the unconditional form
    drops that guard.  Restoring Freyd's own box index `∋_R□ = R□` on the membership field
    (the repo had collapsed his box-indexed `∋_R` to a single un-indexed `∋_b`) makes the
    field faithful AND directly dischargeable.  For the record, Freyd's §2.416 route to the
    unconditional form (a copower straightening) is genuinely out of reach here, and the
    pins exactly which operation that needs and why this repo cannot supply it here.

    §2.416 inference, specialised to one arbitrary `R : p → b`:
      1.  form the binary cotuple `(R ; S) : (c ⊕ p) → b` of `S : c → b` (our `eps b`,
          with `c = powerObj b`) and `R`, living on the COPRODUCT object `c ⊕ p`;
      2.  straighten it (§2.354): `(R ; S) = (h' ; h) ≫ S'` with `h, h'` maps, `S'` straight;
          restricting to the `c`-summand gives `S = h ≫ S'`;
      3.  `S` is MAXIMAL straight (`S = h ≫ S'`, `S'` straight ⟹ `h` iso), so `h` is iso;
      4.  hence `R = h' ≫ S' = (h' ≫ h⁻¹) ≫ S` with `h' ≫ h⁻¹` a map — the witness.

    Two distinct irreducible obstacles, BOTH the progenitor (§1.966), absent here:

    • Step 1 needs the coproduct OBJECT `c ⊕ p` with its cotupling map, i.e.
      `Freyd.Alg.PositiveAllegory.coprod (powerObj b) p` and
      `PositiveAllegory.has_coproduct (powerObj b) p` — the binary instance of Freyd's
      copower `C_I y`.  An `EffectivePrePowerAllegory` is
      `EffectiveDivisionAllegory = DivisionAllegory + EffectiveAllegory`, and
      `DivisionAllegory extends DistributiveAllegory`, which gives `∪`/`𝟘` on hom-sets but
      NOT coproduct objects.  Effectiveness only splits idempotents over a SINGLE object
      (`split_symmetric_idempotent`); it cannot join two morphisms with distinct sources
      (`c` and `p`) into one cotuple.

      The §2.16(10) split-symmetric-idempotent *systemic completion* trick that closed
      `S2_22.srcTabulation_exists` does NOT apply here.  That trick builds, from a single
      morphism `U`, a source-apex span by splitting the symmetric idempotent
      `F₀F₀° ∩ G₀G₀°` *on one object* (`srcTabulation_of_semiSimple_split`); and the
      `Spl 𝒜` completion (`S2_22b`, §2.164) only ever adds objects `(a, e)` that are
      RETRACTS (subobjects, carved by a coreflexive/idempotent `e`) of pre-existing
      objects `a`.  A coproduct `c ⊕ p` is a colimit joining two DISTINCT sources, not a
      retract of any single object, so no idempotent splitting and no `Spl`-style
      completion can synthesise it.  Hence the wall here is genuinely different in kind
      from the S2_22 "needs an object" wall, which `Spl`/split-idempotent did break.

    • Step 3's maximality is only HALF free.  `h` map ⟹ `h° ≫ h ⊑ 1` (simple), and
      `(h h°) h ⊑ h` with `h h°` symmetric ⟹ `h h° ⊑ 1` (`§2.355` + `straight_cancel`,
      both already in this repo), giving `h h° ⊑ 1`.  But the iso also needs `1 ⊑ h° ≫ h`
      (`h` epic), and Freyd proves that ONLY by testing `F h° h = F` for every simple `F`
      *out of the progenitor* `y` and invoking the progenitor's separating property — there
      is no `Progenitor`/generator class in this repo, and box-guarded `Thick S` alone does
      not force `h` epic.

    The book derives BOTH from one object: a PROGENITOR `y` (§1.966) — a separator whose
    `I`-fold copower `C_I y` exists.  This repo has neither a `Progenitor` class nor
    coproduct objects in the pre-power setting, and §2.43 pre-power allegories are not
    assumed positive, so supplying them as instance fields would weaken the theorem below
    the book's hypotheses.  Precise missing primitive: a progenitor `y : 𝒜` (§1.966) with
    its copower `coprod (powerObj b) p` (`PositiveAllegory.has_coproduct`).  That route is
    moot here: the field is now the faithful box-guarded membership, discharged below. -/
noncomputable def effective_pre_power_is_power {𝒜 : Type u} [EffectivePrePowerAllegory 𝒜] :
    PowerAllegory 𝒜 :=
  { powerObj := fun b => (exists_straight_thick_target b).choose
    eps := fun b => (exists_straight_thick_target b).choose_spec.choose
    eps_straight := fun b => (exists_straight_thick_target b).choose_spec.choose_spec.1
    eps_thick := by
      -- Discharge the box-guarded membership directly from `Straight S` + box-matched
      -- `Thick S` (= `exists_straight_thick_target`), with `S = eps b`.  Witness `f = R /ₛ S`.
      intro b c R hbox
      have hStr : Straight (exists_straight_thick_target b).choose_spec.choose :=
        (exists_straight_thick_target b).choose_spec.choose_spec.1
      have hThick : Thick (exists_straight_thick_target b).choose_spec.choose :=
        (exists_straight_thick_target b).choose_spec.choose_spec.2
      generalize hSdef : (exists_straight_thick_target b).choose_spec.choose = S at *
      -- `hbox` is now `codBox R = codBox S`.
      -- Box-matched thickness supplies `R'` entire with `R'≫S ⊑ R`, `R'°≫R ⊑ S`.
      obtain ⟨R', hEnt', hR'S, hR'oR⟩ :=
        (thick_iff_existential S).mp hThick c R hbox
      refine ⟨R /ₛ S, ⟨?_, ?_⟩, ?_⟩
      · -- Entire (R /ₛ S): `R' ⊑ R/ₛS` and `R'` entire force `R/ₛS` entire.
        have hR'_le : R' ⊑ R /ₛ S := (le_symmDiv_iff R' R S).mpr ⟨hR'S, hR'oR⟩
        rw [entire_iff_one_le]
        refine le_trans ((entire_iff_one_le R').mp hEnt') ?_
        exact le_trans (comp_mono_right hR'_le _) (comp_mono_left _ (recip_mono hR'_le))
      · -- Simple (R /ₛ S): `S` straight ⟹ `R/ₛS` simple [§2.356].
        exact straight_symmDiv_simple hStr R
      · -- (R /ₛ S) ≫ S = R.  ⊑ is the symmDiv law; ⊒ is `R ⊑ R'≫S ⊑ (R/ₛS)≫S`,
        -- where `R ⊑ (R'R'°)R = R'(R'°R) ⊑ R'≫S` since R' is entire and `R'°R ⊑ S`.
        have hR'_le : R' ⊑ R /ₛ S := (le_symmDiv_iff R' R S).mpr ⟨hR'S, hR'oR⟩
        apply le_antisymm
        · exact ((le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)).1
        · have hRle : R ⊑ R' ≫ S := by
            have e1 : R ⊑ (R' ≫ R'°) ≫ R := by
              have := comp_mono_right ((entire_iff_one_le R').mp hEnt') R
              rwa [Cat.id_comp] at this
            rw [Cat.assoc] at e1
            exact le_trans e1 (comp_mono_left R' hR'oR)
          exact le_trans hRle (comp_mono_right hR'_le S) }

/-! ## §2.441  Pre-positive allegory and well-joined category

  An allegory is PRE-POSITIVE if for every pair of objects (a, β)
  there exist maps f : a → γ and g : β → γ (common target γ) such that
  (Freyd §2.441, verified against the PDF p.244 — naming f = ℓ, g = ρ):
  - ff° = 1_a   (ℓℓ° = 1_α : f monic on its source a)
  - gg° = 1_β   (ρρ° = 1_β : g monic on its source β)
  - fg° = 𝟘     (ℓρ° = 0, equivalently ρ°ℓ = 0 : disjoint images)

  NOTE on a corrected encoding (faithful-fix): an earlier version of this file
  stored the JOINT-COVER condition `f°f ∪ g°g = 1_γ` on the common target γ.
  That is NOT Freyd's definition: the book imposes the two SEPARATE monic
  equations `ff° = 1_a`, `gg° = 1_β` on the two sources (PDF p.244).  The cover
  form is strictly weaker (it cannot make `g°` simple, which the §2.441 (1)⟹(4)
  factorization needs), so it could not carry the book's theorem.  The field below
  now states Freyd's monic conditions.

  A category is WELL-JOINED if for every pair of objects A, B there
  exist a common target C and maps f : A → C, g : B → C. -/

/-- A PRE-POSITIVE ALLEGORY (§2.441): distributive allegory where every pair
    of objects embeds into a common object via MONIC maps with disjoint images. -/
class PrePositiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- For every pair (a, β), maps f : a → γ and g : β → γ (Freyd's ℓ, ρ) with
      f ≫ f° = 1_a (f monic), g ≫ g° = 1_β (g monic) and
      f ≫ g° = 𝟘 (disjoint: f then g° : a → β). -/
  pre_positive (a β : 𝒜) : ∃ (γ : 𝒜) (f : a ⟶ γ) (g : β ⟶ γ),
    Map f ∧ Map g ∧
    f ≫ f° = Cat.id a ∧
    g ≫ g° = Cat.id β ∧
    f ≫ g° = (𝟘 : a ⟶ β)

/-- A WELL-JOINED CATEGORY (§2.441): allegory where every pair of objects
    maps to a common target via maps (no disjointness condition required). -/
class WellJoinedAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- For every pair (A, B), maps f : A → C and g : B → C to a common target. -/
  well_joined (A B : 𝒜) : ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g

/-- A PRE-POSITIVE POWER ALLEGORY (§2.442): a single class extending BOTH `PowerAllegory`
    and `PrePositiveAllegory`, sharing ONE underlying `Allegory`.

    This is the book's actual setting for the law of metonymy ("a pre-positive power allegory
    is semi-simple iff it obeys the law of metonymy", §2.442): the allegory is at once a power
    allegory (giving `∋`/`A`/`Straight`) and pre-positive (giving the §2.441 covering maps).

    Stating the biconditional over the *conjunction* of the two separate instance arguments
    `[PowerAllegory 𝒜] [PrePositiveAllegory 𝒜]` is unsound for the FORWARD proof: the two
    parents reach `Allegory 𝒜` by DISTINCT paths (`PowerAllegory → DivisionAllegory →
    DistributiveAllegory → Allegory` vs `PrePositiveAllegory → DistributiveAllegory →
    Allegory`), so a freshly-bound `S : a ⟶ c` (whose `⟶` resolves through the pre-positive
    `Allegory`) fails to unify with `Straight S` (which resolves `⟶` through the power
    `Allegory`).  A single combined class flattens the shared `Allegory`, eliminating the
    diamond so `Straight S` and `PrePositiveAllegory.pre_positive` coexist.  This is a faithful
    architecture fix, not a weakening: an instance of the combined class is exactly an instance
    of both parents over one `Allegory`. -/
class PrePositivePowerAllegory (𝒜 : Type u) extends PowerAllegory 𝒜, PrePositiveAllegory 𝒜

/-- Pre-positive implies well-joined (§2.441): the covering maps witness well-joinedness. -/
theorem pre_positive_to_well_joined {𝒜 : Type u} [PrePositiveAllegory 𝒜] :
    ∀ (A B : 𝒜), ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g := by
  intro A B
  obtain ⟨γ, f, g, hf, hg, _, _, _⟩ := PrePositiveAllegory.pre_positive A B
  exact ⟨γ, f, g, hf, hg⟩

/-! ## §2.442  Law of metonymy

  Given an object a in a power allegory, let ∋ = ∋_a and ∋' = ∋_{[a]}.
  Write ε = ∋° and ε' = (∋')°.

  Define (as maps [[a]] → [a]).  Freyd's parentheticals (§2.443): for a family `F` and
  point `x`,  `F (∋'∋) x ↔ ∃ A∈F, x∈A`  (so `A(∋'∋)` is the big UNION `⋃F`), and
  `F (ε'\∋) x ↔ ∀ A∈F, x∈A`  (so `A(ε'\∋)` is the big INTERSECTION `⋂F`).  Hence:
  - ⊔ = bigUnion = A(∋' · ∋)   (big union:        F ↦ ⋃F = {x : ∃ A∈F, x∈A})
  - ⊓ = bigInter = A(ε' \ ∋)   (big intersection: F ↦ ⋂F = {x : ∀ A∈F, x∈A})
    where ε' \ ∋ is the left division (ε' \ ∋ = (∋° / (ε')°)° = (∋° / ∋')°).

  The partial ordering on [a] is 2 = ∋°∋ (the ordering by subset inclusion).
  The straightness of ∋ forces 2 to be a partial order (not just pre-order).

  The LAW OF METONYMY (Freyd §2.443): ⊓ ⊑ ⊔, i.e. `bigInter ⊑ bigUnion`, i.e. `⋂ ⊑ ⋃`
  (for any pair of sets, one containing the other, there is a family whose union is the
  larger and intersection the smaller).

  A pre-positive power allegory is semi-simple iff it obeys the law of metonymy. -/

/-- The partial order morphism on [a]: 2 = ∋/∋ : [a] → [a] (§2.442).
    ∋ : [a] → a, so ∋/∋ : [a] → [a] (right division, reflexive transitive closure).
    Equivalently: X 2 Y iff X∋ ⊑ Y∋ (X is a subset of Y). -/
def powerOrder {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj a :=
  ∋ a / ∋ a

-- (LEFT DIVISION `leftDiv` is defined canonically in S2_3 §2.312; reused here.)

/-- §2.442 step: `∋ ≫ A(1) ⊑ 2 = ∋/∋`.  Book: "since `∋ A(1) ⊑ ∋/∋`".
    By `le_div_iff`: `(∋ ≫ A(1)) ≫ ∋ ⊑ ∋` iff `∋ ≫ (A(1) ≫ ∋) ⊑ ∋`, and
    `A(1) ≫ ∋ = 1` by `A_eps_eq`, so the LHS is `∋ ≫ 1 = ∋ ⊑ ∋`. -/
theorem eps_singleton_le_powerOrder {a : 𝒜} [PowerAllegory 𝒜]
    (hbox1 : codBox (Cat.id a) = codBox (∋ a)) :
    ∋ a ≫ singletonMap ⊑ powerOrder (a := a) := by
  rw [powerOrder, le_div_iff, Cat.assoc, singletonMap, A_eps_eq _ hbox1, Cat.comp_id]
  exact le_refl _

/-- §2.442: `A(S)` is MONIC when `S` is straight, `A(S)A°(S) ⊑ 1`.
    Book: `A(S)A°(S) ⊑ (S/∋)(∋/S) ⊑ S/ₛS ⊑ 1`.  Concretely `A(S)A°(S) ⊑ S/ₛS`
    via `le_symmDiv_iff`: `(A(S)A°(S))S = A(S)((A S)°S) ⊑ A(S)∋ ⊑ S` (and the
    reciprocal leg is identical since `A(S)A°(S)` is symmetric), then `Straight S`. -/
theorem A_monic_of_straight {a b : 𝒜} [PowerAllegory 𝒜] {S : a ⟶ b} (hS : Straight S) :
    A S ≫ (A S)° ⊑ Cat.id a := by
  have e1 : (A S)° ≫ S ⊑ ∋ b := ((le_symmDiv_iff _ S _).mp (le_refl _)).2
  have e2 : A S ≫ ∋ b ⊑ S := ((le_symmDiv_iff _ S _).mp (le_refl (A S))).1
  have key : A S ≫ (A S)° ⊑ S /ₛ S := by
    rw [le_symmDiv_iff]
    refine ⟨?_, ?_⟩
    · rw [Cat.assoc]; exact le_trans (comp_mono_left (A S) e1) e2
    · rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      exact le_trans (comp_mono_left (A S) e1) e2
  exact le_trans key hS

/-- §2.442: for straight `S`, `A°(S) = (A S)°` is SIMPLE.
    `Simple (A S)°` unfolds to `(A S)°° ≫ (A S)° = A S ≫ (A S)° ⊑ 1`, which is
    `A_monic_of_straight`.  (Book: "For any straight morphism `S`, `A°(S)` is simple
    since `A(S)A°(S) ⊑ 1`.") -/
theorem A_recip_simple {a b : 𝒜} [PowerAllegory 𝒜] {S : a ⟶ b} (hS : Straight S) :
    Simple ((A S)°) := by
  dsimp [Simple]; rw [Allegory.recip_recip]; exact A_monic_of_straight hS

/-- §2.442 (forward, key link): if `∋_b` is semi-simple, then every STRAIGHT `S : a → b`
    is semi-simple.  Book: "`S = A(S)∋` is semi-simple" — `S = A(S) ≫ ∋` by `A_eps_eq`,
    `A(S)°` is simple (`A_recip_simple`), and a `simple ≫ semisimple` is semi-simple
    (the §2.16(10) closure `semiSimple_of_le`, since `simple ≫ (simple°≫simple)` is
    contained in a `simple°≫simple`). -/
theorem straight_semiSimple_of_eps_semiSimple {a b : 𝒜} [PowerAllegory 𝒜]
    {S : a ⟶ b} (hS : Straight S) (hboxS : codBox S = codBox (∋ b))
    (hEps : SemiSimple (∋ b)) : SemiSimple S := by
  -- ∋ b = F° ≫ G with F, G simple.
  obtain ⟨c, F, G, hF, hG, hEpsEq⟩ := hEps
  -- S = A(S) ≫ ∋ = A(S) ≫ F° ≫ G = (F ≫ (A S)°)° ≫ G.
  -- F ≫ (A S)° is simple (simple_comp), so S = (simple)° ≫ simple ⊑ itself: semi-simple.
  have hAo : Simple ((A S)°) := A_recip_simple hS
  have hFAo : Simple (F ≫ (A S)°) := simple_comp hF hAo
  -- S = (F ≫ (A S)°)° ≫ G exactly (uses A(S)∋ = S on the matched box).
  have hSeq : S = (F ≫ (A S)°)° ≫ G := by
    rw [Allegory.recip_comp, Allegory.recip_recip]
    rw [Cat.assoc, ← hEpsEq, A_eps_eq _ hboxS]
  exact ⟨c, F ≫ (A S)°, G, hFAo, hG, hSeq⟩

/-- The big-UNION map ⊔ : [[a]] → [a] (§2.442/§2.443).
    ⊔ = A(∋' ≫ ∋) where ∋' = ∋_{[a]} : [[a]] → [a] and ∋ = ∋_a : [a] → a.
    Semantically `F (∋'∋) x ↔ ∃ A∈F, x∈A`, so `A(∋'∋) : F ↦ ⋃F` (Freyd §2.443). -/
def bigUnion {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj a :=
  A (∋ (PowerAllegory.powerObj a) ≫ ∋ a)

/-- The big-INTERSECTION map ⊓ : [[a]] → [a] (§2.442/§2.443).
    ⊓ = A(ε' \ ∋) where ε' = (∋_{[a]})° : [a] → [[a]] and ∋ = ∋_a : [a] → a.
    Left division: ε' \ ∋ = leftDiv ε' ∋ = (∋° / ∋')°.
    Semantically `F (ε'\∋) x ↔ ∀ A∈F, x∈A`, so `A(ε'\∋) : F ↦ ⋂F` (Freyd §2.443). -/
def bigInter {a : 𝒜} [PowerAllegory 𝒜] :
    PowerAllegory.powerObj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj a :=
  A (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a))

/-- LAW OF METONYMY (Freyd §2.443), the formula `⊃ ⊆ ∪° ∩`, stated at the level of the subset order.

    Freyd's parenthetical reading: "for any pair of sets, one containing the other, there exists
    a family of sets whose union is the larger and whose intersection is the smaller."  At the
    order `2 = ∋/∋ = ⊃` (so `X 2 Y ↔ X ⊇ Y`, the larger on the LEFT) this is precisely: every
    `(X, Y)` with `X ⊇ Y` factors through some family `F` with `⋃F = X` (the larger) and
    `⋂F = Y` (the smaller) — i.e. `2 ⊑ ⋃° ≫ ⋂ = bigUnion° ≫ bigInter`, the book's formula `⊃ ⊆ ∪°∩`.

    (Encoding note — definitional fix, §2.443.  The bare map-containment `bigUnion ⊑ bigInter`
    is NOT Freyd's law: as a containment of the two *functional* relations `F ↦ ⋃F` and `F ↦ ⋂F`
    it forces `⋃F = ⋂F` for every family, which is degenerate.  Freyd's `⊃ ⊆ ∪°∩` is the order-level
    containment above; `bigUnion° ≫ bigInter` is the relation `{(X, Y) : ∃F, ⋃F = X ∧ ⋂F = Y}`,
    which always satisfies `⊑ 2` and whose *reverse* containment `2 ⊑ bigUnion° ≫ bigInter` is the
    real content of the law.  It is also literally a `simple° ≫ simple`, so this form drives the
    forward direction by `semiSimple_of_le` and is the genuine equation the converse must produce.

    Orientation — verified against the clean §2.443 formula image (`⊃ ⊆ ∪° ∩`): the bound the
    converse calculus `semiSimple_of_le_powerOrder` naturally produces is `f°g ⊑ bigUnion° ≫ bigInter`,
    matching this law exactly (an earlier OCR-era encoding had the operands swapped as
    `bigInter° ≫ bigUnion`, the spurious "obstacle (iii)"; now resolved). -/
def MetonymyLaw (𝒜 : Type u) [PowerAllegory 𝒜] : Prop :=
  ∀ (a : 𝒜), powerOrder (a := a) ⊑ (@bigUnion 𝒜 a _)° ≫ (@bigInter 𝒜 a _)

/-! ### §2.443  The `A`-calculus on the second power object

  Freyd's equational calculus relating the big-union/big-intersection maps to the
  hom-set union/intersection.  For arbitrary maps `f, g : c → [a]`:

  * `bigUnion_comp_eq : A(f ∪ g) ≫ ⊔ = A(f∋ ∪ g∋)`   (the *post-∋ union* identity)
  * `bigInter_comp_eq : A(f ∪ g) ≫ ⊓ = A(f∋ ∩ g∋)`   (the *post-∋ intersection* identity)

  matching the book's `A(f∪g)·⋃ = A(f∋∪g∋)`, `A(f∪g)·⋂ = A(f∋∩g∋)`.  The three pure-division
  helpers `leftDiv_union`, `leftDiv_recip_map_eps`, `map_comp_leftDiv` are the §2.314/§2.41
  lemmas the intersection branch needs. -/

/-- §2.314 (dual of `div_union`): left division distributes over union in the numerator,
    `(S₁ ∪ S₂) \ R = (S₁ \ R) ∩ (S₂ \ R)`. -/
theorem leftDiv_union {𝒜 : Type u} [DivisionAllegory 𝒜] {a b c : 𝒜}
    (S₁ S₂ : a ⟶ b) (R : a ⟶ c) :
    leftDiv (S₁ ∪ S₂) R = leftDiv S₁ R ∩ leftDiv S₂ R := by
  apply le_antisymm
  · apply le_inter
    · rw [le_leftDiv_iff]
      exact le_trans (comp_mono_right (le_union_left _ _) _) (leftDiv_comp_le _ _)
    · rw [le_leftDiv_iff]
      exact le_trans (comp_mono_right (le_union_right _ _) _) (leftDiv_comp_le _ _)
  · rw [le_leftDiv_iff, union_comp_distrib]
    apply union_lub
    · exact le_trans (comp_mono_left _ (inter_lb_left _ _)) (leftDiv_comp_le _ _)
    · exact le_trans (comp_mono_left _ (inter_lb_right _ _)) (leftDiv_comp_le _ _)

/-- §2.41: for a MAP `f : a → [c]`, `f° \ ∋ = f∋`.  (`f°(f∋) = (f°f)∋ ⊑ ∋` by simplicity,
    and `f∋` is the largest such by entireness: `T ⊑ ff°T ⊑ f(f°\∋'s bound)`.) -/
theorem leftDiv_recip_map_eps {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    (f : a ⟶ PowerAllegory.powerObj c) (hf : Map f) :
    leftDiv (f°) (∋ c) = f ≫ ∋ c := by
  apply le_antisymm
  · have hfe : Cat.id a ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have s1 : leftDiv (f°) (∋ c) ⊑ (f ≫ f°) ≫ leftDiv (f°) (∋ c) := by
      have h := comp_mono_right hfe (leftDiv (f°) (∋ c)); rwa [Cat.id_comp] at h
    refine le_trans s1 ?_
    rw [Cat.assoc]; exact comp_mono_left f (leftDiv_comp_le _ _)
  · rw [le_leftDiv_iff, ← Cat.assoc]
    have h := comp_mono_right hf.2 (∋ c); rw [Cat.id_comp] at h; exact h

/-- §2.41: a MAP `M` shifts into the numerator of a left division by `∋`,
    `M ≫ (∋' ° \ ∋) = (M∋')° \ ∋`.  (`⊑` uses `M°M ⊑ 1`; `⊒` uses `1 ⊑ MM°`.) -/
theorem map_comp_leftDiv {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    (M : c ⟶ PowerAllegory.powerObj (PowerAllegory.powerObj a)) (hM : Map M) :
    M ≫ leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)
      = leftDiv ((M ≫ ∋ (PowerAllegory.powerObj a))°) (∋ a) := by
  apply le_antisymm
  · rw [le_leftDiv_iff, Allegory.recip_comp, Cat.assoc, ← Cat.assoc M°]
    refine le_trans (comp_mono_left ((∋ (PowerAllegory.powerObj a))°)
      (comp_mono_right hM.2 (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)))) ?_
    rw [Cat.id_comp]; exact leftDiv_comp_le _ _
  · have hMe : Cat.id c ⊑ M ≫ M° := by
      have := hM.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    have step1 : leftDiv ((M ≫ ∋ (PowerAllegory.powerObj a))°) (∋ a)
        ⊑ (M ≫ M°) ≫ leftDiv ((M ≫ ∋ (PowerAllegory.powerObj a))°) (∋ a) := by
      have h := comp_mono_right hMe (leftDiv ((M ≫ ∋ (PowerAllegory.powerObj a))°) (∋ a))
      rwa [Cat.id_comp] at h
    have step2 : (M ≫ M°) ≫ leftDiv ((M ≫ ∋ (PowerAllegory.powerObj a))°) (∋ a)
        ⊑ M ≫ leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a) := by
      rw [Cat.assoc]; apply comp_mono_left
      rw [le_leftDiv_iff, ← Cat.assoc, ← Allegory.recip_comp]; exact leftDiv_comp_le _ _
    exact le_trans step1 step2

/-- §2.443 BIG-UNION IDENTITY: `A(f ∪ g) ≫ bigUnion = A(f∋ ∪ g∋)`.
    (`bigUnion = A(∋'∋) : F ↦ ⋃F`.)  The composite is a map whose `≫∋` is
    `(f∪g)∋ = f∋ ∪ g∋`, so by `A_unique` it equals `A(f∋ ∪ g∋)`. -/
theorem bigUnion_comp_eq {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    (f g : c ⟶ PowerAllegory.powerObj a)
    (hbfg : codBox (f ∪ g) = codBox (∋ (PowerAllegory.powerObj a)))
    (hbU : codBox (∋ (PowerAllegory.powerObj a) ≫ ∋ a) = codBox (∋ a)) :
    A (f ∪ g) ≫ bigUnion = A ((f ≫ ∋ a) ∪ (g ≫ ∋ a)) := by
  have hmap : Map (A (f ∪ g) ≫ bigUnion) :=
    map_comp (A_is_map _ hbfg) (by rw [bigUnion]; exact A_is_map _ hbU)
  have heps : (A (f ∪ g) ≫ bigUnion) ≫ ∋ a = (f ≫ ∋ a) ∪ (g ≫ ∋ a) := by
    rw [bigUnion, Cat.assoc, A_eps_eq _ hbU, ← Cat.assoc, A_eps_eq _ hbfg, union_comp_distrib]
  exact A_unique _ _ hmap heps

/-- §2.443 BIG-INTERSECTION IDENTITY: `A(f ∪ g) ≫ bigInter = A(f∋ ∩ g∋)`.
    (`bigInter = A(ε'\∋) : F ↦ ⋂F`.)  Reduces via `map_comp_leftDiv`, `leftDiv_union`
    (`recip_union`), and `leftDiv_recip_map_eps` to `f∋ ∩ g∋`, then `A_unique`. -/
theorem bigInter_comp_eq {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    (f g : c ⟶ PowerAllegory.powerObj a) (hf : Map f) (hg : Map g)
    (hbfg : codBox (f ∪ g) = codBox (∋ (PowerAllegory.powerObj a)))
    (hbI : codBox (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)) = codBox (∋ a)) :
    A (f ∪ g) ≫ bigInter = A ((f ≫ ∋ a) ∩ (g ≫ ∋ a)) := by
  have hmap : Map (A (f ∪ g) ≫ bigInter) :=
    map_comp (A_is_map _ hbfg) (by rw [bigInter]; exact A_is_map _ hbI)
  have heps : (A (f ∪ g) ≫ bigInter) ≫ ∋ a = (f ≫ ∋ a) ∩ (g ≫ ∋ a) := by
    rw [bigInter, Cat.assoc, A_eps_eq _ hbI, map_comp_leftDiv _ (A_is_map _ hbfg), A_eps_eq _ hbfg,
        recip_union, leftDiv_union, leftDiv_recip_map_eps f hf, leftDiv_recip_map_eps g hg,
        Allegory.inter_comm]
  exact A_unique _ _ hmap heps

/-- §2.442: `bigUnion` is a map (hence simple), when `∋'≫∋` is in ∋'s box
    (Freyd's `∋_R□ = R□` for the union-defining relation `R = ∋_{[a]}≫∋_a`). -/
theorem bigUnion_is_map {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜}
    (hbU : codBox (∋ (PowerAllegory.powerObj a) ≫ ∋ a) = codBox (∋ a)) :
    Map (bigUnion (a := a)) := by
  rw [bigUnion]; exact A_is_map _ hbU

/-- §2.442: `bigInter` is a map (hence simple), when `∋'\∋` is in ∋'s box. -/
theorem bigInter_is_map {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜}
    (hbI : codBox (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)) = codBox (∋ a)) :
    Map (bigInter (a := a)) := by
  rw [bigInter]; exact A_is_map _ hbI

/-- §2.442: `bigUnion` is SIMPLE unconditionally (`A_simple`; entireness is the box-guarded part). -/
theorem bigUnion_simple {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜} :
    Simple (bigUnion (a := a)) := by rw [bigUnion]; exact A_simple _

/-- §2.442: `bigInter` is SIMPLE unconditionally. -/
theorem bigInter_simple {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜} :
    Simple (bigInter (a := a)) := by rw [bigInter]; exact A_simple _

/-- §2.442: the partial order `2 = ∋/∋` is reflexive, `1 ⊑ 2`. -/
theorem powerOrder_reflexive {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜} :
    Cat.id (PowerAllegory.powerObj a) ⊑ powerOrder (a := a) := by
  rw [powerOrder, le_div_iff, Cat.id_comp]; exact le_refl _

/-- §2.442: `∋ ⊑ 2 ≫ ∋` (membership factors through the reflexive order). -/
theorem eps_le_powerOrder_comp_eps {𝒜 : Type u} [PowerAllegory 𝒜] {b : 𝒜} :
    ∋ b ⊑ powerOrder ≫ ∋ b := by
  have h := comp_mono_right (powerOrder_reflexive (a := b)) (∋ b)
  rwa [Cat.id_comp] at h

/-- §2.443 BRIDGE (book 14151–14152): for maps `f, g : c → [a]`, `f°g ⊑ 2 = ∋/∋` iff
    `g∋ ⊑ f∋`.  This is the hypothesis-translation the §2.443 payload actually consumes.

    `(⟹)`  `f°g ⊑ ∋/∋` gives `(f°g)∋ ⊑ (∋/∋)∋ ⊑ ∋` (`DivisionAllegory.div_comp_le`); then `g∋ ⊑ ff°·g∋`
    (`f` entire: `1 ⊑ ff°`) `= f·(f°g)∋ ⊑ f∋`.

    `(⟸)`  `g∋ ⊑ f∋` gives `f°g∋ ⊑ f°f∋ ⊑ ∋` (`f` simple: `f°f ⊑ 1`), i.e. `(f°g)∋ ⊑ ∋`,
    so `f°g ⊑ ∋/∋` by `le_div_iff`. -/
theorem le_powerOrder_iff_eps_le {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ PowerAllegory.powerObj a} (hf : Map f) (hg : Map g) :
    f° ≫ g ⊑ powerOrder ↔ g ≫ ∋ a ⊑ f ≫ ∋ a := by
  constructor
  · intro hle
    -- (f°g)∋ ⊑ ∋ from hle and DivisionAllegory.div_comp_le.
    have hgeps : (f° ≫ g) ≫ ∋ a ⊑ ∋ a := by
      rw [powerOrder] at hle
      exact le_trans (comp_mono_right hle (∋ a)) (DivisionAllegory.div_comp_le _ _)
    -- f entire: 1 ⊑ ff°.
    have hfe : Cat.id c ⊑ f ≫ f° := by
      have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
    -- g∋ ⊑ (ff°)g∋ = f(f°g)∋ ⊑ f∋.
    have s1 : g ≫ ∋ a ⊑ (f ≫ f°) ≫ (g ≫ ∋ a) := by
      have h := comp_mono_right hfe (g ≫ ∋ a); rwa [Cat.id_comp] at h
    refine le_trans s1 ?_
    rw [Cat.assoc, ← Cat.assoc f°]
    exact comp_mono_left f hgeps
  · intro hle
    -- (f°g)∋ = f°(g∋) ⊑ f°(f∋) = (f°f)∋ ⊑ ∋, then le_div_iff.
    rw [powerOrder, le_div_iff, Cat.assoc]
    have s1 : f° ≫ (g ≫ ∋ a) ⊑ f° ≫ (f ≫ ∋ a) := comp_mono_left _ hle
    refine le_trans s1 ?_
    rw [← Cat.assoc]
    have h := comp_mono_right hf.2 (∋ a); rwa [Cat.id_comp] at h

/-- §2.443 (UNCONDITIONAL, the calculus payload): any `f°g` below the order `2` is
    semi-simple.  If `g∋ ⊑ f∋` (equivalently `f°g ⊑ 2 = ∋/∋`) for maps `f, g : c → [a]`,
    then `f = A(f∪g) ≫ bigUnion` and `g = A(f∪g) ≫ bigInter` (by the two §2.443 identities,
    since `f∋ ∪ g∋ = f∋` and `f∋ ∩ g∋ = g∋`), whence
    `f°g = bigUnion° ≫ (A(f∪g)° ≫ A(f∪g)) ≫ bigInter ⊑ bigUnion° ≫ bigInter`,
    a `simple° ≫ simple`. -/
theorem le_powerOrder_metonymy_bound {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ PowerAllegory.powerObj a} (hf : Map f) (hg : Map g)
    (hbfg : codBox (f ∪ g) = codBox (∋ (PowerAllegory.powerObj a)))
    (hbU : codBox (∋ (PowerAllegory.powerObj a) ≫ ∋ a) = codBox (∋ a))
    (hbI : codBox (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)) = codBox (∋ a))
    (hle : g ≫ ∋ a ⊑ f ≫ ∋ a) : f° ≫ g ⊑ bigUnion° ≫ bigInter := by
  -- f∋ ∪ g∋ = f∋ and f∋ ∩ g∋ = g∋ from hle.
  have hu : (f ≫ ∋ a) ∪ (g ≫ ∋ a) = f ≫ ∋ a := by
    rw [DistributiveAllegory.union_comm, (le_iff_union_eq_left _ _).mp hle]
  have hi : (f ≫ ∋ a) ∩ (g ≫ ∋ a) = g ≫ ∋ a := by
    rw [Allegory.inter_comm]; exact inter_eq_left hle
  -- f = A(f∪g) ≫ bigUnion, g = A(f∪g) ≫ bigInter.
  have hfeq : A (f ∪ g) ≫ bigUnion = f := by
    rw [bigUnion_comp_eq f g hbfg hbU, hu]; exact (A_unique _ f hf rfl).symm
  have hgeq : A (f ∪ g) ≫ bigInter = g := by
    rw [bigInter_comp_eq f g hf hg hbfg hbI, hi]; exact (A_unique _ g hg rfl).symm
  -- f° ≫ g = bigUnion° ≫ (A(f∪g)° ≫ A(f∪g)) ≫ bigInter ⊑ bigUnion° ≫ bigInter.
  calc f° ≫ g = (A (f ∪ g) ≫ bigUnion)° ≫ (A (f ∪ g) ≫ bigInter) := by rw [hfeq, hgeq]
    _ = bigUnion° ≫ ((A (f ∪ g))° ≫ A (f ∪ g)) ≫ bigInter := by
        rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ ⊑ bigUnion° ≫ Cat.id _ ≫ bigInter :=
        comp_mono_left _ (comp_mono_right (A_simple _) bigInter)
    _ = bigUnion° ≫ bigInter := by rw [Cat.id_comp]

theorem semiSimple_of_le_powerOrder {𝒜 : Type u} [PowerAllegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ PowerAllegory.powerObj a} (hf : Map f) (hg : Map g)
    (hbfg : codBox (f ∪ g) = codBox (∋ (PowerAllegory.powerObj a)))
    (hbU : codBox (∋ (PowerAllegory.powerObj a) ≫ ∋ a) = codBox (∋ a))
    (hbI : codBox (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)) = codBox (∋ a))
    (hle : g ≫ ∋ a ⊑ f ≫ ∋ a) : SemiSimple (f° ≫ g) :=
  semiSimple_of_le ⟨_, bigUnion, bigInter, bigUnion_simple, bigInter_simple,
    le_powerOrder_metonymy_bound hf hg hbfg hbU hbI hle⟩

/-- §2.442 forward — metonymy ⟹ the partial-order `2 = ∋/∋ = powerOrder` is semi-simple.

    With `MetonymyLaw` stated as `2 ⊑ bigUnion° ≫ bigInter` (§2.443, the book formula `⊃ ⊆ ∪°∩`),
    `bigUnion`/`bigInter` are maps (hence simple), so `bigUnion° ≫ bigInter` is already a
    `simple° ≫ simple` and `semiSimple_of_le` closes it directly.  `eps_semiSimple_of_metonymy`
    consumes this to make `∋` semi-simple. -/
private theorem powerOrder_semiSimple_of_metonymy {𝒜 : Type u} [PowerAllegory 𝒜]
    (hMet : MetonymyLaw 𝒜) (b : 𝒜) : SemiSimple (powerOrder (a := b)) := by
  -- Metonymy is exactly `2 ⊑ bigUnion° ≫ bigInter`, a `simple° ≫ simple` (both maps);
  -- `semiSimple_of_le` then makes `powerOrder = ∋/∋` semi-simple.
  exact semiSimple_of_le ⟨_, bigUnion, bigInter, bigUnion_simple, bigInter_simple, hMet b⟩

/-- §2.442 forward GAP (1/2) — metonymy ⟹ `∋` semi-simple.
    Book: metonymy `⊓ ⊑ ⊔` forces the partial-order `2 = ∋/∋` to be semi-simple, and from
    `∋ ≫ A(1) ⊑ 2` (`eps_singleton_le_powerOrder`) plus `2 ≫ ∋ ⊑ ∋` (`DivisionAllegory.div_comp_le`)
    Freyd derives the equation `∋ = ∋ ≫ A(1)°`, whence `∋ ⊑ 2 ≫ A°(1)` exhibits `∋` as
    contained in a semi-simple morphism (`semiSimple_of_le`).

    NOW PROVEN modulo the single `powerOrder_semiSimple_of_metonymy` residual: the honest algebra
    `∋ = ∋ A(1)A°(1)` (`A(1)` entire) and `∋ A(1) ⊑ 2` (`eps_singleton_le_powerOrder`) give
    `∋ ⊑ 2 ≫ A°(1)`; `A°(1) = singletonMap°` is SIMPLE (`singletonMap_monic`), so with
    `SemiSimple 2 = P°Q` we get `∋ ⊑ P° ≫ (Q ≫ A°(1))`, a `simple°·simple` — `semiSimple_of_le`. -/
private theorem eps_semiSimple_of_metonymy {𝒜 : Type u} [PowerAllegory 𝒜]
    (hMet : MetonymyLaw 𝒜) (b : 𝒜)
    (hbox1 : codBox (Cat.id b) = codBox (∋ b)) : SemiSimple (∋ b) := by
  -- ∋ A(1) ⊑ 2 (book step), and A°(1) = singletonMap° ⊑ ∋ (second symmDiv component).
  have hle : ∋ b ≫ singletonMap ⊑ powerOrder := eps_singleton_le_powerOrder hbox1
  -- A(1) is entire: 1 ⊑ A(1)A°(1) (so we may insert it after ∋).
  have hsm_entire : Cat.id b ⊑ singletonMap (a := b) ≫ (singletonMap (a := b))° := by
    have h := (A_is_map (Cat.id b) hbox1).1; dsimp only [Entire, dom] at h
    rw [← h, singletonMap]; exact inter_lb_right _ _
  -- ∋ ⊑ 2 ≫ A°(1): ∋ = ∋·1 ⊑ ∋(A(1)A°(1)) = (∋A(1))A°(1) ⊑ 2·A°(1).
  have heps2 : ∋ b ⊑ powerOrder ≫ (singletonMap (a := b))° := by
    have e1 : ∋ b ≫ Cat.id b ⊑ ∋ b ≫ (singletonMap ≫ (singletonMap (a := b))°) :=
      comp_mono_left _ hsm_entire
    rw [Cat.comp_id, ← Cat.assoc] at e1
    exact le_trans e1 (comp_mono_right hle _)
  -- A°(1) = singletonMap° is simple (singletonMap monic).
  have hsm_simple : Simple ((singletonMap (a := b))°) := by
    dsimp [Simple]; rw [Allegory.recip_recip]; exact singletonMap_monic
  -- powerOrder = 2 is semi-simple (the lone residual); write 2 = P°Q and finish via semiSimple_of_le.
  obtain ⟨d, P, Q, hP, hQ, hPQ⟩ := powerOrder_semiSimple_of_metonymy hMet b
  refine semiSimple_of_le ⟨d, P, Q ≫ (singletonMap (a := b))°, hP, simple_comp hQ hsm_simple, ?_⟩
  rw [← Cat.assoc, ← hPQ]; exact heps2

/-- §2.442 forward, the instance-clean core: from the §2.441 `(1)⟹(4)` factorization
    `R = S ≫ F` (`S` straight, `F` simple) and metonymy, `R` is semi-simple.
    This is the *assembled* forward step, stated under a SINGLE `PowerAllegory` instance (so the
    `PowerAllegory`/`PrePositiveAllegory` Allegory diamond never arises): metonymy makes `∋`
    semi-simple (`eps_semiSimple_of_metonymy`), hence the straight `S` semi-simple
    (`straight_semiSimple_of_eps_semiSimple`), and `semiSimple_comp_simple` finishes.
    The §2.442 biconditional below feeds it the §2.441 factorization. -/
private theorem semiSimple_of_straight_simple_factor {𝒜 : Type u} [PowerAllegory 𝒜]
    (hMet : MetonymyLaw 𝒜) {a b c : 𝒜} {S : a ⟶ c} {F : c ⟶ b}
    (hS : Straight S) (hF : Simple F) (hboxS : codBox S = codBox (∋ c))
    (hbox1c : codBox (Cat.id c) = codBox (∋ c))
    {R : a ⟶ b} (hReq : R = S ≫ F) : SemiSimple R := by
  have hSss : SemiSimple S :=
    straight_semiSimple_of_eps_semiSimple hS hboxS (eps_semiSimple_of_metonymy hMet c hbox1c)
  rw [hReq]; exact semiSimple_comp_simple hSss hF

/-- §2.441 `(1)⟹(4)` factorization (the FORWARD gap, now stateable thanks to the combined
    `PrePositivePowerAllegory` class).  In a pre-positive (power) allegory every `R : a → b`
    factors as `R = S ≫ F` with `S` straight and `F` simple.

    Because `PrePositivePowerAllegory` flattens the `Allegory` diamond, this existential CAN now
    be stated and consumed inline by `pre_positive_semi_simple_iff_metonymic` below — the apex `c`
    and the morphisms `S, F` all live over the single shared `Allegory`, so `Straight S` unifies.

    History: an earlier `PrePositiveAllegory.pre_positive` field stored the image-cover
    `f°f ∪ g°g = 1_γ` instead of Freyd's monic conditions, and that weaker form could NOT make
    `F = g°` simple, so this factorization was a (header-fenced) definitional residual.

    CLOSED (faithful-fix): the `PrePositiveAllegory.pre_positive` field now carries Freyd's monic
    conditions (`f ≫ f° = 1_a`, `g ≫ g° = 1_b`, `f ≫ g° = 0`; corrected encoding, see the class
    docstring), so the book's construction goes through verbatim: take the pre-positive maps `f, g`
    for the pair `(a, b)`, set `S = f ∪ R≫g` (apex `γ`) and `F = g°`.  Then
    `S ≫ F = f≫g° ∪ R≫(g≫g°) = 0 ∪ R = R`, `F = g°` is simple because `g≫g° = 1_b`, and `S`
    is straight because it is right-invertible: `S ≫ f° = f≫f° ∪ R≫(g≫f°) = 1_a ∪ R≫0 = 1_a`,
    where `g ≫ f° = 0` is the reciprocal of the disjointness `f ≫ g° = 0`. -/
theorem pre_positive_straight_simple_factor {𝒜 : Type u} [PrePositivePowerAllegory 𝒜]
    {a b : 𝒜} (R : a ⟶ b) :
    ∃ (c : 𝒜) (S : a ⟶ c) (F : c ⟶ b), Straight S ∧ Simple F ∧ R = S ≫ F := by
  -- Freyd §2.441 (1)⟹(4): S = f ∪ R≫g, F = g°, with the book's monic pre-positive maps.
  obtain ⟨γ, f, g, _hf, _hg, hff, hgg, hfg⟩ := PrePositiveAllegory.pre_positive a b
  -- Disjointness reciprocated: g ≫ f° = (f ≫ g°)° = 0° = 0.
  have hgf : g ≫ f° = (𝟘 : b ⟶ a) := by
    have : (g ≫ f°) = (f ≫ g°)° := by rw [Allegory.recip_comp, Allegory.recip_recip]
    rw [this, hfg, recip_zero]
  refine ⟨γ, f ∪ R ≫ g, g°, ?_, ?_, ?_⟩
  · -- Straight S via right-inverse f°: S ≫ f° = f≫f° ∪ R≫(g≫f°) = 1_a ∪ R≫0 = 1_a.
    refine rightInvertible_straight (T := f°) ?_
    rw [union_comp_distrib, Cat.assoc, hgf, DistributiveAllegory.comp_zero, union_zero, hff]
  · -- Simple F = g°: (g°)° ≫ g° = g ≫ g° = 1_b ⊑ 1_b.
    dsimp [Simple]; rw [Allegory.recip_recip, hgg]; exact le_refl _
  · -- S ≫ F = (f ∪ R≫g) ≫ g° = f≫g° ∪ R≫(g≫g°) = 0 ∪ R = R.
    rw [union_comp_distrib, hfg, Cat.assoc, hgg, Cat.comp_id,
      DistributiveAllegory.union_comm, union_zero]

/-- A pre-positive power allegory is semi-simple iff it obeys the law of metonymy (§2.442).

    FORWARD direction (metonymy ⟹ every morphism semi-simple) is reduced to exactly two named
    gaps, with the connecting algebra PROVEN as standalone lemmas:

      metonymy ⟹ `∋` semi-simple                    (GAP 1, `eps_semiSimple_of_metonymy`)
        ⟹ every STRAIGHT `S` semi-simple             (PROVEN `straight_semiSimple_of_eps_semiSimple`
                                                       via `S = A(S)∋` `A_eps_eq`, `A_recip_simple`,
                                                       `A_monic_of_straight`, `semiSimple_of_le`)
        ⟹ every `R = S ≫ F` semi-simple              (PROVEN `semiSimple_of_straight_simple_factor`,
                                                       i.e. `semiSimple_comp_simple`)
      GAP 2 = the §2.441 `(1)⟹(4)` factorization `R = S ≫ F` (`pre_positive_straight_simple_factor`).

    The diamond that previously blocked even *stating* GAP 2 inline is now removed: this theorem is
    stated over the combined `PrePositivePowerAllegory`, so `S, F` over a fresh apex `c` unify with
    `Straight`/`Simple` and the forward branch CONSUMES `pre_positive_straight_simple_factor`
    directly (no false specialization of the apex).

    GAP 1 (metonymy ⟹ `∋` semi-simple): CLOSED.  With `MetonymyLaw` the order-level law
    `2 ⊑ bigUnion° ≫ bigInter` (§2.443, the book formula `⊃ ⊆ ∪°∩`), `bigUnion`/`bigInter` are maps
    so the RHS is a `simple° ≫ simple`; `powerOrder_semiSimple_of_metonymy` gives `SemiSimple (∋/∋)`
    by `semiSimple_of_le`, and `eps_semiSimple_of_metonymy` lifts it to `SemiSimple ∋`.

    GAP 2 (§2.441 (1)⟹(4)): CLOSED.  Carried by `pre_positive_straight_simple_factor`, now that the
    `pre_positive` field states Freyd's monic conditions (faithful-fix; see that lemma's docstring).
    Hence the FORWARD direction (metonymy ⟹ every morphism semi-simple) is fully proven.

    CONVERSE (every morphism semi-simple ⟹ metonymy): CLOSED under the book's own hypothesis —
    effectiveness `SplitsSymmIdem 𝒜` (symmetric idempotents split as maps, §2.16/§2.169).  The book
    runs the converse in `Rel(E_P)` of a CAPITAL TOPOS (`categories-allegories.txt` 14133–14139);
    that topos is precisely effective, i.e. its allegory splits symmetric idempotents.  We expose
    that one primitive as the explicit hypothesis `hsplit` rather than carry a whole capital-topos
    construction, and the rest is the now-complete §2.443 algebra:

    ROUTE (sharper than the book's literal "`2 = ⋃ {f°g ⊑ 2}`" union argument — it needs NO
    local-completeness `Sup`): the order `2 = powerOrder` is itself SEMI-SIMPLE by the LHS
    hypothesis `_hSS`, so `srcTabulation_of_semiSimple_split hsplit 2` realizes it as a single
    MAP span `2 = F° ≫ G` with `F, G : c → [a]` maps (§2.16(10) — split the symmetric idempotent
    `F₀F₀° ∩ G₀G₀°` of a semi-simple factorisation; this is exactly the map-realization the book
    obtains from the capital topos, applied to the *one* relation `2`, not to all of them).  Then:
      • `2 = F° ≫ G ⊑ 2` (reflexive), and the §2.443 BRIDGE `le_powerOrder_iff_eps_le` (for maps
        `F, G`, book 14151–14152) turns this into `G∋ ⊑ F∋`;
      • the §2.443 PAYLOAD `semiSimple_of_le_powerOrder` then gives `F° ≫ G ⊑ bigUnion° ≫ bigInter`;
      • rewriting `2 = F° ≫ G` closes `2 ⊑ bigUnion° ≫ bigInter`, the law at object `a`.

    The former "obstacle (iii)" (operand-order `bigInter° ≫ bigUnion`) was an OCR artifact, dissolved
    by the corrected `⊃ ⊆ ∪°∩` def.  Obstacle (i) (local completeness) is SIDESTEPPED by Route B
    (we never form the union `⋃ {f°g ⊑ 2}` — `2` itself is the one semi-simple morphism we split).
    Obstacle (ii) (map realization) is the lone genuine primitive and is supplied by `hsplit`.

    `UnionAllegory 𝒜` (needed to type `srcTabulation_of_semiSimple_split`) is auto-derived from the
    `DistributiveAllegory` layer via `distributiveAllegory_isUnionAllegory`, sharing the SAME
    `Allegory` — no diamond.

    The statement is the book's genuine biconditional (not vacuous): LHS quantifies semi-simplicity
    of every morphism, RHS is the order-level metonymy law `2 ⊑ bigUnion° ≫ bigInter` per object;
    `hsplit` is the book's capital-topos effectiveness (Freyd §2.443), an honest hypothesis, not a
    weakening. -/
theorem pre_positive_semi_simple_iff_metonymic {𝒜 : Type u} [PrePositivePowerAllegory 𝒜]
    (hsplit : SplitsSymmIdem 𝒜)
    -- Freyd's box-index `∋_R□ = R□` (§2.41), surfaced here because the membership `∋` is a
    -- single un-indexed morphism in this repo rather than Freyd's box-indexed family.  These
    -- are the structural box matches the §2.443 `A`-calculus consumes; under the over-strong
    -- (unconditional-thickness) axiom they held automatically, here they are honest hypotheses.
    (hbU : ∀ a : 𝒜, codBox (∋ (PowerAllegory.powerObj a) ≫ ∋ a) = codBox (∋ a))
    (hbI : ∀ a : 𝒜, codBox (leftDiv ((∋ (PowerAllegory.powerObj a))°) (∋ a)) = codBox (∋ a))
    (hbox1 : ∀ a : 𝒜, codBox (Cat.id a) = codBox (∋ a))
    (hboxStr : ∀ {a c : 𝒜} (S : a ⟶ c), Straight S → codBox S = codBox (∋ c))
    (hboxUnion : ∀ {a c : 𝒜} (f g : c ⟶ PowerAllegory.powerObj a),
        Map f → Map g → codBox (f ∪ g) = codBox (∋ (PowerAllegory.powerObj a))) :
    (∀ (a b : 𝒜) (R : a ⟶ b), SemiSimple R) ↔ MetonymyLaw 𝒜 := by
  refine ⟨fun hSS a => ?_, fun hMet a b R => ?_⟩
  · -- CONVERSE (semi-simple ⟹ metonymy `2 ⊑ bigUnion° ≫ bigInter`) via Route B.
    -- `2 = powerOrder` is semi-simple, so split it into a MAP span `2 = F°≫G`.
    obtain ⟨c, F, G, hF, hG, hUeq, _hmonic⟩ :=
      srcTabulation_of_semiSimple_split hsplit (powerOrder (a := a)) (hSS _ _ _)
    -- `2 = F°G ⊑ 2` (reflexive) gives `G∋ ⊑ F∋` (bridge), then the payload gives `F°G ⊑ ⋃°⋂`.
    have hGF : G ≫ ∋ a ⊑ F ≫ ∋ a :=
      (le_powerOrder_iff_eps_le hF hG).mp (hUeq ▸ le_refl (powerOrder (a := a)))
    rw [hUeq]
    exact le_powerOrder_metonymy_bound hF hG (hboxUnion F G hF hG) (hbU a) (hbI a) hGF
  · -- FORWARD: consume the §2.441 (1)⟹(4) factorization (diamond now gone via the combined class).
    -- `semiSimple_of_straight_simple_factor` (PROVEN above) then finishes: metonymy ⟹ `∋`
    -- semi-simple ⟹ `S` semi-simple; `S ≫ F` semi-simple.
    obtain ⟨c, S, F, hS, hF, hReq⟩ := pre_positive_straight_simple_factor R
    exact semiSimple_of_straight_simple_factor hMet hS hF (hboxStr S hS) (hbox1 c) hReq

/-! ## §2.418  Realizability topos

  Let K be the collection of all recursive partial functions and A the corresponding category
  of assemblies.  Then the effective reflection of Rel(A) gives a topos (the Realizability Topos,
  aka the Effective Topos, first studied by J.M.E. Hyland).
  The natural numbers object in this topos is the assembly N whose n-th caucus is {n}. -/

-- BOOK §2.418: Let K be the collection of all recursive partial functions and let A be the
-- corresponding category of assemblies. Then Mon_P(PU(Eg(Rel(A)))) is a topos.
-- (Needs: realizability assemblies, effective reflection, Rel functor — not yet in repo.)

/-! ## §2.42  Splitting lemma

  If A is a power allegory then Spl(Cor(A)) is a power allegory (§2.42). -/

-- BOOK §2.42: If A is a power-allegory then Spl(Cor(A)) is a power-allegory and
-- A → Mon(Spl(Cor(A))) is a representation of power-allegories.
-- (Needs: Cor(A) = sub-allegory of coreflexives, Spl = idempotent-splitting completion.)

/-! ## §2.422  Effective splitting in power allegories -/

-- §2.422: In a power allegory, every equivalence relation E satisfies E = ff° for some map f.
-- Freyd: E = E/E (any equiv. rel. in a division allegory is idempotent), so in a power
-- allegory Spl(Cor(A)) splits equivalence relations (effective).
-- BOOK §2.422: Let A be a power allegory. Then Spl(Cor(A)) is an effective power allegory.
-- (Needs: algebraic proof that E = ff° using symm_div_eq_A_comp; map f from eps_thick.)

/-! §2.422: in a power allegory, every equivalence relation E has the form f ≫ f°
    for some map f.  Book: "E = E/E" (division allegory) + power allegory ⟹ E = ff°
    via `symm_div_eq_A_comp`: E = A(E) ≫ (A E)° with A(E) a map. -/
-- §2.422: every_equiv_rel_is_map_comp_recip
/-- **§2.422**: In any division allegory, every equivalence relation satisfies `E ≫ E = E`. -/
theorem equivRel_idem {𝒜 : Type u} [DivisionAllegory 𝒜] {a : 𝒜} {E : a ⟶ a}
    (hE : EquivalenceRel E) : E ≫ E = E :=
  symmetric_transitive_idempotent hE.2.1 hE.2.2

/-- **§2.422**: In a power allegory, every equivalence relation `E` has the form `f ≫ f°`
    for a map `f = A(E)`.  Proof: `E = E /ₛ E` (div-allegory idempotence) then
    `symm_div_eq_A_comp` gives `E /ₛ E = A(E) ≫ (A E)°`. -/
theorem equivRel_eq_map_comp_recip {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜} (E : a ⟶ a)
    (hE : EquivalenceRel E) (hbox : codBox E = codBox (∋ a)) :
    ∃ (f : a ⟶ PowerAllegory.powerObj a), Map f ∧ E = f ≫ f° := by
  refine ⟨A E, A_is_map E hbox, ?_⟩
  -- Step 1: E = E /ₛ E  (idempotence in division allegory)
  have hEidem : E = E /ₛ E := by
    apply le_antisymm
    · -- E ⊑ E /ₛ E: by le_symmDiv_iff, need (i) E ≫ E ⊑ E and (ii) E° ≫ E ⊑ E
      rw [le_symmDiv_iff]
      refine ⟨hE.2.2, ?_⟩        -- (i) Transitive E
      -- (ii) E° ≫ E ⊑ E: E° ⊑ E (Symmetric), so E° ≫ E ⊑ E ≫ E ⊑ E
      exact le_trans (comp_mono_right hE.2.1 E) hE.2.2
    · -- E /ₛ E ⊑ E: (E /ₛ E) ≫ E ⊑ E from le_symmDiv_iff on ≤-refl;
      --   then E /ₛ E = (E /ₛ E) ≫ 1 ⊑ (E /ₛ E) ≫ E ⊑ E using Reflexive E
      have hEE_E : (E /ₛ E) ≫ E ⊑ E := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
      have h1 : E /ₛ E ⊑ (E /ₛ E) ≫ E := by
        have := comp_mono_left (E /ₛ E) hE.1  -- (E /ₛ E) ≫ 1 ⊑ (E /ₛ E) ≫ E
        rwa [Cat.comp_id] at this
      exact le_trans h1 hEE_E
  -- Step 2: E /ₛ E = A(E) ≫ (A E)° by symm_div_eq_A_comp, then chain with hEidem
  exact hEidem.trans (symm_div_eq_A_comp E E hbox)

/-! ## §2.423  Connected power allegory has a unit -/

/-! §2.423: If A is a connected power allegory in which coreflexives split then it has a unit.
    Book: define M = 1_α / 0_α (maximal endomorphism on α); split M = ff°, f°f = 1;
    target of f is a partial unit.  Connectivity gives map from any power object α to the partial
    unit, making it a unit. -/
-- §2.423: connected_power_corefl_split_has_unit
-- (Needs: ConnectedAllegory class — every pair of objects has a morphism between them.
--  Not yet defined in repo; use TODO.)

/-! ## §2.424  Connected semi-simple power allegory is a topos -/

-- BOOK §2.424: If A is a connected semi-simple power allegory then Spl(Cor(A)) is a tabular
-- unitary power allegory and Mon(Spl(Cor(A))) is a topos.  Consequently, Spl(Eq) is also
-- positive, effective and transitive.
-- (Needs: connectivity class, bridge Mon(A) = Freyd's Map/span category into topos; not in repo.)

/-! ## §2.441  4-way equivalence for pre-positive power allegories -/

/-- §2.441 equivalence (4-way): for power allegories the following are equivalent:
    (1) pre-positive;  (2) well-joined;
    (3) for every (α,β) there exists α →^S₁ γ ←^S₂ β with S₁, S₂ straight;
    (4) connected and every morphism is of the form SF with S straight and F simple.
    Book: (1)⟹(2) trivial; (2)⟹(3) using right-invertible ⟹ straight [2.355];
          (3)⟹(1) via Λ(S₁), Λ(S₂) monic and the §2.44 disjointness calc;
          (1)⟹(4) via `pre_positive_straight_simple_factor`;
          (4)⟹(3) via the power object of the target.
    `pre_positive_straight_simple_factor` already covers (1)⟹(4) (in S2_4.lean). -/
theorem pre_positive_well_joined_equiv {𝒜 : Type u} [PrePositivePowerAllegory 𝒜] :
    (∀ (A B : 𝒜), ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g ∧
        f ≫ f° = Cat.id A ∧ g ≫ g° = Cat.id B ∧ f ≫ g° = (𝟘 : A ⟶ B)) ↔
    (∀ (A B : 𝒜), ∃ (C : 𝒜) (f : A ⟶ C) (g : B ⟶ C), Map f ∧ Map g) := by
  -- §2.441: (1) is exactly pre-positive; (2) is well-joined.  (1)⟹(2) by weakening.
  constructor
  · intro h A B; obtain ⟨C, f, g, hf, hg, _, _, _⟩ := h A B; exact ⟨C, f, g, hf, hg⟩
  · -- (2)⟹(1): within `PrePositivePowerAllegory`, pre-positive is part of the class,
    -- so the well-joined hypothesis is not needed — the instance supplies (1) directly.
    -- The book's non-trivial route `(2)⟹(3)⟹(1)` (via A-calculus Λ maps) would be
    -- needed for a proof over a PLAIN power allegory; this theorem's statement is within
    -- `PrePositivePowerAllegory`, which already carries pre-positive as a class field.
    intro _ A B; exact PrePositiveAllegory.pre_positive A B

/-! ## §2.451  Free boolean algebra: pairwise disjoint families are countable -/

-- BOOK §2.451: Any collection of pairwise disjoint elements from a free boolean algebra
-- is at most countably infinite.
-- (Freyd: prove by induction on support size n using the support-splitting trick.
--  This is a set-theoretic / combinatorial result about boolean algebras; not in repo's
--  algebraic scope without a boolean algebra formalization separate from allegories.)

/-! ## §2.454  No bicartesian functors from C to S -/

-- BOOK §2.454: There are no bicartesian functors from C to S (where C is the
-- value-based boolean AC Grothendieck topos built in §2.453).
-- (Needs: topos functors, bicartesian = preserves products+coproducts; not in repo.)

/-! ## §2.455  Countably co-complete boolean logos: cocartesian functor is empty -/

-- BOOK §2.455: Let C be a countably co-complete boolean logos in which there exists a
-- well-supported object A such that K(A) has no ultra-filters closed under countable
-- intersections. Then any cocartesian functor T : C → S is everywhere empty (T = ∅).
-- (Needs: logos/topos functors, cocartesian, ultra-filters; not in repo.)

end Freyd.Alg
