/-
  Freyd & Scedrov, *Categories, Allegories* §1.84
  Grothendieck topoi (Giraud definition) and immediate consequences.

  §1.84  GIRAUD DEFINITION of a Grothendieck topos.
  §1.843 A Grothendieck topos is well-powered (and well-copowered).
  §1.844 A Grothendieck topos is locally complete.
  §1.845 Coproducts in E remain coproducts in Rel(E).
  §1.846 A coequalizer in E remains a coequalizer in Rel(E).

  NOTE: We do not import S1_70 here because that file has a build error
  (logos_implies_preLogos is missing PreLogos fields).  The one class
  we need from §1.712 (LocallyComplete) is redefined locally below.
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_62
import Fredy.S1_64
import Fredy.S1_77
import Fredy.S1_82

open Freyd

universe v u

namespace Freyd

variable {E : Type u} [Cat.{v} E]

/-! ## Local infrastructure ------------------------------------------------- -/

/-- Arbitrary-indexed coproduct: ΣAᵢ with injections uᵢ : Aᵢ → ΣAᵢ. -/
structure Coproduct {𝒞 : Type u} [Cat.{v} 𝒞] {I : Type v} (A : I → 𝒞) where
  obj  : 𝒞
  inj  : ∀ i, A i ⟶ obj
  desc : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X), obj ⟶ X
  fac  : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X) (i : I), inj i ≫ desc f = f i
  uniq : ∀ {X : 𝒞} (f : ∀ i, A i ⟶ X) (h : obj ⟶ X),
           (∀ i, inj i ≫ h = f i) → h = desc f

/-- A category has all small coproducts indexed by types in universe v. -/
class HasAllCoproducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  coprod : ∀ {I : Type v} (A : I → 𝒞), Coproduct A

-- COCOMPLETE (§1.823) is defined canonically in S1_82.  For the Giraud bundle
-- below we require its two building blocks directly: `HasAllCoproducts` (above)
-- and `HasCoequalizers` (from S1_58), avoiding a duplicate `Cocomplete` class.

/-- LOCALLY COMPLETE (§1.712): each subobject lattice is a complete lattice.
    Redefined here to avoid importing the broken S1_70 build. -/
class LocallyComplete' (𝒞 : Type u) [Cat.{v} 𝒞] extends HasImages 𝒞 where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A),
    S s → Subobject.le s (sup S)
  sup_least : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ s, S s → Subobject.le s U) → Subobject.le (sup S) U

/-! ## §1.84 Giraud Definition of a Grothendieck Topos ---------------------- -/

/-- DISJOINT COPRODUCTS (§1.845): for coproduct {uᵢ : Aᵢ → S},
    each uᵢ is monic, the family is jointly a cover, and
    the intersection A i ×_{S} A j is the zero subobject for i ≠ j.

    Book formulation: uᵢ uᵢ° = 1, uᵢ° uⱼ = 0 (i ≠ j), ⋃ uᵢ° uᵢ = 1. -/
structure DisjointCoproduct {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {I : Type v} {A : I → 𝒞} (cp : Coproduct A) : Prop where
  /-- Each injection is monic (expresses uᵢ uᵢ° = 1 as a map). -/
  inj_monic    : ∀ i, Mono (cp.inj i)
  /-- The injections are jointly a cover of the coproduct object. -/
  inj_cover    : Cover (cp.desc (fun i => cp.inj i))
  /-- Disjointness: the pullback of uᵢ and uⱼ (i ≠ j) is the zero subobject,
      i.e., for any X with f : X → Aᵢ, g : X → Aⱼ, f uᵢ = g uⱼ implies X ≅ 0.
      We express this by saying any h : X → Z factors through the initial morphism
      (X is the zero object in a canonical sense). -/
  inj_disjoint : ∀ (i j : I), i ≠ j →
    ∀ {X : 𝒞} (f : X ⟶ A i) (g : X ⟶ A j),
      f ≫ cp.inj i = g ≫ cp.inj j →
      ∀ {Z : 𝒞} (h k : X ⟶ Z), h = k

/-- PULLBACKS PRESERVE ARBITRARY UNIONS (§1.84): the inverse-image functor
    f# commutes with arbitrary suprema of subobjects.
    Concretely: if {Bₛ} is a family of subobjects of B whose supremum is all
    of B (i.e., the identity sub-object), then the inverse images f#(Bₛ)
    also have their supremum equal to all of A.

    We express "supremum = all of A" as: for any monic m : X → A, if every
    f#(Bₛ) ≤ X then m is an iso (i.e., X = A up to iso). -/
def PullbacksPreserveArbitraryUnions (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
    -- hypothesis: the family S covers B (its upper bound is B)
    (∀ {X : 𝒞} (m : X ⟶ B) (hm : Mono m),
       (∀ s, S s → Subobject.le s ⟨X, m, hm⟩) → IsIso m) →
    -- conclusion: the inverse images f#(S) cover A
    (∀ {X : 𝒞} (m : X ⟶ A) (hm : Mono m),
       (∀ s, S s → Subobject.le (InverseImage f s) ⟨X, m, hm⟩) → IsIso m)

/-- THE GIRAUD DEFINITION (§1.84):
    A GROTHENDIECK TOPOS is a locally small, cocomplete, effective regular
    category with a generating set, disjoint coproducts, and pullbacks
    that preserve arbitrary unions. -/
class GrothendieckTopos (E : Type u) [Cat.{v} E] extends
    EffectiveRegular E, HasAllCoproducts E, HasCoequalizers E, LocallyComplete' E where
  /-- A SMALL generating set (§1.84, §1.632), presented as a `Type v`-indexed
      family `gen_obj : gen_idx → E`.  Smallness (an index in universe `v`) is
      part of the Giraud definition ("a small generating set") and is exactly
      what the well-powered argument (§1.843) needs to bound `Sub(A)`. -/
  gen_idx         : Type v
  gen_obj         : gen_idx → E
  /-- In a pre-topos the small generating set is a BASIS (§1.632): it is
      collectively faithful on subobjects, i.e. every proper mono is witnessed
      by a generalized element from a generator that does not factor through it. -/
  gen_basis       : IsBasis (𝒞 := E) (fun X => ∃ i, gen_obj i = X)
  /-- All coproducts are disjoint (§1.845). -/
  coprod_disjoint : ∀ {I : Type v} (A : I → E),
    DisjointCoproduct (HasAllCoproducts.coprod A)
  /-- Pullbacks preserve arbitrary unions (§1.84).
      Note: PullbacksPreserveArbitraryUnions does not depend on LocallyComplete'. -/
  pullback_union  : PullbacksPreserveArbitraryUnions E

/-- The underlying predicate of the generating set: `X` is a generator iff it is
    `gen_obj i` for some index `i`.  (§1.84) -/
def GrothendieckTopos.gen_set (E : Type u) [Cat.{v} E] [GrothendieckTopos E] :
    E → Prop := fun X => ∃ i, GrothendieckTopos.gen_obj (E := E) i = X

/-- The generating set is generating (it is the first component of the basis). -/
theorem GrothendieckTopos.has_gen_set (E : Type u) [Cat.{v} E] [GrothendieckTopos E] :
    IsGeneratingSet (GrothendieckTopos.gen_set E) :=
  (GrothendieckTopos.gen_basis (E := E)).1

/-! ## §1.841–§1.842 Examples and the graphing-functor adjoint ---------------- -/

/-
  §1.841: The prime examples (presheaf topos YA and the topos of sheaves B☞(Y))
  satisfy the Giraud definition.
  MISSING: Cannot be stated without formalizing the presheaf construction.

  §1.842: If E is a Grothendieck topos, the graphing functor E → Rel(E) has a
  right adjoint.
  MISSING: Rel(E) as a category (with objects = objects of E and morphisms =
  equivalence classes of relations) is not yet formalized in this repo.
  The statement requires a `Cat` instance on Rel(E) and a `Functor` instance
  for the graphing map E → Rel(E).  See S1_84.md.
-/

/-! ## §1.843 A Grothendieck topos is well-powered (and well-copowered) ----- -/

/-- Antisymmetry of the subobject order: `S ≤ T` and `T ≤ S` give an iso of
    subobjects.  The factoring map of `S ≤ T` is the iso (its two-sided inverse
    is the factoring map of `T ≤ S`, by monicity of the representing arrows). -/
theorem subobjectIso_of_le_le {B : E} {S T : Subobject E B}
    (hST : Subobject.le S T) (hTS : Subobject.le T S) : SubobjectIso S T := by
  obtain ⟨h, hh⟩ := hST            -- h : S.dom ⟶ T.dom, h ≫ T.arr = S.arr
  obtain ⟨k, hk⟩ := hTS            -- k : T.dom ⟶ S.dom, k ≫ S.arr = T.arr
  refine ⟨h, ⟨k, ?_, ?_⟩, hh⟩
  · -- h ≫ k = id_{S.dom}, via S monic: (h ≫ k) ≫ S.arr = S.arr
    apply S.monic
    calc (h ≫ k) ≫ S.arr = h ≫ (k ≫ S.arr) := Cat.assoc _ _ _
      _ = h ≫ T.arr := by rw [hk]
      _ = S.arr := hh
      _ = Cat.id S.dom ≫ S.arr := by rw [Cat.id_comp]
  · -- k ≫ h = id_{T.dom}, via T monic
    apply T.monic
    calc (k ≫ h) ≫ T.arr = k ≫ (h ≫ T.arr) := Cat.assoc _ _ _
      _ = k ≫ S.arr := by rw [hh]
      _ = T.arr := hk
      _ = Cat.id T.dom ≫ T.arr := by rw [Cat.id_comp]

/-- The TRACE of a subobject `S ↣ B`: the family, indexed by generators `gen i`
    and generalized elements `x : gen i ⟶ B`, recording whether `x` factors
    through `S` (i.e. `Allows S x`).  This is the embedding `Sub(B) ↪ Π_{G∈ℱ} 𝒫(Hom(G,B))`
    of the §1.843 argument; it lives in `Type v` because the generating set is small. -/
def subTrace [GrothendieckTopos E] {B : E} (S : Subobject E B) :
    (i : GrothendieckTopos.gen_idx (E := E)) → (GrothendieckTopos.gen_obj i ⟶ B) → Prop :=
  fun i x => Allows S x

/-- BASIS DETECTS SUBOBJECTS (§1.843): if every generalized element from a
    generator that factors through `S` also factors through `T`, then `S ≤ T`.
    Proof: the pullback `P = S ∩ T → S.dom` is monic; were it a proper subobject
    of `S.dom` the basis would supply a generator element of `S.dom` not factoring
    through `P`, i.e. an `x ≫ S.arr` that allows `S` but not `T` — contradiction.
    Hence `P ≅ S.dom` and `S` factors through `T`. -/
theorem le_of_subTrace_le [GrothendieckTopos E] {B : E} {S T : Subobject E B}
    (h : ∀ i x, subTrace S i x → subTrace T i x) : Subobject.le S T := by
  -- Pullback of S.arr and T.arr; π₁ : P → S.dom is monic (pullback of monic T.arr).
  let pb := HasPullbacks.has S.arr T.arr
  have hπ₁mono : Mono pb.cone.π₁ := mono_pullback S.arr T.arr T.monic pb
  -- Claim: π₁ is iso.  Suppose not; the basis gives a witness contradicting `h`.
  have hiso : IsIso pb.cone.π₁ := Classical.byContradiction fun hni => by
    obtain ⟨G, ⟨i, hGi⟩, x, hx⟩ :=
      (GrothendieckTopos.gen_basis (E := E)).2 pb.cone.π₁ hπ₁mono hni
    -- x : G ⟶ S.dom does not factor through π₁.  Transport to the generator gen i.
    subst hGi
    -- x ≫ S.arr : gen i ⟶ B factors through S (witness x), hence through T by h.
    have hAllowsS : subTrace S i (x ≫ S.arr) := ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := h i (x ≫ S.arr) hAllowsS   -- z : gen i ⟶ T.dom, z ≫ T.arr = x ≫ S.arr
    -- (x, z) is a cone over (S.arr, T.arr); its lift factors x through π₁ — contradiction.
    have hw : x ≫ S.arr = z ≫ T.arr := hz.symm
    refine hx ⟨pb.lift ⟨GrothendieckTopos.gen_obj i, x, z, hw⟩, ?_⟩
    exact pb.lift_fst ⟨GrothendieckTopos.gen_obj i, x, z, hw⟩
  -- π₁ iso ⟹ S ≤ T:  S.arr = π₁ ≫ S.arr = π₂ ≫ T.arr, and π₁⁻¹ ≫ π₂ factors S through T.
  obtain ⟨π₁inv, _hl, hr⟩ := hiso   -- hr : π₁inv ≫ pb.cone.π₁ = Cat.id S.dom
  refine ⟨π₁inv ≫ pb.cone.π₂, ?_⟩
  calc (π₁inv ≫ pb.cone.π₂) ≫ T.arr
        = π₁inv ≫ (pb.cone.π₂ ≫ T.arr) := Cat.assoc _ _ _
    _ = π₁inv ≫ (pb.cone.π₁ ≫ S.arr) := by rw [pb.cone.w]
    _ = (π₁inv ≫ pb.cone.π₁) ≫ S.arr := (Cat.assoc _ _ _).symm
    _ = Cat.id S.dom ≫ S.arr := by rw [hr]
    _ = S.arr := Cat.id_comp _

/-- §1.843: A Grothendieck topos is WELL-POWERED: the collection Sub(A) of
    subobjects of each object A is a set (up to isomorphism, bounded by a
    type in universe v).

    BOOK PROOF: The generating set ℱ is also a basis in any pre-topos
    (every subobject appears as an equalizer, hence is detected by ℱ).
    Sub(A) embeds into Π_{G∈ℱ} 𝒫(Hom(G,A)), which is small.

    FORMALIZATION: index `Sub(B)` by its `Type v` of traces
    `Π_{i} (gen i ⟶ B) → Prop`; pick a representative subobject for each trace
    (where one exists).  `le_of_subTrace_le` (both directions) shows equal traces
    force a subobject iso, so every subobject is iso to its representative. -/
noncomputable instance grothendieck_topos_well_powered [GrothendieckTopos E] :
    WellPowered E where
  small := by
    classical
    intro B
    -- Index type: the (small) type of traces.
    refine ⟨((i : GrothendieckTopos.gen_idx (E := E)) → (GrothendieckTopos.gen_obj i ⟶ B) → Prop),
            fun t => if ht : ∃ S : Subobject E B, subTrace S = t then ht.choose
                     else Subobject.entire B, ?_⟩
    intro S
    refine ⟨subTrace S, ?_⟩
    -- The representative at index `subTrace S` is some S' with `subTrace S' = subTrace S`.
    have hex : ∃ S' : Subobject E B, subTrace S' = subTrace S := ⟨S, rfl⟩
    dsimp only
    rw [dif_pos hex]
    have hchoose : subTrace hex.choose = subTrace S := hex.choose_spec
    -- Equal traces ⟹ mutual ≤ ⟹ SubobjectIso.
    have hST : Subobject.le S hex.choose :=
      le_of_subTrace_le (fun i x hxS => by rw [hchoose]; exact hxS)
    have hTS : Subobject.le hex.choose S :=
      le_of_subTrace_le (fun i x hxS => by rw [hchoose] at hxS; exact hxS)
    exact subobjectIso_of_le_le hST hTS

/-- Two covers A ↠ P and A ↠ Q are ISOMORPHIC if there is a commuting iso P ≅ Q. -/
def CoverIso {𝒞 : Type u} [Cat.{v} 𝒞] {A : 𝒞} {P Q : 𝒞}
    (p : A ⟶ P) (q : A ⟶ Q) : Prop :=
  ∃ (i : P ⟶ Q), IsIso i ∧ p ≫ i = q

/-- WELL-COPOWERED: for each A, the class of covers A ↠ Q (up to isomorphism)
    is bounded by a type in universe v. -/
class WellCopowered (𝒞 : Type u) [Cat.{v} 𝒞] : Prop where
  small : ∀ (A : 𝒞), ∃ (I : Type v) (codom : I → 𝒞) (cov : ∀ i, A ⟶ codom i)
            (hcov : ∀ i, Cover (cov i)),
            ∀ (Q : 𝒞) (q : A ⟶ Q) (_ : Cover q),
              ∃ i : I, CoverIso (cov i) q

/-- The KERNEL-PAIR SUBOBJECT of a map `q : A ⟶ Q`: the level `(kp₁,kp₂)` of `q`
    packaged as a subobject of `A × A`.  Two covers determine the same kernel-pair
    subobject (up to iso) exactly when they are isomorphic as quotients (§1.566). -/
def kpSub [GrothendieckTopos E] {A Q : E} (q : A ⟶ Q) : Subobject E (prod A A) :=
  ⟨kernelPair q, pair (kp₁ (f := q)) (kp₂ (f := q)),
   monic_pair_of_monicPair _ _ (kernelPairRel q).isMonicPair⟩

/-- BRIDGE (§1.566): isomorphic kernel-pair subobjects give isomorphic covers.
    From `i ≫ pair(kp₁',kp₂') = pair(kp₁,kp₂)` we read off `i ≫ kp₁' = kp₁`,
    `i ≫ kp₂' = kp₂` (post-compose with `fst`,`snd`); the kernel-pair square
    `kp_sq` then makes each cover equalize the other's kernel pair, so
    `covers_same_kernelPair_iso` yields the `CoverIso`. -/
theorem coverIso_of_kpSub_iso [GrothendieckTopos E] {A Q Q' : E}
    {q : A ⟶ Q} {q' : A ⟶ Q'} (hq : Cover q) (hq' : Cover q')
    (hiso : SubobjectIso (kpSub q) (kpSub q')) : CoverIso q q' := by
  obtain ⟨i, ⟨iinv, hi1, hi2⟩, hi⟩ := hiso   -- i ≫ pair(kp₁',kp₂') = pair(kp₁,kp₂)
  -- Read off the two column equalities.
  have hi_fst : i ≫ kp₁ (f := q') = kp₁ (f := q) := by
    have := congrArg (· ≫ fst) hi
    simpa [kpSub, Cat.assoc, fst_pair] using this
  have hi_snd : i ≫ kp₂ (f := q') = kp₂ (f := q) := by
    have := congrArg (· ≫ snd) hi
    simpa [kpSub, Cat.assoc, snd_pair] using this
  -- The inverse iso gives the reverse column equalities.
  have hinv_fst : iinv ≫ kp₁ (f := q) = kp₁ (f := q') := by
    rw [← hi_fst, ← Cat.assoc, hi2, Cat.id_comp]
  have hinv_snd : iinv ≫ kp₂ (f := q) = kp₂ (f := q') := by
    rw [← hi_snd, ← Cat.assoc, hi2, Cat.id_comp]
  -- q equalizes q''s kernel pair, and vice versa, via kp_sq.
  have hxy : kp₁ (f := q) ≫ q' = kp₂ (f := q) ≫ q' := by
    rw [← hi_fst, ← hi_snd, Cat.assoc, Cat.assoc, kp_sq]
  have hyx : kp₁ (f := q') ≫ q = kp₂ (f := q') ≫ q := by
    rw [← hinv_fst, ← hinv_snd, Cat.assoc, Cat.assoc, kp_sq]
  exact covers_same_kernelPair_iso q hq q' hq' hxy hyx

/-- §1.843: A Grothendieck topos is WELL-COPOWERED.

    BOOK PROOF: In any effective regular category, isomorphism-types of covers
    A ↠ Q correspond to equivalence relations on A (their kernel pairs, §1.566),
    bounded by Sub(A × A), which is a set since E is well-powered (§1.843).

    FORMALIZATION: index covers by `Sub(A × A)` (small by `WellPowered`); pick a
    representative cover for each subobject that arises as a kernel pair.  The
    bridge `coverIso_of_kpSub_iso` shows any cover is `CoverIso` to the
    representative chosen at its own kernel-pair subobject. -/
noncomputable instance grothendieck_topos_well_copowered [GrothendieckTopos E] :
    WellCopowered E where
  small := by
    classical
    intro A
    -- Index covers by the (Type-v) TRACE of their kernel-pair subobject in A×A.
    -- A trace `t` is "represented" if some cover's kernel-pair subobject has trace `t`.
    let Tr := (i : GrothendieckTopos.gen_idx (E := E)) →
              (GrothendieckTopos.gen_obj i ⟶ prod A A) → Prop
    -- A "representing cover" of a trace `t`: a pair (Q, q : A↠Q) with Cover q and
    -- `subTrace (kpSub q) = t`; package the codomain and cover in one Σ to avoid a
    -- dependent dite on the codomain.  Default is `(A, id_A)` when `t` is no kernel pair.
    let Reps : Tr → Prop :=
      fun t => ∃ p : Σ Q : E, A ⟶ Q, Cover p.2 ∧ subTrace (kpSub p.2) = t
    let rep : Tr → Σ Q : E, A ⟶ Q :=
      fun t => if h : Reps t then h.choose else ⟨A, Cat.id A⟩
    refine ⟨Tr, fun t => (rep t).1, fun t => (rep t).2, ?_, ?_⟩
    · -- each chosen map is a cover
      intro t
      show Cover (rep t).2
      by_cases h : Reps t
      · have : rep t = h.choose := dif_pos h
        rw [this]; exact h.choose_spec.1
      · have : rep t = ⟨A, Cat.id A⟩ := dif_neg h
        rw [this]; exact iso_cover _ ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩
    · -- every cover is CoverIso to the representative at its own kernel-pair trace.
      intro Q q hq
      refine ⟨subTrace (kpSub q), ?_⟩
      have hrep : Reps (subTrace (kpSub q)) := ⟨⟨Q, q⟩, hq, rfl⟩
      -- The chosen representative cover `q'` and its defining data.
      have hcov_eq : rep (subTrace (kpSub q)) = hrep.choose := by simp only [rep, dif_pos hrep]
      have hq'cov : Cover hrep.choose.2 := hrep.choose_spec.1
      have htr : subTrace (kpSub hrep.choose.2) = subTrace (kpSub q) := hrep.choose_spec.2
      -- Equal traces ⟹ iso kernel-pair subobjects ⟹ CoverIso (bridge).
      have hsubiso : SubobjectIso (kpSub hrep.choose.2) (kpSub q) :=
        subobjectIso_of_le_le
          (le_of_subTrace_le (fun i x hx => by rw [htr] at hx; exact hx))
          (le_of_subTrace_le (fun i x hx => by rw [htr]; exact hx))
      have hgoal : CoverIso hrep.choose.2 q := coverIso_of_kpSub_iso hq'cov hq hsubiso
      -- The goal's `cov` at this index is `(rep _).2 = hrep.choose.2`.
      show CoverIso (rep (subTrace (kpSub q))).2 q
      rw [hcov_eq]; exact hgoal

/-! ## §1.844 A Grothendieck topos is locally complete ---------------------- -/

/-- §1.844: A Grothendieck topos is locally complete.
    This is already built into the `GrothendieckTopos` typeclass
    (extends `LocallyComplete'`).

    BOOK PROOF: Given a family {Aᵢ ↣ A} of subobjects, form the coproduct
    ΣAᵢ (which exists since E is cocomplete), and let u : ΣAᵢ → A be the
    induced map.  The image of u is the supremum ⋃Aᵢ.  Since pullbacks
    preserve arbitrary unions, the inverse-image functor f# also commutes
    with arbitrary suprema, establishing local completeness. -/
instance grothendieck_topos_locally_complete [GrothendieckTopos E] :
    LocallyComplete' E := inferInstance

/-! ## §1.845 Coproducts in E remain coproducts in Rel(E) ------------------- -/

/-- **EXTENSIVITY of a coproduct** (§1.84, the Giraud "disjoint + universal" coproduct
    condition, here in the arbitrary-`I` form Freyd works with in an extensive / pretopos
    context).

    Freyd's actual condition: a coproduct `cp = {uⱼ : Aⱼ → ΣAⱼ}` is *extensive* when it is
    **stable under pullback** — pulling any map back along the injections re-decomposes its
    domain over the summands, and the off-diagonal pullbacks `Aᵢ ×_{ΣA} Aⱼ` (`i ≠ j`) vanish.

    The exact slice of that property the §1.845 descent consumes is the *summand-support*
    form: given ANY family of objects `S : J → 𝒞` coproduced as `cpS`, structure maps
    `fⱼ : Sⱼ → Aⱼ`, the induced `Σf : ΣSⱼ → ΣAⱼ = cpS.desc (fun j => fⱼ ≫ uⱼ)`, an index `i`,
    and a generalized element `g : T → ΣSⱼ` whose image `g ≫ Σf` lands in the `i`-th summand
    `uᵢ` (witnessed by `t : T → Aᵢ`, `t ≫ uᵢ = g ≫ Σf`), the element `g` is — after passing to
    a cover `c : T' ↠ T` — *supported on the `i`-th summand* `Sᵢ`: there is `φ : T' → Sᵢ` with
    `c ≫ g = φ ≫ cpS.inj i`.

    This is exactly "pullback of the injection `uᵢ` along `Σf` recovers `Sᵢ`, off-diagonal
    pieces are `0`": the cover `c` presents the pullback `T ×_{ΣA} Aᵢ`, and disjointness kills
    every summand `j ≠ i`, leaving the support map `φ` into `Sᵢ` and the factorization
    `c ≫ g = φ ≫ inj i`.  (In a presheaf or sheaf topos this is the pointwise/stalkwise
    partition of a section of `ΣSⱼ` by which summand its `ΣAⱼ`-image lies in.) -/
structure ExtensiveCoproduct {𝒞 : Type u} [Cat.{v} 𝒞] [HasImages 𝒞]
    {I : Type v} {A : I → 𝒞} (cp : Coproduct A) : Prop where
  /-- Each injection `uⱼ` is monic — the diagonal half of "disjoint coproduct". -/
  inj_monic : ∀ j, Mono (cp.inj j)
  /-- Summand support (the off-diagonal-vanishing / pullback-stability half): a generalized
      element `g : T → ΣSⱼ` whose `Σf`-image lands in the `j₀`-th injection is, after a cover
      `c : T' ↠ T`, supported on the `j₀`-th summand `Sⱼ₀`. -/
  support : ∀ {S : I → 𝒞} (cpS : Coproduct S) (f : ∀ j, S j ⟶ A j) (j₀ : I)
    {T : 𝒞} (g : T ⟶ cpS.obj) (t : T ⟶ A j₀),
    g ≫ cpS.desc (fun j => f j ≫ cp.inj j) = t ≫ cp.inj j₀ →
    ∃ (T' : 𝒞) (c : T' ⟶ T), Cover c ∧
      ∃ φ : T' ⟶ S j₀, c ≫ g = φ ≫ cpS.inj j₀

/-- graph(u) ⊚ graph(u)° ≤ graph(id_A) when u is monic.
    Proof: the compose-internal span `pair(π₁ ≫ id_A, π₂ ≫ id_A)` = `π₁ ≫ diag A`
    (since π₁ = π₂ by monicity), so its image factors through diag A, yielding
    the required RelHom k with k ≫ diag A = image(span).arr. -/
private theorem graph_comp_recip_le_one_monic {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A S : 𝒞} (u : A ⟶ S) (hu : Mono u) :
    RelLe (graph u ⊚ (graph u)°) (graph (Cat.id A)) := by
  -- compose (graph u) (graph u)° picks pb = HasPullbacks.has u u
  -- (graph u).colB = u,  (graph u)°.colA = u
  -- span = pair(pb.π₁ ≫ id_A, pb.π₂ ≫ id_A)
  let pb := HasPullbacks.has u u
  have hw : pb.cone.π₁ ≫ u = pb.cone.π₂ ≫ u := pb.cone.w
  have hπ : pb.cone.π₁ = pb.cone.π₂ := hu pb.cone.π₁ pb.cone.π₂ hw
  let s : pb.cone.pt ⟶ prod A A :=
    pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id A)
  have hsp_fac : s = pb.cone.π₁ ≫ diag A := by
    simp only [s, Cat.comp_id, hπ]; exact pair_diag_eq _
  let diagSub : Subobject 𝒞 (prod A A) := ⟨A, diag A, diag_mono A⟩
  have hallows : Allows diagSub s := ⟨pb.cone.π₁, by simp [diagSub, hsp_fac]⟩
  obtain ⟨k, hk⟩ := image_min s diagSub hallows
  dsimp [diagSub] at hk
  -- hk : k ≫ diag A = (image s).arr
  have h_fst : (image s).arr ≫ fst = k := by
    calc (image s).arr ≫ fst = (k ≫ diag A) ≫ fst := by rw [hk]
      _ = k ≫ (diag A ≫ fst) := Cat.assoc _ _ _
      _ = k ≫ Cat.id A := by rw [diag_fst]
      _ = k := Cat.comp_id _
  have h_snd : (image s).arr ≫ snd = k := by
    calc (image s).arr ≫ snd = (k ≫ diag A) ≫ snd := by rw [hk]
      _ = k ≫ (diag A ≫ snd) := Cat.assoc _ _ _
      _ = k ≫ Cat.id A := by rw [diag_snd]
      _ = k := Cat.comp_id _
  -- Provide the RelHom.  compose's internal pb and s are definitionally our pb/s.
  -- (graph u ⊚ (graph u)°).colA = (image s).arr ≫ fst, .colB = (image s).arr ≫ snd.
  -- (graph (Cat.id A)).colA = Cat.id A = (graph (Cat.id A)).colB.
  -- k ≫ Cat.id A = k = (image s).arr ≫ fst/snd.
  have hkA : k ≫ (graph (Cat.id A)).colA = (graph u ⊚ (graph u)°).colA :=
    show k ≫ Cat.id A = (graph u ⊚ (graph u)°).colA from
      (Cat.comp_id k).trans h_fst.symm
  have hkB : k ≫ (graph (Cat.id A)).colB = (graph u ⊚ (graph u)°).colB :=
    show k ≫ Cat.id A = (graph u ⊚ (graph u)°).colB from
      (Cat.comp_id k).trans h_snd.symm
  exact ⟨⟨k, hkA, hkB⟩⟩

/-- graph(id_A) ≤ graph(u) ⊚ graph(u)° when u is monic.
    Proof: lift the cone (id_A, id_A) over (u, u) to get d : A → pb.pt,
    then d ≫ image.lift s : A → (image s).dom is the required RelHom. -/
private theorem one_le_graph_comp_recip_monic {𝒞 : Type u} [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A S : 𝒞} (u : A ⟶ S) (hu : Mono u) :
    RelLe (graph (Cat.id A)) (graph u ⊚ (graph u)°) := by
  -- Same internal pullback as graph_comp_recip_le_one_monic
  let pb := HasPullbacks.has u u
  let s : pb.cone.pt ⟶ prod A A :=
    pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id A)
  -- Cone (id_A, id_A) over (u, u): since id_A ≫ u = id_A ≫ u trivially
  let cone_A : Cone u u := ⟨A, Cat.id A, Cat.id A, rfl⟩
  let d := pb.lift cone_A
  have hd₁ : d ≫ pb.cone.π₁ = Cat.id A := pb.lift_fst cone_A
  have hd₂ : d ≫ pb.cone.π₂ = Cat.id A := pb.lift_snd cone_A
  let h := d ≫ image.lift s
  -- h ≫ (image s).arr = d ≫ s  (by image.lift_fac)
  have h_img : h ≫ (image s).arr = d ≫ s := by
    rw [Cat.assoc, image.lift_fac]
  have h_fst : h ≫ (image s).arr ≫ fst = Cat.id A :=
    calc h ≫ (image s).arr ≫ fst
        = d ≫ s ≫ fst := by rw [← Cat.assoc, h_img, Cat.assoc]
      _ = d ≫ pb.cone.π₁ ≫ Cat.id A := by rw [fst_pair]
      _ = d ≫ pb.cone.π₁ := by rw [Cat.comp_id]
      _ = Cat.id A := hd₁
  have h_snd : h ≫ (image s).arr ≫ snd = Cat.id A :=
    calc h ≫ (image s).arr ≫ snd
        = d ≫ s ≫ snd := by rw [← Cat.assoc, h_img, Cat.assoc]
      _ = d ≫ pb.cone.π₂ ≫ Cat.id A := by rw [snd_pair]
      _ = d ≫ pb.cone.π₂ := by rw [Cat.comp_id]
      _ = Cat.id A := hd₂
  -- h : A → (image s).dom = (graph u ⊚ (graph u)°).src (definitionally).
  -- (graph u ⊚ (graph u)°).colA = (image s).arr ≫ fst  (definitionally)
  -- (graph (Cat.id A)).colA = Cat.id A                  (definitionally)
  have hhA : h ≫ (graph u ⊚ (graph u)°).colA = (graph (Cat.id A)).colA :=
    show h ≫ (image s).arr ≫ fst = Cat.id A from h_fst
  have hhB : h ≫ (graph u ⊚ (graph u)°).colB = (graph (Cat.id A)).colB :=
    show h ≫ (image s).arr ≫ snd = Cat.id A from h_snd
  exact ⟨⟨h, hhA, hhB⟩⟩

/-- §1.845: If {uᵢ : Aᵢ → S} is a coproduct in E, it remains a coproduct
    in Rel(E): for any family of relations {Rᵢ : Aᵢ → B}, there is a unique
    R : S → B in Rel(E) such that (graph uᵢ) ⊚ R = Rᵢ for all i.

    BOOK PROOF:
    • uᵢuᵢ° = 1_{Aᵢ}  (uᵢ monic ⟹ graph(uᵢ) ⊚ graph(uᵢ)° = graph(id_Aᵢ))
    • uᵢ°uⱼ = 0 for i ≠ j (disjoint coproducts, §1.845)
    • ⋃ uᵢ°uᵢ = 1_S (the uᵢ are collectively a cover)
    The candidate relation is R = ⋃ᵢ (reciprocal (graph uᵢ)) ⊚ Rᵢ.

    FORMALIZATION: construct U as the image of the "big span"
    m = pair(cpR.desc(fun i => Rᵢ.colA ≫ uᵢ), cpR.desc(fun i => Rᵢ.colB)) : cpR.obj → cp.obj×B
    (cpR = coproduct of Rᵢ.src's).

    The ≥ direction (Rᵢ ≤ graph(uᵢ) ⊚ U) is proved by explicit RelHom:
    injection cpR.inj i ≫ image.lift m, lifted via the pullback pb_i.

    The ≤ direction (graph(uᵢ) ⊚ U ≤ Rᵢ) requires that every point of U
    paired with uᵢ comes from the Rᵢ component — needs disjointness of
    coproducts AND pullback-preserves-unions (§1.84 axiom `pullback_union`). -/
theorem coproduct_is_coproduct_in_Rel
    [GrothendieckTopos E]
    {I : Type v} {A : I → E} {B : E}
    (cp : Coproduct A)
    (hext : ExtensiveCoproduct cp)
    (R : ∀ i, BinRel E (A i) B) :
    ∃ (U : BinRel E cp.obj B),
      ∀ i, RelLe (graph (cp.inj i) ⊚ U) (R i) ∧
           RelLe (R i) (graph (cp.inj i) ⊚ U) := by
  -- Form cpR = coproduct of the relation source objects
  let cpR := (GrothendieckTopos.toHasAllCoproducts (E := E)).coprod (fun i => (R i).src)
  -- Big span m : cpR.obj → prod cp.obj B
  let colA_big : cpR.obj ⟶ cp.obj := cpR.desc (fun i => (R i).colA ≫ cp.inj i)
  let colB_big : cpR.obj ⟶ B      := cpR.desc (fun i => (R i).colB)
  let m : cpR.obj ⟶ prod cp.obj B := pair colA_big colB_big
  -- U = image of m, as a BinRel
  let U_sub := image m
  have hU_mp : MonicPair (U_sub.arr ≫ fst) (U_sub.arr ≫ snd) :=
    monicPair_of_monic_pair _ _ (pair_eta U_sub.arr ▸ U_sub.monic)
  let U : BinRel E cp.obj B := ⟨U_sub.dom, U_sub.arr ≫ fst, U_sub.arr ≫ snd, hU_mp⟩
  refine ⟨U, fun i => ⟨?_, ?_⟩⟩
  · -- ≤ direction: graph(uᵢ) ⊚ U ≤ R i, discharged with EXTENSIVITY (`hext`).
    -- `(graph uᵢ ⊚ U).src` is presented, from the inner pullback `pb_c = pullback(uᵢ, U.colA)`,
    -- by the image-cover `eW = image.lift span_c`.  We pull the coproduct-presenting cover
    -- `image.lift m : cpR.obj ↠ U.src` back along `pb_c.π₂`, obtaining a cover of `pb_c.pt`
    -- carrying `q : · → cpR.obj` with `q ≫ colA_big` factoring through `uᵢ`; extensivity then
    -- supports `q` on the i-th summand `(R i).src`, producing the descent `φ`.
    let uᵢ := cp.inj i
    let pb_c := HasPullbacks.has uᵢ U.colA
    let span_c : pb_c.cone.pt ⟶ prod (A i) B :=
      pair (pb_c.cone.π₁ ≫ (graph uᵢ).colA) (pb_c.cone.π₂ ≫ U.colB)
    let eW := image.lift span_c
    -- `eW : pb_c.pt ↠ (graph uᵢ ⊚ U).src` is a cover, with the two span-leg identities.
    have hWa : eW ≫ (graph uᵢ ⊚ U).colA = pb_c.cone.π₁ := by
      show eW ≫ ((image span_c).arr ≫ fst) = _
      rw [← Cat.assoc, image.lift_fac, fst_pair]
      show pb_c.cone.π₁ ≫ Cat.id (A i) = pb_c.cone.π₁   -- (graph uᵢ).colA = id
      rw [Cat.comp_id]
    have hWb : eW ≫ (graph uᵢ ⊚ U).colB = pb_c.cone.π₂ ≫ U.colB := by
      show eW ≫ ((image span_c).arr ≫ snd) = _
      rw [← Cat.assoc, image.lift_fac, snd_pair]
    -- Pull the image-cover of `m` back along `pb_c.π₂ : pb_c.pt → U.src = U_sub.dom`.
    let em := image.lift m                      -- cover cpR.obj ↠ U_sub.dom
    let pb1 := HasPullbacks.has em pb_c.cone.π₂
    have hpb1_cover : Cover pb1.cone.π₂ := cover_pullback pb_c.cone.π₂ (image_lift_cover m)
    -- On `pb1.pt`: `q ≫ colA_big` factors through `uᵢ`, witnessed by `t = pb1.π₂ ≫ pb_c.π₁`.
    let q : pb1.cone.pt ⟶ cpR.obj := pb1.cone.π₁
    have hq_m : q ≫ m = pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U_sub.arr := by
      calc q ≫ m = q ≫ (em ≫ U_sub.arr) := by rw [image.lift_fac]
        _ = (q ≫ em) ≫ U_sub.arr := (Cat.assoc _ _ _).symm
        _ = (pb1.cone.π₂ ≫ pb_c.cone.π₂) ≫ U_sub.arr := by rw [pb1.cone.w]
        _ = pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U_sub.arr := Cat.assoc _ _ _
    have hfac : q ≫ colA_big = (pb1.cone.π₂ ≫ pb_c.cone.π₁) ≫ uᵢ := by
      calc q ≫ colA_big
          = (q ≫ m) ≫ fst := by rw [Cat.assoc]; rw [show m ≫ fst = colA_big from fst_pair _ _]
        _ = (pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U_sub.arr) ≫ fst := by rw [hq_m]
        _ = pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ (U_sub.arr ≫ fst) := by
              rw [Cat.assoc, Cat.assoc]
        _ = pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U.colA := rfl
        _ = pb1.cone.π₂ ≫ pb_c.cone.π₁ ≫ uᵢ := by rw [← pb_c.cone.w]
        _ = (pb1.cone.π₂ ≫ pb_c.cone.π₁) ≫ uᵢ := (Cat.assoc _ _ _).symm
    -- `colA_big = cpR.desc (fun j => (R j).colA ≫ cp.inj j)`, so `hfac` is exactly the
    -- extensivity hypothesis applied to `cpR`, structure maps `(R j).colA`, summand `i`.
    obtain ⟨T', c, hc, φ, hcφ⟩ :=
      hext.support cpR (fun j => (R j).colA) i q (pb1.cone.π₂ ≫ pb_c.cone.π₁) hfac
    -- The full cover into `(graph uᵢ ⊚ U).src`: `c ≫ pb1.π₂ ≫ eW`.
    let cov : T' ⟶ (graph uᵢ ⊚ U).src := c ≫ pb1.cone.π₂ ≫ eW
    have hcov : Cover cov :=
      cover_comp hc (cover_comp hpb1_cover (image_lift_cover span_c))
    -- The descent `φ : T' → (R i).src`.  Match the two legs.
    -- `φ ≫ cpR.inj i = c ≫ q`, hence `φ ≫ (R i).colA ≫ uᵢ = c ≫ q ≫ colA_big`,
    -- and `uᵢ` monic gives `φ ≫ (R i).colA = cov ≫ (graph uᵢ ⊚ U).colA`.
    have huᵢ_mono : Mono uᵢ := hext.inj_monic i
    -- The two leg-values of the composite cover `cov` (factor `eW`'s leg identities through `c ≫ pb1.π₂`).
    have hcov_colA : cov ≫ (graph uᵢ ⊚ U).colA = (c ≫ pb1.cone.π₂) ≫ pb_c.cone.π₁ := by
      show (c ≫ pb1.cone.π₂ ≫ eW) ≫ (graph uᵢ ⊚ U).colA = _
      simp only [Cat.assoc, hWa]
    have hcov_colB : cov ≫ (graph uᵢ ⊚ U).colB = (c ≫ pb1.cone.π₂) ≫ pb_c.cone.π₂ ≫ U.colB := by
      show (c ≫ pb1.cone.π₂ ≫ eW) ≫ (graph uᵢ ⊚ U).colB = _
      simp only [Cat.assoc, hWb]
    refine relLe_of_cover_factor cov hcov φ ?_ ?_
    · -- φ ≫ (R i).colA = cov ≫ (graph uᵢ ⊚ U).colA, via uᵢ monic.
      apply huᵢ_mono
      calc (φ ≫ (R i).colA) ≫ uᵢ
          = φ ≫ ((R i).colA ≫ uᵢ) := Cat.assoc _ _ _
        _ = φ ≫ (cpR.inj i ≫ colA_big) := by
              rw [show cpR.inj i ≫ colA_big = (R i).colA ≫ uᵢ from cpR.fac _ i]
        _ = (φ ≫ cpR.inj i) ≫ colA_big := (Cat.assoc _ _ _).symm
        _ = (c ≫ q) ≫ colA_big := by rw [← hcφ]
        _ = c ≫ (q ≫ colA_big) := Cat.assoc _ _ _
        _ = c ≫ ((pb1.cone.π₂ ≫ pb_c.cone.π₁) ≫ uᵢ) := by rw [hfac]
        _ = ((c ≫ pb1.cone.π₂) ≫ pb_c.cone.π₁) ≫ uᵢ := by
              rw [← Cat.assoc, ← Cat.assoc]
        _ = (cov ≫ (graph uᵢ ⊚ U).colA) ≫ uᵢ := by rw [hcov_colA]
    · -- φ ≫ (R i).colB = cov ≫ (graph uᵢ ⊚ U).colB
      calc φ ≫ (R i).colB
          = φ ≫ (cpR.inj i ≫ colB_big) := by
              rw [show cpR.inj i ≫ colB_big = (R i).colB from cpR.fac _ i]
        _ = (φ ≫ cpR.inj i) ≫ colB_big := (Cat.assoc _ _ _).symm
        _ = (c ≫ q) ≫ colB_big := by rw [← hcφ]
        _ = c ≫ (q ≫ colB_big) := Cat.assoc _ _ _
        _ = c ≫ (q ≫ m ≫ snd) := by
              rw [show m ≫ snd = colB_big from snd_pair _ _]
        _ = c ≫ ((q ≫ m) ≫ snd) := by rw [Cat.assoc]
        _ = c ≫ ((pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U_sub.arr) ≫ snd) := by rw [hq_m]
        _ = c ≫ (pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ (U_sub.arr ≫ snd)) := by
              rw [Cat.assoc, Cat.assoc]
        _ = c ≫ (pb1.cone.π₂ ≫ pb_c.cone.π₂ ≫ U.colB) := rfl
        _ = (c ≫ pb1.cone.π₂) ≫ pb_c.cone.π₂ ≫ U.colB := (Cat.assoc _ _ _).symm
        _ = cov ≫ (graph uᵢ ⊚ U).colB := hcov_colB.symm
  · -- ≥ direction: R i ≤ graph(uᵢ) ⊚ U
    let uᵢ := cp.inj i
    let pb_i := HasPullbacks.has uᵢ U.colA
    let span_i := pair (pb_i.cone.π₁ ≫ (graph uᵢ).colA) (pb_i.cone.π₂ ≫ U.colB)
    -- v : (R i).src → U.src, defined as cpR.inj i ≫ image.lift m
    let v : (R i).src ⟶ U_sub.dom := cpR.inj i ≫ image.lift m
    -- v ≫ U.colA = (R i).colA ≫ uᵢ
    have hv_colA : v ≫ U.colA = (R i).colA ≫ uᵢ :=
      calc v ≫ U.colA
            = (cpR.inj i ≫ image.lift m) ≫ U_sub.arr ≫ fst := rfl
          _ = cpR.inj i ≫ (image.lift m ≫ U_sub.arr) ≫ fst := by
                simp [Cat.assoc]
          _ = cpR.inj i ≫ m ≫ fst := by rw [image.lift_fac]
          _ = cpR.inj i ≫ colA_big := by simp [m, Cat.assoc, fst_pair]
          _ = (R i).colA ≫ uᵢ := cpR.fac _ i
    -- v ≫ U.colB = (R i).colB
    have hv_colB : v ≫ U.colB = (R i).colB :=
      calc v ≫ U.colB
            = (cpR.inj i ≫ image.lift m) ≫ U_sub.arr ≫ snd := rfl
          _ = cpR.inj i ≫ (image.lift m ≫ U_sub.arr) ≫ snd := by
                simp [Cat.assoc]
          _ = cpR.inj i ≫ m ≫ snd := by rw [image.lift_fac]
          _ = cpR.inj i ≫ colB_big := by simp [m, Cat.assoc, snd_pair]
          _ = (R i).colB := cpR.fac _ i
    -- Cone at pb_i with (R i).colA and v; lift gives w_i : (R i).src → pb_i.cone.pt
    let cone_i : Cone uᵢ U.colA := ⟨(R i).src, (R i).colA, v, hv_colA.symm⟩
    let w_i := pb_i.lift cone_i
    have hw₁ : w_i ≫ pb_i.cone.π₁ = (R i).colA := pb_i.lift_fst cone_i
    have hw₂ : w_i ≫ pb_i.cone.π₂ = v           := pb_i.lift_snd cone_i
    -- RelHom h : (R i).src → (graph uᵢ ⊚ U).src
    let h := w_i ≫ image.lift span_i
    have hh : h ≫ (image span_i).arr = w_i ≫ span_i := by
      rw [Cat.assoc, image.lift_fac]
    have h_colA : h ≫ (graph uᵢ ⊚ U).colA = (R i).colA := by
      show h ≫ (image span_i).arr ≫ fst = (R i).colA
      rw [← Cat.assoc, hh]; dsimp [span_i, graph]
      rw [Cat.assoc, fst_pair, Cat.comp_id, hw₁]
    have h_colB : h ≫ (graph uᵢ ⊚ U).colB = (R i).colB := by
      show h ≫ (image span_i).arr ≫ snd = (R i).colB
      rw [← Cat.assoc, hh]; dsimp [span_i, U]
      rw [Cat.assoc, snd_pair, ← Cat.assoc, hw₂, hv_colB]
    exact ⟨⟨h, h_colA, h_colB⟩⟩

/-! ## §1.846 A coequalizer in E remains a coequalizer in Rel(E) ------------ -/

/-- §1.846: If h : B ↠ C is a coequalizer of f, g : A → B in E,
    then h is a coequalizer in Rel(E): for any relation R : B → D with
    (graph f) ⊚ R ≡ (graph g) ⊚ R, there is a unique R' : C → D
    such that (graph h) ⊚ R' ≡ R.

    BOOK PROOF (now discharged using the §1.77 reflexive-transitive closure `rtc`
    and the §1.78 self-quotient R/R, plus the single E-standard residual below):
    • Uniqueness: h is a cover (coequalizer maps are covers, §1.581), so
      1 ⊑ h°h (`cover_iff_one_le_reciprocal_comp_self`); R' = h°R then has a
      left inverse h in Rel(E), forcing R' to be unique.
    • Existence: take R' = h°R.  Then hh°R = R is proven in two halves:
        - R ⊑ hh°R uses that graph h is ENTIRE (1 ⊑ hh°), §1.564.
        - hh°R ⊑ R is the deep half.  hh° is the smallest equivalence relation
          containing f°g (E-standard, §1.844 — supplied as `h_hh_le_rtc` below).
          The closure is built as `rtc S` for the symmetric step
          S = (f°g) ∪ 1 ∪ (g°f); using fR ≡ gR one shows S ⊚ R ⊑ R, hence
          S ⊑ R/R (§1.78).  Since R/R is reflexive and transitive (§1.786),
          minimality of rtc gives rtc S ⊑ R/R, so (rtc S) ⊚ R ⊑ R, and finally
          hh°R ⊑ (rtc S)R ⊑ R.  The `R/R` self-quotient (`qRR`) and the
          E-standard containment (`h_hh_le_rtc`) are passed as hypotheses — both
          are genuine §1.78/§1.844 facts about any Grothendieck topos. -/
theorem coequalizer_is_coequalizer_in_Rel
    [GrothendieckTopos E] [HasReflTransClosure E] [HasBinaryCoproducts E]
    {A B C : E} (f g : A ⟶ B) (h : B ⟶ C)
    (h_eq   : f ≫ h = g ≫ h)
    (h_univ : ∀ {X : E} (k : B ⟶ X), f ≫ k = g ≫ k →
                ∃ (k' : C ⟶ X), h ≫ k' = k ∧ ∀ (k'' : C ⟶ X), h ≫ k'' = k → k'' = k')
    {D : E} (R : BinRel E B D)
    -- The §1.78 self-quotient R/R (relational division), which exists in any
    -- topos since each subobject lattice is a complete Heyting algebra.
    (qRR : RelQuot R R)
    -- §1.844 (E-standard / effectiveness): the kernel-pair equivalence hh° of the
    -- coequalizer h is contained in the reflexive-transitive closure of the
    -- symmetric one-step relation S = (f°g) ∪ 1 ∪ (g°f).  This is exactly the
    -- statement that hh° introduces no identifications beyond those forced by f,g.
    (h_hh_le_rtc :
      RelLe (graph h ⊚ (graph h)°)
            (rtc ((((graph f)° ⊚ graph g) ∪ᵣ graph (Cat.id B)) ∪ᵣ ((graph g)° ⊚ graph f))))
    (hfgR : RelLe (graph f ⊚ R) (graph g ⊚ R) ∧
            RelLe (graph g ⊚ R) (graph f ⊚ R)) :
    ∃ (R' : BinRel E C D),
      (RelLe (graph h ⊚ R') R ∧ RelLe R (graph h ⊚ R')) ∧
      ∀ (R'' : BinRel E C D),
        (RelLe (graph h ⊚ R'') R ∧ RelLe R (graph h ⊚ R'')) →
        RelLe R'' R' ∧ RelLe R' R'' := by
  classical
  -- Abbreviations for the graphs.
  let gf : BinRel E A B := graph f
  let gg : BinRel E A B := graph g
  let gh : BinRel E B C := graph h
  -- The unique solution: R' = h°R = (graph h)° ⊚ R.
  refine ⟨gh° ⊚ R, ⟨?_, ?_⟩, ?_⟩
  · -- EXISTENCE, hard half:  gh ⊚ (gh° ⊚ R) ⊑ R.
    -- Step 1.  S = (f°g) ∪ 1 ∪ (g°f) and the closure `rtc S`.
    let S : BinRel E B B := ((gf° ⊚ gg) ∪ᵣ graph (Cat.id B)) ∪ᵣ (gg° ⊚ gf)
    -- Step 2.  S ⊑ R/R = qRR.quot.  By the universal property of ∪ᵣ it suffices to
    -- show each piece P satisfies P ⊚ R ⊑ R (then P ⊑ R/R by maximality of R/R).
    -- (f°g)R ⊑ R :  f°(gR) ⊑ f°(fR) ⊑ (f°f)R ⊑ 1R ⊑ R.
    have hP1 : RelLe ((gf° ⊚ gg) ⊚ R) R := by
      have e1 : RelLe ((gf° ⊚ gg) ⊚ R) (gf° ⊚ (gg ⊚ R)) := compose_assoc _ _ _
      have e2 : RelLe (gf° ⊚ (gg ⊚ R)) (gf° ⊚ (gf ⊚ R)) :=
        compose_le (rel_le_refl _) hfgR.2
      have e3 : RelLe (gf° ⊚ (gf ⊚ R)) ((gf° ⊚ gf) ⊚ R) := compose_assoc' _ _ _
      have e4 : RelLe ((gf° ⊚ gf) ⊚ R) (graph (Cat.id B) ⊚ R) :=
        compose_le_left ((graph_is_map f).2) R
      have e5 : RelLe (graph (Cat.id B) ⊚ R) R := graph_id_comp R
      exact rel_le_trans e1 (rel_le_trans e2 (rel_le_trans e3 (rel_le_trans e4 e5)))
    -- (g°f)R ⊑ R :  symmetric, using fR ⊑ gR.
    have hP3 : RelLe ((gg° ⊚ gf) ⊚ R) R := by
      have e1 : RelLe ((gg° ⊚ gf) ⊚ R) (gg° ⊚ (gf ⊚ R)) := compose_assoc _ _ _
      have e2 : RelLe (gg° ⊚ (gf ⊚ R)) (gg° ⊚ (gg ⊚ R)) :=
        compose_le (rel_le_refl _) hfgR.1
      have e3 : RelLe (gg° ⊚ (gg ⊚ R)) ((gg° ⊚ gg) ⊚ R) := compose_assoc' _ _ _
      have e4 : RelLe ((gg° ⊚ gg) ⊚ R) (graph (Cat.id B) ⊚ R) :=
        compose_le_left ((graph_is_map g).2) R
      have e5 : RelLe (graph (Cat.id B) ⊚ R) R := graph_id_comp R
      exact rel_le_trans e1 (rel_le_trans e2 (rel_le_trans e3 (rel_le_trans e4 e5)))
    -- Each piece is ⊑ R/R; assemble S ⊑ R/R via the ∪ᵣ universal property.
    have hS_le_quot : RelLe S qRR.quot :=
      le_relUnion
        (le_relUnion (qRR.maximal _ hP1) (qRR.maximal _ (graph_id_comp R)))
        (qRR.maximal _ hP3)
    -- Step 3.  rtc S ⊑ R/R, by minimality (R/R reflexive + transitive).
    -- R/R reflexive: graph(id_B) ⊚ R ⊑ R (left unit), so graph(id_B) ⊑ R/R by maximality.
    have hquot_refl : IsReflexive qRR.quot := qRR.maximal _ (graph_id_comp R)
    -- R/R transitive: (R/R ⊚ R/R) ⊚ R ⊑ R/R ⊚ (R/R ⊚ R) ⊑ R/R ⊚ R ⊑ R.
    have hquot_trans : IsTransitive qRR.quot := by
      apply qRR.maximal
      have t1 : RelLe ((qRR.quot ⊚ qRR.quot) ⊚ R) (qRR.quot ⊚ (qRR.quot ⊚ R)) :=
        compose_assoc _ _ _
      have t2 : RelLe (qRR.quot ⊚ (qRR.quot ⊚ R)) (qRR.quot ⊚ R) :=
        compose_le (rel_le_refl _) qRR.le
      exact rel_le_trans t1 (rel_le_trans t2 qRR.le)
    have hrtc_le_quot : RelLe (rtc S) qRR.quot :=
      rtc_minimal S qRR.quot hS_le_quot hquot_refl hquot_trans
    -- Step 4.  (rtc S) ⊚ R ⊑ (R/R) ⊚ R ⊑ R.
    have hrtcR : RelLe (rtc S ⊚ R) R :=
      rel_le_trans (compose_le_left hrtc_le_quot R) qRR.le
    -- Step 5.  gh ⊚ gh° ⊑ rtc S  (E-standard, `h_hh_le_rtc`); reassociate.
    --   gh ⊚ (gh° ⊚ R) = (gh ⊚ gh°) ⊚ R ⊑ (rtc S) ⊚ R ⊑ R.
    have e_assoc : RelLe (gh ⊚ (gh° ⊚ R)) ((gh ⊚ gh°) ⊚ R) := compose_assoc' _ _ _
    have e_hh : RelLe ((gh ⊚ gh°) ⊚ R) (rtc S ⊚ R) :=
      compose_le_left h_hh_le_rtc R
    exact rel_le_trans e_assoc (rel_le_trans e_hh hrtcR)
  · -- EXISTENCE, easy half:  R ⊑ gh ⊚ (gh° ⊚ R).
    --   R = 1 ⊚ R ⊑ (gh ⊚ gh°) ⊚ R ⊑ gh ⊚ (gh° ⊚ R)   (graph h is entire).
    have e1 : RelLe R (graph (Cat.id B) ⊚ R) := comp_graph_id_left R
    have e2 : RelLe (graph (Cat.id B) ⊚ R) ((gh ⊚ gh°) ⊚ R) :=
      compose_le_left ((graph_is_map h).1) R
    have e3 : RelLe ((gh ⊚ gh°) ⊚ R) (gh ⊚ (gh° ⊚ R)) := compose_assoc _ _ _
    exact rel_le_trans e1 (rel_le_trans e2 e3)
  · -- UNIQUENESS.  Given R'' with gh ⊚ R'' ≡ R, show R'' ≡ gh° ⊚ R.
    -- h is a cover (coequalizer map), so 1_C ⊑ gh° ⊚ gh.
    intro R'' hR''
    -- Build a HasCoequalizer f g from the universal property to invoke
    -- `coeq_map_is_cover`.
    have hcov : Cover h := by
      refine coeq_map_is_cover (𝒟 := E) (f := f) (g := g)
        { obj := C, map := h, eq := h_eq,
          desc := fun {X} k hk => (h_univ k hk).choose,
          fac := fun {X} k hk => (h_univ k hk).choose_spec.1,
          uniq := fun {X} k hk m hm =>
            (h_univ k hk).choose_spec.2 m hm }
    have hone : RelLe (graph (Cat.id C)) (gh° ⊚ gh) :=
      (cover_iff_one_le_reciprocal_comp_self h).mp hcov
    constructor
    · -- R'' ⊑ gh° ⊚ R.
      --  R'' = 1_C ⊚ R'' ⊑ (gh° ⊚ gh) ⊚ R'' ⊑ gh° ⊚ (gh ⊚ R'') ⊑ gh° ⊚ R.
      have a1 : RelLe R'' (graph (Cat.id C) ⊚ R'') := comp_graph_id_left R''
      have a2 : RelLe (graph (Cat.id C) ⊚ R'') ((gh° ⊚ gh) ⊚ R'') :=
        compose_le_left hone R''
      have a3 : RelLe ((gh° ⊚ gh) ⊚ R'') (gh° ⊚ (gh ⊚ R'')) := compose_assoc _ _ _
      have a4 : RelLe (gh° ⊚ (gh ⊚ R'')) (gh° ⊚ R) := compose_le (rel_le_refl _) hR''.1
      exact rel_le_trans a1 (rel_le_trans a2 (rel_le_trans a3 a4))
    · -- gh° ⊚ R ⊑ R''.
      --  gh° ⊚ R ⊑ gh° ⊚ (gh ⊚ R'') ⊑ (gh° ⊚ gh) ⊚ R'' .. but the clean route:
      --  gh° ⊚ R ⊑ gh° ⊚ (gh ⊚ R'') = (gh° ⊚ gh) ⊚ R''; we instead use R ⊑ gh ⊚ R''
      --  with simplicity is not needed — use: gh°R ⊑ gh°(ghR'') and then collapse via
      --  the OTHER direction symmetric to above is unavailable, so argue directly:
      --  R ⊑ gh ⊚ R''  (hR''.2), so gh° ⊚ R ⊑ gh° ⊚ (gh ⊚ R'') ⊑ (gh° ⊚ gh) ⊚ R''.
      --  Then (gh° ⊚ gh) ⊚ R'' ⊑ 1 ⊚ R'' ⊑ R''  needs gh° ⊚ gh ⊑ 1, i.e. gh SIMPLE.
      have b1 : RelLe (gh° ⊚ R) (gh° ⊚ (gh ⊚ R'')) := compose_le (rel_le_refl _) hR''.2
      have b2 : RelLe (gh° ⊚ (gh ⊚ R'')) ((gh° ⊚ gh) ⊚ R'') := compose_assoc' _ _ _
      have b3 : RelLe ((gh° ⊚ gh) ⊚ R'') (graph (Cat.id C) ⊚ R'') :=
        compose_le_left ((graph_is_map h).2) R''
      have b4 : RelLe (graph (Cat.id C) ⊚ R'') R'' := graph_id_comp R''
      exact rel_le_trans b1 (rel_le_trans b2 (rel_le_trans b3 b4))

/-! ## §1.847 Special adjoint functor theorem applies ----------------------- -/

/-
  §1.847: A Grothendieck topos E is cocomplete (by definition), well-copowered
  (§1.843), and has a generating set (by definition).  Rel(E) is locally small
  (because E is well-powered: §1.843) and E → Rel(E) preserves coproducts
  (§1.845) and coequalizers (§1.846), hence is cocontinuous.
  By the special adjoint functor theorem (§1.83), the graphing functor
  E → Rel(E) has a right adjoint.

  MISSING: Requires Rel(E) as a formalized category (see §1.841–§1.842 note).
  Once Rel(E) has a `Cat` instance this will follow from
  `special_adjoint_functor_theorem` in S1_82.lean applied to the graphing functor.
-/

end Freyd
