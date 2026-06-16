/-
  Freyd & Scedrov, *Categories and Allegories* §1.63–§1.66
  Slice pre-logos, Boolean pre-logoi, Pre-topoi, Amalgamation.

  §1.63  If A is a (positive) pre-logos, so is A/B (§1.63).
  §1.631 Complemented subobject: A₁∩A₂=0, A₁∪A₂=A.
  §1.64  Boolean pre-logos: subobject lattices are Boolean algebras.
  §1.644 Ultra-product / ultra-power functors (§1.644).
  §1.645 𝒦𝓮𝓇(T) = values killed by representation T.
  §1.65  Pre-topos = effective positive pre-logos.
  §1.651 Amalgamation Lemma: pushout of two monics exists.
  §1.652 In a pre-topos: covers = epics, monics = cocovers.
  §1.66  (if applicable)
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_51
import Fredy.S1_52
import Fredy.S1_56
import Fredy.S1_58
import Fredy.S1_59
import Fredy.S1_60
import Fredy.S1_57
import Fredy.S1_62


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631 Complemented subobject

  A₁ ⊆ A is COMPLEMENTED if ∃ A₂ ⊆ A with A₁∩A₂=0, A₁∪A₂=A. -/

-- NOTE: `[PreLogos 𝒞]` is attached locally to each declaration that needs it rather
-- than as a module-level `variable`.  A module-level `[PreLogos 𝒞]` would form a
-- diamond with `DisjointBinaryCoproduct.toPreLogos` (§1.621 block below), since that
-- class also supplies a `PreLogos` instance for the same `𝒞`.

/-- A₁ is COMPLEMENTED if there's A₂ with A₁∩A₂=0 and A₁∪A₂=A.
    (Placeholder: intersection not yet defined.) -/
def IsComplemented [PreLogos 𝒞] {A : 𝒞} (A₁ : Subobject 𝒞 A) : Prop :=
  ∃ (A₂ : Subobject 𝒞 A),
    (∀ (S : Subobject 𝒞 A), Subobject.le S A₁ → Subobject.le S A₂ → False)
    -- A₁∩A₂ is minimal (no non-trivial common subobject)
    ∧ Subobject.le (Subobject.entire A) (HasSubobjectUnions.union A₁ A₂)
    -- A₁∪A₂ = A (entire)

/-! ## §1.64 Boolean pre-logos

  A BOOLEAN PRE-LOGOS is a pre-logos where every subobject lattice
  is Boolean (every subobject has a complement). -/

class BooleanPreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends PreLogos 𝒞 where
  hasComplement : ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplemented S

/-! ## §1.645 𝒦𝓮𝓇(T) — values killed by a representation

  For T: A → B a representation of boolean pre-logoi, Kℯℛ(T) is
  the set of subterminators U ⊆ 1 such that T(U) = 0. -/

/-- **§1.645** `Kℯℛ(T) = { U ⊆ 1 | T(U) = 0 }` — the set of subterminators whose
    value under the representation `T` is the NULL (zero) object.

    Book text (§1.645): "we define `𝒦ℯℛ(T)` as the set of values killed by `T`:
    `𝒦ℯℛ(T) = { U ⊆ 1 | T(U) = 0 }`".  Here `0` is the bottom of the target's
    subobject lattice (`PreLogos.bottom`, the empty join / null object) — the
    OPPOSITE extreme from the terminator `1`.

    INTEGRITY FIX: the previous definition tested `Isomorphic (T U.dom) one`
    (the terminator, i.e. `T(U) = 1`), which is exactly backwards — it would make
    `Kℯℛ(T)` the values sent to the TOP rather than killed.  Corrected to test
    against the zero object `(PreLogos.bottom _).dom`. -/
def killedValues {𝒟 : Type u} [Cat.{v} 𝒟] [PreLogos 𝒞] [PreLogos 𝒟]
    (T : 𝒞 → 𝒟) [Functor T] : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T U.dom) (PreLogos.bottom (T U.dom)).dom

/-! ## §1.646 Faithful representability of small special categories

  Every small special Cartesian category is faithfully representable in Set.
  Every small special positive pre-logos is faithfully representable in Set.
  PROOF (§1.646): Combine §1.472/§1.637 (finite separation) with a diagonal
  ultra-filter argument: I = finite sets of proper subobjects, choose T_S for
  each S, form T : A → Set^I, extend to an ultra-filter F ⊇ principal coideals.
  T^F is faithful.  (Requires ultra-filter machinery; sorry.) -/

-- §1.646 (note): Every small special Cartesian category embeds faithfully in Set.
-- Proof combines §1.472/§1.637 with an ultra-filter diagonal argument.
-- Requires ultra-filter infrastructure outside this repo's scope.

-- §1.647 (note): A boolean pre-logos is special iff two-valued.
-- Proof: complement of (A₁×B₂)∪(B₁×A₂) in B₁×B₂ is A₁°×A₂°.
-- Requires complement intersection/union infrastructure not yet formalized.

-- §1.648 (note): Ultra-power T = Set^I → Set^I/F is bicartesian iff F is
-- a complete measure (meets every countable partition of I).
-- Requires ultra-filter/ultra-product infrastructure outside this repo.

/-! ## §1.65 Pre-topos

  A PRE-TOPOS is an effective positive pre-logos:
  effective regular + positive pre-logos. -/

class PreTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    EffectiveRegular 𝒞, PositivePreLogos 𝒞

/-! ## §1.621/§1.623 Disjointness of positive coproducts

  Freyd's positivity is NOT the bare case-universal-property of `HasBinaryCoproducts`.
  §1.626 is explicit: "Coproducts can exist without positivity.  Any distributive
  lattice, viewed as a category, is a pre-logos with coproducts.  It is positive iff
  it is degenerate."  In a lattice the join `A ∨ B` is a coproduct but the injections
  `A ↣ A∨B`, `B ↣ A∨B` are not jointly monic and `A ∧ B ≠ 0`.

  In a POSITIVE pre-logos the coproduct `A + B` is, by §1.623, *constructed* as the
  ambient object `C` for which `A, B ⊆ C` are subobjects with `A ∩ B = 0` and
  `A ∪ B = C` — and §1.621 says exactly such a disjoint complemented union IS a
  coproduct.  So disjointness is part of the DATA of a positive coproduct, faithfully
  recorded below as Freyd's §1.621 conditions on the injections of `HasBinaryCoproducts`:

  * `inl`, `inr` are monic (they are subobject inclusions);
  * `inl ∩ inr ≤ 0`  (the §1.621 disjointness `A₁ ∩ A₂ = 0`);
  * `inl ∪ inr = the whole coproduct`  (the §1.621 union `A₁ ∪ A₂ = A`).

  This matches the binary form of the `DisjointCoproduct` structure that S1_84 uses
  for arbitrary-indexed coproducts (uᵢ monic, uᵢ°uⱼ = 0, ⋃uᵢ°uᵢ = 1).
  INTENDED MIGRATION: once S1_62 is free to edit, fold `DisjointBinaryCoproduct`'s
  three fields into `PositivePreLogos` itself (the natural home of §1.623). -/

/-- The left injection `inl : A ⟶ A+B` packaged as a subobject of `A+B`, given that
    it is monic.  Used to phrase §1.621 disjointness `inl ∩ inr ≤ 0` via the existing
    `Subobject.inter`. -/
def inlSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Mono (HasBinaryCoproducts.inl (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨A, HasBinaryCoproducts.inl, h⟩

/-- The right injection `inr : B ⟶ A+B` packaged as a subobject of `A+B`. -/
def inrSub [HasBinaryCoproducts 𝒞] {A B : 𝒞} (h : Mono (HasBinaryCoproducts.inr (A := A) (B := B))) :
    Subobject 𝒞 (HasBinaryCoproducts.coprod A B) :=
  ⟨B, HasBinaryCoproducts.inr, h⟩

/-- **§1.621/§1.623 DISJOINT BINARY COPRODUCT.**  A positive pre-logos in which the
    coproduct injections satisfy Freyd's §1.621 disjoint-complemented-union conditions.
    This is the missing positivity content that the amalgamation lemma (§1.651),
    balancedness (§1.652), and Diaconescu's theorem (§1.662) all rest on. -/
class DisjointBinaryCoproduct (𝒞 : Type u) [Cat.{v} 𝒞] extends PositivePreLogos 𝒞 where
  /-- The left injection is monic (it is a subobject inclusion). -/
  inl_monic : ∀ {A B : 𝒞}, Mono (HasBinaryCoproducts.inl (A := A) (B := B))
  /-- The right injection is monic. -/
  inr_monic : ∀ {A B : 𝒞}, Mono (HasBinaryCoproducts.inr (A := A) (B := B))
  /-- §1.621 disjointness: `inl ∩ inr = 0` (their intersection is the bottom subobject).
      The intersection is the pullback of `inl` and `inr`, here `≤ PreLogos.bottom`. -/
  inl_inter_inr : ∀ {A B : 𝒞},
    Subobject.le (Subobject.inter (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_monic)
                                  (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_monic))
                 (PreLogos.bottom (HasBinaryCoproducts.coprod A B))
  /-- §1.621 union: `inl ∪ inr = A+B` (the injections jointly cover the coproduct). -/
  inl_union_inr : ∀ {A B : 𝒞},
    Subobject.le (Subobject.entire (HasBinaryCoproducts.coprod A B))
                 (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_monic)
                                           (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_monic))

/-! ### Reusable disjointness lemmas

  Downstream files (`amalgamation_lemma` §1.651, `pretopos_balanced` §1.652,
  the Diaconescu equivalences §1.662) need these three facts about positive
  coproducts.  Each is a direct projection of the §1.621 fields above. -/

/-- **§1.621**: in a positive (disjoint) coproduct the left injection is monic. -/
theorem inl_mono [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Mono (HasBinaryCoproducts.inl (A := A) (B := B)) :=
  DisjointBinaryCoproduct.inl_monic

/-- **§1.621**: in a positive (disjoint) coproduct the right injection is monic. -/
theorem inr_mono [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Mono (HasBinaryCoproducts.inr (A := A) (B := B)) :=
  DisjointBinaryCoproduct.inr_monic

/-- **§1.621 disjointness, pullback form**: the intersection (pullback) of `inl` and
    `inr` in `A+B` is the zero subobject — `inl ∩ inr ≤ 0`.  This is the categorical
    statement "`pullback(inl, inr) ≅ 0`": its domain receives a map to `(bottom).dom`,
    and `bottom_min` gives a map back, so the two are isomorphic when bottom is the
    initial object.  Phrased as a subobject inequality to stay constructive. -/
theorem inl_inter_inr_le_bottom [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Subobject.le (Subobject.inter (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                  (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono))
                 (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) :=
  DisjointBinaryCoproduct.inl_inter_inr

/-- **§1.621/§1.623 union**: `inl ∪ inr = A+B`; the injections jointly cover. -/
theorem inl_union_inr_entire [DisjointBinaryCoproduct 𝒞] {A B : 𝒞} :
    Subobject.le (Subobject.entire (HasBinaryCoproducts.coprod A B))
                 (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                           (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)) :=
  DisjointBinaryCoproduct.inl_union_inr

/-- **§1.621 disjointness, elementwise form** (the shape `amalgamation_lemma` and the
    cokernel-pair argument of §1.652 actually consume): if a generalized element of `A`
    and one of `B` are identified in `A+B` (`f ≫ inl = g ≫ inr`), then they factor
    through the bottom (zero) subobject of `A+B` — there is a map `e : X ⟶ (bottom).dom`
    with `e ≫ (bottom).arr = f ≫ inl`.  This is the categorical content of
    "`pullback(inl, inr) ≅ 0`": the equalizing pair lifts into the intersection
    `inl ∩ inr`, which is `≤ 0` by §1.621.  Derived from `inl_inter_inr_le_bottom`. -/
theorem coprod_inl_inr_disjoint_elt [DisjointBinaryCoproduct 𝒞] {A B : 𝒞}
    {X : 𝒞} (f : X ⟶ A) (g : X ⟶ B)
    (hfg : f ≫ HasBinaryCoproducts.inl = g ≫ HasBinaryCoproducts.inr) :
    ∃ e : X ⟶ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).dom,
      e ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr = f ≫ HasBinaryCoproducts.inl := by
  -- f, g form a cone over (inlSub.arr, inrSub.arr); lift into their pullback = inl ∩ inr.
  let pb := HasPullbacks.has (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr
                             (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono).arr
  have hcone : f ≫ (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr
             = g ≫ (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono).arr := hfg
  let w := pb.lift ⟨X, f, g, hcone⟩
  -- inl ∩ inr ≤ bottom gives e with (w ≫ e) ≫ bottom.arr = w ≫ (inl ∩ inr).arr = f ≫ inl.
  obtain ⟨e, he⟩ := inl_inter_inr_le_bottom (𝒞 := 𝒞) (A := A) (B := B)
  have hwπ₁ : w ≫ pb.cone.π₁ = f := pb.lift_fst ⟨X, f, g, hcone⟩
  refine ⟨w ≫ e, ?_⟩
  -- (inl ∩ inr).arr = π₁ ≫ inlSub.arr = π₁ ≫ inl, and w ≫ π₁ = f.
  calc (w ≫ e) ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr
      = w ≫ (e ≫ (PreLogos.bottom (HasBinaryCoproducts.coprod A B)).arr) := Cat.assoc _ _ _
    _ = w ≫ (Subobject.inter (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                             (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)).arr := by rw [he]
    _ = w ≫ (pb.cone.π₁ ≫ (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr) := rfl
    _ = (w ≫ pb.cone.π₁) ≫ (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono).arr := (Cat.assoc _ _ _).symm
    _ = f ≫ HasBinaryCoproducts.inl := by rw [hwπ₁]; rfl

variable (𝒞)

/-- A pre-topos has disjoint coproducts (§1.621): every pre-topos is positive, and
    positivity *means* the coproduct is the disjoint complemented union §1.623, so the
    §1.621 disjointness conditions hold.  Recorded as the class field bundle that
    downstream pre-topos proofs consume; concrete `PreTopos` instances must supply it
    exactly as Freyd builds it. -/
class PreToposDisjoint (𝒞 : Type u) [Cat.{v} 𝒞] extends
    PreTopos 𝒞, DisjointBinaryCoproduct 𝒞

variable {𝒞}

/-! ## §1.651 Amalgamation Lemma

  In a pre-topos, given monics x: A↣B, y: A↣C, there exists a
  pushout B ↣ D, C ↣ D completing the square. -/

/-- **§1.651 Amalgamation Lemma**: In a pre-topos, the pushout of two
    monics with a common source exists and the resulting maps are monic.
    Proof: form B+C, define equivalence relation E identifying x(a)∼y(a),
    then the effective quotient B+C ↠ D gives the pushout.

    CONSTRUCTIVE PROGRESS (this file): with `[DisjointBinaryCoproduct 𝒞]` now supplying §1.62
    positivity and `[HasCoequalizers 𝒞]` (Freyd's §1.654/657: a pretopos used cocartesianly has
    coequalizers), the pushout object is built EXPLICITLY as `D := coeq(x≫inl, y≫inr)` with
    `u := inl≫q`, `v := inr≫q`.  The commutativity leg `x≫u = y≫v` is discharged sorry-free
    (it is literally the coequalizer equation `q.eq`).

    SHARPENED RESIDUAL (the two `sorry`s below): `Mono u` and `Mono v`.  This is the genuine
    descent obligation: the kernel pair of the regular epi `q` is the equivalence relation
    GENERATED on `B+C` by `{x(a)≫inl ∼ y(a)≫inr}`, and one must show its restriction to the
    image of `inl` (resp. `inr`) is the diagonal.  Disjointness (`inl_inter_inr_le_bottom`,
    `coprod_inl_inr_disjoint_elt`) and `inl/inr_mono` are the NECESSARY ingredients (without
    them `u,v` are not monic), but the proof additionally needs the transitive-closure /
    zigzag analysis of the generated relation — i.e. the construction of a minimal equivalence
    relation containing a given relation, which in this repo only exists *given*
    `HasMinEquivContaining` (built from coequalizers in `preTopos_cocartesian_to_minEquiv`),
    not as a standalone descent lemma for the legs.  Faithful sorry on exactly the two leg
    monicities; the object, the maps, and the square are now real. -/
theorem amalgamation_lemma [DisjointBinaryCoproduct 𝒞] [PreTopos 𝒞] [HasCoequalizers 𝒞]
    {A B C : 𝒞}
    (x : A ⟶ B) (hx : Mono x) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ Mono v ∧ x ≫ u = y ≫ v := by
  -- D := coequalizer of (x ≫ inl, y ≫ inr) : A ⇉ B+C.  u := inl ≫ q, v := inr ≫ q.
  let q := HasCoequalizers.coeq (x ≫ HasBinaryCoproducts.inl) (y ≫ HasBinaryCoproducts.inr)
  refine ⟨q.obj, HasBinaryCoproducts.inl ≫ q.map, HasBinaryCoproducts.inr ≫ q.map, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · -- commutativity: x ≫ (inl ≫ q) = y ≫ (inr ≫ q) is exactly the coequalizer equation.
    rw [← Cat.assoc, ← Cat.assoc]; exact q.eq

/-! ## §1.652 Covers = epics, Monics = cocovers

  In a pre-topos, covers coincide with epimorphisms, and monics
  coincide with coequalizers (cocovers). -/

/-- **§1.652 (crux): a pre-topos is BALANCED** — a map that is both monic and
    epic is an isomorphism.  This is the genuine positivity content of §1.652:
    the cokernel pair of `m` is built from the *disjoint* coproduct `B + B`
    (positivity) via the effective quotient, and a monic that is also epic
    equalizes a pair of equal legs, hence splits.  It is **not** derivable from
    the current axioms — `HasBinaryCoproducts` carries only the bare universal
    property, with no disjointness/universality, so the cokernel-pair argument
    has no axiom to stand on.  Isolated here as the single obligation that both
    reverse-directions below (`cover_eq_epic_preTopos`, `monic_eq_cocover`) rest
    on; closing it needs §1.62 positivity axiomatized as Freyd states it
    (disjoint + universal coproducts).

    STATE (with `[DisjointBinaryCoproduct 𝒞]` now available): the §1.62 positivity axiom IS
    present, so the cokernel-pair `B ⇉ D := coeq(m≫inl, m≫inr)` is now a real object (cf.
    `amalgamation_lemma` with `x = y = m`).  `m` epic forces the two cokernel-pair legs equal,
    which (cokernel pair = pushout of `m,m`) splits `m`.  The remaining gap is identical to the
    one residual in `amalgamation_lemma`: that the cokernel-pair legs are MONIC (the generated
    equivalence relation restricts to the diagonal on `inl(B)`), which needs the transitive
    closure / descent analysis not yet a standalone lemma.  Faithful sorry on exactly that. -/
theorem pretopos_balanced [DisjointBinaryCoproduct 𝒞] [PreTopos 𝒞] {A B : 𝒞}
    (m : A ⟶ B) (hm : Mono m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  sorry

theorem cover_eq_epic_preTopos [DisjointBinaryCoproduct 𝒞] [PreTopos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · -- Cover → epic (§1.512): already proved
    exact cover_epi
  · intro hepi
    rw [cover_iff_image_entire]
    -- Goal: Subobject.IsEntire (image f), i.e., IsIso (image f).arr.
    -- `(image f).arr` is monic; since `f = lift ≫ arr` is epic, `arr` is epic too.
    have h_arr_epi : ∀ {C : 𝒞} (g h : B ⟶ C), (image f).arr ≫ g = (image f).arr ≫ h → g = h := by
      intro C g h heq
      apply hepi
      calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac f]
        _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
        _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [heq]
        _ = (image.lift f ≫ (image f).arr) ≫ h := by rw [← Cat.assoc]
        _ = f ≫ h := by rw [image.lift_fac f]
    -- monic + epic ⟹ iso by balancedness (`pretopos_balanced`), so `image f` is entire.
    exact pretopos_balanced (image f).arr (image f).monic h_arr_epi

/-- **§1.652**: In a pre-topos, monics coincide with cocovers
    (maps that are coequalizers of some pair).
    Requires effective regularity (every monic is a regular monic = an equalizer,
    dually every epic is a regular epic = a coequalizer).
    The `HEq` in the statement is a placeholder for an isomorphism between
    the coequalizer map and `f`. -/
theorem monic_eq_cocover_preTopos [PreTopos 𝒞] [HasCoequalizers 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Mono f ↔ ∃ (C : 𝒞) (p q : C ⟶ A), HEq ((HasCoequalizers.coeq p q).map) f := by
  sorry

/-! ## §1.653 Pushout of a monic and any morphism in a pre-topos

  Given morphisms f: A → B and monic y: A ↣ C in a pre-topos, there is a pushout
  square with the top map monic.  The proof factors f as cover ∘ monic (image
  factorization) and applies the amalgamation lemma §1.651 to the two monics. -/

/-- **§1.653**: In a pre-topos, given f : A → B and monic y : A ↣ C, there exists a
    pushout square (with the B-map monic).
    PROOF: Factor A → B as A ↠ I ↣ B.  Apply §1.651 to I ↣ B and I ↣ C' (pushing y
    through the cover A ↠ I), stack the two squares, and use the pasting lemma.

    STATE: `amalgamation_lemma` (§1.651) is now a real construction here; this §1.653 result
    is the standard reduction to it (image-factor `f`, push `y` through the cover, paste).
    The two unmet pieces are (a) the cover/image transport of `y` into the slice over `I` and
    (b) the pasting lemma for the stacked square — neither of which the disjointness lemmas
    touch; they are pullback/pasting infrastructure orthogonal to §1.62 positivity, and the
    leg-monicity it inherits is the same descent residual as §1.651.  Faithful sorry. -/
theorem pushout_monic_in_pretopos [DisjointBinaryCoproduct 𝒞] [PreTopos 𝒞] [HasCoequalizers 𝒞]
    {A B C : 𝒞}
    (f : A ⟶ B) (y : A ⟶ C) (hy : Mono y) :
    ∃ (D : 𝒞) (u : B ⟶ D) (v : C ⟶ D), Mono u ∧ f ≫ u = y ≫ v := by
  sorry

/-! ## §1.654/§1.657 Pre-topos is cocartesian iff minimal equivalence relations exist

  A pre-topos is COCARTESIAN (its opposite is regular) if and only if
  for every endo-relation R on an object A there exists a minimal
  equivalence relation Ê ⊇ R on A.
  (§1.657: effectiveness means Ê is the level of some coequalizer A → B.)

  Proof sketch (§1.657):
  · (⇒) If A has coequalizers, given f: A→B with level E ⊇ R, then E is
    the minimal equivalence relation containing R (effectiveness).
  · (⇐) Conversely, given R = x°y (level of x,y : C⇒A), form the
    minimal equivalence Ê containing x°y; by effectiveness, Ê = level of
    some cover z: A→B; then z is a coequalizer of x and y. -/

/-- Every endo-relation on every object has a minimal equivalence relation containing it. -/
def HasMinEquivContaining (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] : Prop :=
  ∀ (A : 𝒞) (R : BinRel 𝒞 A A),
    ∃ (E : BinRel 𝒞 A A), EquivalenceRelation E
      ∧ RelLe R E
      ∧ ∀ (F : BinRel 𝒞 A A), EquivalenceRelation F → RelLe R F → RelLe E F

/-- The reciprocal-composition relation `(graph g) ⊚ (graph g)°` is contained in the
    level (kernel pair) of `g`: a composed point `(a, c)` satisfies `a ≫ g = c ≫ g`
    (the pullback square forces it), so its span lifts into `kernelPair g`, and
    image-minimality (`image_min`) turns that into the required `RelHom`. -/
private theorem graphComp_le_kernelPairRel [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe ((graph g) ⊚ (graph g)°) (kernelPairRel g) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hw : a' ≫ g = c' ≫ g := by
    have := pb.cone.w
    simp only [graph, reciprocal] at this ⊢
    dsimp [a', c']; simpa [graph, reciprocal, Cat.comp_id] using this
  let S : Subobject 𝒞 (prod A A) :=
    ⟨kernelPair g, pair (kp₁ (f := g)) (kp₂ (f := g)),
      monic_pair_of_monicPair _ _ (kernelPairRel g).isMonicPair⟩
  let w := (HasPullbacks.has g g).lift ⟨_, a', c', hw⟩
  have hspan : w ≫ pair (kp₁ (f := g)) (kp₂ (f := g)) = sp := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]; exact kp_lift_p₁ _ _ hw
    · rw [Cat.assoc, snd_pair]; exact kp_lift_p₂ _ _ hw
  obtain ⟨k, hk⟩ := image_min sp S ⟨w, hspan⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ kp₁ (f := g) = (image sp).arr ≫ fst
    calc k ≫ kp₁ (f := g) = (k ≫ pair (kp₁ (f := g)) (kp₂ (f := g))) ≫ fst := by
            rw [Cat.assoc, fst_pair]
      _ = (image sp).arr ≫ fst := by rw [hk]
  · show k ≫ kp₂ (f := g) = (image sp).arr ≫ snd
    calc k ≫ kp₂ (f := g) = (k ≫ pair (kp₁ (f := g)) (kp₂ (f := g))) ≫ snd := by
            rw [Cat.assoc, snd_pair]
      _ = (image sp).arr ≫ snd := by rw [hk]

/-- The level (kernel pair) of `g` is contained in `(graph g) ⊚ (graph g)°`: the
    kernel-pair legs `(kp₁, kp₂)` form a cone over `g, g`, hence lift into the
    composition's pullback, then through `image.lift`. -/
private theorem kernelPairRel_le_graphComp [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] [HasImages 𝒞] {A Q : 𝒞} (g : A ⟶ Q) :
    RelLe (kernelPairRel g) ((graph g) ⊚ (graph g)°) := by
  let pb := HasPullbacks.has (graph g).colB ((graph g)°).colA
  let a' := pb.cone.π₁ ≫ (graph g).colA
  let c' := pb.cone.π₂ ≫ ((graph g)°).colB
  let sp : pb.cone.pt ⟶ prod A A := pair a' c'
  have hcone : kp₁ (f := g) ≫ (graph g).colB = kp₂ (f := g) ≫ ((graph g)°).colA := by
    simp only [graph, reciprocal]; exact kp_sq
  let v := pb.lift ⟨_, kp₁ (f := g), kp₂ (f := g), hcone⟩
  have hv1 : v ≫ pb.cone.π₁ = kp₁ (f := g) := pb.lift_fst _
  have hv2 : v ≫ pb.cone.π₂ = kp₂ (f := g) := pb.lift_snd _
  refine ⟨⟨v ≫ image.lift sp, ?_, ?_⟩⟩
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst) = kp₁ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ fst)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ fst) := by rw [image.lift_fac]
      _ = v ≫ a' := by rw [fst_pair]
      _ = (v ≫ pb.cone.π₁) ≫ (graph g).colA := by dsimp [a']; rw [Cat.assoc]
      _ = kp₁ (f := g) := by rw [hv1]; simp [graph, Cat.comp_id]
  · show (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd) = kp₂ (f := g)
    calc (v ≫ image.lift sp) ≫ ((image sp).arr ≫ snd)
        = v ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) := by simp [Cat.assoc]
      _ = v ≫ (sp ≫ snd) := by rw [image.lift_fac]
      _ = v ≫ c' := by rw [snd_pair]
      _ = (v ≫ pb.cone.π₂) ≫ ((graph g)°).colB := by dsimp [c']; rw [Cat.assoc]
      _ = kp₂ (f := g) := by rw [hv2]; simp [graph, reciprocal, Cat.comp_id]

/-- **§1.657**: A pre-topos with coequalizers satisfies HasMinEquivContaining.
    Given `R` on `A`, take the coequalizer `q : A → Q` of `R.colA, R.colB`; its
    level `Ê := kernelPairRel q` is an equivalence relation (§1.567) containing `R`
    (lift via `q`'s coequalizing equation).  Minimality: any equivalence `F ⊇ R` is,
    by effectiveness, the level of a cover `g`; from `R ⊂ F ⊂ level g` we get
    `R.colA ≫ g = R.colB ≫ g`, the coequalizer UMP factors `g = q ≫ d`, hence
    `level q ⊂ level g ⊂ F`. -/
theorem preTopos_cocartesian_to_minEquiv {𝒞 : Type u} [Cat.{v} 𝒞] [PreTopos 𝒞]
    [HasCoequalizers 𝒞] : HasMinEquivContaining 𝒞 := by
  intro A R
  let hcoeq := HasCoequalizers.coeq R.colA R.colB
  refine ⟨kernelPairRel hcoeq.map, level_is_equivalence_relation hcoeq.map, ?_, ?_⟩
  · -- R ⊂ kernelPairRel hcoeq.map : lift R into the kernel pair via hcoeq.eq.
    let l := (HasPullbacks.has hcoeq.map hcoeq.map).lift ⟨_, R.colA, R.colB, hcoeq.eq⟩
    refine ⟨⟨l, ?_, ?_⟩⟩
    · exact kp_lift_p₁ R.colA R.colB hcoeq.eq
    · exact kp_lift_p₂ R.colA R.colB hcoeq.eq
  · -- Minimality.
    intro F hF hRF
    obtain ⟨_, Q, g, _hgcov, hFle, hleF⟩ := EffectiveRegular.effective F hF
    -- R ⊂ F ⊂ (graph g ⊚ graph g°) ⊂ kernelPairRel g.
    have hRkp : RelLe R (kernelPairRel g) :=
      rel_le_trans (rel_le_trans hRF hFle) (graphComp_le_kernelPairRel g)
    obtain ⟨⟨w, hwA, hwB⟩⟩ := hRkp
    -- The coequalized pair becomes equal after g.
    have hRg : R.colA ≫ g = R.colB ≫ g := by
      have e1 : w ≫ kp₁ (f := g) = R.colA := hwA
      have e2 : w ≫ kp₂ (f := g) = R.colB := hwB
      rw [← e1, ← e2, Cat.assoc, Cat.assoc, kp_sq]
    -- Coequalizer UMP: g factors as hcoeq.map ≫ d.
    have hd : hcoeq.map ≫ hcoeq.desc g hRg = g := hcoeq.fac g hRg
    -- kernelPairRel hcoeq.map ⊂ kernelPairRel g (legs of one kernel pair land in the other).
    have hkpkp : RelLe (kernelPairRel hcoeq.map) (kernelPairRel g) := by
      have hsq : kp₁ (f := hcoeq.map) ≫ g = kp₂ (f := hcoeq.map) ≫ g := by
        rw [← hd, ← Cat.assoc, ← Cat.assoc, kp_sq]
      let l := (HasPullbacks.has g g).lift ⟨_, kp₁ (f := hcoeq.map), kp₂ (f := hcoeq.map), hsq⟩
      exact ⟨⟨l, kp_lift_p₁ _ _ hsq, kp_lift_p₂ _ _ hsq⟩⟩
    -- kernelPairRel g ⊂ (graph g ⊚ graph g°) ⊂ F.
    have hkpF : RelLe (kernelPairRel g) F :=
      rel_le_trans (kernelPairRel_le_graphComp g) hleF
    exact rel_le_trans hkpkp hkpF

theorem preTopos_minEquiv_to_cocartesian {𝒞 : Type u} [Cat.{v} 𝒞] [PreTopos 𝒞]
    (h : HasMinEquivContaining 𝒞) : Nonempty (HasCoequalizers 𝒞) := by
  -- Build coequalizers from the minimal-equivalence hypothesis (§1.657 backward direction).
  -- Key: all Prop reasoning is packaged into hcoeProp via obtain; Classical.choose
  -- then lifts the existential data into the Type world for HasCoequalizer.
  suffices ∀ {C A : 𝒞} (f g : C ⟶ A), HasCoequalizer f g by exact ⟨⟨fun f g => this f g⟩⟩
  intro C A f g
  -- Step 1: Build R = image relation of (f,g) : C → A×A.
  let sp : C ⟶ prod A A := pair f g
  let I := image sp
  have hImp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) :=
    monicPair_of_monic_pair _ _ (by rw [← pair_eta I.arr]; exact I.monic)
  let R : BinRel 𝒞 A A := ⟨I.dom, I.arr ≫ fst, I.arr ≫ snd, hImp⟩
  have hRA : image.lift sp ≫ R.colA = f := by
    show image.lift sp ≫ I.arr ≫ fst = f; rw [← Cat.assoc, image.lift_fac, fst_pair]
  have hRB : image.lift sp ≫ R.colB = g := by
    show image.lift sp ≫ I.arr ≫ snd = g; rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- Step 2–4: packaged as a Prop lemma so obtain works throughout.
  have hcoeProp : ∃ (Q : 𝒞) (z : A ⟶ Q), Cover z ∧ f ≫ z = g ≫ z ∧
      ∀ {X : 𝒞} (k : A ⟶ X), f ≫ k = g ≫ k →
        ∃ d : Q ⟶ X, z ≫ d = k ∧ ∀ d' : Q ⟶ X, z ≫ d' = k → d' = d := by
    -- Step 2: get minimal equivalence E ⊇ R.
    obtain ⟨E, hEeq, hRE, hEmin⟩ := h A R
    -- Step 3: effectiveness gives cover z : A → Q.
    obtain ⟨_, Q, z, hzcov, hEle, hleE⟩ := EffectiveRegular.effective E hEeq
    -- R ⊂ kernelPairRel z.
    have hRkpz : RelLe R (kernelPairRel z) :=
      rel_le_trans (rel_le_trans hRE hEle) (graphComp_le_kernelPairRel z)
    -- Step 4a: f ≫ z = g ≫ z.
    have hfz : f ≫ z = g ≫ z := by
      obtain ⟨⟨w, hwA, hwB⟩⟩ := hRkpz
      -- hwA : w ≫ (kernelPairRel z).colA = R.colA, i.e. w ≫ kp₁(z) = R.colA
      -- hwB : w ≫ (kernelPairRel z).colB = R.colB, i.e. w ≫ kp₂(z) = R.colB
      have hcolAz : R.colA ≫ z = R.colB ≫ z := by
        have e1 : w ≫ kp₁ (f := z) = R.colA := by simpa [kernelPairRel] using hwA
        have e2 : w ≫ kp₂ (f := z) = R.colB := by simpa [kernelPairRel] using hwB
        calc R.colA ≫ z = (w ≫ kp₁ (f := z)) ≫ z := by rw [e1]
          _ = w ≫ kp₂ (f := z) ≫ z := by rw [Cat.assoc, kp_sq]
          _ = R.colB ≫ z := by rw [← Cat.assoc, e2]
      calc f ≫ z = image.lift sp ≫ R.colA ≫ z := by rw [← hRA, Cat.assoc]
        _ = image.lift sp ≫ R.colB ≫ z := by rw [hcolAz]
        _ = g ≫ z := by rw [← Cat.assoc, hRB]
    -- Step 4b: UMP.
    refine ⟨Q, z, hzcov, hfz, fun {X} k hfk => ?_⟩
    -- R.colA ≫ k = R.colB ≫ k via cover_epi on image.lift sp.
    have hRk : R.colA ≫ k = R.colB ≫ k := by
      apply cover_epi (image_lift_cover sp)
      calc image.lift sp ≫ R.colA ≫ k = f ≫ k := by rw [← Cat.assoc, hRA]
        _ = g ≫ k := hfk
        _ = image.lift sp ≫ R.colB ≫ k := by rw [← Cat.assoc, hRB]
    -- R ⊂ kernelPairRel k.
    have hRkpk : RelLe R (kernelPairRel k) := by
      let l := (HasPullbacks.has k k).lift ⟨_, R.colA, R.colB, hRk⟩
      exact ⟨⟨l, kp_lift_p₁ R.colA R.colB hRk, kp_lift_p₂ R.colA R.colB hRk⟩⟩
    -- E ⊂ kernelPairRel k by minimality.
    have hEkpk := hEmin (kernelPairRel k) (level_is_equivalence_relation k) hRkpk
    -- kernelPairRel z ⊂ kernelPairRel k.
    have hkpzkpk : RelLe (kernelPairRel z) (kernelPairRel k) :=
      rel_le_trans (rel_le_trans (kernelPairRel_le_graphComp z) hleE) hEkpk
    -- kp₁(z) ≫ k = kp₂(z) ≫ k.
    have hkpeq : kp₁ (f := z) ≫ k = kp₂ (f := z) ≫ k := by
      obtain ⟨⟨φ, hφA, hφB⟩⟩ := hkpzkpk
      -- hφA : φ ≫ (kernelPairRel k).colA = (kernelPairRel z).colA, i.e. φ ≫ kp₁(k) = kp₁(z)
      -- hφB : φ ≫ (kernelPairRel k).colB = (kernelPairRel z).colB, i.e. φ ≫ kp₂(k) = kp₂(z)
      have e1 : φ ≫ kp₁ (f := k) = kp₁ (f := z) := by simpa [kernelPairRel] using hφA
      have e2 : φ ≫ kp₂ (f := k) = kp₂ (f := z) := by simpa [kernelPairRel] using hφB
      calc kp₁ (f := z) ≫ k = (φ ≫ kp₁ (f := k)) ≫ k := by rw [e1]
        _ = φ ≫ kp₂ (f := k) ≫ k := by rw [Cat.assoc, kp_sq]
        _ = kp₂ (f := z) ≫ k := by rw [← Cat.assoc, e2]
    exact cover_is_coequalizer_of_level z hzcov k hkpeq
  -- Lift the Prop data into the HasCoequalizer structure using Classical.choose.
  let Q  := Classical.choose hcoeProp
  let hz := Classical.choose_spec hcoeProp  -- ∃ z, ...
  let z  := Classical.choose hz
  let hzdata := Classical.choose_spec hz    -- Cover z ∧ f≫z=g≫z ∧ UMP
  have hzcov : Cover z := hzdata.1
  have hfz   : f ≫ z = g ≫ z := hzdata.2.1
  have hUMP  : ∀ {X : 𝒞} (k : A ⟶ X), f ≫ k = g ≫ k →
      ∃ d : Q ⟶ X, z ≫ d = k ∧ ∀ d' : Q ⟶ X, z ≫ d' = k → d' = d := hzdata.2.2
  exact {
    obj  := Q
    map  := z
    eq   := hfz
    desc := fun k hfk => Classical.choose (hUMP k hfk)
    fac  := fun k hfk => (Classical.choose_spec (hUMP k hfk)).1
    uniq := fun k hfk m hm => (Classical.choose_spec (hUMP k hfk)).2 m hm
  }

/-! ## §1.655 Bicartesian representation criterion

  If A and B are pre-topoi and T : A → B a functor preserving 0, pushouts,
  finite products and monics, then T is a bicartesian representation.
  PROOF SKETCH (§1.655): T preserves pullbacks of monics (by §1.651 + pasting);
  T preserves equalizers (products ⟹ equalizers); T preserves covers (=
  coequalizers, §1.652; T preserves pushouts and 0). -/

-- §1.655 (note): A functor T between pre-topoi preserving 0, pushouts, products
-- and monics is a bicartesian representation.
-- PROOF: Products + §1.651 → T preserves pullbacks of monics; products → equalizers
-- (§1.434); covers = coequalizers + pushout preservation → T preserves covers.
-- Requires formalizing the Functor API for inter-category morphisms.

/-! ## §1.658 Decidable object

  An object A in a pre-logos is DECIDABLE if the diagonal (1,1): A → A×A
  has a complement in the subobject lattice of A×A.

  Every object in a pre-topos is decidable iff the pre-topos is boolean.

  PROOF SKETCH:
  (⇐) Boolean ⇒ every subobject is complemented, in particular the diagonal.
  (⇒) Given A decidable, let A' → A×B be any subobject; form the equalizer of
      (A' → A×B → B → B×B) and (A' → A×B → A×B → B×B via diag∘second).
      Because pullbacks of complemented subobjects are complemented (§1.658),
      the Boolean algebra structure transfers to all subobjects via slices. -/

/-- **§1.658**: A in a pre-logos is DECIDABLE if the diagonal `diag A : A → A×A`
    has a complement in `Subobject 𝒞 (prod A A)`.
    Lean note: `diag A` is monic (§1.42: `diag_mono`); the subobject is `{ dom := A, arr := diag A, monic := diag_mono A }`. -/
def DecidableObject [PreLogos 𝒞] [HasBinaryProducts 𝒞] (A : 𝒞) : Prop :=
  IsComplemented ({ dom := A, arr := diag A, monic := diag_mono A } : Subobject 𝒞 (prod A A))

/-- **§1.658**: Every object in a pre-topos is decidable iff the pre-topos is boolean.
    The harder direction (all decidable → boolean) follows because pullbacks of
    complemented subobjects are complemented, and every subobject U ⊆ 1 can be
    pulled back to any slice, where it coincides with the diagonal. -/
theorem preTopos_boolean_iff_all_decidable [PreTopos 𝒞] [HasBinaryProducts 𝒞] :
    (Nonempty (BooleanPreLogos 𝒞)) ↔ ∀ (A : 𝒞), DecidableObject A := by
  refine ⟨fun ⟨hbool⟩ A => ?_, fun h => ?_⟩
  · -- (⇒) BooleanPreLogos → every diagonal subobject is complemented = DecidableObject A.
    -- The instance mismatch between hbool.toPreLogos and the ambient [PreLogos 𝒞] variable
    -- is resolved by using hbool's union_min to bridge to the ambient union.
    unfold DecidableObject IsComplemented
    let diagSub : Subobject 𝒞 (prod A A) := { dom := A, arr := diag A, monic := diag_mono A }
    obtain ⟨A₂, hdisj, hunion⟩ := hbool.hasComplement diagSub
    refine ⟨A₂, hdisj, ?_⟩
    -- hunion : entire ≤ hbool.union diagSub A₂; goal: entire ≤ ambient(PreTopos).union diagSub A₂.
    -- Bridge hbool's union to the PreTopos union via hbool.union_min applied with the
    -- PreTopos-union as the common upper bound.  All `union_*` calls are taken from
    -- `hbool.toPreLogos.toHasSubobjectUnions` so they agree with `hunion`.
    let unionAmb := @HasSubobjectUnions.union 𝒞 _ _
      (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hleft  : diagSub.le unionAmb :=
      @HasSubobjectUnions.union_left 𝒞 _ _
        (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hright : A₂.le unionAmb :=
      @HasSubobjectUnions.union_right 𝒞 _ _
        (PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions) (prod A A) diagSub A₂
    have hle : (hbool.toPreLogos.toHasSubobjectUnions.union diagSub A₂).le unionAmb :=
      hbool.toPreLogos.toHasSubobjectUnions.union_min diagSub A₂ _ hleft hright
    obtain ⟨e1, he1⟩ := hunion
    obtain ⟨e2, he2⟩ := hle
    exact ⟨e1 ≫ e2, by rw [Cat.assoc, he2, he1]⟩
  · -- (⇐) All decidable → BooleanPreLogos.
    -- Requires pullback stability of complements (§1.658): if K is complemented and f : B → C,
    -- then InverseImage f K is complemented. Every subobject S of B can then be shown
    -- complemented by pulling back the diagonal (which is decidable) along an appropriate map.
    --
    -- SHARPENED BLOCKER (infra audit):
    --   • InverseImage (S1_60:51) and its union-preservation (PreLogos.invImage_preserves_union,
    --     invImage_preserves_bottom, S1_60:89/91) ARE available — so "f# of a complement is a
    --     complement" is *almost* in reach for the `IsComplementedSub` formulation
    --     (Subobject.inter, S1_62:75), but NOT for the `IsComplemented` placeholder used here,
    --     whose intersection clause is the ad-hoc "no nontrivial common lower bound" predicate
    --     rather than `Subobject.inter _ _ ≤ bottom`.  The two are not interchangeable without a
    --     bridge lemma `IsComplemented ↔ IsComplementedSub` (also unformalized).
    --   • The genuine missing step is the *construction* exhibiting an arbitrary S ⊆ B as a
    --     pullback of the (decidable, hence complemented) diagonal diag A ⊆ A×A along some
    --     classifying map B → A×A.  Freyd builds this in the slice 𝒮(1) and transports along the
    --     slice projection; the slice pre-topos and its complement transport are not in this repo.
    -- Reduces to: (a) IsComplemented↔IsComplementedSub bridge, (b) the diagonal-classifies-S
    -- slice construction. Faithful sorry.
    sorry

/-! ## §1.659 Decidability in functor categories and sheaves

  T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B ∈ A.
  For sheaves: X → Y is decidable iff every pair of points with the same
  stalk have disjoint neighborhoods; in particular, decidable iff Y is Hausdorff.
  (These results require the sheaf/functor-category infrastructure; stated
  with sorry pending that development.) -/

-- §1.659 (note): T ∈ Fᴬ is decidable iff T(x) is a monic map for all x : A → B in A.
-- For sheaves on Y: X → Y is decidable iff stalk-equal points have disjoint neighborhoods
-- (Y Hausdorff → X → Y decidable iff X Hausdorff).
-- Requires functor category and sheaf infrastructure.

/-! ## §1.66 Choice objects in a pre-topos

  We study choice objects [§1.57] in a regular category. -/

section Choice66

variable [RegularCategory 𝒞]

/-- **§1.66**: A subobject of a choice object is choice.
    If C is choice and m: A↣C is monic, then A is choice.
    PROOF: Let R be an entire relation from X to A.
    Then m ≫ R is an entire relation from X to C (composition with a map).
    Because C is choice, m ≫ R contains a map f: X → C.
    Since m is monic, f factors uniquely through A: the factorization gives
    the required map in R. (Requires: entire relations compose with maps.) -/
theorem subobject_of_choice_is_choice {A C : 𝒞} (m : A ⟶ C) (hm : Mono m)
    (hC : Choice C) : Choice A := by
  intro X R hent
  -- Post-compose R : X → A with the monic m to get R' : X → C, same left leg.
  have hp' : MonicPair R.colA (R.colB ≫ m) := by
    intro W f g hA hB
    have hB' : f ≫ R.colB = g ≫ R.colB :=
      hm _ _ (by simpa [Cat.assoc] using hB)
    exact R.isMonicPair f g hA hB'
  let R' : BinRel 𝒞 X C := BinRel.mk R.src R.colA (R.colB ≫ m) hp'
  -- R is entire ⇒ R.colA is a cover ⇒ R' is entire (same left leg).
  have hcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hent' : Entire R' :=
    (tabulated_is_entire_iff_left_cover R.colA (R.colB ≫ m) hp').mpr hcov
  -- C is choice: R' contains a map; its witness `h : X → R.src` also witnesses
  -- the map `h ≫ R.colB : X → A` inside R.
  obtain ⟨_f, h, hA, _hB⟩ := hC R' hent'
  exact ⟨h ≫ R.colB, h, hA, rfl⟩

/-- **§1.66**: A quotient (cover target) of a choice object is choice.
    If C is choice and x: C↠B is a cover, then B is choice.
    PROOF (book §1.66): x: C → B is also a subobject of C via x° ⊂ 1_C
    (the inclusion via a map contained in x°). Apply subobject_of_choice. -/
theorem quotient_of_choice_is_choice {B C : 𝒞} (x : C ⟶ B) (hx : Cover x)
    (hC : Choice C) : Choice B := by
  intro X R hent
  -- R : X → B entire ⇒ R.colA : R.src → X is a cover.
  have hcovA : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  -- Pull the cover x : C → B back along R.colB : R.src → B.
  -- `has x R.colB` cone: π₁ : pt → C, π₂ : pt → R.src, π₁ ≫ x = π₂ ≫ R.colB.
  let pb := HasPullbacks.has x R.colB
  have hcov_π₂ : Cover pb.cone.π₂ := cover_pullback (f := x) R.colB hx
  have hw : pb.cone.π₁ ≫ x = pb.cone.π₂ ≫ R.colB := pb.cone.w
  -- Build R'' : X → C with src = pb.pt, left leg = π₂ ≫ R.colA (a cover),
  -- right leg = π₁ : pt → C.  Monic pair: left leg cancels the R-data and the
  -- pullback's π₁ is determined by π₂ via the universal property... we instead
  -- check joint-monicity directly.
  have hp'' : MonicPair (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ := by
    intro W f g hA hB
    -- hA : f ≫ (π₂ ≫ R.colA) = g ≫ (π₂ ≫ R.colA),  hB : f ≫ π₁ = g ≫ π₁.
    -- From hB and hw: f ≫ π₂ ≫ R.colB = g ≫ π₂ ≫ R.colB.
    have hB2 : (f ≫ pb.cone.π₂) ≫ R.colB = (g ≫ pb.cone.π₂) ≫ R.colB := by
      have : f ≫ (pb.cone.π₁ ≫ x) = g ≫ (pb.cone.π₁ ≫ x) := by
        rw [← Cat.assoc, ← Cat.assoc, hB]
      rw [hw] at this
      simpa [Cat.assoc] using this
    have hA2 : (f ≫ pb.cone.π₂) ≫ R.colA = (g ≫ pb.cone.π₂) ≫ R.colA := by
      simpa [Cat.assoc] using hA
    -- (π₂'s composites with R.colA, R.colB) agree ⇒ f ≫ π₂ = g ≫ π₂ (R monic pair).
    have hπ₂ : f ≫ pb.cone.π₂ = g ≫ pb.cone.π₂ :=
      R.isMonicPair (f ≫ pb.cone.π₂) (g ≫ pb.cone.π₂) hA2 hB2
    -- Together with hB (agreement on π₁), the pullback's joint monicity (lift_uniq) gives f = g.
    have hw' : (f ≫ pb.cone.π₁) ≫ x = (f ≫ pb.cone.π₂) ≫ R.colB := by
      rw [Cat.assoc, Cat.assoc, hw]
    let c : Cone x R.colB := ⟨W, f ≫ pb.cone.π₁, f ≫ pb.cone.π₂, hw'⟩
    have hf : f = pb.lift c := pb.lift_uniq c f rfl rfl
    have hg : g = pb.lift c := pb.lift_uniq c g hB.symm hπ₂.symm
    rw [hf, hg]
  let R'' : BinRel 𝒞 X C := BinRel.mk pb.cone.pt (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ hp''
  have hent'' : Entire R'' :=
    (tabulated_is_entire_iff_left_cover (pb.cone.π₂ ≫ R.colA) pb.cone.π₁ hp'').mpr
      (cover_comp hcov_π₂ hcovA)
  -- C choice: R'' contains a map with witness h : X → pb.pt.
  obtain ⟨_f, h, hA, _hB⟩ := hC R'' hent''
  -- hA : h ≫ (π₂ ≫ R.colA) = id_X.  The map into B is h ≫ π₁ ≫ x = h ≫ π₂ ≫ R.colB.
  refine ⟨h ≫ pb.cone.π₁ ≫ x, h ≫ pb.cone.π₂, ?_, ?_⟩
  · -- (h ≫ π₂) ≫ R.colA = id_X
    rw [Cat.assoc]; exact hA
  · -- (h ≫ π₂) ≫ R.colB = h ≫ π₁ ≫ x
    calc (h ≫ pb.cone.π₂) ≫ R.colB = h ≫ (pb.cone.π₂ ≫ R.colB) := Cat.assoc _ _ _
      _ = h ≫ (pb.cone.π₁ ≫ x) := by rw [← hw]
      _ = h ≫ pb.cone.π₁ ≫ x := rfl

end Choice66

/-! ## §1.661 Finite products of choice objects are choice

  In a regular category, finite products of choice objects are choice.
  (Proof uses: any entire relation targeted at a terminator is already a map;
  for binary products, decompose R : X → B₁×B₂ via its projections.) -/

section Choice661

variable [RegularCategory 𝒞]

/-- **§1.661**: The terminator is always choice in a regular category.
    PROOF: Any entire relation R : X → 1 is automatically simple, because all maps
    to `one` are equal (terminal uniqueness), so `R° ⊚ R : one → one` trivially lies
    inside `graph id_one`.  Hence R is a map, its left leg R.colA is an iso, and its
    inverse is the required section. -/
theorem terminator_is_choice : Choice (one : 𝒞) := by
  intro A R hent
  -- Terminal uniqueness forces R to be simple.
  have h_simple : Simple R :=
    ⟨⟨(R° ⊚ R).colA,
      by simp [graph, Cat.comp_id],
      by simp [graph]; rw [Cat.comp_id]; exact term_uniq _ _⟩⟩
  -- Entire + Simple = Map, so R.colA is an isomorphism.
  have h_iso : IsIso R.colA :=
    (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp ⟨hent, h_simple⟩
  obtain ⟨inv, _hinv_left, hinv_right⟩ := h_iso
  exact ⟨inv ≫ R.colB, inv, hinv_right, rfl⟩

/-- Helper for §1.661: project an entire relation `R : A → C` through a *map*
    `g : C → D` and extract, from `Choice D`, an actual morphism `f : A → D` that is
    realized inside `R` after `g` — there is a witness `w : A → R.src` with
    `w ≫ R.colA = id_A` and `w ≫ R.colB ≫ g = f`.  This is the constructive,
    sorry-free half of §1.661: the image relation
    `R_g := {(R.colA a, (R.colB ≫ g) a)}` is jointly monic and its left leg is a
    cover (it post-factors the cover `R.colA`), hence entire; choice of `D` hands
    back the factor map together with its section.  (No modular law needed here.) -/
private theorem choice_factor_through_map {A C D : 𝒞}
    (R : BinRel 𝒞 A C) (hent : Entire R) (g : C ⟶ D) (hD : Choice D) :
    ∃ (f : A ⟶ D) (E : BinRel 𝒞 A D) (w : A ⟶ E.src),
      Cover E.colA ∧ w ≫ E.colA = Cat.id A ∧ w ≫ E.colB = f := by
  -- R_g = image of ⟨R.colA, R.colB ≫ g⟩ : R.src → A × D, viewed as a relation A → D.
  let sp : R.src ⟶ prod A D := pair R.colA (R.colB ≫ g)
  let I := image sp
  have hp : MonicPair (I.arr ≫ fst) (I.arr ≫ snd) := by
    intro W u v hA hB
    have hfst : (u ≫ I.arr) ≫ fst = (v ≫ I.arr) ≫ fst := by
      rw [Cat.assoc, Cat.assoc]; exact hA
    have hsnd : (u ≫ I.arr) ≫ snd = (v ≫ I.arr) ≫ snd := by
      rw [Cat.assoc, Cat.assoc]; exact hB
    have : u ≫ I.arr = v ≫ I.arr := by
      rw [pair_eta (u ≫ I.arr), pair_eta (v ≫ I.arr), hfst, hsnd]
    exact I.monic u v this
  let R_g : BinRel 𝒞 A D := BinRel.mk I.dom (I.arr ≫ fst) (I.arr ≫ snd) hp
  -- left leg of R_g is a cover: `image.lift sp ≫ R_g.colA = R.colA` (a cover, R entire).
  have hcovA : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hfac : image.lift sp ≫ R_g.colA = R.colA := by
    show image.lift sp ≫ (I.arr ≫ fst) = R.colA
    rw [← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- right factor of a cover is a cover.
  have hcov_Rg : Cover R_g.colA := by
    intro K m k hm hk
    refine hcovA m (image.lift sp ≫ k) hm ?_
    rw [Cat.assoc, hk]; exact hfac
  have hent_g : Entire R_g :=
    (tabulated_is_entire_iff_left_cover R_g.colA R_g.colB hp).mpr hcov_Rg
  obtain ⟨f, w, hwA, hwB⟩ := hD R_g hent_g
  exact ⟨f, R_g, w, hcov_Rg, hwA, hwB⟩

/-- A morphism with a section is a cover (split epi ⟹ cover):
    given `s ≫ e = id`, any monic `m` that `e` factors through is split epi
    (via `s ≫ g`), and a monic split epi is an iso. -/
private theorem cover_of_section {X Y : 𝒞} (e : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ e = Cat.id Y) : Cover e := by
  intro C m g hm hgm
  -- m is split epi: (s ≫ g) ≫ m = s ≫ e = id_Y.
  have hsplit : (s ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, hs]
  -- m monic + (s≫g) a section ⟹ m iso.
  refine ⟨s ≫ g, ?_, hsplit⟩
  -- m ≫ (s ≫ g) = id_C : m is monic, and m ≫ (s≫g) ≫ m = m ≫ id by hsplit.
  apply hm
  rw [Cat.assoc, hsplit, Cat.comp_id, Cat.id_comp]

/-- If a composite `c ≫ g` is a cover then its right factor `g` is a cover:
    any monic `m` that `g` factors through, `c ≫ g` also factors through, so
    `c ≫ g` being a cover forces `m` iso. -/
private theorem cover_right_factor {X Y Z : 𝒞} (c : X ⟶ Y) (g : Y ⟶ Z)
    (h : Cover (c ≫ g)) : Cover g := by
  intro D m k hm hkm
  refine h m (c ≫ k) hm ?_
  rw [Cat.assoc, hkm]

/-- A relation composed with the graph of a map stays entire (the totality of
    `R` is preserved by post-composition with a total map `p`).  Used in §1.661 to
    project the entire `R : A → B₁×B₂` through `fst`/`snd` into the choice factors. -/
private theorem entire_comp_graph {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
    (R : BinRel 𝒞 A B) (hent : Entire R) (p : B ⟶ C) : Entire (R ⊚ graph p) := by
  have hRcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  let pb := HasPullbacks.has R.colB (Cat.id B)
  let span : pb.cone.pt ⟶ prod A C := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ p)
  have hfac : image.lift span ≫ (R ⊚ graph p).colA = pb.cone.π₁ ≫ R.colA := by
    show image.lift span ≫ ((image span).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- pb.π₁ is iso (pullback against id_B), so pb.π₁ ≫ R.colA is a cover.
  have hsq : Cat.id R.src ≫ R.colB = R.colB ≫ Cat.id B := by rw [Cat.id_comp, Cat.comp_id]
  let s : R.src ⟶ pb.cone.pt := pb.lift ⟨R.src, Cat.id R.src, R.colB, hsq⟩
  have hs₁ : s ≫ pb.cone.π₁ = Cat.id R.src := pb.lift_fst _
  have hs₂ : s ≫ pb.cone.π₂ = R.colB := pb.lift_snd _
  have hπ₁s : pb.cone.π₁ ≫ s = Cat.id pb.cone.pt := by
    have e1 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₁ = pb.cone.π₁ := by rw [Cat.assoc, hs₁, Cat.comp_id]
    have e2 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₂ = pb.cone.π₂ := by
      rw [Cat.assoc, hs₂]; have hw := pb.cone.w; rw [Cat.comp_id] at hw; exact hw
    have hid₁ : Cat.id pb.cone.pt ≫ pb.cone.π₁ = pb.cone.π₁ := Cat.id_comp _
    have hid₂ : Cat.id pb.cone.pt ≫ pb.cone.π₂ = pb.cone.π₂ := Cat.id_comp _
    let cn : Cone R.colB (Cat.id B) := ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, pb.cone.w⟩
    exact (pb.lift_uniq cn _ e1 e2).trans (pb.lift_uniq cn _ hid₁ hid₂).symm
  have hcov_pre : Cover (pb.cone.π₁ ≫ R.colA) :=
    cover_precomp_iso ⟨s, hπ₁s, hs₁⟩ hRcov
  -- image.lift span ≫ (R⊚graph p).colA is a cover ⟹ (R⊚graph p).colA is a cover.
  have hcomp : Cover (image.lift span ≫ (R ⊚ graph p).colA) := by rw [hfac]; exact hcov_pre
  have : Cover (R ⊚ graph p).colA := cover_right_factor _ _ hcomp
  exact (tabulated_is_entire_iff_left_cover _ _ (R ⊚ graph p).isMonicPair).mpr this

/-- **Pinning lemma**: the relation `graph f ⊚ (graph p)°` (for maps `f : A → C`,
    `p : B → C`) is contained in the "agree at C" relation: its two legs satisfy
    `colA ≫ f = colB ≫ p`.  (Its image-cover `image.lift span` carries the pullback
    square `π₁ ≫ f = π₂ ≫ p`; covers are epic, so the equation descends.) -/
private theorem comp_recip_pin {A B C : 𝒞} (f : A ⟶ C) (p : B ⟶ C) :
    (graph f ⊚ (graph p)°).colA ≫ f = (graph f ⊚ (graph p)°).colB ≫ p := by
  let pb := HasPullbacks.has (graph f).colB ((graph p)°).colA
  let span : pb.cone.pt ⟶ prod A B :=
    pair (pb.cone.π₁ ≫ (graph f).colA) (pb.cone.π₂ ≫ ((graph p)°).colB)
  -- image.lift span ≫ colA = π₁ (since (graph f).colA = id_A), likewise colB = π₂.
  have hA : image.lift span ≫ (graph f ⊚ (graph p)°).colA = pb.cone.π₁ := by
    show image.lift span ≫ ((image span).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id B) ≫ fst = _
    rw [fst_pair]; exact Cat.comp_id _
  have hB : image.lift span ≫ (graph f ⊚ (graph p)°).colB = pb.cone.π₂ := by
    show image.lift span ≫ ((image span).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac]
    show pair (pb.cone.π₁ ≫ Cat.id A) (pb.cone.π₂ ≫ Cat.id B) ≫ snd = _
    rw [snd_pair]; exact Cat.comp_id _
  -- pullback square: π₁ ≫ (graph f).colB = π₂ ≫ (graph p)°.colA, i.e. π₁ ≫ f = π₂ ≫ p.
  have hw : pb.cone.π₁ ≫ f = pb.cone.π₂ ≫ p := pb.cone.w
  -- descend along the cover `image.lift span` (covers are epic).
  apply cover_epi (image_lift_cover span)
  calc image.lift span ≫ ((graph f ⊚ (graph p)°).colA ≫ f)
      = (image.lift span ≫ (graph f ⊚ (graph p)°).colA) ≫ f := (Cat.assoc _ _ _).symm
    _ = pb.cone.π₁ ≫ f := by rw [hA]
    _ = pb.cone.π₂ ≫ p := hw
    _ = (image.lift span ≫ (graph f ⊚ (graph p)°).colB) ≫ p := by rw [hB]
    _ = image.lift span ≫ ((graph f ⊚ (graph p)°).colB ≫ p) := Cat.assoc _ _ _

/-- **§1.563 entire-refinement** (the §1.661 gluing engine): if `f : A → C` is a map with
    `graph f ⊂ R ⊚ graph p` (for `R : A → B` and a morphism `p : B → C`), then the *refined*
    relation `R' := R ⊓ (graph f ⊚ (graph p)°)` is entire.  (Totality is carried by the map
    `f`; `R` itself need not be entire — in §1.661 it is, which is what supplies `hf`.)

    Constructive proof via the intersection-form modular law (`modular_identity`):
    setting `R, S := graph p, T := graph f` and using `graph f ⊂ R⊚graph p`
    (so `(R⊚graph p) ⊓ graph f = graph f`), modularity gives `graph f ⊂ R' ⊚ graph p`.
    The witnessing `RelHom` provides `h : A → (R'⊚graph p).src` with `h ≫ (R'⊚graph p).colA
    = id_A`, i.e. `(R'⊚graph p).colA` is split epi hence a cover; its left leg factors the
    cover `image.lift` of `R'.colA`, so `R'.colA` is a composite of covers, hence a cover —
    which is exactly `Entire R'`. -/
private theorem entire_refine {A B C : 𝒞} [PullbacksTransferCovers 𝒞]
    (R : BinRel 𝒞 A B) (p : B ⟶ C) (f : A ⟶ C)
    (hf : graph f ⊂ R ⊚ graph p) :
    Entire (R ⊓ (graph f ⊚ (graph p)°)) := by
  -- abbreviation: R' := R ⊓ (graph f ⊚ (graph p)°)
  let R' := R ⊓ (graph f ⊚ (graph p)°)
  -- modular_identity with (R, graph p, graph f):
  --   (R ⊚ graph p) ⊓ graph f ⊂ (R ⊓ (graph f ⊚ (graph p)°)) ⊚ graph p = R' ⊚ graph p
  have hmod : ((R ⊚ graph p) ⊓ graph f) ⊂ R' ⊚ graph p :=
    modular_identity R (graph p) (graph f)
  -- graph f ⊂ R ⊚ graph p  ⟹  graph f ⊂ (R ⊚ graph p) ⊓ graph f, so graph f ⊂ R'⊚graph p.
  have hgf : graph f ⊂ R' ⊚ graph p :=
    rel_le_trans (le_intersect hf (rel_le_refl (graph f))) hmod
  -- It suffices to show R'.colA is a cover (Entire ⟺ left leg cover).
  suffices hcov : Cover R'.colA by
    exact (tabulated_is_entire_iff_left_cover R'.colA R'.colB R'.isMonicPair).mpr hcov
  -- The composite R' ⊚ graph p factors R'.colA through a pullback-against-identity:
  --   image.lift span ≫ (R'⊚graph p).colA = pb.π₁ ≫ R'.colA,  pb := pullback(R'.colB, id_B).
  let pb := HasPullbacks.has R'.colB (Cat.id B)
  let span : pb.cone.pt ⟶ prod A C :=
    pair (pb.cone.π₁ ≫ R'.colA) (pb.cone.π₂ ≫ p)
  -- (R'⊚graph p).colA = (image span).arr ≫ fst, definitionally.
  have hcolA_def : (R' ⊚ graph p).colA = (image span).arr ≫ fst := rfl
  -- factorization: image.lift span ≫ (R'⊚graph p).colA = pb.π₁ ≫ R'.colA.
  have hfac : image.lift span ≫ (R' ⊚ graph p).colA = pb.cone.π₁ ≫ R'.colA := by
    rw [hcolA_def, ← Cat.assoc, image.lift_fac]; exact fst_pair _ _
  -- (R'⊚graph p).colA is a cover: graph f ⊂ R'⊚graph p gives a section (graph f has colA = id_A).
  obtain ⟨h, hA, _hB⟩ := hgf
  have hsec : h ≫ (R' ⊚ graph p).colA = Cat.id A := by simpa [graph] using hA
  have hcov_comp : Cover (R' ⊚ graph p).colA := cover_of_section _ h hsec
  -- pb.cone.π₁ is iso (pullback against id_B): section s := pb.lift ⟨_, id, R'.colB, _⟩.
  have hsq : Cat.id R'.src ≫ R'.colB = R'.colB ≫ Cat.id B := by rw [Cat.id_comp, Cat.comp_id]
  let s : R'.src ⟶ pb.cone.pt := pb.lift ⟨R'.src, Cat.id R'.src, R'.colB, hsq⟩
  have hs₁ : s ≫ pb.cone.π₁ = Cat.id R'.src := pb.lift_fst _
  have hs₂ : s ≫ pb.cone.π₂ = R'.colB := pb.lift_snd _
  -- π₁ ≫ s = id_pt: both `π₁ ≫ s` and `id` lift the canonical cone over (R'.colB, id_B).
  have hπ₁s : pb.cone.π₁ ≫ s = Cat.id pb.cone.pt := by
    have e1 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₁ = pb.cone.π₁ := by rw [Cat.assoc, hs₁, Cat.comp_id]
    have e2 : (pb.cone.π₁ ≫ s) ≫ pb.cone.π₂ = pb.cone.π₂ := by
      rw [Cat.assoc, hs₂]; have hw := pb.cone.w; rw [Cat.comp_id] at hw; exact hw
    have hid₁ : Cat.id pb.cone.pt ≫ pb.cone.π₁ = pb.cone.π₁ := Cat.id_comp _
    have hid₂ : Cat.id pb.cone.pt ≫ pb.cone.π₂ = pb.cone.π₂ := Cat.id_comp _
    let cn : Cone R'.colB (Cat.id B) := ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, pb.cone.w⟩
    exact (pb.lift_uniq cn _ e1 e2).trans (pb.lift_uniq cn _ hid₁ hid₂).symm
  have hπ₁_iso : IsIso pb.cone.π₁ := ⟨s, hπ₁s, hs₁⟩
  -- pb.π₁ ≫ R'.colA is a cover (image.lift cover ≫ (R'⊚graph p).colA cover, via hfac).
  have hcov_pre : Cover (pb.cone.π₁ ≫ R'.colA) := by
    rw [← hfac]; exact cover_comp (image_lift_cover span) hcov_comp
  -- R'.colA = s ≫ (π₁ ≫ R'.colA), a cover precomposed by the iso s ⟹ cover.
  have hR'colA : s ≫ (pb.cone.π₁ ≫ R'.colA) = R'.colA := by
    rw [← Cat.assoc, hs₁, Cat.id_comp]
  have hfin : Cover (s ≫ (pb.cone.π₁ ≫ R'.colA)) :=
    cover_precomp_iso ⟨pb.cone.π₁, hs₁, hπ₁s⟩ hcov_pre
  rwa [hR'colA] at hfin

/-- **§1.661**: The binary product of two choice objects is choice.
    PROOF (book §1.661): Let R be entire from A to B₁×B₂.
    R∘fst° is entire targeted at B₁, so it contains a map f₁ (`entire_comp_graph` +
    `Choice B₁`).  The *refined* relation R' := R ∩ (f₁∘fst°) is again entire — this is
    the §1.563 intersection-modular content, discharged here sorry-free by `entire_refine`
    (built on `modular_identity`).  R' pins the B₁-coordinate to f₁ (`comp_recip_pin`),
    so ⟨R'.colA, R'.colB ≫ snd⟩ is jointly monic; its left leg is the cover R'.colA, hence
    the B₂-valued relation R'₂ is entire and `Choice B₂` extracts f₂ *together with a single
    witness `w : A → R'.src`*.  By the pinning, w ≫ R'.colB = pair f₁ f₂, and R' ⊂ R carries
    w into R.src — giving the map ⟨f₁,f₂⟩ ⊂ R.  Fully constructive on `modular_identity`. -/
theorem prod_choice_is_choice [PullbacksTransferCovers 𝒞] {B₁ B₂ : 𝒞}
    (h₁ : Choice B₁) (h₂ : Choice B₂) : Choice (prod B₁ B₂) := by
  intro A R hent
  -- (1) f₁ : A → B₁ contained in R ⊚ graph fst  (R⊚fst° entire, B₁ choice).
  have hent_fst : Entire (R ⊚ graph (fst : prod B₁ B₂ ⟶ B₁)) := entire_comp_graph R hent fst
  obtain ⟨f₁, h₁w, h₁A, h₁B⟩ := h₁ (R ⊚ graph fst) hent_fst
  have hgf₁ : graph f₁ ⊂ R ⊚ graph fst := ⟨⟨h₁w, by simpa [graph] using h₁A, h₁B⟩⟩
  -- (2) the refined relation R' := R ⊓ (graph f₁ ⊚ (graph fst)°), entire by `entire_refine`.
  let R' : BinRel 𝒞 A (prod B₁ B₂) := R ⊓ (graph f₁ ⊚ (graph fst)°)
  have hentR' : Entire R' := entire_refine R fst f₁ hgf₁
  -- (3) pinning: every R'-point has fst-coordinate = f₁ of its A-coordinate.
  obtain ⟨z, hzA, hzB⟩ := intersect_le_right R (graph f₁ ⊚ (graph fst)°)
  have hpin : R'.colB ≫ fst = R'.colA ≫ f₁ := by
    have hbase := comp_recip_pin f₁ (fst : prod B₁ B₂ ⟶ B₁)
    -- transport along z : R'.src → (graph f₁ ⊚ (graph fst)°).src.
    calc R'.colB ≫ fst = (z ≫ (graph f₁ ⊚ (graph fst)°).colB) ≫ fst := by rw [hzB]
      _ = z ≫ ((graph f₁ ⊚ (graph fst)°).colB ≫ fst) := Cat.assoc _ _ _
      _ = z ≫ ((graph f₁ ⊚ (graph fst)°).colA ≫ f₁) := by rw [hbase]
      _ = (z ≫ (graph f₁ ⊚ (graph fst)°).colA) ≫ f₁ := (Cat.assoc _ _ _).symm
      _ = R'.colA ≫ f₁ := by rw [hzA]
  -- (4) R'₂ : A → B₂ with source R'.src, legs (R'.colA, R'.colB ≫ snd) — jointly monic
  --     thanks to the pinning, left leg R'.colA a cover (R' entire) ⟹ R'₂ entire.
  have hR'cov : Cover R'.colA :=
    (tabulated_is_entire_iff_left_cover R'.colA R'.colB R'.isMonicPair).mp hentR'
  have hp₂ : MonicPair R'.colA (R'.colB ≫ snd) := by
    intro W u v hua hub
    -- hua : u ≫ R'.colA = v ≫ R'.colA,  hub : u ≫ (R'.colB ≫ snd) = v ≫ (R'.colB ≫ snd).
    -- fst-coordinates agree by pinning; together with snd, R'.colB-coords agree ⟹ R'.isMonicPair.
    have hfst : (u ≫ R'.colB) ≫ fst = (v ≫ R'.colB) ≫ fst := by
      calc (u ≫ R'.colB) ≫ fst = u ≫ (R'.colB ≫ fst) := Cat.assoc _ _ _
        _ = u ≫ (R'.colA ≫ f₁) := by rw [hpin]
        _ = (u ≫ R'.colA) ≫ f₁ := (Cat.assoc _ _ _).symm
        _ = (v ≫ R'.colA) ≫ f₁ := by rw [hua]
        _ = v ≫ (R'.colA ≫ f₁) := Cat.assoc _ _ _
        _ = v ≫ (R'.colB ≫ fst) := by rw [hpin]
        _ = (v ≫ R'.colB) ≫ fst := (Cat.assoc _ _ _).symm
    have hsnd : (u ≫ R'.colB) ≫ snd = (v ≫ R'.colB) ≫ snd := by
      rw [Cat.assoc, Cat.assoc]; exact hub
    have hcolB : u ≫ R'.colB = v ≫ R'.colB := by
      rw [pair_eta (u ≫ R'.colB), pair_eta (v ≫ R'.colB), hfst, hsnd]
    exact R'.isMonicPair u v hua hcolB
  let R'₂ : BinRel 𝒞 A B₂ := BinRel.mk R'.src R'.colA (R'.colB ≫ snd) hp₂
  have hentR'₂ : Entire R'₂ :=
    (tabulated_is_entire_iff_left_cover R'.colA (R'.colB ≫ snd) hp₂).mpr hR'cov
  -- (5) Choice B₂ extracts f₂ with a single witness w : A → R'.src.
  obtain ⟨f₂, w, hwA, hwB⟩ := h₂ R'₂ hentR'₂
  -- hwA : w ≫ R'.colA = id_A,  hwB : w ≫ (R'.colB ≫ snd) = f₂.
  -- (6) w ≫ R'.colB = pair f₁ f₂  (snd by hwB, fst by pinning + hwA).
  have hwBfull : w ≫ R'.colB = pair f₁ f₂ := by
    rw [pair_eta (w ≫ R'.colB)]
    congr 1
    · -- w ≫ R'.colB ≫ fst = w ≫ R'.colA ≫ f₁ = f₁.
      calc (w ≫ R'.colB) ≫ fst = w ≫ (R'.colB ≫ fst) := Cat.assoc _ _ _
        _ = w ≫ (R'.colA ≫ f₁) := by rw [hpin]
        _ = (w ≫ R'.colA) ≫ f₁ := (Cat.assoc _ _ _).symm
        _ = f₁ := by rw [hwA, Cat.id_comp]
    · calc (w ≫ R'.colB) ≫ snd = w ≫ (R'.colB ≫ snd) := Cat.assoc _ _ _
        _ = f₂ := hwB
  -- (7) transport the witness into R.src via R' ⊂ R, giving ⟨f₁,f₂⟩ ⊂ R.
  obtain ⟨k, hkA, hkB⟩ := intersect_le_left R (graph f₁ ⊚ (graph fst)°)
  refine ⟨pair f₁ f₂, w ≫ k, ?_, ?_⟩
  · calc (w ≫ k) ≫ R.colA = w ≫ (k ≫ R.colA) := Cat.assoc _ _ _
      _ = w ≫ R'.colA := by rw [hkA]
      _ = Cat.id A := hwA
  · calc (w ≫ k) ≫ R.colB = w ≫ (k ≫ R.colB) := Cat.assoc _ _ _
      _ = w ≫ R'.colB := by rw [hkB]
      _ = pair f₁ f₂ := hwBfull

end Choice661

/-! ## §1.662 Diaconescu's theorem in a pre-topos

  In a pre-topos, the following are equivalent:
  (1) Binary coproducts of choice objects are choice.
  (2) 1+1 is choice.
  (3) The pre-topos is boolean. -/

section Diaconescu

variable [PreTopos 𝒞] [HasBinaryCoproducts 𝒞]

/-- **§1.662**: (1) → (2): trivially, 1+1 is a coproduct of 1 and 1, and 1 is choice. -/
theorem coprod_choice_to_one_one_choice
    (h : ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
         Choice (HasBinaryCoproducts.coprod B₁ B₂)) :
    Choice (HasBinaryCoproducts.coprod (one : 𝒞) one) :=
  h one one terminator_is_choice terminator_is_choice

/-- **§1.662**: (2) → (3): 1+1 choice implies boolean.
    PROOF: The intermediate condition (2a) — every cover X∪Y=B can be
    refined to a partition X'⊆X, Y'⊆Y with X'∪Y'=B and X'∩Y'=∅ —
    is a restatement of (2) because maps B → 1+1 are partitions of B.
    (2a) is inherited by slices, so it suffices to show 𝒮(1) is boolean.
    Any U ⊆ 1 gives a pushout P = 1 +_U 1; 1+1 choice ⟹ P is a subobject
    of 1+1; 1+1 is decidable (§1.658) and so is P; U is complemented as a
    pullback of a complemented subobject.

    BLOCKER: the chain needs (a) the slice pre-topos 𝒮(1)=𝒞 inheriting condition
    (2a), (b) the pushout P = 1 +_U 1 — now a real construction via `amalgamation_lemma`
    (§1.651), whose residual is only the leg-monicity descent, (c) "pullback of a
    complemented subobject is complemented" (§1.658 complement intersection/union infra,
    not yet formalized — IsComplemented uses a placeholder intersection).  The §1.62
    disjointness lemmas (`coprod_inl_inr_disjoint_elt`, `inl_union_inr_entire`) supply the
    "maps B→1+1 are disjoint-complemented partitions" content for (2a), but the slice
    transport (a) and complement pullback-stability (c) remain genuinely absent.  Faithful
    statement; reduces to amalgamation_lemma + complement pullback-stability. -/
theorem one_one_choice_to_boolean [HasBinaryProducts 𝒞]
    (h : Choice (HasBinaryCoproducts.coprod (one : 𝒞) one)) :
    Nonempty (BooleanPreLogos 𝒞) := by
  sorry

/-- **§1.662**: (3) → (1): boolean implies binary coproducts of choice objects are choice.
    PROOF: Given S: A → B₁+B₂ entire, the subobject Dom(S∘inl°) ⊆ A is complemented
    (boolean pre-topos). The restriction of S to Dom(S∘inl°) is entire into B₁, so
    contains f₁ (B₁ choice). The restriction to the complement is entire into B₂,
    so contains f₂ (B₂ choice). Then f₁+f₂ (copairing) is a map in S.

    BLOCKER (genuine residual): "Dom(S∘inl°) ⊆ A is complemented" and "the restriction of S
    to that (complemented) subobject is entire into B₁" require a relation domain/restriction
    operator (`Dom`, not yet defined in this repo) and the §1.658 complement infrastructure
    (`IsComplemented` currently a placeholder; complement pullback-stability absent).  The
    §1.563 modular gluing is now AVAILABLE (`modular_identity` proven; cf. the sorry-free
    `entire_refine`/`prod_choice_is_choice` above), so the only remaining gap is the §1.658
    complement layer + the relation-domain operator.  Faithful statement; reduces to those. -/
theorem boolean_to_coprod_choice_is_choice [HasBinaryProducts 𝒞]
    (hbool : Nonempty (BooleanPreLogos 𝒞)) :
    ∀ (B₁ B₂ : 𝒞), Choice B₁ → Choice B₂ →
      Choice (HasBinaryCoproducts.coprod B₁ B₂) := by
  sorry

end Diaconescu

end Freyd
