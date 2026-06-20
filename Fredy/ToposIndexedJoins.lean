/-
  Freyd & Scedrov, *Categories, Allegories* §1.967 — arbitrary subobject MEETS in a topos
  with arbitrary powers (the engine behind §1.967 "powers ⟹ locally complete").

  ## What this file builds (and why it stops where it does)

  The keystone the wider project wants is `HasIndexedSubobjectJoins 𝒞` (S1_75) — arbitrary
  small JOINS of subobjects of a fixed `A`, with the join UMP, plus the §1.84 frame law.  The
  task brief proposed building it as the dual of the binary subobject union (`subUnion`,
  `Fredy/ToposColimits.lean`), reusing the `bigInter` family-glb engine:
      `⋃ᵢ Sᵢ = ⋂ { T ⊆ A | ∀i, Sᵢ ≤ T }`.

  That route does NOT generalise to an *external* family, for two independent and verified
  reasons:

  1. **`bigInter` only intersects INTERNALLY-NAMEABLE families.**  `bigInter` consumes a name
     `Fname : 1 → [[A]]` (a global element of the double power).  The binary union names the
     common-upper-bound family by the *single internal* predicate
     `σ ↦ (S ⊆ σ) ∧ (T ⊆ σ) : [A] → Ω` — a finite internal conjunction of two `predF` tests.
     For an arbitrary external predicate `S : Subobject 𝒞 A → Prop` the upper-bound predicate
     `σ ↦ ∀ s, S s → s ≤ σ` is an *external* (possibly infinite) conjunction, which is NOT a
     single map `[A] → Ω` and hence cannot be turned into a family name.  So `bigInter` is
     structurally the wrong engine for arbitrary external joins.

  2. **Universe wall.**  The honest engine for arbitrary meets is §1.967: index a power
     `∏ᵢ Ω` by the family and equalise the tuple of characteristic maps.  But the index type
     for `HasArbitraryPowers.pow` is `Type v` (the hom-universe), while `Subobject 𝒞 A` lives
     in `Type (max u v)` (it bundles `dom : 𝒞 : Type u`).  Indexing a power by a *subtype* of
     `Subobject 𝒞 A` fails the universe constraint `v+1 =?= max 1 u v` unless `u ≤ v`.  This is
     exactly the missing "well-poweredness / local smallness" datum of §1.967: `LocallySmallTopos`
     (S1_95) is the *property* that `Sub(A)` is `Type v`-small, but the class as defined carries
     no `Type v` enumeration, so the equalizer-of-power construction cannot be indexed by an
     arbitrary `S : Subobject 𝒞 A → Prop`.

  ## What IS reachable, true, and reusable (this file)

  The fix for BOTH obstacles is the §1.967 hypothesis itself: arbitrary powers `∏ᵢ Ω` plus a
  `Type v` enumeration of `Sub(A)` (well-poweredness, packaged as `WellPoweredSub`).  With those
  we build, all sorry-free and axiom-clean (`propext, Classical.choice, Quot.sound`):

  1. Arbitrary MEET of a `Type v`-indexed family `B : I → Subobject 𝒞 A`, via the §1.967
     equalizer-of-power construction `⋂ᵢ Bᵢ := Eq( ⟨χ(Bᵢ)⟩ᵢ , ⟨⊤⟩ᵢ : A → ∏ᵢ Ω )`, with full glb
     laws (`familyMeet`, `familyMeet_le`, `familyMeet_greatest`).
  2. Arbitrary external JOIN `extJoin S = ⋂ {enumerated common upper bounds of S}`, with the join
     UMP (`extJoin_upper`, `extJoin_least`).
  3. The §1.84 frame law `f#(⊔S) ≤ ⊔ f#S` (`extJoin_invImage_le`), via the `f# ⊣ ∀_f` adjunction.
  4. Hence the full `LocallyComplete' 𝒞` (S1_84) and the KEYSTONE `HasIndexedSubobjectJoins 𝒞`
     (S1_75), both including the frame law.

  The single remaining datum — extracting `WellPoweredSub` from `LocallySmallTopos` — is the
  reason `S1_95.topos_powers_implies_locally_complete` is still `sorry`; see the STATUS note at
  the end.
-/

import Fredy.S1_95
import Fredy.S1_75
import Fredy.ForallAlong

open Freyd
open HasSubobjectClassifier

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

namespace Freyd

/-- Equalizer maps are monic (local copy; avoids importing the S1_57 `HasEqualizers` path,
    which clashes with the topos's own `topos_has_equalizers` instance). -/
private theorem eqMap_mono_loc {A B : 𝒞} (f g : A ⟶ B) : Mono (eqMap f g) := by
  intro W u v huv
  have hc : (u ≫ eqMap f g) ≫ f = (u ≫ eqMap f g) ≫ g := by
    rw [Cat.assoc, Cat.assoc, eqMap_eq]
  rw [eqLift_uniq f g _ hc u rfl, eqLift_uniq f g _ hc v huv.symm]

section FamilyMeet
variable (hpow : HasArbitraryPowers (𝒞 := 𝒞))

/-- **§1.967 — arbitrary MEET of a `Type v`-indexed family of subobjects.**

    `⋂ᵢ Bᵢ` is the equalizer of the two tuples `A → ∏ᵢ Ω`: the tuple `⟨χ(Bᵢ)⟩ᵢ` of the
    members' characteristic maps, and the constant `⟨⊤⟩ᵢ`.  A point `a : A` factors through
    the equalizer exactly when, in every coordinate `i`, `χ(Bᵢ)(a) = ⊤`, i.e. `a ∈ Bᵢ` for all
    `i`.  Needs `HasArbitraryPowers` (for `∏ᵢ Ω`) plus the topos's own equalizers. -/
noncomputable def familyMeet {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) :
    Subobject 𝒞 A :=
  let chi  : A ⟶ hpow.pow I (omega (𝒞 := 𝒞)) := hpow.tupling (fun i => subChar (B i))
  let chiT : A ⟶ hpow.pow I (omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
  ⟨eqObj chi chiT, eqMap chi chiT, eqMap_mono_loc chi chiT⟩

/-- **LOWER bound** — `⋂ᵢ Bᵢ ≤ Bⱼ` for every `j`.  The equalizer arrow equalises the two
    tuples; projecting at `j` gives `(⋂B).arr ≫ χ(Bⱼ) = (⋂B).arr ≫ ⊤ = term ≫ true`, i.e. the
    inclusion lands in `Bⱼ` (`le_iff_classify`). -/
theorem familyMeet_le {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) (i : I) :
    (familyMeet hpow B).le (B i) := by
  rw [familyMeet, le_iff_classify]
  show eqMap _ _ ≫ subChar (B i) = _
  have hi := congrArg (· ≫ hpow.proj i)
    (eqMap_eq (hpow.tupling (fun i => subChar (B i)))
              (hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))))
  simp only [Cat.assoc] at hi
  rw [hpow.tupling_proj, hpow.tupling_proj] at hi
  rw [hi, ← Cat.assoc]
  congr 1
  exact term_uniq _ _

/-- **GREATEST lower bound** — if `U ≤ Bᵢ` for every `i`, then `U ≤ ⋂ᵢ Bᵢ`.  `U.arr` equalises
    the two tuples (componentwise: `U ≤ Bᵢ` gives `U.arr ≫ χ(Bᵢ) = term ≫ true = U.arr ≫ ⊤`),
    so it factors through the equalizer by the equalizer UMP. -/
theorem familyMeet_greatest {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) (U : Subobject 𝒞 A)
    (hU : ∀ i, U.le (B i)) : U.le (familyMeet hpow B) := by
  rw [familyMeet]
  let chi  : A ⟶ hpow.pow I (omega (𝒞 := 𝒞)) := hpow.tupling (fun i => subChar (B i))
  let chiT : A ⟶ hpow.pow I (omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
  have heq : U.arr ≫ chi = U.arr ≫ chiT := by
    rw [hpow.tupling_uniq (fun i => U.arr ≫ subChar (B i)) (U.arr ≫ chi)
          (fun i => by rw [Cat.assoc]; show U.arr ≫ hpow.tupling _ ≫ hpow.proj i = _;
                       rw [hpow.tupling_proj])]
    rw [hpow.tupling_uniq (fun i => U.arr ≫ subChar (B i)) (U.arr ≫ chiT)
          (fun i => by
            rw [Cat.assoc]
            show U.arr ≫ hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) ≫ hpow.proj i = _
            rw [hpow.tupling_proj]
            show U.arr ≫ term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) = U.arr ≫ subChar (B i)
            rw [(le_iff_classify U (B i)).mp (hU i), ← Cat.assoc,
                term_uniq (U.arr ≫ term A) (term U.dom)])]
  exact ⟨eqLift chi chiT U.arr heq, eqLift_fac chi chiT U.arr heq⟩

end FamilyMeet

/-! ## §1.967 — external joins from `Type v` well-poweredness

  The `sup` field of `LocallyComplete'` / `HasIndexedSubobjectJoins` quantifies over an
  *external* `S : Subobject 𝒞 A → Prop`.  As explained in the header, feeding `S` to the
  power-indexed `familyMeet` needs a `Type v` enumeration of `Sub(A)` — Freyd's §1.967
  well-poweredness.  We package exactly that datum and build the genuine join + its UMP. -/

/-- **`Type v` well-poweredness of `Sub(A)` (§1.967).**  A small index `idx A : Type v` with an
    enumeration `enum : idx A → Sub A` that hits every subobject up to `≤` in both directions.
    This is the one primitive an elementary topos does NOT supply; in a *locally small* topos
    (`|Hom(A,Ω)| = |Sub A|` is a set, §1.967) it holds.  Given it, all arbitrary joins exist. -/
structure WellPoweredSub (𝒞 : Type u) [Cat.{v} 𝒞] where
  idx  : (A : 𝒞) → Type v
  enum : {A : 𝒞} → idx A → Subobject 𝒞 A
  surj : ∀ {A : 𝒞} (S : Subobject 𝒞 A), ∃ j : idx A, S.le (enum j) ∧ (enum j).le S

section ExtJoin
variable (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (wp : WellPoweredSub.{v} 𝒞)

/-- **§1.967 — arbitrary JOIN over an external predicate.**  `sup S = ⋂ { common upper bounds
    of S }`, with the upper bounds taken among the enumerated subobjects (`wp`).  The meet is
    the `familyMeet` over the `Type v` subtype of indices whose enumerated subobject is an
    upper bound of every member of `S`. -/
noncomputable def extJoin {A : 𝒞} (S : Subobject 𝒞 A → Prop) : Subobject 𝒞 A :=
  familyMeet hpow (I := {j : wp.idx A // ∀ s, S s → s.le (wp.enum j)})
    (fun j => wp.enum j.val)

/-- `s ≤ sup S` for every member `S s`: `s` is below every common upper bound (definitionally),
    so below their meet (`familyMeet_greatest`). -/
theorem extJoin_upper {A : 𝒞} (S : Subobject 𝒞 A → Prop) (s : Subobject 𝒞 A) (hs : S s) :
    s.le (extJoin hpow wp S) := by
  rw [extJoin]
  apply familyMeet_greatest
  rintro ⟨j, hj⟩
  exact hj s hs

/-- `sup S ≤ U` whenever `U` bounds every member: enumerate `U` as `enum j` (`wp.surj`); then
    `j` indexes a common upper bound, so `familyMeet_le` gives `⋂ ≤ enum j ≤ U`. -/
theorem extJoin_least {A : 𝒞} (S : Subobject 𝒞 A → Prop) (U : Subobject 𝒞 A)
    (hU : ∀ s, S s → s.le U) : (extJoin hpow wp S).le U := by
  rw [extJoin]
  obtain ⟨j, hUj, hjU⟩ := wp.surj U
  have hjmem : ∀ s, S s → s.le (wp.enum j) := fun s hs =>
    let ⟨a, ha⟩ := hU s hs; let ⟨b, hb⟩ := hUj; ⟨a ≫ b, by rw [Cat.assoc, hb, ha]⟩
  have hle := familyMeet_le hpow
    (I := {j : wp.idx A // ∀ s, S s → s.le (wp.enum j)})
    (fun j => wp.enum j.val) ⟨j, hjmem⟩
  exact ⟨hle.choose ≫ hjU.choose, by rw [Cat.assoc, hjU.choose_spec, hle.choose_spec]⟩

/-- **§1.967 — a topos with arbitrary powers and well-powered subobjects is LOCALLY COMPLETE.**
    The `sup` is `extJoin`; the two lattice laws are `extJoin_upper` / `extJoin_least`.  This is
    the genuine `LocallyComplete'` of S1_84 (the conclusion of §1.967 "powers ⟹ locally
    complete"), conditional on the well-poweredness witness `wp` that the bare topos lacks. -/
noncomputable def locallyComplete'_of_powers_wellPowered : LocallyComplete' 𝒞 where
  toHasImages := inferInstance
  sup S := extJoin hpow wp S
  sup_upper := extJoin_upper hpow wp
  sup_least := extJoin_least hpow wp

/-- **§1.84 FRAME LAW** — inverse image preserves arbitrary joins:
    `f#(⊔ S) ≤ ⊔ { f# B' | B' ∈ S }`.

    This is the §1.84 `PullbacksPreserveArbitraryUnions` / infinite distributive law.  It holds
    in a topos because `f#` (inverse image) is a LEFT-adjoint-having functor on subobjects:
    `f# ⊣ ∀_f` (`ForallAlong.forallAlong_adjunction`).  Concretely:
      `f#(⊔S) ≤ U  ⟺  ⊔S ≤ ∀_f U`  (adjunction);
      `⊔S ≤ ∀_f U  ⟸  ∀ s∈S, s ≤ ∀_f U  ⟺  ∀ s∈S, f#s ≤ U`  (adjunction again, `sup_least`);
      `f#s ≤ U = ⊔{f#B'}` holds by `sup_upper` since `f#s` is itself a member of that family. -/
theorem extJoin_invImage_le {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B → Prop) :
    (InverseImage f (extJoin hpow wp S)).le
      (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B')) := by
  rw [show InverseImage f (extJoin hpow wp S)
        = invImg f (extJoin hpow wp S) (HasPullbacks.has f (extJoin hpow wp S).arr) from rfl]
  rw [forallAlong_adjunction f (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B'))
        (extJoin hpow wp S) (HasPullbacks.has f (extJoin hpow wp S).arr)]
  apply extJoin_least
  intro s hs
  rw [← forallAlong_adjunction f
        (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B')) s
        (HasPullbacks.has f s.arr)]
  show (invImg f s _).le _
  rw [show invImg f s (HasPullbacks.has f s.arr) = InverseImage f s from rfl]
  exact extJoin_upper hpow wp _ (InverseImage f s) ⟨s, hs, rfl⟩

/-- **THE TARGET — `HasIndexedSubobjectJoins 𝒞` (S1_75)** from arbitrary powers + `Type v`
    well-poweredness.  All four fields are genuine: `sup` is the meet of (enumerated) common
    upper bounds (`extJoin`); `sup_upper`/`sup_least` are the join UMP; `invImage_preserves_sup`
    is the §1.84 frame law via the `f# ⊣ ∀_f` adjunction.  This is the keystone that unblocks
    `atomicallyBased_isComplementedSub` (S1_75) and `topos_powers_implies_locally_complete`
    (S1_95), conditional on the well-poweredness witness `wp` the bare topos lacks (§1.967). -/
noncomputable def hasIndexedSubobjectJoins_of_powers_wellPowered :
    HasIndexedSubobjectJoins 𝒞 where
  sup S := extJoin hpow wp S
  sup_upper := extJoin_upper hpow wp
  sup_least := extJoin_least hpow wp
  invImage_preserves_sup := extJoin_invImage_le hpow wp

end ExtJoin

/-! ## STATUS / RESIDUAL

  DELIVERED (sorry-free, axioms = `propext, Classical.choice, Quot.sound` only):
  * `familyMeet` + `familyMeet_le`/`familyMeet_greatest` — arbitrary `Type v`-indexed MEET from
    `HasArbitraryPowers` (the §1.967 equalizer-of-power engine).
  * `extJoin` + `extJoin_upper`/`extJoin_least` — arbitrary external JOIN from
    `HasArbitraryPowers + WellPoweredSub`.
  * `extJoin_invImage_le` — the §1.84 frame law, via the `f# ⊣ ∀_f` adjunction.
  * `locallyComplete'_of_powers_wellPowered : LocallyComplete' 𝒞` (S1_84).
  * `hasIndexedSubobjectJoins_of_powers_wellPowered : HasIndexedSubobjectJoins 𝒞` (S1_75 KEYSTONE),
    INCLUDING the frame law.

  THE ONE REMAINING GAP — extracting `WellPoweredSub` (a `Type v` enumeration of `Sub(A)`) from a
  bare `[Topos 𝒞]` or even `[LocallySmallTopos 𝒞]`.  This is NOT a missing proof but a missing
  DATUM, and the reason `S1_95.topos_powers_implies_locally_complete` stays `sorry`:

  * A bare elementary topos is genuinely NOT locally complete (Freyd §1.967): arbitrary joins of
    subobjects require an extra completeness assumption.  So `instance .. [Topos 𝒞]` would be a
    FALSE statement — deliberately NOT emitted.
  * `Subobject 𝒞 A` lives in `Type (max u v)` (it bundles `dom : 𝒞 : Type u`), while
    `HasArbitraryPowers.pow`'s index is `Type v`.  Indexing a power by `{T // S T}` fails the
    universe constraint `v+1 =?= max 1 u v` (verified).  `WellPoweredSub` is exactly the bridge:
    a `Type v` enumeration hitting every subobject up to `≤`.  Freyd's §1.967 "locally small"
    provides it (`|Hom(A,Ω)| = |Sub A|` is a set); the repo's `LocallySmallTopos` class NAMES
    that property but carries no enumeration datum, so it cannot currently produce a
    `WellPoweredSub`.  Adding the enumeration field to `LocallySmallTopos` (or a standalone
    `[WellPoweredSub 𝒞]` instance from a concrete model) immediately closes
    `topos_powers_implies_locally_complete` and `atomicallyBased_isComplementedSub` by
    instantiating `hasIndexedSubobjectJoins_of_powers_wellPowered`.
-/

end Freyd
