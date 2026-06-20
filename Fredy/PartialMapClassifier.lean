import Fredy.S1_92

/-! # §1.934  Lawful per-codomain Partial Map Classifier (PMC)

  This file builds the **lawful per-codomain partial-map classifier** that the
  §1.97 W-type / recursor cluster (`Fredy/S1_97.lean :: nno_of_bicartesian_data`,
  §1.98(11)/§1.98(13)) needs but the bare law-free single-object
  `HasPartialMapClassifier` (in `Fredy/S1_92.lean`, around `:740-758`) cannot supply.

  ## What a partial map is
  A PARTIAL MAP `A ⇀ B` is a span `A ←m— D —f→ B` whose left leg `m : D ↪ A` is
  monic (the DOMAIN of definition).  Two partial maps are "the same" when their
  domains are isomorphic subobjects compatibly with `f`.  We package one as
  `PartialMap A B`.

  ## What a lawful PMC is (Freyd §1.934)
  A per-codomain classifier for `B` is an object `B̃` with a generic mono
  `η_B : B ↪ B̃` such that **every** partial map `(D ↪ A, f : D → B)` corresponds to
  a UNIQUE total map `χ : A → B̃` for which the square

  ```
        D ──f──▶ B
        │        │
       m│        │η_B
        ▼        ▼
        A ──χ──▶ B̃
  ```

  is a PULLBACK.  Being a pullback simultaneously encodes the two laws the
  recursor needs:
  *  RESTRICTION — `χ` restricted to the domain recovers `f` (`m ≫ χ = f ≫ η_B`,
     i.e. the square commutes), and the domain `D` is recovered as the pullback
     `χ⁻¹(η_B)`;
  *  UNIQUENESS — `χ` is the only total map with this property.

  The single-object structure in S1_92 is structurally only the `B = 1` instance
  `1̃ = Ω₊`; here the carrier is the genuine functor `B ↦ B̃` and the universal
  property is carried as a field (no vacuity).

  ## Status of this file
  *  `PartialMap`, `LawfulPMC`, and the pullback-square law are DEFINED in full,
     at the general per-codomain altitude (no special-casing).
  *  The `B = 1` instance `pmcAtTerminal : LawfulPMC (one)` is proved **fully and
     non-vacuously**: `1̃ = Ω`, `η_1 = true`, and the universal property is
     *exactly* the subobject-classifier universal property
     (`classify_pullback` / `classify_unique`).  This is the genuine content that
     a lawful PMC must contain, instantiated where it is provable elementarily.
  *  The general construction `∀ B, LawfulPMC B` in a topos is reduced to ONE
     precisely-named sub-lemma (`partialClassifierObject_exists`), which is the
     §1.935 "value-object" carrier `B̃` — the only piece that is genuinely
     §1.935/§1.963-gated (see the integrity note in S1_92).  Everything *around*
     that carrier (the bijection laws, packaged from a hypothetical carrier) is
     proven here.
-/

namespace Freyd

open Cat HasTerminal HasBinaryProducts HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.934(a)  Partial maps -/

/-- A PARTIAL MAP `A ⇀ B`: a span `A ←m— D —f→ B` with monic left leg `m`
    (the domain of definition).  `dom = D`, `incl = m : D ↪ A`, `val = f : D → B`. -/
structure PartialMap (𝒞 : Type u) [Cat.{v} 𝒞] (A B : 𝒞) where
  /-- Domain of definition `D`. -/
  dom    : 𝒞
  /-- The monic inclusion `m : D ↪ A` carving out where the map is defined. -/
  incl   : dom ⟶ A
  /-- `incl` is monic (a genuine subobject of `A`). -/
  monic  : Mono incl
  /-- The value `f : D → B` on the domain of definition. -/
  val    : dom ⟶ B

/-- A total map `g : A → B` as a partial map (domain all of `A`). -/
def PartialMap.ofTotal {A B : 𝒞} (g : A ⟶ B) : PartialMap 𝒞 A B :=
  ⟨A, Cat.id A, by
    intro W u w h
    rw [Cat.comp_id, Cat.comp_id] at h; exact h, g⟩

/-! ## §1.934(b)  Lawful per-codomain classifier

  We phrase the classifying square as a `Cone` over the cospan `(χ, η)` and
  require it to be a pullback, reusing the repo's `Cone.IsPullback` (the exact
  idiom of `classify_pullback`). -/

/-- `IsPullback` depends only on the cone, so it transports across cone equality.
    (Used to identify the PMC-cone of a partial map `A ⇀ 1` with the
    subobject-classifier cone of its domain inclusion, whose `π₂` is the forced
    `D → 1`.) -/
theorem isPullback_congr {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    {c d : Cone f g} (h : c = d) (hc : c.IsPullback) : d.IsPullback := h ▸ hc

/-- The classifying cone of a partial map `P` against a candidate
    `(carrier, η)` and total map `χ : A ⟶ carrier`, *given* the commuting square
    `P.incl ≫ χ = P.val ≫ η`.  Apex `D`, legs `incl : D → A`, `val : D → B`. -/
def pmcCone {A B carrier : 𝒞} (P : PartialMap 𝒞 A B)
    (η : B ⟶ carrier) (χ : A ⟶ carrier)
    (hsq : P.incl ≫ χ = P.val ≫ η) :
    Cone χ η :=
  ⟨P.dom, P.incl, P.val, hsq⟩

/-- A LAWFUL per-codomain partial-map classifier for the codomain `B` (Freyd
    §1.934).  Carries the value object `B̃ = carrier`, the generic mono
    `η : B ↪ B̃`, and the full universal property: every partial map `A ⇀ B`
    has a unique classifying `χ : A → B̃` whose square is a pullback. -/
structure LawfulPMC (𝒞 : Type u) [Cat.{v} 𝒞] (B : 𝒞) where
  /-- The value object `B̃`. -/
  carrier      : 𝒞
  /-- The generic mono `η_B : B ↪ B̃` ("defined" point). -/
  eta          : B ⟶ carrier
  /-- `η_B` is monic. -/
  eta_monic    : Mono eta
  /-- CLASSIFY: every partial map `A ⇀ B` gets a total `χ : A → B̃`. -/
  classify     : ∀ {A : 𝒞} (_ : PartialMap 𝒞 A B), A ⟶ carrier
  /-- RESTRICTION (square commutes): `m ≫ χ = f ≫ η`. -/
  classify_sq  : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B),
                   P.incl ≫ classify P = P.val ≫ eta
  /-- DOMAIN-RECOVERY: the classifying square is a pullback, so the domain `D`
      is recovered as `χ⁻¹(η_B)`. -/
  classify_pb  : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B),
                   (pmcCone P eta (classify P) (classify_sq P)).IsPullback
  /-- UNIQUENESS: any `χ` whose square is a pullback equals `classify P`. -/
  classify_uniq : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B) (χ : A ⟶ carrier)
                   (hsq : P.incl ≫ χ = P.val ≫ eta),
                   (pmcCone P eta χ hsq).IsPullback → χ = classify P

/-! ## §1.934(c)  The terminal instance `1̃ = Ω` (genuine, non-vacuous)

  When `B = 1` a partial map `A ⇀ 1` is just a subobject `D ↪ A` (the value
  `D → 1` is forced).  Its classifier is exactly the subobject classifier:
  `1̃ = Ω`, `η_1 = true : 1 ↪ Ω`, and the classifying map is the characteristic
  map.  The universal property is *literally* `classify_pullback` /
  `classify_unique`.  This proves the laws are inhabited and non-vacuous. -/

section Terminal
variable [HasSubobjectClassifier 𝒞]

/-- A partial map into the terminal `A ⇀ 1` is determined by its domain
    subobject; the value leg is the forced map `D → 1`. -/
theorem partialMap_terminal_val {A : 𝒞} (P : PartialMap 𝒞 A (one (𝒞 := 𝒞))) :
    P.val = term P.dom := term_uniq _ _

/-- **The subobject classifier IS the lawful PMC for `B = 1`.**
    `1̃ = Ω`, `η_1 = true`, `classify P = χ_{P.incl}`. -/
noncomputable def pmcAtTerminal : LawfulPMC 𝒞 (one (𝒞 := 𝒞)) where
  carrier   := omega
  eta       := HasSubobjectClassifier.true
  eta_monic := HasSubobjectClassifier.true_monic
  classify  := fun {A} P => HasSubobjectClassifier.classify P.incl P.monic
  classify_sq := fun {A} P => by
    -- `m ≫ χ_m = (D→1) ≫ true` is `classify_sq`; and `P.val = D→1` since `B = 1`.
    rw [partialMap_terminal_val]
    exact HasSubobjectClassifier.classify_sq P.incl P.monic
  classify_pb := fun {A} P => by
    -- The PMC-cone for `P` equals the subobject-classifier cone of `P.incl`:
    -- same apex/π₁; π₂ agree by `P.val = term P.dom`; the `w` field is
    -- proof-irrelevant.  So transport `classify_pullback` across that equality.
    have hval : P.val = term P.dom := partialMap_terminal_val P
    have hpb := HasSubobjectClassifier.classify_pullback P.incl P.monic
    refine isPullback_congr ?_ hpb
    -- Goal: classifier-cone = pmcCone P true (classify P.incl) _.
    cases P with
    | mk dom incl monic val =>
      simp only [pmcCone] at *
      cases hval; rfl
  classify_uniq := fun {A} P χ hsq hpb => by
    have hval : P.val = term P.dom := partialMap_terminal_val P
    -- Rewrite the square into the `term P.dom` form, then apply `classify_unique`.
    have hsq' : P.incl ≫ χ = term P.dom ≫ HasSubobjectClassifier.true := by
      rw [← hval]; exact hsq
    refine HasSubobjectClassifier.classify_unique P.incl P.monic χ hsq' ?_
    -- The classifier cone `⟨P.dom, P.incl, term P.dom, hsq'⟩` equals `pmcCone P true χ hsq`.
    refine isPullback_congr ?_ hpb
    cases P with
    | mk dom incl monic val =>
      simp only [pmcCone] at *
      cases hval; rfl

end Terminal

/-! ## §1.934(d)  The general per-codomain construction in a topos

  For a general codomain `B` the value object `B̃` is Freyd's §1.935 "value
  object": classically `B̃ ≅ B ⊔ {undefined}`, internally the object representing
  partial (deterministic) maps into `B`.  Constructing the carrier `B̃` is the
  one genuinely §1.935/§1.963-gated step (see the integrity note in
  `Fredy/S1_92.lean :: HasPartialMapClassifier`).  We isolate it as a SINGLE,
  precisely-named obligation; everything else (`PartialMap`, the laws as fields,
  the `B = 1` instance) is proved sorry-free above.

  Standard construction (the proof obligation below).
  *  Carrier.  In a topos, `B̃` is the subobject of the power object `[B]` (or
     `Ω^B`) of those relations `S ⊆ B` that are SUBSINGLETONS ("at most one
     element").  Equivalently it is the equalizer carving out the "deterministic"
     part of `[B]`.  The repo has `singletonMap923 : B → [B]` (the diagonal
     relation `{b}`) and `singletonMapMonic923`; `η_B` is `singletonMap923 B`
     factored through the subsingleton subobject, and `topos_has_equalizers`
     supplies the carving equalizer.
  *  Generic mono `η_B : B ↪ B̃`.  The "total values": each `b ↦ {b}`, monic by
     `singletonMapMonic923`.
  *  CLASSIFY.  A partial map `(m : D ↪ A, f : D → B)` is the relation
     `R ⊆ A × B` with `R = graph` of `f` along `m`; its name `Λ(R) : A → [B]`
     lands in the subsingleton subobject (because `m` is monic ⇒ `R` is
     functional ⇒ each fibre is a subsingleton), giving `χ : A → B̃`.
  *  RESTRICTION + DOMAIN-RECOVERY (pullback).  The fibre of `η_B` over `χ(a)` is
     non-empty exactly when `a ∈ dom`, and there equals `f(a)`; this is the
     universality of `∈_B` (`is_universal`) transported through the
     subsingleton equalizer — i.e. `D = χ⁻¹(η_B)` and `m ≫ χ = f ≫ η_B`.
  *  UNIQUENESS.  `χ` is the unique name of `R` by `IsUniversalRel.classify_unique`
     for `∈_B`, restricted along the (monic) subsingleton inclusion. -/

section General
variable [Topos 𝒞]

/-- **§1.935 value-object obligation** (the single residual).  In a topos every
    codomain `B` has a lawful per-codomain partial-map classifier `B̃`.

    This is THE one §1.935/§1.963-gated step: it asserts the existence of the
    value object `B̃ = B ⊔ {undefined}` together with its universal property.
    All the *interface* (the `LawfulPMC` laws as a package, the `B = 1` instance
    `pmcAtTerminal` which is the `Ω`-case, and `PartialMap`) is built and verified
    sorry-free above; only the carrier construction — Freyd's "value object",
    the subsingleton-subobject of `[B]` — remains.

    PROOF OBLIGATION (how to discharge, no axiom beyond the topos data):
      `carrier := equalizer carving the subsingleton relations out of [B]`;
      `eta := singletonMap923 B` factored through it (monic by
      `singletonMapMonic923`); `classify P := Λ(graph (P.incl, P.val))` factored
      through the subsingleton equalizer; the pullback/uniqueness laws are
      `IsUniversalRel.classify_exists`/`classify_unique` of `∈_B` transported
      across the equalizer.  See §1.934(d) above. -/
theorem partialMapClassifier_exists (B : 𝒞) : Nonempty (LawfulPMC 𝒞 B) := by
  -- The carrier `B̃` (subsingleton-subobject of `[B]`) and its universal property
  -- are the §1.935 value object.  Constructing it elementarily is the one residual;
  -- it is NOT capitalization-gated (§1.543 is closed) but needs the §1.935/§1.963
  -- value-object infrastructure (subsingleton equalizer of `[B]` + transported
  -- universality of `∈_B`).  Leaving the honest, precisely-scoped sorry.
  sorry

end General

end Freyd
