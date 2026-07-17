/-
  Freyd & Scedrov, *Categories and Allegories* — INITIAL and STRICT INITIAL objects.

  Dual of the terminal-object development (§1.421, `IsTerminalObj` in `Horn.lean`,
  `HasTerminal` in `S1_42.lean`).  This is basic categorical infrastructure needed by
  §1.474 (where `0 := zeroObj` must be *initial* for `B×0 → 0` to be an iso) and
  elsewhere; it is NOT §1.543-gated.

  The structural class for an initial object already exists in the repo as
  `HasCoterminator` (S1_58.lean, dual of `HasTerminal`), together with the
  `StrictCoterminator` predicate and the §1.58¶2 facts.  To stay DRY we do NOT
  redefine that class.  What is genuinely new — and what §1.474 actually needs — is
  the *predicate*-level API:

    * `IsInitial X`        — the universal property "unique map out of `X`", a
                             predicate on an object (dual of `IsTerminalObj`), so it
                             can be asserted of a specific object such as `zeroObj`;
    * `IsStrictInitial X`  — `IsInitial X` together with strictness (every map *into*
                             `X` is an iso);
    * the basic lemmas (map-out unique, initial→initial iso, initial unique up to
                       iso, the dual of `terminator_unique_iso`); and
    * bridges `HasCoterminator → IsInitial coterm`, `StrictCoterminator → IsInitial`
      (via the existing §1.58¶2 proof, hence the binary-products hypothesis).
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_58

open CategoryTheory Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ### The INITIAL predicate

  An object `X` is INITIAL when every object `Y` receives a unique map from `X`.
  This is the exact dual of `IsTerminalObj` (`Horn.lean`):
  `IsTerminalObj o := ∀ X, ∃ f : X ⟶ o, ∀ g : X ⟶ o, g = f`. -/

/-- The INITIAL predicate in `𝒞`: every object receives a unique map from `o`
    (dual of `IsTerminalObj`). -/
def IsInitial (o : 𝒞) : Prop := ∀ Y : 𝒞, ∃ f : o ⟶ Y, ∀ g : o ⟶ Y, g = f

/-- The canonical map out of an initial object (dual of `term`). -/
noncomputable def IsInitial.out {o : 𝒞} (ho : IsInitial o) (Y : 𝒞) : o ⟶ Y :=
  (ho Y).choose

/-- Any two maps out of an initial object are equal (dual of `term_uniq`). -/
theorem IsInitial.hom_uniq {o : 𝒞} (ho : IsInitial o) {Y : 𝒞} (f g : o ⟶ Y) : f = g :=
  (ho Y).choose_spec f |>.trans ((ho Y).choose_spec g).symm

/-! ### §1.421 (dual) Initial object unique up to unique iso

  Dual of `terminator_unique_iso`: the unique map between two initial objects is an
  iso. -/

/-- Two initial objects are isomorphic: the canonical map `o₁ → o₂` is an iso
    (dual of: terminators are isomorphic). -/
theorem IsInitial.iso {o₁ o₂ : 𝒞} (h₁ : IsInitial o₁) (h₂ : IsInitial o₂) :
    IsIso (h₁.out o₂) :=
  ⟨h₂.out o₁, h₁.hom_uniq _ _, h₂.hom_uniq _ _⟩

/-! ### Bridge to the structural class `HasCoterminator`

  `HasCoterminator` is the repo's structural witness of an initial object (S1_58.lean).
  Its `zero` object is initial in the predicate sense, and conversely an instance can
  be built from `IsInitial` (mirroring how `HasTerminal` packages `IsTerminalObj`). -/

/-- The coterminator object of a `HasCoterminator` instance is initial. -/
theorem HasCoterminator.coterm_isInitial [HasCoterminator 𝒞] : IsInitial (coterm : 𝒞) :=
  fun Y => ⟨zeroMap Y, fun g => HasCoterminator.init_uniq g (zeroMap Y)⟩

/-- An object satisfying `IsInitial` packages into a `HasCoterminator` instance
    (dual of how a terminator packages `HasTerminal`).  `noncomputable` because the
    map out is extracted from the `∃` via choice, exactly as for the §1.58 bridge. -/
noncomputable def IsInitial.hasCoterminator {o : 𝒞} (ho : IsInitial o) : HasCoterminator 𝒞 where
  zero := o
  init Y := ho.out Y
  init_uniq f g := ho.hom_uniq f g

/-! ### STRICT INITIAL objects

  An initial object `0` is STRICT when every morphism *into* `0` is an isomorphism
  (Freyd §1.58¶2, stated there for the coterminator as `StrictCoterminator`).  We
  package strictness together with initiality as `IsStrictInitial`, and record the
  hypothesis-free strictness consequences (improper subobjects, entire equalizers)
  plus the §1.58¶2 derivation that strictness *implies* initiality in any category
  with binary products. -/

/-- An object `o` is STRICT INITIAL when it is initial and every morphism targeted at
    `o` is an isomorphism. -/
def IsStrictInitial (o : 𝒞) : Prop := IsInitial o ∧ StrictCoterminator o

theorem IsStrictInitial.isInitial {o : 𝒞} (h : IsStrictInitial o) : IsInitial o := h.1

theorem IsStrictInitial.strict {o : 𝒞} (h : IsStrictInitial o) : StrictCoterminator o := h.2

/-- **Strictness, hypothesis-free.**  Every equalizer targeted at a strict initial
    object is entire (its inclusion is an iso).  Reuses
    `strictCoterminator_equalizer_entire`. -/
theorem IsStrictInitial.equalizer_entire {o B : 𝒞} (h : IsStrictInitial o)
    {f g : o ⟶ B} (c : EqualizerCone f g) : IsIso c.map :=
  strictCoterminator_equalizer_entire h.2 c


/-- **§1.58¶2.**  In any category with binary products, a strict coterminator is
    initial.  The map out is `fst⁻¹ ≫ snd : Z → A` (with `fst : Z×A → Z` an iso since
    targeted at `Z`), and `strictCoterminator_hom_unique` forces it to be unique.
    `noncomputable`: extracting the iso-inverse needs choice, as in §1.58. -/
theorem StrictCoterminator.isInitial [HasBinaryProducts 𝒞] {Z : 𝒞}
    (hZ : StrictCoterminator Z) : IsInitial Z :=
  fun A => ⟨(hZ (fst : prod Z A ⟶ Z)).choose ≫ snd,
            fun g => strictCoterminator_hom_unique hZ g _⟩

/-- **§1.58¶2.**  In a category with binary products, a strict coterminator is a
    *strict initial* object (it is strict by hypothesis and initial by the previous
    lemma). -/
theorem StrictCoterminator.isStrictInitial [HasBinaryProducts 𝒞] {Z : 𝒞}
    (hZ : StrictCoterminator Z) : IsStrictInitial Z :=
  ⟨hZ.isInitial, hZ⟩

end Freyd
