/-
  §1.635 — the STALK FAMILY collective conservativity (toward §2.218).

  Freyd represents a capital positive pre-logos in a POWER of `Set` via the family of stalks
  `{T_F̂}` over ultra-filters `F̂` of complemented subterminators.  The family is COLLECTIVELY
  faithful (Freyd §1.635:239-253): given a proper subobject, SOME ultra-filter's stalk keeps it
  proper.  No single stalk reflects isos — that needs full well-pointedness, which the
  capitalization does NOT give; the family does not.

  This file builds the collective-conservativity ingredients.  First brick: the stalk evaluated
  on a SUBTERMINATOR `V` is inhabited iff `V` is in the filter (`TF_subterminator_nonempty`) —
  the bridge between the geometric "stalk" and the combinatorial "ultra-filter membership" that
  Freyd's separation argument turns on. -/
import Fredy.S1_75

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [PreLogos 𝒞]

/-- **Stalk of a subterminator = filter membership.**  For a FILTER `ℱ` (upward-closed) and a
    subterminator `V : Subobject 𝒞 one`, the stalk `T_ℱ(V.dom)` is inhabited iff `V ∈ ℱ`.

    `←`: `V ∈ ℱ` names the identity `V.dom → V.dom`.  `→`: a name `a : U.dom → V.dom` with `U ∈ ℱ`
    forces `U ≤ V` (both `U.dom, V.dom` map uniquely to the terminator `one`, so `a ≫ V.arr =
    U.arr`), and upward-closure lifts `U ∈ ℱ` to `V ∈ ℱ`. -/
theorem TF_subterminator_nonempty (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsFilter ℱ)
    (V : Subobject 𝒞 one) : Nonempty (TF ℱ V.dom) ↔ ℱ V := by
  constructor
  · rintro ⟨t⟩
    obtain ⟨⟨U, hU, a⟩, -⟩ := Quot.exists_rep t
    exact hℱ.2 U V hU ⟨a, term_uniq _ _⟩
  · intro hV
    exact ⟨TF.mk ℱ ⟨V, hV, Cat.id V.dom⟩⟩

variable [HasBinaryCoproducts 𝒞]

/-- **§1.635 detection at the stalk level.**  A PROPER complemented subterminator `V` (≠ `1`) is
    killed by SOME ultra-filter stalk: there is an ultra-filter `ℱ` with `T_ℱ(V.dom)` EMPTY.

    This is `exists_ultrafilter_excluding` (§1.635:253) read through the stalk: the excluding
    ultra-filter omits `V`, and a name `U.dom → V.dom` from a member `U ∈ ℱ` would force `V ∈ ℱ`
    (`ultrafilter_isFilter` up-closure to the complemented `V`), a contradiction. -/
theorem exists_stalk_empty_of_proper (V : Subobject 𝒞 one) (hVcomp : IsComplementedSub V)
    (hVproper : ¬ (Subobject.entire one).le V) :
    ∃ ℱ, IsUltraFilter ℱ ∧ ¬ Nonempty (TF ℱ V.dom) := by
  obtain ⟨ℱ, hUF, hnotV⟩ := exists_ultrafilter_excluding V hVcomp hVproper
  refine ⟨ℱ, hUF, fun ⟨t⟩ => ?_⟩
  obtain ⟨⟨U, hU, a⟩, -⟩ := Quot.exists_rep t
  exact hnotV (ultrafilter_isFilter ℱ hUF U V hU hVcomp ⟨a, term_uniq _ _⟩)

end Freyd
