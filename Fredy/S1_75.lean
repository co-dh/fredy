/-
  Freyd & Scedrov, *Categories, Allegories* §1.75  THE STONE REPRESENTATION THEOREM

  This file formalizes the cleanly stateable, infrastructure-light part of §1.75:
  the §1.751 vocabulary of ATOMS that opens the proof of the Stone Representation
  Theorem.  The Stone theorem proper (§1.75, §1.752–§1.755) is irreducibly
  topological — it builds the Stone space 𝒮(ℬ) of the boolean algebra of
  complemented subterminators, its stalk/sheaf functor `T : A → 𝓜(X)`, and uses
  point-set facts about Cantor space / the real line (Appendix A).  None of that
  machinery (Stone spaces, ultra-filters, stalk functors, sheaves on ℝ) exists in
  this repo, so those statements are recorded MISSING below rather than faked.

  §1.751  ATOM:  an object whose unique PROPER subobject is 0.
          ATOMICALLY BASED logos:  its atoms form a basis (§1.632).
          ATOMLESS logos:  it has no atoms.
          "Atomically based ⇒ boolean."   (book theorem; honest `sorry`)

  REUSE (DRY):
    Subobject, Subobject.le, Subobject.IsEntire   (S1_51)
    PreLogos, PreLogos.bottom, HasSubobjectUnions  (S1_60)
    IsComplemented, BooleanPreLogos                (S1_64)
    IsBasis                                        (S1_62)
-/

import Fredy.S1_51
import Fredy.S1_60
import Fredy.S1_62
import Fredy.S1_64

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.751  Atoms -/

/-- A subobject `S ↣ A` is PROPER (§1.751) if it is not entire, i.e. its
    representing mono is not an isomorphism.  (Freyd: "proper subobject" = a
    subobject strictly below the whole object.) -/
def Subobject.IsProper {A : 𝒞} (S : Subobject 𝒞 A) : Prop :=
  ¬ S.IsEntire

/-- An object `A` is an ATOM (§1.751): "0 is its unique proper subobject."

    Unwound (Freyd's literal phrasing):
    * `0` (the bottom subobject) is itself proper — equivalently `A` is not a
      zero-object; the book stresses "the definition of atom excludes
      zero-objects";
    * every proper subobject of `A` coincides with `0`, i.e. factors through the
      bottom.  Since `bottom_min` already gives `0 ≤ S` for all `S`, demanding
      `S ≤ 0` pins `S` to `0` as a subobject.

    So: `0` is proper, and every proper subobject is `≤ 0`. -/
def IsAtom [PreLogos 𝒞] (A : 𝒞) : Prop :=
  (PreLogos.bottom A).IsProper ∧
  ∀ (S : Subobject 𝒞 A), S.IsProper → S.le (PreLogos.bottom A)

/-- A logos is ATOMICALLY BASED (§1.751) if its atoms form a basis (§1.632):
    the representable functors `Hom(A, −)` for atoms `A` are collectively faithful
    and separate proper subobjects.  Reuses `IsBasis` from §1.632. -/
def AtomicallyBased [PreLogos 𝒞] [HasPullbacks 𝒞] : Prop :=
  IsBasis (𝒞 := 𝒞) (fun A => IsAtom A)

/-- A logos is ATOMLESS (§1.751) if it has no atoms.  (Freyd: "note that the
    definition of atom excludes zero-objects", so a degenerate/zero logos is
    vacuously atomless under this reading.) -/
def Atomless [PreLogos 𝒞] : Prop :=
  ∀ (A : 𝒞), ¬ IsAtom A

/-! ## §1.751  Atomically based ⇒ boolean -/

/-- **§1.751**: an ATOMICALLY BASED logos is BOOLEAN — excluded middle holds for
    every subobject.

    Freyd's argument: given `S ⊆ A`, define `¬S` as the join of all atom-images
    that do not factor through `S`:
        `¬S = ⊔ { image(x) | G atom, x : G → A, ¬∃ y : G → S.dom, y ≫ S.arr = x }`.
    Then:
    (1) `S ∩ ¬S = 0`: if `T ≤ S` and `T ≤ ¬S`, then by atomicity the atom basis
        would force some atom-image into both `S` and the join of non-S atoms,
        contradicting that those images are disjoint from `S`.
    (2) `S ∪ ¬S = A`: if not, `IsBasis` gives an atom `G` with `x : G → A` not
        factoring through `S ∪ ¬S`; by atomicity `x#S = 0` (since `x` misses `S`)
        and `image(x) ≤ ¬S` (by construction), contradicting `x` missing `¬S`.

    **PRECISE GAP — `HasIndexedSubobjectJoins` missing.**
    Step (1)/(2) both require constructing `¬S` as an INDEXED join over a
    (potentially infinite) family parameterized by all atoms `G` and maps `x : G → A`
    not factoring through `S`.  This repo's `HasSubobjectUnions` (S1_60) provides
    only BINARY joins; there is no `HasIndexedSubobjectJoins` typeclass or any
    well-foundedness principle that could bootstrap binary joins into the required
    arbitrary join.  Even classically, forming the join requires either:
      (a) a `HasIndexedSubobjectJoins` axiom (arbitrary small joins of subobjects), or
      (b) finiteness of the atom basis (not assumed by `AtomicallyBased`/`IsBasis`).
    In addition, deciding constructively whether `x : G → A` factors through `S`
    (i.e. `∃ y : G → S.dom, y ≫ S.arr = x`) requires classical reasoning or a
    decidability instance on `Subobject.le`.
    The rest of the argument (inverse-image preservation of unions, atomicity of
    `x#S`, and the `IsComplemented` disjointness clause matching `IsComplemented`'s
    ad-hoc formulation) are secondary obligations that unblock once the join exists. -/
theorem atomicallyBased_isBoolean [PreLogos 𝒞] [HasPullbacks 𝒞]
    (h : AtomicallyBased (𝒞 := 𝒞)) :
    ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplemented S := by
  -- BLOCKED: constructing the complement ¬S as an indexed join of atom-images not
  -- below S requires HasIndexedSubobjectJoins, which is not in this repo.
  -- See docstring for the full gap analysis.
  sorry

/-! ## §1.751  Periodic-power / reduction-to-atomless (recorded MISSING)

  The remainder of §1.751 reduces the Stone theorem to the ATOMLESS case via the
  PERIODIC POWER `℘A` (periodic functions ℕ → A), a sublogos of `A^ℕ` with a
  faithful diagonal representation `A → ℘A` that is atomless whenever `A` is
  non-degenerate.  Faithfully stating this needs:
    * countable powers `A^ℕ` and the sublogos of periodic sequences,
    * the diagonal representation and its faithfulness,
    * preservation of "positive & capital".
  None of this infrastructure exists in the repo, so it is NOT emitted as Lean
  here (no vacuous stub).  See S1_75.md.

  §1.752–§1.755 (the Stone space 𝒮(ℬ), the stalk/sheaf functor `T : A → 𝓜(X)`,
  the two characterizing properties, and the descent to faithfulness) are likewise
  recorded MISSING in S1_75.md: they require Stone-space/ultra-filter/sheaf
  machinery outside this repo's category-theoretic core.
-/

end Freyd
