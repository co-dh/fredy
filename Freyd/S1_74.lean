/-
  Freyd & Scedrov, *Categories, Allegories* §1.74  The GEOMETRIC REPRESENTATION THEOREM.

  §1.74     Geometric Representation Theorem: every countable (positive) logos is
            faithfully representable in a countable power of the logos of SHEAVES
            ON THE REAL LINE; with a coprime terminator, in 𝓜(ℝ) itself.
  §1.741    𝓜(ℝ) ≃ 𝓜(open subset of ℝ).
  §1.742    Every small (positive) logos has a faithful representation A → 𝒴^D.
  §1.743    𝒴^D is focal iff D has a coterminator.
  §1.744    DOMINATION of one category by another (left-full + onto-on-objects functor),
            and the induced faithful representation 𝒴^D → 𝒴^D′.
  §1.745    Every category (with a coterminator) is dominated by a (rooted) tree.
  §1.746    Every countable category with a coterminator is dominated by the binary tree.
  §1.747–§1.74(10)  Lazard sheaves on 2*, the Wilson/sobrification space, the FREYD CURVE,
            the open continuous surjection [-1/2,1/2] → 2* ∪ 2^ℕ.

  ----------------------------------------------------------------------------
  WHAT IS FORMALIZED HERE

  §1.74 is, overwhelmingly, point-set TOPOLOGY: Lazard sheaves on the binary tree
  topologised by up-deals, the Cantor topology on 2^ℕ, the sobrification (Wilson
  space), and the explicit FREYD CURVE realising an open continuous surjection from
  the real line.  None of that is faithfully stateable on the repo's current
  hand-built `Cat` infrastructure (there is no topology / sheaf layer), so it stays
  MISSING — see S1_74.md for the precise census.

  The one piece of §1.74 that is PURE category theory — independent of every
  topological notion — is the abstract DOMINATION relation of §1.744–§1.746: a
  functor that is *onto on objects* and *left-full*.  Domination is the device by
  which §1.744 transports a faithful representation along a functor `D′ → D`
  (`𝒴^D` faithfully representable in `𝒴^D′`).  We give that vocabulary faithfully and
  prove the two structural facts the book uses implicitly: domination is REFLEXIVE
  (the identity functor) and TRANSITIVE (functor composition).  These are exactly the
  closure properties §1.745–§1.746 chain together ("dominated by D⁺, therefore by ℕ*,
  therefore by 2*").

  The sheaf-theoretic *consequence* of domination — that `𝒴^D` is faithfully
  representable *as a logos* in `𝒴^D′` — needs the logos structure on functor
  categories (double-sharps in `𝒴^C`, §1.713) which is not built; it is recorded
  MISSING, not stubbed.
-/

import Freyd.S1_18

universe v u₁ u₂ u₃

namespace Freyd

/-! ## §1.744  Domination of categories

  Throughout, `F : D' → D` is a functor between (possibly large) categories living in
  arbitrary universes — domination is used in §1.745–6 between a category and its tree
  of paths, which is genuinely a different type. -/

section Domination

variable {D' : Type u₁} [Cat.{v} D'] {D : Type u₂} [Cat.{v} D]

/-- **§1.744 ONTO ON OBJECTS.**  The functor `F` hits every object of `D`. -/
def OntoObjects (F : D' → D) [Functor F] : Prop :=
  ∀ B : D, ∃ A : D', F A = B

/-- **§1.744 LEFT-FULL.**  For each `A : D'` and each `g : F A ⟶ B` in `D`, there is a
    morphism `f : A ⟶ A'` in `D'` lying over `g` — i.e. with `F A' = B` and, modulo that
    identification, `F f = g`.  (The book: "for each `D ∈ |D'|` and each `g : F(D) → B`
    there exists `f : D → A` so that `F(f) = g`.")

    The codomain identification `hA' : F A' = B` is needed to even type the equation
    `F f = g`; we transport `g` back along it with `hA' ▸ g`. -/
def LeftFull (F : D' → D) [hF : Functor F] : Prop :=
  ∀ (A : D') {B : D} (g : F A ⟶ B), ∃ (A' : D') (hA' : F A' = B) (f : A ⟶ A'),
    hF.map f = hA' ▸ g

/-- **§1.744 `D'` DOMINATES `D`.**  There is a functor `F : D' → D` that is onto on
    objects and left-full.  (The book notes such `F` need not be full.) -/
def Dominates (D' : Type u₁) [Cat.{v} D'] (D : Type u₂) [Cat.{v} D] : Prop :=
  ∃ (F : D' → D) (_ : Functor F), OntoObjects F ∧ LeftFull F

end Domination

/-! ### Structural closure of domination (§1.745–§1.746 chaining)

  §1.745–6 build a chain "`D` is dominated by `P(D)`, hence by `D⁺`, hence by ℕ*,
  hence by 2*", silently using that domination is a reflexive, transitive relation on
  categories.  We supply both facts. -/

/-- **Domination is reflexive.**  Every category dominates itself, via the identity
    functor: it is onto on objects (take `A := B`) and left-full (take `f := g`). -/
theorem dominates_refl (D : Type u₂) [Cat.{v} D] : Dominates D D := by
  refine ⟨(fun X => X), inferInstance, ?_, ?_⟩
  · intro B; exact ⟨B, rfl⟩
  · intro A B g; exact ⟨B, rfl, g, rfl⟩

/-- **Domination is transitive.**  If `E` dominates `D'` and `D'` dominates `D`, then `E`
    dominates `D`, via the composite functor.  Onto-on-objects composes by chasing
    preimages; left-fullness composes because a lift over `D'` of a lift over `D` is a
    lift over `D` for the composite. -/
theorem dominates_trans {E : Type u₃} [Cat.{v} E] {D' : Type u₁} [Cat.{v} D']
    {D : Type u₂} [Cat.{v} D] (h₁ : Dominates E D') (h₂ : Dominates D' D) :
    Dominates E D := by
  obtain ⟨F, hF, hFonto, hFfull⟩ := h₁
  obtain ⟨G, hG, hGonto, hGfull⟩ := h₂
  -- the repo's `compFunctor` instance is single-universe; build the cross-universe
  -- composite `Functor` by hand.
  let hGF : Functor (G ∘ F) :=
    { map := fun {_ _} f => hG.map (hF.map f)
      map_id := fun X => by
        show hG.map (hF.map (Cat.id X)) = Cat.id (G (F X))
        rw [hF.map_id, hG.map_id]
      map_comp := fun f g => by
        show hG.map (hF.map (f ≫ g)) = _
        rw [hF.map_comp, hG.map_comp] }
  refine ⟨G ∘ F, hGF, ?_, ?_⟩
  · -- onto on objects: pull `B` back through `G`, then through `F`
    intro B
    obtain ⟨A', hA'⟩ := hGonto B
    obtain ⟨A, hA⟩ := hFonto A'
    exact ⟨A, by simp only [Function.comp_apply, hA, hA']⟩
  · -- left-full: lift `g : (G∘F) A ⟶ B` first along `G`, then the resulting `D'`-map along `F`
    intro A B g
    -- `g : G (F A) ⟶ B`; lift along `G` to a map out of `F A` in `D'`.
    obtain ⟨A'₀, hA'₀, f₀, hf₀⟩ := hGfull (F A) g
    -- lift `f₀ : F A ⟶ A'₀` along `F` to a map out of `A` in `E`.
    obtain ⟨A₁, hA₁, f₁, hf₁⟩ := hFfull A f₀
    refine ⟨A₁, ?_, f₁, ?_⟩
    · -- `(G∘F) A₁ = B`
      simp only [Function.comp_apply, hA₁, hA'₀]
    · -- `(G∘F).map f₁ = (proof) ▸ g`
      show hG.map (hF.map f₁) = _
      rw [hf₁]
      -- now `hG.map (hA₁ ▸ f₀)`; push the cast out and use `hf₀`
      subst hA₁
      simp only [hf₀]

/-! ## §1.744 D' dominates D ⟹ S^D faithfully representable in S^D'

  "If D' dominates D then S^D is faithfully representable in S^D' as a logos."
  (Freyd §1.744; proof is identity-checking using §1.713's formula for double-sharps
  in functor categories.)

  OPEN.  Three missing pieces, none in the repo:
  1. `Logos (FunctorObj D S)` instance: `FunctorCategory.lean` gives only `RegularCategory`
     on `FunctorObj 𝒜 𝒮`; the logos structure (the right adjoint `f##` in `S^D`,
     §1.713's pointwise formula `(f## A')_d = f_d## A'_d`) is NOT built.
  2. `LogosMap` predicate: a Lean type asserting a functor between logoi preserves `f##`;
     currently absent from the repo (see `S1_72.lean` note near line 449).
  3. The restriction functor `F* : S^D → S^D'` (precompose with F): a `FunctorObj`-level
     functor built from `LeftFull F` and `OntoObjects F` — not constructed anywhere. -/

-- BOOK §1.744: If D' dominates D then S^D is faithfully representable in S^D' as a logos.
-- OPEN: needs (1) `Logos (FunctorObj D S)` via pointwise §1.713 double-sharps,
--   (2) a `LogosMap` predicate, (3) the restriction functor `F* : S^D → S^D'`.

/-! ## §1.745 Every category dominated by a rooted tree

  "Every category (with a coterminator) is dominated by a (rooted) tree."
  (Freyd §1.745; by taking P(D) = tree of finite composable paths, ordered by prolongation,
  with functor P(D) → D sending a path to the target of its last map.)

  OPEN.  Missing: a concrete Lean category `PathTree D` whose objects are finite
  composable sequences in D, morphisms are prolongations, and a `Functor (PathTree D → D)`
  (target-of-last-map) that is `OntoObjects` and `LeftFull`.  None of this exists. -/

-- BOOK §1.745: Every category (with a coterminator) is dominated by a (rooted) tree.
-- OPEN: needs `PathTree D` category (composable-path tree) + domination functor to D.

/-! ## §1.746 Every countable category dominated by the binary tree

  "Every countable category with a coterminator is dominated by the binary tree."
  (Freyd §1.746; by homogenising P(D) to D⁺ (words of morphisms) and then to ℕ*,
  then dominating ℕ* by the binary tree 2* via the function f with f⁻¹(n) infinite.)

  OPEN.  Missing: concrete categories `WordCat D` (free monoid on morphisms of D),
  `NatStar` (the category with objects ℕ, unique morphism n → m for n ≤ m), `BinTree`
  (the binary tree 2* = full binary tree as a category), and the three domination
  functors `WordCat D → PathTree D`, `NatStar → WordCat D` (for countable D), and
  `BinTree → NatStar` (via the function with infinite fibers).  None exist in repo. -/

-- BOOK §1.746: Every countable category with a coterminator is dominated by the binary tree.
-- OPEN: needs `WordCat D`, `NatStar`, `BinTree` categories and three domination functors.

/-! ## §1.748 Open continuous map ⟹ logos representation

  "If g: X → Y is an open continuous map, then g#: H(Y) → H(X) is a representation of logoi."
  (Freyd §1.748; proof: g open ⟹ g# preserves double-sharps, via the pointwise description
  of double-sharps in H(X) as unions of open subspaces [§1.713].)

  OPEN.  Missing:
  1. `TopologicalSpace X` and `OpenSubset X` infrastructure (none in repo; `Locale.lean`
     has a locale/frame layer but no concrete topological space type with open sets).
  2. `H(X)` as a category: the category of Lazard sheaves on X (or equivalently of
     sheaves on the locale O(X)) — not constructed anywhere.
  3. The functor `g# : H(Y) → H(X)` for `g : X → Y` open continuous, and the
     `LogosMap` proof that it preserves double-sharps.
  This is irreducibly topological; no category-theoretic shortcut exists. -/

-- BOOK §1.748: If g: X → Y is an open continuous map, then g#: H(Y) → H(X) is a
-- representation of logoi.
-- OPEN: needs TopologicalSpace/OpenSubset infra, category H(X) of Lazard sheaves,
--   and proof g# preserves double-sharps via §1.713's pointwise formula.

end Freyd
