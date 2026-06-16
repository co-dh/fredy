/-
  Freyd & Scedrov, *Categories and Allegories* §1.38–§1.399
  Duality, Stone duality, Finite presentation, Q-sequences.

  §1.38 DUALITY: a contravariant strong equivalence between categories.
  §1.389 STONE DUALITY: Boolean algebras ↔ Stone spaces.
  §1.392 FINITE PRESENTATION via Q-SEQUENCE: a category presented
         by a finite graph with composition/identity equations.
  §1.395 COMPLEMENTARY Q-SEQUENCE.
-/


import Fredy.S1_1
import Fredy.S1_18
import Fredy.S1_31
import Fredy.S1_41
import Fredy.S1_81


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.38 Duality

  A DUALITY between 𝒞 and 𝒟 is a contravariant strong equivalence.
  Concretely: a pair of contravariant functors F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞
  such that G∘F ≅ Id_𝒞 (covariant natural iso) and F∘G ≅ Id_𝒟.

  Since contra∘contra = covariant, G∘F and F∘G carry covariant Functor
  instances (via `compContraFunctor` below), and `NatIso` from §1.31 applies. -/

/-- Composing two contravariant functors gives a covariant functor. -/
instance compContraFunctor {ℰ : Type u} [Cat.{v} ℰ] (F : 𝒞 → 𝒟) (G : 𝒟 → ℰ)
    [hF : ContraFunctor F] [hG : ContraFunctor G] : Functor (G ∘ F) where
  map f        := hG.map (hF.map f)
  map_id X     := by simp only [Function.comp]; rw [hF.map_id, hG.map_id]
  map_comp f g := by simp only [Function.comp]; rw [hF.map_comp, hG.map_comp]

/-- A DUALITY between 𝒞 and 𝒟 (§1.38): a contravariant strong equivalence.
    F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 are both contravariant, with G∘F ≅ Id_𝒞 and
    F∘G ≅ Id_𝒟 as covariant natural isomorphisms. -/
structure Duality (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [ContraFunctor F] [ContraFunctor G] where
  unit   : Nonempty (NatIso (G ∘ F) (λ X : 𝒞 => X))
  counit : Nonempty (NatIso (F ∘ G) (λ X : 𝒟 => X))

/-! ## §1.389 Stone duality

  STONE DUALITY: the category of Boolean algebras is dual to the
  category of Stone spaces (compact Hausdorff totally disconnected).
  A STONE SPACE is a compact totally disconnected Hausdorff space. -/

/-- STONE SPACE (§1.389): compact, Hausdorff, totally disconnected.
    (Set-theoretic definition; we give a placeholder type.) -/
opaque StoneSpace : Type u

/- STONE DUALITY (§1.389): BoolAlg° ≅ Stone.  Placeholder — the `def` is
   omitted until `Cat StoneSpace` and the equivalence are formalized. -/

/-! ## §1.392 Finite presentation via Q-sequence

  A Q-SEQUENCE presents a category by generators (graph) and
  relations (equations on paths).  SATISFIES means the equations hold.

  FINITE PRESENTATION: a category given by a finite graph and
  finitely many equations. -/

/-- A Q-SEQUENCE (§1.392): a directed graph with equations. -/
structure QSequence where
  objects   : Type
  arrows    : Type
  src       : arrows → objects
  tgt       : arrows → objects
  equations : Type
  eq_lhs    : equations → List arrows
  eq_rhs    : equations → List arrows

/-! ### Path composition for Q-sequences

  A *path* in a Q-sequence is a list of arrows where each consecutive pair
  is composable: `Q.tgt aᵢ = Q.src aᵢ₊₁`.  Given an interpretation
  `interp : Q.objects → 𝒜` and `arrowMap a : interp (Q.src a) ⟶ interp (Q.tgt a)`,
  we lift a composable path to a single hom in `𝒜`.

  We carry the composability witness in the type, using a `Fin`-indexed
  family of composability proofs. -/

/-- A composable path in `Q`: a list of arrows together with the proof that
    consecutive endpoints match. -/
def ComposablePath (Q : QSequence) : List Q.arrows → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rest => Q.tgt a = Q.src b ∧ ComposablePath Q (b :: rest)

/-- Lift a non-empty composable path to a morphism in `𝒜`. -/
def composeComposablePath {Q : QSequence} {𝒜 : Type u} [Cat.{v} 𝒜]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    : (path : List Q.arrows) → (h : path ≠ []) → ComposablePath Q path
    → interp (Q.src (path.head h)) ⟶ interp (Q.tgt (path.getLast h))
  | [a],            _,  _        => arrowMap a
  | a :: b :: rest, _, ⟨hab, hc⟩ =>
      arrowMap a ≫ (hab ▸ composeComposablePath interp arrowMap (b :: rest)
        (List.cons_ne_nil b rest) hc)

/-- SATISFIES a Q-sequence (§1.392): for every equation, both sides are composable
    paths with matching source and target in `Q`, and their compositions in `𝒜`
    agree (after transporting to the same type via the endpoint-matching proofs). -/
def SatisfiesQSequence (Q : QSequence) (𝒜 : Type u) [Cat.{v} 𝒜]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a)) : Prop :=
  ∀ (e : Q.equations)
    (hlL : Q.eq_lhs e ≠ []) (hlR : Q.eq_rhs e ≠ [])
    (hcL : ComposablePath Q (Q.eq_lhs e)) (hcR : ComposablePath Q (Q.eq_rhs e))
    (hSrc : Q.src ((Q.eq_lhs e).head hlL) = Q.src ((Q.eq_rhs e).head hlR))
    (hTgt : Q.tgt ((Q.eq_lhs e).getLast hlL) = Q.tgt ((Q.eq_rhs e).getLast hlR)),
    -- Transport lhs to the type of rhs and compare
    hSrc ▸ hTgt ▸
      composeComposablePath interp arrowMap (Q.eq_lhs e) hlL hcL =
    composeComposablePath interp arrowMap (Q.eq_rhs e) hlR hcR

/-- COMPLEMENTARY Q-SEQUENCE (§1.395): dual by reversing arrows.
    The book's complementary Q-sequence transposes V's and 3's; for
    finitely-presented Q-sequences this reverses lhs↔rhs paths and src↔tgt. -/
def complementaryQSequence (Q : QSequence) : QSequence where
  objects   := Q.objects
  arrows    := Q.arrows
  src       := Q.tgt
  tgt       := Q.src
  equations := Q.equations
  eq_lhs  e := (Q.eq_rhs e).reverse
  eq_rhs  e := (Q.eq_lhs e).reverse

/-! ### §1.395 Isomorphisms preserve and reflect satisfaction

  The book (§1.395) states: "A₀ → B satisfies a Q-sequence iff A₀ → B → B' does"
  whenever B → B' is an isomorphism.  In our object-centric formalization,
  the analogous statement is that a functor `F : 𝒜 → ℬ` that reflects equality
  (i.e., is an embedding) reflects satisfaction of Q-sequences under post-composition.

  The key technical ingredient is that functors distribute over `composeComposablePath`. -/

/-- A functor distributes over `composeComposablePath`: the composition of
    `F`-images equals the `F`-image of the composition. -/
private theorem functor_composeComposablePath
    {Q : QSequence} {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    : ∀ (path : List Q.arrows) (h : path ≠ []) (hc : ComposablePath Q path),
      hF.map (composeComposablePath interp arrowMap path h hc) =
        composeComposablePath (F ∘ interp) (fun a => hF.map (arrowMap a)) path h hc
  | [_], _, _ => rfl
  | a :: b :: rest, _, hc => by
      obtain ⟨hab, hc'⟩ := hc
      simp only [composeComposablePath]
      rw [hF.map_comp]
      congr 1
      -- Use the inductive hypothesis and then commute F.map with the ▸ transport
      have key := functor_composeComposablePath F interp arrowMap (b :: rest)
                    (List.cons_ne_nil _ _) hc'
      show hF.map (hab ▸ composeComposablePath interp arrowMap (b :: rest)
                     (List.cons_ne_nil b rest) hc') =
           hab ▸ composeComposablePath (F ∘ interp) (fun x => hF.map (arrowMap x))
                   (b :: rest) (List.cons_ne_nil b rest) hc'
      rw [← key]
      exact hab.symm.rec rfl

/-- A functor commutes with double transport along object equalities: transporting the
    `F`-image equals the `F`-image of the transport.  Proved by `subst`-ing both equalities. -/
private theorem functor_dbl_transport
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    {P : Type} (interp : P → 𝒜)
    {x x' y y' : P} (hx : x = x') (hy : y = y')
    (f : interp x ⟶ interp y) :
    hx ▸ hy ▸ hF.map f = hF.map (hx ▸ hy ▸ f) := by
  subst hx; subst hy; rfl

/-- Isomorphisms (embedding functors) preserve and reflect satisfaction of a Q-sequence
    (§1.395).  The book's statement: `A₀ → B` satisfies iff `A₀ → B → B'` does when
    `B → B'` is an isomorphism.  We state this as: if `F : 𝒜 → ℬ` is an embedding,
    then satisfaction of a Q-sequence via `(F ∘ interp, F ∘ arrowMap)` implies (and
    is implied by) satisfaction via `(interp, arrowMap)`.

    The reflect direction (given here) uses `Embedding F` (injectivity on homs).
    The preserve direction is `iso_preserves_sat` below (functoriality alone suffices). -/
theorem iso_reflects_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    (hEmb : Embedding F)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q ℬ (F ∘ interp) (fun a => hF.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒜 interp arrowMap := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have heq := sat e hlL hlR hcL hcR hSrc hTgt
  simp only [← functor_composeComposablePath F interp arrowMap] at heq
  -- heq : hSrc ▸ hTgt ▸ F.map (compose interp lhs) = F.map (compose interp rhs)
  -- Goal : hSrc ▸ hTgt ▸ compose interp lhs = compose interp rhs
  -- Apply F-injectivity, then commute F.map with the double transport.
  apply hEmb
  rw [← functor_dbl_transport F interp hSrc hTgt]
  exact heq

/-- Any functor preserves satisfaction of a Q-sequence (§1.395): if `interp, arrowMap`
    satisfies the Q-sequence in `𝒜`, then `F ∘ interp, F ∘ arrowMap` satisfies it in `ℬ`.
    This is immediate from functoriality (F distributes over path composition). -/
theorem iso_preserves_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q 𝒜 interp arrowMap) :
    SatisfiesQSequence Q ℬ (F ∘ interp) (fun a => hF.map (arrowMap a)) := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have heq := sat e hlL hlR hcL hcR hSrc hTgt
  simp only [← functor_composeComposablePath F interp arrowMap]
  -- Goal: hSrc ▸ hTgt ▸ F.map (compose interp lhs) = F.map (compose interp rhs)
  -- Commute F.map with the double transport, then apply `congrArg hF.map heq`.
  rw [functor_dbl_transport F interp hSrc hTgt]
  exact congrArg hF.map heq

/-! ## §1.39 Linear order / finite presentation

  A LINEARLY ORDERED CATEGORY has objects totally ordered. -/

/-- A LINEARLY ORDERED CATEGORY (§1.39): objects form a totally ordered set. -/
class LinearlyOrdered (𝒞 : Type u) [Cat.{v} 𝒞] where
  order : 𝒞 → 𝒞 → Prop
  total : ∀ a b : 𝒞, order a b ∨ order b a

end Freyd
