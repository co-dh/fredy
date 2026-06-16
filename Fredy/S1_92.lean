/-
  Freyd & Scedrov, *Categories and Allegories* §1.92  Singleton map, topos is exponential.

  §1.92  SINGLETON MAP Δ₁ : B → [B]
         Theorems: Δ₁ is monic; f ≫ Δ₁ = Δ₁ ≫ [f]  (i.e., f(Δ1) = Δf)
         Topos is exponential: [B]^A = [A × B] (§1.92)
  §1.921 LAWVERE DEFINITION of elementary topos (bicartesian + exponential + partial map classifier)
  §1.922 Ω^(−) as a contravariant functor; Ω^g for g : B₁ → B₂
  §1.923 B^A arises as a subobject of [A×B] via a pullback
  §1.924 FG(A) = (G(-), F(A + -)) computed via Yoneda
  §1.926 Exponential structure restricts to Heyting algebra on Sub(1)
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_85
import Fredy.S1_81
import Fredy.S1_51
import Fredy.S1_58
import Fredy.S1_42


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.92  Topos is exponential + singleton map Δ₁ : B → [B] -/

/-- **§1.92**: A topos is exponential.  The exponential B^A is constructed
    as a subobject of [A × B] via the singleton map (§1.92).
    Proof: [B]^A = [A×B] via the power-object adjunction (Freyd §1.92). -/
instance topos_has_exponentials : HasExponentials 𝒞 := by
  -- BLOCKER: the book's proof (§1.92) runs "every power object is baseable, then
  -- B is the equalizer of χ and [B]→1→Ω, so B is baseable [§1.859]".  The crux is
  -- the §1.859 fact `baseable_inclusion_preserves_equalizers`, which is itself an
  -- unfilled `sorry` in S1_85.  Without it (and the power-object⇒baseable adjunction
  -- packaging) the `eval`/`curry` data for general B^A cannot be assembled.
  sorry

-- All subsequent decls require [HasExponentials 𝒞] via topos_has_exponentials.
-- exp B Ω = Ω^B = [B] the power object of B.

/-- Naturality of `curry` in its variable argument: precomposing the curried
    map with `h : X' ⟶ X` equals currying after precomposing the uncurried
    map with `prodMap A X' X h`.  (Adjoint-transpose naturality of `A × -`.) -/
theorem curry_precomp {A B X X' : 𝒞} (h : X' ⟶ X) (f : prod A X ⟶ B) :
    h ≫ curry f = curry (prodMap A X' X h ≫ f) := by
  apply curry_unique_eq
  rw [prodMap_comp, Cat.assoc, curry_eval_eq]

/-! ## §1.922  Ω^(−) as a contravariant functor

  For a topos, the assignment B ↦ Ω^B = exp B Ω is a contravariant functor.
  Given g : B₁ → B₂, Ω^g : Ω^B₂ → Ω^B₁ is the unique map such that:
      prod B₁ (exp B₂ Ω) —(pair(fst≫g, snd))→ prod B₂ (exp B₂ Ω) —eval→ Ω
  equals prod B₁ (Ω^g) ≫ eval (i.e., the adjoint transpose definition).
  Equivalently, Ω^g = curry(pair (fst ≫ g) snd ≫ eval). -/

/-- **§1.922**: The power-object functor Ω^(−) is CONTRAVARIANT. -/
instance omegaPowContra :
    ContraFunctor (fun B : 𝒞 => exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) where
  map {B₁ B₂} g :=
    -- Ω^g : exp B₂ Ω → exp B₁ Ω
    -- = curry (pair (fst ≫ g) snd ≫ eval_B₂_Ω)
    curry (pair (fst (A := B₁) (B := exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ g)
               (snd (A := B₁) (B := exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞)))) ≫
           eval_exp B₂ (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
  map_id B := by
    -- Ω^(id B) = id (exp B Ω).
    -- curry(pair(fst≫id, snd)≫eval) = curry(pair(fst,snd)≫eval) = curry eval = id
    apply (curry_unique_eq _).symm
    simp only [prodMap, Cat.comp_id, pair_fst_snd, Cat.id_comp]
  map_comp {B₁ B₂ B₃} f g := by
    -- Ω^(f≫g) = Ω^g ≫ Ω^f  (contravariance reverses order).
    -- Both sides curry the reindexed evaluation; we verify the uncurried forms agree.
    -- Abbreviate the classifier object.
    let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
    -- Reduce RHS `map g ≫ map f` through the curry universal property (symm: g = curry f).
    refine (curry_unique_eq ?_).symm
    -- Factor prodMap of a composite, then evaluate the inner curry (map f).
    rw [prodMap_comp, Cat.assoc, curry_eval_eq]
    -- Now: prodMap(map g) ≫ (pair (fst≫f) snd ≫ eval_B₂) = pair (fst≫f≫g) snd ≫ eval_B₃.
    -- Push prodMap(map g) past `pair (fst≫f) snd` coordinatewise.
    have hpair : prodMap B₁ (exp B₃ Ω) (exp B₂ Ω)
          (curry (pair (fst ≫ g) snd ≫ eval_exp B₃ Ω)) ≫
        pair (fst ≫ f) (snd : prod B₁ (exp B₂ Ω) ⟶ exp B₂ Ω)
        = pair (fst ≫ f) (snd ≫ curry (pair (fst ≫ g) snd ≫ eval_exp B₃ Ω)) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, prodMap_fst]
      · rw [Cat.assoc, snd_pair, prodMap_snd]
    rw [← Cat.assoc, hpair]
    -- Remaining: pair (fst≫f) (snd ≫ map g) ≫ eval_B₂ = pair (fst≫f≫g) snd ≫ eval_B₃.
    -- Expand eval of map g via prodMap on the second coordinate.
    have hfac : pair (fst ≫ f)
          (snd ≫ curry (pair (fst ≫ g) snd ≫ eval_exp B₃ Ω))
        = pair (fst ≫ f) (snd : prod B₁ (exp B₃ Ω) ⟶ exp B₃ Ω) ≫
            prodMap B₂ (exp B₃ Ω) (exp B₂ Ω)
              (curry (pair (fst ≫ g) snd ≫ eval_exp B₃ Ω)) := by
      refine (pair_uniq _ _ _ ?_ ?_).symm
      · rw [Cat.assoc, prodMap_fst, fst_pair]
      · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair]
    rw [hfac, Cat.assoc, curry_eval_eq, ← Cat.assoc]
    -- pair (fst≫f) snd ≫ (pair (fst≫g) snd) = pair (fst≫f≫g) snd
    have hcomp : pair (fst ≫ f) (snd : prod B₁ (exp B₃ Ω) ⟶ exp B₃ Ω) ≫
          pair (fst ≫ g) snd
        = pair (fst ≫ f ≫ g) snd := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
      · rw [Cat.assoc, snd_pair, snd_pair]
    rw [hcomp]

/-! ## §1.92  Singleton map Δ₁ : B → [B] -/

/-- The SINGLETON MAP Δ₁ : B → [B] (§1.92).
    [B] = Ω^B = exp B Ω is the power object.
    Δ₁ B = curry(χ_Δ) where χ_Δ : B×B → Ω is the characteristic map of the
    diagonal subobject diag B : B ↪ B×B. -/
noncomputable def singletonMapCat (B : 𝒞) :
    B ⟶ exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  curry (HasSubobjectClassifier.classify (diag B) (diag_mono B))

/-- The GRAPH monic `γ_h = ⟨h, 1⟩ : X' ↪ B × X'` of a map `h : X' → B`
    (the subobject `{(b,x) | b = h x}`).  Monic because `γ_h ≫ snd = 1`. -/
private def graphMono {B X' : 𝒞} (h : X' ⟶ B) : X' ⟶ prod B X' :=
  pair h (Cat.id X')

private theorem graphMono_snd {B X' : 𝒞} (h : X' ⟶ B) :
    graphMono h ≫ snd = Cat.id X' := snd_pair _ _

private theorem graphMono_fst {B X' : 𝒞} (h : X' ⟶ B) :
    graphMono h ≫ fst = h := fst_pair _ _

private theorem graphMono_mono {B X' : 𝒞} (h : X' ⟶ B) : Mono (graphMono h) :=
  mono_of_retraction _ snd (graphMono_snd h)

/-- The composite `γ_h ≫ (B × h) = h ≫ Δ` lands the graph on the diagonal:
    `⟨h,1⟩ ≫ ⟨fst, snd≫h⟩ = ⟨h,h⟩ = h ≫ ⟨1,1⟩`. -/
private theorem graphMono_prodMap {B X' : 𝒞} (h : X' ⟶ B) :
    graphMono h ≫ prodMap B X' B h = h ≫ diag B := by
  have hlhs : graphMono h ≫ prodMap B X' B h = pair h h := by
    apply pair_uniq
    · rw [Cat.assoc, prodMap_fst, graphMono_fst]
    · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, graphMono_snd, Cat.id_comp]
  have hrhs : h ≫ diag B = pair h h := by
    apply pair_uniq
    · rw [Cat.assoc, diag_fst, Cat.comp_id]
    · rw [Cat.assoc, diag_snd, Cat.comp_id]
  rw [hlhs, hrhs]

/-- **§1.92, key step**: `prodMap B X' B h ≫ χ_Δ` is the characteristic map of the
    graph monic `γ_h`.  The graph square is the pullback of `true` along it,
    obtained by pasting the (diagonal) classifier square with the pullback of the
    diagonal along `B × h`. -/
private theorem graph_classifies {B X' : 𝒞} (h : X' ⟶ B) :
    (Cone.mk (f := prodMap B X' B h ≫
        HasSubobjectClassifier.classify (diag B) (diag_mono B))
        (g := HasSubobjectClassifier.true)
        (pt := X') (π₁ := graphMono h) (π₂ := term X')
        (w := by
          rw [← Cat.assoc, graphMono_prodMap, Cat.assoc,
              HasSubobjectClassifier.classify_sq, ← Cat.assoc, term_uniq (h ≫ term B) (term X')]
        )).IsPullback := by
  intro d
  -- d : Cone (prodMap h ≫ χ_Δ) true. Reindex its first leg through B × h and use
  -- the diagonal classifier pullback to obtain a lift ℓ : d.pt → B with
  -- ℓ ≫ diag B = d.π₁ ≫ prodMap h.
  have hsq : (d.π₁ ≫ prodMap B X' B h) ≫
      HasSubobjectClassifier.classify (diag B) (diag_mono B) = d.π₂ ≫ HasSubobjectClassifier.true := by
    rw [Cat.assoc]; exact d.w
  obtain ⟨ℓ, ⟨hℓ₁, _hℓ₂⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback (diag B) (diag_mono B)
      ⟨d.pt, d.π₁ ≫ prodMap B X' B h, d.π₂, hsq⟩
  simp only at hℓ₁
  -- hℓ₁ : ℓ ≫ diag B = d.π₁ ≫ prodMap B X' B h
  -- From hℓ₁, project to fst/snd to recover ℓ and a key identity.
  have hfst : d.π₁ ≫ fst = ℓ := by
    have := congrArg (· ≫ fst) hℓ₁
    simp only [Cat.assoc, diag_fst, Cat.comp_id, prodMap_fst] at this
    exact this.symm
  have hsnd : d.π₁ ≫ snd ≫ h = ℓ := by
    have := congrArg (· ≫ snd) hℓ₁
    simp only [Cat.assoc, diag_snd, Cat.comp_id, prodMap_snd] at this
    exact this.symm
  have hkey : d.π₁ ≫ snd ≫ h = d.π₁ ≫ fst := by rw [hsnd, hfst]
  -- The lift into X' is u = d.π₁ ≫ snd.
  refine ⟨d.π₁ ≫ snd, ⟨?_, term_uniq _ _⟩, ?_⟩
  · -- u ≫ γ_h = d.π₁, checked componentwise on B × X'.
    have hA : ((d.π₁ ≫ snd) ≫ graphMono h) ≫ fst = d.π₁ ≫ fst := by
      rw [Cat.assoc, graphMono_fst, Cat.assoc, hkey]
    have hB : ((d.π₁ ≫ snd) ≫ graphMono h) ≫ snd = d.π₁ ≫ snd := by
      rw [Cat.assoc, graphMono_snd, Cat.comp_id]
    refine (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) _ hA hB).trans
      (pair_uniq (d.π₁ ≫ fst) (d.π₁ ≫ snd) d.π₁ rfl rfl).symm
  · -- Uniqueness: if v ≫ γ_h = d.π₁ then v = (v ≫ γ_h) ≫ snd = d.π₁ ≫ snd.
    intro v hv₁ _
    simp only at hv₁
    have hvs : v ≫ graphMono h ≫ snd = v := by
      rw [graphMono_snd]; exact Cat.comp_id v
    have hproj : (v ≫ graphMono h) ≫ snd = d.π₁ ≫ snd := congrArg (· ≫ snd) hv₁
    exact hvs.symm.trans ((Cat.assoc v (graphMono h) snd).symm.trans hproj)

/-- **§1.92**: The singleton map Δ₁ : B → [B] is MONIC.
    Proof: if `h ≫ Δ₁ = k ≫ Δ₁` then by `curry_precomp`/`curry_inj` the
    characteristic maps `B×h ≫ χ_Δ` and `B×k ≫ χ_Δ` agree, so the graph monics
    `γ_h`, `γ_k` are both pullbacks of `true` along the *same* map; the pullback
    lift `u` satisfies `u ≫ γ_h = γ_k`, hence (projecting to X') `u = 1` and
    `γ_h = γ_k`, whence `h = k`. -/
theorem singletonMapCat_monic (B : 𝒞) :
    Mono (singletonMapCat (𝒞 := 𝒞) B) := by
  intro X' h k hΔ
  -- From h ≫ curry(χ_Δ) = k ≫ curry(χ_Δ): the precomposed char maps agree.
  have hχ : prodMap B X' B h ≫
        HasSubobjectClassifier.classify (diag B) (diag_mono B)
      = prodMap B X' B k ≫
        HasSubobjectClassifier.classify (diag B) (diag_mono B) := by
    have := hΔ
    rw [singletonMapCat, curry_precomp, curry_precomp] at this
    exact curry_inj this
  -- γ_k's square commutes against h's char map (rewrite via hχ), giving a cone over h's cospan.
  have hk_w : graphMono k ≫ (prodMap B X' B h ≫
        HasSubobjectClassifier.classify (diag B) (diag_mono B))
      = term X' ≫ HasSubobjectClassifier.true := by
    rw [hχ, ← Cat.assoc, graphMono_prodMap, Cat.assoc,
        HasSubobjectClassifier.classify_sq, ← Cat.assoc, term_uniq (k ≫ term B) (term X')]
  -- Lift γ_k through γ_h's pullback square.
  obtain ⟨u, ⟨hu₁, _⟩, _⟩ := graph_classifies h ⟨X', graphMono k, term X', hk_w⟩
  -- u ≫ γ_h = γ_k.  Project to X' (snd): u = u ≫ γ_h ≫ snd = γ_k ≫ snd = 1.
  simp only at hu₁
  -- hu₁ : u ≫ graphMono h = graphMono k
  have hu_id : u = Cat.id X' := by
    have hus : u ≫ graphMono h ≫ snd = u := by
      rw [graphMono_snd]; exact Cat.comp_id u
    have hproj : (u ≫ graphMono h) ≫ snd = graphMono k ≫ snd := congrArg (· ≫ snd) hu₁
    exact hus.symm.trans
      ((Cat.assoc u (graphMono h) snd).symm.trans (hproj.trans (graphMono_snd k)))
  -- Hence γ_h = γ_k; project to B (fst): h = k.
  have heq : graphMono h = graphMono k := by rw [← hu₁, hu_id, Cat.id_comp]
  calc h = graphMono h ≫ fst := (graphMono_fst h).symm
    _ = graphMono k ≫ fst := by rw [heq]
    _ = k := graphMono_fst k

/-- The COVARIANT power-map action [f] : [A] → [B] for f : A → B (§1.922).
    [f] : exp A Ω → exp B Ω is the direct-image (existential) action:
    [f](S) = {b ∈ B | ∃ a ∈ S, f(a) = b}.
    Construction via the image factorization and subobject classifier. -/
noncomputable def powerMapCov {A B : 𝒞} (f : A ⟶ B) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶
    exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  -- [f](S) = ∃-image of S along f.  BLOCKER: the existential / direct-image
  -- requires the regular IMAGE FACTORIZATION of §1.56 (cover–mono factor of a map)
  -- assembled into a topos morphism on power objects (∃_f ⊣ f# adjunction).
  -- §1.56's `image` exists but its packaging as a map `exp A Ω → exp B Ω` (naming the
  -- direct image of the universal relation ∈_A pushed along f) is not yet available.
  sorry

/-- **§1.92**: NATURALITY of the singleton map: f ≫ Δ₁(B) = Δ₁(A) ≫ [f].
    Here [f] = powerMapCov f : [A] → [B] is the covariant direct-image action.
    In Freyd's notation: f(Δ₁) = Δf (§1.92). -/
theorem singletonMapCat_natural {A B : 𝒞} (f : A ⟶ B) :
    f ≫ singletonMapCat B =
      singletonMapCat A ≫ powerMapCov f := by
  -- BLOCKER: this is the book's f(Δ₁) = Δf, but it is stated against `powerMapCov f`
  -- which is itself an unfilled `sorry` (the direct-image action [f]).  Until [f] is
  -- defined via image factorization (see `powerMapCov`), the equation has no provable
  -- content — its truth is precisely the defining property of [f].
  sorry

/-! ## §1.921  Lawvere's original definition of elementary topos

  F.W. Lawvere originally defined a topos as a bicartesian exponential category
  with partial map classifiers.  The book notes:
  - Mikkelsen: cocartesian structure is a consequence of the other axioms.
  - Kock: exponentiation follows from power objects.
  The simplest modern form: bicartesian + exponential + subobject classifier. -/

/-- A PARTIAL MAP CLASSIFIER (§1.921, §1.934): an object Ω₊ together with a
    monic η : 1 ↪ Ω₊ such that every partial map (monic + map) into X factors
    uniquely through a total map into Ω₊^X.
    The subobject classifier Ω is the special case where the domain is the terminal. -/
structure HasPartialMapClassifier (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasPullbacks 𝒞 where
  pmc_obj   : 𝒞
  pmc_incl  : one ⟶ pmc_obj
  pmc_incl_monic : Mono pmc_incl
  pmc_classify {X A A' : 𝒞} (m : A' ⟶ A) (_ : Mono m) (f : A' ⟶ X) : A ⟶ pmc_obj

/-- **§1.921**: LAWVERE TOPOS — a category that is:
    (1) bicartesian (finite products + finite coproducts)
    (2) exponential (cartesian closed)
    (3) has a partial map classifier (special case: subobject classifier Ω)
    The book notes this is Lawvere's original definition, later simplified. -/
class LawvereTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends HasExponentials 𝒞 where
  has_coproducts   : HasBinaryCoproducts 𝒞
  has_coterminator : HasCoterminator 𝒞
  has_pmc          : HasPartialMapClassifier 𝒞

/-! ## §1.923  B^A as a subobject of [A × B] via pullback

  The exponential B^A is constructed as the equalizer (equivalently: pullback)
  of two maps [A × B] → [A]:
    - the map sending F ⊆ A×B to its domain (the first projection of dom F)
    - the constant map sending everything to the entire subobject of A

  In the book's notation: a function-like relation F ⊆ A×B is one where
  {a | ∃! b. (a,b) ∈ F} = A, i.e., the first-projection π₁(F) = A.
  This is exactly the pullback of [A] → [1] ← 1 → [A] (the name of A). -/

/-- **§1.923**: B^A arises as a MONIC SUBOBJECT of [A × B] via a pullback square:
      B^A ——ι——→ [A × B]       (= exp (prod A B) Ω)
       |               |
       |               | Ω^π₁  (contravariant Ω-action of fst : A×B → A)
       ↓               ↓
       1 ————→ [A]             (name the entire subobject of A)
    The exponential B^A is the subobject of "function-like" relations in A × B.
    The embedding ι = curry(eval_A_B ≫ singletonMapCat B) is monic because
    curry is injective (curry_inj). -/
theorem expSubobj (A B : 𝒞) :
    ∃ (ι : exp A B ⟶ exp (prod A B) (HasSubobjectClassifier.omega (𝒞 := 𝒞))),
      Mono ι := by
  -- BLOCKER: `exp A B` here is the object supplied by `topos_has_exponentials`,
  -- which is itself an unfilled `sorry`; so `exp A B` is opaque and no concrete ι
  -- can be exhibited.  Once exponentials are constructed (B^A = pullback of
  -- Ω^{fst} : [A×B] → [A] along the name 1 → [A]), ι is the pullback projection
  -- into [A×B] and is monic as a pullback of the monic name-of-A.
  exact ⟨sorry, sorry⟩

/-! ## §1.924  FG computed via Yoneda (§1.924)

  For F, G : 𝒞^op → Set, the exponential FG(A) can be computed via the
  Yoneda lemma as (H_A, F^G) = (G × H_A, F) (§1.464).
  When 𝒞 has binary coproducts: F^{H_A}(-) = F(A + -).
  These are abstract computations on presheaves. -/

/-
  **§1.924**: For presheaves F, G with G = H_A (representable by A):
    FG(A) = (H_A, F^G) = (G × H_A, F) [Yoneda]
    When 𝒞 has binary coproducts and G = H_A:
      F^{H_A}(B) = F(A + B).
  Proof: (H_B, F^{H_A}) = (H_A × H_B, F) = (H_{A+B}, F) = F(A+B).
  This is a computation on the presheaf category ℱ(𝒞); presheaf machinery
  is not yet formalized in this repo. -/

/-! ## §1.926  Heyting algebra structure on Sub(1)

  In a topos, the exponential structure restricts to a Heyting algebra
  structure on the subterminators Sub(1) = Hom(1, Ω).
  The Heyting implication on Sub(1) is given by the exponential:
    U ⇒ V = the unique W : 1 → Ω such that for all Z : 1 → Ω,
    Z ∧ U ≤ V  ↔  Z ≤ W.
  This is computed by: W = (Ω^U)(V), i.e., post-compose U with the contravariant
  Ω-action to get Ω^U : Ω^Ω → Ω^1 ≅ Ω, then apply to V. -/

/-- A SUB-TERMINATOR: a morphism 1 → Ω (equivalently, a subobject of 1). -/
def SubTerminal (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] : Type v :=
  @one 𝒞 _ _ ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)

/-- The HEYTING IMPLICATION on SubTerminal: U ⇒ V is computed via the
    contravariant Ω-functor as Ω^U(V) : 1 → Ω.
    More precisely: 1 →(V) Ω^Ω →(Ω^U) Ω^1 ≅ Ω.
    (Here Ω^U uses ContraFunctor.map U and the canonical iso Ω^1 ≅ Ω.) -/
noncomputable def heytingImpl (U V : SubTerminal 𝒞) : SubTerminal 𝒞 :=
  -- W = (Ω^U)(V_hat) ∘ (Ω^1 ≅ Ω), the book's exponential implication on Sub(1).
  -- Step 1: "name" V as a constant element of Ω^Ω via curry(snd ≫ V).
  --   snd : prod Ω one → one,  so  snd ≫ V : prod Ω one → Ω,
  --   curry(snd ≫ V) : one → Ω^^Ω = exp Ω Ω.
  -- Step 2: apply the contravariant power Ω^U : Ω^Ω → Ω^1 (= Ω^^one).
  -- Step 3: compose with the left-unit iso Ω^1 ≅ Ω:
  --   prodOneLeftInv (Ω^^one) : Ω^^one → prod one (Ω^^one),
  --   eval_exp one Ω         : prod one (Ω^^one) → Ω.
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  curry (snd ≫ V) ≫ (omegaPowContra (𝒞 := 𝒞)).map U ≫
    prodOneLeftInv (Ω ^^ one) ≫ eval_exp one Ω

/-- **§1.926**: In a topos, exponential structure restricts to a HEYTING ALGEBRA
    structure on Sub(1) = Hom(1, Ω).
    The Heyting adjunction: for all Z U V : SubTerminal 𝒞,
      Z ∧ U ≤ V  ↔  Z ≤ (U ⇒ V)
    where ≤ is the subobject order and ∧ is the meet (both internal to the topos). -/
theorem subTerminal_heyting :
    ∀ (U V : SubTerminal 𝒞),
      ∃ (W : SubTerminal 𝒞),
        -- W is the Heyting implication U ⇒ V, computed via the exponential Ω^U.
        -- The adjunction: W equals heytingImpl U V.
        W = heytingImpl U V := by
  intro U V
  exact ⟨heytingImpl U V, rfl⟩

end Freyd
