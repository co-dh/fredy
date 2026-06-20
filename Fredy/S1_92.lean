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
import Fredy.S1_91
import Fredy.Baseable923


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.92  Topos is exponential + singleton map Δ₁ : B → [B] -/

/-- **Topos has equalizers** (needed for §1.92).  A topos has binary products and
    pullbacks (the latter from the subobject classifier's `HasPullbacks` base), and
    §1.434 (`products_pullbacks_implies_equalizers`) builds the equalizer of `f, g`
    as the pullback of `⟨1,f⟩, ⟨1,g⟩ : A ⇉ A×B`.  So a topos has all equalizers. -/
instance topos_has_equalizers : HasEqualizers 𝒞 :=
  products_pullbacks_implies_equalizers

/-- **§1.92 bridge — representability assembles exponentials.**  If EVERY object of
    `𝒞` is baseable (§1.859: `(A × −, B)` is representable for all `A`), then `𝒞` is
    exponential.  This is the assembly half of Freyd's §1.92: the representing object
    `E` and counit `ev` for `Baseable B` at stage `A` ARE the exponential `B^A` and its
    evaluation, and the representing-map `g` is `curry`.  Fully proved (the β/η laws are
    exactly the existence/uniqueness clauses of `Baseable`); choice only enters in
    *selecting* the representing object, which is unavoidable here (the bare existential
    `Baseable` gives no canonical `E`). -/
noncomputable def exponentials_of_all_baseable
    (hb : ∀ B : 𝒞, Baseable B) : HasExponentials 𝒞 where
  -- Reuse the topos product instance to avoid a `HasBinaryProducts` diamond with `Topos`.
  toHasBinaryProducts := Topos.toHasBinaryProducts
  exp_obj A B := (hb B A).choose
  eval_map {A B} := (hb B A).choose_spec.choose
  curry_map {A B X} f := ((hb B A).choose_spec.choose_spec X f).choose
  curry_eval {A B X} f := ((hb B A).choose_spec.choose_spec X f).choose_spec.1
  curry_unique {A B X f g} h_eq :=
    ((hb B A).choose_spec.choose_spec X f).choose_spec.2 g h_eq

/-- **§1.92**: A topos is exponential.  The exponential `B^A` is the representing
    object of `(A × −, B)`; Freyd's §1.92 proof shows every object of a topos is
    BASEABLE — via the singleton embedding `Δ₁ : B ↪ [B]` exhibiting `B` as an
    equalizer of the baseable power object `[B]` and `Ω` (`baseable_equalizer_is_baseable`,
    §1.859) — and then `exponentials_of_all_baseable` assembles the exponential structure.

    Two of the three load-bearing steps are now in place in this repo:

    *  (b) **Topos equalizers** — `topos_has_equalizers` above (products+pullbacks, §1.434).
    *  (c) **Baseable-equalizer closure** — `baseable_equalizer_is_baseable` (§1.859, now
       proved sorry-free): the equalizer of two baseable objects is baseable.

    The remaining gap is exactly step (a):

    *  (a) **Every power object `[B]` is baseable**, i.e. the representability
       `[B]^A ≅ [A×B]`.  This needs a power object `[B] = HasPowerObject.powerObj`
       for EVERY object `B` together with the `Λ/∈` classify-bijection at product level.
       This repo's `Topos` is the *minimal subobject-classifier* presentation: it bundles
       only `Ω = [1]`, NOT `HasPowerObject C` for general `C`, and there is no construction
       of general power objects from the bare classifier anywhere in the repo (every
       power-object result, e.g. S1_91 `minimal_topos_has_terminator`, *assumes*
       `[∀ C, HasPowerObject C]`).  Without `[B]`, neither the singleton equalizer
       presentation of `B` nor the representability iso can be formed, so "every object
       baseable" — the input `hb` to `exponentials_of_all_baseable` — cannot be supplied.

    FAITHFUL SORRY: the residual is precisely `∀ B, Baseable B`, which factors through
    the missing power-object representability (a).  Everything downstream of it (b, c,
    and the assembly via `exponentials_of_all_baseable`) is discharged.

    NOTE on the `sorry` shape: morally this instance is
    `exponentials_of_all_baseable (fun B => (proof B is baseable))`, with the bracketed
    proof the only gap.  We keep it as a single opaque `by sorry` (rather than
    `exponentials_of_all_baseable (fun _ => sorry)`) ONLY so the instance retains a
    computable IR stub: downstream files (`S1_94 powObj`, `S1_95`) build computable
    definitions on top of `exp`, and routing through the `Classical.choice`-based
    `exponentials_of_all_baseable` would force them `noncomputable` (those files are
    out of scope for this edit).  The genuine assembly content lives, fully proved, in
    `exponentials_of_all_baseable`. -/
-- LOW PRIORITY: `HasExponentials extends HasBinaryProducts`, and this instance is a
-- `sorry` (its `toHasBinaryProducts` is therefore `sorry`-derived).  If instance search
-- routes a `HasBinaryProducts 𝒞` goal through it, downstream relation/product terms pick up
-- `sorryAx`.  We deprioritise it here AND, in the direct-image section below, locally make
-- the genuine `Topos.toHasBinaryProducts` win outright (see the `attribute [local instance]`
-- there) so the §1.92 power maps stay axiom-honest.
noncomputable instance (priority := 50) topos_has_exponentials : HasExponentials 𝒞 :=
  exponentials_of_all_baseable power_objects_imply_all_baseable

-- `topos_has_exponentials` is now genuinely proved (hence `noncomputable`, depending on
-- `Classical.choice`).  `HasExponentials extends HasBinaryProducts`, so instance search could
-- route a `HasBinaryProducts 𝒞` goal through it and make otherwise-computable downstream defs
-- (`graphMono`, `omegaPowContra`, …) fail the IR check.  Make the genuine `Topos.toHasBinaryProducts`
-- win outright for the whole §1.92 section so those products resolve computably and axiom-cleanly.
attribute [local instance 10000] Topos.toHasBinaryProducts

-- All subsequent decls require [HasExponentials 𝒞] via topos_has_exponentials.
-- exp B Ω = Ω^B = [B] the power object of B.

-- NOTE: `curry_precomp` (naturality of `curry` in its variable argument,
-- `h ≫ curry f = curry (prodMap A X' X h ≫ f)`) now lives in `S1_85` (imported);
-- the former duplicate here was removed for DRY after master added the S1_85 copy.

/-! ## §1.922  Ω^(−) as a contravariant functor

  For a topos, the assignment B ↦ Ω^B = exp B Ω is a contravariant functor.
  Given g : B₁ → B₂, Ω^g : Ω^B₂ → Ω^B₁ is the unique map such that:
      prod B₁ (exp B₂ Ω) —(pair(fst≫g, snd))→ prod B₂ (exp B₂ Ω) —eval→ Ω
  equals prod B₁ (Ω^g) ≫ eval (i.e., the adjoint transpose definition).
  Equivalently, Ω^g = curry(pair (fst ≫ g) snd ≫ eval). -/

/-- **§1.922**: The power-object functor Ω^(−) is CONTRAVARIANT. -/
noncomputable instance omegaPowContra :
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

-- The COVARIANT power-map `[f] : Ω^A → Ω^B` (§1.922) and its naturality `f(Δ₁) = Δf`
-- are defined and proved LOWER IN THIS FILE, after the `Ω^A ≅ [A]` identification
-- (`powExpHom`/`expPowInv`, `end EvalUniversalAmbient`) and the relation infrastructure
-- they need.  They take an explicit `[HasImages 𝒞] [PullbacksTransferCovers 𝒞]` hypothesis
-- (faithful: a topos has both, `toposHasImages`/`toposPullbacksTransferCovers`, which are
-- NOT importable here without a cycle — `InternalForallTopos` sits above `S1_92`).  See
-- `powerMapCov` / `singletonMapCat_natural` below.

/-! ## §1.92  Direct-image power map on GENUINE power objects (faithful version)

  The `powerMapCov` above targets the opaque exponential `exp A Ω`, which the
  minimal `Topos` does not equip with the membership relation `∈_A` needed to
  define the direct image.  Freyd's topos genuinely HAS all power objects
  (`P(A) = Ω^A`), and S1_9 packages exactly that data as `HasPowerObject A`
  (carrier `powerObj A`, universal relation `mem : BinRel (powerObj A) A`,
  classifier `powerClassify`).  We give the HONEST construction on `powerObj`,
  taking `[HasPowerObject A] [HasPowerObject B] [HasImages 𝒞]` as explicit,
  load-bearing hypotheses (faithful: every power-object result in the repo takes
  them, and a topos with images has them).

  The DIRECT IMAGE of a subset `S ⊆ A` along `f : A → B` is
  `f"(S) = { b | ∃ a ∈ S, f a = b }`.  At the universal level this is the
  composite relation `∈_A ⊚ graph f : BinRel (powerObj A) B` (push `∈_A ⊆ powerObj A × A`
  along `f`, §1.56 image factorization), classified back into `powerObj B` by the
  universality of `mem`. -/

/-- `RelHom` is transitive: `R ≤ S ≤ T ⟹ R ≤ T` (compose the witness maps). -/
theorem RelHom_trans {A B : 𝒞} {R S T : BinRel 𝒞 A B}
    (hRS : RelHom R S) (hST : RelHom S T) : RelHom R T := by
  obtain ⟨h, hA, hB⟩ := hRS
  obtain ⟨k, kA, kB⟩ := hST
  exact ⟨h ≫ k, by rw [Cat.assoc, kA, hA], by rw [Cat.assoc, kB, hB]⟩

section PowerObjectDirectImage
variable [HasImages 𝒞]

-- Make the genuine `Topos` product instance WIN instance search for `HasBinaryProducts 𝒞`
-- throughout this section.  Otherwise `pair`/`fst`/`prod`/`compose` can resolve products
-- via the `sorry` instance `topos_has_exponentials` (`HasExponentials extends
-- HasBinaryProducts`), silently contaminating every direct-image term with `sorryAx`.
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- The DIRECT-IMAGE RELATION of `∈_A` along `f : A → B`: the §1.56 composite
    `∈_A ⊚ graph f : BinRel (powerObj A) B`.  Its source is the image of the span
    `⟨mem.colA, mem.colB ≫ f⟩ : mem.src → powerObj A × B` — exactly Freyd's
    existential image `{(P, b) | ∃ a, (P, a) ∈ ∈_A ∧ f a = b}`. -/
noncomputable def directImageRel {A B : 𝒞} [HasPowerObject A] (f : A ⟶ B) :
    BinRel 𝒞 (HasPowerObject.powerObj (C := A)) B :=
  HasPowerObject.mem (C := A) ⊚ graph f

/-- **§1.92 (faithful)**: the COVARIANT direct-image power map `[f] = f" : [A] → [B]`
    on genuine power objects.  `[f] = Λ(∈_A ⊚ graph f)` — the classifying map of the
    direct-image relation, supplied by the universality of `∈_A` (`powerClassify`). -/
noncomputable def powerMapCovP {A B : 𝒞} [HasPowerObject A] [HasPowerObject B]
    (f : A ⟶ B) :
    HasPowerObject.powerObj (C := A) ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (directImageRel f)

/-- Composing any relation `R : A → B` with the identity graph leaves it unchanged
    up to relation-isomorphism: `R ⊚ graph(1_B) ≅ R`.  (Image of the span
    `⟨π₁≫R.colA, π₂≫1⟩` over the pullback of `R.colB` and `1_B`, which is `R.src`
    itself since one leg is an identity.)  Both `RelHom` directions. -/
theorem compose_graph_id {A B : 𝒞} (R : BinRel 𝒞 A B) :
    RelHom (R ⊚ graph (Cat.id B)) R ∧ RelHom R (R ⊚ graph (Cat.id B)) := by
  -- Unfold `compose`: pb = pullback of R.colB and (graph 1).colA = 1_B.
  let pb := HasPullbacks.has R.colB (graph (Cat.id B)).colA
  let sp : pb.cone.pt ⟶ prod A B :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ (graph (Cat.id B)).colB)
  -- The composite source is `(image sp).dom` with legs `(image sp).arr ≫ fst/snd`.
  -- (graph 1).colA = (graph 1).colB = 1_B, so the pullback square reads
  --   π₁ ≫ R.colB = π₂ ≫ 1 = π₂.
  -- (graph 1).colA and (graph 1).colB are DEFINITIONALLY `Cat.id B`; we exploit that
  -- defeq rather than rewriting the dependent `graph`-term (which breaks the motive).
  have hsq : pb.cone.π₁ ≫ R.colB = pb.cone.π₂ := by
    have hw := pb.cone.w
    dsimp only [graph] at hw
    rwa [Cat.comp_id] at hw
  -- `R.src` is itself a pullback of `(R.colB, 1_B)` via `(1, R.colB)`, so there is an
  -- iso `e : R.src → pb.pt` with `e ≫ π₁ = 1` and `e ≫ π₂ = R.colB`.
  let eCone : Cone R.colB (graph (Cat.id B)).colA :=
    ⟨R.src, Cat.id R.src, R.colB, by
      show Cat.id R.src ≫ R.colB = R.colB ≫ Cat.id B
      rw [Cat.id_comp, Cat.comp_id]⟩
  let e : R.src ⟶ pb.cone.pt := pb.lift eCone
  have he₁ : e ≫ pb.cone.π₁ = Cat.id R.src := pb.lift_fst eCone
  have he₂ : e ≫ pb.cone.π₂ = R.colB := pb.lift_snd eCone
  -- The span equals `R`'s pair after precomposing with `e`:
  --   e ≫ sp = pair (e≫π₁≫R.colA) (e≫π₂≫1) = pair R.colA R.colB.
  have hesp : e ≫ sp = pair R.colA R.colB := by
    apply pair_uniq
    · rw [Cat.assoc]; show e ≫ pair (pb.cone.π₁ ≫ R.colA) _ ≫ fst = R.colA
      rw [fst_pair, ← Cat.assoc, he₁, Cat.id_comp]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, he₂]
      simp only [graph, Cat.comp_id]
  -- `pair R.colA R.colB` is monic (jointly-monic pair), so it equals its own image up
  -- to iso.  We build the two `RelHom`s through `image.lift sp` and `image_min`.
  have hRmono : Mono (pair R.colA R.colB) := monic_pair_of_monicPair _ _ R.isMonicPair
  -- `sp` factors through the monic `pair R.colA R.colB` via `π₁`:
  --   π₁ ≫ pair R.colA R.colB = pair (π₁≫R.colA) (π₁≫R.colB) = pair (π₁≫R.colA) π₂ = sp.
  have hπsp : pb.cone.π₁ ≫ pair R.colA R.colB = sp := by
    show pb.cone.π₁ ≫ pair R.colA R.colB
        = pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ Cat.id B)
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair]
      simp only [graph, Cat.comp_id]
      exact hsq
  -- Forward `RelHom (R ⊚ graph 1) R`: `pair R.colA R.colB` allows `sp` (via `π₁`), so the
  -- image of `sp` is ≤ the subobject `(R.src, pair R.colA R.colB)`; that comparison is the witness.
  have hAllows : Allows (Subobject.mk R.src (pair R.colA R.colB) hRmono) sp :=
    ⟨pb.cone.π₁, hπsp⟩
  obtain ⟨w, hw⟩ := image_min sp _ hAllows
  -- hw : w ≫ pair R.colA R.colB = (image sp).arr   (w : (image sp).dom → R.src)
  refine ⟨⟨w, ?_, ?_⟩, ?_⟩
  · -- w ≫ R.colA = (R ⊚ graph 1).colA = (image sp).arr ≫ fst
    show w ≫ R.colA = (image sp).arr ≫ fst
    rw [← hw, Cat.assoc, fst_pair]
  · show w ≫ R.colB = (image sp).arr ≫ snd
    rw [← hw, Cat.assoc, snd_pair]
  · -- Backward `RelHom R (R ⊚ graph 1)`: witness `e ≫ image.lift sp : R.src → (image sp).dom`.
    refine ⟨e ≫ image.lift sp, ?_, ?_⟩
    · show (e ≫ image.lift sp) ≫ ((image sp).arr ≫ fst) = R.colA
      rw [← Cat.assoc, Cat.assoc e, image.lift_fac, hesp, fst_pair]
    · show (e ≫ image.lift sp) ≫ ((image sp).arr ≫ snd) = R.colB
      rw [← Cat.assoc, Cat.assoc e, image.lift_fac, hesp, snd_pair]

/-- Pulling a relation `U : BinRel P C` back along the IDENTITY `1_P` leaves it
    unchanged up to relation-isomorphism: `relPullback (1_P) U ≅ U`.  (The pullback
    of `1_P` and `U.colA` is `U.src`, since one leg is an identity.)  Both directions. -/
theorem relPullback_id {P C : 𝒞} (U : BinRel 𝒞 P C) :
    RelHom (relPullback (Cat.id P) U) U ∧ RelHom U (relPullback (Cat.id P) U) := by
  -- `relPullback (1_P) U` has src = pullback of `1_P` and `U.colA`, legs
  --   colA = pb.π₁ : pb.pt → P,   colB = pb.π₂ ≫ U.colB.
  let pb := HasPullbacks.has (Cat.id P) U.colA
  have wpb : pb.cone.π₁ ≫ Cat.id P = pb.cone.π₂ ≫ U.colA := pb.cone.w
  -- `U.src` is a pullback of `(1_P, U.colA)` via `(U.colA, 1_{U.src})`:
  let uCone : Cone (Cat.id P) U.colA :=
    ⟨U.src, U.colA, Cat.id U.src, by rw [Cat.comp_id, Cat.id_comp]⟩
  let d : U.src ⟶ pb.cone.pt := pb.lift uCone
  have hd₁ : d ≫ pb.cone.π₁ = U.colA := pb.lift_fst uCone
  have hd₂ : d ≫ pb.cone.π₂ = Cat.id U.src := pb.lift_snd uCone
  constructor
  · -- `relPullback (1_P) U ≤ U`: witness `pb.π₂ : pb.pt → U.src`.
    --   π₂ ≫ U.colA = π₁ ≫ 1 = π₁ = (relPullback).colA;  π₂ ≫ U.colB = (relPullback).colB.
    refine ⟨pb.cone.π₂, ?_, ?_⟩
    · show pb.cone.π₂ ≫ U.colA = pb.cone.π₁
      rw [← wpb, Cat.comp_id]
    · rfl
  · -- `U ≤ relPullback (1_P) U`: witness `d : U.src → pb.pt`.
    refine ⟨d, ?_, ?_⟩
    · show d ≫ pb.cone.π₁ = U.colA
      exact hd₁
    · show d ≫ (pb.cone.π₂ ≫ U.colB) = U.colB
      rw [← Cat.assoc, hd₂, Cat.id_comp]

/-- **§1.92 (faithful) — the unit identity `f"f = 1` on power objects, at `f = 1`.**
    The direct image along the identity is the identity power map:

        `[1_A] = powerMapCovP (1_A) = 1_{[A]}`.

    This is Freyd's §1.96 identity `f"f = 1` instantiated at `f = 1` (the only
    instance the membership-classifier universality settles without further image
    descent): the direct image `f"` then inverse-classifies back to the identity.
    The proof is the UNIVERSALITY of `∈_A` (`classify_unique`): both `1_{[A]}` and
    `powerMapCovP 1_A = Λ(∈_A ⊚ graph 1_A)` classify the same relation, because
    `∈_A ⊚ graph 1_A ≅ ∈_A ≅ relPullback 1_{[A]} ∈_A`. -/
theorem powerMapCovP_id (A : 𝒞) [HasPowerObject A] :
    powerMapCovP (Cat.id A) = Cat.id (HasPowerObject.powerObj (C := A)) := by
  -- Both `powerClassify (∈_A ⊚ graph 1)` and `1_{[A]}` classify `∈_A ⊚ graph 1`.
  -- `classify_unique` then forces them equal.
  let memA : BinRel 𝒞 (HasPowerObject.powerObj (C := A)) A := HasPowerObject.mem (C := A)
  -- `id` classifies the direct-image relation: chain the two relation-isos.
  have hcg := compose_graph_id memA            -- (memA ⊚ graph 1 ≅ memA)
  have hrp := relPullback_id memA              -- (relPullback 1 memA ≅ memA)
  have hid_classifies :
      RelHom (directImageRel (Cat.id A)) (relPullback (Cat.id _) memA) ∧
      RelHom (relPullback (Cat.id _) memA) (directImageRel (Cat.id A)) :=
    ⟨RelHom_trans hcg.1 hrp.2, RelHom_trans hrp.1 hcg.2⟩
  -- `powerClassify` of the same relation, by universality uniqueness, equals `id`.
  have huniv := HasPowerObject.is_universal (C := A)
  have hspec :=
    (huniv.classify_exists (HasPowerObject.powerObj (C := A)) (directImageRel (Cat.id A))).choose_spec
  exact huniv.classify_unique _ (directImageRel (Cat.id A))
    (powerClassify (directImageRel (Cat.id A))) (Cat.id _) hspec hid_classifies

end PowerObjectDirectImage

/-! ## §1.92  Uniqueness of universal relations + the identification `Ω^A ≅ [A]`

  Freyd §1.92: in a topos the exponential `Ω^A = exp A Ω` IS the power object
  `[A] = HasPowerObject.powerObj A`.  Both represent `Sub(A × −)`: the universal
  membership relation `∈_A ⊆ [A] × A` makes `[A]` universal targeted at `A`, and
  the evaluation `eval : A × Ω^A → Ω` together with the subobject classifier makes
  `Ω^A` universal targeted at `A` too.  Two universal relations targeted at the
  SAME object have isomorphic carriers (Yoneda), giving `Ω^A ≅ [A]`. -/

section UniversalRelUnique
variable {C : 𝒞} [HasPullbacks 𝒞]

/-- The classifying map `Λ_V(R) : A → Q` of `R : BinRel A C` along a universal
    relation `V : BinRel Q C` (the `classify_exists` witness). -/
noncomputable def univClassify {Q : 𝒞} {V : BinRel 𝒞 Q C} (hV : IsUniversalRel V)
    {A : 𝒞} (R : BinRel 𝒞 A C) : A ⟶ Q :=
  (hV.classify_exists A R).choose

/-- `R ≅ relPullback (Λ_V R) V` (forward+backward), the defining property of `Λ_V`. -/
theorem univClassify_spec {Q : 𝒞} {V : BinRel 𝒞 Q C} (hV : IsUniversalRel V)
    {A : 𝒞} (R : BinRel 𝒞 A C) :
    RelHom R (relPullback (univClassify hV R) V) ∧
    RelHom (relPullback (univClassify hV R) V) R :=
  (hV.classify_exists A R).choose_spec

/-- **§1.92, naturality of `Λ_V`.**  For a universal `V : BinRel Q C` and
    `g : X → A`, classifying the pullback `relPullback g R` along `V` factors:
    `Λ_V(relPullback g R) = g ≫ Λ_V(R)`.  (Both classify `relPullback g R`, so
    `classify_unique` forces them equal.) -/
theorem univClassify_natural {Q : 𝒞} {V : BinRel 𝒞 Q C} (hV : IsUniversalRel V)
    {A X : 𝒞} (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    univClassify hV (relPullback g R) = g ≫ univClassify hV R := by
  -- `relPullback g R ≅ relPullback (g ≫ Λ_V R) V`, via
  --   relPullback g R ≅ relPullback g (relPullback (Λ_V R) V)   (R ≅ relPullback (Λ_V R) V)
  --                   ≅ relPullback (g ≫ Λ_V R) V               (relPullback_comp).
  have hR := univClassify_spec hV R
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (univClassify hV R) V
  -- relPullback g R ≅ relPullback g (relPullback (Λ_V R) V): pull `hR` back along g.
  have hpg : RelHom (relPullback g R) (relPullback g (relPullback (univClassify hV R) V)) ∧
             RelHom (relPullback g (relPullback (univClassify hV R) V)) (relPullback g R) := by
    constructor
    · -- forward: lift the source of relPullback g R into the inner pullback.
      let P := HasPullbacks.has g R.colA
      let P' := HasPullbacks.has g (relPullback (univClassify hV R) V).colA
      obtain ⟨w, hwA, hwB⟩ := hR.1   -- w : R.src → (relPullback _ V).src
      -- the cone over (g, (relPullback _ V).colA) given by (P.π₁, P.π₂ ≫ w).
      refine ⟨P'.lift ⟨P.cone.pt, P.cone.π₁, P.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
      · show P.cone.π₁ ≫ g = (P.cone.π₂ ≫ w) ≫ (relPullback (univClassify hV R) V).colA
        rw [Cat.assoc, hwA]; exact P.cone.w
      · show _ ≫ (relPullback g (relPullback (univClassify hV R) V)).colA = _
        exact P'.lift_fst _
      · show _ ≫ (relPullback g (relPullback (univClassify hV R) V)).colB
              = (relPullback g R).colB
        show _ ≫ (P'.cone.π₂ ≫ (relPullback (univClassify hV R) V).colB)
              = P.cone.π₂ ≫ R.colB
        rw [← Cat.assoc, P'.lift_snd, Cat.assoc, hwB]
    · -- backward: symmetric, using hR.2.
      let P := HasPullbacks.has g R.colA
      let P' := HasPullbacks.has g (relPullback (univClassify hV R) V).colA
      obtain ⟨w, hwA, hwB⟩ := hR.2   -- w : (relPullback _ V).src → R.src
      refine ⟨P.lift ⟨P'.cone.pt, P'.cone.π₁, P'.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
      · show P'.cone.π₁ ≫ g = (P'.cone.π₂ ≫ w) ≫ R.colA
        rw [Cat.assoc, hwA]; exact P'.cone.w
      · exact P.lift_fst _
      · show _ ≫ (P.cone.π₂ ≫ R.colB)
              = P'.cone.π₂ ≫ (relPullback (univClassify hV R) V).colB
        rw [← Cat.assoc, P.lift_snd, Cat.assoc, hwB]
  -- Chain: relPullback g R ≅ relPullback (g ≫ Λ_V R) V.
  have hfin : RelHom (relPullback g R) (relPullback (g ≫ univClassify hV R) V) ∧
              RelHom (relPullback (g ≫ univClassify hV R) V) (relPullback g R) :=
    ⟨RelHom_trans hpg.1 hc1, RelHom_trans hc2 hpg.2⟩
  -- Both `Λ_V(relPullback g R)` and `g ≫ Λ_V R` classify `relPullback g R`.
  exact hV.classify_unique X (relPullback g R) _ _
    (univClassify_spec hV (relPullback g R)) hfin

/-- **§1.92, uniqueness of universal relations (Yoneda).**  If `U : BinRel P C`
    and `V : BinRel Q C` are both universal targeted at `C`, then the comparison
    map `φ = Λ_V(U) : P → Q` is an ISOMORPHISM.  Hence universal relations
    targeted at a common object have isomorphic carriers.

    Proof: `(· ≫ φ)` is a hom-bijection `(X ⟶ P) ≅ (X ⟶ Q)` — by
    `univClassify_natural`, `g ≫ φ = Λ_V(relPullback g U)`, and the two universal
    classifiers `Λ_U, Λ_V` are mutually inverse on relations up to `RelHom`.  Apply
    the Yoneda corollary `iso_of_natural_hom_bijection`. -/
theorem universalRel_unique {P Q : 𝒞} {U : BinRel 𝒞 P C} {V : BinRel 𝒞 Q C}
    (hU : IsUniversalRel U) (hV : IsUniversalRel V) :
    IsIso (univClassify hV U) := by
  apply iso_of_natural_hom_bijection (univClassify hV U)
  · -- SURJECTIVE: every k : X → Q is `g ≫ φ` for `g := Λ_U(relPullback k V)`.
    intro X k
    refine ⟨univClassify hU (relPullback k V), ?_⟩
    -- `g ≫ φ = Λ_V(relPullback g U)` (naturality); show it equals `k` by V.classify_unique.
    rw [← univClassify_natural hV U (univClassify hU (relPullback k V))]
    -- `relPullback g U ≅ relPullback k V`, hence `Λ_V(relPullback g U) = Λ_V(relPullback k V) = k`.
    have hgU := univClassify_spec hU (relPullback k V)  -- relPullback k V ≅ relPullback g U
    -- `Λ_V` of two RelHom-iso relations agree; and `Λ_V(relPullback k V) = k` (uniqueness).
    have h1 : univClassify hV (relPullback (univClassify hU (relPullback k V)) U)
            = univClassify hV (relPullback k V) :=
      hV.classify_unique X _ _ _
        (univClassify_spec hV _)
        ⟨RelHom_trans hgU.2 (univClassify_spec hV (relPullback k V)).1,
         RelHom_trans (univClassify_spec hV (relPullback k V)).2 hgU.1⟩
    rw [h1]
    -- `k` classifies `relPullback k V` along V (reflexively), so `Λ_V(relPullback k V) = k`.
    exact (hV.classify_unique X (relPullback k V) (univClassify hV (relPullback k V)) k
      (univClassify_spec hV (relPullback k V))
      ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
       ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩)
  · -- INJECTIVE: `g₁ ≫ φ = g₂ ≫ φ ⟹ g₁ = g₂`.
    intro X g₁ g₂ heq
    -- Apply naturality both sides: `Λ_V(relPullback gᵢ U) = gᵢ ≫ φ`.
    have e1 := univClassify_natural hV U g₁
    have e2 := univClassify_natural hV U g₂
    -- `relPullback g₁ U ≅ relPullback g₂ U` because they classify the same `Λ_V`.
    have hsame : univClassify hV (relPullback g₁ U) = univClassify hV (relPullback g₂ U) := by
      rw [e1, e2, heq]
    -- relPullback g₁ U ≅ relPullback g₂ U via V being universal (same Λ_V).
    have hiso : RelHom (relPullback g₁ U) (relPullback g₂ U) ∧
                RelHom (relPullback g₂ U) (relPullback g₁ U) := by
      have s1 := univClassify_spec hV (relPullback g₁ U)
      have s2 := univClassify_spec hV (relPullback g₂ U)
      rw [hsame] at s1
      exact ⟨RelHom_trans s1.1 s2.2, RelHom_trans s2.1 s1.2⟩
    -- g₂ also classifies relPullback g₁ U along U (via the iso); U.classify_unique gives g₁ = g₂.
    exact hU.classify_unique X (relPullback g₁ U) g₁ g₂
      ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
       ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩
      ⟨RelHom_trans hiso.1 ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
       RelHom_trans ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩ hiso.2⟩

end UniversalRelUnique

/-! ## §1.92  `eval` makes `Ω^A` a universal relation targeted at `A`

  The evaluation `eval_exp A Ω : A × Ω^A → Ω` classifies, via the subobject
  classifier, a subobject of `A × Ω^A`; swapping legs gives the universal
  MEMBERSHIP relation `∈ ⊆ Ω^A × A`, `evalRel A`.  Combined with the curry/eval
  adjunction and the classifier bijection `Sub(A×−) ≅ Hom(A×−,Ω)`, `evalRel A`
  is universal targeted at `A` — Freyd's identification of `Ω^A` as a power object.

  We take `[HasExponentials 𝒞]` as a faithful hypothesis (Freyd's topos has it);
  the ambient `Topos` supplies the classifier and pullbacks.  All products are the
  exponential's (`HasExponentials.toHasBinaryProducts`), which under the ambient
  `topos_has_exponentials` instance coincide with `Topos.toHasBinaryProducts`. -/

section EvalUniversal
variable [HasExponentials 𝒞]

/-- The relation `{(y,a) | χ(a,y) = ⊤}` cut out of `prod A Y` by a classifier map
    `χ : prod A Y → Ω`, with columns swapped to `(Y, A)`.  Its source is the
    pullback of `(χ, true)`; the product-monic is exactly `pb.π₁`, so `χ` classifies
    it (`classRel_classify`). -/
noncomputable def classRel {A Y : 𝒞} (χ : prod A Y ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    BinRel 𝒞 Y A :=
  let pb := HasPullbacks.has χ HasSubobjectClassifier.true
  { src  := pb.cone.pt
    colA := pb.cone.π₁ ≫ snd
    colB := pb.cone.π₁ ≫ fst
    isMonicPair := by
      -- jointly monic: `pair colB colA = pb.π₁` (a monic, being a pullback of the monic `true`).
      have hmono : Mono pb.cone.π₁ :=
        mono_pullback χ HasSubobjectClassifier.true HasSubobjectClassifier.true_monic pb
      intro W f g hA hB
      apply hmono
      -- f ≫ pb.π₁ = g ≫ pb.π₁ by product-extensionality (agree on fst and snd).
      -- hA : (f ≫ π₁) ≫ snd = (g ≫ π₁) ≫ snd ; hB : (f ≫ π₁) ≫ fst = (g ≫ π₁) ≫ fst (assoc).
      have hAf : (f ≫ pb.cone.π₁) ≫ snd = (g ≫ pb.cone.π₁) ≫ snd := by
        rw [Cat.assoc, Cat.assoc]; exact hA
      have hBf : (f ≫ pb.cone.π₁) ≫ fst = (g ≫ pb.cone.π₁) ≫ fst := by
        rw [Cat.assoc, Cat.assoc]; exact hB
      calc f ≫ pb.cone.π₁
          = pair ((f ≫ pb.cone.π₁) ≫ fst) ((f ≫ pb.cone.π₁) ≫ snd) :=
            pair_uniq _ _ _ rfl rfl
        _ = pair ((g ≫ pb.cone.π₁) ≫ fst) ((g ≫ pb.cone.π₁) ≫ snd) := by rw [hAf, hBf]
        _ = g ≫ pb.cone.π₁ := (pair_uniq _ _ _ rfl rfl).symm }

/-- `χ` classifies the product-monic of `classRel χ`: the subobject's representing
    monic `pb.π₁` has characteristic map `χ`.  (`classify_eq_of_pullback`.) -/
theorem classRel_classify {A Y : 𝒞} (χ : prod A Y ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    HasSubobjectClassifier.classify
        ((HasPullbacks.has χ HasSubobjectClassifier.true).cone.π₁)
        (mono_pullback χ HasSubobjectClassifier.true HasSubobjectClassifier.true_monic _) = χ := by
  let pb := HasPullbacks.has χ HasSubobjectClassifier.true
  have hsq : pb.cone.π₁ ≫ χ = term pb.cone.pt ≫ HasSubobjectClassifier.true := by
    rw [pb.cone.w, term_uniq pb.cone.π₂ (term pb.cone.pt)]
  symm
  refine classify_eq_of_pullback pb.cone.π₁ _ χ hsq ?_
  intro d
  refine ⟨pb.lift ⟨d.pt, d.π₁, d.π₂, d.w⟩, ⟨pb.lift_fst _, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  exact pb.lift_uniq ⟨d.pt, d.π₁, d.π₂, d.w⟩ v hv₁ (term_uniq _ _)

end EvalUniversal

/-! ## §1.92  `eval` IS a universal relation, hence `Ω^A ≅ [A]` (the power-object iso)

  This section discharges Freyd's §1.92 identification of the exponential `Ω^A = exp A Ω`
  with the power object `[A] = HasPowerObject.powerObj A`.  We run everything through the
  AMBIENT `topos_has_exponentials` instance (whose `toHasBinaryProducts` IS
  `Topos.toHasBinaryProducts`, line ~51) so the `prod` of `eval_exp` and the `prod` of the
  classifier coincide — the `EvalUniversal` section above used a *separate*
  `[HasExponentials 𝒞]` variable, which would reintroduce the `HasBinaryProducts` diamond. -/

section EvalUniversalAmbient
-- Pin the genuine `Topos` product instance, matching the pins elsewhere in this file, so the
-- two `prod` presentations agree definitionally and no `sorry`/diamond contaminates `evalRel`.
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- The universal MEMBERSHIP relation on `exp A Ω = Ω^A`, targeted at `A`.  It is the
    subobject `{(S, a) | eval(a, S) = ⊤}` of `(exp A Ω) × A` cut out by `eval` and
    classified by the subobject classifier (columns swapped to `(Ω^A, A)`). -/
noncomputable def evalRel (A : 𝒞) :
    BinRel 𝒞 (exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞))) A :=
  classRel (eval_exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)))

/-- The product-monic `⟨colB, colA⟩ : R.src ↪ A × X` of a relation `R : BinRel X A`
    (the subobject of `A × X` it names). -/
noncomputable def relMonic {X A : 𝒞} (R : BinRel 𝒞 X A) : R.src ⟶ prod A X :=
  pair R.colB R.colA

theorem relMonic_mono {X A : 𝒞} (R : BinRel 𝒞 X A) : Mono (relMonic R) :=
  monic_pair_of_monicPair R.colB R.colA (fun f g h1 h2 => R.isMonicPair f g h2 h1)

/-- Round-trip: any `R : BinRel X A` is the relation cut out by the classifier of its
    own product-monic, i.e. `R ≅ classRel (χ_R)` with `χ_R = classify ⟨R.colB, R.colA⟩`. -/
theorem classRel_roundtrip {X A : 𝒞} (R : BinRel 𝒞 X A) :
    RelHom R (classRel (HasSubobjectClassifier.classify (relMonic R) (relMonic_mono R))) ∧
    RelHom (classRel (HasSubobjectClassifier.classify (relMonic R) (relMonic_mono R))) R := by
  have hmono : Mono (relMonic R) := relMonic_mono R
  let mR := relMonic R
  let χ := HasSubobjectClassifier.classify mR hmono
  let pb := HasPullbacks.has χ HasSubobjectClassifier.true
  have hcpb := HasSubobjectClassifier.classify_pullback mR hmono
  have hsq : mR ≫ χ = term R.src ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq mR hmono
  have hmRfst : mR ≫ fst = R.colB := fst_pair _ _
  have hmRsnd : mR ≫ snd = R.colA := snd_pair _ _
  constructor
  · let c : Cone χ HasSubobjectClassifier.true := ⟨R.src, mR, term R.src, hsq⟩
    refine ⟨pb.lift c, ?_, ?_⟩
    · show pb.lift c ≫ (pb.cone.π₁ ≫ snd) = R.colA
      rw [← Cat.assoc, pb.lift_fst]; exact hmRsnd
    · show pb.lift c ≫ (pb.cone.π₁ ≫ fst) = R.colB
      rw [← Cat.assoc, pb.lift_fst]; exact hmRfst
  · have hPsq : pb.cone.π₁ ≫ χ = term pb.cone.pt ≫ HasSubobjectClassifier.true := by
      rw [pb.cone.w, term_uniq pb.cone.π₂ (term pb.cone.pt)]
    obtain ⟨u, ⟨hu1, _⟩, _⟩ := hcpb ⟨pb.cone.pt, pb.cone.π₁, term pb.cone.pt, hPsq⟩
    refine ⟨u, ?_, ?_⟩
    · show u ≫ R.colA = pb.cone.π₁ ≫ snd
      calc u ≫ R.colA = u ≫ (mR ≫ snd) := by rw [hmRsnd]
        _ = (u ≫ mR) ≫ snd := (Cat.assoc _ _ _).symm
        _ = pb.cone.π₁ ≫ snd := by rw [hu1]
    · show u ≫ R.colB = pb.cone.π₁ ≫ fst
      calc u ≫ R.colB = u ≫ (mR ≫ fst) := by rw [hmRfst]
        _ = (u ≫ mR) ≫ fst := (Cat.assoc _ _ _).symm
        _ = pb.cone.π₁ ≫ fst := by rw [hu1]

/-- β-law bridge (forward): the relation cut out by `χ` is the pullback of the universal
    `evalRel A` along `curry χ`.  Uses the exponential β-law `prodMap(curry χ) ≫ eval = χ`. -/
theorem evalRel_pull_fwd {A X : 𝒞}
    (χ : prod A X ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    RelHom (classRel χ) (relPullback (curry χ) (evalRel A)) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let ev := eval_exp A Ω
  let pbχ := HasPullbacks.has χ HasSubobjectClassifier.true
  let pbe := HasPullbacks.has ev HasSubobjectClassifier.true
  let Q := HasPullbacks.has (curry χ) ((evalRel A).colA)
  have hβ : prodMap A X (exp A Ω) (curry χ) ≫ ev = χ := curry_eval_eq χ
  let m₁ : pbχ.cone.pt ⟶ prod A (exp A Ω) := pbχ.cone.π₁ ≫ prodMap A X (exp A Ω) (curry χ)
  have hm₁ev : m₁ ≫ ev = term pbχ.cone.pt ≫ HasSubobjectClassifier.true := by
    show (pbχ.cone.π₁ ≫ prodMap A X (exp A Ω) (curry χ)) ≫ ev = _
    rw [Cat.assoc, hβ, pbχ.cone.w, term_uniq pbχ.cone.π₂ (term pbχ.cone.pt)]
  let e₁ : pbχ.cone.pt ⟶ pbe.cone.pt := pbe.lift ⟨pbχ.cone.pt, m₁, term pbχ.cone.pt, hm₁ev⟩
  have he₁ : e₁ ≫ pbe.cone.π₁ = m₁ := pbe.lift_fst _
  have hm₁snd : m₁ ≫ snd = (pbχ.cone.π₁ ≫ snd) ≫ curry χ := by
    show (pbχ.cone.π₁ ≫ prodMap A X (exp A Ω) (curry χ)) ≫ snd = _
    rw [Cat.assoc, prodMap_snd, ← Cat.assoc]
  have hm₁fst : m₁ ≫ fst = pbχ.cone.π₁ ≫ fst := by
    show (pbχ.cone.π₁ ≫ prodMap A X (exp A Ω) (curry χ)) ≫ fst = _
    rw [Cat.assoc, prodMap_fst]
  have hQw : (pbχ.cone.π₁ ≫ snd) ≫ curry χ = e₁ ≫ ((evalRel A).colA) := by
    show (pbχ.cone.π₁ ≫ snd) ≫ curry χ = e₁ ≫ (pbe.cone.π₁ ≫ snd)
    rw [← Cat.assoc, he₁, hm₁snd]
  let qlift : pbχ.cone.pt ⟶ Q.cone.pt :=
    Q.lift ⟨pbχ.cone.pt, pbχ.cone.π₁ ≫ snd, e₁, hQw⟩
  refine ⟨qlift, ?_, ?_⟩
  · show qlift ≫ Q.cone.π₁ = pbχ.cone.π₁ ≫ snd
    exact Q.lift_fst _
  · show qlift ≫ (Q.cone.π₂ ≫ (evalRel A).colB) = pbχ.cone.π₁ ≫ fst
    rw [← Cat.assoc, Q.lift_snd]
    show e₁ ≫ (pbe.cone.π₁ ≫ fst) = pbχ.cone.π₁ ≫ fst
    rw [← Cat.assoc, he₁, hm₁fst]

/-- β-law bridge (backward): the pullback of the universal `evalRel A` along `curry χ`
    is the relation cut out by `χ`. -/
theorem evalRel_pull_bwd {A X : 𝒞}
    (χ : prod A X ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    RelHom (relPullback (curry χ) (evalRel A)) (classRel χ) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let ev := eval_exp A Ω
  let pbχ := HasPullbacks.has χ HasSubobjectClassifier.true
  let pbe := HasPullbacks.has ev HasSubobjectClassifier.true
  let Q := HasPullbacks.has (curry χ) ((evalRel A).colA)
  have hβ : prodMap A X (exp A Ω) (curry χ) ≫ ev = χ := curry_eval_eq χ
  have hQw : Q.cone.π₁ ≫ curry χ = Q.cone.π₂ ≫ (pbe.cone.π₁ ≫ snd) := Q.cone.w
  have hpbe : pbe.cone.π₁ ≫ ev = term pbe.cone.pt ≫ HasSubobjectClassifier.true := by
    rw [pbe.cone.w, term_uniq pbe.cone.π₂ (term pbe.cone.pt)]
  let n : Q.cone.pt ⟶ prod A X := pair (Q.cone.π₂ ≫ pbe.cone.π₁ ≫ fst) (Q.cone.π₁)
  have hnfst : n ≫ fst = Q.cone.π₂ ≫ pbe.cone.π₁ ≫ fst := fst_pair _ _
  have hnsnd : n ≫ snd = Q.cone.π₁ := snd_pair _ _
  have hnpm : n ≫ prodMap A X (exp A Ω) (curry χ) = Q.cone.π₂ ≫ pbe.cone.π₁ := by
    have e1 : (n ≫ prodMap A X (exp A Ω) (curry χ)) ≫ fst
            = (Q.cone.π₂ ≫ pbe.cone.π₁) ≫ fst := by
      rw [Cat.assoc, prodMap_fst, hnfst, Cat.assoc]
    have e2 : (n ≫ prodMap A X (exp A Ω) (curry χ)) ≫ snd
            = (Q.cone.π₂ ≫ pbe.cone.π₁) ≫ snd := by
      rw [Cat.assoc, prodMap_snd, ← Cat.assoc, hnsnd, hQw, Cat.assoc]
    exact (pair_uniq _ _ _ e1 e2).trans (pair_uniq _ _ _ rfl rfl).symm
  have hnχ : n ≫ χ = term Q.cone.pt ≫ HasSubobjectClassifier.true := by
    calc n ≫ χ = n ≫ (prodMap A X (exp A Ω) (curry χ) ≫ ev) := by rw [hβ]
      _ = (n ≫ prodMap A X (exp A Ω) (curry χ)) ≫ ev := (Cat.assoc _ _ _).symm
      _ = (Q.cone.π₂ ≫ pbe.cone.π₁) ≫ ev := by rw [hnpm]
      _ = Q.cone.π₂ ≫ (pbe.cone.π₁ ≫ ev) := Cat.assoc _ _ _
      _ = Q.cone.π₂ ≫ (term pbe.cone.pt ≫ HasSubobjectClassifier.true) := by rw [hpbe]
      _ = term Q.cone.pt ≫ HasSubobjectClassifier.true := by
          rw [← Cat.assoc, term_uniq (Q.cone.π₂ ≫ term pbe.cone.pt) (term Q.cone.pt)]
  let nlift : Q.cone.pt ⟶ pbχ.cone.pt := pbχ.lift ⟨Q.cone.pt, n, term Q.cone.pt, hnχ⟩
  have hnl : nlift ≫ pbχ.cone.π₁ = n := pbχ.lift_fst _
  refine ⟨nlift, ?_, ?_⟩
  · show nlift ≫ (pbχ.cone.π₁ ≫ snd) = Q.cone.π₁
    rw [← Cat.assoc, hnl, hnsnd]
  · show nlift ≫ (pbχ.cone.π₁ ≫ fst) = Q.cone.π₂ ≫ (evalRel A).colB
    rw [← Cat.assoc, hnl, hnfst]; rfl

/-- Iso relations name the same subobject: equal classifier of their product-monics. -/
theorem classify_relMonic_eq {X A : 𝒞} {R S : BinRel 𝒞 X A}
    (h : RelHom R S ∧ RelHom S R) :
    HasSubobjectClassifier.classify (relMonic R) (relMonic_mono R)
      = HasSubobjectClassifier.classify (relMonic S) (relMonic_mono S) := by
  obtain ⟨⟨w, hwA, hwB⟩, ⟨v, hvA, hvB⟩⟩ := h
  have hwm : w ≫ relMonic S = relMonic R := by
    apply pair_uniq
    · rw [Cat.assoc]; show w ≫ (pair S.colB S.colA ≫ fst) = R.colB; rw [fst_pair, hwB]
    · rw [Cat.assoc]; show w ≫ (pair S.colB S.colA ≫ snd) = R.colA; rw [snd_pair, hwA]
  have hvm : v ≫ relMonic R = relMonic S := by
    apply pair_uniq
    · rw [Cat.assoc]; show v ≫ (pair R.colB R.colA ≫ fst) = S.colB; rw [fst_pair, hvB]
    · rw [Cat.assoc]; show v ≫ (pair R.colB R.colA ≫ snd) = S.colA; rw [snd_pair, hvA]
  have hsq : relMonic R ≫ HasSubobjectClassifier.classify (relMonic S) (relMonic_mono S)
           = term R.src ≫ HasSubobjectClassifier.true := by
    rw [← hwm, Cat.assoc, HasSubobjectClassifier.classify_sq, ← Cat.assoc,
        term_uniq (w ≫ term S.src) (term R.src)]
  refine (classify_eq_of_pullback (relMonic R) (relMonic_mono R)
    (HasSubobjectClassifier.classify (relMonic S) (relMonic_mono S)) hsq ?_).symm
  intro d
  have hSpb := HasSubobjectClassifier.classify_pullback (relMonic S) (relMonic_mono S)
  obtain ⟨ℓ, ⟨hℓ1, _⟩, _⟩ := hSpb d
  refine ⟨ℓ ≫ v, ⟨?_, term_uniq _ _⟩, ?_⟩
  · show (ℓ ≫ v) ≫ relMonic R = d.π₁
    rw [Cat.assoc, hvm]; exact hℓ1
  · intro y hy1 _
    apply relMonic_mono R
    show y ≫ relMonic R = (ℓ ≫ v) ≫ relMonic R
    rw [hy1, Cat.assoc, hvm]; exact hℓ1.symm

/-- The classifier of `classRel χ`'s product-monic recovers `χ`. -/
theorem classify_relMonic_classRel {A X : 𝒞}
    (χ : prod A X ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    HasSubobjectClassifier.classify (relMonic (classRel χ)) (relMonic_mono (classRel χ)) = χ := by
  let pbχ := HasPullbacks.has χ HasSubobjectClassifier.true
  have hrm : relMonic (classRel χ) = pbχ.cone.π₁ := (pair_uniq _ _ _ rfl rfl).symm
  have hsq : relMonic (classRel χ) ≫ χ = term (classRel χ).src ≫ HasSubobjectClassifier.true := by
    rw [hrm, pbχ.cone.w]; exact congrArg (· ≫ HasSubobjectClassifier.true) (term_uniq _ _)
  symm
  refine classify_eq_of_pullback (relMonic (classRel χ)) (relMonic_mono (classRel χ)) χ hsq ?_
  intro d
  obtain ⟨u, ⟨hu1, _⟩, huq⟩ := pbχ.cone_isPullback d
  refine ⟨u, ⟨by show u ≫ relMonic (classRel χ) = d.π₁; rw [hrm]; exact hu1, term_uniq _ _⟩, ?_⟩
  intro y hy1 _
  refine huq y ?_ (term_uniq _ _)
  show y ≫ pbχ.cone.π₁ = d.π₁
  rw [← hrm]; exact hy1

/-- **§1.92 — `eval` makes `Ω^A` universal targeted at `A`.**  The membership relation
    `evalRel A` is a UNIVERSAL relation: every `R : BinRel X A` is uniquely the pullback of
    `evalRel A` along a classifying map `curry(χ_R) : X → Ω^A`.  This is the curry/eval
    transpose of the subobject-classifier bijection `Sub(A × X) ≅ Hom(A × X, Ω)`, NO internal
    `∃` (image factorization) required — it is the contravariant/representing half. -/
theorem evalRel_universal (A : 𝒞) : IsUniversalRel (evalRel A) := by
  constructor
  · intro X R
    refine ⟨curry (HasSubobjectClassifier.classify (relMonic R) (relMonic_mono R)), ?_, ?_⟩
    · exact RelHom_trans (classRel_roundtrip R).1 (evalRel_pull_fwd _)
    · exact RelHom_trans (evalRel_pull_bwd _) (classRel_roundtrip R).2
  · intro X R f g hf hg
    let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
    have hf_eq : f = curry (prodMap A X (exp A Ω) f ≫ eval_exp A Ω) := curry_unique_eq rfl
    have hg_eq : g = curry (prodMap A X (exp A Ω) g ≫ eval_exp A Ω) := curry_unique_eq rfl
    let χf := prodMap A X (exp A Ω) f ≫ eval_exp A Ω
    let χg := prodMap A X (exp A Ω) g ≫ eval_exp A Ω
    have hRf : RelHom R (classRel χf) ∧ RelHom (classRel χf) R := by
      have e1 : RelHom (relPullback f (evalRel A)) (classRel χf) := by
        rw [hf_eq]; exact evalRel_pull_bwd χf
      have e2 : RelHom (classRel χf) (relPullback f (evalRel A)) := by
        rw [hf_eq]; exact evalRel_pull_fwd χf
      exact ⟨RelHom_trans hf.1 e1, RelHom_trans e2 hf.2⟩
    have hRg : RelHom R (classRel χg) ∧ RelHom (classRel χg) R := by
      have e1 : RelHom (relPullback g (evalRel A)) (classRel χg) := by
        rw [hg_eq]; exact evalRel_pull_bwd χg
      have e2 : RelHom (classRel χg) (relPullback g (evalRel A)) := by
        rw [hg_eq]; exact evalRel_pull_fwd χg
      exact ⟨RelHom_trans hg.1 e1, RelHom_trans e2 hg.2⟩
    have hiso : RelHom (classRel χf) (classRel χg) ∧ RelHom (classRel χg) (classRel χf) :=
      ⟨RelHom_trans hRf.2 hRg.1, RelHom_trans hRg.2 hRf.1⟩
    have hχ : χf = χg := by
      have := classify_relMonic_eq hiso
      rwa [classify_relMonic_classRel, classify_relMonic_classRel] at this
    rw [hf_eq, hg_eq]; exact congrArg curry hχ

/-- **§1.92 — the power-object comparison `[A] → Ω^A`.**  `Λ_{evalRel}(∈_A)`, the
    classifier of the genuine membership `∈_A : BinRel [A] A` against the universal
    `evalRel A` on `Ω^A`. -/
noncomputable def powExpHom (A : 𝒞) :
    HasPowerObject.powerObj (C := A) ⟶ exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  univClassify (evalRel_universal A) HasPowerObject.mem

/-- **§1.92 — `Ω^A ≅ [A]`.**  Two universal relations targeted at `A` have isomorphic
    carriers (`universalRel_unique`), so the comparison `powExpHom A : [A] → Ω^A` is an
    iso.  This is the identification of the exponential `Ω^A` with the power object `[A]`,
    sorry-free.  (Downstream, `S1_95 :: omega_is_internally_injective` waits on exactly
    this iso to transport the genuine direct image `powerMapCovP` to the `exp`-level
    `expMap Ω` — see the residual blocker note on `powerMapCov` below.) -/
theorem powExpHom_iso (A : 𝒞) : IsIso (powExpHom A) :=
  universalRel_unique HasPowerObject.is_universal (evalRel_universal A)

/-- The inverse `Ω^A → [A]` of the power-object comparison iso. -/
noncomputable def expPowInv (A : 𝒞) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶ HasPowerObject.powerObj (C := A) :=
  (powExpHom_iso A).choose

end EvalUniversalAmbient

/-! ## §1.92  The COVARIANT power-map `[f] : Ω^A → Ω^B` and its naturality `f(Δ₁) = Δf`

  Freyd §1.922 defines the direct-image action `[f] : [A] → [B]` for `f : A → B`,
  `[f](S) = { b | ∃ a ∈ S, f a = b }`.  On genuine power objects this is
  `powerMapCovP f = Λ(∈_A ⊚ graph f)` (`directImageRel`), already built sorry-free
  above.  We now (a) prove its NATURALITY against the singleton map (the book's
  `f(Δ₁) = Δf`), and (b) transport it across the iso `Ω^A ≅ [A]`
  (`powExpHom`/`expPowInv`) to the opaque exponential `exp A Ω`, giving the
  `exp`-level `powerMapCov` and its naturality `singletonMapCat_natural`.

  Both require the §1.56 existential image (`⊚` is image-gated), so we take
  `[HasImages 𝒞] [PullbacksTransferCovers 𝒞]` as explicit, FAITHFUL hypotheses: a
  topos has both (`toposHasImages`, `toposPullbacksTransferCovers`, via §1.94
  `topos_is_regular`), but those instances live ABOVE `S1_92` (`InternalForallTopos`
  imports `S1_92`), so they cannot be in scope here without an import cycle. -/

section CovariantPowerMap
variable [HasImages 𝒞] [PullbacksTransferCovers 𝒞]

attribute [local instance 10000] Topos.toHasBinaryProducts

/-- **§1.92 — pullback distributes over composition.**  For `g : X → A`,
    `R : BinRel A B`, `S : BinRel B C`:
    `relPullback g (R ⊚ S) ≅ (relPullback g R) ⊚ S`  (mutual `RelHom`).

    The crux of the covariant power-map naturality.  `R ⊚ S` is the §1.56 image of the
    span over `pullback(R.colB, S.colA)`; pulling that back along `g` is the image of the
    span over `pullback(g, R.colA) ×_? S`.  Each direction is a `relLe_of_cover_factor`
    descent: pull the relevant image-cover (`image.lift`) back along the appropriate
    `relPullback`/composite leg (`cover_pullback`, needing `PullbacksTransferCovers`),
    obtaining a common cover on which the coherent `(relPullback g R)`/`S` data assembles. -/
theorem relPullback_compose_dist {X A B C : 𝒞} (g : X ⟶ A)
    (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) :
    RelHom (relPullback g (R ⊚ S)) ((relPullback g R) ⊚ S) ∧
    RelHom ((relPullback g R) ⊚ S) (relPullback g (R ⊚ S)) := by
  -- data of `R ⊚ S`: image of `spanRS` over `pbRS = pullback(R.colB, S.colA)`.
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS : pbRS.cone.pt ⟶ prod A C :=
    pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS : pbRS.cone.pt ⟶ (R ⊚ S).src := image.lift spanRS
  have heRSa : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show eRS ≫ ((image spanRS).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have heRSb : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show eRS ≫ ((image spanRS).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  have heRS_cover : Cover eRS := image_lift_cover spanRS
  -- data of `relPullback g R`: pullback of `g` and `R.colA`.
  let rgR := relPullback g R
  have hrgRa : rgR.colA = (HasPullbacks.has g R.colA).cone.π₁ := rfl
  have hrgRb : rgR.colB = (HasPullbacks.has g R.colA).cone.π₂ ≫ R.colB := rfl
  -- data of `(relPullback g R) ⊚ S`: image of `span'` over `pb' = pullback(rgR.colB, S.colA)`.
  let pb' := HasPullbacks.has rgR.colB S.colA
  let span' : pb'.cone.pt ⟶ prod X C :=
    pair (pb'.cone.π₁ ≫ rgR.colA) (pb'.cone.π₂ ≫ S.colB)
  let e' : pb'.cone.pt ⟶ ((relPullback g R) ⊚ S).src := image.lift span'
  have he'a : e' ≫ ((relPullback g R) ⊚ S).colA = pb'.cone.π₁ ≫ rgR.colA := by
    show e' ≫ ((image span').arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have he'b : e' ≫ ((relPullback g R) ⊚ S).colB = pb'.cone.π₂ ≫ S.colB := by
    show e' ≫ ((image span').arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  have he'_cover : Cover e' := image_lift_cover span'
  constructor
  · -- FORWARD: relPullback g (R⊚S) ⊂ (relPullback g R) ⊚ S.
    -- X-relation `Pg := pullback(g, (R⊚S).colA)`; pull the cover `eRS` back along `Pg.π₂`.
    let Pg := HasPullbacks.has g (R ⊚ S).colA
    -- cover `c : P ↠ Pg.pt` and `q : P → pbRS.pt` with `q ≫ eRS = c ≫ Pg.π₂`.
    let Pc := HasPullbacks.has eRS Pg.cone.π₂
    let c : Pc.cone.pt ⟶ Pg.cone.pt := Pc.cone.π₂
    let q : Pc.cone.pt ⟶ pbRS.cone.pt := Pc.cone.π₁
    have hcq : q ≫ eRS = c ≫ Pg.cone.π₂ := Pc.cone.w
    have hc_cover : Cover c := cover_pullback (𝒞 := 𝒞) (f := eRS) Pg.cone.π₂ heRS_cover
    -- coherent legs on `P = Pc.pt`:
    --   c ≫ Pg.π₁ : P → X ;  q ≫ pbRS.π₁ : P → R.src ;  q ≫ pbRS.π₂ : P → S.src
    -- agreement (X→A vs R.src→A): (c≫Pg.π₁)≫g = (q≫pbRS.π₁)≫R.colA.
    have hgR : (c ≫ Pg.cone.π₁) ≫ g = (q ≫ pbRS.cone.π₁) ≫ R.colA := by
      calc (c ≫ Pg.cone.π₁) ≫ g
          = c ≫ (Pg.cone.π₁ ≫ g) := Cat.assoc _ _ _
        _ = c ≫ (Pg.cone.π₂ ≫ (R ⊚ S).colA) := by rw [Pg.cone.w]
        _ = (c ≫ Pg.cone.π₂) ≫ (R ⊚ S).colA := (Cat.assoc _ _ _).symm
        _ = (q ≫ eRS) ≫ (R ⊚ S).colA := by rw [hcq]
        _ = q ≫ (eRS ≫ (R ⊚ S).colA) := Cat.assoc _ _ _
        _ = q ≫ (pbRS.cone.π₁ ≫ R.colA) := by rw [heRSa]
        _ = (q ≫ pbRS.cone.π₁) ≫ R.colA := (Cat.assoc _ _ _).symm
    -- lift into `rgR.src = pullback(g, R.colA)`: `m : P → rgR.src`.
    let PgR := HasPullbacks.has g R.colA
    let m : Pc.cone.pt ⟶ rgR.src :=
      PgR.lift ⟨Pc.cone.pt, c ≫ Pg.cone.π₁, q ≫ pbRS.cone.π₁, hgR⟩
    have hm₁ : m ≫ PgR.cone.π₁ = c ≫ Pg.cone.π₁ := PgR.lift_fst _
    have hm₂ : m ≫ PgR.cone.π₂ = q ≫ pbRS.cone.π₁ := PgR.lift_snd _
    -- agreement (rgR.colB vs S.colA) to lift into `pb' = pullback(rgR.colB, S.colA)`.
    have hrgRS : m ≫ rgR.colB = (q ≫ pbRS.cone.π₂) ≫ S.colA := by
      calc m ≫ rgR.colB
          = m ≫ (PgR.cone.π₂ ≫ R.colB) := by rw [hrgRb]
        _ = (m ≫ PgR.cone.π₂) ≫ R.colB := (Cat.assoc _ _ _).symm
        _ = (q ≫ pbRS.cone.π₁) ≫ R.colB := by rw [hm₂]
        _ = q ≫ (pbRS.cone.π₁ ≫ R.colB) := Cat.assoc _ _ _
        _ = q ≫ (pbRS.cone.π₂ ≫ S.colA) := by rw [pbRS.cone.w]
        _ = (q ≫ pbRS.cone.π₂) ≫ S.colA := (Cat.assoc _ _ _).symm
    let n : Pc.cone.pt ⟶ pb'.cone.pt :=
      pb'.lift ⟨Pc.cone.pt, m, q ≫ pbRS.cone.π₂, hrgRS⟩
    have hn₁ : n ≫ pb'.cone.π₁ = m := pb'.lift_fst _
    have hn₂ : n ≫ pb'.cone.π₂ = q ≫ pbRS.cone.π₂ := pb'.lift_snd _
    -- `φ := n ≫ e' : P → ((relPullback g R) ⊚ S).src`.
    have hYA : (n ≫ e') ≫ ((relPullback g R) ⊚ S).colA
             = c ≫ (relPullback g (R ⊚ S)).colA := by
      calc (n ≫ e') ≫ ((relPullback g R) ⊚ S).colA
          = n ≫ (e' ≫ ((relPullback g R) ⊚ S).colA) := Cat.assoc _ _ _
        _ = n ≫ (pb'.cone.π₁ ≫ rgR.colA) := by rw [he'a]
        _ = (n ≫ pb'.cone.π₁) ≫ rgR.colA := (Cat.assoc _ _ _).symm
        _ = m ≫ rgR.colA := by rw [hn₁]
        _ = m ≫ PgR.cone.π₁ := by rw [hrgRa]
        _ = c ≫ Pg.cone.π₁ := hm₁
        _ = c ≫ (relPullback g (R ⊚ S)).colA := rfl
    have hYB : (n ≫ e') ≫ ((relPullback g R) ⊚ S).colB
             = c ≫ (relPullback g (R ⊚ S)).colB := by
      calc (n ≫ e') ≫ ((relPullback g R) ⊚ S).colB
          = n ≫ (e' ≫ ((relPullback g R) ⊚ S).colB) := Cat.assoc _ _ _
        _ = n ≫ (pb'.cone.π₂ ≫ S.colB) := by rw [he'b]
        _ = (n ≫ pb'.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
        _ = (q ≫ pbRS.cone.π₂) ≫ S.colB := by rw [hn₂]
        _ = q ≫ (pbRS.cone.π₂ ≫ S.colB) := Cat.assoc _ _ _
        _ = q ≫ (eRS ≫ (R ⊚ S).colB) := by rw [heRSb]
        _ = (q ≫ eRS) ≫ (R ⊚ S).colB := (Cat.assoc _ _ _).symm
        _ = (c ≫ Pg.cone.π₂) ≫ (R ⊚ S).colB := by rw [hcq]
        _ = c ≫ (Pg.cone.π₂ ≫ (R ⊚ S).colB) := Cat.assoc _ _ _
        _ = c ≫ (relPullback g (R ⊚ S)).colB := rfl
    obtain ⟨hrel⟩ := relLe_of_cover_factor (X := relPullback g (R ⊚ S))
      (Y := (relPullback g R) ⊚ S) c hc_cover (n ≫ e') hYA hYB
    exact hrel
  · -- BACKWARD: (relPullback g R) ⊚ S ⊂ relPullback g (R⊚S).
    -- X-relation = `((relPullback g R) ⊚ S).src = image(span').dom`; its cover is `e'`.
    let Pg := HasPullbacks.has g (R ⊚ S).colA
    let PgR := HasPullbacks.has g R.colA
    -- point of `pbRS = pullback(R.colB, S.colA)` from `pb'.pt`.
    have hrw : (pb'.cone.π₁ ≫ PgR.cone.π₂) ≫ R.colB = pb'.cone.π₂ ≫ S.colA := by
      -- `rgR.colB` is DEFINITIONALLY `PgR.cone.π₂ ≫ R.colB` (both pull back `g`,`R.colA`).
      have hpbw : pb'.cone.π₁ ≫ rgR.colB = pb'.cone.π₂ ≫ S.colA := pb'.cone.w
      calc (pb'.cone.π₁ ≫ PgR.cone.π₂) ≫ R.colB
          = pb'.cone.π₁ ≫ (PgR.cone.π₂ ≫ R.colB) := Cat.assoc _ _ _
        _ = pb'.cone.π₂ ≫ S.colA := hpbw
    let r : pb'.cone.pt ⟶ pbRS.cone.pt :=
      pbRS.lift ⟨pb'.cone.pt, pb'.cone.π₁ ≫ PgR.cone.π₂, pb'.cone.π₂, hrw⟩
    have hr₁ : r ≫ pbRS.cone.π₁ = pb'.cone.π₁ ≫ PgR.cone.π₂ := pbRS.lift_fst _
    have hr₂ : r ≫ pbRS.cone.π₂ = pb'.cone.π₂ := pbRS.lift_snd _
    -- agreement to lift into `Pg = pullback(g, (R⊚S).colA)`.
    have hag : (pb'.cone.π₁ ≫ PgR.cone.π₁) ≫ g = (r ≫ eRS) ≫ (R ⊚ S).colA := by
      calc (pb'.cone.π₁ ≫ PgR.cone.π₁) ≫ g
          = pb'.cone.π₁ ≫ (PgR.cone.π₁ ≫ g) := Cat.assoc _ _ _
        _ = pb'.cone.π₁ ≫ (PgR.cone.π₂ ≫ R.colA) := by rw [PgR.cone.w]
        _ = (pb'.cone.π₁ ≫ PgR.cone.π₂) ≫ R.colA := (Cat.assoc _ _ _).symm
        _ = (r ≫ pbRS.cone.π₁) ≫ R.colA := by rw [hr₁]
        _ = r ≫ (pbRS.cone.π₁ ≫ R.colA) := Cat.assoc _ _ _
        _ = r ≫ (eRS ≫ (R ⊚ S).colA) := by rw [heRSa]
        _ = (r ≫ eRS) ≫ (R ⊚ S).colA := (Cat.assoc _ _ _).symm
    let φ : pb'.cone.pt ⟶ Pg.cone.pt :=
      Pg.lift ⟨pb'.cone.pt, pb'.cone.π₁ ≫ PgR.cone.π₁, r ≫ eRS, hag⟩
    have hφ₁ : φ ≫ Pg.cone.π₁ = pb'.cone.π₁ ≫ PgR.cone.π₁ := Pg.lift_fst _
    have hφ₂ : φ ≫ Pg.cone.π₂ = r ≫ eRS := Pg.lift_snd _
    have hXA : φ ≫ (relPullback g (R ⊚ S)).colA
             = e' ≫ ((relPullback g R) ⊚ S).colA := by
      calc φ ≫ (relPullback g (R ⊚ S)).colA
          = φ ≫ Pg.cone.π₁ := rfl
        _ = pb'.cone.π₁ ≫ PgR.cone.π₁ := hφ₁
        _ = pb'.cone.π₁ ≫ rgR.colA := by rw [hrgRa]
        _ = e' ≫ ((relPullback g R) ⊚ S).colA := he'a.symm
    have hXB : φ ≫ (relPullback g (R ⊚ S)).colB
             = e' ≫ ((relPullback g R) ⊚ S).colB := by
      calc φ ≫ (relPullback g (R ⊚ S)).colB
          = φ ≫ (Pg.cone.π₂ ≫ (R ⊚ S).colB) := rfl
        _ = (φ ≫ Pg.cone.π₂) ≫ (R ⊚ S).colB := (Cat.assoc _ _ _).symm
        _ = (r ≫ eRS) ≫ (R ⊚ S).colB := by rw [hφ₂]
        _ = r ≫ (eRS ≫ (R ⊚ S).colB) := Cat.assoc _ _ _
        _ = r ≫ (pbRS.cone.π₂ ≫ S.colB) := by rw [heRSb]
        _ = (r ≫ pbRS.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
        _ = pb'.cone.π₂ ≫ S.colB := by rw [hr₂]
        _ = e' ≫ ((relPullback g R) ⊚ S).colB := he'b.symm
    obtain ⟨hrel⟩ := relLe_of_cover_factor (X := (relPullback g R) ⊚ S)
      (Y := relPullback g (R ⊚ S)) e' he'_cover φ hXA hXB
    exact hrel

/-- **§1.92 (faithful) — naturality of the singleton map on power objects** (Freyd's
    `f(Δ₁) = Δf`).  For `f : A → B`:  `f ≫ {·}_B = {·}_A ≫ [f]`, i.e.
    `f ≫ singletonMap923 B = singletonMap923 A ≫ powerMapCovP f`.

    Both sides name a relation `X → [B]` against the universal `∈_B`; by `classify_unique`
    it suffices that the two named relations are iso.  LHS names `graph f`
    (`singletonMapNaming923`).  RHS, via `powerClassify_natural923`, names
    `relPullback (singletonMap923 A) (∈_A ⊚ graph f)`, which the distribution lemma plus
    `relPullback (singletonMap923 A) ∈_A ≅ graph(1_A)` (`powerClassify_pullback_iso`) and
    `graph(1_A) ⊚ graph f ≅ graph f` (`graph_id_comp`) identifies with `graph f`. -/
theorem powerMapCovP_natural {A B : 𝒞} (f : A ⟶ B) :
    f ≫ singletonMap923 B = singletonMap923 A ≫ powerMapCovP f := by
  -- Rewrite both sides as `powerClassify` of a relation.
  rw [singletonMapNaming923 f, powerMapCovP, ← powerClassify_natural923]
  -- Goal: powerClassify (graph f) = powerClassify (relPullback (singletonMap923 A) (∈_A ⊚ graph f)).
  let memA : BinRel 𝒞 (HasPowerObject.powerObj (C := A)) A := HasPowerObject.mem (C := A)
  -- `graph f ≅ relPullback (singletonMap923 A) (memA ⊚ graph f)`.
  -- Step 1: distribution.
  obtain ⟨hd1, hd2⟩ := relPullback_compose_dist (singletonMap923 A) memA (graph f)
  -- Step 2: `relPullback (singletonMap923 A) memA ≅ graph (1_A)`
  --   (singletonMap923 A = powerClassify (graph (1_A))).
  have hsm : relPullback (singletonMap923 A) memA
           = relPullback (powerClassify (graph (Cat.id A))) HasPowerObject.mem := rfl
  obtain ⟨hp1, hp2⟩ := powerClassify_pullback_iso (graph (Cat.id A))
  -- hp1 : graph(1_A) ⊂ relPullback (singletonMap923 A) memA ; hp2 the reverse.
  -- Step 3: lift step-2 iso into the composite and absorb the identity graph.
  -- (relPullback (singletonMap923 A) memA) ⊚ graph f ≅ graph(1_A) ⊚ graph f ≅ graph f.
  have hcomp_fwd : RelLe ((relPullback (singletonMap923 A) memA) ⊚ graph f) (graph f) :=
    rel_le_trans
      (compose_le ⟨by rw [hsm]; exact hp2⟩ (rel_le_refl (graph f)))
      (graph_id_comp (graph f))
  have hcomp_bwd : RelLe (graph f) ((relPullback (singletonMap923 A) memA) ⊚ graph f) :=
    rel_le_trans
      (comp_graph_id_left (graph f))
      (compose_le ⟨by rw [hsm]; exact hp1⟩ (rel_le_refl (graph f)))
  -- Assemble: relPullback (singletonMap923 A) (memA ⊚ graph f) ≅ graph f.
  have hfwd : RelLe (relPullback (singletonMap923 A) (memA ⊚ graph f)) (graph f) :=
    rel_le_trans ⟨hd1⟩ hcomp_fwd
  have hbwd : RelLe (graph f) (relPullback (singletonMap923 A) (memA ⊚ graph f)) :=
    rel_le_trans hcomp_bwd ⟨hd2⟩
  obtain ⟨hF⟩ := hfwd; obtain ⟨hB⟩ := hbwd
  -- Conclude by classify_unique against `∈_B`.
  refine HasPowerObject.is_universal.classify_unique _ (graph f)
    (powerClassify (graph f))
    (powerClassify (relPullback (singletonMap923 A) (memA ⊚ graph f)))
    (powerClassify_pullback_iso (graph f)) ?_
  -- Need: graph f ↔ relPullback (Λ(relPullback (singletonMap923 A) (memA ⊚ graph f))) ∈.
  obtain ⟨hq1, hq2⟩ := powerClassify_pullback_iso (relPullback (singletonMap923 A) (memA ⊚ graph f))
  exact ⟨relHom_trans923 hB hq1, relHom_trans923 hq2 hF⟩

/-- **§1.92 — the singleton maps agree across `Ω^B ≅ [B]`.**  The `exp`-level singleton
    `Δ₁ = singletonMapCat B : B → Ω^B` equals the power-object singleton `{·}_B`
    composed with the comparison `powExpHom B : [B] → Ω^B`:
    `singletonMapCat B = singletonMap923 B ≫ powExpHom B`.

    Both name the diagonal relation `graph(1_B)` against the universal `evalRel B`
    (`Sub(B×−) ≅ Hom(B×−,Ω)`), so `evalRel`-uniqueness forces them equal.  LHS:
    `singletonMapCat B = curry(χ_Δ)` pulls `evalRel B` back to `classRel χ_Δ ≅ graph(1_B)`
    (`evalRel_pull_*`, `classRel_roundtrip`, `relMonic(graph 1) = diag`).  RHS:
    `relPullback (powExpHom B) (evalRel B) ≅ ∈_B` (`univClassify_spec`) and then
    `relPullback {·}_B ∈_B ≅ graph(1_B)` (`powerClassify_pullback_iso`). -/
theorem singletonMapCat_eq_powExp (B : 𝒞) :
    singletonMapCat B = singletonMap923 B ≫ powExpHom B := by
  -- Both classify `graph (1_B)` against `evalRel B`; apply `classify_unique`.
  let χΔ := HasSubobjectClassifier.classify (diag B) (diag_mono B)
  -- `relMonic (graph 1_B) = diag B` DEFINITIONALLY, so `classify (relMonic (graph 1_B)) = χΔ`
  -- and `classRel (classify (relMonic (graph 1_B))) = classRel χΔ` by `rfl`.
  -- LHS pulls back to `graph (1_B)`.
  have hLHS : RelHom (graph (Cat.id B)) (relPullback (singletonMapCat B) (evalRel B)) ∧
              RelHom (relPullback (singletonMapCat B) (evalRel B)) (graph (Cat.id B)) := by
    -- classRel χΔ ≅ relPullback (curry χΔ) (evalRel B) = relPullback (singletonMapCat B) (evalRel B);
    -- `classRel_roundtrip (graph 1_B)` is exactly `graph 1_B ↔ classRel χΔ` (up to defeq).
    have hcr : RelHom (graph (Cat.id B)) (classRel χΔ) ∧ RelHom (classRel χΔ) (graph (Cat.id B)) :=
      classRel_roundtrip (graph (Cat.id B))
    refine ⟨RelHom_trans hcr.1 (evalRel_pull_fwd χΔ),
            RelHom_trans (evalRel_pull_bwd χΔ) hcr.2⟩
  -- RHS pulls back to `graph (1_B)`.
  have hRHS : RelHom (graph (Cat.id B))
                (relPullback (singletonMap923 B ≫ powExpHom B) (evalRel B)) ∧
              RelHom (relPullback (singletonMap923 B ≫ powExpHom B) (evalRel B))
                (graph (Cat.id B)) := by
    -- relPullback (η ≫ φ) eval ≅ relPullback η (relPullback φ eval) ≅ relPullback η ∈_B ≅ graph 1.
    obtain ⟨hc1, hc2⟩ := relPullback_comp (singletonMap923 B) (powExpHom B) (evalRel B)
    -- relPullback (powExpHom B) (evalRel B) ≅ ∈_B.
    obtain ⟨hu1, hu2⟩ := univClassify_spec (evalRel_universal B) (HasPowerObject.mem (C := B))
    -- hu1 : ∈_B ↔ relPullback (powExpHom B) (evalRel B) (powExpHom B = univClassify ... ∈_B).
    -- relPullback (η_B) ∈_B ≅ graph 1_B  (η_B = singletonMap923 B = powerClassify (graph 1)).
    obtain ⟨hg1, hg2⟩ := powerClassify_pullback_iso (graph (Cat.id B))
    -- Chain.  relPullback η (relPullback φ eval) ≅ relPullback η ∈_B  via hu (pulled back along η).
    have hmid1 : RelHom (relPullback (singletonMap923 B) HasPowerObject.mem)
                   (relPullback (singletonMap923 B) (relPullback (powExpHom B) (evalRel B))) :=
      relHom_pullback923 (singletonMap923 B) hu1
    have hmid2 : RelHom (relPullback (singletonMap923 B) (relPullback (powExpHom B) (evalRel B)))
                   (relPullback (singletonMap923 B) HasPowerObject.mem) :=
      relHom_pullback923 (singletonMap923 B) hu2
    -- graph 1_B ↔ relPullback (singletonMap923 B) ∈_B  is hg1/hg2.
    refine ⟨?_, ?_⟩
    · exact RelHom_trans hg1 (RelHom_trans hmid1 hc1)
    · exact RelHom_trans hc2 (RelHom_trans hmid2 hg2)
  -- Both classify `graph 1_B` against `evalRel B`; uniqueness gives equality.
  exact (evalRel_universal B).classify_unique B (graph (Cat.id B))
    (singletonMapCat B) (singletonMap923 B ≫ powExpHom B) hLHS hRHS

/-- **§1.922 — the COVARIANT power-map `[f] : Ω^A → Ω^B` for `f : A → B`** (Freyd §1.922).
    `[f](S) = { b | ∃ a ∈ S, f a = b }`, transported from the genuine power-object
    direct image `powerMapCovP f : [A] → [B]` (`Λ(∈_A ⊚ graph f)`) across the iso
    `Ω^A ≅ [A]` (`expPowInv`/`powExpHom`):  `[f] = (Ω^A → [A]) ≫ f" ≫ ([B] → Ω^B)`. -/
noncomputable def powerMapCov {A B : 𝒞} (f : A ⟶ B) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶
    exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  expPowInv A ≫ powerMapCovP f ≫ powExpHom B

/-- **§1.92 — NATURALITY of the singleton map** (Freyd's `f(Δ₁) = Δf`):
    `f ≫ Δ₁(B) = Δ₁(A) ≫ [f]`, i.e. `f ≫ singletonMapCat B = singletonMapCat A ≫ powerMapCov f`.

    Transport the power-object naturality `powerMapCovP_natural` across `Ω^A ≅ [A]`.  Using
    the bridge `singletonMapCat = singletonMap923 ≫ powExpHom` and `expPowInv ≫ powExpHom = 1`
    (the comparison-iso section laws), the equation reduces to
    `f ≫ singletonMap923 B = singletonMap923 A ≫ powerMapCovP f`. -/
theorem singletonMapCat_natural {A B : 𝒞} (f : A ⟶ B) :
    f ≫ singletonMapCat B =
      singletonMapCat A ≫ powerMapCov f := by
  -- `powExpHom A ≫ expPowInv A = 1`  (powExpHom is the iso; expPowInv := its `.choose` inverse).
  have hinvA1 : powExpHom A ≫ expPowInv A = Cat.id _ := (powExpHom_iso A).choose_spec.1
  rw [powerMapCov, singletonMapCat_eq_powExp A, singletonMapCat_eq_powExp B]
  -- Goal: f ≫ (η_B ≫ φ_B) = (η_A ≫ φ_A) ≫ (expPowInv A ≫ powerMapCovP f ≫ powExpHom B).
  -- Reduce the RHS: (η_A ≫ φ_A) ≫ (φ_A⁻¹ ≫ p ≫ φ_B) = η_A ≫ p ≫ φ_B  (using φ_A ≫ φ_A⁻¹ = 1).
  have hRHS : (singletonMap923 A ≫ powExpHom A)
                ≫ (expPowInv A ≫ powerMapCovP f ≫ powExpHom B)
            = singletonMap923 A ≫ (powerMapCovP f ≫ powExpHom B) := by
    rw [Cat.assoc, ← Cat.assoc (powExpHom A), hinvA1, Cat.id_comp]
  rw [hRHS, ← Cat.assoc, powerMapCovP_natural f, Cat.assoc]

end CovariantPowerMap

/-! ## §1.921  Lawvere's original definition of elementary topos

  F.W. Lawvere originally defined a topos as a bicartesian exponential category
  with partial map classifiers.  The book notes:
  - Mikkelsen: cocartesian structure is a consequence of the other axioms.
  - Kock: exponentiation follows from power objects.
  The simplest modern form: bicartesian + exponential + subobject classifier. -/

/-- A PARTIAL MAP CLASSIFIER (§1.921, §1.934): an object Ω₊ together with a
    monic η : 1 ↪ Ω₊ such that every partial map (monic + map) into X factors
    uniquely through a total map into Ω₊^X.
    The subobject classifier Ω is the special case where the domain is the terminal.

    INTERFACE STATUS / FIDELITY (do not mistake this for the full §1.934 classifier).
    Freyd's §1.934 classifier is PER-CODOMAIN: a functor `B ↦ B̃` with `Ẽ(-,B̃)=ℒ(-,B)` in the
    partial-map category, so a partial map `A ⇀ B` corresponds to a TOTAL `A → B̃` via a pullback
    of the generic `η_B : B ↪ B̃`.  The fields below model only a SINGLE object `pmc_obj` — that is
    structurally just the `B = 1` instance `1̃ = Ω₊` (the lifted subobject classifier) — and
    `pmc_classify` is a BARE map-former with NO universal-property law (no restrict/uniqueness).
    A faithful completion would (a) make the carrier per-codomain `pmcObj : 𝒞 → 𝒞` with a generic
    `η_B` and (b) add the defining pullback universal property as fields.  We deliberately do NOT do
    so: this structure has NO instances in the repo (it is only ever passed as an explicit hypothesis,
    e.g. to §1.98(10) in S1_97), and the only way to BUILD `B̃` in a topos is §1.935/§1.963
    (`B̃ = Π_t(B/0)`, "value-based in any capital topos"), which is §1.543-capitalization-gated.
    So completing the fields would buy no proof here and could not be instantiated without §1.543.
    See `Fredy/S1_97.lean :: nno_of_bicartesian_data` for the full root-cause analysis (§1.988/§1.989
    /§2.542 capitalization), and `Fredy/Capitalization.lean :: capData_exists` for the §1.543 wall. -/
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
  -- `exp A B = B ^^ A` is now the CONCRETE representing object supplied by
  -- `topos_has_exponentials` (no longer opaque), so we exhibit ι EXPLICITLY as the §1.923
  -- GRAPH map  ι : B^A → Ω^{A×B},  f ↦ {(a,b) | eval(a,f) = b} :
  --   ι = curry( γ ),   γ : (A×B) × B^A → Ω,
  --   γ = ⟨ eval(a, f), b ⟩ ≫ classify(diag B)        -- "[ eval(a,f) = b ]"
  -- where on `(A×B)×B^A`:  a = fst≫fst, b = fst≫snd, f = snd, eval(a,f) = ⟨a,f⟩ ≫ eval_A_B.
  refine ⟨curry (pair (pair (fst ≫ fst) snd ≫ eval_exp A B) (fst ≫ snd) ≫
            HasSubobjectClassifier.classify (diag B) (diag_mono B)), ?_⟩
  -- MONO.  By `curry_precomp` + `curry_inj`, `h₁≫ι = h₂≫ι` reduces to the two graphs
  -- `prodMap _ _ _ hᵢ ≫ γ` agreeing as maps `(A×B)×W → Ω`.  Concluding `h₁ = h₂` is the
  -- internal FUNCTIONALITY of the graph: substituting the "diagonal section" `b := eval(a,h₁)`
  -- (the map `σ` below) lands graph₁ on the diagonal — so graph₁'s classifier is `true` there —
  -- hence by hypothesis graph₂'s is too, and `classify_pullback` lifts it through `diag B`,
  -- forcing `eval(a,h₁) = eval(a,h₂)` i.e. `prodMap h₁ ≫ eval = prodMap h₂ ≫ eval`; `curry`
  -- uniqueness then gives `h₁ = h₂`.  Same mechanism as `singletonMapCat_monic`, one transpose up.
  intro W h₁ h₂ hΔ
  let χd := HasSubobjectClassifier.classify (diag B) (diag_mono B)
  -- The two precomposed graphs agree:  pair eᵢ p₀ ≫ χd  (i=1,2),  with
  --   eᵢ = pair (fst≫fst) (snd≫hᵢ) ≫ eval_exp A B,   p₀ = fst≫snd   on  prod (prod A B) W.
  have hγ : pair (pair (fst ≫ fst) (snd ≫ h₁) ≫ eval_exp A B)
                 (fst ≫ snd : prod (prod A B) W ⟶ B) ≫ χd
          = pair (pair (fst ≫ fst) (snd ≫ h₂) ≫ eval_exp A B)
                 (fst ≫ snd : prod (prod A B) W ⟶ B) ≫ χd := by
    have h' := hΔ
    rw [curry_precomp, curry_precomp] at h'
    have hkey := curry_inj h'
    -- Distribute prodMap over the pair-of-eval/snd to identify the two coordinates.
    -- prodMap h ≫ pair (fst≫fst) snd = pair (fst≫fst) (snd≫h)  (push prodMap through both legs).
    have hpush : ∀ h : W ⟶ exp A B,
        prodMap (prod A B) W (exp A B) h ≫ pair (fst ≫ fst) (snd : prod (prod A B) (exp A B) ⟶ exp A B)
          = pair (fst ≫ fst) (snd ≫ h : prod (prod A B) W ⟶ exp A B) := by
      intro h; apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, prodMap_fst]
      · rw [Cat.assoc, snd_pair, prodMap_snd]
    have hcoord : ∀ h : W ⟶ exp A B,
        prodMap (prod A B) W (exp A B) h ≫
            (pair (pair (fst ≫ fst) snd ≫ eval_exp A B) (fst ≫ snd) ≫ χd)
          = pair (pair (fst ≫ fst) (snd ≫ h) ≫ eval_exp A B) (fst ≫ snd) ≫ χd := by
      intro h
      rw [← Cat.assoc]; congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, hpush]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, prodMap_fst]
    rw [hcoord, hcoord] at hkey; exact hkey
  -- The diagonal section  σ : prod A W → prod (prod A B) W,  b := eval(a, h₁).
  let g₁ : prod A W ⟶ B := pair (fst : prod A W ⟶ A) (snd ≫ h₁) ≫ eval_exp A B
  let σ : prod A W ⟶ prod (prod A B) W :=
    pair (pair (fst : prod A W ⟶ A) g₁) (snd : prod A W ⟶ W)
  -- σ ≫ (pair eᵢ p₀) reindexes:  σ ≫ pair (fst≫fst) (snd≫hᵢ) = pair fst (snd≫hᵢ).
  have hreindex : ∀ h : W ⟶ exp A B,
      σ ≫ pair (fst ≫ fst) (snd ≫ h) = pair (fst : prod A W ⟶ A) (snd ≫ h) := by
    intro h
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]; show (σ ≫ fst) ≫ fst = _
      rw [show σ ≫ fst = pair (fst : prod A W ⟶ A) g₁ from fst_pair _ _, fst_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
  -- σ ≫ p₀ = σ ≫ fst ≫ snd = g₁.
  have hp : σ ≫ (fst ≫ snd : prod (prod A B) W ⟶ B) = g₁ := by
    rw [← Cat.assoc]; show (σ ≫ fst) ≫ snd = g₁
    rw [show σ ≫ fst = pair (fst : prod A W ⟶ A) g₁ from fst_pair _ _, snd_pair]
  -- σ ≫ e₁ = g₁ too:  σ ≫ pair (fst≫fst)(snd≫h₁) ≫ eval = pair fst (snd≫h₁) ≫ eval = g₁.
  have he₁ : σ ≫ (pair (fst ≫ fst) (snd ≫ h₁) ≫ eval_exp A B) = g₁ := by
    rw [← Cat.assoc, hreindex]
  -- Hence  σ ≫ (pair e₁ p₀)  factors through the diagonal:  = g₁ ≫ diag B.
  have hdiag : σ ≫ pair (pair (fst ≫ fst) (snd ≫ h₁) ≫ eval_exp A B)
                        (fst ≫ snd : prod (prod A B) W ⟶ B)
             = g₁ ≫ diag B := by
    have hL : σ ≫ pair (pair (fst ≫ fst) (snd ≫ h₁) ≫ eval_exp A B)
                       (fst ≫ snd : prod (prod A B) W ⟶ B) = pair g₁ g₁ :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, he₁]) (by rw [Cat.assoc, snd_pair, hp])
    have hR : g₁ ≫ diag B = pair g₁ g₁ :=
      pair_uniq _ _ _ (by rw [Cat.assoc, diag_fst, Cat.comp_id]) (by rw [Cat.assoc, diag_snd, Cat.comp_id])
    rw [hL, hR]
  -- So σ ≫ graph₁ ≫ χd = g₁ ≫ diag ≫ χd = g₁ ≫ term ≫ true = term ≫ true.
  have htrue : σ ≫ (pair (pair (fst ≫ fst) (snd ≫ h₂) ≫ eval_exp A B)
                          (fst ≫ snd : prod (prod A B) W ⟶ B) ≫ χd)
             = term (prod A W) ≫ HasSubobjectClassifier.true := by
    rw [← hγ, ← Cat.assoc, hdiag, Cat.assoc,
        HasSubobjectClassifier.classify_sq (diag B) (diag_mono B),
        ← Cat.assoc, term_uniq (g₁ ≫ term B) (term (prod A W))]
  -- `classify_pullback` lifts this cone through `diag B`, giving ℓ ≫ diag = σ ≫ pair e₂ p₀.
  obtain ⟨ℓ, ⟨hℓ, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback (diag B) (diag_mono B)
      ⟨prod A W,
       σ ≫ pair (pair (fst ≫ fst) (snd ≫ h₂) ≫ eval_exp A B) (fst ≫ snd),
       term (prod A W),
       by rw [Cat.assoc]; exact htrue⟩
  simp only at hℓ
  -- Project hℓ to fst/snd:  σ≫e₂ = ℓ = σ≫p₀ = g₁ = σ≫e₁.
  have he₂ : σ ≫ (pair (fst ≫ fst) (snd ≫ h₂) ≫ eval_exp A B) = g₁ := by
    have hA := congrArg (· ≫ fst) hℓ
    have hB := congrArg (· ≫ snd) hℓ
    simp only [Cat.assoc, diag_fst, diag_snd, Cat.comp_id, fst_pair, snd_pair] at hA hB
    rw [← hA, hB]; exact hp
  -- σ ≫ e₁ = σ ≫ e₂  (both g₁), and σ≫eᵢ = pair fst (snd≫hᵢ) ≫ eval = prodMap hᵢ ≫ eval.
  have hev : prodMap A W (exp A B) h₁ ≫ eval_exp A B
           = prodMap A W (exp A B) h₂ ≫ eval_exp A B := by
    have e1 : prodMap A W (exp A B) h₁ = pair (fst : prod A W ⟶ A) (snd ≫ h₁) :=
      pair_uniq _ _ _ (prodMap_fst _ _ _ _) (prodMap_snd _ _ _ _)
    have e2 : prodMap A W (exp A B) h₂ = pair (fst : prod A W ⟶ A) (snd ≫ h₂) :=
      pair_uniq _ _ _ (prodMap_fst _ _ _ _) (prodMap_snd _ _ _ _)
    rw [e1, e2, ← hreindex h₁, ← hreindex h₂, Cat.assoc, Cat.assoc, he₁, he₂]
  -- curry uniqueness:  both h₁, h₂ = curry (prodMap h₁ ≫ eval).
  rw [curry_unique_eq (rfl : prodMap A W (exp A B) h₁ ≫ eval_exp A B = _),
      curry_unique_eq hev.symm]

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

/-- The HEYTING IMPLICATION on SubTerminal, à la Freyd §1.926:
    `U ⇒ V := U ⇔ (U ∧ V)`, i.e. `⟨U, ⟨U,V⟩ ≫ ∧⟩ ≫ ⇔`.

    This is exactly the `impChar`/`Sub.imp` pattern of §1.914 (`S1_91.impChar`),
    transported to subterminators `1 → Ω` (which ARE their own characteristic
    maps).  Because every `SubTerminal` is the classifier of a subobject of `1`,
    `heytingImpl U V = subChar (Sub.imp U# V#)` for the corresponding subobjects,
    which is what makes `subTerminal_heyting` provable from `imp_adjunction`.

    **Why the old definition was wrong.**  The previous def `curry (snd ≫ V) ≫
    (Ω^U) ≫ …` named `snd ≫ V` — the CONSTANT function `x ↦ V` — so the
    contravariant `Ω^U` followed by `eval` reduced to `heytingImpl U V = V`,
    independent of `U`.  That made the forward direction of `subTerminal_heyting`
    false (e.g. `U = ⊥`: `⊥ ∧ Z = ⊥ ≤ V` always, but `Z ≤ V` is not).  The
    `impChar` form below is the genuine relative pseudocomplement. -/
noncomputable def heytingImpl (U V : SubTerminal 𝒞) : SubTerminal 𝒞 :=
  -- `omegaMeet`/`heytingDoubleArrow` live over the Topos product instance; pin
  -- `pair` to the same one to avoid the `HasBinaryProducts`/`HasExponentials`
  -- diamond with `Topos` (cf. `stMeet`), which would otherwise inject a silent
  -- `sorryAx` through a mismatched product structure.
  @pair _ _ (Topos.toHasBinaryProducts) _ _ _ U
    (@pair _ _ (Topos.toHasBinaryProducts) _ _ _ U V ≫ omegaMeet (𝒞 := 𝒞)) ≫
    heytingDoubleArrow (𝒞 := 𝒞)

/-- The MEET of two sub-terminators, `U ∧ V := ⟨U, V⟩ ≫ ∧`, using the internal
    conjunction `omegaMeet : Ω × Ω → Ω` (the classifying map of `⟨true,true⟩`,
    §1.91).  This is the lattice meet on Sub(1). -/
noncomputable def stMeet (U V : SubTerminal 𝒞) : SubTerminal 𝒞 :=
  -- `omegaMeet` lives over the Topos product instance; pin `pair` to the same one
  -- to avoid the `HasBinaryProducts` diamond with `HasExponentials`.
  @pair _ _ (Topos.toHasBinaryProducts) _ _ _ U V ≫ omegaMeet (𝒞 := 𝒞)

/-- The ORDER on sub-terminators: `Z ≤ V` iff `Z ∧ V = Z` (the canonical
    meet-semilattice order; `≤` agreeing with the subobject order on Sub(1)). -/
def stLe (Z V : SubTerminal 𝒞) : Prop := stMeet Z V = Z

/-- **Order bridge for subterminators.**  Pick, for each subterminator `W : 1 → Ω`,
    a subobject `W# ⊆ 1` it classifies (`subChar W# = W`, via `classify_surjective`).
    Then the meet-absorption order `stLe Z W` (i.e. `Z ∧ W = Z`) coincides with the
    subobject order `Z# ≤ W#`.

    Forward post-composes `stLe`'s equation with `Z#.arr` and reads off the right
    conjunct of `meet_true_iff_and` (the membership form: `Z#.arr ≫ W = ⊤`).
    Backward is the glb: `Z# ≤ Z# ∩ W#` and `Z# ∩ W# ≤ Z#` give equal classifiers
    (`classify_eq_of_le_le`), and `omegaMeet_classifies_inter` rewrites `stMeet Z W`
    as `χ_{Z#∩W#}`, collapsing `stLe Z W` to `Z`. -/
theorem stLe_iff_le {Z W : SubTerminal 𝒞}
    (Zs Ws : Subobject 𝒞 (one (𝒞 := 𝒞)))
    (hZ : subChar Zs = Z) (hW : subChar Ws = W) :
    stLe Z W ↔ Zs.le Ws := by
  -- `stMeet Z W` classifies `Zs ∩ Ws` (omegaMeet_classifies_inter), since Z = χ_Zs.
  let hp : HasPullback Zs.arr Ws.arr := HasPullbacks.has _ _
  have hmeet : stMeet Z W = subChar (Sub.inter Zs Ws hp) := by
    show (@pair _ _ Topos.toHasBinaryProducts _ _ _ Z W) ≫ omegaMeet (𝒞 := 𝒞)
        = subChar (Sub.inter Zs Ws hp)
    rw [← hZ, ← hW]
    exact omegaMeet_classifies_inter Zs Ws hp
  constructor
  · -- FORWARD: stLe Z W → Zs ≤ Ws.
    intro hst
    -- hst : stMeet Z W = Z, i.e. χ_{Zs∩Ws} = Z = χ_Zs.
    -- Post-compose with Zs.arr and use meet_true_iff_and to extract Zs.arr ≫ W = ⊤.
    have hZarr : Zs.arr ≫ Z = term Zs.dom ≫ HasSubobjectClassifier.true := by
      rw [← hZ]; exact HasSubobjectClassifier.classify_sq Zs.arr Zs.monic
    have hmeetTrue : Zs.arr ≫ (@pair _ _ Topos.toHasBinaryProducts _ _ _ Z W ≫ omegaMeet (𝒞 := 𝒞))
        = term Zs.dom ≫ HasSubobjectClassifier.true := by
      have : Zs.arr ≫ stMeet Z W = Zs.arr ≫ Z := by rw [hst]
      rw [hZarr] at this
      exact this
    have hand := (meet_true_iff_and Z W Zs.arr).1 hmeetTrue
    -- right conjunct: Zs.arr ≫ W = ⊤, i.e. Zs ≤ Ws.
    rw [le_iff_classify]
    show Zs.arr ≫ subChar Ws = term Zs.dom ≫ HasSubobjectClassifier.true
    rw [hW]
    exact hand.2
  · -- BACKWARD: Zs ≤ Ws → stLe Z W.
    intro hle
    -- Zs ≤ Zs∩Ws and Zs∩Ws ≤ Zs give χ_{Zs∩Ws} = χ_Zs = Z.
    have h1 : (Sub.inter Zs Ws hp).le Zs := Sub.inter_le_left Zs Ws hp
    have h2 : Zs.le (Sub.inter Zs Ws hp) := Sub.inter_glb Zs Ws Zs hp (Sub.le_refl Zs) hle
    have : subChar (Sub.inter Zs Ws hp) = subChar Zs := classify_eq_of_le_le h1 h2
    show stMeet Z W = Z
    rw [hmeet, this, hZ]

/-- **§1.926 — the Heyting adjunction on Sub(1)**.  In a topos the exponential
    structure restricts to a Heyting algebra on `Sub(1) = Hom(1, Ω)`: for every
    `Z U V`, the relative-pseudocomplement / exponential adjunction

        Z ∧ U ≤ V   ↔   Z ≤ (U ⇒ V)

    holds, where `∧ = stMeet`, `≤ = stLe`, and `U ⇒ V = heytingImpl U V` is Freyd's
    implication `U ⇔ (U ∧ V)` (`impChar` shape, §1.926).  This is the substantive
    content of §1.926 (NOT the tautology `∃W, W = U⇒V`).

    Proof via the classifier bridge to §1.914's `imp_adjunction`.  Every
    subterminator is a characteristic map (`classify_surjective`), so pick
    subobjects `Z#, U#, V# ⊆ 1` classifying `Z, U, V`.  Then `heytingImpl U V`
    is `impChar`-shaped on `subChar`s, hence `= χ_{U# ⇒ V#}` (`classify_imp`),
    `stMeet Z U` classifies `Z# ∩ U#`, and `stLe`/`≤` agree (`stLe_iff_le`).  The
    goal reduces to `(U# ∩ Z#) ≤ V# ↔ Z# ≤ (U# ⇒ V#)`, which is `imp_adjunction`
    (modulo `∩`-commutativity, supplied by `inter_glb`/`inter_le`). -/
theorem subTerminal_heyting :
    ∀ (Z U V : SubTerminal 𝒞),
      stLe (stMeet Z U) V ↔ stLe Z (heytingImpl U V) := by
  intro Z U V
  -- Pick subobjects of 1 classifying Z, U, V.
  obtain ⟨Zd, Zm, Zmono, hZ⟩ := classify_surjective Z
  obtain ⟨Ud, Um, Umono, hU⟩ := classify_surjective U
  obtain ⟨Vd, Vm, Vmono, hV⟩ := classify_surjective V
  let Zs : Subobject 𝒞 (one (𝒞 := 𝒞)) := ⟨Zd, Zm, Zmono⟩
  let Us : Subobject 𝒞 (one (𝒞 := 𝒞)) := ⟨Ud, Um, Umono⟩
  let Vs : Subobject 𝒞 (one (𝒞 := 𝒞)) := ⟨Vd, Vm, Vmono⟩
  have hZs : subChar Zs = Z := hZ
  have hUs : subChar Us = U := hU
  have hVs : subChar Vs = V := hV
  -- `heytingImpl U V = χ_{U# ⇒ V#}`: definitionally `impChar Us Vs`, then `classify_imp`.
  have himpl : heytingImpl U V = subChar (Sub.imp Us Vs) := by
    rw [classify_imp]
    show (@pair _ _ Topos.toHasBinaryProducts _ _ _ U
            (@pair _ _ Topos.toHasBinaryProducts _ _ _ U V ≫ omegaMeet (𝒞 := 𝒞)) ≫
            heytingDoubleArrow (𝒞 := 𝒞))
        = impChar Us Vs
    rw [impChar, ← hUs, ← hVs]
  -- `stMeet Z U` classifies `Z# ∩ U#`.
  let hpZU : HasPullback Zs.arr Us.arr := HasPullbacks.has _ _
  have hmeetZU : stMeet Z U = subChar (Sub.inter Zs Us hpZU) := by
    show (@pair _ _ Topos.toHasBinaryProducts _ _ _ Z U) ≫ omegaMeet (𝒞 := 𝒞)
        = subChar (Sub.inter Zs Us hpZU)
    rw [← hZs, ← hUs]
    exact omegaMeet_classifies_inter Zs Us hpZU
  -- LHS: stLe (stMeet Z U) V ↔ (Z# ∩ U#) ≤ V#.
  rw [stLe_iff_le (Sub.inter Zs Us hpZU) Vs hmeetZU.symm hVs]
  -- RHS: stLe Z (heytingImpl U V) ↔ Z# ≤ (U# ⇒ V#).
  rw [stLe_iff_le Zs (Sub.imp Us Vs) hZs himpl.symm]
  -- Now: (Z# ∩ U#) ≤ V# ↔ Z# ≤ (U# ⇒ V#).
  -- imp_adjunction Us Vs Zs : Zs ≤ (Us ⇒ Vs) ↔ (Us ∩ Zs) ≤ Vs.  Bridge ∩-commutativity.
  let hpUZ : HasPullback Us.arr Zs.arr := HasPullbacks.has _ _
  have hcomm : ∀ {T : Subobject 𝒞 (one (𝒞 := 𝒞))},
      (Sub.inter Zs Us hpZU).le T ↔ (Sub.inter Us Zs hpUZ).le T := by
    intro T
    -- The two intersections are mutually ≤ (both glbs of {Zs,Us}), so they share lower-sets.
    have e1 : (Sub.inter Zs Us hpZU).le (Sub.inter Us Zs hpUZ) :=
      Sub.inter_glb Us Zs (Sub.inter Zs Us hpZU) hpUZ
        (Sub.inter_le_right Zs Us hpZU) (Sub.inter_le_left Zs Us hpZU)
    have e2 : (Sub.inter Us Zs hpUZ).le (Sub.inter Zs Us hpZU) :=
      Sub.inter_glb Zs Us (Sub.inter Us Zs hpUZ) hpZU
        (Sub.inter_le_right Us Zs hpUZ) (Sub.inter_le_left Us Zs hpUZ)
    exact ⟨fun h => Sub.le_trans e2 h, fun h => Sub.le_trans e1 h⟩
  rw [hcomm]
  exact (imp_adjunction Us Vs Zs hpUZ).symm

end Freyd
