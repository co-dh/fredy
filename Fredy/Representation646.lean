import Fredy.Ultraproduct
import Fredy.FiniteSeparation
import Fredy.Horn

open Freyd Freyd.UF

universe u

namespace Freyd
namespace Rep646

variable {𝒞 : Type u} [Cat.{u} 𝒞]

/-! ## The per-list hom-product `T_S` and its functorial action

`T_S A` is the finite product, over the objects `i` listed in `S`, of the **pointed**
hom-set `Hom(i, A)₊ = Option (i ⟶ A)` — phrased as a dependent function on the membership
subtype `{x // x ∈ S}` (the form `Ultraproduct : (I → Type u) → _` consumes).  The basepoint
(`none`) is forced: the bare product `∀ i ∈ S, Hom(i, A)` is EMPTY as soon as some `i ∈ S`
admits no map to `A`, and an empty value-type would make `T A` empty and the representation
vacuously non-faithful.  Adjoining a basepoint to each hom-set keeps every `T_S A` inhabited
(the all-`none` section) WITHOUT disturbing faithfulness/properness, which both turn on the
genuine arrow `id_A` living in the `i = A` component.  `T_S φ` postcomposes (`Option.map`). -/

/-- `T_S A := {i // i ∈ S} → Option (i ⟶ A)` (finite product of pointed hom-sets). -/
def TS (S : List 𝒞) (A : 𝒞) : Type u := (i : {x : 𝒞 // x ∈ S}) → Option (i.1 ⟶ A)

/-- Postcomposition by `φ : A ⟶ B`, the action of `T_S` on a map (basepoint-preserving). -/
def TSmap (S : List 𝒞) {A B : 𝒞} (φ : A ⟶ B) : TS S A → TS S B :=
  fun hom i => (hom i).map (· ≫ φ)

@[simp] theorem TSmap_apply (S : List 𝒞) {A B : 𝒞} (φ : A ⟶ B) (hom : TS S A)
    (i : {x : 𝒞 // x ∈ S}) : TSmap S φ hom i = (hom i).map (· ≫ φ) := rfl

theorem TSmap_id (S : List 𝒞) (A : 𝒞) : TSmap S (Cat.id A) = (id : TS S A → TS S A) := by
  funext hom i
  show (hom i).map (· ≫ Cat.id A) = hom i
  have : (fun x : i.1 ⟶ A => x ≫ Cat.id A) = id := by funext x; exact Cat.comp_id x
  rw [this, Option.map_id_fun, id_eq]

theorem TSmap_comp (S : List 𝒞) {A B C : 𝒞} (φ : A ⟶ B) (ψ : B ⟶ C) :
    TSmap S (φ ≫ ψ) = (fun hom => TSmap S ψ (TSmap S φ hom)) := by
  funext hom i; simp only [TSmap]; cases hom i with
  | none => rfl
  | some h => simp [Option.map, Cat.assoc]

/-! ## The base of principal coideals and the representing ultrafilter

The index is `I := List 𝒞`.  For a list `c`, its **coideal** is `{S | c ⊆ S}` (lists
containing every object of `c`).  These are nonempty (`c ∈ coideal c`) and downward
directed (`coideal (c ++ d) ⊆ coideal c, coideal d`), so they form a `Filter.Base`.  The
coideal of the singleton `[A]` is exactly `{S | A ∈ S}`, so the generated ultrafilter
contains `{S | A ∈ S}` for every object `A` — the largeness used in faithfulness and
non-iso. -/

/-- The coideal of a list `c`: the lists `S` containing every object of `c`. -/
def coideal (c : List 𝒞) : Set (List 𝒞) := fun S => ∀ x ∈ c, x ∈ S

/-- The coideal of `[A]` is `{S | A ∈ S}`. -/
theorem coideal_singleton (A : 𝒞) : coideal [A] = (fun S => A ∈ S) := by
  funext S; apply propext
  exact ⟨fun h => h A (List.mem_singleton.2 rfl),
    fun h x hx => by rw [List.mem_singleton.1 hx]; exact h⟩

/-- The filter base of principal coideals, indexed by lists. -/
def coidealBase : Filter.Base (List 𝒞) (List 𝒞) where
  pt := []
  set := coideal
  nonempty c := ⟨c, fun _ hx => hx⟩
  directed c d := by
    refine ⟨c ++ d, fun S hS x hx => hS x (List.mem_append.2 (Or.inl hx)),
      fun S hS x hx => hS x (List.mem_append.2 (Or.inr hx))⟩

/-- A representing ultrafilter on `List 𝒞`, containing every principal coideal. -/
noncomputable def U (𝒞 : Type u) [Cat.{u} 𝒞] : Ultrafilter (List 𝒞) :=
  (exists_ultrafilter_of_base (coidealBase (𝒞 := 𝒞))).choose

/-- Every coideal `coideal c` is `U`-large. -/
theorem coideal_mem (c : List 𝒞) : (U 𝒞).toFilter.sets (coideal c) :=
  (exists_ultrafilter_of_base (coidealBase (𝒞 := 𝒞))).choose_spec c

/-- `{S | A ∈ S}` is `U`-large for every object `A` (coideal of the singleton). -/
theorem mem_coideal_singleton (A : 𝒞) : (U 𝒞).toFilter.sets (fun S => A ∈ S) := by
  have := coideal_mem (𝒞 := 𝒞) [A]
  rwa [coideal_singleton] at this

/-! ## The §1.646 representation `T : 𝒞 → Type u` -/

/-- The §1.646 representation: `T A := Ultraproduct (S ↦ T_S A) U`. -/
noncomputable def Trep (𝒞 : Type u) [Cat.{u} 𝒞] (A : 𝒞) : Type u :=
  Ultraproduct (fun S => TS S A) (U 𝒞)

/-- The morphism part: `T φ := Ultraproduct.map (S ↦ T_S φ) U`. -/
noncomputable def TrepMap {A B : 𝒞} (φ : A ⟶ B) : Trep 𝒞 A → Trep 𝒞 B :=
  Ultraproduct.map (fun S => TSmap S φ) (U 𝒞)

/-- **Functoriality** of `T`, from `Ultraproduct.map_id`/`map_comp`. -/
noncomputable instance trepFunctor : Functor (Trep 𝒞) where
  map := TrepMap
  map_id A := by
    show TrepMap (Cat.id A) = Cat.id (Trep 𝒞 A)
    unfold TrepMap
    have hfam : (fun S => TSmap S (Cat.id A)) = (fun S => (id : TS S A → TS S A)) := by
      funext S; exact TSmap_id S A
    rw [hfam]; exact Ultraproduct.map_id
  map_comp {A B C} φ ψ := by
    -- in `setCat`, `g ≫ h` is `h ∘ g`; `Ultraproduct.map_comp` says exactly this.
    show TrepMap (φ ≫ ψ) = (fun a => TrepMap ψ (TrepMap φ a))
    unfold TrepMap
    have hfam : (fun S => TSmap S (φ ≫ ψ))
        = (fun S => (TSmap S ψ) ∘ (TSmap S φ)) := by
      funext S; rw [TSmap_comp]; rfl
    rw [hfam, ← Ultraproduct.map_comp]
    rfl

/-! ## Faithfulness (the representation separates maps)

The witness is the **identity section** `idSec A : ∀ S, T_S A`: at each list `S` and each
member `i ∈ S` it places `some id_A` when `i = A` (Yoneda's separating element) and the
basepoint `none` otherwise.  Evaluating `T f` and `T g` on its class, the `i = A` component
reads `some (id_A ≫ f) = some f` versus `some g`; so on the `U`-large coideal `{S | A ∈ S}`
the two images disagree whenever `f ≠ g`. -/

open Classical in
/-- The identity section: `some id_A` on the `i = A` coordinate, `none` elsewhere. -/
noncomputable def idSec (A : 𝒞) (S : List 𝒞) : TS S A :=
  fun i => if h : i.1 = A then some (h ▸ Cat.id A) else none

/-- On any list `S` with `A ∈ S`, the `A`-component of `idSec A S` is `some id_A`. -/
theorem idSec_apply_self (A : 𝒞) {S : List 𝒞} (hA : A ∈ S) :
    idSec A S ⟨A, hA⟩ = some (Cat.id A) := by
  classical
  show (if h : A = A then some (h ▸ Cat.id A) else none) = some (Cat.id A)
  rw [dif_pos rfl]

/-- **Faithfulness.**  `T` separates maps: `T f = T g ⟹ f = g`.  The disagreement of `f, g`
    survives in the `U`-large coideal `{S | A ∈ S}` via the `i = A` component of `idSec`. -/
theorem trep_separatesMaps : SeparatesMaps (Trep 𝒞) := by
  intro A B f g hfg
  -- Apply the (equal) maps to the class of the identity section.
  have happ : TrepMap f (Ultraproduct.mk (U 𝒞) (idSec A))
      = TrepMap g (Ultraproduct.mk (U 𝒞) (idSec A)) :=
    congrFun hfg (Ultraproduct.mk (U 𝒞) (idSec A))
  -- Unfold to a `U`-large agreement of the two postcomposed sections.
  rw [TrepMap, TrepMap, Ultraproduct.map_mk, Ultraproduct.map_mk,
    Ultraproduct.mk_eq_mk] at happ
  -- Intersect the agreement coideal with the singleton coideal `{S | A ∈ S}`.
  have hcap := (U 𝒞).toFilter.inter_mem happ (mem_coideal_singleton (𝒞 := 𝒞) A)
  obtain ⟨S, hagree, hA⟩ := (U 𝒞).toFilter.mem_nonempty hcap
  -- At the `A`-component the two sections read `some (id_A ≫ f)` and `some (id_A ≫ g)`.
  have hcomp := congrFun hagree ⟨A, hA⟩
  simp only [Ultraproduct.liftSection, TSmap, idSec_apply_self A hA, Option.map_some] at hcomp
  have : Cat.id A ≫ f = Cat.id A ≫ g := Option.some.inj hcomp
  rwa [Cat.id_comp, Cat.id_comp] at this

/-! ## Properness preservation (a proper mono `m : A' ↪ A` maps to a proper map of sets)

`T m` stays a MONO because each `T_S m = Option.map (· ≫ m)` is injective (postcomposing by
a mono is injective on hom-sets, and `Option.map` of an injection is an injection); the
injective set is all of `List 𝒞`, hence `U`-large, so `Ultraproduct.map_injective` applies.

`T m` stays NON-ISO because, on the `U`-large coideal `{S | A ∈ S}`, the identity section
`idSec A S` is OUTSIDE the image of `T_S m`: a preimage would supply `r : A ⟶ A'` with
`r ≫ m = id_A`, i.e. a section of `m`; combined with `m` monic this makes `m` an iso,
contradicting properness.  `Ultraproduct.map_not_surjective` then makes `T m` non-surjective,
hence non-iso. -/

/-- A mono with a section is an iso: if `r ≫ m = id` and `m` is monic then `m` is iso.
    (`m ≫ r ≫ m = m = id ≫ m`, so monic gives `m ≫ r = id`.) -/
theorem isIso_of_section_of_mono {A' A : 𝒞} {m : A' ⟶ A} (hm : Monic m) {r : A ⟶ A'}
    (hr : r ≫ m = Cat.id A) : IsIso m := by
  refine ⟨r, ?_, hr⟩
  apply hm (m ≫ r) (Cat.id A')
  rw [Cat.assoc, hr, Cat.comp_id, Cat.id_comp]

/-- Each `T_S m` is injective when `m` is monic (postcomposition by a mono, lifted to
    `Option`). -/
theorem tsmap_injective_of_mono {A' A : 𝒞} {m : A' ⟶ A} (hm : Monic m) (S : List 𝒞) :
    Function.Injective (TSmap S m) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  simp only [TSmap] at hi
  cases hx : x i with
  | none => cases hy : y i with
    | none => rfl
    | some hy' => rw [hx, hy] at hi; exact absurd hi (by simp)
  | some hx' => cases hy : y i with
    | none => rw [hx, hy] at hi; exact absurd hi (by simp)
    | some hy' =>
      rw [hx, hy] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      exact congrArg some (hm hx' hy' hi)

/-- **`T m` is a mono** (injective) for monic `m`: each `T_S m` is injective, `U`-largely. -/
theorem trep_map_injective {A' A : 𝒞} {m : A' ⟶ A} (hm : Monic m) :
    Function.Injective (TrepMap m) := by
  refine Ultraproduct.map_injective (fun S => TSmap S m) (U 𝒞) ?_
  exact (U 𝒞).toFilter.up_closed (U 𝒞).toFilter.univ_mem
    (fun S _ => tsmap_injective_of_mono hm S)

/-- **`T m` is not surjective** for a PROPER mono `m`: the identity section `idSec A` is
    missed on the `U`-large coideal `{S | A ∈ S}`. -/
theorem trep_map_not_surjective {A' A : 𝒞} {m : A' ⟶ A} (hm : Monic m) (hniso : ¬ IsIso m) :
    ¬ ∃ q, TrepMap m q = Ultraproduct.mk (U 𝒞) (idSec A) := by
  refine Ultraproduct.map_not_surjective (fun S => TSmap S m) (U 𝒞) (idSec A) ?_
  -- on `{S | A ∈ S}` no section maps to `idSec A S` (it would split `m`).
  refine (U 𝒞).toFilter.up_closed (mem_coideal_singleton (𝒞 := 𝒞) A) (fun S hA a hcon => ?_)
  -- evaluate at the `A`-component: `(a ⟨A,hA⟩).map (·≫m) = some id_A`.
  have hcomp := congrFun hcon ⟨A, hA⟩
  rw [idSec_apply_self A hA] at hcomp
  simp only [TSmap] at hcomp
  -- so `a ⟨A,hA⟩ = some r` with `r ≫ m = id_A`, giving a section of `m`.
  cases ha : a ⟨A, hA⟩ with
  | none => rw [ha] at hcomp; exact absurd hcomp (by simp)
  | some r =>
    rw [ha] at hcomp
    simp only [Option.map_some, Option.some.injEq] at hcomp
    exact hniso (isIso_of_section_of_mono hm hcomp)

/-- **Properness preserved.**  A proper mono `m : A' ↪ A` (monic, non-iso) maps under `T` to
    a monic, non-iso map of sets (`Monic (T m) ∧ ¬ IsIso (T m)`) — the §1.453
    `PreservesProperness` conclusion, in its cross-universe form. -/
theorem trep_preserves_properMono {A' A : 𝒞} {m : A' ⟶ A} (hm : ProperMono m) :
    Monic (trepFunctor.map m) ∧ ¬ IsIso (trepFunctor.map m) := by
  obtain ⟨hmono, hniso⟩ := hm
  refine ⟨?_, ?_⟩
  · -- mono in `setCat` is injectivity.
    intro W x y hxy
    funext w
    exact trep_map_injective hmono (congrFun hxy w)
  · -- iso in `setCat` would be surjective, contradicting the missed identity section.
    rintro ⟨ginv, _, h2⟩
    refine trep_map_not_surjective hmono hniso ⟨ginv (Ultraproduct.mk (U 𝒞) (idSec A)), ?_⟩
    exact congrFun h2 (Ultraproduct.mk (U 𝒞) (idSec A))

/-! ## The §1.646 representation theorem -/

/-- **§1.646 (representation theorem).**  Every small category `𝒞` (in particular every small
    special positive pre-logos / special Cartesian category) admits a representation
    `T : 𝒞 → Type u` into the category of sets that is

    * a `Functor`,
    * FAITHFUL (separates maps), and
    * PROPERNESS-PRESERVING: a proper mono `m : A' ↪ A` maps to a monic, non-iso map of sets.

    The representation is `T A = Ultraproduct (S ↦ ∀ i ∈ S, Hom(i, A)₊) U` over the index
    `List 𝒞`, with `U` an ultrafilter containing every principal coideal `{S | A ∈ S}`
    (Phase A), and `T φ` postcomposition collapsed through `Ultraproduct.map` (Phase B).  The
    properness conclusion is stated as `Monic (T m) ∧ ¬ IsIso (T m)` (the §1.453
    `PreservesProperness` conclusion) in its cross-universe form, since `T : 𝒞 → Type u`
    lands one universe up from `𝒞`. -/
theorem representation646 (𝒞 : Type u) [Cat.{u} 𝒞] :
    ∃ (T : 𝒞 → Type u) (hT : Functor T),
      SeparatesMaps T ∧
      ∀ {A' A : 𝒞} {m : A' ⟶ A}, ProperMono m →
        Monic (hT.map m) ∧ ¬ IsIso (hT.map m) :=
  ⟨Trep 𝒞, trepFunctor, trep_separatesMaps, fun hm => trep_preserves_properMono hm⟩

end Rep646
end Freyd
