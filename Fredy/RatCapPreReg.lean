/-
  §1.543 — CONCRETE pre-regularity of the §1.547 base-change slice colimit `ratCapCat P`.

  `LaxColimitPreReg.lean` proves `laxColimPreRegular : PreRegularCategory (laxColimCat L hL)` from
  four hypothesis bundles `LaxTerminalData L`/`LaxProductData L`/`LaxEqualizerData L`/`hcanon`.  This
  file INHABITS those four bundles for `L := laxOfProjSystem' P`, the §1.547 base-change slice system
  (fibres `L.A i = Over (P.pr i)`, transitions `L.F hij = baseChangeObj (P.proj hij)`), and assembles

      instance : PreRegularCategory (ratCapCat P).

  The per-fibre finite-limit data is `overPreRegular` (`SliceRegular.lean`).  The transition
  PRESERVATION (each bundle's `pres`/`presPair`/`presLift`) is exactly "the pullback functor `g*`
  preserves finite limits".  We prove this constructively via the BASE-CHANGE ADJUNCTION
  `Σ_g ⊣ g*` (`reindexObj g ⊣ baseChangeObj g`): a slice map `z ⟶ g* W` in `Over C` is the SAME
  DATA as a slice map `reindexObj g z ⟶ W` in `Over D` (both are an arrow `z.dom ⟶ W.dom` with
  `· ≫ W.hom = z.hom ≫ g`).  The bijection `bcHomEquiv` transports the fibre's product/equalizer
  universal property (joint-monic, pairing, lift) across `g*`, giving every bundle field.

  Mathlib-free; built on the repo's own `Cat` + `SliceRegular` + `CapitalizationLaxColimit` +
  `LaxColimitPreReg`.
-/
import Fredy.LaxColimitPreReg

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]

/-! ## The base-change adjunction `Σ_g ⊣ g*` on the underlying-arrow level

  For `g : C ⟶ D`, base-change `baseChangeObj g : Over D → Over C` sends `W` to the pullback
  `W ×_D C` with structure map `π₂`.  A slice map `u : z ⟶ baseChangeObj g W` in `Over C` is an
  arrow `u.f : z.dom ⟶ (W ×_D C).pt` with `u.f ≫ π₂ = z.hom`.  Post-composing `u.f` with `π₁`
  gives an arrow `z.dom ⟶ W.dom`, and the pullback square turns the over-`C` law into the over-`D`
  law `(u.f ≫ π₁) ≫ W.hom = z.hom ≫ g`.  This is the adjunction transpose; we package its two
  directions as `bcRight`/`bcLeft` and prove they are mutually inverse, plus the naturality we need
  (it intertwines post-composition `· ≫ baseChangeMap g m` with `· ≫ m`). -/
section BaseChangeAdj

variable {C D : 𝒞} (g : C ⟶ D)

/-- The base pullback `W ×_D C` of `W.hom` along `g`.  `abbrev` so `(bcPB g W).cone.pt` is
    definitionally `(baseChangeObj g W).dom` (both unfold to `HasPullbacks.has W.hom g`). -/
abbrev bcPB (W : Over D) : HasPullback W.hom g := HasPullbacks.has W.hom g

/-- **Transpose (right→left): `(z ⟶ g* W) → (reindexObj g z ⟶ W)`.**  Post-compose with `π₁`.  The
    over-`D` law is the pullback square: `(u.f ≫ π₁) ≫ W.hom = u.f ≫ (π₂ ≫ g) = z.hom ≫ g`. -/
def bcTranspose {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    reindexObj g z ⟶ W :=
  ⟨u.f ≫ (bcPB g W).cone.π₁, by
    show (u.f ≫ (bcPB g W).cone.π₁) ≫ W.hom = z.hom ≫ g
    rw [Cat.assoc, (bcPB g W).cone.w, ← Cat.assoc]
    show (u.f ≫ (bcPB g W).cone.π₂) ≫ g = z.hom ≫ g
    rw [show u.f ≫ (bcPB g W).cone.π₂ = z.hom from u.w]⟩

/-- **Transpose (left→right): `(reindexObj g z ⟶ W) → (z ⟶ g* W)`.**  Lift the cone `(a.f, z.hom)`
    into the pullback `W ×_D C`; the cone commutes because `a.f ≫ W.hom = z.hom ≫ g` (the over-`D`
    law).  The lift's `π₂`-leg is `z.hom`, the over-`C` law. -/
def bcLift {z : Over C} {W : Over D} (a : reindexObj g z ⟶ W) :
    z ⟶ baseChangeObj g W :=
  ⟨(bcPB g W).lift ⟨z.dom, a.f, z.hom, by
      show a.f ≫ W.hom = z.hom ≫ g; exact a.w⟩,
    (bcPB g W).lift_snd _⟩

@[simp] theorem bcTranspose_f {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    (bcTranspose g u).f = u.f ≫ (bcPB g W).cone.π₁ := rfl

/-- `bcLift ∘ bcTranspose = id` (over `C`): both arrows lift the same pullback cone, by
    `lift_uniq`. -/
theorem bcLift_bcTranspose {z : Over C} {W : Over D} (u : z ⟶ baseChangeObj g W) :
    bcLift g (bcTranspose g u) = u :=
  OverHom.ext ((bcPB g W).lift_uniq
    ⟨z.dom, (bcTranspose g u).f, z.hom, (bcTranspose g u).w⟩ u.f rfl u.w).symm

/-- `bcTranspose ∘ bcLift = id` (over `D`): the lift's `π₁`-leg is `a.f`, by `lift_fst`. -/
theorem bcTranspose_bcLift {z : Over C} {W : Over D} (a : reindexObj g z ⟶ W) :
    bcTranspose g (bcLift g a) = a :=
  OverHom.ext ((bcPB g W).lift_fst _)

/-- **Naturality of the transpose.**  Post-composing in `Over D` with `m : W ⟶ W'` corresponds to
    post-composing in `Over C` with `baseChangeMap g m`: `bcTranspose (u ⊚ g*m) = bcTranspose u ⊚ m`.
    (Both underlying arrows are `u.f ≫ π₁ˣ ≫ ...`; the base-change map's `π₁`-leg is `lift_fst`.) -/
theorem bcTranspose_natural {z : Over C} {W W' : Over D} (u : z ⟶ baseChangeObj g W)
    (m : W ⟶ W') :
    bcTranspose g (u ⊚ baseChangeMap g m) = bcTranspose g u ⊚ m := by
  apply OverHom.ext
  show (u.f ≫ (baseChangeMap g m).f) ≫ (bcPB g W').cone.π₁
      = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  show (u.f ≫ (bcPB g W').lift (baseChangeCone g m)) ≫ (bcPB g W').cone.π₁
      = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  rw [Cat.assoc, (bcPB g W').lift_fst (baseChangeCone g m)]
  show u.f ≫ ((bcPB g W).cone.π₁ ≫ m.f) = (u.f ≫ (bcPB g W).cone.π₁) ≫ m.f
  rw [Cat.assoc]

/-- **Base-change reflects equality of maps into `g* W`.**  If two maps `u v : z ⟶ g* W` have equal
    transposes, they are equal (the transpose is injective, being one half of a bijection). -/
theorem bcTranspose_inj {z : Over C} {W : Over D} {u v : z ⟶ baseChangeObj g W}
    (h : bcTranspose g u = bcTranspose g v) : u = v := by
  rw [← bcLift_bcTranspose g u, ← bcLift_bcTranspose g v, h]

end BaseChangeAdj

/-! ## Inhabiting the four bundles for `L := laxOfProjSystem' P`

  Throughout, `L.A i = Over (P.pr i)`, `L.F hij = baseChangeObj (P.proj hij)`, and
  `(L.functF hij).map = baseChangeMap (P.proj hij)`.  Each fibre is `overPreRegular`, supplying
  `HasTerminal`/`HasBinaryProducts`/`HasEqualizers`.  The transition-preservation fields are proved
  by transporting the fibre's universal property across the base-change adjunction `bcTranspose`. -/
section Bundles

variable (P : ProjSystem ι D 𝒞)

/-- The base map of the `i ≤ j` transition: the projection `P.proj hij : P.pr j ⟶ P.pr i`. -/
private abbrev pj {i j : ι} (hij : D.le i j) : P.pr j ⟶ P.pr i := P.proj hij

/-- `(laxOfProjSystem' P).functF hij` acts on arrows as `baseChangeMap (P.proj hij)`. -/
private theorem functF_map {i j : ι} (hij : D.le i j) {X Y : Over (P.pr i)} (m : X ⟶ Y) :
    @Functor.map _ _ _ _ _ ((laxOfProjSystem' P).functF hij) X Y m
      = baseChangeMap (pj P hij) m := rfl

/-! ### `LaxTerminalData` -/

/-- **`LaxTerminalData (laxOfProjSystem' P)`.**  Per-fibre terminal is `overHasTerminal (P.pr i)`.
    The pushed terminal `g*(overTerm)` receives `bcLift g (term …)` from any `X`; uniqueness is the
    fibre terminal's `term_uniq` transported across the transpose bijection. -/
noncomputable def ratLaxTerminalData : LaxTerminalData (laxOfProjSystem' P) where
  ht i := overHasTerminal (P.pr i)
  pushTrm {i j} hij X :=
    letI : HasTerminal (Over (P.pr i)) := overHasTerminal (P.pr i)
    bcLift (pj P hij) (term (reindexObj (pj P hij) X))
  pushUniq {i j} hij {X} f g := by
    letI : HasTerminal (Over (P.pr i)) := overHasTerminal (P.pr i)
    exact bcTranspose_inj (pj P hij)
      (term_uniq (bcTranspose (pj P hij) f) (bcTranspose (pj P hij) g))

/-! ### `LaxProductData`

  `g*((hp i).prod a b)`-maps transpose to `(a × b)`-maps in the fibre; `bcTranspose_natural`
  carries `· ≫ map fst|snd` to `· ≫ fst|snd`, so the fibre product's joint-monicity (`pres`) and
  pairing (`presPair`) push across via the transpose bijection. -/

/-- Joint-monicity of a fibre binary product (from `pair_uniq`): two maps equal after `fst` and
    after `snd` are equal. -/
private theorem fibreProd_jointMono {i : ι} (a b : Over (P.pr i)) (z : Over (P.pr i))
    (s t : z ⟶ (overHasBinaryProducts (P.pr i)).prod a b)
    (hf : s ≫ (overHasBinaryProducts (P.pr i)).fst = t ≫ (overHasBinaryProducts (P.pr i)).fst)
    (hs : s ≫ (overHasBinaryProducts (P.pr i)).snd = t ≫ (overHasBinaryProducts (P.pr i)).snd) :
    s = t := by
  letI : HasBinaryProducts (Over (P.pr i)) := overHasBinaryProducts (P.pr i)
  have ht := (overHasBinaryProducts (P.pr i)).pair_uniq (t ≫ (overHasBinaryProducts (P.pr i)).fst)
    (t ≫ (overHasBinaryProducts (P.pr i)).snd) t rfl rfl
  have hsp := (overHasBinaryProducts (P.pr i)).pair_uniq (t ≫ (overHasBinaryProducts (P.pr i)).fst)
    (t ≫ (overHasBinaryProducts (P.pr i)).snd) s hf hs
  rw [hsp, ← ht]

/-- **`LaxProductData (laxOfProjSystem' P)`.**  Per-fibre products `overHasBinaryProducts`; `pres`
    (joint-monic preservation) and `presPair` (pairing preservation) via the adjunction transpose. -/
noncomputable def ratLaxProductData : LaxProductData (laxOfProjSystem' P) where
  hp i := overHasBinaryProducts (P.pr i)
  pres {i j} hij a b z u v hf hs := by
    letI : HasBinaryProducts (Over (P.pr i)) := overHasBinaryProducts (P.pr i)
    -- transpose both projection-equalities (naturality), then fibre joint-monicity.
    apply bcTranspose_inj (pj P hij)
    refine fibreProd_jointMono P a b _ _ _ ?_ ?_
    · exact (bcTranspose_natural (pj P hij) u _).symm.trans
        ((congrArg (bcTranspose (pj P hij)) hf).trans (bcTranspose_natural (pj P hij) v _))
    · exact (bcTranspose_natural (pj P hij) u _).symm.trans
        ((congrArg (bcTranspose (pj P hij)) hs).trans (bcTranspose_natural (pj P hij) v _))
  presPair {i j} hij a b z p q := by
    letI : HasBinaryProducts (Over (P.pr i)) := overHasBinaryProducts (P.pr i)
    -- transpose `p,q` into the fibre, pair, lift back.
    let p' := bcTranspose (pj P hij) p
    let q' := bcTranspose (pj P hij) q
    refine ⟨bcLift (pj P hij) ((overHasBinaryProducts (P.pr i)).pair p' q'), ?_, ?_⟩
    · apply bcTranspose_inj (pj P hij)
      refine (bcTranspose_natural (pj P hij) _ _).trans ?_
      rw [bcTranspose_bcLift (pj P hij)]
      exact (overHasBinaryProducts (P.pr i)).fst_pair p' q'
    · apply bcTranspose_inj (pj P hij)
      refine (bcTranspose_natural (pj P hij) _ _).trans ?_
      rw [bcTranspose_bcLift (pj P hij)]
      exact (overHasBinaryProducts (P.pr i)).snd_pair p' q'

/-! ### `LaxEqualizerData`

  Requires `[HasEqualizers 𝒞]` (the per-fibre `overHasEqualizers`).  `g*(eqObj f g)`-maps transpose
  to `eqObj`-maps in the fibre; `bcTranspose_natural` carries `· ≫ map (eqMap)` to `· ≫ eqMap` and
  `· ≫ map f|g` to `· ≫ f|g`, so the fibre equalizer's monicity (`pres`) and lift (`presLift`) push
  across via the transpose bijection. -/

variable [HasEqualizers 𝒞]

/-- The fibre equalizer map is monic: two maps `s t` into `eqObj f g` equal after `eqMap` are equal
    (both are the unique lift of the same equalizing cone, by `HasEqualizer.uniq`). -/
private theorem fibreEq_mono {i : ι} {A B : Over (P.pr i)} (f g : A ⟶ B) (z : Over (P.pr i))
    (s t : z ⟶ @eqObj _ _ (overHasEqualizers (P.pr i)) _ _ f g)
    (h : s ≫ @eqMap _ _ (overHasEqualizers (P.pr i)) _ _ f g
       = t ≫ @eqMap _ _ (overHasEqualizers (P.pr i)) _ _ f g) :
    s = t := by
  letI : HasEqualizers (Over (P.pr i)) := overHasEqualizers (P.pr i)
  let E := (HasEqualizers.eq A B f g)
  -- the cone whose map is `s ≫ eqMap`; both `s` and `t` are its lift.
  have he : (s ≫ eqMap f g) ≫ f = (s ≫ eqMap f g) ≫ g := by
    rw [Cat.assoc, Cat.assoc, eqMap_eq f g]
  let c : EqualizerCone f g := ⟨z, s ≫ eqMap f g, he⟩
  have hs : s = E.lift c := E.uniq c s rfl
  have ht : t = E.lift c := E.uniq c t h.symm
  rw [hs, ht]

/-- **`LaxEqualizerData (laxOfProjSystem' P)`.**  Per-fibre equalizers `overHasEqualizers`; `pres`
    (monicity preservation) and `presLift` (lift preservation) via the adjunction transpose. -/
noncomputable def ratLaxEqualizerData : LaxEqualizerData (laxOfProjSystem' P) where
  he i := overHasEqualizers (P.pr i)
  pres {i j} hij A B f g z u v huv := by
    letI : HasEqualizers (Over (P.pr i)) := overHasEqualizers (P.pr i)
    apply bcTranspose_inj (pj P hij)
    refine fibreEq_mono P f g _ _ _ ?_
    exact (bcTranspose_natural (pj P hij) u _).symm.trans
      ((congrArg (bcTranspose (pj P hij)) huv).trans (bcTranspose_natural (pj P hij) v _))
  presLift {i j} hij A B f g z k hk := by
    letI : HasEqualizers ((laxOfProjSystem' P).A i) := overHasEqualizers (P.pr i)
    -- transpose `k` into the fibre; it equalizes `f,g` there; take the fibre lift, push back.
    let k' := bcTranspose (pj P hij) k
    have hk' : k' ≫ f = k' ≫ g :=
      (bcTranspose_natural (pj P hij) k f).symm.trans
        ((congrArg (bcTranspose (pj P hij)) hk).trans (bcTranspose_natural (pj P hij) k g))
    let l : reindexObj (pj P hij) z ⟶ eqObj f g := eqLift f g k' hk'
    refine ⟨bcLift (pj P hij) l, ?_⟩
    apply bcTranspose_inj (pj P hij)
    refine (bcTranspose_natural (pj P hij) _ _).trans ?_
    rw [bcTranspose_bcLift (pj P hij)]
    exact eqLift_fac f g k' hk'

/-! ### Assembly: pre-regularity of `ratCapCat P` modulo `hcanon`

  With the three concrete bundles `ratLaxTerminalData`/`ratLaxProductData`/`ratLaxEqualizerData`
  inhabited, `laxColimPreRegular` reduces `PreRegularCategory (ratCapCat P)` to the SINGLE remaining
  representative-level hypothesis `hcanon` (the canonical colimit pullback's `π₂` is a cover whenever
  the cospan leg is).  This mirrors the STRICT `Colim.colimitPreRegular`, which likewise takes its
  `hcanon` as a hypothesis (the strict file's own assembly does not discharge it generically — it
  needs the stage-inclusion-preserves-pullbacks + cover-lifting infrastructure).  We package the
  concrete three-bundle reduction here; `hcanon` is the precise next blocker. -/

/-- `ratCapCat P` as the lax colimit category (definitionally `laxColimCat (laxOfProjSystem' P)
    (coherentProj P)`). -/
noncomputable abbrev ratCat (P : ProjSystem ι D 𝒞) : Cat (Obj (laxOfProjSystem' P)) :=
  laxColimCat (laxOfProjSystem' P) (coherentProj P)

/-- **`PreRegularCategory (ratCapCat P)` from the canonical-pullback cover-transfer `hcanon`.**  The
    three finite-limit bundles are the concrete `ratLax*Data` (base-change preserves slice
    terminal/products/equalizers, proved via the adjunction transpose); the only residual is
    `hcanon`, identical in shape to the strict `colimitPreRegular`'s `hcanon`. -/
noncomputable def ratCapPreRegular [Nonempty ι] [HasEqualizers 𝒞] (P : ProjSystem ι D 𝒞)
    (hcanon : letI : Cat (Obj (laxOfProjSystem' P)) := ratCat P
        letI : HasPullbacks (Obj (laxOfProjSystem' P)) :=
          laxColimHasPullbacks (laxOfProjSystem' P) (coherentProj P)
            (ratLaxTerminalData P) (ratLaxProductData P) (ratLaxEqualizerData P)
      ∀ {A B Z : Obj (laxOfProjSystem' P)} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    @PreRegularCategory (Obj (laxOfProjSystem' P)) (ratCat P) :=
  laxColimPreRegular (laxOfProjSystem' P) (coherentProj P)
    (ratLaxTerminalData P) (ratLaxProductData P) (ratLaxEqualizerData P) hcanon

end Bundles

end Freyd.LaxColim
