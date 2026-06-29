/-
  §2.218 R3 (positive) — the POSITIVE Capitalization Lemma.

  Assemble `capitalization_lemma_regular_positive`: every small POSITIVE pre-logos `A`
  (`[DisjointBinaryCoproduct A]`) admits a faithful representation into a CAPITAL, POSITIVE
  pre-logos `Ā`.  This is the coproduct mirror of `capitalization_lemma_regular`
  (`Fredy/CapDataRegular.lean`): we feed the strict `colimitPositive` (`Fredy/ColimitPositive.lean`)
  the §1.543 cofinal ω-tower, whose stages are now known positive (`stageDisjoint`, in
  `Fredy/CapDataPositive.lean`), together with the per-stage binary-coproduct preservation iterated
  along the tower (the coproduct mirror of `transN_preservesBinaryProducts`/`towerHp…`).

  Per-step input: there is NO `CapStep.stepCoprods` field, so the per-rung coproduct preservation is
  threaded EXTERNALLY from the committed `uniformStep_preservesBinaryCoproducts`
  (`Fredy/UniformStepCoproduct.lean`), specialised to the cofinal successor `uniformStepFun`. -/
import Fredy.CapDataPositive
import Fredy.UniformStepCoproduct
import Fredy.CapDataRegular
import Fredy.ColimitPositive
import Fredy.ObjInclRegular

open Freyd
open Freyd.Colim
open Freyd.CofinalProj
open Freyd.LaxColim
open Freyd.UniformCap (uniformStep_preservesBinaryCoproducts)

namespace Freyd.LaxColim

universe u w

/-- **General lax-colimit strict coterminator** (generalises `laxColimStrictInitial` from the chosen
    `stageZero` to an ARBITRARY fibre object `Y` whose transitions out of `i₀` all land on strict
    coterminators).  Same proof: a map `g` into `objIncl i₀ Y` is a germ `homInclL xX Y a f₀`; its
    codomain `L.F a.2.2 Y` is a strict coterminator (`htrans a.2.2`), so `f₀` (a map into it) is iso,
    lifted to the colimit by `homInclL_isIso_of_rep`. -/
theorem laxColimStrictCot {ι : Type u} {D : Directed ι} (L : LaxCatSystem.{u, w} ι D)
    (hL : Coherent L) {i₀ : ι} (Y : L.A i₀)
    (htrans : ∀ {j : ι} (hij : D.le i₀ j), @StrictCoterminator (L.A j) (L.catA j) (L.F hij Y)) :
    letI : Cat (Obj L) := laxColimCat L hL
    @StrictCoterminator (Obj L) (laxColimCat L hL) (objIncl L i₀ Y) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro X g
  obtain ⟨jX, xX⟩ := X
  refine Quotient.inductionOn g (fun rep => ?_)
  obtain ⟨a, f₀⟩ := rep
  obtain ⟨g₀, h1, h2⟩ := htrans a.2.2 f₀
  exact homInclL_isIso_of_rep L hL xX Y a f₀ g₀ h1 h2

end Freyd.LaxColim

namespace Freyd.UniformCap

open Freyd.CofinalProj
open Freyd.LaxColim

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S] [DecidableEq S] [Nonempty (WSList S)]

/-- **The §1.547 successor `uniformStepObj` preserves STRICT COTERMINATORS** (strict initials).  The
    successor factors as `uniformStepObj W Z = objIncl (laxOfProjSystem' (cofinalProjSystem S)) W.base
    (terminalSliceObj W Z)`.  When `Z` is a strict coterminator of `S`, the slice object
    `terminalSliceObj W Z = ⟨Z, !⟩` is a strict coterminator of `Over (∏ base)` (`overIso_of_underlying`
    on the underlying iso), and every base-change transition out of `W.base` preserves it
    (`baseChange_strictCoterminator`), so `laxColimStrictCot` makes its `objIncl` a strict
    coterminator of the lax colimit.  This is the per-rung input to the tower `hinitpres`. -/
theorem uniformStep_preservesStrictCot (W : WSCover S) {Z : S} (hZ : StrictCoterminator Z) :
    @StrictCoterminator (uniformTargetTy W) (uniformTargetCat W) (uniformStepObj W Z) := by
  -- the slice object `⟨Z, !⟩` is a strict coterminator (its underlying arrow is iso since `Z` is).
  have hslice : StrictCoterminator (terminalSliceObj W Z) :=
    fun {Y} g => overIso_of_underlying g (hZ g.f)
  -- objIncl of it is a strict coterminator: transitions out of `W.base` are base-changes, which
  -- preserve strict coterminators.
  intro X f
  exact laxColimStrictCot (laxOfProjSystem' (cofinalProjSystem (S := S)))
    (coherentProj (cofinalProjSystem (S := S))) (i₀ := W.base) (terminalSliceObj W Z)
    (fun {j} hij => baseChange_strictCoterminator ((cofinalProjSystem (S := S)).proj hij) hslice) f

end Freyd.UniformCap

namespace Freyd.Colim

universe u

variable {𝒜 ℬ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ]

/-- **The coproduct injections `inl, inr` are jointly epic.**  Two maps out of `coprod A B` agreeing
    after precomposition with `inl` and `inr` are equal (each is the copairing of its `inl`/`inr`
    legs, by `case_uniq`). -/
theorem coprod_jointEpi [HasBinaryCoproducts 𝒜] {A B w : 𝒜}
    (m n : HasBinaryCoproducts.coprod A B ⟶ w)
    (h1 : HasBinaryCoproducts.inl ≫ m = HasBinaryCoproducts.inl ≫ n)
    (h2 : HasBinaryCoproducts.inr ≫ m = HasBinaryCoproducts.inr ≫ n) : m = n := by
  have hm : m = HasBinaryCoproducts.case (HasBinaryCoproducts.inl ≫ m) (HasBinaryCoproducts.inr ≫ m) :=
    HasBinaryCoproducts.case_uniq _ _ m rfl rfl
  have hn : n = HasBinaryCoproducts.case (HasBinaryCoproducts.inl ≫ n) (HasBinaryCoproducts.inr ≫ n) :=
    HasBinaryCoproducts.case_uniq _ _ n rfl rfl
  rw [hm, hn, h1, h2]

/-- **Joint epi-ness of `(F inl, F inr)` from `PreservesBinaryCoproducts`** (coproduct dual of
    `preservesBinaryProducts_jointly_monic`).  The comparison `φ = case (F inl) (F inr)` is iso,
    hence epic; and `inl ≫ φ = F inl`, `inr ≫ φ = F inr`, so two maps out of `F(A+B)` agreeing after
    `F inl` and `F inr` agree after `φ`, hence are equal.  This is the `hcoppres` content. -/
theorem preservesBinaryCoproducts_jointEpi [HasBinaryCoproducts 𝒜] [HasBinaryCoproducts ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F] (hpc : PreservesBinaryCoproducts F) {A B : 𝒜} {z : ℬ}
    (u v : F (HasBinaryCoproducts.coprod A B) ⟶ z)
    (hl : hF.map (HasBinaryCoproducts.inl (A := A) (B := B)) ≫ u
        = hF.map (HasBinaryCoproducts.inl (A := A) (B := B)) ≫ v)
    (hr : hF.map (HasBinaryCoproducts.inr (A := A) (B := B)) ≫ u
        = hF.map (HasBinaryCoproducts.inr (A := A) (B := B)) ≫ v) : u = v := by
  obtain ⟨ψ, _, hψ2⟩ := (hpc (A := A) (B := B) :
    IsIso (HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
      (hF.map (HasBinaryCoproducts.inr (A := A) (B := B)))))
  -- φ ≫ u = φ ≫ v (jointly epic inl,inr after rewriting `inl ≫ φ = F inl`), then ψ ≫ φ = id gives u = v.
  have hcomp : HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
        (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) ≫ u
      = HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
        (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) ≫ v :=
    coprod_jointEpi _ _
      (by rw [← Cat.assoc, ← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hl)
      (by rw [← Cat.assoc, ← Cat.assoc, HasBinaryCoproducts.case_inr]; exact hr)
  calc u = (ψ ≫ HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
              (hF.map (HasBinaryCoproducts.inr (A := A) (B := B)))) ≫ u := by rw [hψ2, Cat.id_comp]
    _ = ψ ≫ (HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
              (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) ≫ u) := by rw [Cat.assoc]
    _ = ψ ≫ (HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
              (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))) ≫ v) := by rw [hcomp]
    _ = (ψ ≫ HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
              (hF.map (HasBinaryCoproducts.inr (A := A) (B := B)))) ≫ v := by rw [Cat.assoc]
    _ = v := by rw [hψ2, Cat.id_comp]

/-- **Copairing through `(F inl, F inr)` from `PreservesBinaryCoproducts`** (coproduct dual of
    `preservesBinaryProducts_pair`).  The comparison `φ = case (F inl) (F inr)` being iso lets any
    `p : F A ⟶ z`, `q : F B ⟶ z` factor through `F(A+B)`: take `r := φ⁻¹ ≫ case p q`, using
    `F inl ≫ φ⁻¹ = inl`.  This is the `hcoppres_case` content. -/
theorem preservesBinaryCoproducts_case [HasBinaryCoproducts 𝒜] [HasBinaryCoproducts ℬ]
    (F : 𝒜 → ℬ) [hF : Functor F] (hpc : PreservesBinaryCoproducts F) {A B : 𝒜} {z : ℬ}
    (p : F A ⟶ z) (q : F B ⟶ z) :
    ∃ r : F (HasBinaryCoproducts.coprod A B) ⟶ z,
      hF.map (HasBinaryCoproducts.inl (A := A) (B := B)) ≫ r = p
      ∧ hF.map (HasBinaryCoproducts.inr (A := A) (B := B)) ≫ r = q := by
  obtain ⟨ψ, hψ1, _⟩ := (hpc (A := A) (B := B) :
    IsIso (HasBinaryCoproducts.case (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
      (hF.map (HasBinaryCoproducts.inr (A := A) (B := B)))))
  -- `F inl ≫ ψ = inl`: `F inl = inl ≫ φ` (case_inl) and `φ ≫ ψ = id`, so `F inl ≫ ψ = inl ≫ φ ≫ ψ = inl`.
  have hFinl : hF.map (HasBinaryCoproducts.inl (A := A) (B := B)) ≫ ψ = HasBinaryCoproducts.inl := by
    rw [← HasBinaryCoproducts.case_inl (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
      (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))), Cat.assoc, hψ1, Cat.comp_id]
  have hFinr : hF.map (HasBinaryCoproducts.inr (A := A) (B := B)) ≫ ψ = HasBinaryCoproducts.inr := by
    rw [← HasBinaryCoproducts.case_inr (hF.map (HasBinaryCoproducts.inl (A := A) (B := B)))
      (hF.map (HasBinaryCoproducts.inr (A := A) (B := B))), Cat.assoc, hψ1, Cat.comp_id]
  refine ⟨ψ ≫ HasBinaryCoproducts.case p q, ?_, ?_⟩
  · rw [← Cat.assoc, hFinl, HasBinaryCoproducts.case_inl]
  · rw [← Cat.assoc, hFinr, HasBinaryCoproducts.case_inr]

end Freyd.Colim

namespace Freyd

universe u

/-- **Per-rung binary-coproduct preservation (variable previous pre-regular structure).**  Mirror of
    `succ_component` (CapDataPositive): with the previous pre-regular structure `pr` as an explicit
    VARIABLE and `e : dbcPreReg dC = pr`, `subst e` makes the §1.547 successor's pre-regular structure
    DEFEQ to the coproduct-derived one, so the committed `uniformStep_preservesBinaryCoproducts`
    applies on the nose (its `[DisjointBinaryCoproduct]`-derived `PreRegularCategory` then equals
    `dbcPreReg dC`).  The successor's coproducts are exactly `(succ_component …).1.toHasBinaryCoproducts`
    — the lax target of `uniformStep_preservesBinaryCoproducts`. -/
theorem rungPresCoprod {C : Type u} (ct : Cat.{u} C) (pr : @PreRegularCategory C ct)
    (dC : @DisjointBinaryCoproduct C ct) (e : dbcPreReg dC = pr) :
    @PreservesBinaryCoproducts C (uniformStepFun ⟨C, ct, pr⟩).T ct
      (uniformStepFun ⟨C, ct, pr⟩).catT
      (uniformStepFun ⟨C, ct, pr⟩).step (uniformStepFun ⟨C, ct, pr⟩).stepFun
      dC.toHasBinaryCoproducts
      (succ_component ct pr dC e).1.toHasBinaryCoproducts := by
  subst e
  letI iCat : Cat C := ct
  letI : DisjointBinaryCoproduct C := dC
  letI : DecidableEq C := (wsCover ⟨C, ct, dbcPreReg dC⟩).dec
  intro A B
  exact uniformStep_preservesBinaryCoproducts (S := C) (wsCover ⟨C, ct, dbcPreReg dC⟩) (A := A) (B := B)

/-- **The iterated transition `transN n d` preserves binary coproducts.**  Coproduct mirror of
    `transN_preservesBinaryProducts` (Capitalization).  The per-rung input is `rungPresCoprod` (the
    committed `uniformStep_preservesBinaryCoproducts`), composed `d` times via
    `preservesBinaryCoproducts_comp`.  Per-stage coproducts are the disjoint coproducts
    `(stageDisjoint …).toHasBinaryCoproducts`. -/
theorem transN_preservesBinaryCoproducts (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre) (n d : Nat) :
    @PreservesBinaryCoproducts _ _ (stageBundle uniformStepFun b n).cat
      (stageBundle uniformStepFun b (n+d)).cat
      (transN uniformStepFun b n d) (transNFun uniformStepFun b n d)
      (stageDisjoint b hb0 hpb0 n).toHasBinaryCoproducts
      (stageDisjoint b hb0 hpb0 (n+d)).toHasBinaryCoproducts := by
  induction d with
  | zero =>
    intro A B
    letI iCop : HasBinaryCoproducts (stageBundle uniformStepFun b n).carrier :=
      (stageDisjoint b hb0 hpb0 n).toHasBinaryCoproducts
    letI iCop0 : HasBinaryCoproducts (stageBundle uniformStepFun b (n+0)).carrier :=
      (stageDisjoint b hb0 hpb0 (n+0)).toHasBinaryCoproducts
    show @IsIso _ (stageBundle uniformStepFun b (n+0)).cat _ _
      (HasBinaryCoproducts.case ((transNFun uniformStepFun b n 0).map HasBinaryCoproducts.inl)
        ((transNFun uniformStepFun b n 0).map HasBinaryCoproducts.inr))
    rw [show (transNFun uniformStepFun b n 0).map (HasBinaryCoproducts.inl (A := A) (B := B))
          = HasBinaryCoproducts.inl from rfl,
      show (transNFun uniformStepFun b n 0).map (HasBinaryCoproducts.inr (A := A) (B := B))
          = HasBinaryCoproducts.inr from rfl,
      show HasBinaryCoproducts.case (HasBinaryCoproducts.inl (A := A) (B := B))
            HasBinaryCoproducts.inr = Cat.id _ from
        (HasBinaryCoproducts.case_uniq _ _ _ (Cat.comp_id _) (Cat.comp_id _)).symm]
    exact ⟨Cat.id _, Cat.id_comp _, Cat.id_comp _⟩
  | succ d ihF =>
    intro A B
    exact @preservesBinaryCoproducts_comp (stageBundle uniformStepFun b n).carrier
      (stageBundle uniformStepFun b (n+d)).carrier (stageBundle uniformStepFun b (n+d+1)).carrier
      (stageBundle uniformStepFun b n).cat (stageBundle uniformStepFun b (n+d)).cat
      (stageBundle uniformStepFun b (n+d+1)).cat
      (stageDisjoint b hb0 hpb0 n).toHasBinaryCoproducts
      (stageDisjoint b hb0 hpb0 (n+d)).toHasBinaryCoproducts
      (stageDisjoint b hb0 hpb0 (n+d+1)).toHasBinaryCoproducts
      (transN uniformStepFun b n d) (stageStep uniformStepFun b (n+d))
      (transNFun uniformStepFun b n d) (stageStepFun uniformStepFun b (n+d))
      ihF
      (rungPresCoprod (stageBundle uniformStepFun b (n+d)).cat (stageBundle uniformStepFun b (n+d)).pre
        (stageDisjointAux b hb0 hpb0 (n+d)).1 (stageDisjointAux b hb0 hpb0 (n+d)).2)
      (A := A) (B := B)

/-- **The `stageCast`-transported difference functor preserves binary coproducts** (generic over the
    target stage equality `h : m + d = n`).  `subst h` collapses both `stageCast` and `stageCastHom`,
    reducing to `transN_preservesBinaryCoproducts`.  Coproduct mirror of
    `stageCast_transN_preservesBinaryProducts`. -/
theorem stageCast_transN_preservesBinaryCoproducts (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre)
    (m d n : Nat) (h : m + d = n) :
    @PreservesBinaryCoproducts _ _ (stageBundle uniformStepFun b m).cat
      (stageBundle uniformStepFun b n).cat
      (fun x => stageCast b uniformStepFun h (transN uniformStepFun b m d x))
      { map := fun {x y} g => stageCastHom b uniformStepFun h ((transNFun uniformStepFun b m d).map g)
        map_id := fun x => by rw [(transNFun uniformStepFun b m d).map_id, stageCastHom_id]
        map_comp := fun f g => by rw [(transNFun uniformStepFun b m d).map_comp, stageCastHom_comp] }
      (stageDisjoint b hb0 hpb0 m).toHasBinaryCoproducts
      (stageDisjoint b hb0 hpb0 n).toHasBinaryCoproducts := by
  subst h
  exact transN_preservesBinaryCoproducts b hb0 hpb0 m d

/-- **`towerF hij` preserves binary coproducts.**  `towerF`/`towerFunctF` ARE the `stageCast`-transport
    of `transN`/`transNFun`, so apply the generic transport.  Coproduct mirror of
    `towerF_preservesBinaryProducts`. -/
theorem towerF_preservesBinaryCoproducts (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) :
    @PreservesBinaryCoproducts _ _ (stageBundle uniformStepFun b i.down).cat
      (stageBundle uniformStepFun b j.down).cat (towerF b uniformStepFun hij)
      (towerFunctF b uniformStepFun hij)
      (stageDisjoint b hb0 hpb0 i.down).toHasBinaryCoproducts
      (stageDisjoint b hb0 hpb0 j.down).toHasBinaryCoproducts :=
  stageCast_transN_preservesBinaryCoproducts b hb0 hpb0 i.down (j.down - i.down) j.down
    (Nat.add_sub_cancel' hij)

/-! ### The destructured tower coproduct-preservation package (mirror of `towerHp`/`towerHppres`/…) -/

/-- The tower's per-stage binary coproducts (the disjoint coproducts). -/
noncomputable def towerHcop (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre)
    (i : ULift.{u} Nat) :
    @HasBinaryCoproducts ((towerSystem b uniformStepFun).A i) ((towerSystem b uniformStepFun).catA i) :=
  (stageDisjoint b hb0 hpb0 i.down).toHasBinaryCoproducts

/-- **`hcoppres`** (joint epi-ness of `(F inl, F inr)`) from `towerF_preservesBinaryCoproducts`. -/
theorem towerHcoppres (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a c : (towerSystem b uniformStepFun).A i) (z : (towerSystem b uniformStepFun).A j)
    (u v : (towerSystem b uniformStepFun).F hij ((towerHcop b hb0 hpb0 i).coprod a c) ⟶ z)
    (hl : ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inl ≫ u
        = ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inl ≫ v)
    (hr : ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inr ≫ u
        = ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inr ≫ v) : u = v :=
  @Freyd.Colim.preservesBinaryCoproducts_jointEpi (stageBundle uniformStepFun b i.down).carrier
    (stageBundle uniformStepFun b j.down).carrier (stageBundle uniformStepFun b i.down).cat
    (stageBundle uniformStepFun b j.down).cat (towerHcop b hb0 hpb0 i) (towerHcop b hb0 hpb0 j)
    (towerF b uniformStepFun hij) (towerFunctF b uniformStepFun hij)
    (towerF_preservesBinaryCoproducts b hb0 hpb0 hij) a c z u v hl hr

/-- **`hcoppres_case`** (copairing through `(F inl, F inr)`) from `towerF_preservesBinaryCoproducts`. -/
theorem towerHcoppresCase (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a c : (towerSystem b uniformStepFun).A i) (z : (towerSystem b uniformStepFun).A j)
    (p : (towerSystem b uniformStepFun).F hij a ⟶ z) (q : (towerSystem b uniformStepFun).F hij c ⟶ z) :
    ∃ r : (towerSystem b uniformStepFun).F hij ((towerHcop b hb0 hpb0 i).coprod a c) ⟶ z,
      ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inl ≫ r = p
      ∧ ((towerSystem b uniformStepFun).functF hij).map (towerHcop b hb0 hpb0 i).inr ≫ r = q :=
  @Freyd.Colim.preservesBinaryCoproducts_case (stageBundle uniformStepFun b i.down).carrier
    (stageBundle uniformStepFun b j.down).carrier (stageBundle uniformStepFun b i.down).cat
    (stageBundle uniformStepFun b j.down).cat (towerHcop b hb0 hpb0 i) (towerHcop b hb0 hpb0 j)
    (towerF b uniformStepFun hij) (towerFunctF b uniformStepFun hij)
    (towerF_preservesBinaryCoproducts b hb0 hpb0 hij) a c z p q

/-! ### Strict-initial preservation along the tower (for the colimit `hinitpres`) -/

/-- **`transN n d` preserves strict coterminators.**  Fold the per-rung
    `uniformStep_preservesStrictCot` over the `d` rungs.  (No coproduct instance is involved, so this
    threads through the bundled `(stage k).pre` with no instance diamond.) -/
theorem transN_preservesStrictCot (b : PreRegBundle.{u}) (n d : Nat)
    (Z : (stageBundle uniformStepFun b n).carrier)
    (hZ : @StrictCoterminator _ (stageBundle uniformStepFun b n).cat Z) :
    @StrictCoterminator _ (stageBundle uniformStepFun b (n+d)).cat (transN uniformStepFun b n d Z) := by
  induction d with
  | zero => exact hZ
  | succ d ih =>
    letI : DecidableEq (stageBundle uniformStepFun b (n+d)).carrier :=
      (wsCover (stageBundle uniformStepFun b (n+d))).dec
    letI : Nonempty (WSList (stageBundle uniformStepFun b (n+d)).carrier) :=
      ⟨(wsCover (stageBundle uniformStepFun b (n+d))).base⟩
    intro X f
    exact Freyd.UniformCap.uniformStep_preservesStrictCot
      (S := (stageBundle uniformStepFun b (n+d)).carrier)
      (wsCover (stageBundle uniformStepFun b (n+d))) ih f

/-- **The `stageCast` preserves strict coterminators** (it is `Eq.rec`, an iso). -/
theorem stageCast_preservesStrictCot (b : PreRegBundle.{u}) {m n : Nat} (h : m = n)
    (Z : (stageBundle uniformStepFun b m).carrier)
    (hZ : @StrictCoterminator _ (stageBundle uniformStepFun b m).cat Z) :
    @StrictCoterminator _ (stageBundle uniformStepFun b n).cat (stageCast b uniformStepFun h Z) := by
  subst h; exact hZ

/-- **`towerF hij` preserves strict coterminators.**  `towerF` is `stageCast ∘ transN`. -/
theorem towerF_preservesStrictCot (b : PreRegBundle.{u}) {i j : ULift.{u} Nat}
    (hij : uliftNatDirected.le i j) (Z : (stageBundle uniformStepFun b i.down).carrier)
    (hZ : @StrictCoterminator _ (stageBundle uniformStepFun b i.down).cat Z) :
    @StrictCoterminator _ (stageBundle uniformStepFun b j.down).cat (towerF b uniformStepFun hij Z) :=
  stageCast_preservesStrictCot b (Nat.add_sub_cancel' hij)
    (transN uniformStepFun b i.down (j.down - i.down) Z)
    (transN_preservesStrictCot b i.down (j.down - i.down) Z hZ)

/-! ### §5 — the positive `CapData` reducer + the POSITIVE Capitalization Lemma -/

/-- **§1.543 reduction, POSITIVE form.**  Mirror of `capitalization_of_capData_regular_of_covers`,
    but produces a genuine `DisjointBinaryCoproduct Ā` (positive pre-logos) via the strict
    `colimitPositive`.  Beyond the regular inputs (`hi`/`hmono`/`hcovpres`) it consumes the per-stage
    disjoint coproducts `hdisj`, per-stage pre-logoi `hbot`, the strict-initial preservation
    `hinitpres`, and the coproduct transition coherence `hcoppres`/`hcoppres_case`.  The colimit's
    `RegularCategory`/`HasSubobjectUnions` are built (`colimitPreRegular`+`colimitHasImages`,
    `hasSubobjectUnions_of_coproducts_images`); `colimitPreLogos` threads that very `hReg`, so the
    `DisjointBinaryCoproduct`'s forgotten terminal is `hPre.toHasTerminal` on the nose and `cd.capital`
    lands directly.  Faithful `A → Ā = objIncl i₀ ∘ base`. -/
theorem capitalization_of_capData_positive {A : Type u} [Cat.{u} A] [PreRegularCategory A]
    (cd : CapData.{u} A)
    (hi : ∀ i, HasImages (cd.C.A i))
    (hmono : Colim.TransMono cd.C)
    (hcovpres : ∀ {i j : cd.ι} (hij : cd.D.le i j),
        @PreservesCovers _ _ (cd.C.catA i) (cd.C.catA j) (cd.C.F hij) (cd.C.functF hij))
    (hdisj : ∀ i, DisjointBinaryCoproduct (cd.C.A i))
    (hbot : ∀ i, PreLogos (cd.C.A i))
    (hinitpres : ∀ {i j : cd.ι} (hij : cd.D.le i j),
        @StrictCoterminator (cd.C.A j) (cd.C.catA j) (cd.C.F hij (Colim.stageZero cd.C hbot i)))
    (hcoppres : ∀ {i j} (hij : cd.D.le i j) (a b : cd.C.A i) (z : cd.C.A j)
        (u v : cd.C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : cd.D.le i j) (a b : cd.C.A i) (z : cd.C.A j)
        (p : cd.C.F hij a ⟶ z) (q : cd.C.F hij b ⟶ z),
        ∃ r : cd.C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hD : @DisjointBinaryCoproduct Ā hC),
      @Capital.{u, u} Ā hC (hD.toPositivePreLogos.toPreLogos.toRegularCategory.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{u, u} A _ Ā hC F hF := by
  haveI := cd.hne
  letI : Cat cd.C.Obj := colimitCat cd.C cd.hC
  letI hPre : PreRegularCategory cd.C.Obj :=
    colimitPreRegular cd.C cd.hC cd.ht cd.htpres cd.hp cd.hppres cd.hppres_pair
      cd.he cd.hepres cd.hepres_lift cd.hcanon
  -- image preservation per transition, derived from cover + mono preservation (target pullbacks).
  have himgpres : ∀ {i j : cd.ι} (hij : cd.D.le i j) {X Y : cd.C.A i} (f : X ⟶ Y),
      IsImage ((cd.C.functF hij).map f)
        (@Subobject.map _ _ (cd.C.catA i) (cd.C.catA j) (cd.C.F hij) (cd.C.functF hij)
          (hmono hij) _ (@image _ (cd.C.catA i) (hi i) _ _ f)) := by
    intro i j hij X Y f
    letI : Cat (cd.C.A i) := cd.C.catA i
    letI : Cat (cd.C.A j) := cd.C.catA j
    letI : HasImages (cd.C.A i) := hi i
    letI : HasBinaryProducts (cd.C.A j) := cd.hp j
    letI : HasEqualizers (cd.C.A j) := cd.he j
    letI : HasPullbacks (cd.C.A j) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact Colim.transitions_preserve_images (cd.C.F hij) (hF := cd.C.functF hij)
      (hmono hij) (hcovpres hij) f
  letI hImg : HasImages cd.C.Obj := Colim.colimitHasImages cd.C cd.hC hi cd.hfaith hmono himgpres
  letI hReg : RegularCategory cd.C.Obj := { hPre with toHasImages := hImg }
  letI hCop : HasBinaryCoproducts cd.C.Obj :=
    Colim.colimitCoprodOfDisjoint cd.C cd.hC hdisj hcoppres hcoppres_case
  letI hUn : HasSubobjectUnions cd.C.Obj := hasSubobjectUnions_of_coproducts_images
  letI hD : DisjointBinaryCoproduct cd.C.Obj :=
    Colim.colimitPositive cd.C cd.hC hdisj hmono hbot hinitpres cd.ht cd.htpres cd.hp cd.hppres
      cd.hppres_pair cd.he cd.hepres cd.hepres_lift hcoppres hcoppres_case hi cd.hfaith himgpres
  refine ⟨cd.C.Obj, _, hD, cd.capital, ?_⟩
  letI := cd.baseFun
  letI : @Functor (cd.C.A cd.i₀) (cd.C.catA cd.i₀) cd.C.Obj _ (cd.C.objIncl cd.i₀) :=
    stageInclFunctor cd.C cd.hC cd.i₀
  exact ⟨cd.C.objIncl cd.i₀ ∘ cd.base, inferInstance,
    faithful_comp cd.baseFaithful (stageInclFaithful cd.C cd.hC cd.hfaith cd.hcons cd.i₀)⟩

/-- **§1.54 + §2.218 R3 — the POSITIVE Capitalization Lemma.**  Every small POSITIVE pre-logos `A`
    (a `DisjointBinaryCoproduct`) admits a faithful representation into a CAPITAL, POSITIVE pre-logos
    `Ā` (again a `DisjointBinaryCoproduct`).  Same cofinal ω-tower as `capitalization_lemma_regular`,
    but the colimit is built by the strict `colimitPositive`: every stage is a disjoint binary
    coproduct (`stageDisjoint`), the coproducts are carried forward (`towerHcoppres`/`Case` from the
    iterated `uniformStep_preservesBinaryCoproducts`), and the strict initial is preserved
    (`towerF_preservesStrictCot`).  `RegularCategory Ā` comes free from the `DisjointBinaryCoproduct`. -/
theorem capitalization_lemma_regular_positive (A : Type u) [Cat.{u} A] [DisjointBinaryCoproduct A] :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hD : @DisjointBinaryCoproduct Ā hC),
      @Capital.{u, u} Ā hC (hD.toPositivePreLogos.toPreLogos.toRegularCategory.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : Functor F), @Faithful.{u, u} A _ Ā hC F hF := by
  have hFD : ∀ (S : PreRegBundle.{u}),
      letI := S.cat; letI := S.pre; letI := (wsCover S).dec
      Freyd.UniformWellPoints.FibreDensity (wsCover S) :=
    fun S => Freyd.CofinalProj.wsCover_fibreDensity S
  let ccs : CofinalCapStep.{u} :=
    { step := uniformStepFun
      wellPoints := fun S =>
        letI := S.cat; letI := S.pre; letI := (wsCover S).dec
        Freyd.UniformWellPoints.stepWellPoints_of_fibreDensity (wsCover S) (hFD S) }
  let b : PreRegBundle.{u} := ⟨A, inferInstance, inferInstance⟩
  letI cd : CapData.{u} A := capData_of_tower A ccs.step b rfl
    (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
    (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
    (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
    (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
    (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
    (towerHcanon b ccs.step)
    (tower_capital_of_cofinal A ccs b
      (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
      (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
      (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
      (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
      (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
      (towerHcanon b ccs.step)
      (hstage_of_cofinal b ccs
        (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
        (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
        (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
        (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
        (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
        (towerHcanon b ccs.step)))
  -- the per-stage disjoint coproducts and pre-logoi (`b.pre = dbcPreReg inferInstance` by `rfl`).
  letI hbot : ∀ i, PreLogos (cd.C.A i) :=
    fun i => (stageDisjoint b inferInstance rfl i.down).toPositivePreLogos.toPreLogos
  exact capitalization_of_capData_positive cd
    (fun i => stageHasImages b RegularCategory.toHasImages i.down)
    (fun {i j} hij {x y} {φ} hφ => towerHmono b ccs.step hij φ hφ)
    (fun {i j} hij {x y} φ hφ => towerHcovpres b ccs.step hij φ hφ)
    (fun i => stageDisjoint b inferInstance rfl i.down)
    hbot
    (fun {i j} hij => towerF_preservesStrictCot b hij (Colim.stageZero cd.C hbot i)
      (fun {X} f => any_map_to_zero_is_iso (hbot i) f))
    (fun {i j} hij a c z u v hl hr => towerHcoppres b inferInstance rfl hij a c z u v hl hr)
    (fun {i j} hij a c z p q => towerHcoppresCase b inferInstance rfl hij a c z p q)

/-- **§1.54 + §2.218 R3 — the STRENGTHENED POSITIVE Capitalization Lemma.**  Same conclusion as
    `capitalization_lemma_regular_positive` (a faithful embedding into a capital positive pre-logos
    `Ā`), but the embedding `F` is ALSO a `RegularFunctor` (w.r.t. the positivity-derived regular
    structures on `A` and `Ā`) and REFLECTS ALL ISOS.  This is the form §2.218's stalk route
    consumes: `Rel(Tstar ∘ F)` is then faithful (`F` reflects isos, `Tstar` reflects isos, and
    power-covers split in `Set^I`).

    `F = objIncl ⟨0⟩` (stage 0 of the §1.543 ω-tower is `A`, so `base = id`).  Its five
    `RegularFunctor` fields are the colimit-stage-inclusion preservation lemmas
    (`objIncl_preservesBinaryProducts`, `objIncl_preservesPullbacks_generic`, `objIncl_preservesCover`,
    `objIncl_preservesMono`, `objIncl_preservesImages_generic`) against the IN-SCOPE colimit regular
    structure `hReg`, which is exactly `hD.toPositivePreLogos.toPreLogos.toRegularCategory` (the
    `DisjointBinaryCoproduct` threads `hReg` verbatim through `colimitPreLogos`); the source products
    `cd.hp ⟨0⟩` are `A`'s positivity-derived products on the nose.  Iso-reflection is
    `objIncl_reflectsIso` fed the tower's conservativity `cd.hcons`. -/
theorem capitalization_lemma_regular_positive_strong (A : Type u) [Cat.{u} A]
    [DisjointBinaryCoproduct A] :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hD : @DisjointBinaryCoproduct Ā hC),
      @Capital.{u, u} Ā hC (hD.toPositivePreLogos.toPreLogos.toRegularCategory.toHasTerminal) ∧
      ∃ (F : A → Ā) (hF : @Functor A _ Ā hC F),
        @Faithful.{u, u} A _ Ā hC F hF ∧
        @RelFunctor.RegularFunctor A Ā _ hC F hF
            (DisjointBinaryCoproduct.toPositivePreLogos.toPreLogos.toRegularCategory)
            (hD.toPositivePreLogos.toPreLogos.toRegularCategory) ∧
        ∀ {X Y : A} (f : X ⟶ Y), @IsIso Ā hC _ _ (hF.map f) → IsIso f := by
  -- ===== build the cofinal ω-tower CapData (identical to `capitalization_lemma_regular_positive`) =====
  have hFD : ∀ (S : PreRegBundle.{u}),
      letI := S.cat; letI := S.pre; letI := (wsCover S).dec
      Freyd.UniformWellPoints.FibreDensity (wsCover S) :=
    fun S => Freyd.CofinalProj.wsCover_fibreDensity S
  let ccs : CofinalCapStep.{u} :=
    { step := uniformStepFun
      wellPoints := fun S =>
        letI := S.cat; letI := S.pre; letI := (wsCover S).dec
        Freyd.UniformWellPoints.stepWellPoints_of_fibreDensity (wsCover S) (hFD S) }
  let b : PreRegBundle.{u} := ⟨A, inferInstance, inferInstance⟩
  letI cd : CapData.{u} A := capData_of_tower A ccs.step b rfl
    (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
    (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
    (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
    (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
    (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
    (towerHcanon b ccs.step)
    (tower_capital_of_cofinal A ccs b
      (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
      (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
      (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
      (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
      (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
      (towerHcanon b ccs.step)
      (hstage_of_cofinal b ccs
        (towerHasTerminal b ccs.step) (fun {i j} hij => towerHtpres b ccs.step hij) (towerHp b ccs.step)
        (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
        (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q) (towerHe b ccs.step)
        (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
        (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
        (towerHcanon b ccs.step)))
  -- per-stage positivity data and regularity inputs (the same the existing proof feeds the reducer)
  letI hbot : ∀ i, PreLogos (cd.C.A i) :=
    fun i => (stageDisjoint b inferInstance rfl i.down).toPositivePreLogos.toPreLogos
  let hi : ∀ i, HasImages (cd.C.A i) := fun i => stageHasImages b RegularCategory.toHasImages i.down
  let hdisj : ∀ i, DisjointBinaryCoproduct (cd.C.A i) :=
    fun i => stageDisjoint b inferInstance rfl i.down
  let hmonoTrans : Colim.TransMono cd.C :=
    fun {i j} hij {x y} {φ} hφ => towerHmono b ccs.step hij φ hφ
  let hmonoElem : ∀ {i j : cd.ι} (hij : cd.D.le i j) {x y : cd.C.A i} (φ : x ⟶ y),
      Monic φ → Monic ((cd.C.functF hij).map φ) :=
    fun {i j} hij {x y} φ hφ => towerHmono b ccs.step hij φ hφ
  let hcovpresElem : ∀ {i j : cd.ι} (hij : cd.D.le i j) {x y : cd.C.A i} (φ : x ⟶ y),
      Cover φ → Cover ((cd.C.functF hij).map φ) :=
    fun {i j} hij {x y} φ hφ => towerHcovpres b ccs.step hij φ hφ
  let hcoppres : ∀ {i j : cd.ι} (hij : cd.D.le i j) (a c : cd.C.A i) (z : cd.C.A j)
      (u v : cd.C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a c) ⟶ z),
      (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
          = (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
      (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
          = (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v :=
    fun {i j} hij a c z u v hl hr => towerHcoppres b inferInstance rfl hij a c z u v hl hr
  let hcoppres_case : ∀ {i j : cd.ι} (hij : cd.D.le i j) (a c : cd.C.A i) (z : cd.C.A j)
      (p : cd.C.F hij a ⟶ z) (q : cd.C.F hij c ⟶ z),
      ∃ r : cd.C.F hij ((hdisj i).toHasBinaryCoproducts.coprod a c) ⟶ z,
        (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
        ∧ (cd.C.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q :=
    fun {i j} hij a c z p q => towerHcoppresCase b inferInstance rfl hij a c z p q
  let hinitpres : ∀ {i j : cd.ι} (hij : cd.D.le i j),
      @StrictCoterminator (cd.C.A j) (cd.C.catA j) (cd.C.F hij (Colim.stageZero cd.C hbot i)) :=
    fun {i j} hij => towerF_preservesStrictCot b hij (Colim.stageZero cd.C hbot i)
      (fun {X} f => any_map_to_zero_is_iso (hbot i) f)
  -- ===== inline `capitalization_of_capData_positive` to expose `hReg`/`hD` transparently =====
  haveI := cd.hne
  letI : Cat cd.C.Obj := colimitCat cd.C cd.hC
  letI hPre : PreRegularCategory cd.C.Obj :=
    colimitPreRegular cd.C cd.hC cd.ht cd.htpres cd.hp cd.hppres cd.hppres_pair
      cd.he cd.hepres cd.hepres_lift cd.hcanon
  have himgpres : ∀ {i j : cd.ι} (hij : cd.D.le i j) {X Y : cd.C.A i} (f : X ⟶ Y),
      IsImage ((cd.C.functF hij).map f)
        (@Subobject.map _ _ (cd.C.catA i) (cd.C.catA j) (cd.C.F hij) (cd.C.functF hij)
          (hmonoTrans hij) _ (@image _ (cd.C.catA i) (hi i) _ _ f)) := by
    intro i j hij X Y f
    letI : Cat (cd.C.A i) := cd.C.catA i
    letI : Cat (cd.C.A j) := cd.C.catA j
    letI : HasImages (cd.C.A i) := hi i
    letI : HasBinaryProducts (cd.C.A j) := cd.hp j
    letI : HasEqualizers (cd.C.A j) := cd.he j
    letI : HasPullbacks (cd.C.A j) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact Colim.transitions_preserve_images (cd.C.F hij) (hF := cd.C.functF hij)
      (hmonoTrans hij) (hcovpresElem hij ·) f
  letI hImg : HasImages cd.C.Obj :=
    Colim.colimitHasImages cd.C cd.hC hi cd.hfaith hmonoTrans himgpres
  letI hReg : RegularCategory cd.C.Obj := { hPre with toHasImages := hImg }
  letI hCop : HasBinaryCoproducts cd.C.Obj :=
    Colim.colimitCoprodOfDisjoint cd.C cd.hC hdisj hcoppres hcoppres_case
  letI hUn : HasSubobjectUnions cd.C.Obj := hasSubobjectUnions_of_coproducts_images
  letI hD : DisjointBinaryCoproduct cd.C.Obj :=
    Colim.colimitPositive cd.C cd.hC hdisj hmonoTrans hbot hinitpres cd.ht cd.htpres cd.hp cd.hppres
      cd.hppres_pair cd.he cd.hepres cd.hepres_lift hcoppres hcoppres_case hi cd.hfaith himgpres
  -- ===== assemble: `F = objIncl ⟨0⟩` is faithful, regular, and reflects all isos =====
  letI : @Functor (cd.C.A cd.i₀) (cd.C.catA cd.i₀) cd.C.Obj _ (cd.C.objIncl cd.i₀) :=
    stageInclFunctor cd.C cd.hC cd.i₀
  refine ⟨cd.C.Obj, _, hD, cd.capital, cd.C.objIncl cd.i₀, inferInstance,
    stageInclFaithful cd.C cd.hC cd.hfaith cd.hcons cd.i₀, ?_, ?_⟩
  · -- `objIncl ⟨0⟩` is a `RegularFunctor` against `hReg = hD.…toRegularCategory`.
    exact
      { pres_prod := objIncl_preservesBinaryProducts cd.C cd.hC cd.hp cd.hppres cd.hppres_pair cd.i₀
        pres_pullback := objIncl_preservesPullbacks_generic cd.C cd.hC cd.ht cd.htpres cd.hp
          cd.hppres cd.hppres_pair cd.he cd.hepres cd.hepres_lift cd.i₀
        pres_covers := fun {_ _} φ hφ =>
          objIncl_preservesCover cd.C cd.hC cd.hfaith hcovpresElem (i := cd.i₀) φ hφ
        pres_mono := objIncl_preservesMono cd.C cd.hC hmonoElem cd.i₀
        pres_image := objIncl_preservesImages_generic cd.C cd.hC cd.hfaith hcovpresElem hmonoElem cd.i₀ }
  · -- `objIncl ⟨0⟩` reflects all isos (full conservativity `cd.hcons`).
    exact fun {X Y} f hiso => objIncl_reflectsIso cd.C cd.hC cd.hcons cd.i₀ f hiso

end Freyd

#print axioms Freyd.capitalization_lemma_regular_positive
#print axioms Freyd.capitalization_lemma_regular_positive_strong
