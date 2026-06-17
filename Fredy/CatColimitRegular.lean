/-
  M3a — terminal object of the colimit category.

  If each stage `C.A i` has a terminal and the transitions preserve it, then the
  colimit category `C.Obj` has a terminal object.
-/

import Fredy.CatColimit
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_51
import Fredy.S1_52
open Freyd
namespace Freyd.Colim
universe u w
variable {ι : Type u} {D : Directed ι}

noncomputable def colimitHasTerminal (C : CatSystem ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one) :
    @HasTerminal C.Obj (colimitCat C hC) := by
  let i₀ : ι := Classical.choice hne
  let one : C.Obj := C.objIncl i₀ (ht i₀).one
  let io := (colimOut C one).1
  let o := (colimOut C one).2
  have hOneSpec : C.objIncl io o = one := colimOut_spec C one
  have hOneRel : Rel C.objSystem ⟨io, o⟩ ⟨i₀, (ht i₀).one⟩ :=
    Quotient.exact hOneSpec
  -- Eliminate ∃ from hOneRel via Classical.choose (goal is Type, not Prop)
  let k₀ := Classical.choose hOneRel
  have h_spec1 : ∃ (hik : D.le io k₀) (hjk : D.le i₀ k₀), C.F hik o = C.F hjk (ht i₀).one :=
    Classical.choose_spec hOneRel
  let h_io_k₀ := Classical.choose h_spec1
  have h_spec2 : ∃ (hjk : D.le i₀ k₀), C.F h_io_k₀ o = C.F hjk (ht i₀).one :=
    Classical.choose_spec h_spec1
  let h_i₀_k₀ := Classical.choose h_spec2
  have h_obj_eq : C.F h_io_k₀ o = C.F h_i₀_k₀ (ht i₀).one :=
    Classical.choose_spec h_spec2
  have ho_is_term : C.F h_io_k₀ o = (ht k₀).one := by
    rw [h_obj_eq, hpres h_i₀_k₀]
  refine @HasTerminal.mk C.Obj (colimitCat C hC) one ?_ ?_
  · -- trm: (X : C.Obj) → colimHom C hC X one
    intro X
    let jX := (colimOut C X).1
    let xX := (colimOut C X).2
    -- D.bound is ∃; Classical.choose since trm returns Type
    let bd := D.bound jX k₀
    let k := Classical.choose bd
    have hbd_spec : D.le jX k ∧ D.le k₀ k := Classical.choose_spec bd
    have h_jX_k : D.le jX k := hbd_spec.1
    have h_k₀_k : D.le k₀ k := hbd_spec.2
    have h_io_k : D.le io k := D.trans h_io_k₀ h_k₀_k
    have hok : C.F h_io_k o = (ht k).one := by
      calc
        C.F h_io_k o = C.F (D.trans h_io_k₀ h_k₀_k) o := rfl
        _ = C.F h_k₀_k (C.F h_io_k₀ o) := by rw [C.F_trans]
        _ = C.F h_k₀_k ((ht k₀).one) := by rw [ho_is_term]
        _ = (ht k).one := hpres h_k₀_k
    let m : C.F h_jX_k xX ⟶ C.F h_io_k o :=
      castHom rfl hok.symm ((ht k).trm (C.F h_jX_k xX))
    exact homIncl C hC xX o ⟨k, h_jX_k, h_io_k⟩ m
  · -- uniq: ∀ {X} (f g : colimHom C hC X one), f = g
    intro X f g
    let jX := (colimOut C X).1
    let xX := (colimOut C X).2
    refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
    apply Quotient.sound
    -- pick k' ≥ a.1, b.1, k₀
    obtain ⟨m, ham, hbm⟩ := D.bound a.1 b.1
    obtain ⟨k', hmk', hk₀k'⟩ := D.bound m k₀
    let hak' : D.le a.1 k' := D.trans ham hmk'
    let hbk' : D.le b.1 k' := D.trans hbm hmk'
    let hiok' : D.le io k' := D.trans h_io_k₀ hk₀k'
    have h_jX_k' : D.le jX k' := D.trans a.2.1 hak'
    let ub : UpperBound D jX io := ⟨k', h_jX_k', hiok'⟩
    let fa' : C.F ub.2.1 xX ⟶ C.F ub.2.2 o := homTr C xX o a ub hak' fa
    let gb' : C.F ub.2.1 xX ⟶ C.F ub.2.2 o := homTr C xX o b ub hbk' gb
    -- o at level k' becomes the terminal (ht k').one
    have hok' : C.F hiok' o = (ht k').one := by
      calc
        C.F hiok' o = C.F (D.trans h_io_k₀ hk₀k') o := rfl
        _ = C.F hk₀k' (C.F h_io_k₀ o) := by rw [C.F_trans]
        _ = C.F hk₀k' ((ht k₀).one) := by rw [ho_is_term]
        _ = (ht k').one := hpres hk₀k'
    have hL'R' : castHom rfl hok' fa' = castHom rfl hok' gb' :=
      (ht k').uniq (castHom rfl hok' fa') (castHom rfl hok' gb')
    -- Strip the cast via Eq.rec on hok'
    have h_eq : fa' = gb' :=
      Eq.rec (motive := λ T (h : C.F hiok' o = T) =>
        ∀ (f g : C.F ub.2.1 xX ⟶ C.F hiok' o), castHom rfl h f = castHom rfl h g → f = g)
        (λ f g h_eq_cast => by simpa [castHom] using h_eq_cast)
        hok' fa' gb' hL'R'
    exact ⟨ub, hak', hbk', h_eq⟩

/-!
  M3b — binary products of the colimit category.

  If each stage `C.A i` has binary products and the transitions preserve them
  (cast-free: the image of a stage product cone is again a product), the
  colimit category `C.Obj` has binary products.
-/

noncomputable def colimitHasBinaryProducts (C : CatSystem ι D) (hC : C.Coherent)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q) :
    @HasBinaryProducts C.Obj (colimitCat C hC) := by
  -- Helper: proof irrelevance for D.le (a Prop)
  have hDirSubsingleton : ∀ {i j : ι} (h h' : D.le i j), h = h' := by
    intro i j h h'; exact Subsingleton.elim h h'
  -- Helper: C.F respects proof irrelevance
  have hF_proof_irrel : ∀ {i j : ι} (h h' : D.le i j) (a : C.A i), C.F h a = C.F h' a := by
    intro i j h h' a; rw [hDirSubsingleton h h']
  -- Shared data parameterized by (A, B): ensures fst, snd, pair all use the same product stage.
  let iObj (A : C.Obj) : ι := (colimOut C A).1
  let xObj (A : C.Obj) : C.A (iObj A) := (colimOut C A).2
  let k (A B : C.Obj) : ι := Classical.choose (D.bound (iObj A) (iObj B))
  have hbd (A B : C.Obj) : D.le (iObj A) (k A B) ∧ D.le (iObj B) (k A B) :=
    Classical.choose_spec (D.bound (iObj A) (iObj B))
  let hA_k (A B : C.Obj) : D.le (iObj A) (k A B) := (hbd A B).1
  let hB_k (A B : C.Obj) : D.le (iObj B) (k A B) := (hbd A B).2
  let ak (A B : C.Obj) : C.A (k A B) := C.F (hA_k A B) (xObj A)
  let bk (A B : C.Obj) : C.A (k A B) := C.F (hB_k A B) (xObj B)
  -- Product object (uses shared k)
  let prodFun (X Y : C.Obj) : C.Obj :=
    C.objIncl (k X Y) ((hp (k X Y)).prod (ak X Y) (bk X Y))
  -- Representative of the product object
  let ip (A B : C.Obj) : ι := (colimOut C (prodFun A B)).1
  let op (A B : C.Obj) : C.A (ip A B) := (colimOut C (prodFun A B)).2
  have hProdSpec (A B : C.Obj) : C.objIncl (ip A B) (op A B) = prodFun A B :=
    colimOut_spec C (prodFun A B)
  have hProdRel (A B : C.Obj) : Rel C.objSystem ⟨ip A B, op A B⟩
      ⟨k A B, (hp (k A B)).prod (ak A B) (bk A B)⟩ :=
    Quotient.exact (hProdSpec A B)
  let kp (A B : C.Obj) : ι := Classical.choose (hProdRel A B)
  have h_kp_spec1 (A B : C.Obj) : ∃ (hik : D.le (ip A B) (kp A B)) (hjk : D.le (k A B) (kp A B)),
      C.F hik (op A B) = C.F hjk ((hp (k A B)).prod (ak A B) (bk A B)) :=
    Classical.choose_spec (hProdRel A B)
  let h_ip_kp (A B : C.Obj) : D.le (ip A B) (kp A B) := Classical.choose (h_kp_spec1 A B)
  have h_kp_spec2 (A B : C.Obj) : ∃ (hjk : D.le (k A B) (kp A B)),
      C.F (h_ip_kp A B) (op A B) = C.F hjk ((hp (k A B)).prod (ak A B) (bk A B)) :=
    Classical.choose_spec (h_kp_spec1 A B)
  let h_k_kp (A B : C.Obj) : D.le (k A B) (kp A B) := Classical.choose (h_kp_spec2 A B)
  have h_prod_eq (A B : C.Obj) : C.F (h_ip_kp A B) (op A B) = C.F (h_k_kp A B) ((hp (k A B)).prod (ak A B) (bk A B)) :=
    Classical.choose_spec (h_kp_spec2 A B)
  -- fst and snd as let definitions (unfoldable in law proofs)
  let fst {A B : C.Obj} : colimHom C hC (prodFun A B) A :=
    homIncl C hC (op A B) (xObj A) ⟨kp A B, h_ip_kp A B, D.trans (hA_k A B) (h_k_kp A B)⟩
      (castHom (h_prod_eq A B).symm
        (calc
          C.F (h_k_kp A B) (ak A B) = C.F (h_k_kp A B) (C.F (hA_k A B) (xObj A)) := rfl
          _ = C.F (D.trans (hA_k A B) (h_k_kp A B)) (xObj A) := by rw [C.F_trans (hA_k A B) (h_k_kp A B) (xObj A)])
        ((C.functF (h_k_kp A B)).map ((hp (k A B)).fst (A:=ak A B) (B:=bk A B))))
  let snd {A B : C.Obj} : colimHom C hC (prodFun A B) B :=
    homIncl C hC (op A B) (xObj B) ⟨kp A B, h_ip_kp A B, D.trans (hB_k A B) (h_k_kp A B)⟩
      (castHom (h_prod_eq A B).symm
        (calc
          C.F (h_k_kp A B) (bk A B) = C.F (h_k_kp A B) (C.F (hB_k A B) (xObj B)) := rfl
          _ = C.F (D.trans (hB_k A B) (h_k_kp A B)) (xObj B) := by rw [C.F_trans (hB_k A B) (h_k_kp A B) (xObj B)])
        ((C.functF (h_k_kp A B)).map ((hp (k A B)).snd (A:=ak A B) (B:=bk A B))))
  -- Existence of a mediating morphism for any f, g (used to define pair via choice)
  have h_exists_pair (Z X Y : C.Obj) (f : colimHom C hC Z X) (g : colimHom C hC Z Y) :
      ∃ h : colimHom C hC Z (prodFun X Y),
        colimComp C hC h (fst (A:=X) (B:=Y)) = f ∧ colimComp C hC h (snd (A:=X) (B:=Y)) = g := by
    -- Eliminate quotients on f and g
    refine Quotient.inductionOn f (fun ⟨af, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨ag, ga⟩ => ?_)
    -- Now f = mk ⟨af, fa⟩ and g = mk ⟨ag, ga⟩
    -- Build h using the shared data
    let iZ := iObj Z; let z := xObj Z
    let iX := iObj X; let iY := iObj Y
    let k0 := k X Y; let kp0 := kp X Y
    let ip0 := ip X Y; let op0 := op X Y
    let h_ip_kp0 := h_ip_kp X Y; let h_k_kp0 := h_k_kp X Y
    let h_prod_eq0 := h_prod_eq X Y
    -- Pick M ≥ af.1, ag.1, kp0
    obtain ⟨m, ham, hbm⟩ := D.bound af.1 ag.1
    obtain ⟨M, hmM, hkpM⟩ := D.bound m kp0
    let haM : D.le af.1 M := D.trans ham hmM
    let hbM : D.le ag.1 M := D.trans hbm hmM
    let h_k_M : D.le k0 M := D.trans h_k_kp0 hkpM
    let h_ip_M : D.le ip0 M := D.trans h_ip_kp0 hkpM
    let h_iZ_M : D.le iZ M := D.trans af.2.1 haM
    let h_iX_M : D.le iX M := D.trans (hA_k X Y) h_k_M
    let h_iY_M : D.le iY M := D.trans (hB_k X Y) h_k_M
    -- Transport fa and gb to level M
    let ub_a_M : UpperBound D iZ iX := ⟨M, h_iZ_M, D.trans af.2.2 haM⟩
    let ub_b_M : UpperBound D iZ iY := ⟨M, D.trans ag.2.1 hbM, D.trans ag.2.2 hbM⟩
    let fa_M_raw : C.F h_iZ_M z ⟶ C.F (D.trans af.2.2 haM) (xObj X) := homTr C z (xObj X) af ub_a_M haM fa
    let gb_M_raw : C.F (D.trans ag.2.1 hbM) z ⟶ C.F (D.trans ag.2.2 hbM) (xObj Y) :=
      homTr C z (xObj Y) ag ub_b_M hbM ga
    have h_fa_tgt : C.F (D.trans af.2.2 haM) (xObj X) = C.F h_iX_M (xObj X) :=
      hF_proof_irrel (D.trans af.2.2 haM) h_iX_M (xObj X)
    have h_gb_tgt : C.F (D.trans ag.2.2 hbM) (xObj Y) = C.F h_iY_M (xObj Y) :=
      hF_proof_irrel (D.trans ag.2.2 hbM) h_iY_M (xObj Y)
    have h_gb_src : C.F (D.trans ag.2.1 hbM) z = C.F h_iZ_M z :=
      hF_proof_irrel (D.trans ag.2.1 hbM) h_iZ_M z
    let fa_M : C.F h_iZ_M z ⟶ C.F h_iX_M (xObj X) := castHom rfl h_fa_tgt fa_M_raw
    let gb_M : C.F h_iZ_M z ⟶ C.F h_iY_M (xObj Y) := castHom h_gb_src h_gb_tgt gb_M_raw
    have h_fa_to_ak : C.F h_iX_M (xObj X) = C.F h_k_M (ak X Y) := by
      calc
        C.F h_iX_M (xObj X) = C.F (D.trans (hA_k X Y) h_k_M) (xObj X) := rfl
        _ = C.F h_k_M (C.F (hA_k X Y) (xObj X)) := by rw [C.F_trans (hA_k X Y) h_k_M (xObj X)]
        _ = C.F h_k_M (ak X Y) := rfl
    have h_gb_to_bk : C.F h_iY_M (xObj Y) = C.F h_k_M (bk X Y) := by
      calc
        C.F h_iY_M (xObj Y) = C.F (D.trans (hB_k X Y) h_k_M) (xObj Y) := rfl
        _ = C.F h_k_M (C.F (hB_k X Y) (xObj Y)) := by rw [C.F_trans (hB_k X Y) h_k_M (xObj Y)]
        _ = C.F h_k_M (bk X Y) := rfl
    let p_pair : C.F h_iZ_M z ⟶ C.F h_k_M (ak X Y) := castHom rfl h_fa_to_ak fa_M
    let q_pair : C.F h_iZ_M z ⟶ C.F h_k_M (bk X Y) := castHom rfl h_gb_to_bk gb_M
    obtain ⟨r, hr_fst, hr_snd⟩ := hpres_pair h_k_M (ak X Y) (bk X Y) (C.F h_iZ_M z) p_pair q_pair
    have h_prod_eq_M : C.F h_ip_M op0 = C.F h_k_M ((hp k0).prod (ak X Y) (bk X Y)) := by
      calc
        C.F h_ip_M op0 = C.F (D.trans h_ip_kp0 hkpM) op0 := rfl
        _ = C.F hkpM (C.F h_ip_kp0 op0) := by rw [C.F_trans h_ip_kp0 hkpM op0]
        _ = C.F hkpM (C.F h_k_kp0 ((hp k0).prod (ak X Y) (bk X Y))) := by rw [h_prod_eq0]
        _ = C.F (D.trans h_k_kp0 hkpM) ((hp k0).prod (ak X Y) (bk X Y)) := by
          rw [C.F_trans h_k_kp0 hkpM ((hp k0).prod (ak X Y) (bk X Y))]
        _ = C.F h_k_M ((hp k0).prod (ak X Y) (bk X Y)) := rfl
    let r' : C.F h_iZ_M z ⟶ C.F h_ip_M op0 := castHom rfl h_prod_eq_M.symm r
    let ub_pair : UpperBound D iZ ip0 := ⟨M, h_iZ_M, h_ip_M⟩
    let h := homIncl C hC z op0 ub_pair r'
    -- Define ub_fst and m_fst explicitly so we can work with them
    let ub_fst : UpperBound D ip0 (iObj X) := ⟨kp0, h_ip_kp0, D.trans (hA_k X Y) h_k_kp0⟩
    let m_fst : C.F h_ip_kp0 op0 ⟶ C.F (D.trans (hA_k X Y) h_k_kp0) (xObj X) :=
      castHom h_prod_eq0.symm
        (calc
          C.F h_k_kp0 (ak X Y) = C.F h_k_kp0 (C.F (hA_k X Y) (xObj X)) := rfl
          _ = C.F (D.trans (hA_k X Y) h_k_kp0) (xObj X) := by rw [C.F_trans (hA_k X Y) h_k_kp0 (xObj X)])
        ((C.functF h_k_kp0).map ((hp k0).fst (A:=ak X Y) (B:=bk X Y)))
    have h_fst_eq : fst (A:=X) (B:=Y) = homIncl C hC op0 (xObj X) ub_fst m_fst := rfl
    have h_fst_ok : colimComp C hC h (fst (A:=X) (B:=Y)) = Quotient.mk (setoid (homSystem C hC z (xObj X))) ⟨af, fa⟩ := by
      show homCompRaw C hC z op0 (xObj X) ub_pair r' ub_fst m_fst = homIncl C hC z (xObj X) af fa
      refine homCompRaw_eq_of_stage C hC z op0 (xObj X) ub_pair r' ub_fst m_fst af fa M
        (D.refl M) hkpM haM ?_
      -- hstage: homTr(r', refl M) ≫ homTr(m_fst, hkpM) = homTr(fa, haM), all at level M
      have h1 : homTr C z op0 ub_pair ⟨M, D.trans ub_pair.2.1 (D.refl M), D.trans ub_pair.2.2 (D.refl M)⟩ (D.refl M) r' = r' := by
        simpa [ub_pair] using homTr_refl C hC z op0 ⟨M, D.trans ub_pair.2.1 (D.refl M), D.trans ub_pair.2.2 (D.refl M)⟩ r'
      rw [h1]
      have h_mfst_push : homTr C op0 (xObj X) ub_fst ⟨M, D.trans ub_fst.2.1 hkpM, D.trans ub_fst.2.2 hkpM⟩ hkpM m_fst
          = castHom (h_prod_eq_M.symm) (h_fa_to_ak.symm.trans (hF_proof_irrel _ _ _))
              ((C.functF h_k_M).map ((hp k0).fst (A:=ak X Y) (B:=bk X Y))) := by
        dsimp [homTr, m_fst]
        rw [map_castHom (C.F hkpM) (hT := C.functF hkpM), castHom_castHom]
        exact castHom_heq_congr _ _ _ _
          (hC.trans_map h_k_kp0 hkpM ((hp k0).fst (A:=ak X Y) (B:=bk X Y))).symm
      rw [h_mfst_push]
      dsimp [r']
      rw [castHom_comp]
      rw [hr_fst]
      dsimp [p_pair, fa_M, fa_M_raw, ub_a_M]
      unfold homTr
      simp only [castHom_castHom]
    -- snd proof is symmetric
    have h_snd_ok : colimComp C hC h (snd (A:=X) (B:=Y)) = Quotient.mk (setoid (homSystem C hC z (xObj Y))) ⟨ag, ga⟩ := by
      let ub_snd : UpperBound D ip0 (iObj Y) := ⟨kp0, h_ip_kp0, D.trans (hB_k X Y) h_k_kp0⟩
      let m_snd : C.F h_ip_kp0 op0 ⟶ C.F (D.trans (hB_k X Y) h_k_kp0) (xObj Y) :=
        castHom h_prod_eq0.symm
          (calc
            C.F h_k_kp0 (bk X Y) = C.F h_k_kp0 (C.F (hB_k X Y) (xObj Y)) := rfl
            _ = C.F (D.trans (hB_k X Y) h_k_kp0) (xObj Y) := by rw [C.F_trans (hB_k X Y) h_k_kp0 (xObj Y)])
          ((C.functF h_k_kp0).map ((hp k0).snd (A:=ak X Y) (B:=bk X Y)))
      show homCompRaw C hC z op0 (xObj Y) ub_pair r' ub_snd m_snd = homIncl C hC z (xObj Y) ag ga
      refine homCompRaw_eq_of_stage C hC z op0 (xObj Y) ub_pair r' ub_snd m_snd ag ga M
        (D.refl M) hkpM hbM ?_
      have h1 : homTr C z op0 ub_pair ⟨M, D.trans ub_pair.2.1 (D.refl M), D.trans ub_pair.2.2 (D.refl M)⟩ (D.refl M) r' = r' := by
        simpa [ub_pair] using homTr_refl C hC z op0 ⟨M, D.trans ub_pair.2.1 (D.refl M), D.trans ub_pair.2.2 (D.refl M)⟩ r'
      rw [h1]
      have h_msnd_push : homTr C op0 (xObj Y) ub_snd ⟨M, D.trans ub_snd.2.1 hkpM, D.trans ub_snd.2.2 hkpM⟩ hkpM m_snd
          = castHom (h_prod_eq_M.symm) (h_gb_to_bk.symm.trans (hF_proof_irrel _ _ _))
              ((C.functF h_k_M).map ((hp k0).snd (A:=ak X Y) (B:=bk X Y))) := by
        dsimp [homTr, m_snd]
        rw [map_castHom (C.F hkpM) (hT := C.functF hkpM), castHom_castHom]
        exact castHom_heq_congr _ _ _ _
          (hC.trans_map h_k_kp0 hkpM ((hp k0).snd (A:=ak X Y) (B:=bk X Y))).symm
      rw [h_msnd_push]
      dsimp [r']
      rw [castHom_comp]
      rw [hr_snd]
      dsimp [q_pair, gb_M, gb_M_raw, ub_b_M]
      unfold homTr
      simp only [castHom_castHom]
    exact ⟨h, h_fst_ok, h_snd_ok⟩
  -- Define pair via Classical.choice on h_exists_pair
  let pair {X A B : C.Obj} (f : colimHom C hC X A) (g : colimHom C hC X B) : colimHom C hC X (prodFun A B) :=
    Classical.choose (h_exists_pair X A B f g)
  have h_fst_pair : ∀ {Z X Y : C.Obj} (f : colimHom C hC Z X) (g : colimHom C hC Z Y),
      colimComp C hC (pair f g) (fst (A:=X) (B:=Y)) = f := by
    intro Z X Y f g; exact (Classical.choose_spec (h_exists_pair Z X Y f g)).1
  have h_snd_pair : ∀ {Z X Y : C.Obj} (f : colimHom C hC Z X) (g : colimHom C hC Z Y),
      colimComp C hC (pair f g) (snd (A:=X) (B:=Y)) = g := by
    intro Z X Y f g; exact (Classical.choose_spec (h_exists_pair Z X Y f g)).2
  have h_pair_uniq : ∀ {Z X Y : C.Obj} (f : colimHom C hC Z X) (g : colimHom C hC Z Y)
      (h : colimHom C hC Z (prodFun X Y)),
      colimComp C hC h (fst (A:=X) (B:=Y)) = f → colimComp C hC h (snd (A:=X) (B:=Y)) = g → h = pair f g := by
    intro Z X Y f g h h_hfst h_hsnd
    have e1 : colimComp C hC h (fst (A:=X) (B:=Y)) = colimComp C hC (pair f g) (fst (A:=X) (B:=Y)) := by
      rw [h_hfst, h_fst_pair]
    have e2 : colimComp C hC h (snd (A:=X) (B:=Y)) = colimComp C hC (pair f g) (snd (A:=X) (B:=Y)) := by
      rw [h_hsnd, h_snd_pair]
    revert e1 e2
    refine Quotient.inductionOn₂ h (pair f g) ?_
    rintro ⟨ah, mha⟩ ⟨ap, mpa⟩ e1 e2
    -- projection germs (defeq to `fst`/`snd`)
    let ub_fstg : UpperBound D (ip X Y) (iObj X) := ⟨kp X Y, h_ip_kp X Y, D.trans (hA_k X Y) (h_k_kp X Y)⟩
    let m_fstg : C.F (h_ip_kp X Y) (op X Y) ⟶ C.F (D.trans (hA_k X Y) (h_k_kp X Y)) (xObj X) :=
      castHom (h_prod_eq X Y).symm
        (calc C.F (h_k_kp X Y) (ak X Y) = C.F (h_k_kp X Y) (C.F (hA_k X Y) (xObj X)) := rfl
          _ = C.F (D.trans (hA_k X Y) (h_k_kp X Y)) (xObj X) := by rw [C.F_trans (hA_k X Y) (h_k_kp X Y) (xObj X)])
        ((C.functF (h_k_kp X Y)).map ((hp (k X Y)).fst (A:=ak X Y) (B:=bk X Y)))
    let ub_sndg : UpperBound D (ip X Y) (iObj Y) := ⟨kp X Y, h_ip_kp X Y, D.trans (hB_k X Y) (h_k_kp X Y)⟩
    let m_sndg : C.F (h_ip_kp X Y) (op X Y) ⟶ C.F (D.trans (hB_k X Y) (h_k_kp X Y)) (xObj Y) :=
      castHom (h_prod_eq X Y).symm
        (calc C.F (h_k_kp X Y) (bk X Y) = C.F (h_k_kp X Y) (C.F (hB_k X Y) (xObj Y)) := rfl
          _ = C.F (D.trans (hB_k X Y) (h_k_kp X Y)) (xObj Y) := by rw [C.F_trans (hB_k X Y) (h_k_kp X Y) (xObj Y)])
        ((C.functF (h_k_kp X Y)).map ((hp (k X Y)).snd (A:=ak X Y) (B:=bk X Y)))
    have er1 : homCompRaw C hC (colimOut C Z).2 (op X Y) (xObj X) ah mha ub_fstg m_fstg
             = homCompRaw C hC (colimOut C Z).2 (op X Y) (xObj X) ap mpa ub_fstg m_fstg := e1
    have er2 : homCompRaw C hC (colimOut C Z).2 (op X Y) (xObj Y) ah mha ub_sndg m_sndg
             = homCompRaw C hC (colimOut C Z).2 (op X Y) (xObj Y) ap mpa ub_sndg m_sndg := e2
    -- common level L0 ≥ ah.1, ap.1, kp X Y; rewrite both composites as `compAt` at L0
    obtain ⟨w, hw_a, hw_p⟩ := D.bound ah.1 ap.1
    obtain ⟨L0, hL0_w, hL0_kp⟩ := D.bound w (kp X Y)
    have ha_L0 : D.le ah.1 L0 := D.trans hw_a hL0_w
    have hp_L0 : D.le ap.1 L0 := D.trans hw_p hL0_w
    rw [homCompRaw_eq_compAt C hC (colimOut C Z).2 (op X Y) (xObj X) ah mha ub_fstg m_fstg L0 ha_L0 hL0_kp,
        homCompRaw_eq_compAt C hC (colimOut C Z).2 (op X Y) (xObj X) ap mpa ub_fstg m_fstg L0 hp_L0 hL0_kp] at er1
    rw [homCompRaw_eq_compAt C hC (colimOut C Z).2 (op X Y) (xObj Y) ah mha ub_sndg m_sndg L0 ha_L0 hL0_kp,
        homCompRaw_eq_compAt C hC (colimOut C Z).2 (op X Y) (xObj Y) ap mpa ub_sndg m_sndg L0 hp_L0 hL0_kp] at er2
    obtain ⟨Kf, hKf_A, hKf_B, hKf_eq⟩ := Quotient.exact er1
    obtain ⟨Ks, hKs_A, hKs_B, hKs_eq⟩ := Quotient.exact er2
    dsimp only [homSystem] at hKf_eq hKs_eq
    obtain ⟨L, hL_Kf, hL_Ks⟩ := D.bound Kf.1 Ks.1
    have key_f := congrArg
      (homTr C (colimOut C Z).2 (xObj X) Kf ⟨L, D.trans Kf.2.1 hL_Kf, D.trans Kf.2.2 hL_Kf⟩ hL_Kf) hKf_eq
    have key_s := congrArg
      (homTr C (colimOut C Z).2 (xObj Y) Ks ⟨L, D.trans Ks.2.1 hL_Ks, D.trans Ks.2.2 hL_Ks⟩ hL_Ks) hKs_eq
    rw [← homTr_trans C hC, ← homTr_trans C hC] at key_f
    rw [← homTr_trans C hC, ← homTr_trans C hC] at key_s
    rw [homTr_comp C] at key_f
    rw [homTr_comp C] at key_f
    rw [homTr_comp C] at key_s
    rw [homTr_comp C] at key_s
    rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key_f
    rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key_s
    -- product level data at L
    have hkp_L : D.le (kp X Y) L := D.trans hL0_kp (D.trans hKf_A hL_Kf)
    have hk_L : D.le (k X Y) L := D.trans (h_k_kp X Y) hkp_L
    have h_prod_eq_L : C.F (D.trans (h_ip_kp X Y) hkp_L) (op X Y)
        = C.F hk_L ((hp (k X Y)).prod (ak X Y) (bk X Y)) := by
      calc C.F (D.trans (h_ip_kp X Y) hkp_L) (op X Y)
            = C.F hkp_L (C.F (h_ip_kp X Y) (op X Y)) := by rw [C.F_trans (h_ip_kp X Y) hkp_L (op X Y)]
        _ = C.F hkp_L (C.F (h_k_kp X Y) ((hp (k X Y)).prod (ak X Y) (bk X Y))) := by rw [h_prod_eq X Y]
        _ = C.F hk_L ((hp (k X Y)).prod (ak X Y) (bk X Y)) := by
              rw [← C.F_trans (h_k_kp X Y) hkp_L ((hp (k X Y)).prod (ak X Y) (bk X Y))]
    have h_aktoX_L : C.F hk_L (ak X Y) = C.F (D.trans (D.trans (hA_k X Y) (h_k_kp X Y)) hkp_L) (xObj X) := by
      rw [show C.F hk_L (ak X Y) = C.F hk_L (C.F (hA_k X Y) (xObj X)) from rfl,
          ← C.F_trans (hA_k X Y) hk_L (xObj X)]
    have h_bktoY_L : C.F hk_L (bk X Y) = C.F (D.trans (D.trans (hB_k X Y) (h_k_kp X Y)) hkp_L) (xObj Y) := by
      rw [show C.F hk_L (bk X Y) = C.F hk_L (C.F (hB_k X Y) (xObj Y)) from rfl,
          ← C.F_trans (hB_k X Y) hk_L (xObj Y)]
    have hpush_f : homTr C (op X Y) (xObj X) ub_fstg ⟨L, D.trans ub_fstg.2.1 hkp_L, D.trans ub_fstg.2.2 hkp_L⟩ hkp_L m_fstg
        = castHom h_prod_eq_L.symm h_aktoX_L ((C.functF hk_L).map ((hp (k X Y)).fst (A:=ak X Y) (B:=bk X Y))) := by
      dsimp [homTr, m_fstg]
      rw [map_castHom (C.F hkp_L) (hT := C.functF hkp_L), castHom_castHom]
      exact castHom_heq_congr _ _ _ _
        (hC.trans_map (h_k_kp X Y) hkp_L ((hp (k X Y)).fst (A:=ak X Y) (B:=bk X Y))).symm
    have hpush_s : homTr C (op X Y) (xObj Y) ub_sndg ⟨L, D.trans ub_sndg.2.1 hkp_L, D.trans ub_sndg.2.2 hkp_L⟩ hkp_L m_sndg
        = castHom h_prod_eq_L.symm h_bktoY_L ((C.functF hk_L).map ((hp (k X Y)).snd (A:=ak X Y) (B:=bk X Y))) := by
      dsimp [homTr, m_sndg]
      rw [map_castHom (C.F hkp_L) (hT := C.functF hkp_L), castHom_castHom]
      exact castHom_heq_congr _ _ _ _
        (hC.trans_map (h_k_kp X Y) hkp_L ((hp (k X Y)).snd (A:=ak X Y) (B:=bk X Y))).symm
    rw [hpush_f] at key_f
    rw [hpush_s] at key_s
    have hik : D.le ah.1 L := D.trans ha_L0 (D.trans hKf_A hL_Kf)
    have hjk : D.le ap.1 L := D.trans hp_L0 (D.trans hKf_B hL_Kf)
    -- cast slides across composition (proof-irrelevant transports)
    have cR : ∀ {U V V' W : C.A L} (he : V = V') (a : U ⟶ V) (b : V' ⟶ W),
        castHom rfl he a ≫ b = a ≫ castHom he.symm rfl b := by
      intro U V V' W he a b; subst he; rfl
    have cT : ∀ {U V W W' : C.A L} (he : W = W') (a : U ⟶ V) (b : V ⟶ W),
        castHom rfl he (a ≫ b) = a ≫ castHom rfl he b := by
      intro U V W W' he a b; subst he; rfl
    refine Quotient.sound ⟨⟨L, D.trans ah.2.1 hik, D.trans ah.2.2 hik⟩, hik, hjk, ?_⟩
    dsimp only [homSystem]
    have hu := hpres hk_L (ak X Y) (bk X Y)
        (C.F (D.trans ah.2.1 hik) (colimOut C Z).2)
        (castHom rfl h_prod_eq_L
          (homTr C (colimOut C Z).2 (op X Y) ah ⟨L, D.trans ah.2.1 hik, D.trans ah.2.2 hik⟩ hik mha))
        (castHom rfl h_prod_eq_L
          (homTr C (colimOut C Z).2 (op X Y) ap ⟨L, D.trans ah.2.1 hik, D.trans ah.2.2 hik⟩ hjk mpa))
        (by
          rw [cR, cR]
          have hh := congrArg (castHom rfl h_aktoX_L.symm) key_f
          rw [cT, cT, castHom_castHom] at hh
          exact hh)
        (by
          rw [cR, cR]
          have hh := congrArg (castHom rfl h_bktoY_L.symm) key_s
          rw [cT, cT, castHom_castHom] at hh
          exact hh)
    have hu2 := congrArg (castHom rfl h_prod_eq_L.symm) hu
    rw [castHom_castHom, castHom_castHom] at hu2
    exact hu2
  exact @HasBinaryProducts.mk C.Obj (colimitCat C hC) prodFun fst snd pair h_fst_pair h_snd_pair h_pair_uniq

/-!
  M3 — equalizers of the colimit category.

  Packaged as one existence `Prop` (`hEdata`) so `Quotient.inductionOn` may be
  used on `F`, `G` and the cone leg `c` alike; the `HasEqualizer` structure is
  then extracted by choice.  `hpres` (transitions keep `eqMap` left-cancellable)
  gives uniqueness; `hpres_lift` (transitions create equalizer-lifts) gives the
  factorisation.  Mirrors `colimitHasBinaryProducts`.
-/

noncomputable def colimitHasEqualizers (C : CatSystem ι D) (hC : C.Coherent)
    (he : ∀ i, HasEqualizers (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hpres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k) :
    @HasEqualizers C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  have hDirSubsingleton : ∀ {i j : ι} (h h' : D.le i j), h = h' :=
    fun {_ _} h h' => Subsingleton.elim h h'
  have hF_proof_irrel : ∀ {i j : ι} (h h' : D.le i j) (a : C.A i), C.F h a = C.F h' a :=
    fun {_ _} h h' a => by rw [hDirSubsingleton h h']
  have hEdata : ∀ (X Y : C.Obj) (F G : X ⟶ Y),
      ∃ (E : C.Obj) (m : E ⟶ X), m ≫ F = m ≫ G ∧
        ∀ (W : C.Obj) (c : W ⟶ X), c ≫ F = c ≫ G →
          ∃ l : W ⟶ E, l ≫ m = c ∧ ∀ l' : W ⟶ E, l' ≫ m = c → l' = l := by
    intro X Y F G
    refine Quotient.inductionOn F (fun Fr => ?_)
    refine Quotient.inductionOn G (fun Gr => ?_)
    obtain ⟨aF, fF⟩ := Fr
    obtain ⟨aG, gG⟩ := Gr
    -- representatives of X, Y
    let iX := (colimOut C X).1; let xX := (colimOut C X).2
    let iY := (colimOut C Y).1; let xY := (colimOut C Y).2
    -- common stage M for the two parallel germs; proof-irrelevance aligns the targets
    obtain ⟨M, haFM, haGM⟩ := D.bound aF.1 aG.1
    let hiXM : D.le iX M := D.trans aF.2.1 haFM
    let hiYM : D.le iY M := D.trans aF.2.2 haFM
    let fM : C.F hiXM xX ⟶ C.F hiYM xY := homTr C xX xY aF ⟨M, hiXM, hiYM⟩ haFM fF
    let gM : C.F hiXM xX ⟶ C.F hiYM xY := homTr C xX xY aG ⟨M, hiXM, hiYM⟩ haGM gG
    -- equalizer object at stage M, included into the colimit
    let Eobj : C.A M := eqObj fM gM
    let E : C.Obj := C.objIncl M Eobj
    -- transport `E`'s chosen representative back to `⟨M, Eobj⟩` (mirrors products)
    let ipE : ι := (colimOut C E).1; let opE : C.A ipE := (colimOut C E).2
    have hESpec : C.objIncl ipE opE = E := colimOut_spec C E
    have hERel : Rel C.objSystem ⟨ipE, opE⟩ ⟨M, Eobj⟩ := Quotient.exact hESpec
    let kpE : ι := Classical.choose hERel
    have hkpE1 : ∃ (hik : D.le ipE kpE) (hjk : D.le M kpE), C.F hik opE = C.F hjk Eobj :=
      Classical.choose_spec hERel
    let h_ipE_kpE : D.le ipE kpE := Classical.choose hkpE1
    have hkpE2 : ∃ (hjk : D.le M kpE), C.F h_ipE_kpE opE = C.F hjk Eobj := Classical.choose_spec hkpE1
    let h_M_kpE : D.le M kpE := Classical.choose hkpE2
    have h_E_eq : C.F h_ipE_kpE opE = C.F h_M_kpE Eobj := Classical.choose_spec hkpE2
    -- the equalizer map E ⟶ X, as a germ from `opE` (= colimOut rep of E) to `xX`
    let ubm : UpperBound D ipE iX := ⟨kpE, h_ipE_kpE, D.trans hiXM h_M_kpE⟩
    let gm : C.F ubm.2.1 opE ⟶ C.F ubm.2.2 xX :=
      castHom h_E_eq.symm (C.F_trans hiXM h_M_kpE xX).symm ((C.functF h_M_kpE).map (eqMap fM gM))
    let m : E ⟶ X := homIncl C hC opE xX ubm gm
    -- `m` is monic: reduce `l ≫ m = l' ≫ m` to a stage equation, cancel `eqMap` via `hpres`.
    have hm_mono : ∀ {W : C.Obj} (l l' : W ⟶ E), l ≫ m = l' ≫ m → l = l' := by
      intro W
      refine Quotient.ind₂ (fun lr lr' hll => ?_)
      obtain ⟨aL, lL⟩ := lr
      obtain ⟨aL', lL'⟩ := lr'
      let xW : C.A (colimOut C W).1 := (colimOut C W).2
      -- common stage P ≥ aL.1, aL'.1, kpE
      obtain ⟨P0, hP0a, hP0b⟩ := D.bound aL.1 aL'.1
      obtain ⟨P, hP0P, hkpEP⟩ := D.bound P0 kpE
      have haLP : D.le aL.1 P := D.trans hP0a hP0P
      have haLP' : D.le aL'.1 P := D.trans hP0b hP0P
      -- reduce both composites to `compAt` at `P`
      rw [show (Quotient.mk (setoid (homSystem C hC xW opE)) ⟨aL, lL⟩ : W ⟶ E) ≫ m
            = homCompRaw C hC xW opE xX aL lL ubm gm from rfl,
          show (Quotient.mk (setoid (homSystem C hC xW opE)) ⟨aL', lL'⟩ : W ⟶ E) ≫ m
            = homCompRaw C hC xW opE xX aL' lL' ubm gm from rfl,
          homCompRaw_eq_compAt C hC xW opE xX aL lL ubm gm P haLP hkpEP,
          homCompRaw_eq_compAt C hC xW opE xX aL' lL' ubm gm P haLP' hkpEP] at hll
      obtain ⟨R, hPR, hPR', hReq⟩ := Quotient.exact hll
      dsimp only [homSystem] at hReq
      obtain ⟨L, hRL, _⟩ := D.bound R.1 R.1
      have key := congrArg
        (homTr C xW xX R ⟨L, D.trans R.2.1 hRL, D.trans R.2.2 hRL⟩ hRL) hReq
      rw [← homTr_trans C hC, ← homTr_trans C hC] at key
      rw [homTr_comp C, homTr_comp C] at key
      rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key
      -- key : homTr lL (aL→L) ≫ homTr gm (ubm→L) = homTr lL' (aL'→L) ≫ homTr gm (ubm→L)
      have hkpEL : D.le kpE L := D.trans hkpEP (D.trans hPR hRL)
      have hML : D.le M L := D.trans h_M_kpE hkpEL
      have hipEL : D.le ipE L := D.trans h_ipE_kpE hkpEL
      have hiXL : D.le iX L := D.trans hiXM hML
      have hHd : C.F hML Eobj = C.F hipEL opE :=
        calc C.F hML Eobj = C.F hkpEL (C.F h_M_kpE Eobj) := by rw [C.F_trans h_M_kpE hkpEL Eobj]
          _ = C.F hkpEL (C.F h_ipE_kpE opE) := by rw [← h_E_eq]
          _ = C.F hipEL opE := by rw [← C.F_trans h_ipE_kpE hkpEL opE]
      have hHc : C.F hML (C.F hiXM xX) = C.F hiXL xX := (C.F_trans hiXM hML xX).symm
      have hpush_gm : homTr C opE xX ubm ⟨L, hipEL, hiXL⟩ hkpEL gm
          = castHom hHd hHc ((C.functF hML).map (eqMap fM gM)) := by
        dsimp [homTr, gm]
        rw [map_castHom (C.F hkpEL) (hT := C.functF hkpEL), castHom_castHom]
        exact castHom_heq_congr _ _ _ _ (hC.trans_map h_M_kpE hkpEL (eqMap fM gM)).symm
      rw [hpush_gm] at key
      -- cancel the `eqMap`-map on the right via `hpres`
      have cR : ∀ {U V V' Wq : C.A L} (he : V = V') (a : U ⟶ V) (b : V' ⟶ Wq),
          castHom rfl he a ≫ b = a ≫ castHom he.symm rfl b := by
        intro _ _ _ _ he a b; subst he; rfl
      have cT : ∀ {U V Wq Wq' : C.A L} (he : Wq = Wq') (a : U ⟶ V) (b : V ⟶ Wq),
          castHom rfl he (a ≫ b) = a ≫ castHom rfl he b := by
        intro _ _ _ _ he a b; subst he; rfl
      have hbig : D.le aL.1 L := D.trans haLP (D.trans hPR hRL)
      have hbig' : D.le aL'.1 L := D.trans haLP' (D.trans hPR hRL)
      refine Quotient.sound ⟨⟨L, D.trans aL.2.1 hbig, D.trans aL.2.2 hbig⟩, hbig, hbig', ?_⟩
      dsimp only [homSystem]
      have hu := hpres hML fM gM (C.F (D.trans aL.2.1 hbig) xW)
        (castHom rfl hHd.symm (homTr C xW opE aL ⟨L, D.trans aL.2.1 hbig, D.trans aL.2.2 hbig⟩ hbig lL))
        (castHom rfl hHd.symm (homTr C xW opE aL' ⟨L, D.trans aL'.2.1 hbig', D.trans aL'.2.2 hbig'⟩ hbig' lL'))
        (by
          rw [cR, cR]
          have hh := congrArg (castHom rfl hHc.symm) key
          rw [cT, cT, castHom_castHom] at hh
          exact hh)
      have hu2 := congrArg (castHom rfl hHd) hu
      rw [castHom_castHom, castHom_castHom] at hu2
      exact hu2
    refine ⟨E, m, ?_, ?_⟩
    · -- equalizing: m ≫ F = m ≫ G.
      -- Generic: composing `m` (germ `gm` at `kpE`) with a right germ `gg` that
      -- lifts to `gMrep : fM↔gM` at `M` equals the germ `eqMap fM gM ≫ gMrep`.
      have hcomp : ∀ (a : UpperBound D iX iY) (gg : C.F a.2.1 xX ⟶ C.F a.2.2 xY)
          (haM : D.le a.1 M) (gMrep : C.F hiXM xX ⟶ C.F hiYM xY)
          (_hgg : homTr C xX xY a ⟨M, hiXM, hiYM⟩ haM gg = gMrep),
          homCompRaw C hC opE xX xY ubm gm a gg
            = homIncl C hC opE xY ⟨kpE, h_ipE_kpE, D.trans hiYM h_M_kpE⟩
                (castHom h_E_eq.symm (C.F_trans hiYM h_M_kpE xY).symm
                  ((C.functF h_M_kpE).map (eqMap fM gM ≫ gMrep))) := by
        intro a gg haM gMrep hgg
        refine homCompRaw_eq_of_stage C hC opE xX xY ubm gm a gg
          ⟨kpE, h_ipE_kpE, D.trans hiYM h_M_kpE⟩ _ kpE (D.refl kpE) (D.trans haM h_M_kpE)
          (D.refl kpE) ?_
        -- stage equation at `kpE`
        rw [homTr_refl C hC opE xX ubm gm]
        rw [show homTr C xX xY a ⟨kpE, D.trans a.2.1 (D.trans haM h_M_kpE), D.trans a.2.2 (D.trans haM h_M_kpE)⟩
              (D.trans haM h_M_kpE) gg
            = homTr C xX xY ⟨M, hiXM, hiYM⟩ ⟨kpE, D.trans hiXM h_M_kpE, D.trans hiYM h_M_kpE⟩ h_M_kpE gMrep from by
          rw [← hgg, ← homTr_trans C hC xX xY a ⟨M, hiXM, hiYM⟩ _ haM h_M_kpE gg]]
        rw [homTr_refl C hC opE xY ⟨kpE, h_ipE_kpE, D.trans hiYM h_M_kpE⟩]
        -- now: gm ≫ homTr gMrep = castHom .. (map (eqMap fM gM ≫ gMrep))
        show castHom h_E_eq.symm (C.F_trans hiXM h_M_kpE xX).symm ((C.functF h_M_kpE).map (eqMap fM gM))
            ≫ castHom (C.F_trans hiXM h_M_kpE xX).symm (C.F_trans hiYM h_M_kpE xY).symm
                ((C.functF h_M_kpE).map gMrep)
          = castHom h_E_eq.symm (C.F_trans hiYM h_M_kpE xY).symm
              ((C.functF h_M_kpE).map (eqMap fM gM ≫ gMrep))
        rw [castHom_comp, ← (C.functF h_M_kpE).map_comp]
      show homCompRaw C hC opE xX xY ubm gm aF fF = homCompRaw C hC opE xX xY ubm gm aG gG
      rw [hcomp aF fF haFM fM rfl, hcomp aG gG haGM gM rfl, eqMap_eq fM gM]
    · intro W c
      refine Quotient.inductionOn c (fun cr => ?_)
      obtain ⟨aC, cC⟩ := cr
      intro hc
      let xW : C.A (colimOut C W).1 := (colimOut C W).2
      -- common stage P ≥ aC.1, aF.1, aG.1, then reflect `hc`
      obtain ⟨P1, hcP1, hfP1⟩ := D.bound aC.1 aF.1
      obtain ⟨P, hP1P, hgP⟩ := D.bound P1 aG.1
      have hcP : D.le aC.1 P := D.trans hcP1 hP1P
      have hfP : D.le aF.1 P := D.trans hfP1 hP1P
      change homCompRaw C hC xW xX xY aC cC aF fF = homCompRaw C hC xW xX xY aC cC aG gG at hc
      rw [homCompRaw_eq_compAt C hC xW xX xY aC cC aF fF P hcP hfP,
          homCompRaw_eq_compAt C hC xW xX xY aC cC aG gG P hcP hgP] at hc
      obtain ⟨R, hPR, hPR', hReq⟩ := Quotient.exact hc
      dsimp only [homSystem] at hReq
      obtain ⟨L, hRL, hkpEL⟩ := D.bound R.1 kpE
      have hML : D.le M L := D.trans h_M_kpE hkpEL
      have key := congrArg
        (homTr C xW xY R ⟨L, D.trans R.2.1 hRL, D.trans R.2.2 hRL⟩ hRL) hReq
      rw [← homTr_trans C hC, ← homTr_trans C hC] at key
      rw [homTr_comp C, homTr_comp C] at key
      rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key
      -- key : homTr cC (aC→L) ≫ homTr fF (aF→L) = homTr cC (aC→L) ≫ homTr gG (aG→L)
      have hiXL : D.le iX L := D.trans hiXM hML
      have hiYL : D.le iY L := D.trans hiYM hML
      have hipEL : D.le ipE L := D.trans h_ipE_kpE hkpEL
      have hHdL : C.F hML Eobj = C.F hipEL opE :=
        calc C.F hML Eobj = C.F hkpEL (C.F h_M_kpE Eobj) := by rw [C.F_trans h_M_kpE hkpEL Eobj]
          _ = C.F hkpEL (C.F h_ipE_kpE opE) := by rw [← h_E_eq]
          _ = C.F hipEL opE := by rw [← C.F_trans h_ipE_kpE hkpEL opE]
      have hAX : C.F hiXL xX = C.F hML (C.F hiXM xX) := C.F_trans hiXM hML xX
      have hAY : C.F hiYL xY = C.F hML (C.F hiYM xY) := C.F_trans hiYM hML xY
      have hpush_f : homTr C xX xY aF ⟨L, hiXL, hiYL⟩ (D.trans haFM hML) fF
          = castHom hAX.symm hAY.symm ((C.functF hML).map fM) := by
        rw [homTr_trans C hC xX xY aF ⟨M, hiXM, hiYM⟩ ⟨L, hiXL, hiYL⟩ haFM hML fF]; rfl
      have hpush_g : homTr C xX xY aG ⟨L, hiXL, hiYL⟩ (D.trans haGM hML) gG
          = castHom hAX.symm hAY.symm ((C.functF hML).map gM) := by
        rw [homTr_trans C hC xX xY aG ⟨M, hiXM, hiYM⟩ ⟨L, hiXL, hiYL⟩ haGM hML gG]; rfl
      rw [hpush_f, hpush_g] at key
      -- cancel the codomain cast to get the `hpres_lift` hypothesis
      let cL := homTr C xW xX aC ⟨L, D.trans aC.2.1 (D.trans hcP (D.trans hPR hRL)),
        D.trans aC.2.2 (D.trans hcP (D.trans hPR hRL))⟩ (D.trans hcP (D.trans hPR hRL)) cC
      have cR : ∀ {U V V' Wq : C.A L} (he : V = V') (a : U ⟶ V) (b : V' ⟶ Wq),
          castHom rfl he a ≫ b = a ≫ castHom he.symm rfl b := by
        intro _ _ _ _ he a b; subst he; rfl
      have cT : ∀ {U V Wq Wq' : C.A L} (he : Wq = Wq') (a : U ⟶ V) (b : V ⟶ Wq),
          castHom rfl he (a ≫ b) = a ≫ castHom rfl he b := by
        intro _ _ _ _ he a b; subst he; rfl
      have hk : (castHom rfl hAX cL) ≫ (C.functF hML).map fM
              = (castHom rfl hAX cL) ≫ (C.functF hML).map gM := by
        have hh := congrArg (castHom rfl hAY) key
        rw [cT, cT] at hh
        rw [show castHom rfl hAY (castHom hAX.symm hAY.symm ((C.functF hML).map fM))
              = castHom hAX.symm rfl ((C.functF hML).map fM) from by rw [castHom_castHom],
            show castHom rfl hAY (castHom hAX.symm hAY.symm ((C.functF hML).map gM))
              = castHom hAX.symm rfl ((C.functF hML).map gM) from by rw [castHom_castHom]] at hh
        rw [← cR, ← cR] at hh
        exact hh
      obtain ⟨r, hr⟩ := hpres_lift hML fM gM (C.F (D.trans aC.2.1 (D.trans hcP (D.trans hPR hRL))) xW)
        (castHom rfl hAX cL) hk
      -- the lift `l : W ⟶ E`
      have haCL : D.le aC.1 L := D.trans hcP (D.trans hPR hRL)
      let lmap : W ⟶ E := homIncl C hC xW opE ⟨L, D.trans aC.2.1 haCL, hipEL⟩ (castHom rfl hHdL r)
      have hiXL2 : D.le iX L := D.trans hiXM hML
      have hHcL : C.F hML (C.F hiXM xX) = C.F hiXL2 xX := (C.F_trans hiXM hML xX).symm
      have hpush_gmL : homTr C opE xX ubm ⟨L, hipEL, hiXL2⟩ hkpEL gm
          = castHom hHdL hHcL ((C.functF hML).map (eqMap fM gM)) := by
        dsimp [homTr, gm]
        rw [map_castHom (C.F hkpEL) (hT := C.functF hkpEL), castHom_castHom]
        exact castHom_heq_congr _ _ _ _ (hC.trans_map h_M_kpE hkpEL (eqMap fM gM)).symm
      have hfac : lmap ≫ m = Quotient.mk (setoid (homSystem C hC xW xX)) ⟨aC, cC⟩ := by
        show homCompRaw C hC xW opE xX ⟨L, D.trans aC.2.1 haCL, hipEL⟩ (castHom rfl hHdL r) ubm gm
          = Quotient.mk (setoid (homSystem C hC xW xX)) ⟨aC, cC⟩
        rw [show (Quotient.mk (setoid (homSystem C hC xW xX)) ⟨aC, cC⟩)
              = homIncl C hC xW xX aC cC from rfl]
        refine homCompRaw_eq_of_stage C hC xW opE xX ⟨L, D.trans aC.2.1 haCL, hipEL⟩
          (castHom rfl hHdL r) ubm gm aC cC L (D.refl L) hkpEL haCL ?_
        rw [homTr_refl C hC, hpush_gmL, castHom_comp, hr]
        -- castHom rfl hAX.symm-ish (castHom rfl hAX cL) collapses to cL = homTr cC (aC→L)
        rw [castHom_castHom]
        rfl
      exact ⟨lmap, hfac, fun l' hl' => hm_mono l' lmap (hl'.trans hfac.symm)⟩
  refine ⟨fun X Y F G => ?_⟩
  -- extract the data by choice (the goal `HasEqualizer F G` is a Type, so `obtain` is illegal)
  let E : C.Obj := (hEdata X Y F G).choose
  let m : E ⟶ X := (hEdata X Y F G).choose_spec.choose
  have hmeq : m ≫ F = m ≫ G := (hEdata X Y F G).choose_spec.choose_spec.1
  have huniv : ∀ (W : C.Obj) (c : W ⟶ X), c ≫ F = c ≫ G →
      ∃ l : W ⟶ E, l ≫ m = c ∧ ∀ l' : W ⟶ E, l' ≫ m = c → l' = l :=
    (hEdata X Y F G).choose_spec.choose_spec.2
  exact {
    cone := ⟨E, m, hmeq⟩
    lift := fun c => (huniv c.dom c.map c.eq).choose
    fac := fun c => (huniv c.dom c.map c.eq).choose_spec.1
    uniq := fun c l hl => (huniv c.dom c.map c.eq).choose_spec.2 l hl }

/-! ## M3 — cover-transfer for the colimit (toward `PreRegularCategory C.Obj`)

  Foundational reflection lemmas.  `Cover` is a `∀`-over-monos, so transferring it
  to the colimit needs iso/mono/cover preservation+reflection through `colimitCat`,
  each fighting the `colimOut` representative transport. -/

/-- **Iso preservation:** a colimit morphism whose stage representative `f₀` is an
    isomorphism (witnessed by `g₀`) is itself an isomorphism in `colimitCat`. -/
theorem colimHom_isIso_of_rep (C : CatSystem ι D) (hC : C.Coherent) {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (g₀ : C.F a.2.2 (colimOut C B).2 ⟶ C.F a.2.1 (colimOut C A).2)
    (h1 : f₀ ≫ g₀ = Cat.id (C.F a.2.1 (colimOut C A).2))
    (h2 : g₀ ≫ f₀ = Cat.id (C.F a.2.2 (colimOut C B).2)) :
    @IsIso C.Obj (colimitCat C hC) A B (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀) := by
  letI : Cat C.Obj := colimitCat C hC
  obtain ⟨av, ah1, ah2⟩ := a
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  refine ⟨homIncl C hC xB xA ⟨av, ah2, ah1⟩ g₀, ?_, ?_⟩
  · show homCompRaw C hC xA xB xA ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ = colimId C hC A
    rw [homCompRaw_eq_compAt C hC xA xB xA ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ av (D.refl av) (D.refl av)]
    unfold compAt
    simp only [homTr_refl C hC]; rw [h1]
    show homIncl C hC xA xA ⟨av, ah1, ah1⟩ (Cat.id (C.F ah1 xA)) = colimId C hC A
    rw [← homTr_id C xA ⟨(colimOut C A).1, D.refl _, D.refl _⟩ ⟨av, ah1, ah1⟩ ah1]
    exact homIncl_compat C hC xA xA ah1 (Cat.id _)
  · show homCompRaw C hC xB xA xB ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ = colimId C hC B
    rw [homCompRaw_eq_compAt C hC xB xA xB ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ av (D.refl av) (D.refl av)]
    unfold compAt
    simp only [homTr_refl C hC]; rw [h2]
    show homIncl C hC xB xB ⟨av, ah2, ah2⟩ (Cat.id (C.F ah2 xB)) = colimId C hC B
    rw [← homTr_id C xB ⟨(colimOut C B).1, D.refl _, D.refl _⟩ ⟨av, ah2, ah2⟩ ah2]
    exact homIncl_compat C hC xB xB ah2 (Cat.id _)

/-- **`homIncl` is injective on hom-sets when the transition functors are faithful.**
    Two stage germs at the same bound including to the same colimit morphism are
    equal — the linchpin for reflecting monos/covers/pullbacks from `colimitCat`
    to a stage.  `Quotient.exact` gives a common bound where the `homTr`-pushes
    agree; `homTr` is `castHom ∘ functF.map`, so cast-invertibility + faithfulness
    of `functF` strip back to `g = g'`. -/
theorem homIncl_injective (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {i j : ι} (x : C.A i) (y : C.A j) (a : UpperBound D i j)
    (g g' : C.F a.2.1 x ⟶ C.F a.2.2 y)
    (h : homIncl C hC x y a g = homIncl C hC x y a g') : g = g' := by
  obtain ⟨k, hik, hjk, heq⟩ := Quotient.exact h
  rw [Subsingleton.elim hjk hik] at heq
  dsimp only [homSystem, homTr] at heq
  have hstrip := congrArg (castHom (C.F_trans a.2.1 hik x) (C.F_trans a.2.2 hik y)) heq
  rw [castHom_castHom, castHom_castHom] at hstrip
  exact hfaith hik g g' hstrip

/-- **Mono preservation:** a colimit morphism with representative `f₀` is monic in
    `colimitCat` provided `f₀` stays left-cancellable under all transitions
    (`hcancel`).  Reflect `p ≫ f = q ≫ f` to a common stage `L`, where it becomes
    `· ≫ (functF haL).map f₀ = · ≫ (functF haL).map f₀`; `hcancel` then cancels. -/
theorem colimHom_mono_of_rep (C : CatSystem ι D) (hC : C.Coherent) {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (hcancel : ∀ {j : ι} (hjk : D.le a.1 j) (z : C.A j)
        (u v : z ⟶ C.F hjk (C.F a.2.1 (colimOut C A).2)),
        u ≫ (C.functF hjk).map f₀ = v ≫ (C.functF hjk).map f₀ → u = v) :
    @Mono C.Obj (colimitCat C hC) A B
      (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀) := by
  letI : Cat C.Obj := colimitCat C hC
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  intro W
  refine Quotient.ind₂ (fun pr qr hpq => ?_)
  obtain ⟨ap, p₀⟩ := pr
  obtain ⟨aq, q₀⟩ := qr
  let xW : C.A (colimOut C W).1 := (colimOut C W).2
  obtain ⟨P0, hP0p, hP0q⟩ := D.bound ap.1 aq.1
  obtain ⟨P, hP0P, haP⟩ := D.bound P0 a.1
  have hapP : D.le ap.1 P := D.trans hP0p hP0P
  have haqP : D.le aq.1 P := D.trans hP0q hP0P
  change homCompRaw C hC xW xA xB ap p₀ a f₀ = homCompRaw C hC xW xA xB aq q₀ a f₀ at hpq
  rw [homCompRaw_eq_compAt C hC xW xA xB ap p₀ a f₀ P hapP haP,
      homCompRaw_eq_compAt C hC xW xA xB aq q₀ a f₀ P haqP haP] at hpq
  obtain ⟨R, hPR, hPR', hReq⟩ := Quotient.exact hpq
  dsimp only [homSystem] at hReq
  obtain ⟨L, hRL, _⟩ := D.bound R.1 R.1
  have key := congrArg (homTr C xW xB R ⟨L, D.trans R.2.1 hRL, D.trans R.2.2 hRL⟩ hRL) hReq
  rw [← homTr_trans C hC, ← homTr_trans C hC] at key
  rw [homTr_comp C, homTr_comp C] at key
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key
  -- key : homTr p₀ (ap→L) ≫ homTr f₀ (a→L) = homTr q₀ (aq→L) ≫ homTr f₀ (a→L)
  have haL : D.le a.1 L := D.trans haP (D.trans hPR hRL)
  have hiAL : D.le (colimOut C A).1 L := D.trans a.2.1 haL
  have hiBL : D.le (colimOut C B).1 L := D.trans a.2.2 haL
  have hHc : C.F haL (C.F a.2.1 xA) = C.F hiAL xA := (C.F_trans a.2.1 haL xA).symm
  have hHc2 : C.F haL (C.F a.2.2 xB) = C.F hiBL xB := (C.F_trans a.2.2 haL xB).symm
  have hpush_f : homTr C xA xB a ⟨L, hiAL, hiBL⟩ haL f₀
      = castHom hHc hHc2 ((C.functF haL).map f₀) := rfl
  rw [hpush_f] at key
  have cR : ∀ {U V V' Wq : C.A L} (he : V = V') (b : U ⟶ V) (c : V' ⟶ Wq),
      castHom rfl he b ≫ c = b ≫ castHom he.symm rfl c := by
    intro _ _ _ _ he b c; subst he; rfl
  have cT : ∀ {U V Wq Wq' : C.A L} (he : Wq = Wq') (b : U ⟶ V) (c : V ⟶ Wq),
      castHom rfl he (b ≫ c) = b ≫ castHom rfl he c := by
    intro _ _ _ _ he b c; subst he; rfl
  have hbig : D.le ap.1 L := D.trans hapP (D.trans hPR hRL)
  have hbig' : D.le aq.1 L := D.trans haqP (D.trans hPR hRL)
  refine Quotient.sound ⟨⟨L, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩, hbig, hbig', ?_⟩
  dsimp only [homSystem]
  have hu := hcancel haL (C.F (D.trans ap.2.1 hbig) xW)
    (castHom rfl hHc.symm (homTr C xW xA ap ⟨L, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩ hbig p₀))
    (castHom rfl hHc.symm (homTr C xW xA aq ⟨L, D.trans aq.2.1 hbig', D.trans aq.2.2 hbig'⟩ hbig' q₀))
    (by
      rw [cR, cR]
      have hh := congrArg (castHom rfl hHc2.symm) key
      rw [cT, cT, castHom_castHom] at hh
      exact hh)
  have hu2 := congrArg (castHom rfl hHc) hu
  rw [castHom_castHom, castHom_castHom] at hu2
  exact hu2

/-- `castHom` is injective (it's a transport along object equalities). -/
theorem castHom_injective {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') {a b : X ⟶ Y}
    (h : castHom hX hY a = castHom hX hY b) : a = b := by
  subst hX; subst hY; exact h

/-- **Mono reflection** (converse of `colimHom_mono_of_rep`): if `homIncl a f₀` is
    monic in `colimitCat` (and transitions are faithful), then its stage germ `f₀`
    is left-cancellable under all transitions.  Given stage maps `u, v` with
    `u ≫ functF.map f₀ = v ≫ functF.map f₀` at a stage `j ≥ a.1`, include them as
    `colimitCat` maps `objIncl j z ⟶ A` at the rep-agreement stage `s` of
    `objIncl j z`; composing with `homIncl a f₀` reduces — via `homCompRaw_eq_compAt`
    + `castHom_comp` + `map_comp` — to `functF.map (u ≫ functF.map f₀)`, so the
    colimit mono forces the two inclusions equal, and `homIncl_injective` +
    `castHom_injective` + faithfulness strip back to `u = v`. -/
theorem colimHom_mono_reflects (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (hmono : @Mono C.Obj (colimitCat C hC) A B
      (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀))
    {j : ι} (hjk : D.le a.1 j) (z : C.A j)
    (u v : z ⟶ C.F hjk (C.F a.2.1 (colimOut C A).2))
    (huv : u ≫ (C.functF hjk).map f₀ = v ≫ (C.functF hjk).map f₀) : u = v := by
  letI : Cat C.Obj := colimitCat C hC
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  let W := C.objIncl j z
  let xW := (colimOut C W).2
  -- rep agreement of `objIncl j z` at a stage `s ≥ j`
  obtain ⟨s, hps, hjs, heq0⟩ := Quotient.exact (colimOut_spec C W)
  dsimp only [CatSystem.objSystem] at heq0
  -- heq0 : C.F hps xW = C.F hjs z
  have h_as : D.le a.1 s := D.trans hjk hjs
  -- codomain casts at stage `s` (independent of `u`/`v`)
  have hcodA : C.F hjs (C.F hjk (C.F a.2.1 xA)) = C.F (D.trans a.2.1 h_as) xA := by
    rw [← C.F_trans a.2.1 hjk xA, ← C.F_trans (D.trans a.2.1 hjk) hjs xA]
  have hcodB : C.F hjs (C.F hjk (C.F a.2.2 xB)) = C.F (D.trans a.2.2 h_as) xB := by
    rw [← C.F_trans a.2.2 hjk xB, ← C.F_trans (D.trans a.2.2 hjk) hjs xB]
  -- include a stage map `m : z ⟶ …` as a germ `xW ⟶ xA` at stage `s`
  let germ : (z ⟶ C.F hjk (C.F a.2.1 xA)) → (C.F hps xW ⟶ C.F (D.trans a.2.1 h_as) xA) :=
    fun m => castHom heq0.symm hcodA ((C.functF hjs).map m)
  let U : C.objIncl j z ⟶ A := homIncl C hC xW xA ⟨s, hps, D.trans a.2.1 h_as⟩ (germ u)
  let V : C.objIncl j z ⟶ A := homIncl C hC xW xA ⟨s, hps, D.trans a.2.1 h_as⟩ (germ v)
  -- `f₀` pushed from bound `a` to stage `s` factors as the iterated transition map
  have hpf : homTr C xA xB a ⟨s, D.trans a.2.1 h_as, D.trans a.2.2 h_as⟩ h_as f₀
      = castHom hcodA hcodB ((C.functF hjs).map ((C.functF hjk).map f₀)) := by
    unfold homTr
    exact castHom_heq_congr _ _ hcodA hcodB (hC.trans_map hjk hjs f₀)
  -- composing the germ with the pushed `f₀` only sees `m ≫ functF.map f₀`
  have key : ∀ (m : z ⟶ C.F hjk (C.F a.2.1 xA)),
      germ m ≫ homTr C xA xB a ⟨s, D.trans a.2.1 h_as, D.trans a.2.2 h_as⟩ h_as f₀
        = castHom heq0.symm hcodB ((C.functF hjs).map (m ≫ (C.functF hjk).map f₀)) := by
    intro m
    show castHom heq0.symm hcodA ((C.functF hjs).map m) ≫ _ = _
    rw [hpf, castHom_comp, ← (C.functF hjs).map_comp]
  -- the two inclusions agree after composing with `homIncl a f₀`
  have hUV : colimComp C hC U (homIncl C hC xA xB a f₀)
      = colimComp C hC V (homIncl C hC xA xB a f₀) := by
    show homCompRaw C hC xW xA xB ⟨s, hps, D.trans a.2.1 h_as⟩ (germ u) a f₀
       = homCompRaw C hC xW xA xB ⟨s, hps, D.trans a.2.1 h_as⟩ (germ v) a f₀
    rw [homCompRaw_eq_compAt C hC xW xA xB ⟨s, hps, D.trans a.2.1 h_as⟩ (germ u) a f₀ s (D.refl s) h_as,
        homCompRaw_eq_compAt C hC xW xA xB ⟨s, hps, D.trans a.2.1 h_as⟩ (germ v) a f₀ s (D.refl s) h_as]
    unfold compAt
    rw [homTr_refl C hC, homTr_refl C hC, key u, key v, huv]
  -- colimit mono ⇒ U = V ⇒ germ u = germ v ⇒ map u = map v ⇒ u = v
  have hUVeq : U = V := hmono U V hUV
  have hgerm : germ u = germ v :=
    homIncl_injective C hC hfaith xW xA ⟨s, hps, D.trans a.2.1 h_as⟩ (germ u) (germ v) hUVeq
  exact hfaith hjs u v (castHom_injective heq0.symm hcodA hgerm)

/-- **Extract a stage equation from a colimit composite equality.**  If
    `homCompRaw uf f ug g = homIncl uh hh`, then at some stage `N` the pushed germs
    `f`, `g` compose to the pushed `hh`.  `homCompRaw_eq_compAt` presents the composite
    as one `homIncl`; `Quotient.exact` gives a common upper bound, which we push to a
    *constructed* stage `L` (the hom-colimit is indexed by `UpperBound`s, not bare
    stages, so its bounds aren't explicit constructors that `homTr_comp`/`homTr_trans`
    can match) where the equation becomes a plain stage equation. -/
theorem homCompRaw_eq_stage (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (uf : UpperBound D ip iq) (f : C.F uf.2.1 xp ⟶ C.F uf.2.2 xq)
    (ug : UpperBound D iq ir) (g : C.F ug.2.1 xq ⟶ C.F ug.2.2 xr)
    (uh : UpperBound D ip ir) (hh : C.F uh.2.1 xp ⟶ C.F uh.2.2 xr)
    (h : homCompRaw C hC xp xq xr uf f ug g = homIncl C hC xp xr uh hh) :
    ∃ (N : ι) (hfN : D.le uf.1 N) (hgN : D.le ug.1 N) (hhN : D.le uh.1 N),
      homTr C xp xq uf ⟨N, D.trans uf.2.1 hfN, D.trans uf.2.2 hfN⟩ hfN f
        ≫ homTr C xq xr ug ⟨N, D.trans ug.2.1 hgN, D.trans ug.2.2 hgN⟩ hgN g
      = homTr C xp xr uh ⟨N, D.trans uh.2.1 hhN, D.trans uh.2.2 hhN⟩ hhN hh := by
  obtain ⟨M, hfM, hgM⟩ := D.bound uf.1 ug.1
  rw [homCompRaw_eq_compAt C hC xp xq xr uf f ug g M hfM hgM] at h
  unfold compAt at h
  obtain ⟨N, h1, h2, heq⟩ := Quotient.exact h
  dsimp only [homSystem] at heq
  obtain ⟨L, hNL, _⟩ := D.bound N.1 N.1
  have key := congrArg (homTr C xp xr N ⟨L, D.trans N.2.1 hNL, D.trans N.2.2 hNL⟩ hNL) heq
  rw [← homTr_trans C hC, ← homTr_trans C hC, homTr_comp C,
      ← homTr_trans C hC, ← homTr_trans C hC] at key
  exact ⟨L, D.trans hfM (D.trans h1 hNL), D.trans hgM (D.trans h1 hNL), D.trans h2 hNL, key⟩

/-- **Stage equation from a colimit composite equal to the identity** — the `homIncl …
    id` special case of `homCompRaw_eq_stage`, finished by `homTr_id`. -/
theorem homCompRaw_eq_id_stage (C : CatSystem ι D) (hC : C.Coherent) {ip iq : ι}
    (xp : C.A ip) (xq : C.A iq)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ip) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xp)
    (h : homCompRaw C hC xp xq xp a f b g
        = homIncl C hC xp xp ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (C.F (D.refl ip) xp))) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N),
      homTr C xp xq a ⟨N, D.trans a.2.1 haN, D.trans a.2.2 haN⟩ haN f
        ≫ homTr C xq xp b ⟨N, D.trans b.2.1 hbN, D.trans b.2.2 hbN⟩ hbN g
      = Cat.id (C.F (D.trans a.2.1 haN) xp) := by
  obtain ⟨N, haN, hbN, _, key⟩ := homCompRaw_eq_stage C hC xp xq xp a f b g
    ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (C.F (D.refl ip) xp)) h
  rw [homTr_id C] at key
  exact ⟨N, haN, hbN, key⟩

/-- `castHom` reflects isomorphisms (it's a transport along object equalities). -/
theorem isIso_of_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) (h : IsIso (castHom hX hY m)) : IsIso m := by
  subst hX; subst hY; exact h

/-- **Iso reflection** (converse of `colimHom_isIso_of_rep`): if `homIncl a f₀` is an
    isomorphism in `colimitCat`, then its stage germ `f₀` becomes an isomorphism after
    transition to some stage `L`.  `Quotient.inductionOn` the colimit inverse to a stage
    germ `g₀`; the two iso equations reduce (via `homCompRaw_eq_id_stage`) to stage
    identities at stages `N1, N2`; bound them to a common `L` and transport both, so
    `homTr f₀` and `homTr g₀` are mutually inverse at `L`; `isIso_of_castHom` strips the
    `homTr` cast to leave `IsIso (functF.map f₀)`. -/
theorem colimHom_isIso_reflects (C : CatSystem ι D) (hC : C.Coherent) {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (hiso : @IsIso C.Obj (colimitCat C hC) A B
      (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀)) :
    ∃ (L : ι) (hL : D.le a.1 L), IsIso ((C.functF hL).map f₀) := by
  letI : Cat C.Obj := colimitCat C hC
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  obtain ⟨ginv, hl, hr⟩ := hiso
  revert hl hr
  refine Quotient.inductionOn ginv (fun rep => ?_)
  obtain ⟨b, g₀⟩ := rep
  intro hl hr
  have hl' : homCompRaw C hC xA xB xA a f₀ b g₀
      = homIncl C hC xA xA ⟨(colimOut C A).1, D.refl _, D.refl _⟩
          (Cat.id (C.F (D.refl (colimOut C A).1) xA)) := hl
  have hr' : homCompRaw C hC xB xA xB b g₀ a f₀
      = homIncl C hC xB xB ⟨(colimOut C B).1, D.refl _, D.refl _⟩
          (Cat.id (C.F (D.refl (colimOut C B).1) xB)) := hr
  obtain ⟨N1, haN1, hbN1, eq1⟩ := homCompRaw_eq_id_stage C hC xA xB a f₀ b g₀ hl'
  obtain ⟨N2, hbN2, haN2, eq2⟩ := homCompRaw_eq_id_stage C hC xB xA b g₀ a f₀ hr'
  obtain ⟨L, hN1L, hN2L⟩ := D.bound N1 N2
  have haL : D.le a.1 L := D.trans haN1 hN1L
  have hbL : D.le b.1 L := D.trans hbN1 hN1L
  -- transport both stage identities to the common stage `L`
  have eq1L : homTr C xA xB a ⟨L, D.trans a.2.1 haL, D.trans a.2.2 haL⟩ haL f₀
      ≫ homTr C xB xA b ⟨L, D.trans b.2.1 hbL, D.trans b.2.2 hbL⟩ hbL g₀
      = Cat.id (C.F (D.trans a.2.1 haL) xA) := by
    have t := congrArg
      (homTr C xA xA ⟨N1, D.trans a.2.1 haN1, D.trans a.2.1 haN1⟩
        ⟨L, D.trans (D.trans a.2.1 haN1) hN1L, D.trans (D.trans a.2.1 haN1) hN1L⟩ hN1L) eq1
    rw [homTr_comp C, ← homTr_trans C hC, ← homTr_trans C hC, homTr_id C] at t
    exact t
  have eq2L : homTr C xB xA b ⟨L, D.trans b.2.1 hbL, D.trans b.2.2 hbL⟩ hbL g₀
      ≫ homTr C xA xB a ⟨L, D.trans a.2.1 haL, D.trans a.2.2 haL⟩ haL f₀
      = Cat.id (C.F (D.trans b.2.1 hbL) xB) := by
    have t := congrArg
      (homTr C xB xB ⟨N2, D.trans b.2.1 hbN2, D.trans b.2.1 hbN2⟩
        ⟨L, D.trans (D.trans b.2.1 hbN2) hN2L, D.trans (D.trans b.2.1 hbN2) hN2L⟩ hN2L) eq2
    rw [homTr_comp C, ← homTr_trans C hC, ← homTr_trans C hC, homTr_id C] at t
    exact t
  have hisoL : IsIso (homTr C xA xB a ⟨L, D.trans a.2.1 haL, D.trans a.2.2 haL⟩ haL f₀) :=
    ⟨homTr C xB xA b ⟨L, D.trans b.2.1 hbL, D.trans b.2.2 hbL⟩ hbL g₀, eq1L, eq2L⟩
  exact ⟨L, haL, isIso_of_castHom (C.F_trans a.2.1 haL xA).symm (C.F_trans a.2.2 haL xB).symm
    ((C.functF haL).map f₀) hisoL⟩

/-- `castHom` carries monos to monos (transport along object equalities). -/
theorem mono_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) (h : Mono m) : Mono (castHom hX hY m) := by
  subst hX; subst hY; exact h

/-- `castHom` carries covers to covers (transport along object equalities). -/
theorem cover_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) (h : Cover m) : Cover (castHom hX hY m) := by
  subst hX; subst hY; exact h

/-- **Cover preservation:** if the stage germ `f₀` is a cover at *every* stage it is
    transported to (`hcov`), then `homIncl a f₀` is a cover in `colimitCat`.  Given a
    `colimitCat` mono `m` factoring `homIncl a f₀` through `g`, reflect `m, g` to stage
    reps; `homCompRaw_eq_stage` brings the factorization `g₀ ≫ m₀ = f₀` to a common
    stage `N`; mono reflection makes `m₀` monic at `N`, and the stage cover `f₀` (via
    `hcov`) forces `m₀` to be a stage iso (`monic_cover_iso`); iso preservation
    (`colimHom_isIso_of_rep`) + `homIncl_compat` lift that back to `IsIso m`. -/
theorem colimHom_cover_of_rep (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (hcov : ∀ (L : ι) (haL : D.le a.1 L), Cover ((C.functF haL).map f₀)) :
    @Cover C.Obj (colimitCat C hC) A B (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀) := by
  letI : Cat C.Obj := colimitCat C hC
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  intro Cobj m g hm hgm
  let xC := (colimOut C Cobj).2
  revert hm hgm
  refine Quotient.inductionOn₂ m g (fun mrep grep => ?_)
  obtain ⟨bm, m₀⟩ := mrep
  obtain ⟨bg, g₀⟩ := grep
  intro hm hgm
  -- bring the factorization `g₀ ≫ m₀ = f₀` to a common stage `N`
  have hgm' : homCompRaw C hC xA xC xB bg g₀ bm m₀ = homIncl C hC xA xB a f₀ := hgm
  obtain ⟨N, hgN, hmN, hfN, eqN⟩ := homCompRaw_eq_stage C hC xA xC xB bg g₀ bm m₀ a f₀ hgm'
  -- `m₀` is monic at `N` (mono reflection); `f₀` is a cover at `N` (`hcov`)
  have hm_map : Mono ((C.functF hmN).map m₀) :=
    fun {W} u v huv => colimHom_mono_reflects C hC hfaith bm m₀ hm hmN W u v huv
  have hm_N : Mono (homTr C xC xB bm ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩ hmN m₀) :=
    mono_castHom _ _ _ hm_map
  have hcov_N : Cover (homTr C xA xB a ⟨N, D.trans a.2.1 hfN, D.trans a.2.2 hfN⟩ hfN f₀) :=
    cover_castHom _ _ _ (hcov N hfN)
  -- the stage mono `m₀ @ N` factors the stage cover `f₀ @ N`, so it is a stage iso
  have hiso_mN : IsIso (homTr C xC xB bm ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩ hmN m₀) :=
    hcov_N _ _ hm_N eqN
  obtain ⟨n_N, hn1, hn2⟩ := hiso_mN
  -- lift the stage iso to `colimitCat` and absorb the push
  have hlift := colimHom_isIso_of_rep C hC ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩
    (homTr C xC xB bm ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩ hmN m₀) n_N hn1 hn2
  rwa [homIncl_compat C hC xC xB hmN m₀] at hlift

/-- A witness that the `colimOut` representatives of `objIncl i x` and `objIncl i y`
    both agree with `x`, `y` at a common stage `K` — the data needed to transport a
    stage morphism `x ⟶ y` into a `colimitCat` morphism. -/
structure HioWitness (C : CatSystem ι D) {i : ι} (x y : C.A i) where
  K : ι
  hpx : D.le (colimOut C (C.objIncl i x)).1 K
  hpy : D.le (colimOut C (C.objIncl i y)).1 K
  hix : D.le i K
  hgx : C.F hpx (colimOut C (C.objIncl i x)).2 = C.F hix x
  hgy : C.F hpy (colimOut C (C.objIncl i y)).2 = C.F hix y

/-- The transport of a stage morphism `g : x ⟶ y` into a germ
    `colimOut(objIncl i x) ⟶ colimOut(objIncl i y)` at the witness stage. -/
def HioWitness.germ {C : CatSystem ι D} {i : ι} {x y : C.A i} (w : HioWitness C x y)
    (g : x ⟶ y) :
    C.F w.hpx (colimOut C (C.objIncl i x)).2 ⟶ C.F w.hpy (colimOut C (C.objIncl i y)).2 :=
  castHom w.hgx.symm w.hgy.symm ((C.functF w.hix).map g)

/-- A chosen witness, materialized from the `colimOut` `Rel`s by `Classical.choose`. -/
noncomputable def hioWitness (C : CatSystem ι D) (hC : C.Coherent) {i : ι} (x y : C.A i) :
    HioWitness C x y := by
  classical
  let hxrel : Rel C.objSystem
      ⟨(colimOut C (C.objIncl i x)).1, (colimOut C (C.objIncl i x)).2⟩ ⟨i, x⟩ :=
    Quotient.exact (colimOut_spec C (C.objIncl i x))
  let hyrel : Rel C.objSystem
      ⟨(colimOut C (C.objIncl i y)).1, (colimOut C (C.objIncl i y)).2⟩ ⟨i, y⟩ :=
    Quotient.exact (colimOut_spec C (C.objIncl i y))
  let kx := Classical.choose hxrel
  let hipx_kx := Classical.choose (Classical.choose_spec hxrel)
  let hi_kx := Classical.choose (Classical.choose_spec (Classical.choose_spec hxrel))
  have hx_eq := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hxrel))
  let ky := Classical.choose hyrel
  let hipy_ky := Classical.choose (Classical.choose_spec hyrel)
  let hi_ky := Classical.choose (Classical.choose_spec (Classical.choose_spec hyrel))
  have hy_eq := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hyrel))
  dsimp only [CatSystem.objSystem] at hx_eq hy_eq
  let K := Classical.choose (D.bound kx ky)
  let hkxK := (Classical.choose_spec (D.bound kx ky)).1
  let hkyK := (Classical.choose_spec (D.bound kx ky)).2
  refine ⟨K, D.trans hipx_kx hkxK, D.trans hipy_ky hkyK, D.trans hi_kx hkxK, ?_, ?_⟩
  · calc C.F (D.trans hipx_kx hkxK) (colimOut C (C.objIncl i x)).2
        = C.F hkxK (C.F hipx_kx (colimOut C (C.objIncl i x)).2) := by rw [C.F_trans hipx_kx hkxK]
      _ = C.F hkxK (C.F hi_kx x) := by rw [hx_eq]
      _ = C.F (D.trans hi_kx hkxK) x := (C.F_trans hi_kx hkxK x).symm
  · calc C.F (D.trans hipy_ky hkyK) (colimOut C (C.objIncl i y)).2
        = C.F hkyK (C.F hipy_ky (colimOut C (C.objIncl i y)).2) := by rw [C.F_trans hipy_ky hkyK]
      _ = C.F hkyK (C.F hi_ky y) := by rw [hy_eq]
      _ = C.F (D.trans hi_kx hkxK) y := by
            rw [show D.trans hi_kx hkxK = D.trans hi_ky hkyK from Subsingleton.elim _ _,
                C.F_trans hi_ky hkyK y]

noncomputable def homInclObj (C : CatSystem ι D) (hC : C.Coherent) {i : ι} {x y : C.A i}
    (g : x ⟶ y) :
    HomColim C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2 :=
  homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
    ⟨(hioWitness C hC x y).K, (hioWitness C hC x y).hpx, (hioWitness C hC x y).hpy⟩
    ((hioWitness C hC x y).germ g)

/-- Pushing a witness germ to a higher stage `L` equals the canonical
    `functF`-map germ at `L` (transported by the rep equalities).  Mirrors the
    `hpush_gm`/`hpush_f` pattern. -/
theorem homInclObj_germ_push (C : CatSystem ι D) (hC : C.Coherent) {i : ι} {x y : C.A i}
    (g : x ⟶ y) (w : HioWitness C x y) (L : ι) (hwL : D.le w.K L)
    (Hcx : C.F (D.trans w.hix hwL) x = C.F (D.trans w.hpx hwL) (colimOut C (C.objIncl i x)).2)
    (Hcy : C.F (D.trans w.hix hwL) y = C.F (D.trans w.hpy hwL) (colimOut C (C.objIncl i y)).2) :
    homTr C (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
        ⟨w.K, w.hpx, w.hpy⟩ ⟨L, D.trans w.hpx hwL, D.trans w.hpy hwL⟩ hwL (w.germ g)
      = castHom Hcx Hcy ((C.functF (D.trans w.hix hwL)).map g) := by
  dsimp only [HioWitness.germ, homTr]
  rw [map_castHom (C.F hwL) (hT := C.functF hwL), castHom_castHom]
  exact castHom_heq_congr _ _ _ _ (hC.trans_map w.hix hwL g).symm

/-- **Representative-independence:** `homInclObj g` equals the germ `homIncl` at
    *any* witness `w` (not just the chosen one), since both reduce — via the push
    lemma + `homIncl_compat` — to the same canonical `functF`-map germ at a common
    stage (the proofs differ only proof-irrelevantly). -/
theorem homInclObj_eq (C : CatSystem ι D) (hC : C.Coherent) {i : ι} {x y : C.A i}
    (g : x ⟶ y) (w : HioWitness C x y) :
    homInclObj C hC g
      = homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
          ⟨w.K, w.hpx, w.hpy⟩ (w.germ g) := by
  obtain ⟨L, hw0L, hwL⟩ := D.bound (hioWitness C hC x y).K w.K
  have key : ∀ (v : HioWitness C x y) (hvL : D.le v.K L),
      homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
          ⟨v.K, v.hpx, v.hpy⟩ (v.germ g)
        = homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
          ⟨L, D.trans v.hpx hvL, D.trans v.hpy hvL⟩
          (castHom (by rw [C.F_trans v.hix hvL x, ← v.hgx, ← C.F_trans v.hpx hvL])
                   (by rw [C.F_trans v.hix hvL y, ← v.hgy, ← C.F_trans v.hpy hvL])
                   ((C.functF (D.trans v.hix hvL)).map g)) := by
    intro v hvL
    rw [← homInclObj_germ_push C hC g v L hvL _ _]
    exact (homIncl_compat C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
      (a := ⟨v.K, v.hpx, v.hpy⟩) (b := ⟨L, D.trans v.hpx hvL, D.trans v.hpy hvL⟩) hvL (v.germ g)).symm
  rw [show homInclObj C hC g
        = homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
            ⟨(hioWitness C hC x y).K, (hioWitness C hC x y).hpx, (hioWitness C hC x y).hpy⟩
            ((hioWitness C hC x y).germ g) from rfl,
      key (hioWitness C hC x y) hw0L, key w hwL]

/-- **`homInclObj` preserves composition** (functoriality of the stage inclusion).
    Build a common stage `L` where all three `colimOut` reps agree with `x,y,z`,
    apply `homInclObj_eq` to compute the three inclusions at shared witnesses there,
    reduce `colimComp` to `homCompRaw` at `L`, and match germs via `castHom_comp`+`map_comp`. -/
theorem homInclObj_comp (C : CatSystem ι D) (hC : C.Coherent) {i : ι} {x y z : C.A i}
    (g : x ⟶ y) (g' : y ⟶ z) :
    homInclObj C hC (g ≫ g') = colimComp C hC (homInclObj C hC g) (homInclObj C hC g') := by
  obtain ⟨sx, hpxsx, hisx, hxeq⟩ := Quotient.exact (colimOut_spec C (C.objIncl i x))
  obtain ⟨sy, hpysy, hisy, hyeq⟩ := Quotient.exact (colimOut_spec C (C.objIncl i y))
  obtain ⟨sz, hpzsz, hisz, hzeq⟩ := Quotient.exact (colimOut_spec C (C.objIncl i z))
  dsimp only [CatSystem.objSystem] at hxeq hyeq hzeq
  obtain ⟨sxy, hsx_sxy, hsy_sxy⟩ := D.bound sx sy
  obtain ⟨L, hsxy_L, hszL⟩ := D.bound sxy sz
  have hsxL : D.le sx L := D.trans hsx_sxy hsxy_L
  have hsyL : D.le sy L := D.trans hsy_sxy hsxy_L
  have hiL : D.le i L := D.trans hisx hsxL
  have hgxL : C.F (D.trans hpxsx hsxL) (colimOut C (C.objIncl i x)).2 = C.F hiL x := by
    rw [C.F_trans hpxsx hsxL, hxeq, ← C.F_trans hisx hsxL]
  have hgyL : C.F (D.trans hpysy hsyL) (colimOut C (C.objIncl i y)).2 = C.F hiL y := by
    rw [C.F_trans hpysy hsyL, hyeq,
        show hiL = D.trans hisy hsyL from Subsingleton.elim _ _, ← C.F_trans hisy hsyL]
  have hgzL : C.F (D.trans hpzsz hszL) (colimOut C (C.objIncl i z)).2 = C.F hiL z := by
    rw [C.F_trans hpzsz hszL, hzeq,
        show hiL = D.trans hisz hszL from Subsingleton.elim _ _, ← C.F_trans hisz hszL]
  let w_xy : HioWitness C x y := ⟨L, D.trans hpxsx hsxL, D.trans hpysy hsyL, hiL, hgxL, hgyL⟩
  let w_yz : HioWitness C y z := ⟨L, D.trans hpysy hsyL, D.trans hpzsz hszL, hiL, hgyL, hgzL⟩
  let w_xz : HioWitness C x z := ⟨L, D.trans hpxsx hsxL, D.trans hpzsz hszL, hiL, hgxL, hgzL⟩
  rw [homInclObj_eq C hC g w_xy, homInclObj_eq C hC g' w_yz, homInclObj_eq C hC (g ≫ g') w_xz]
  show homIncl C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i z)).2
      ⟨L, w_xz.hpx, w_xz.hpy⟩ (w_xz.germ (g ≫ g'))
    = homCompRaw C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i y)).2
        (colimOut C (C.objIncl i z)).2 ⟨L, w_xy.hpx, w_xy.hpy⟩ (w_xy.germ g)
        ⟨L, w_yz.hpx, w_yz.hpy⟩ (w_yz.germ g')
  rw [homCompRaw_eq_compAt C hC _ _ _ ⟨L, w_xy.hpx, w_xy.hpy⟩ (w_xy.germ g)
        ⟨L, w_yz.hpx, w_yz.hpy⟩ (w_yz.germ g') L (D.refl L) (D.refl L)]
  unfold compAt
  rw [homTr_refl C hC, homTr_refl C hC]
  -- Both sides are now `homIncl` of a germ at stage `L`; reduce the RHS composition
  -- of germs to a single germ via `castHom_comp` + `map_comp`, matching the LHS germ
  -- of `g ≫ g'`.  The two `UpperBound`s agree by proof irrelevance, so `rfl` closes it.
  dsimp only [HioWitness.germ]
  rw [castHom_comp, ← (C.functF hiL).map_comp]
/-- **The stage-inclusion `homInclObj` is injective** (faithful) when transitions
    are faithful: it shares the same `colimOut`-transport bound for `g`, `g'`, so
    `homIncl_injective` + cast-invertibility + `hfaith` strip back to `g = g'`. -/
theorem homInclObj_injective (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {i : ι} {x y : C.A i} (g g' : x ⟶ y)
    (h : homInclObj C hC g = homInclObj C hC g') : g = g' := by
  unfold homInclObj at h
  have hc := homIncl_injective C hC hfaith _ _ _ _ _ h
  exact hfaith _ _ _ (castHom_injective _ _ hc)

/-- **Mono preservation for the stage inclusion.**  If `g : x ⟶ y` is left-cancellable
    under every transition from `i` (`hcancel`), then `homInclObj g` is monic in
    `colimitCat`.  Apply `colimHom_mono_of_rep` to the chosen-witness germ; the germ is
    `castHom ∘ functF.map g`, so cast-slides (`cR`/`cT`) reduce its cancellation back to
    `hcancel` on `g`. -/
theorem homInclObj_mono_of_stage (C : CatSystem ι D) (hC : C.Coherent)
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hcancel : ∀ {j : ι} (hij : D.le i j) (z : C.A j) (u v : z ⟶ C.F hij x),
        u ≫ (C.functF hij).map g = v ≫ (C.functF hij).map g → u = v) :
    @Mono C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g) := by
  let w := hioWitness C hC x y
  have hcancel' : ∀ {j : ι} (hjk : D.le w.K j) (z : C.A j)
      (u v : z ⟶ C.F hjk (C.F w.hpx (colimOut C (C.objIncl i x)).2)),
      u ≫ (C.functF hjk).map (w.germ g) = v ≫ (C.functF hjk).map (w.germ g) → u = v := by
    intro j hjk z u v huv
    have e_x : C.F hjk (C.F w.hpx (colimOut C (C.objIncl i x)).2) = C.F (D.trans w.hix hjk) x :=
      (congrArg (C.F hjk) w.hgx).trans (C.F_trans w.hix hjk x).symm
    have e_y : C.F hjk (C.F w.hpy (colimOut C (C.objIncl i y)).2) = C.F (D.trans w.hix hjk) y :=
      (congrArg (C.F hjk) w.hgy).trans (C.F_trans w.hix hjk y).symm
    have hgerm_map : (C.functF hjk).map (w.germ g)
        = castHom e_x.symm e_y.symm ((C.functF (D.trans w.hix hjk)).map g) := by
      dsimp only [HioWitness.germ]
      rw [map_castHom (C.F hjk) (hT := C.functF hjk)]
      exact castHom_heq_congr _ _ e_x.symm e_y.symm (hC.trans_map w.hix hjk g).symm
    have cR : ∀ {P Q Q' R : C.A j} (he : Q = Q') (bb : P ⟶ Q) (cc : Q' ⟶ R),
        castHom rfl he bb ≫ cc = bb ≫ castHom he.symm rfl cc := by
      intro _ _ _ _ he bb cc; subst he; rfl
    have cT : ∀ {P Q R R' : C.A j} (he : R = R') (bb : P ⟶ Q) (cc : Q ⟶ R),
        castHom rfl he (bb ≫ cc) = bb ≫ castHom rfl he cc := by
      intro _ _ _ _ he bb cc; subst he; rfl
    rw [hgerm_map] at huv
    have hcc : (castHom rfl e_x u) ≫ (C.functF (D.trans w.hix hjk)).map g
        = (castHom rfl e_x v) ≫ (C.functF (D.trans w.hix hjk)).map g := by
      apply castHom_injective rfl e_y.symm
      rw [cT, cT, cR, cR]
      exact huv
    exact castHom_injective rfl e_x
      (hcancel (D.trans w.hix hjk) z (castHom rfl e_x u) (castHom rfl e_x v) hcc)
  rw [homInclObj_eq C hC g w]
  intro Z p q hpq
  exact colimHom_mono_of_rep (A := C.objIncl i x) (B := C.objIncl i y) C hC
    ⟨w.K, w.hpx, w.hpy⟩ (w.germ g) hcancel' p q hpq

/-- **Iso preservation for the stage inclusion.**  A stage iso `g : x ⟶ y` (inverse
    `g'`) is carried to an iso `homInclObj g` in `colimitCat`.  The chosen-witness germ
    `w.germ g = castHom ∘ functF.map g`; the witness germ of `g'` at the *swapped* bound
    is its inverse (functoriality of `functF` + `castHom_comp` collapse both composites
    to `castHom ∘ functF.map (g ≫ g') = castHom ∘ functF.map id = id`), so
    `colimHom_isIso_of_rep` yields the colimit iso.  Dual to `homInclObj_isIso_reflects`. -/
theorem homInclObj_isIso_of_stage (C : CatSystem ι D) (hC : C.Coherent)
    {i : ι} {x y : C.A i} (g : x ⟶ y) (g' : y ⟶ x)
    (h1 : g ≫ g' = Cat.id x) (h2 : g' ≫ g = Cat.id y) :
    @IsIso C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g) := by
  let w := hioWitness C hC x y
  rw [homInclObj_eq C hC g w]
  -- inverse germ: `g'` transported at the swapped bound, with the witness rep-equalities
  refine colimHom_isIso_of_rep (A := C.objIncl i x) (B := C.objIncl i y) C hC
    ⟨w.K, w.hpx, w.hpy⟩ (w.germ g) (castHom w.hgy.symm w.hgx.symm ((C.functF w.hix).map g')) ?_ ?_
  · -- (w.germ g) ≫ (inverse germ) = id
    show castHom w.hgx.symm w.hgy.symm ((C.functF w.hix).map g)
        ≫ castHom w.hgy.symm w.hgx.symm ((C.functF w.hix).map g') = Cat.id _
    rw [castHom_comp, ← (C.functF w.hix).map_comp, h1, (C.functF w.hix).map_id, castHom_id]
  · show castHom w.hgy.symm w.hgx.symm ((C.functF w.hix).map g')
        ≫ castHom w.hgx.symm w.hgy.symm ((C.functF w.hix).map g) = Cat.id _
    rw [castHom_comp, ← (C.functF w.hix).map_comp, h2, (C.functF w.hix).map_id, castHom_id]

/-- **Cover preservation for the stage inclusion.**  If `g : x ⟶ y` is a cover that
    stays a cover under *every* transition from `i` (`hcov`), then `homInclObj g` is a
    cover in `colimitCat`.  Apply `colimHom_cover_of_rep` to the chosen-witness germ:
    pushing it to a stage `L` gives `castHom ∘ functF.map g` (over `D.trans w.hix L`),
    so `cover_castHom` reduces the per-stage cover obligation to `hcov`.  Dual to
    `homInclObj_cover_reflects`; with per-stage cover-stability this lifts a stage cover
    to the colimit (item (2) in the `hcanon` residual). -/
theorem homInclObj_cover_of_stage (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hcov : ∀ {j : ι} (hij : D.le i j), Cover ((C.functF hij).map g)) :
    @Cover C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g) := by
  let w := hioWitness C hC x y
  rw [homInclObj_eq C hC g w]
  have hcov' : ∀ (L : ι) (hwL : D.le w.K L), Cover ((C.functF hwL).map (w.germ g)) := by
    intro L hwL
    -- the germ pushed to `L` is `castHom .. (functF (w.hix ≫ L)).map g`; cover_castHom + hcov
    have e_x : C.F hwL (C.F w.hpx (colimOut C (C.objIncl i x)).2) = C.F (D.trans w.hix hwL) x :=
      (congrArg (C.F hwL) w.hgx).trans (C.F_trans w.hix hwL x).symm
    have e_y : C.F hwL (C.F w.hpy (colimOut C (C.objIncl i y)).2) = C.F (D.trans w.hix hwL) y :=
      (congrArg (C.F hwL) w.hgy).trans (C.F_trans w.hix hwL y).symm
    have hgerm_map : (C.functF hwL).map (w.germ g)
        = castHom e_x.symm e_y.symm ((C.functF (D.trans w.hix hwL)).map g) := by
      dsimp only [HioWitness.germ]
      rw [map_castHom (C.F hwL) (hT := C.functF hwL)]
      exact castHom_heq_congr _ _ e_x.symm e_y.symm (hC.trans_map w.hix hwL g).symm
    rw [hgerm_map]
    -- `apply` (not `exact …  _`) so Lean resolves `cover_castHom`'s `m` metavar before
    -- the `Cover`-fold unification (a bare `_` leaves the result type η-expanded).
    apply cover_castHom e_x.symm e_y.symm
    exact hcov (D.trans w.hix hwL)
  apply colimHom_cover_of_rep (A := C.objIncl i x) (B := C.objIncl i y) C hC hfaith
    ⟨w.K, w.hpx, w.hpy⟩ (w.germ g)
  exact hcov'

/-- **Iso reflection for the stage inclusion.**  If `homInclObj g` is an isomorphism in
    `colimitCat` and transitions are conservative (`hcons`), then `g` is an isomorphism.
    `colimHom_isIso_reflects` gives a stage `L` where `functF.map` of the witness germ is
    iso; the germ is `castHom ∘ functF.map g`, so `isIso_of_castHom` leaves
    `IsIso (functF.map g)`, which `hcons` reflects to `IsIso g`. -/
theorem homInclObj_isIso_reflects (C : CatSystem ι D) (hC : C.Coherent)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hiso : @IsIso C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g)) :
    IsIso g := by
  let w := hioWitness C hC x y
  rw [homInclObj_eq C hC g w] at hiso
  obtain ⟨L, hL, hisoL⟩ := colimHom_isIso_reflects (A := C.objIncl i x) (B := C.objIncl i y) C hC
    ⟨w.K, w.hpx, w.hpy⟩ (w.germ g) hiso
  have e_x : C.F hL (C.F w.hpx (colimOut C (C.objIncl i x)).2) = C.F (D.trans w.hix hL) x :=
    (congrArg (C.F hL) w.hgx).trans (C.F_trans w.hix hL x).symm
  have e_y : C.F hL (C.F w.hpy (colimOut C (C.objIncl i y)).2) = C.F (D.trans w.hix hL) y :=
    (congrArg (C.F hL) w.hgy).trans (C.F_trans w.hix hL y).symm
  have hgerm_map : (C.functF hL).map (w.germ g)
      = castHom e_x.symm e_y.symm ((C.functF (D.trans w.hix hL)).map g) := by
    dsimp only [HioWitness.germ]
    rw [map_castHom (C.F hL) (hT := C.functF hL)]
    exact castHom_heq_congr _ _ e_x.symm e_y.symm (hC.trans_map w.hix hL g).symm
  rw [hgerm_map] at hisoL
  exact hcons (D.trans w.hix hL) g (isIso_of_castHom _ _ _ hisoL)

/-- **Cover reflection for the stage inclusion.**  If `homInclObj g` is a cover in
    `colimitCat` (with transitions preserving monos `hmono` and conservative `hcons`),
    then `g` is a cover in its stage.  A stage mono `m'` factoring `g` includes to a
    `colimitCat` mono `homInclObj m'` (preservation, via `hmono`) factoring `homInclObj g`
    (functoriality `homInclObj_comp`); the colimit cover forces it iso, and iso reflection
    (`homInclObj_isIso_reflects`, via `hcons`) brings the iso back to the stage. -/
theorem homInclObj_cover_reflects (C : CatSystem ι D) (hC : C.Coherent)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Mono φ → Mono ((C.functF hij).map φ))
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hcov : @Cover C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g)) :
    Cover g := by
  intro C'' m' g' hm' hgm'
  -- include the stage mono/factor; preservation makes the inclusion a colimit mono
  have hM_mono : @Mono C.Obj (colimitCat C hC) (C.objIncl i C'') (C.objIncl i y)
      (homInclObj C hC m') :=
    homInclObj_mono_of_stage C hC m' (fun {j} hij z u v huv => hmono hij m' hm' u v huv)
  have hfac : colimComp C hC (homInclObj C hC g') (homInclObj C hC m') = homInclObj C hC g := by
    rw [← homInclObj_comp C hC g' m', hgm']
  have hMiso : @IsIso C.Obj (colimitCat C hC) (C.objIncl i C'') (C.objIncl i y)
      (homInclObj C hC m') :=
    hcov (homInclObj C hC m') (homInclObj C hC g') hM_mono hfac
  exact homInclObj_isIso_reflects C hC hcons m' hMiso

/-- **Cover reflection** (colimOut-rep form, the form the assembly needs): if `homIncl a f₀` is a
    cover in `colimitCat` (transitions conservative `hcons`, mono-preserving `hmono`), then its stage
    germ `f₀` is a cover.  Mirrors `colimHom_mono_reflects`: a stage mono `m'` and factor `g'` of `f₀`
    are included as `colimitCat` maps `objIncl·t ⟶ B`, `A ⟶ objIncl·t` at the rep-agreement stage `s`
    of `objIncl·t`; their composite reduces (`homCompRaw_eq_compAt` + `homTr_refl` + `castHom_comp` +
    `map_comp`) to `homIncl a f₀`, so the colimit cover forces `M` iso; `colimHom_isIso_reflects` +
    `hcons` bring the iso back to `m'`. -/
theorem colimHom_cover_reflects (C : CatSystem ι D) (hC : C.Coherent)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso ((C.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Mono φ → Mono ((C.functF hij).map φ))
    {A B : C.Obj}
    (a : UpperBound D (colimOut C A).1 (colimOut C B).1)
    (f₀ : C.F a.2.1 (colimOut C A).2 ⟶ C.F a.2.2 (colimOut C B).2)
    (hcov : @Cover C.Obj (colimitCat C hC) A B
      (homIncl C hC (colimOut C A).2 (colimOut C B).2 a f₀)) :
    Cover f₀ := by
  letI : Cat C.Obj := colimitCat C hC
  intro t m' g' hm' hgm'
  let xA := (colimOut C A).2; let xB := (colimOut C B).2
  let T := C.objIncl a.1 t
  let rep_t := (colimOut C T).2
  obtain ⟨s, h_pt, h_ts, heqt⟩ := Quotient.exact (colimOut_spec C T)
  dsimp only [CatSystem.objSystem] at heqt
  -- heqt : C.F h_pt rep_t = C.F h_ts t
  have domcast : C.F h_ts (C.F a.2.1 xA) = C.F (D.trans a.2.1 h_ts) xA := (C.F_trans a.2.1 h_ts xA).symm
  have codcast : C.F h_ts (C.F a.2.2 xB) = C.F (D.trans a.2.2 h_ts) xB := (C.F_trans a.2.2 h_ts xB).symm
  let germ_G : C.F (D.trans a.2.1 h_ts) xA ⟶ C.F h_pt rep_t :=
    castHom domcast heqt.symm ((C.functF h_ts).map g')
  let germ_M : C.F h_pt rep_t ⟶ C.F (D.trans a.2.2 h_ts) xB :=
    castHom heqt.symm codcast ((C.functF h_ts).map m')
  let G : A ⟶ T := homIncl C hC xA rep_t ⟨s, D.trans a.2.1 h_ts, h_pt⟩ germ_G
  let M : T ⟶ B := homIncl C hC rep_t xB ⟨s, h_pt, D.trans a.2.2 h_ts⟩ germ_M
  -- M is a colimit mono (mono preservation of the germ, from `m'` mono via `hmono`)
  have hM_mono : @Mono C.Obj (colimitCat C hC) T B M := by
    have hcancel : ∀ {j : ι} (hj : D.le s j) (z : C.A j) (u v : z ⟶ C.F hj (C.F h_pt rep_t)),
        u ≫ (C.functF hj).map germ_M = v ≫ (C.functF hj).map germ_M → u = v := by
      intro j hj z u v huv
      have ed : C.F hj (C.F h_pt rep_t) = C.F (D.trans h_ts hj) t :=
        (congrArg (C.F hj) heqt).trans (C.F_trans h_ts hj t).symm
      have ec : C.F hj (C.F (D.trans a.2.2 h_ts) xB) = C.F (D.trans h_ts hj) (C.F a.2.2 xB) := by
        rw [← C.F_trans (D.trans a.2.2 h_ts) hj xB, ← C.F_trans a.2.2 (D.trans h_ts hj) xB]
      have hgm : (C.functF hj).map germ_M
          = castHom ed.symm ec.symm ((C.functF (D.trans h_ts hj)).map m') := by
        show (C.functF hj).map (castHom heqt.symm codcast ((C.functF h_ts).map m')) = _
        rw [map_castHom (C.F hj) (hT := C.functF hj)]
        exact castHom_heq_congr _ _ ed.symm ec.symm (hC.trans_map h_ts hj m').symm
      rw [hgm] at huv
      have cR : ∀ {P Q Q' R : C.A j} (he : Q = Q') (bb : P ⟶ Q) (cc : Q' ⟶ R),
          castHom rfl he bb ≫ cc = bb ≫ castHom he.symm rfl cc := by
        intro _ _ _ _ he bb cc; subst he; rfl
      have cT : ∀ {P Q R R' : C.A j} (he : R = R') (bb : P ⟶ Q) (cc : Q ⟶ R),
          castHom rfl he (bb ≫ cc) = bb ≫ castHom rfl he cc := by
        intro _ _ _ _ he bb cc; subst he; rfl
      have hcc : (castHom rfl ed u) ≫ (C.functF (D.trans h_ts hj)).map m'
          = (castHom rfl ed v) ≫ (C.functF (D.trans h_ts hj)).map m' := by
        apply castHom_injective rfl ec.symm
        rw [cT, cT, cR, cR]
        exact huv
      exact castHom_injective rfl ed
        (hmono (D.trans h_ts hj) m' hm' (castHom rfl ed u) (castHom rfl ed v) hcc)
    intro Z p q hpq
    exact colimHom_mono_of_rep (A := T) (B := B) C hC ⟨s, h_pt, D.trans a.2.2 h_ts⟩ germ_M hcancel p q hpq
  -- the composite `G ≫ M` reduces to `homIncl a f₀`
  have hfac : colimComp C hC G M = homIncl C hC xA xB a f₀ := by
    show homCompRaw C hC xA rep_t xB ⟨s, D.trans a.2.1 h_ts, h_pt⟩ germ_G ⟨s, h_pt, D.trans a.2.2 h_ts⟩ germ_M
       = homIncl C hC xA xB a f₀
    rw [homCompRaw_eq_compAt C hC xA rep_t xB ⟨s, D.trans a.2.1 h_ts, h_pt⟩ germ_G
          ⟨s, h_pt, D.trans a.2.2 h_ts⟩ germ_M s (D.refl s) (D.refl s)]
    unfold compAt
    rw [homTr_refl C hC, homTr_refl C hC]
    have hcomp : germ_G ≫ germ_M
        = homTr C xA xB a ⟨s, D.trans a.2.1 h_ts, D.trans a.2.2 h_ts⟩ h_ts f₀ := by
      show castHom domcast heqt.symm ((C.functF h_ts).map g')
          ≫ castHom heqt.symm codcast ((C.functF h_ts).map m') = _
      rw [castHom_comp, ← (C.functF h_ts).map_comp, hgm']
      rfl
    rw [hcomp]
    exact homIncl_compat C hC xA xB h_ts f₀
  -- colimit cover ⇒ M iso ⇒ (iso reflection + hcons) ⇒ m' iso
  have hMiso : @IsIso C.Obj (colimitCat C hC) T B M := hcov M G hM_mono hfac
  obtain ⟨L, hL, hisoL⟩ := colimHom_isIso_reflects (A := T) (B := B) C hC
    ⟨s, h_pt, D.trans a.2.2 h_ts⟩ germ_M hMiso
  -- hisoL : IsIso ((functF hL).map germ_M); strip to IsIso (functF.map m'), then hcons
  have ed : C.F hL (C.F h_pt rep_t) = C.F (D.trans h_ts hL) t :=
    (congrArg (C.F hL) heqt).trans (C.F_trans h_ts hL t).symm
  have ec : C.F hL (C.F (D.trans a.2.2 h_ts) xB) = C.F (D.trans h_ts hL) (C.F a.2.2 xB) := by
    rw [← C.F_trans (D.trans a.2.2 h_ts) hL xB, ← C.F_trans a.2.2 (D.trans h_ts hL) xB]
  have hgm : (C.functF hL).map germ_M
      = castHom ed.symm ec.symm ((C.functF (D.trans h_ts hL)).map m') := by
    show (C.functF hL).map (castHom heqt.symm codcast ((C.functF h_ts).map m')) = _
    rw [map_castHom (C.F hL) (hT := C.functF hL)]
    exact castHom_heq_congr _ _ ed.symm ec.symm (hC.trans_map h_ts hL m').symm
  rw [hgm] at hisoL
  exact hcons (D.trans h_ts hL) m' (isIso_of_castHom _ _ _ hisoL)

/-- **Generic comparison-iso from a product universal property.**  In a category
    with binary products, if a cone `(P, p₁, p₂)` over `A, B` is universal (`hup`:
    unique mediator for every competitor), then the canonical comparison
    `pair p₁ p₂ : P ⟶ A × B` is an isomorphism.  Purely formal: the inverse is the
    mediator of `(fst, snd)`; the two round-trips collapse by `pair_uniq` (on the
    `A × B` side) and the UP uniqueness (on the `P` side). -/
theorem isIso_of_product_up {𝒞 : Type w} [Cat.{w} 𝒞] [HasBinaryProducts 𝒞]
    {A B P : 𝒞} (p₁ : P ⟶ A) (p₂ : P ⟶ B)
    (hup : ∀ {Z : 𝒞} (f : Z ⟶ A) (g : Z ⟶ B),
      ∃ u : Z ⟶ P, (u ≫ p₁ = f ∧ u ≫ p₂ = g) ∧
        ∀ v : Z ⟶ P, v ≫ p₁ = f → v ≫ p₂ = g → v = u) :
    IsIso (pair p₁ p₂ : P ⟶ prod A B) := by
  obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ := hup (fst (A := A) (B := B)) (snd (A := A) (B := B))
  refine ⟨u, ?_, ?_⟩
  · obtain ⟨_, _, huniq⟩ := hup p₁ p₂
    have e1 : (pair p₁ p₂ ≫ u) ≫ p₁ = p₁ := by rw [Cat.assoc, hu₁, fst_pair]
    have e2 : (pair p₁ p₂ ≫ u) ≫ p₂ = p₂ := by rw [Cat.assoc, hu₂, snd_pair]
    rw [huniq (pair p₁ p₂ ≫ u) e1 e2, huniq (Cat.id P) (Cat.id_comp _) (Cat.id_comp _)]
  · have h1 : (u ≫ pair p₁ p₂) ≫ fst = fst (A := A) (B := B) := by rw [Cat.assoc, fst_pair, hu₁]
    have h2 : (u ≫ pair p₁ p₂) ≫ snd = snd (A := A) (B := B) := by rw [Cat.assoc, snd_pair, hu₂]
    rw [pair_uniq _ _ (u ≫ pair p₁ p₂) h1 h2, pair_fst_snd]

/-- **Two same-domain germs are a `MonicPair` in `colimitCat` when jointly
    cancellable under transitions** (joint dual of `colimHom_mono_of_rep`).  Both
    germs `f₀, f₁` share the domain rep `xP` at carrier `L`; if every pair of
    stage maps agreeing after `f₀` and after `f₁` is already equal (`hcancel`),
    then `(homIncl f₀, homIncl f₁)` is jointly left-cancellable.  Push the two
    competitors `s, t` to a common stage, where both leg-equations become stage
    equations, and apply `hcancel`. -/
theorem colimHom_monicPair_of_rep (C : CatSystem ι D) (hC : C.Coherent)
    {P A B : C.Obj} {L : ι}
    (hpd : D.le (colimOut C P).1 L) (hca : D.le (colimOut C A).1 L) (hcb : D.le (colimOut C B).1 L)
    (f₀ : C.F hpd (colimOut C P).2 ⟶ C.F hca (colimOut C A).2)
    (f₁ : C.F hpd (colimOut C P).2 ⟶ C.F hcb (colimOut C B).2)
    (hcancel : ∀ {j : ι} (hjk : D.le L j) (z : C.A j)
        (u v : z ⟶ C.F hjk (C.F hpd (colimOut C P).2)),
        u ≫ (C.functF hjk).map f₀ = v ≫ (C.functF hjk).map f₀ →
        u ≫ (C.functF hjk).map f₁ = v ≫ (C.functF hjk).map f₁ → u = v) :
    @MonicPair C.Obj (colimitCat C hC) P A B
      (homIncl C hC (colimOut C P).2 (colimOut C A).2 ⟨L, hpd, hca⟩ f₀)
      (homIncl C hC (colimOut C P).2 (colimOut C B).2 ⟨L, hpd, hcb⟩ f₁) := by
  letI : Cat C.Obj := colimitCat C hC
  let xP := (colimOut C P).2; let xA := (colimOut C A).2; let xB := (colimOut C B).2
  intro W
  refine Quotient.ind₂ (fun pr qr hf hs => ?_)
  obtain ⟨ap, p₀⟩ := pr
  obtain ⟨aq, q₀⟩ := qr
  let xW : C.A (colimOut C W).1 := (colimOut C W).2
  -- reduce both leg-equations to common-stage germ equations
  change homCompRaw C hC xW xP xA ap p₀ ⟨L, hpd, hca⟩ f₀
       = homCompRaw C hC xW xP xA aq q₀ ⟨L, hpd, hca⟩ f₀ at hf
  change homCompRaw C hC xW xP xB ap p₀ ⟨L, hpd, hcb⟩ f₁
       = homCompRaw C hC xW xP xB aq q₀ ⟨L, hpd, hcb⟩ f₁ at hs
  obtain ⟨P1, hapP1, haqP1⟩ := D.bound ap.1 aq.1
  obtain ⟨Q, hP1Q, hLQ⟩ := D.bound P1 L
  have hapQ : D.le ap.1 Q := D.trans hapP1 hP1Q
  have haqQ : D.le aq.1 Q := D.trans haqP1 hP1Q
  rw [homCompRaw_eq_compAt C hC xW xP xA ap p₀ ⟨L, hpd, hca⟩ f₀ Q hapQ hLQ,
      homCompRaw_eq_compAt C hC xW xP xA aq q₀ ⟨L, hpd, hca⟩ f₀ Q haqQ hLQ] at hf
  rw [homCompRaw_eq_compAt C hC xW xP xB ap p₀ ⟨L, hpd, hcb⟩ f₁ Q hapQ hLQ,
      homCompRaw_eq_compAt C hC xW xP xB aq q₀ ⟨L, hpd, hcb⟩ f₁ Q haqQ hLQ] at hs
  obtain ⟨Rf, hRfp, hRfq, hRfeq⟩ := Quotient.exact hf
  obtain ⟨Rs, hRsp, hRsq, hRseq⟩ := Quotient.exact hs
  dsimp only [homSystem] at hRfeq hRseq
  obtain ⟨Lf, hRfL, hRsL⟩ := D.bound Rf.1 Rs.1
  have keyf := congrArg (homTr C xW xA Rf ⟨Lf, D.trans Rf.2.1 hRfL, D.trans Rf.2.2 hRfL⟩ hRfL) hRfeq
  have keys := congrArg (homTr C xW xB Rs ⟨Lf, D.trans Rs.2.1 hRsL, D.trans Rs.2.2 hRsL⟩ hRsL) hRseq
  rw [← homTr_trans C hC, ← homTr_trans C hC] at keyf
  rw [← homTr_trans C hC, ← homTr_trans C hC] at keys
  rw [homTr_comp C, homTr_comp C] at keyf
  rw [homTr_comp C, homTr_comp C] at keys
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at keyf
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at keys
  -- push f₀ (via Rf) and f₁ (via Rs) to the common stage Lf
  have hLLf : D.le L Lf := D.trans hLQ (D.trans hRfp hRfL)
  have hiAL : D.le (colimOut C A).1 Lf := D.trans hca hLLf
  have hiBL : D.le (colimOut C B).1 Lf := D.trans hcb hLLf
  have hiPL : D.le (colimOut C P).1 Lf := D.trans hpd hLLf
  have hHcA : C.F hLLf (C.F hpd xP) = C.F hiPL xP := (C.F_trans hpd hLLf xP).symm
  have hHcA2 : C.F hLLf (C.F hca xA) = C.F hiAL xA := (C.F_trans hca hLLf xA).symm
  have hHcB2 : C.F hLLf (C.F hcb xB) = C.F hiBL xB := (C.F_trans hcb hLLf xB).symm
  have hpush_f0 : homTr C xP xA ⟨L, hpd, hca⟩ ⟨Lf, hiPL, hiAL⟩ hLLf f₀
      = castHom hHcA hHcA2 ((C.functF hLLf).map f₀) := rfl
  have hpush_f1 : homTr C xP xB ⟨L, hpd, hcb⟩ ⟨Lf, hiPL, hiBL⟩ hLLf f₁
      = castHom hHcA hHcB2 ((C.functF hLLf).map f₁) := rfl
  rw [hpush_f0] at keyf
  rw [hpush_f1] at keys
  have cR : ∀ {U V V' Wq : C.A Lf} (he : V = V') (b : U ⟶ V) (c : V' ⟶ Wq),
      castHom rfl he b ≫ c = b ≫ castHom he.symm rfl c := by
    intro _ _ _ _ he b c; subst he; rfl
  have cT : ∀ {U V Wq Wq' : C.A Lf} (he : Wq = Wq') (b : U ⟶ V) (c : V ⟶ Wq),
      castHom rfl he (b ≫ c) = b ≫ castHom rfl he c := by
    intro _ _ _ _ he b c; subst he; rfl
  have hbig : D.le ap.1 Lf := D.trans hapQ (D.trans hRfp hRfL)
  have hbig' : D.le aq.1 Lf := D.trans haqQ (D.trans hRfp hRfL)
  refine Quotient.sound ⟨⟨Lf, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩, hbig, hbig', ?_⟩
  dsimp only [homSystem]
  have hu := hcancel hLLf (C.F (D.trans ap.2.1 hbig) xW)
    (castHom rfl hHcA.symm (homTr C xW xP ap ⟨Lf, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩ hbig p₀))
    (castHom rfl hHcA.symm (homTr C xW xP aq ⟨Lf, D.trans aq.2.1 hbig', D.trans aq.2.2 hbig'⟩ hbig' q₀))
    (by
      rw [cR, cR]
      have hh := congrArg (castHom rfl hHcA2.symm) keyf
      rw [cT, cT, castHom_castHom] at hh
      exact hh)
    (by
      rw [cR, cR]
      have hh := congrArg (castHom rfl hHcB2.symm) keys
      rw [cT, cT, castHom_castHom] at hh
      exact hh)
  have hu2 := congrArg (castHom rfl hHcA) hu
  rw [castHom_castHom, castHom_castHom] at hu2
  exact hu2

/-- **`objIncl i` preserves binary products** (M3-cov hcanon ingredient (3) for
    products).  Given per-stage products (`hp`) and the transition-preservation
    hypotheses (`hpres`, `hpres_pair`) that build `colimitHasBinaryProducts`, the
    canonical comparison `objIncl i (a × b) ⟶ objIncl i a × objIncl i b` — i.e.
    `pair (homInclObj fst) (homInclObj snd)` — is an iso in `colimitCat`.

    PROOF (via `isIso_of_product_up`).  The cone `(objIncl(a×b), homInclObj fst,
    homInclObj snd)` is a universal product cone.  Push the competitor `f, g` and
    the chosen reps of `objIncl a`, `objIncl b`, `objIncl(a×b)` to one common stage
    `L ≥ i`; `hpres_pair` (transitions preserve the stage product) supplies the
    mediator germ `r`, and `homInclObj_eq` + `homCompRaw_eq_of_stage` reduce each
    projection-composite to `r ≫ functF.map fst = pL` (resp. snd).  Uniqueness is
    `colimHom_monicPair_of_rep` with `hpres` as the joint stage-cancellation. -/
theorem objIncl_preserves_products (C : CatSystem ι D) (hC : C.Coherent)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (i : ι) (a b : C.A i) :
    @IsIso C.Obj (colimitCat C hC) _ _
      (@pair C.Obj (colimitCat C hC) (colimitHasBinaryProducts C hC hp hpres hpres_pair)
        (C.objIncl i ((hp i).prod a b)) (C.objIncl i a) (C.objIncl i b)
        (homInclObj C hC ((hp i).fst (A := a) (B := b)))
        (homInclObj C hC ((hp i).snd (A := a) (B := b)))) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hpres hpres_pair
  -- abbreviations (`set` is a Mathlib tactic unavailable here; `let`s unfold by defeq).
  let P0 : C.A i := (hp i).prod a b
  let fstS : P0 ⟶ a := (hp i).fst
  let sndS : P0 ⟶ b := (hp i).snd
  let xa : C.A (colimOut C (C.objIncl i a)).1 := (colimOut C (C.objIncl i a)).2
  let xb : C.A (colimOut C (C.objIncl i b)).1 := (colimOut C (C.objIncl i b)).2
  let xprod : C.A (colimOut C (C.objIncl i P0)).1 := (colimOut C (C.objIncl i P0)).2
  -- fold the goal to use the abbreviations (so `rw [homInclObj_eq … fstS …]` matches)
  show @IsIso C.Obj (colimitCat C hC) _ _
    (@pair C.Obj (colimitCat C hC) (colimitHasBinaryProducts C hC hp hpres hpres_pair)
      (C.objIncl i P0) (C.objIncl i a) (C.objIncl i b)
      (homInclObj C hC fstS) (homInclObj C hC sndS))
  obtain ⟨ka, hpa, hia, heqa⟩ := Quotient.exact (colimOut_spec C (C.objIncl i a))
  obtain ⟨kb, hpb, hib, heqb⟩ := Quotient.exact (colimOut_spec C (C.objIncl i b))
  obtain ⟨kP, hpP, hiP, heqP⟩ := Quotient.exact (colimOut_spec C (C.objIncl i P0))
  dsimp only [CatSystem.objSystem] at heqa heqb heqP
  -- a common stage L ≥ i, ka, kb, kP
  obtain ⟨m1, hkam, hkbm⟩ := D.bound ka kb
  obtain ⟨L, hm1L, hkPL⟩ := D.bound m1 kP
  have hkaL : D.le ka L := D.trans hkam hm1L
  have hkbL : D.le kb L := D.trans hkbm hm1L
  have hiL : D.le i L := D.trans hia hkaL
  have hgaL : C.F (D.trans hpa hkaL) xa = C.F hiL a := by
    rw [C.F_trans hpa hkaL, heqa, ← C.F_trans hia hkaL]
  have hgbL : C.F (D.trans hpb hkbL) xb = C.F hiL b := by
    rw [C.F_trans hpb hkbL, heqb, show hiL = D.trans hib hkbL from Subsingleton.elim _ _,
        ← C.F_trans hib hkbL]
  have hgPL : C.F (D.trans hpP hkPL) xprod = C.F hiL P0 := by
    rw [C.F_trans hpP hkPL, heqP, show hiL = D.trans hiP hkPL from Subsingleton.elim _ _,
        ← C.F_trans hiP hkPL]
  let wF : HioWitness C P0 a := ⟨L, D.trans hpP hkPL, D.trans hpa hkaL, hiL, hgPL, hgaL⟩
  let wS : HioWitness C P0 b := ⟨L, D.trans hpP hkPL, D.trans hpb hkbL, hiL, hgPL, hgbL⟩
  refine isIso_of_product_up _ _ (fun {Z} f g => ?_)
  -- joint monicity of the two projections (uniqueness half)
  have hMP : @MonicPair C.Obj (colimitCat C hC) (C.objIncl i P0) (C.objIncl i a) (C.objIncl i b)
      (homInclObj C hC fstS) (homInclObj C hC sndS) := by
    rw [homInclObj_eq C hC fstS wF, homInclObj_eq C hC sndS wS]
    refine colimHom_monicPair_of_rep C hC (D.trans hpP hkPL) (D.trans hpa hkaL) (D.trans hpb hkbL)
      (wF.germ fstS) (wS.germ sndS) (fun {j} hjk z u v hu hv => ?_)
    -- reduce both germ maps to `castHom ∘ functF.map`, apply `hpres`
    have e_P : C.F hjk (C.F (D.trans hpP hkPL) xprod) = C.F (D.trans hiL hjk) P0 :=
      (congrArg (C.F hjk) hgPL).trans (C.F_trans hiL hjk P0).symm
    have e_a : C.F hjk (C.F (D.trans hpa hkaL) xa) = C.F (D.trans hiL hjk) a :=
      (congrArg (C.F hjk) hgaL).trans (C.F_trans hiL hjk a).symm
    have e_b : C.F hjk (C.F (D.trans hpb hkbL) xb) = C.F (D.trans hiL hjk) b :=
      (congrArg (C.F hjk) hgbL).trans (C.F_trans hiL hjk b).symm
    have hmapF : (C.functF hjk).map (wF.germ fstS)
        = castHom e_P.symm e_a.symm ((C.functF (D.trans hiL hjk)).map fstS) := by
      dsimp only [HioWitness.germ]
      rw [map_castHom (C.F hjk) (hT := C.functF hjk)]
      exact castHom_heq_congr _ _ e_P.symm e_a.symm (hC.trans_map hiL hjk fstS).symm
    have hmapS : (C.functF hjk).map (wS.germ sndS)
        = castHom e_P.symm e_b.symm ((C.functF (D.trans hiL hjk)).map sndS) := by
      dsimp only [HioWitness.germ]
      rw [map_castHom (C.F hjk) (hT := C.functF hjk)]
      exact castHom_heq_congr _ _ e_P.symm e_b.symm (hC.trans_map hiL hjk sndS).symm
    have cR : ∀ {P Q Q' R : C.A j} (he : Q = Q') (bb : P ⟶ Q) (cc : Q' ⟶ R),
        castHom rfl he bb ≫ cc = bb ≫ castHom he.symm rfl cc := by
      intro _ _ _ _ he bb cc; subst he; rfl
    have cT : ∀ {P Q R R' : C.A j} (he : R = R') (bb : P ⟶ Q) (cc : Q ⟶ R),
        castHom rfl he (bb ≫ cc) = bb ≫ castHom rfl he cc := by
      intro _ _ _ _ he bb cc; subst he; rfl
    rw [hmapF] at hu
    rw [hmapS] at hv
    have huu : (castHom rfl e_P u) ≫ (C.functF (D.trans hiL hjk)).map fstS
        = (castHom rfl e_P v) ≫ (C.functF (D.trans hiL hjk)).map fstS := by
      apply castHom_injective rfl e_a.symm; rw [cT, cT, cR, cR]; exact hu
    have hvv : (castHom rfl e_P u) ≫ (C.functF (D.trans hiL hjk)).map sndS
        = (castHom rfl e_P v) ≫ (C.functF (D.trans hiL hjk)).map sndS := by
      apply castHom_injective rfl e_b.symm; rw [cT, cT, cR, cR]; exact hv
    exact castHom_injective rfl e_P
      (hpres (D.trans hiL hjk) a b z (castHom rfl e_P u) (castHom rfl e_P v) huu hvv)
  -- existence half: build the mediator at stage L
  refine Quotient.inductionOn f (fun ⟨af, fa⟩ => ?_)
  refine Quotient.inductionOn g (fun ⟨bg, ga⟩ => ?_)
  let z : C.A (colimOut C Z).1 := (colimOut C Z).2
  obtain ⟨m2, hafm, hbgm⟩ := D.bound af.1 bg.1
  obtain ⟨N, hm2N, hLN⟩ := D.bound m2 L
  have hafN : D.le af.1 N := D.trans hafm hm2N
  have hbgN : D.le bg.1 N := D.trans hbgm hm2N
  have hiN : D.le i N := D.trans hiL hLN
  -- rep-agreements at N
  have hgaN : C.F (D.trans (D.trans hpa hkaL) hLN) xa = C.F hiN a := by
    rw [C.F_trans (D.trans hpa hkaL) hLN, hgaL, ← C.F_trans hiL hLN]
  have hgbN : C.F (D.trans (D.trans hpb hkbL) hLN) xb = C.F hiN b := by
    rw [C.F_trans (D.trans hpb hkbL) hLN, hgbL, ← C.F_trans hiL hLN]
  have hgPN : C.F (D.trans (D.trans hpP hkPL) hLN) xprod = C.F hiN P0 := by
    rw [C.F_trans (D.trans hpP hkPL) hLN, hgPL, ← C.F_trans hiL hLN]
  -- witnesses at N
  let wFN : HioWitness C P0 a :=
    ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans (D.trans hpa hkaL) hLN, hiN, hgPN, hgaN⟩
  let wSN : HioWitness C P0 b :=
    ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans (D.trans hpb hkbL) hLN, hiN, hgPN, hgbN⟩
  -- competitor germs at N
  let fL_raw : C.F (D.trans af.2.1 hafN) z ⟶ C.F (D.trans af.2.2 hafN) xa :=
    homTr C z xa af ⟨N, D.trans af.2.1 hafN, D.trans af.2.2 hafN⟩ hafN fa
  let gL_raw : C.F (D.trans bg.2.1 hbgN) z ⟶ C.F (D.trans bg.2.2 hbgN) xb :=
    homTr C z xb bg ⟨N, D.trans bg.2.1 hbgN, D.trans bg.2.2 hbgN⟩ hbgN ga
  have hzeq : C.F (D.trans bg.2.1 hbgN) z = C.F (D.trans af.2.1 hafN) z :=
    C.F_proof_irrel _ _ z
  have hfa_tgt : C.F (D.trans af.2.2 hafN) xa = C.F hiN a := by
    rw [show D.trans af.2.2 hafN = D.trans (D.trans hpa hkaL) hLN from Subsingleton.elim _ _]
    exact hgaN
  have hgb_tgt : C.F (D.trans bg.2.2 hbgN) xb = C.F hiN b := by
    rw [show D.trans bg.2.2 hbgN = D.trans (D.trans hpb hkbL) hLN from Subsingleton.elim _ _]
    exact hgbN
  let pL : C.F (D.trans af.2.1 hafN) z ⟶ C.F hiN a := castHom rfl hfa_tgt fL_raw
  let qL : C.F (D.trans af.2.1 hafN) z ⟶ C.F hiN b := castHom hzeq hgb_tgt gL_raw
  obtain ⟨r, hr_fst, hr_snd⟩ := hpres_pair hiN a b (C.F (D.trans af.2.1 hafN) z) pL qL
  let rgerm : C.F (D.trans af.2.1 hafN) z ⟶ C.F (D.trans (D.trans hpP hkPL) hLN) xprod :=
    castHom rfl hgPN.symm r
  let u : Z ⟶ C.objIncl i P0 :=
    homIncl C hC z xprod ⟨N, D.trans af.2.1 hafN, D.trans (D.trans hpP hkPL) hLN⟩ rgerm
  have hux : u ≫ homInclObj C hC fstS = Quotient.mk _ ⟨af, fa⟩ := by
    show colimComp C hC u (homInclObj C hC fstS) = _
    rw [homInclObj_eq C hC fstS wFN]
    show homCompRaw C hC z xprod xa ⟨N, D.trans af.2.1 hafN, D.trans (D.trans hpP hkPL) hLN⟩ rgerm
        ⟨wFN.K, wFN.hpx, wFN.hpy⟩ (wFN.germ fstS)
      = homIncl C hC z xa af fa
    refine homCompRaw_eq_of_stage C hC z xprod xa
      ⟨N, D.trans af.2.1 hafN, D.trans (D.trans hpP hkPL) hLN⟩ rgerm
      ⟨wFN.K, wFN.hpx, wFN.hpy⟩ (wFN.germ fstS) af fa N (D.refl N) (D.refl N) hafN ?_
    rw [homTr_refl C hC, homTr_refl C hC]
    show rgerm ≫ castHom hgPN.symm hgaN.symm ((C.functF hiN).map fstS)
      = homTr C z xa af ⟨N, D.trans af.2.1 hafN, D.trans af.2.2 hafN⟩ hafN fa
    show castHom rfl hgPN.symm r ≫ castHom hgPN.symm hgaN.symm ((C.functF hiN).map fstS) = fL_raw
    rw [castHom_comp]
    rw [show r ≫ (C.functF hiN).map fstS = pL from hr_fst]
    show castHom rfl hgaN.symm (castHom rfl hfa_tgt fL_raw) = fL_raw
    rw [castHom_castHom]
    exact castHom_of_heq rfl _ HEq.rfl
  have huy : u ≫ homInclObj C hC sndS = Quotient.mk _ ⟨bg, ga⟩ := by
    show colimComp C hC u (homInclObj C hC sndS) = _
    rw [homInclObj_eq C hC sndS wSN]
    show homCompRaw C hC z xprod xb ⟨N, D.trans af.2.1 hafN, D.trans (D.trans hpP hkPL) hLN⟩ rgerm
        ⟨wSN.K, wSN.hpx, wSN.hpy⟩ (wSN.germ sndS)
      = homIncl C hC z xb bg ga
    refine homCompRaw_eq_of_stage C hC z xprod xb
      ⟨N, D.trans af.2.1 hafN, D.trans (D.trans hpP hkPL) hLN⟩ rgerm
      ⟨wSN.K, wSN.hpx, wSN.hpy⟩ (wSN.germ sndS) bg ga N (D.refl N) (D.refl N) hbgN ?_
    rw [homTr_refl C hC, homTr_refl C hC]
    show castHom rfl hgPN.symm r ≫ castHom hgPN.symm hgbN.symm ((C.functF hiN).map sndS)
      = homTr C z xb bg ⟨N, D.trans bg.2.1 hbgN, D.trans bg.2.2 hbgN⟩ hbgN ga
    rw [castHom_comp]
    rw [show r ≫ (C.functF hiN).map sndS = qL from hr_snd]
    show castHom rfl hgbN.symm (castHom hzeq hgb_tgt gL_raw) = gL_raw
    rw [castHom_castHom]
    exact castHom_of_heq hzeq _ HEq.rfl
  -- assemble: mediator `u`, its two factorisations, uniqueness via `hMP`
  exact ⟨u, ⟨hux, huy⟩, fun v hv₁ hv₂ => hMP v u (hv₁.trans hux.symm) (hv₂.trans huy.symm)⟩

/-- **`objIncl i` preserves equalizers** (M3-cov hcanon ingredient (3) for
    equalizers).  Given per-stage equalizers (`he`) and the transition-preservation
    hypotheses (`hepres`, `hepres_lift`) that build `colimitHasEqualizers`, the
    `objIncl i`-image of the stage equalizer cone of a parallel pair `f g : a ⟶ b`
    — namely `(objIncl i (eqObj f g), homInclObj (eqMap f g))` over
    `(homInclObj f, homInclObj g)` — is an equalizer cone in `colimitCat`.

    PROOF (mirror of `objIncl_preserves_products`).  The cone equalizes by
    `homInclObj_comp` + `eqMap_eq`.  For the universal property: a competitor `d`
    with `d.map ≫ homInclObj f = d.map ≫ homInclObj g` is pushed (together with the
    chosen reps of `objIncl i a, b` and `objIncl i (eqObj f g)`) to one common stage
    `N ≥ i`, where its leg-equation becomes a stage equation; `hepres_lift` supplies
    the mediator germ `r`, and `homInclObj_eq` + `homCompRaw_eq_of_stage` reduce the
    factorisation `u ≫ homInclObj (eqMap f g) = d.map` to `r ≫ functF.map (eqMap) =
    germ`.  Uniqueness is `homInclObj_mono_of_stage` with `hepres`. -/
theorem objIncl_preserves_equalizers (C : CatSystem ι D) (hC : C.Coherent)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (i : ι) {a b : C.A i} (f g : a ⟶ b) :
    @EqualizerCone.IsEqualizer C.Obj (colimitCat C hC)
      (C.objIncl i a) (C.objIncl i b) (homInclObj C hC f) (homInclObj C hC g)
      (@EqualizerCone.mk C.Obj (colimitCat C hC) _ _ (homInclObj C hC f) (homInclObj C hC g)
        (C.objIncl i (@eqObj _ _ (he i) a b f g))
        (homInclObj C hC (@eqMap _ _ (he i) a b f g))
        (by
          letI : Cat C.Obj := colimitCat C hC
          letI : HasEqualizers (C.A i) := he i
          show colimComp C hC (homInclObj C hC (eqMap f g)) (homInclObj C hC f)
             = colimComp C hC (homInclObj C hC (eqMap f g)) (homInclObj C hC g)
          rw [← homInclObj_comp C hC (eqMap f g) f, ← homInclObj_comp C hC (eqMap f g) g,
              eqMap_eq f g])) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasEqualizers (C.A i) := he i
  let Eobj : C.A i := eqObj f g
  let eS : Eobj ⟶ a := eqMap f g
  -- uniqueness: `homInclObj eS` is monic (`eqMap` is jointly cancellable via `hepres`)
  have hmono : @Mono C.Obj (colimitCat C hC) (C.objIncl i Eobj) (C.objIncl i a)
      (homInclObj C hC eS) :=
    homInclObj_mono_of_stage C hC eS
      (fun {j} hij z u v huv => hepres hij f g z u v huv)
  -- reps of `objIncl i a`, `objIncl i b` and `objIncl i Eobj`, aligned at a stage `L ≥ i`
  obtain ⟨ka, hpa, hia, heqa⟩ := Quotient.exact (colimOut_spec C (C.objIncl i a))
  obtain ⟨kb, hpb, hib, heqb⟩ := Quotient.exact (colimOut_spec C (C.objIncl i b))
  obtain ⟨kE, hpE, hiE, heqE⟩ := Quotient.exact (colimOut_spec C (C.objIncl i Eobj))
  dsimp only [CatSystem.objSystem] at heqa heqb heqE
  let xa : C.A (colimOut C (C.objIncl i a)).1 := (colimOut C (C.objIncl i a)).2
  let xb : C.A (colimOut C (C.objIncl i b)).1 := (colimOut C (C.objIncl i b)).2
  let xE : C.A (colimOut C (C.objIncl i Eobj)).1 := (colimOut C (C.objIncl i Eobj)).2
  obtain ⟨m1, hkam, hkbm⟩ := D.bound ka kb
  obtain ⟨L, hm1L, hkEL⟩ := D.bound m1 kE
  have hkaL : D.le ka L := D.trans hkam hm1L
  have hkbL : D.le kb L := D.trans hkbm hm1L
  have hiL : D.le i L := D.trans hia hkaL
  have hgaL : C.F (D.trans hpa hkaL) xa = C.F hiL a := by
    rw [C.F_trans hpa hkaL, heqa, ← C.F_trans hia hkaL]
  have hgbL : C.F (D.trans hpb hkbL) xb = C.F hiL b := by
    rw [C.F_trans hpb hkbL, heqb, show hiL = D.trans hib hkbL from Subsingleton.elim _ _,
        ← C.F_trans hib hkbL]
  have hgEL : C.F (D.trans hpE hkEL) xE = C.F hiL Eobj := by
    rw [C.F_trans hpE hkEL, heqE, show hiL = D.trans hiE hkEL from Subsingleton.elim _ _,
        ← C.F_trans hiE hkEL]
  intro d
  -- existence half: present `d.map` by a representative germ and push to a common stage
  refine Quotient.inductionOn d.map (motive := fun mm =>
    mm = d.map → ∃ u : d.dom ⟶ C.objIncl i Eobj,
      colimComp C hC u (homInclObj C hC eS) = d.map ∧
      ∀ v : d.dom ⟶ C.objIncl i Eobj, colimComp C hC v (homInclObj C hC eS) = d.map → v = u)
    (fun ⟨ad, dm⟩ hdrep => ?_) rfl
  let zz : C.A (colimOut C d.dom).1 := (colimOut C d.dom).2
  -- a first stage `N ≥ ad.1, L` to express the competitor and the two parallel germs
  obtain ⟨N, hadN, hLN⟩ := D.bound ad.1 L
  have hiN : D.le i N := D.trans hiL hLN
  have hgaN : C.F (D.trans (D.trans hpa hkaL) hLN) xa = C.F hiN a := by
    rw [C.F_trans (D.trans hpa hkaL) hLN, hgaL, ← C.F_trans hiL hLN]
  have hgbN : C.F (D.trans (D.trans hpb hkbL) hLN) xb = C.F hiN b := by
    rw [C.F_trans (D.trans hpb hkbL) hLN, hgbL, ← C.F_trans hiL hLN]
  let wfN : HioWitness C a b :=
    ⟨N, D.trans (D.trans hpa hkaL) hLN, D.trans (D.trans hpb hkbL) hLN, hiN, hgaN, hgbN⟩
  let wgN : HioWitness C a b :=
    ⟨N, D.trans (D.trans hpa hkaL) hLN, D.trans (D.trans hpb hkbL) hLN, hiN, hgaN, hgbN⟩
  -- reduce the competitor's leg-equation `d.eq` to a germ equation; `Quotient.exact`
  -- produces the working stage `M := R.1 ≥ N` where everything is built.
  have hde : homCompRaw C hC zz xa xb ad dm ⟨N, wfN.hpx, wfN.hpy⟩ (wfN.germ f)
      = homCompRaw C hC zz xa xb ad dm ⟨N, wgN.hpx, wgN.hpy⟩ (wgN.germ g) := by
    have h0 : colimComp C hC (Quotient.mk _ ⟨ad, dm⟩)
          (homIncl C hC xa xb ⟨N, wfN.hpx, wfN.hpy⟩ (wfN.germ f))
        = colimComp C hC (Quotient.mk _ ⟨ad, dm⟩)
          (homIncl C hC xa xb ⟨N, wgN.hpx, wgN.hpy⟩ (wgN.germ g)) := by
      rw [← homInclObj_eq C hC f wfN, ← homInclObj_eq C hC g wgN, hdrep]; exact d.eq
    exact h0
  rw [homCompRaw_eq_compAt C hC zz xa xb ad dm ⟨N, wfN.hpx, wfN.hpy⟩ (wfN.germ f)
        N hadN (D.refl N),
      homCompRaw_eq_compAt C hC zz xa xb ad dm ⟨N, wgN.hpx, wgN.hpy⟩ (wgN.germ g)
        N hadN (D.refl N)] at hde
  obtain ⟨R, hNR, hNR', hReq⟩ := Quotient.exact hde
  dsimp only [homSystem] at hReq
  let M : ι := R.1
  have hNM : D.le N M := hNR
  have hiM : D.le i M := D.trans hiN hNM
  have hadM : D.le ad.1 M := D.trans hadN hNM
  have hLM : D.le L M := D.trans hLN hNM
  -- rep-equalities at the working stage `M`
  have hgaM : C.F (D.trans (D.trans hpa hkaL) hLM) xa = C.F hiM a := by
    rw [C.F_trans (D.trans hpa hkaL) hLM, hgaL, ← C.F_trans hiL hLM]
  have hgbM : C.F (D.trans (D.trans hpb hkbL) hLM) xb = C.F hiM b := by
    rw [C.F_trans (D.trans hpb hkbL) hLM, hgbL, ← C.F_trans hiL hLM]
  have hgEM : C.F (D.trans (D.trans hpE hkEL) hLM) xE = C.F hiM Eobj := by
    rw [C.F_trans (D.trans hpE hkEL) hLM, hgEL, ← C.F_trans hiL hLM]
  let wEM : HioWitness C Eobj a :=
    ⟨M, D.trans (D.trans hpE hkEL) hLM, D.trans (D.trans hpa hkaL) hLM, hiM, hgEM, hgaM⟩
  -- competitor germ pushed to `M`, then cast to land in `C.F hiM a`
  let dM_raw : C.F (D.trans ad.2.1 hadM) zz ⟶ C.F (D.trans ad.2.2 hadM) xa :=
    homTr C zz xa ad ⟨M, D.trans ad.2.1 hadM, D.trans ad.2.2 hadM⟩ hadM dm
  have hda_tgt : C.F (D.trans ad.2.2 hadM) xa = C.F hiM a := by
    rw [show D.trans ad.2.2 hadM = D.trans (D.trans hpa hkaL) hLM from Subsingleton.elim _ _]
    exact hgaM
  let pL : C.F (D.trans ad.2.1 hadM) zz ⟶ C.F hiM a := castHom rfl hda_tgt dM_raw
  -- transport `hReq` to the equation `pL ≫ functF.map f = pL ≫ functF.map g` at `M`
  have key := congrArg
    (homTr C zz xb R ⟨M, D.trans R.2.1 (D.refl M), D.trans R.2.2 (D.refl M)⟩ (D.refl M)) hReq
  rw [← homTr_trans C hC, ← homTr_trans C hC] at key
  rw [homTr_comp C, homTr_comp C] at key
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at key
  -- the witness germs pushed from `N` to `M` are `castHom ∘ functF.map f` (resp. g) at `M`
  have HcfP : C.F (D.trans wfN.hix hNM) a = C.F (D.trans wfN.hpx hNM) xa :=
    by rw [show D.trans wfN.hix hNM = hiM from Subsingleton.elim _ _,
           show D.trans wfN.hpx hNM = D.trans (D.trans hpa hkaL) hLM from Subsingleton.elim _ _, hgaM]
  have HcfQ : C.F (D.trans wfN.hix hNM) b = C.F (D.trans wfN.hpy hNM) xb :=
    by rw [show D.trans wfN.hix hNM = hiM from Subsingleton.elim _ _,
           show D.trans wfN.hpy hNM = D.trans (D.trans hpb hkbL) hLM from Subsingleton.elim _ _, hgbM]
  have hpush_f := homInclObj_germ_push C hC f wfN M hNM HcfP HcfQ
  have hpush_g := homInclObj_germ_push C hC g wgN M hNM HcfP HcfQ
  rw [hpush_f] at key
  rw [hpush_g] at key
  -- `key` now equates two composites `dM_raw ≫ castHom HcfP HcfQ (functF.map f/g)` at `M`.
  -- push both codomains from `xb` to `b` (via `hgbM`), then slide the casts to extract
  -- the clean `pL`-cancellation `pL ≫ functF.map f = pL ≫ functF.map g`.
  have cR : ∀ {U V V' Wq : C.A M} (he : V = V') (aa : U ⟶ V) (bb : V' ⟶ Wq),
      castHom rfl he aa ≫ bb = aa ≫ castHom he.symm rfl bb := by
    intro _ _ _ _ he aa bb; subst he; rfl
  have cT : ∀ {U V Wq Wq' : C.A M} (he : Wq = Wq') (aa : U ⟶ V) (bb : V ⟶ Wq),
      castHom rfl he (aa ≫ bb) = aa ≫ castHom rfl he bb := by
    intro _ _ _ _ he aa bb; subst he; rfl
  have key2 := congrArg (castHom rfl hgbM) key
  rw [cT, cT, castHom_castHom, castHom_castHom] at key2
  -- key2 : dM_raw ≫ castHom HcfP (HcfQ.trans hgbM) (functF f) = … (functF g)
  have hk : pL ≫ (C.functF hiM).map f = pL ≫ (C.functF hiM).map g := by
    show castHom rfl hda_tgt dM_raw ≫ (C.functF hiM).map f
       = castHom rfl hda_tgt dM_raw ≫ (C.functF hiM).map g
    rw [cR hda_tgt, cR hda_tgt]
    -- both sides: `dM_raw ≫ castHom hda_tgt.symm rfl (functF.map _)`, defeq to `key2`'s legs
    have hslide : ∀ (h : a ⟶ b),
        castHom hda_tgt.symm rfl ((C.functF hiM).map h)
          = castHom HcfP (HcfQ.trans hgbM) ((C.functF hiM).map h) := by
      intro h
      exact castHom_of_heq _ _ (heq_castHom HcfP (HcfQ.trans hgbM) ((C.functF hiM).map h)).symm
    rw [hslide f, hslide g]
    exact key2
  obtain ⟨r, hr⟩ := hepres_lift hiM f g (C.F (D.trans ad.2.1 hadM) zz) pL hk
  let rgerm : C.F (D.trans ad.2.1 hadM) zz ⟶ C.F (D.trans (D.trans hpE hkEL) hLM) xE :=
    castHom rfl hgEM.symm r
  let u : d.dom ⟶ C.objIncl i Eobj :=
    homIncl C hC zz xE ⟨M, D.trans ad.2.1 hadM, D.trans (D.trans hpE hkEL) hLM⟩ rgerm
  have hux : colimComp C hC u (homInclObj C hC eS) = d.map := by
    rw [← hdrep, homInclObj_eq C hC eS wEM]
    show homCompRaw C hC zz xE xa ⟨M, D.trans ad.2.1 hadM, D.trans (D.trans hpE hkEL) hLM⟩ rgerm
        ⟨wEM.K, wEM.hpx, wEM.hpy⟩ (wEM.germ eS)
      = homIncl C hC zz xa ad dm
    refine homCompRaw_eq_of_stage C hC zz xE xa
      ⟨M, D.trans ad.2.1 hadM, D.trans (D.trans hpE hkEL) hLM⟩ rgerm
      ⟨wEM.K, wEM.hpx, wEM.hpy⟩ (wEM.germ eS) ad dm M (D.refl M) (D.refl M) hadM ?_
    rw [homTr_refl C hC, homTr_refl C hC]
    show rgerm ≫ castHom hgEM.symm hgaM.symm ((C.functF hiM).map eS)
      = homTr C zz xa ad ⟨M, D.trans ad.2.1 hadM, D.trans ad.2.2 hadM⟩ hadM dm
    show castHom rfl hgEM.symm r ≫ castHom hgEM.symm hgaM.symm ((C.functF hiM).map eS) = dM_raw
    rw [castHom_comp]
    rw [show r ≫ (C.functF hiM).map eS = pL from hr]
    show castHom rfl hgaM.symm (castHom rfl hda_tgt dM_raw) = dM_raw
    rw [castHom_castHom]
    exact castHom_of_heq rfl _ HEq.rfl
  exact ⟨u, hux, fun v hv => hmono v u (hv.trans hux.symm)⟩

/-! ## Generic finite-limit-preservation ⟹ pullback-cone preservation

  A functor `F` preserving binary products and equalizers sends the §1.432
  chosen pullback of any cospan to a pullback cone of the image cospan.  This is the
  category-theoretic content behind `objIncl_preserves_pullbacks`: with the two
  comparison isos (`PreservesBinaryProducts` / `PreservesEqualizers`, both established
  for `objIncl i` by `objIncl_preserves_products` / `objIncl_preserves_equalizers`),
  the image of a stage pullback is a colimit pullback.  We work directly from the
  universal property — the §1.432 build expresses the pullback of `(f,g)` as the
  equalizer of `(fst≫f, snd≫g)` over `prod A B`, and the two isos relate the `F`-image
  of that equalizer to the equalizer of `(fst≫Ff, snd≫Fg)` over `prod (F A) (F B)`. -/

/-- **An equalizer of `(fst≫f, snd≫g)` over `A × B` is a pullback of `(f, g)`.**
    Constructive universal-property version of the §1.432 construction for an
    *arbitrary* equalizer cone (not just the chosen one): if `(E, m)` equalizes
    `fst≫f` and `snd≫g`, then `(E, m≫fst, m≫snd)` is a pullback of `(f, g)`. -/
theorem pullback_of_equalizer {𝒟 : Type u} [Cat.{v} 𝒟] [HasBinaryProducts 𝒟]
    {A B C E : 𝒟} {f : A ⟶ C} {g : B ⟶ C} {m : E ⟶ prod A B}
    (hmeq : m ≫ (fst ≫ f) = m ≫ (snd ≫ g))
    (heq : (EqualizerCone.mk E m hmeq).IsEqualizer) :
    (Cone.mk (f := f) (g := g) E (m ≫ fst) (m ≫ snd)
      (by rw [Cat.assoc, Cat.assoc]; exact hmeq)).IsPullback := by
  intro d
  -- a cone `d` over `(f,g)`: `d.π₁ ≫ f = d.π₂ ≫ g`.  Pair the legs to land in `A × B`.
  have hpd : pair d.π₁ d.π₂ ≫ (fst ≫ f) = pair d.π₁ d.π₂ ≫ (snd ≫ g) := by
    rw [← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair]; exact d.w
  obtain ⟨u, hu, huniq⟩ := heq (EqualizerCone.mk d.pt (pair d.π₁ d.π₂) hpd)
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · show u ≫ (m ≫ fst) = d.π₁
    rw [← Cat.assoc, hu, fst_pair]
  · show u ≫ (m ≫ snd) = d.π₂
    rw [← Cat.assoc, hu, snd_pair]
  · intro v hv₁ hv₂
    -- `v ≫ m` equalizes the pair (it pairs to `(d.π₁,d.π₂)`), so `v = u` by uniqueness.
    refine huniq v ?_
    show v ≫ m = pair d.π₁ d.π₂
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc]; exact hv₁
    · rw [Cat.assoc]; exact hv₂

/-- **Transport an equalizer along an iso of the parallel pair's domain.**  If `(E,e)`
    is the equalizer of `(φ ≫ p, φ ≫ q)` and `φ : X ⟶ Y` is iso, then `(E, e ≫ φ)` is the
    equalizer of `(p, q)`.  Used to slide the `F`-image equalizer of `(F(fst≫f),F(snd≫g))`
    onto the cospan `(fst≫Ff, snd≫Fg)` over `prod (F A) (F B)` (the two pairs differ by the
    product-comparison iso `φ = pair (F fst) (F snd)`). -/
theorem isEqualizer_comp_iso {𝒟 : Type u} [Cat.{v} 𝒟]
    {X Y Z E : 𝒟} {p q : Y ⟶ Z} {φ : X ⟶ Y} (hφ : IsIso φ) {e : E ⟶ X}
    (hew : e ≫ (φ ≫ p) = e ≫ (φ ≫ q))
    (heq : (EqualizerCone.mk (f := φ ≫ p) (g := φ ≫ q) E e hew).IsEqualizer) :
    (EqualizerCone.mk (f := p) (g := q) E (e ≫ φ)
      (show (e ≫ φ) ≫ p = (e ≫ φ) ≫ q by rw [Cat.assoc, Cat.assoc]; exact hew)).IsEqualizer := by
  obtain ⟨φ', hφφ', hφ'φ⟩ := hφ
  intro d
  -- `d : EqualizerCone p q`, i.e. `d.map ≫ p = d.map ≫ q`.  Pull `d.map` back through `φ'`
  -- to a cone over `(φ≫p, φ≫q)` with map `d.map ≫ φ'`.
  have hd' : (d.map ≫ φ') ≫ (φ ≫ p) = (d.map ≫ φ') ≫ (φ ≫ q) := by
    rw [← Cat.assoc, Cat.assoc d.map, hφ'φ, Cat.comp_id,
        ← Cat.assoc (d.map ≫ φ'), Cat.assoc d.map, hφ'φ, Cat.comp_id]
    exact d.eq
  obtain ⟨u, hu, huniq⟩ := heq (EqualizerCone.mk d.dom (d.map ≫ φ') hd')
  refine ⟨u, ?_, ?_⟩
  · show u ≫ (e ≫ φ) = d.map
    rw [← Cat.assoc, hu, Cat.assoc, hφ'φ, Cat.comp_id]
  · intro v hv
    -- `v ≫ e = d.map ≫ φ'` (post-compose `hv : v ≫ (e≫φ) = d.map` by `φ'`), so `v = u`.
    refine huniq v ?_
    show v ≫ e = d.map ≫ φ'
    calc v ≫ e = (v ≫ e) ≫ Cat.id _ := (Cat.comp_id _).symm
      _ = (v ≫ e) ≫ (φ ≫ φ') := by rw [hφφ']
      _ = ((v ≫ e) ≫ φ) ≫ φ' := (Cat.assoc _ _ _).symm
      _ = (v ≫ (e ≫ φ)) ≫ φ' := by rw [Cat.assoc v e φ]
      _ = d.map ≫ φ' := by rw [hv]

/-- **Transport an equalizer along an iso of its apex.**  If `(E, e)` is the equalizer of
    `(f, g)` and `i : E' ⟶ E`, `j : E ⟶ E'` are mutually inverse, then `(E', i ≫ e)` is also
    the equalizer of `(f, g)`.  Used to move the chosen equalizer (which `PreservesEqualizers`
    relates by an iso `k`) onto the `F`-image apex `F (eqObj …)`. -/
theorem isEqualizer_iso_apex {𝒟 : Type u} [Cat.{v} 𝒟] {A B E E' : 𝒟} {f g : A ⟶ B}
    {e : E ⟶ A} {hfe : e ≫ f = e ≫ g} (heq : (EqualizerCone.mk E e hfe).IsEqualizer)
    (i : E' ⟶ E) (j : E ⟶ E') (hij : i ≫ j = Cat.id E') (hji : j ≫ i = Cat.id E) :
    (EqualizerCone.mk (f := f) (g := g) E' (i ≫ e)
      (show (i ≫ e) ≫ f = (i ≫ e) ≫ g by rw [Cat.assoc, Cat.assoc, hfe])).IsEqualizer := by
  intro d
  obtain ⟨u, hu, huniq⟩ := heq d
  refine ⟨u ≫ j, ?_, ?_⟩
  · show (u ≫ j) ≫ (i ≫ e) = d.map
    rw [Cat.assoc, ← Cat.assoc j i e, hji, Cat.id_comp, hu]
  · intro v hv
    -- `v ≫ i ≫ e = d.map`, so `v ≫ i = u`; hence `v = v ≫ id = v ≫ i ≫ j = u ≫ j`.
    have hvi : (v ≫ i) ≫ e = d.map := by rw [Cat.assoc]; exact hv
    have : v ≫ i = u := huniq (v ≫ i) hvi
    calc v = v ≫ Cat.id E' := (Cat.comp_id _).symm
      _ = v ≫ (i ≫ j) := by rw [hij]
      _ = (v ≫ i) ≫ j := (Cat.assoc _ _ _).symm
      _ = u ≫ j := by rw [this]

/-- **A product- and equalizer-preserving functor sends the §1.432 chosen pullback to a
    pullback cone.**  Given `PreservesBinaryProducts F` and `PreservesEqualizers F`, the
    image `(F P.pt, F P.π₁, F P.π₂)` of the chosen pullback `P = products_equalizers_implies_pullbacks
    f g` is a pullback of `(F f, F g)`.  Combining the two comparison isos: the §1.432 pullback
    apex is `eqObj (fst≫f) (snd≫g)`; its `F`-image is (via `PreservesEqualizers`, `isEqualizer_iso_apex`)
    the equalizer of `(F(fst≫f), F(snd≫g))`, which equals `(fst≫Ff, snd≫Fg)` precomposed by the
    product-comparison iso `φ` (`isEqualizer_comp_iso`); `pullback_of_equalizer` then turns this
    equalizer over `prod (F A)(F B)` into the desired pullback. -/
theorem image_chosenPullback_isPullback {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasEqualizers 𝒞]
    [HasTerminal 𝒟] [HasBinaryProducts 𝒟] [HasEqualizers 𝒟]
    (F : 𝒞 → 𝒟) [hF : Functor F]
    (hprod : PreservesBinaryProducts F) (hpeq : PreservesEqualizers F)
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) :
    (Cone.mk (f := hF.map f) (g := hF.map g)
      (F (products_equalizers_implies_pullbacks f g).cone.pt)
      (hF.map (products_equalizers_implies_pullbacks f g).cone.π₁)
      (hF.map (products_equalizers_implies_pullbacks f g).cone.π₂)
      (by rw [← hF.map_comp, ← hF.map_comp,
              (products_equalizers_implies_pullbacks f g).cone.w])).IsPullback := by
  -- abbreviations for the §1.432 apex/map of the source pullback
  let eo : 𝒞 := eqObj (fst ≫ f) (snd ≫ g)
  let em : eo ⟶ prod A B := eqMap (fst ≫ f) (snd ≫ g)
  -- (F eo, F em) is the equalizer of (F(fst≫f), F(snd≫g)) — `PreservesEqualizers` + apex-iso
  have hFem_eq : hF.map em ≫ hF.map (fst ≫ f) = hF.map em ≫ hF.map (snd ≫ g) :=
    (hF.map_comp em (fst ≫ f)).symm.trans
      ((congrArg hF.map (eqMap_eq (fst ≫ f) (snd ≫ g))).trans (hF.map_comp em (snd ≫ g)))
  -- chosen equalizer of (F(fst≫f), F(snd≫g)); k is the comparison from F eo, iso by hpeq
  let cD := HasEqualizers.eq (F (prod A B)) (F C) (hF.map (fst ≫ f)) (hF.map (snd ≫ g))
  let hcone : EqualizerCone (hF.map (fst ≫ f)) (hF.map (snd ≫ g)) :=
    { dom := F eo, map := hF.map em, eq := hFem_eq }
  let k := cD.lift hcone
  have hk_fac : k ≫ eqMap (hF.map (fst ≫ f)) (hF.map (snd ≫ g)) = hF.map em := cD.fac hcone
  have hk_iso : IsIso k := hpeq (fst ≫ f) (snd ≫ g)
  obtain ⟨k', hkk', hk'k⟩ := hk_iso
  -- (F eo, F em) is an equalizer: transport the chosen equalizer along the iso k (apex move)
  have hFem_isEq : (EqualizerCone.mk (F eo) (hF.map em) hFem_eq).IsEqualizer := by
    -- transport the chosen equalizer (apex eqObj..) to apex F eo via k : F eo → eqObj..
    have h0 := isEqualizer_iso_apex
      (chosenEqualizer_isEqualizer (hF.map (fst ≫ f)) (hF.map (snd ≫ g))) k k' hkk' hk'k
    -- h0 : (F eo, k ≫ eqMap) IsEqualizer; and k ≫ eqMap = F em (hk_fac)
    intro d
    obtain ⟨u, hu, huniq⟩ := h0 d
    refine ⟨u, ?_, fun v hv => huniq v ?_⟩
    · -- hu : u ≫ (k ≫ eqMap) = d.map ; goal u ≫ F em = d.map
      exact (congrArg (u ≫ ·) hk_fac).symm.trans hu
    · -- hv : v ≫ F em = d.map ; goal v ≫ (k ≫ eqMap) = d.map
      exact (congrArg (v ≫ ·) hk_fac).trans hv
  -- product-comparison iso φ : F(prod A B) → prod (F A)(F B); φ ≫ fst = F fst, φ ≫ snd = F snd
  let φ : F (prod A B) ⟶ prod (F A) (F B) :=
    pair (hF.map (fst (A := A) (B := B))) (hF.map snd)
  have hφ_iso : IsIso φ := hprod (A := A) (B := B)
  have hφ_fst : φ ≫ fst = hF.map (fst (A := A) (B := B)) := fst_pair _ _
  have hφ_snd : φ ≫ snd = hF.map (snd (A := A) (B := B)) := snd_pair _ _
  -- the pair (F(fst≫f), F(snd≫g)) is (φ≫(fst≫Ff), φ≫(snd≫Fg))
  have hpair_f : hF.map (fst ≫ f) = φ ≫ (fst ≫ hF.map f) := by
    rw [hF.map_comp, ← Cat.assoc, hφ_fst]
  have hpair_g : hF.map (snd ≫ g) = φ ≫ (snd ≫ hF.map g) := by
    rw [hF.map_comp, ← Cat.assoc, hφ_snd]
  -- transport hFem_isEq onto the φ-precomposed pair (proof-irrelevant cone rewrite)
  have hFem_isEq' : (EqualizerCone.mk (f := φ ≫ (fst ≫ hF.map f)) (g := φ ≫ (snd ≫ hF.map g))
      (F eo) (hF.map em) (by rw [← hpair_f, ← hpair_g]; exact hFem_eq)).IsEqualizer := by
    intro d
    -- a cone over (φ≫p, φ≫q) is the same data as a cone over (F(fst≫f),F(snd≫g)) by hpair
    have hd : d.map ≫ hF.map (fst ≫ f) = d.map ≫ hF.map (snd ≫ g) := by
      rw [hpair_f, hpair_g]; exact d.eq
    obtain ⟨u, hu, huniq⟩ := hFem_isEq (EqualizerCone.mk d.dom d.map hd)
    exact ⟨u, hu, huniq⟩
  have hslid := isEqualizer_comp_iso hφ_iso
    (by rw [← hpair_f, ← hpair_g]; exact hFem_eq) hFem_isEq'
  -- hslid : (F eo, F em ≫ φ) is the equalizer of (fst≫Ff, snd≫Fg) over prod (F A)(F B)
  have hmeq : (hF.map em ≫ φ) ≫ (fst ≫ hF.map f) = (hF.map em ≫ φ) ≫ (snd ≫ hF.map g) := by
    rw [Cat.assoc, Cat.assoc, ← hpair_f, ← hpair_g]; exact hFem_eq
  have hpb := pullback_of_equalizer hmeq hslid
  -- hpb : (F eo, (F em ≫ φ)≫fst, (F em ≫ φ)≫snd) is the pullback of (Ff, Fg).
  -- those projections equal F P.π₁ = F(em≫fst), F P.π₂ = F(em≫snd).
  intro d
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hpb d
  -- bridge: (F em ≫ φ) ≫ fst = F (em ≫ fst), likewise snd
  have hbr₁ : hF.map em ≫ φ ≫ fst = hF.map (em ≫ fst) := by rw [hφ_fst, ← hF.map_comp]
  have hbr₂ : hF.map em ≫ φ ≫ snd = hF.map (em ≫ snd) := by rw [hφ_snd, ← hF.map_comp]
  have hpr₁ : (hF.map em ≫ φ) ≫ fst = hF.map (em ≫ fst) := (Cat.assoc _ _ _).trans hbr₁
  have hpr₂ : (hF.map em ≫ φ) ≫ snd = hF.map (em ≫ snd) := (Cat.assoc _ _ _).trans hbr₂
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · show u ≫ hF.map (em ≫ fst) = d.π₁
    rw [← hpr₁]; exact hu₁
  · show u ≫ hF.map (em ≫ snd) = d.π₂
    rw [← hpr₂]; exact hu₂
  · intro v hv₁ hv₂
    refine huniq v ?_ ?_
    · show v ≫ (hF.map em ≫ φ) ≫ fst = d.π₁
      rw [show (hF.map em ≫ φ) ≫ fst = hF.map (em ≫ fst) from (Cat.assoc _ _ _).trans hbr₁]
      exact hv₁
    · show v ≫ (hF.map em ≫ φ) ≫ snd = d.π₂
      rw [show (hF.map em ≫ φ) ≫ snd = hF.map (em ≫ snd) from (Cat.assoc _ _ _).trans hbr₂]
      exact hv₂

/-! ## M3b — pullbacks for the colimit category

  The colimit category has pullbacks, obtained from the terminal object,
  binary products, and equalizers already constructed (`colimitHasTerminal`,
  `colimitHasBinaryProducts`, `colimitHasEqualizers`) via the §1.432 route
  `products_equalizers_implies_pullbacks`.  DRY: we do not rebuild the
  representative-transport machinery; we reuse the three finite-limit
  constructors and the stage-level §1.432 derivation. -/
noncomputable def colimitHasPullbacks (C : CatSystem ι D) (hC : C.Coherent) [hne : Nonempty ι]
    -- terminal data
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    -- binary-product data
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    -- equalizer data
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k) :
    @HasPullbacks C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  letI : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hppres hppres_pair
  letI : HasEqualizers C.Obj := colimitHasEqualizers C hC he hepres hepres_lift
  exact ⟨fun f g => products_equalizers_implies_pullbacks f g⟩

/-- **Comparison map of two pullbacks of the same cospan is an iso.**  If `c` and
    `c'` both satisfy `Cone.IsPullback` over the cospan `f, g`, the unique map
    `φ : c.pt ⟶ c'.pt` compatible with the projections is an isomorphism: its
    inverse is the reverse comparison `ψ : c'.pt ⟶ c.pt`, and `φψ`, `ψφ` both
    satisfy the projection equations that the identity uniquely satisfies. -/
theorem pullback_comparison_iso {𝒞 : Type u} [Cat.{v} 𝒞] {A B Z : 𝒞}
    {f : A ⟶ Z} {g : B ⟶ Z} {c c' : Cone f g}
    (hc : c.IsPullback) (hc' : c'.IsPullback) :
    ∃ φ : c.pt ⟶ c'.pt, IsIso φ ∧ φ ≫ c'.π₁ = c.π₁ ∧ φ ≫ c'.π₂ = c.π₂ := by
  obtain ⟨φ, ⟨hφ1, hφ2⟩, _⟩ := hc' c
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, _⟩ := hc c'
  -- ψφ : c.pt ⟶ c.pt is compatible with c's projections, hence = id (uniqueness in c)
  obtain ⟨_, _, huniq⟩ := hc c
  have hψφ : ψ ≫ φ = Cat.id c'.pt := by
    obtain ⟨_, _, huniq'⟩ := hc' c'
    rw [huniq' (ψ ≫ φ) (by rw [Cat.assoc, hφ1, hψ1]) (by rw [Cat.assoc, hφ2, hψ2]),
        ← huniq' (Cat.id c'.pt) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]
  have hφψ : φ ≫ ψ = Cat.id c.pt := by
    rw [huniq (φ ≫ ψ) (by rw [Cat.assoc, hψ1, hφ1]) (by rw [Cat.assoc, hψ2, hφ2]),
        ← huniq (Cat.id c.pt) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]
  exact ⟨φ, ⟨ψ, hφψ, hψφ⟩, hφ1, hφ2⟩

/-- **Cover of the canonical pullback's `π₂` from *any* witnessing pullback cone.**
    In any category with pullbacks, the chosen pullback `(HasPullbacks.has f g).cone`
    is comparison-iso to *every* other pullback cone `c` of the same cospan
    (`pullback_comparison_iso`); the comparison `φ : (canonical).pt ⟶ c.pt` is iso with
    `φ ≫ c.π₂ = (canonical).π₂`, so `cover_precomp_iso` lifts `Cover c.π₂` to
    `Cover (canonical).π₂`.  This is the category-level dual of the reduction inside
    `colimitPullbacksTransferCovers`: it turns the opaque "canonical `π₂` is a cover"
    obligation into the concrete "*some* pullback cone of `(f, g)` has `π₂` a cover".
    Reusable in any `[Cat] [HasPullbacks]`, so DRY for both colimit assemblies. -/
theorem canonicalPullback_cover_of_witness {𝒞 : Type u} [Cat.{v} 𝒞] [HasPullbacks 𝒞]
    {A B Z : 𝒞} (f : A ⟶ Z) (g : B ⟶ Z)
    (c : Cone f g) (hc : c.IsPullback) (hcov : Cover c.π₂) :
    Cover (HasPullbacks.has f g).cone.π₂ := by
  -- compare the canonical cone to the witness `c`; `φ : canonical.pt ⟶ c.pt`, `φ ≫ c.π₂ = canonical.π₂`
  obtain ⟨φ, hφiso, _, hφ2⟩ := pullback_comparison_iso (HasPullbacks.has f g).cone_isPullback hc
  rw [← hφ2]
  exact cover_precomp_iso hφiso hcov

/-- **M3b — pullbacks transfer covers in the colimit category.**

  Given the finite-limit data of `colimitHasPullbacks` (so `C.Obj` has pullbacks)
  plus a *stage-level* transfer hypothesis, the colimit category satisfies
  `PullbacksTransferCovers`.  Strategy: an arbitrary pullback cone `c` of a cospan
  `f, g` with `f` a cover is compared (`pullback_comparison_iso`) to the canonical
  pullback `pb`; the comparison `φ` is iso with `φ ≫ pb.π₂ = c.π₂`, so by
  `cover_precomp_iso` it suffices that `pb.cone.π₂` is a cover.  That last fact is
  exactly `hcanon` — the canonical-pullback transfer, the only part requiring the
  representative-level argument. -/
noncomputable def colimitPullbacksTransferCovers (C : CatSystem ι D) (hC : C.Coherent)
    (hpull : @HasPullbacks C.Obj (colimitCat C hC))
    (hcanon : letI : Cat C.Obj := colimitCat C hC
      ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (hpull.has f g).cone.π₂) :
    @PullbacksTransferCovers C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasPullbacks C.Obj := hpull
  refine ⟨fun {A B Z f g} c hc hf => ?_⟩
  -- canonical pullback and its cover-transfer
  let pb := hpull.has f g
  have hpbcov : Cover pb.cone.π₂ := hcanon f g hf
  -- comparison iso between the arbitrary pullback `c` and the canonical `pb.cone`
  obtain ⟨φ, hφiso, _, hφ2⟩ := pullback_comparison_iso hc pb.cone_isPullback
  -- c.π₂ = φ ≫ pb.cone.π₂ is a cover by pre-composition with the iso φ
  rw [← hφ2]
  show Cover (φ ≫ pb.cone.π₂)
  exact cover_precomp_iso hφiso hpbcov

/-- **M3 assembly: the colimit is a pre-regular category.**

  Bundle `colimitHasTerminal`, `colimitHasBinaryProducts`, `colimitHasPullbacks`,
  and `colimitPullbacksTransferCovers` into `PreRegularCategory C.Obj`.

  All finite-limit data is deferred to the caller (terminal, products, equalizers);
  the PTC data additionally requires the `hcanon` witness that the canonical colimit
  pullback's π₂ is a cover when the cospan leg is a cover — satisfied by the
  slice-embedding system in M4.

  RESIDUAL on `hcanon`.  `canonicalPullback_cover_of_witness` reduces `hcanon` to:
  *exhibit one pullback cone of `(f, g)` whose `π₂` is a cover*.  The natural witness
  is the GERM of a stage pullback at the common stage `N` of the germs `fN, gN`:
  `pt = objIncl N (stage-pullback-obj)`, projections = `homInclObj` of the stage
  projections.  Discharging `hcanon` generically still needs TWO ingredients absent
  from the present finite-limit-preservation package, hence kept as a hypothesis:
  (1) PER-STAGE `PullbacksTransferCovers` (so the stage pullback's `π₂` is a stage
      cover — the stages here ARE pre-regular, so the caller can supply it), and
  (2) COVER-PRESERVATION by the transition functors `functF` (so the stage cover lifts to
      the colimit).
  Plus the germ cone's `IsPullback` proof (product/equalizer reflection at the colimit).

  STATUS.  Ingredient (2) is now DISCHARGED generically by `homInclObj_cover_of_stage`
  (the forward dual of `homInclObj_cover_reflects`): a stage cover stable under every
  transition `functF` becomes a `colimitCat` cover of `homInclObj`.  Its sibling
  `homInclObj_isIso_of_stage` (forward dual of `homInclObj_isIso_reflects`) supplies the
  iso half.  The stage inclusion is PACKAGED AS A FUNCTOR (`Capitalization.stageInclFunctor i`:
  object map `objIncl i`, morphism map `homInclObj`, identities via `homInclObj_id`,
  composition via `homInclObj_comp`), so the §1.43/§1.45 finite-limit machinery
  (`PreservesPullbacks`, `Level.map`, `cartesianFunctor_preserves_pullbacks`, `reflectsMono`)
  applies to it directly.

  The ONE remaining piece for a generic `hcanon` is ingredient (3): the germ cone's
  `IsPullback` at the colimit — equivalently `PreservesPullbacks (objIncl i)`.  With the
  functor in hand this reduces (via `cartesianFunctor_preserves_pullbacks`) to
  `PreservesBinaryProducts (objIncl i)` + `PreservesEqualizers (objIncl i)`, i.e. the two
  comparison isos `objIncl(a×b) → objIncl a × objIncl b` and `objIncl(eqObj f g) →
  eqObj (homInclObj f)(homInclObj g)`.  Each is a bounded representative-transport build
  comparable in size to `colimitHasBinaryProducts`/`colimitHasEqualizers` (reusing
  `homInclObj_eq`, `castHom`, the germ lemmas).  Until those two isos land, both assemblies
  still pass `hcanon` through as a hypothesis. -/
noncomputable def colimitPreRegular (C : CatSystem ι D) (hC : C.Coherent) [hne : Nonempty ι]
    -- terminal
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    -- binary products
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    -- equalizers
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    -- pullbacks-transfer-covers: the canonical pullback's π₂ is a cover
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
      ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    @PreRegularCategory C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  letI hterm : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  letI hprod : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hppres hppres_pair
  letI hpull : HasPullbacks C.Obj :=
    colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
  letI hptc : PullbacksTransferCovers C.Obj :=
    colimitPullbacksTransferCovers C hC hpull hcanon
  exact {}

end Freyd.Colim

namespace Freyd

/-- `ULift.{u} Nat` with `Nat`'s order is a directed preorder: the `Type u` index of the
    ω-tower (the colimit machinery requires `ι : Type u`).  Relocated here (from `Capitalization`)
    so it sits UPSTREAM of `Capitalization`: both `Capitalization` (the outer tower) and
    `Fredy.Inflation` (the inner chain-slice `CatSystem`) index over it. -/
def uliftNatDirected : Colim.Directed (ULift.{u} Nat) where
  le a b := a.down ≤ b.down
  refl a := Nat.le_refl a.down
  trans h h' := Nat.le_trans h h'
  bound a b := ⟨⟨Nat.max a.down b.down⟩, Nat.le_max_left _ _, Nat.le_max_right _ _⟩

end Freyd
