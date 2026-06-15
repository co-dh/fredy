/-
  M3a — terminal object of the colimit category.

  If each stage `C.A i` has a terminal and the transitions preserve it, then the
  colimit category `C.Obj` has a terminal object.
-/

import Fredy.CatColimit
import Fredy.S1_42
import Fredy.S1_43
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
      refine ⟨homIncl C hC xW opE
        ⟨L, D.trans aC.2.1 (D.trans hcP (D.trans hPR hRL)), hipEL⟩ (castHom rfl hHdL r), ?_, ?_⟩
      · sorry
      · sorry
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
