/-
  M3a — terminal object of the colimit category.

  If each stage `C.A i` has a terminal and the transitions preserve it, then the
  colimit category `C.Obj` has a terminal object.
-/

import Fredy.CatColimit
import Fredy.S1_42
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
      sorry
    -- snd proof is symmetric
    have h_snd_ok : colimComp C hC h (snd (A:=X) (B:=Y)) = Quotient.mk (setoid (homSystem C hC z (xObj Y))) ⟨ag, ga⟩ := by
      sorry
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
    sorry
  exact @HasBinaryProducts.mk C.Obj (colimitCat C hC) prodFun fst snd pair h_fst_pair h_snd_pair h_pair_uniq
