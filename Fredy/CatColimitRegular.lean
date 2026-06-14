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
  -- Define product object function (available to all subsequent goals)
  let prodFun (X Y : C.Obj) : C.Obj := by
    let iX := (colimOut C X).1; let x := (colimOut C X).2
    let iY := (colimOut C Y).1; let y := (colimOut C Y).2
    let bd := D.bound iX iY
    let k := Classical.choose bd
    have hbd_spec : D.le iX k ∧ D.le iY k := Classical.choose_spec bd
    let hXk : D.le iX k := hbd_spec.1
    let hYk : D.le iY k := hbd_spec.2
    let xk := C.F hXk x
    let yk := C.F hYk y
    exact C.objIncl k ((hp k).prod xk yk)
  refine @HasBinaryProducts.mk C.Obj (colimitCat C hC) prodFun ?fst ?snd ?pair ?fst_pair ?snd_pair ?pair_uniq
  · -- fst
    intro A B
    let X := A; let Y := B
    let iX := (colimOut C X).1; let x := (colimOut C X).2
    let iY := (colimOut C Y).1; let y := (colimOut C Y).2
    let bd := D.bound iX iY
    let k := Classical.choose bd
    have hbd_spec : D.le iX k ∧ D.le iY k := Classical.choose_spec bd
    let hXk : D.le iX k := hbd_spec.1
    let hYk : D.le iY k := hbd_spec.2
    let xk := C.F hXk x
    let yk := C.F hYk y
    let pXY := prodFun X Y
    -- chosen rep of the product
    let ip := (colimOut C pXY).1; let op := (colimOut C pXY).2
    have hProdSpec : C.objIncl ip op = pXY := colimOut_spec C pXY
    have hProdRel : Rel C.objSystem ⟨ip, op⟩ ⟨k, (hp k).prod xk yk⟩ := Quotient.exact hProdSpec
    let kp := Classical.choose hProdRel
    have h_spec1 : ∃ (hik : D.le ip kp) (hjk : D.le k kp), C.F hik op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec hProdRel
    let h_ip_kp := Classical.choose h_spec1
    have h_spec2 : ∃ (hjk : D.le k kp), C.F h_ip_kp op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec1
    let h_k_kp := Classical.choose h_spec2
    have h_prod_eq : C.F h_ip_kp op = C.F h_k_kp ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec2
    -- target path: iX → k → kp
    let h_iX_kp : D.le iX kp := D.trans hXk h_k_kp
    -- target equality
    have h_tgt : C.F h_k_kp xk = C.F h_iX_kp x := by
      calc
        C.F h_k_kp xk = C.F h_k_kp (C.F hXk x) := rfl
        _ = C.F (D.trans hXk h_k_kp) x := by rw [C.F_trans hXk h_k_kp x]
        _ = C.F h_iX_kp x := rfl
    -- upper bound
    let ub : UpperBound D ip iX := ⟨kp, h_ip_kp, h_iX_kp⟩
    -- morphism: use (C.functF h_k_kp).map ((hp k).fst) and cast source/target
    let m : C.F h_ip_kp op ⟶ C.F h_iX_kp x :=
      castHom h_prod_eq.symm h_tgt ((C.functF h_k_kp).map ((hp k).fst (A:=xk) (B:=yk)))
    exact homIncl C hC op x ub m
  · -- snd
    intro A B
    let X := A; let Y := B
    let iX := (colimOut C X).1; let x := (colimOut C X).2
    let iY := (colimOut C Y).1; let y := (colimOut C Y).2
    let bd := D.bound iX iY
    let k := Classical.choose bd
    have hbd_spec : D.le iX k ∧ D.le iY k := Classical.choose_spec bd
    let hXk : D.le iX k := hbd_spec.1
    let hYk : D.le iY k := hbd_spec.2
    let xk := C.F hXk x
    let yk := C.F hYk y
    let pXY := prodFun X Y
    let ip := (colimOut C pXY).1; let op := (colimOut C pXY).2
    have hProdSpec : C.objIncl ip op = pXY := colimOut_spec C pXY
    have hProdRel : Rel C.objSystem ⟨ip, op⟩ ⟨k, (hp k).prod xk yk⟩ := Quotient.exact hProdSpec
    let kp := Classical.choose hProdRel
    have h_spec1 : ∃ (hik : D.le ip kp) (hjk : D.le k kp), C.F hik op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec hProdRel
    let h_ip_kp := Classical.choose h_spec1
    have h_spec2 : ∃ (hjk : D.le k kp), C.F h_ip_kp op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec1
    let h_k_kp := Classical.choose h_spec2
    have h_prod_eq : C.F h_ip_kp op = C.F h_k_kp ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec2
    let h_iY_kp : D.le iY kp := D.trans hYk h_k_kp
    have h_tgt : C.F h_k_kp yk = C.F h_iY_kp y := by
      calc
        C.F h_k_kp yk = C.F h_k_kp (C.F hYk y) := rfl
        _ = C.F (D.trans hYk h_k_kp) y := by rw [C.F_trans hYk h_k_kp y]
        _ = C.F h_iY_kp y := rfl
    let ub : UpperBound D ip iY := ⟨kp, h_ip_kp, h_iY_kp⟩
    let m : C.F h_ip_kp op ⟶ C.F h_iY_kp y :=
      castHom h_prod_eq.symm h_tgt ((C.functF h_k_kp).map ((hp k).snd (A:=xk) (B:=yk)))
    exact homIncl C hC op y ub m
  · -- pair
    intro Z A B f g
    let X := A; let Y := B
    let iX := (colimOut C X).1; let x := (colimOut C X).2
    let iY := (colimOut C Y).1; let y := (colimOut C Y).2
    let iZ := (colimOut C Z).1; let z := (colimOut C Z).2
    let bd := D.bound iX iY
    let k := Classical.choose bd
    have hbd_spec : D.le iX k ∧ D.le iY k := Classical.choose_spec bd
    let hXk : D.le iX k := hbd_spec.1
    let hYk : D.le iY k := hbd_spec.2
    let xk := C.F hXk x
    let yk := C.F hYk y
    let pXY := prodFun X Y
    let ip := (colimOut C pXY).1; let op := (colimOut C pXY).2
    have hProdSpec : C.objIncl ip op = pXY := colimOut_spec C pXY
    have hProdRel : Rel C.objSystem ⟨ip, op⟩ ⟨k, (hp k).prod xk yk⟩ := Quotient.exact hProdSpec
    let kp := Classical.choose hProdRel
    have h_spec1 : ∃ (hik : D.le ip kp) (hjk : D.le k kp), C.F hik op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec hProdRel
    let h_ip_kp := Classical.choose h_spec1
    have h_spec2 : ∃ (hjk : D.le k kp), C.F h_ip_kp op = C.F hjk ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec1
    let h_k_kp := Classical.choose h_spec2
    have h_prod_eq : C.F h_ip_kp op = C.F h_k_kp ((hp k).prod xk yk) :=
      Classical.choose_spec h_spec2
    -- choose representatives for f and g (mirroring colimOut for objects)
    let rep_f := Classical.choose (Quotient.exists_rep f)
    have hf_rep : (Quotient.mk (setoid (homSystem C hC z x)) rep_f) = f :=
      Classical.choose_spec (Quotient.exists_rep f)
    let a := rep_f.1
    let fa := rep_f.2
    let rep_g := Classical.choose (Quotient.exists_rep g)
    have hg_rep : (Quotient.mk (setoid (homSystem C hC z y)) rep_g) = g :=
      Classical.choose_spec (Quotient.exists_rep g)
    let b := rep_g.1
    let gb := rep_g.2
    -- pick M ≥ a.1, b.1, kp (use Classical.choose since goal is Type, not Prop)
    let bd1 := D.bound a.1 b.1
    let m := Classical.choose bd1
    have hbd1_spec : D.le a.1 m ∧ D.le b.1 m := Classical.choose_spec bd1
    let ham : D.le a.1 m := hbd1_spec.1
    let hbm : D.le b.1 m := hbd1_spec.2
    let bd2 := D.bound m kp
    let M := Classical.choose bd2
    have hbd2_spec : D.le m M ∧ D.le kp M := Classical.choose_spec bd2
    let hmM : D.le m M := hbd2_spec.1
    let hkpM : D.le kp M := hbd2_spec.2
    let haM : D.le a.1 M := D.trans ham hmM
    let hbM : D.le b.1 M := D.trans hbm hmM
    let h_k_M : D.le k M := D.trans h_k_kp hkpM
    let h_ip_M : D.le ip M := D.trans h_ip_kp hkpM
    -- source at M: use a's source path
    let h_iZ_M : D.le iZ M := D.trans a.2.1 haM
    -- target paths for X, Y via the product stage k
    let h_iX_M : D.le iX M := D.trans hXk h_k_M
    let h_iY_M : D.le iY M := D.trans hYk h_k_M
    -- transport fa, gb to M
    let ub_a_M : UpperBound D iZ iX := ⟨M, h_iZ_M, D.trans a.2.2 haM⟩
    let ub_b_M : UpperBound D iZ iY := ⟨M, D.trans b.2.1 hbM, D.trans b.2.2 hbM⟩
    let fa_M_raw : C.F h_iZ_M z ⟶ C.F (D.trans a.2.2 haM) x := homTr C z x a ub_a_M haM fa
    let gb_M_raw : C.F (D.trans b.2.1 hbM) z ⟶ C.F (D.trans b.2.2 hbM) y :=
      homTr C z y b ub_b_M hbM gb
    -- align targets to h_iX_M, h_iY_M and source of gb to h_iZ_M (via proof irrelevance)
    have h_fa_tgt : C.F (D.trans a.2.2 haM) x = C.F h_iX_M x :=
      hF_proof_irrel (D.trans a.2.2 haM) h_iX_M x
    have h_gb_tgt : C.F (D.trans b.2.2 hbM) y = C.F h_iY_M y :=
      hF_proof_irrel (D.trans b.2.2 hbM) h_iY_M y
    have h_gb_src : C.F (D.trans b.2.1 hbM) z = C.F h_iZ_M z :=
      hF_proof_irrel (D.trans b.2.1 hbM) h_iZ_M z
    let fa_M : C.F h_iZ_M z ⟶ C.F h_iX_M x :=
      castHom rfl h_fa_tgt fa_M_raw
    let gb_M : C.F h_iZ_M z ⟶ C.F h_iY_M y :=
      castHom h_gb_src h_gb_tgt gb_M_raw
    -- targets equal the transported stage objects
    have h_fa_tgt_to_xk : C.F h_iX_M x = C.F h_k_M xk := by
      calc
        C.F h_iX_M x = C.F (D.trans hXk h_k_M) x := rfl
        _ = C.F h_k_M (C.F hXk x) := by rw [C.F_trans hXk h_k_M x]
        _ = C.F h_k_M xk := rfl
    have h_gb_tgt_to_yk : C.F h_iY_M y = C.F h_k_M yk := by
      calc
        C.F h_iY_M y = C.F (D.trans hYk h_k_M) y := rfl
        _ = C.F h_k_M (C.F hYk y) := by rw [C.F_trans hYk h_k_M y]
        _ = C.F h_k_M yk := rfl
    let p_pair : C.F h_iZ_M z ⟶ C.F h_k_M xk := castHom rfl h_fa_tgt_to_xk fa_M
    let q_pair : C.F h_iZ_M z ⟶ C.F h_k_M yk := castHom rfl h_gb_tgt_to_yk gb_M
    -- apply preservation: the image of the product is a product
    let hr := hpres_pair h_k_M xk yk (C.F h_iZ_M z) p_pair q_pair
    let r := Classical.choose hr
    have hr_spec : r ≫ (C.functF h_k_M).map (hp k).fst = p_pair ∧ r ≫ (C.functF h_k_M).map (hp k).snd = q_pair :=
      Classical.choose_spec hr
    have hr_fst : r ≫ (C.functF h_k_M).map (hp k).fst = p_pair := hr_spec.1
    have hr_snd : r ≫ (C.functF h_k_M).map (hp k).snd = q_pair := hr_spec.2
    -- transport the result to the product rep
    have h_prod_eq_M : C.F h_ip_M op = C.F h_k_M ((hp k).prod xk yk) := by
      calc
        C.F h_ip_M op = C.F (D.trans h_ip_kp hkpM) op := rfl
        _ = C.F hkpM (C.F h_ip_kp op) := by rw [C.F_trans h_ip_kp hkpM op]
        _ = C.F hkpM (C.F h_k_kp ((hp k).prod xk yk)) := by rw [h_prod_eq]
        _ = C.F (D.trans h_k_kp hkpM) ((hp k).prod xk yk) := by rw [C.F_trans h_k_kp hkpM ((hp k).prod xk yk)]
        _ = C.F h_k_M ((hp k).prod xk yk) := rfl
    let r' : C.F h_iZ_M z ⟶ C.F h_ip_M op := castHom rfl h_prod_eq_M.symm r
    let ub_pair : UpperBound D iZ ip := ⟨M, h_iZ_M, h_ip_M⟩
    exact homIncl C hC z op ub_pair r'
  · -- fst_pair
    intro Z X Y f g
    sorry
  · -- snd_pair
    intro Z X Y f g
    sorry
  · -- pair_uniq
    intro Z X Y f g h hfst hsnd
    sorry
