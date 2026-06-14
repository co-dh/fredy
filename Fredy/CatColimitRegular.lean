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
  have hOneRel : Rel C.objSystem ⟨io, o⟩ ⟨i₀, (ht i₀).one⟩ := Quotient.exact hOneSpec
  let k₀ := Classical.choose hOneRel
  have h_spec1 : ∃ (hik : D.le io k₀) (hjk : D.le i₀ k₀), C.F hik o = C.F hjk (ht i₀).one := Classical.choose_spec hOneRel
  let h_io_k₀ := Classical.choose h_spec1
  have h_spec2 : ∃ (hjk : D.le i₀ k₀), C.F h_io_k₀ o = C.F hjk (ht i₀).one := Classical.choose_spec h_spec1
  let h_i₀_k₀ := Classical.choose h_spec2
  have h_obj_eq : C.F h_io_k₀ o = C.F h_i₀_k₀ (ht i₀).one := Classical.choose_spec h_spec2
  have ho_is_term : C.F h_io_k₀ o = (ht k₀).one := by rw [h_obj_eq, hpres h_i₀_k₀]
  refine @HasTerminal.mk C.Obj (colimitCat C hC) one ?_ ?_
  · intro X
    let jX := (colimOut C X).1; let xX := (colimOut C X).2
    let bd := D.bound jX k₀; let k := Classical.choose bd
    have hbd_spec : D.le jX k ∧ D.le k₀ k := Classical.choose_spec bd
    have h_jX_k : D.le jX k := hbd_spec.1; have h_k₀_k : D.le k₀ k := hbd_spec.2
    have h_io_k : D.le io k := D.trans h_io_k₀ h_k₀_k
    have hok : C.F h_io_k o = (ht k).one := by
      calc
        C.F h_io_k o = C.F (D.trans h_io_k₀ h_k₀_k) o := rfl
        _ = C.F h_k₀_k (C.F h_io_k₀ o) := by rw [C.F_trans]
        _ = C.F h_k₀_k ((ht k₀).one) := by rw [ho_is_term]
        _ = (ht k).one := hpres h_k₀_k
    let m : C.F h_jX_k xX ⟶ C.F h_io_k o := castHom rfl hok.symm ((ht k).trm (C.F h_jX_k xX))
    exact homIncl C hC xX o ⟨k, h_jX_k, h_io_k⟩ m
  · intro X f g
    let jX := (colimOut C X).1; let xX := (colimOut C X).2
    refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
    apply Quotient.sound
    obtain ⟨m, ham, hbm⟩ := D.bound a.1 b.1
    obtain ⟨k', hmk', hk₀k'⟩ := D.bound m k₀
    let hak' : D.le a.1 k' := D.trans ham hmk'; let hbk' : D.le b.1 k' := D.trans hbm hmk'
    let hiok' : D.le io k' := D.trans h_io_k₀ hk₀k'
    have h_jX_k' : D.le jX k' := D.trans a.2.1 hak'
    let ub : UpperBound D jX io := ⟨k', h_jX_k', hiok'⟩
    let fa' : C.F ub.2.1 xX ⟶ C.F ub.2.2 o := homTr C xX o a ub hak' fa
    let gb' : C.F ub.2.1 xX ⟶ C.F ub.2.2 o := homTr C xX o b ub hbk' gb
    have hok' : C.F hiok' o = (ht k').one := by
      calc
        C.F hiok' o = C.F (D.trans h_io_k₀ hk₀k') o := rfl
        _ = C.F hk₀k' (C.F h_io_k₀ o) := by rw [C.F_trans]
        _ = C.F hk₀k' ((ht k₀).one) := by rw [ho_is_term]
        _ = (ht k').one := hpres hk₀k'
    have hL'R' : castHom rfl hok' fa' = castHom rfl hok' gb' := (ht k').uniq (castHom rfl hok' fa') (castHom rfl hok' gb')
    have h_eq : fa' = gb' :=
      Eq.rec (motive := λ T (h : C.F hiok' o = T) => ∀ (f g : C.F ub.2.1 xX ⟶ C.F hiok' o), castHom rfl h f = castHom rfl h g → f = g)
        (λ f g h_eq_cast => by simpa [castHom] using h_eq_cast) hok' fa' gb' hL'R'
    exact ⟨ub, hak', hbk', h_eq⟩

/-! M3b — binary products of the colimit category. -/

axiom colimitHasBinaryProducts (C : CatSystem ι D) (hC : C.Coherent)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u : z ⟶ C.F hij ((hp i).prod a b)) (v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q) :
    @HasBinaryProducts C.Obj (colimitCat C hC)
