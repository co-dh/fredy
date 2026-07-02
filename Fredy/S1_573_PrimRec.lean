/-
  Freyd & Scedrov, *Categories and Allegories* §1.573–§1.574
  The category **P** of primitive recursive functions and its idempotent-splitting
  completion **P̂** = Spl(P).

  §1.573: replacing 'recursive' by 'primitive recursive' in §1.572 gives a category P
  that is NOT cartesian (equalizers can fail).  But given `x, y : ω → α` and `n` with
  `x(n) = y(n)` (if there is no such `n`, then 0 is the equalizer), the function
      `e(i) = i` if `x(i) = y(i)`, `n` otherwise
  satisfies `e² = e`, `ex = ey`, and every `z : β → ω` with `zx = zy` has `ze = z` —
  precisely what is needed for `x, y` to acquire an equalizer once all idempotents are
  split.  P̂ := Spl(P) (equivalent to the category of all primitive recursive subsets
  of ω) is cartesian.

  §1.574: the representable functor `P̂(ω̂, −) : P̂ → 𝒮` is faithful.

  The primitive recursive fragment is carved out of §1.572's Kleene codes by the
  mu-freeness predicate `IsPrim`, so every evaluation lemma of `S1_572_Recursive`
  transfers as-is; only the closure lemmas that USED `mu` (Cantor weight `cw`,
  division/remainder by a constant) are re-done mu-free, by unary primitive recursion
  (`natIter`) in place of unbounded search.

  SKIPPED (classical Ackermann-scale formalizations, out of scope here):
  • §1.573's negative half — "P is not cartesian" — needs a function growing faster
    than every primitive recursive function to defeat all candidate equalizers.
  • §1.574's one-to-one onto `x : ω → ω` in P with `x⁻¹ ∉ P` (whence R is a category
    of fractions of P), for the same reason.
  • "representation of regular categories": P̂'s regular structure is not developed
    here, only its cartesian structure (§1.573) and the faithfulness of `P̂(ω̂, −)`.
-/

import Fredy.S1_572_Recursive
import Fredy.S1_39
import Fredy.S1_55
import Fredy.S2_21c

open Freyd Freyd.Rcat

namespace Freyd.Pcat

/-! ## Part 1: primitive recursive codes = the mu-free Kleene codes -/

/-- Mu-freeness: `IsPrim c` iff the code `c` contains no `mu`.  A `Prop`-valued
    predicate over §1.572's `RecCode` (rather than a separate inductive) so that every
    evaluation lemma about explicit codes (`evalAdd`, `evalConst`, …) transfers as-is. -/
def IsPrim : {k : Nat} → RecCode k → Prop
  | _, .zero      => True
  | _, .succ      => True
  | _, .proj _    => True
  | _, .comp f gs => IsPrim f ∧ ∀ j, IsPrim (gs j)
  | _, .prec g h  => IsPrim g ∧ IsPrim h
  | _, .mu _      => False

/-- Primitive recursive codes are TOTAL: `Eval` converges on every input.
    (Structural induction; the recursion of `prec` is an inner induction on the
    first argument, and `comp` assembles its finitely many subvalues by the
    constructive finite choice `S2_21c.finChoice`.) -/
theorem IsPrim.total : ∀ {k : Nat} (c : RecCode k), IsPrim c → ∀ v, ∃ y, Eval c v y := by
  intro k c
  induction c with
  | zero => exact fun _ _ => ⟨0, .zero⟩
  | succ => exact fun _ v => ⟨v 0 + 1, .succ⟩
  | proj i => exact fun _ v => ⟨v i, .proj i⟩
  | comp f gs ihf ihg =>
    intro h v
    obtain ⟨w, hw⟩ := S2_21c.finChoice fun j => ihg j (h.2 j) v
    obtain ⟨y, hy⟩ := ihf h.1 w
    exact ⟨y, .comp w hw hy⟩
  | prec g hs ihg ihh =>
    intro h v
    have key : ∀ (n : Nat) (w : Vec _), ∃ y, Eval (.prec g hs) (vcons n w) y := by
      intro n w
      induction n with
      | zero =>
        obtain ⟨y, hy⟩ := ihg h.1 w
        exact ⟨y, .prec_zero rfl hy⟩
      | succ n ihn =>
        obtain ⟨r, hr⟩ := ihn
        obtain ⟨y, hy⟩ := ihh h.2 (vcons n (vcons r w))
        exact ⟨y, .prec_succ rfl hr hy⟩
    obtain ⟨y, hy⟩ := key (v 0) (vtail v)
    exact ⟨y, by rwa [vcons_head_tail] at hy⟩
  | mu f ih => exact fun h => h.elim

/-! ### Primitive recursive functions -/

/-- A `k`-ary function is PRIMITIVE RECURSIVE if some mu-free code converges to its
    value on every input (§1.572's `RecursiveV` with the code constrained to `IsPrim`). -/
def PrimRecV {k : Nat} (f : Vec k → Nat) : Prop :=
  ∃ c : RecCode k, IsPrim c ∧ ∀ v, Eval c v (f v)

/-- Unary primitive recursive functions ℕ → ℕ. -/
def PrimRec1 (f : Nat → Nat) : Prop := PrimRecV fun v : Vec 1 => f (v 0)

/-- Binary primitive recursive functions ℕ → ℕ → ℕ. -/
def PrimRec2 (f : Nat → Nat → Nat) : Prop := PrimRecV fun v : Vec 2 => f (v 0) (v 1)

/-- Primitive recursive functions are recursive. -/
theorem PrimRecV.recursiveV {k : Nat} {f : Vec k → Nat} : PrimRecV f → RecursiveV f
  | ⟨c, _, hc⟩ => ⟨c, hc⟩

theorem PrimRec1.recursive1 {f : Nat → Nat} (h : PrimRec1 f) : Recursive1 f :=
  h.recursiveV

theorem PrimRecV.congr {k : Nat} {f g : Vec k → Nat} (hf : PrimRecV f)
    (h : ∀ v, f v = g v) : PrimRecV g := by
  obtain ⟨c, hp, hc⟩ := hf
  exact ⟨c, hp, fun v => h v ▸ hc v⟩

theorem PrimRec1.congr {f g : Nat → Nat} (hf : PrimRec1 f) (h : ∀ n, f n = g n) :
    PrimRec1 g := PrimRecV.congr hf fun v => h (v 0)

theorem PrimRec2.congr {f g : Nat → Nat → Nat} (hf : PrimRec2 f)
    (h : ∀ a b, f a b = g a b) : PrimRec2 g := PrimRecV.congr hf fun v => h (v 0) (v 1)

theorem PrimRecV.proj {k : Nat} (i : Fin k) : PrimRecV (fun v : Vec k => v i) :=
  ⟨.proj i, trivial, fun _ => .proj i⟩

theorem PrimRec1.id : PrimRec1 fun n => n := PrimRecV.proj 0

theorem PrimRec2.fstArg : PrimRec2 fun a _ => a := PrimRecV.proj 0

theorem PrimRec2.sndArg : PrimRec2 fun _ b => b := PrimRecV.proj 1

theorem isPrim_constCode (k c : Nat) : IsPrim (constCode k c) := by
  induction c with
  | zero => trivial
  | succ c ih => exact ⟨trivial, fun _ => ih⟩

theorem PrimRecV.const (k c : Nat) : PrimRecV (fun _ : Vec k => c) :=
  ⟨constCode k c, isPrim_constCode k c, fun v => evalConst k c v⟩

theorem PrimRec1.const (c : Nat) : PrimRec1 fun _ => c := PrimRecV.const 1 c

/-! ### Closure under composition.  Unlike §1.572's `RecursiveV.comp` (which chooses an
    arbitrary finite family of codes by `Classical.choose`), we only ever compose through
    explicit one- and two-code families, keeping the closure lemmas choice-free. -/

theorem PrimRec1.comp {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => g (f n) := by
  obtain ⟨cf, pf, hcf⟩ := hf
  obtain ⟨cg, pg, hcg⟩ := hg
  exact ⟨.comp cg fun _ => cf, ⟨pg, fun _ => pf⟩,
    fun v => .comp (fun _ => f (v 0)) (fun _ => hcf v) (hcg _)⟩

/-- Unary post-composition at any arity. -/
theorem PrimRecV.comp1 {k : Nat} {F : Nat → Nat} {f : Vec k → Nat}
    (hF : PrimRec1 F) (hf : PrimRecV f) : PrimRecV (fun v => F (f v)) := by
  obtain ⟨cF, pF, hcF⟩ := hF
  obtain ⟨cf, pf, hcf⟩ := hf
  exact ⟨.comp cF fun _ => cf, ⟨pF, fun _ => pf⟩,
    fun v => .comp (fun _ => f v) (fun _ => hcf v) (hcF _)⟩

/-- Binary combination at any arity: from a primitive recursive binary `H` and
    primitive recursive arguments, `v ↦ H (f v) (g v)` is primitive recursive. -/
theorem PrimRecV.comp2 {k : Nat} {H : Nat → Nat → Nat} {f g : Vec k → Nat}
    (hH : PrimRec2 H) (hf : PrimRecV f) (hg : PrimRecV g) :
    PrimRecV (fun v => H (f v) (g v)) := by
  obtain ⟨cH, pH, hcH⟩ := hH
  obtain ⟨cf, pf, hcf⟩ := hf
  obtain ⟨cg, pg, hcg⟩ := hg
  refine ⟨.comp cH (fun j => if j.val = 0 then cf else cg),
    ⟨pH, fun j => by dsimp only; split <;> assumption⟩, fun v => ?_⟩
  refine .comp (vcons (f v) (fun _ => g v)) (fun j => ?_) ?_
  · rcases j with ⟨jv, hj⟩
    match jv, hj with
    | 0, _ => exact hcf v
    | 1, _ => exact hcg v
  · exact hcH (vcons (f v) fun _ => g v)

theorem PrimRec1.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat}
    (hH : PrimRec2 H) (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => H (f n) (g n) :=
  PrimRecV.comp2 (f := fun v : Vec 1 => f (v 0)) (g := fun v : Vec 1 => g (v 0)) hH hf hg

theorem PrimRec2.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat → Nat}
    (hH : PrimRec2 H) (hf : PrimRec2 f) (hg : PrimRec2 g) :
    PrimRec2 fun a b => H (f a b) (g a b) :=
  PrimRecV.comp2 (f := fun v : Vec 2 => f (v 0) (v 1)) (g := fun v : Vec 2 => g (v 0) (v 1))
    hH hf hg

theorem PrimRec2.swap {f : Nat → Nat → Nat} (hf : PrimRec2 f) :
    PrimRec2 fun a b => f b a :=
  PrimRec2.comp2 hf PrimRec2.sndArg PrimRec2.fstArg

theorem PrimRec2.ofFst {f : Nat → Nat} (hf : PrimRec1 f) : PrimRec2 fun a _ => f a :=
  PrimRecV.comp1 (f := fun v : Vec 2 => v 0) hf (PrimRecV.proj 0)

theorem PrimRec2.ofSnd {f : Nat → Nat} (hf : PrimRec1 f) : PrimRec2 fun _ b => f b :=
  PrimRecV.comp1 (f := fun v : Vec 2 => v 1) hf (PrimRecV.proj 1)

/-! ### Arithmetic base (the §1.572 codes are all mu-free) -/

theorem isPrim_addCode : IsPrim addCode := ⟨trivial, trivial, fun _ => trivial⟩

theorem PrimRec2.add : PrimRec2 fun a b => a + b := by
  refine PrimRecV.congr (g := fun v : Vec 2 => v 0 + v 1)
    ⟨addCode, isPrim_addCode, fun v => evalAdd v⟩ ?_
  intro v
  exact Nat.add_comm (v 1) (v 0)

theorem isPrim_predCode : IsPrim predCode := ⟨trivial, trivial⟩

theorem isPrim_rsubCode : IsPrim rsubCode := ⟨trivial, isPrim_predCode, fun _ => trivial⟩

theorem PrimRec2.sub : PrimRec2 fun a b => a - b := by
  have h : PrimRec2 fun a b => b - a :=
    ⟨rsubCode, isPrim_rsubCode, fun v => by
      have := evalRsub_aux (v 0) (vtail v)
      rwa [vcons_head_tail v] at this⟩
  exact h.swap

theorem isPrim_mulCode : IsPrim mulCode :=
  ⟨trivial, isPrim_addCode, fun j => by dsimp only; split <;> trivial⟩

theorem PrimRec2.mul : PrimRec2 fun a b => a * b :=
  ⟨mulCode, isPrim_mulCode, fun v => by
    have := evalMul_aux (v 0) (vtail v)
    rwa [vcons_head_tail v] at this⟩

theorem PrimRec1.add {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n + g n := PrimRec1.comp2 PrimRec2.add hf hg

theorem PrimRec1.mul {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n * g n := PrimRec1.comp2 PrimRec2.mul hf hg

theorem PrimRec1.sub {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n - g n := PrimRec1.comp2 PrimRec2.sub hf hg

theorem PrimRec2.eqInd : PrimRec2 Rcat.eqInd :=
  PrimRec2.comp2 (H := fun a b => a - b) PrimRec2.sub
    (PrimRec2.comp2 (H := fun _ _ => (1 : Nat)) (PrimRec2.ofFst (PrimRec1.const 1))
      PrimRec2.fstArg PrimRec2.sndArg)
    (PrimRec2.comp2 PrimRec2.add PrimRec2.sub (PrimRec2.swap PrimRec2.sub))

/-- `if n = c then a else w n` is primitive recursive when `w` is. -/
theorem PrimRec1.ifEqConst (c a : Nat) {w : Nat → Nat} (hw : PrimRec1 w) :
    PrimRec1 fun n => if n = c then a else w n := by
  have hind : PrimRec1 fun n => eqInd n c :=
    PrimRec1.comp2 PrimRec2.eqInd PrimRec1.id (PrimRec1.const c)
  have harith : PrimRec1 fun n => a * eqInd n c + w n * (1 - eqInd n c) :=
    PrimRec1.add (PrimRec1.mul (PrimRec1.const a) hind)
      (PrimRec1.mul hw (PrimRec1.sub (PrimRec1.const 1) hind))
  refine harith.congr fun n => ?_
  by_cases h : n = c
  · rw [if_pos h, eqInd_eq h]; simp
  · rw [if_neg h, eqInd_ne h]; simp

/-- Any finite lookup table (0 outside its domain) is primitive recursive — the book's
    "any function from a finite natural number" convention, in P. -/
theorem PrimRec1.finTable (m : Nat) (t : Fin m → Nat) :
    PrimRec1 fun j => if h : j < m then t ⟨j, h⟩ else 0 := by
  induction m with
  | zero =>
    refine (PrimRec1.const 0).congr fun n => ?_
    rw [dif_neg (by omega)]
  | succ m ih =>
    have prev := ih fun i => t i.castSucc
    have := PrimRec1.ifEqConst m (t ⟨m, Nat.lt_succ_self m⟩) prev
    refine this.congr fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      rw [if_pos rfl, dif_pos (Nat.lt_succ_self j)]
    · rw [if_neg hjm]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (Nat.lt_succ_of_lt hj)]
        rfl
      · rw [dif_neg hj, dif_neg (by omega)]

/-- Unary primitive recursion (`natIter`) preserves primitive recursiveness —
    §1.572's `Recursive1.natIter` restricted to mu-free codes. -/
theorem PrimRec1.natIter (g0 : Nat) {H : Nat → Nat → Nat} (hH : PrimRec2 H) :
    PrimRec1 (Rcat.natIter g0 H) := by
  obtain ⟨cH, pH, hcH⟩ := hH
  refine ⟨.prec (constCode 0 g0) cH, ⟨isPrim_constCode 0 g0, pH⟩, fun v => ?_⟩
  have key : ∀ (n : Nat) (w : Vec 0),
      Eval (.prec (constCode 0 g0) cH) (vcons n w) (Rcat.natIter g0 H n) := by
    intro n w
    induction n with
    | zero => exact .prec_zero rfl (evalConst 0 g0 w)
    | succ n ih =>
      refine .prec_succ rfl ih ?_
      exact hcH (vcons n (vcons (Rcat.natIter g0 H n) w))
  have := key (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

theorem PrimRec1.tri : PrimRec1 Rcat.tri :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add PrimRec2.sndArg
    (PrimRec2.comp2 PrimRec2.add PrimRec2.fstArg (PrimRec2.ofFst (PrimRec1.const 1))))

/-! ## Part 2: the Cantor projections and div/mod are primitive recursive

  §1.572 computed the Cantor weight `cw` and `·/(m+1)`, `·%(m+1)` by unbounded
  mu-search.  Here they are re-done mu-free: each satisfies a first-order recursion,
  so `natIter` (= a `prec` code) suffices — bounded search is not even needed. -/

/-- Mu-free Cantor weight: the diagonal index of `c`, by unary primitive recursion —
    it increments exactly when `c+1` reaches the next triangular number. -/
def cwP : Nat → Nat := natIter 0 fun c r => r + eqInd (c + 1) (tri (r + 1))

theorem cwP_zero : cwP 0 = 0 := rfl

theorem cwP_succ (c : Nat) : cwP (c + 1) = cwP c + eqInd (c + 1) (tri (cwP c + 1)) := rfl

theorem PrimRec1.cwP : PrimRec1 Pcat.cwP :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add PrimRec2.sndArg
    (PrimRec2.comp2 PrimRec2.eqInd
      (PrimRec2.ofFst (PrimRec1.add PrimRec1.id (PrimRec1.const 1)))
      (PrimRec2.ofSnd (PrimRec1.comp
        (PrimRec1.add PrimRec1.id (PrimRec1.const 1)) PrimRec1.tri))))

/-- `cwP` sandwiches `c` between consecutive triangular numbers. -/
theorem cwP_spec (c : Nat) : tri (cwP c) ≤ c ∧ c < tri (cwP c + 1) := by
  induction c with
  | zero =>
    rw [cwP_zero]
    refine ⟨Nat.le_refl 0, ?_⟩
    rw [tri_succ, tri_zero]
    omega
  | succ c ih =>
    rw [cwP_succ]
    by_cases h : c + 1 = tri (cwP c + 1)
    · rw [eqInd_eq h]
      have hstep : tri (cwP c + 1 + 1) = tri (cwP c + 1) + (cwP c + 1 + 1) :=
        tri_succ (cwP c + 1)
      exact ⟨by omega, by omega⟩
    · rw [eqInd_ne h, Nat.add_zero]
      exact ⟨by omega, by omega⟩

theorem cwP_eq_cw (c : Nat) : cwP c = cw c := by
  refine (theLeast_unique (fun s => c < tri (s + 1))
    ⟨c, by have := le_tri (c + 1); omega⟩ (cwP_spec c).2 fun i hi => ?_).symm
  show ¬c < tri (i + 1)
  have h1 : tri (i + 1) ≤ tri (cwP c) := tri_mono (by omega)
  have h2 := (cwP_spec c).1
  omega

theorem PrimRec1.cw : PrimRec1 Rcat.cw := PrimRec1.cwP.congr cwP_eq_cw

theorem PrimRec1.csnd : PrimRec1 Rcat.csnd :=
  (PrimRec1.sub PrimRec1.id (PrimRec1.comp PrimRec1.cw PrimRec1.tri)).congr
    fun _ => rfl

theorem PrimRec1.cfst : PrimRec1 Rcat.cfst :=
  (PrimRec1.sub PrimRec1.cw PrimRec1.csnd).congr fun _ => rfl

theorem PrimRec2.cp : PrimRec2 Rcat.cp := by
  have h : PrimRec2 fun a b => Rcat.tri (a + b) + b :=
    PrimRec2.comp2 PrimRec2.add
      (PrimRec2.comp2 (PrimRec2.ofSnd PrimRec1.tri) PrimRec2.fstArg PrimRec2.add)
      PrimRec2.sndArg
  exact h.congr fun _ _ => rfl

/-! ### Division and remainder by a positive constant, mu-free -/

/-- Mu-free remainder mod `m+1`: unary recursion cycling through `0, 1, …, m, 0, …`. -/
def modP (m : Nat) : Nat → Nat :=
  natIter 0 fun _ r => (r + 1) * (1 - eqInd (r + 1) (m + 1))

theorem modP_succ (m c : Nat) :
    modP m (c + 1) = (modP m c + 1) * (1 - eqInd (modP m c + 1) (m + 1)) := rfl

theorem PrimRec1.modP (m : Nat) : PrimRec1 (Pcat.modP m) := by
  have hA : PrimRec2 fun (_ r : Nat) => r + 1 :=
    PrimRec2.comp2 PrimRec2.add PrimRec2.sndArg (PrimRec2.ofFst (PrimRec1.const 1))
  exact PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.mul hA
    (PrimRec2.comp2 PrimRec2.sub (PrimRec2.ofFst (PrimRec1.const 1))
      (PrimRec2.comp2 PrimRec2.eqInd hA (PrimRec2.ofFst (PrimRec1.const (m + 1))))))

theorem modP_eq (m c : Nat) : Pcat.modP m c = c % (m + 1) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hq := Nat.div_add_mod c (m + 1)
    rw [modP_succ, ih]
    have hmc : (c / (m + 1)) * (m + 1) = (m + 1) * (c / (m + 1)) := Nat.mul_comm _ _
    by_cases h : c % (m + 1) + 1 = m + 1
    · rw [h, eqInd_eq rfl]
      have hsucc : (c / (m + 1) + 1) * (m + 1) = (m + 1) * (c / (m + 1)) + (m + 1) := by
        rw [Nat.succ_mul, Nat.mul_comm]
      have hc1 : c + 1 = (c / (m + 1) + 1) * (m + 1) + 0 := by omega
      rw [hc1, mulAdd_mod m _ 0 (Nat.succ_pos m)]
      simp
    · rw [eqInd_ne h]
      have hmod : c % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
      have hc1 : c + 1 = (c / (m + 1)) * (m + 1) + (c % (m + 1) + 1) := by omega
      rw [hc1, mulAdd_mod m _ _ (by omega)]
      simp

theorem PrimRec1.modConst (m : Nat) : PrimRec1 fun c => c % (m + 1) :=
  (PrimRec1.modP m).congr (modP_eq m)

/-- Mu-free quotient by `m+1`: increments exactly when the remainder wraps around. -/
def divP (m : Nat) : Nat → Nat := natIter 0 fun c r => r + eqInd (modP m c) m

theorem divP_succ (m c : Nat) : divP m (c + 1) = divP m c + eqInd (modP m c) m := rfl

theorem PrimRec1.divP (m : Nat) : PrimRec1 (Pcat.divP m) :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add PrimRec2.sndArg
    (PrimRec2.ofFst (PrimRec1.comp2 PrimRec2.eqInd (PrimRec1.modP m)
      (PrimRec1.const m))))

theorem divP_eq (m c : Nat) : Pcat.divP m c = c / (m + 1) := by
  induction c with
  | zero => rw [Nat.zero_div]; rfl
  | succ c ih =>
    have hq := Nat.div_add_mod c (m + 1)
    have hmod : c % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
    have hmc : (c / (m + 1)) * (m + 1) = (m + 1) * (c / (m + 1)) := Nat.mul_comm _ _
    rw [divP_succ, ih, modP_eq]
    by_cases h : c % (m + 1) = m
    · rw [eqInd_eq h]
      have hsucc : (c / (m + 1) + 1) * (m + 1) = (m + 1) * (c / (m + 1)) + (m + 1) := by
        rw [Nat.succ_mul, Nat.mul_comm]
      have hc1 : c + 1 = (c / (m + 1) + 1) * (m + 1) + 0 := by omega
      rw [hc1, mulAdd_div m _ 0 (Nat.succ_pos m)]
    · rw [eqInd_ne h, Nat.add_zero]
      have hc1 : c + 1 = (c / (m + 1)) * (m + 1) + (c % (m + 1) + 1) := by omega
      rw [hc1, mulAdd_div m _ _ (by omega)]

theorem PrimRec1.divConst (m : Nat) : PrimRec1 fun c => c / (m + 1) :=
  (PrimRec1.divP m).congr (divP_eq m)

end Freyd.Pcat
