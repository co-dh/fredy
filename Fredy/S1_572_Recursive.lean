/-
  Freyd & Scedrov, *Categories and Allegories* §1.572
  The category **R** of recursive functions.

  Objects: the extended natural numbers 0, 1, 2, …, ω (von Neumann: α = {β | β < α}),
  encoded as `ExtNat := Option Nat` (`some n` = the finite ordinal n, `none` = ω).
  Morphisms: recursive functions; any function from a finite natural number is
  understood to be recursive (book convention).

  **R is an AC regular category** (§1.572): given x : α → β define e : α → α by
  e(n) = min{ i ≤ n | x(i) = x(n) }; then e² = e, ex = x, e and x have the same
  level, and §1.571 (`ac_factorization_via_idempotent`) applies.

  Computability is hand-rolled (STRICTLY MATHLIB-FREE): Kleene's n-ary μ-recursive
  codes `RecCode` with a big-step evaluation relation `Eval`.  `Recursive` means
  "computed by a code that converges on every input".
-/

import Fredy.S1_57

open Freyd

namespace Freyd.Rcat

/-! ## Part 1: μ-recursive codes and their semantics -/

/-- Input vectors: `k`-tuples of naturals. -/
abbrev Vec (k : Nat) := Fin k → Nat

/-- Prepend a value to an input vector. -/
def vcons {k : Nat} (a : Nat) (v : Vec k) : Vec (k + 1) := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨j+1, h⟩ => v ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first entry of an input vector. -/
def vtail {k : Nat} (v : Vec (k + 1)) : Vec k := fun i => v i.succ

@[simp] theorem vcons_zero {k : Nat} (a : Nat) (v : Vec k) : vcons a v 0 = a := rfl

@[simp] theorem vcons_one {k : Nat} (a : Nat) (v : Vec (k + 1)) : vcons a v 1 = v 0 := rfl

@[simp] theorem vcons_succ {k : Nat} (a : Nat) (v : Vec k) (i : Fin k) :
    vcons a v i.succ = v i := rfl

@[simp] theorem vtail_vcons {k : Nat} (a : Nat) (v : Vec k) : vtail (vcons a v) = v := rfl

theorem vcons_head_tail {k : Nat} (v : Vec (k + 1)) : vcons (v 0) (vtail v) = v := by
  funext i
  rcases i with ⟨(_ | j), h⟩
  · rfl
  · rfl

/-- Kleene's μ-recursive codes, `k` = arity.  `zero` is arity-polymorphic (the
    constantly-0 function), `succ` is unary successor, `proj i` the i-th projection,
    `comp` composition, `prec` primitive recursion on the FIRST argument, `mu`
    unbounded minimization on a new first argument. -/
inductive RecCode : Nat → Type where
  | zero {k : Nat} : RecCode k
  | succ : RecCode 1
  | proj {k : Nat} (i : Fin k) : RecCode k
  | comp {k m : Nat} (f : RecCode m) (gs : Fin m → RecCode k) : RecCode k
  | prec {k : Nat} (g : RecCode k) (h : RecCode (k + 2)) : RecCode (k + 1)
  | mu {k : Nat} (f : RecCode (k + 1)) : RecCode k

/-- Big-step convergence: `Eval c v y` means code `c` on input `v` halts with output `y`.
    `prec g h`: value at `0::v` is `g v`; at `(n+1)::v` it is `h (n :: r :: v)` where `r`
    is the value at `n::v`.  `mu f`: the least `y` with `f (y::v) = 0`, all smaller
    arguments converging to a nonzero value (witnessed by `r · + 1`). -/
inductive Eval : {k : Nat} → RecCode k → Vec k → Nat → Prop where
  | zero {k : Nat} {v : Vec k} : Eval .zero v 0
  | succ {v : Vec 1} : Eval .succ v (v 0 + 1)
  | proj {k : Nat} (i : Fin k) {v : Vec k} : Eval (.proj i) v (v i)
  | comp {k m : Nat} {f : RecCode m} {gs : Fin m → RecCode k} {v : Vec k} {y : Nat}
      (w : Vec m) (hg : ∀ j, Eval (gs j) v (w j)) (hf : Eval f w y) :
      Eval (.comp f gs) v y
  | prec_zero {k : Nat} {g : RecCode k} {h : RecCode (k + 2)} {v : Vec (k + 1)} {y : Nat}
      (h0 : v 0 = 0) (hg : Eval g (vtail v) y) : Eval (.prec g h) v y
  | prec_succ {k : Nat} {g : RecCode k} {h : RecCode (k + 2)} {v : Vec (k + 1)} {n r y : Nat}
      (h0 : v 0 = n + 1) (hr : Eval (.prec g h) (vcons n (vtail v)) r)
      (hh : Eval h (vcons n (vcons r (vtail v))) y) : Eval (.prec g h) v y
  | mu {k : Nat} {f : RecCode (k + 1)} {v : Vec k} {y : Nat} (r : Nat → Nat)
      (hy : Eval f (vcons y v) 0) (hlt : ∀ i, i < y → Eval f (vcons i v) (r i + 1)) :
      Eval (.mu f) v y

/-- `Eval` is single-valued (functionality). -/
theorem Eval.det {k : Nat} {c : RecCode k} {v : Vec k} {y₁ : Nat}
    (h₁ : Eval c v y₁) : ∀ {y₂ : Nat}, Eval c v y₂ → y₁ = y₂ := by
  induction h₁ with
  | zero => intro y₂ h₂; cases h₂; rfl
  | succ => intro y₂ h₂; cases h₂; rfl
  | proj i => intro y₂ h₂; cases h₂; rfl
  | comp w hg hf ihg ihf =>
    intro y₂ h₂
    cases h₂ with
    | comp w' hg' hf' =>
      have hw : w = w' := funext fun j => ihg j (hg' j)
      exact ihf (hw ▸ hf')
  | prec_zero h0 hg ihg =>
    intro y₂ h₂
    cases h₂ with
    | prec_zero h0' hg' => exact ihg hg'
    | prec_succ h0' hr' hh' => omega
  | prec_succ h0 hr hh ihr ihh =>
    rename_i n r y
    intro y₂ h₂
    cases h₂ with
    | prec_zero h0' hg' => omega
    | prec_succ h0' hr' hh' =>
      rename_i n' r'
      have hn : n = n' := by omega
      subst hn
      have hrr : r = r' := ihr hr'
      subst hrr
      exact ihh hh'
  | mu r hy hlt ihy ihlt =>
    rename_i y
    intro y₂ h₂
    cases h₂ with
    | mu r' hy' hlt' =>
      rcases Nat.lt_trichotomy y y₂ with h | h | h
      · exact absurd (ihy (hlt' _ h)) (by omega)
      · exact h
      · exact absurd (ihlt _ h hy') (by omega)

/-! ### Recursive functions -/

/-- A `k`-ary function is RECURSIVE if some code converges to its value on every input. -/
def RecursiveV {k : Nat} (f : Vec k → Nat) : Prop := ∃ c : RecCode k, ∀ v, Eval c v (f v)

/-- Unary recursive functions ℕ → ℕ. -/
def Recursive1 (f : Nat → Nat) : Prop := RecursiveV fun v : Vec 1 => f (v 0)

/-- Binary recursive functions ℕ → ℕ → ℕ. -/
def Recursive2 (f : Nat → Nat → Nat) : Prop := RecursiveV fun v : Vec 2 => f (v 0) (v 1)

theorem RecursiveV.congr {k : Nat} {f g : Vec k → Nat} (hf : RecursiveV f)
    (h : ∀ v, f v = g v) : RecursiveV g := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun v => h v ▸ hc v⟩

theorem Recursive1.congr {f g : Nat → Nat} (hf : Recursive1 f) (h : ∀ n, f n = g n) :
    Recursive1 g := RecursiveV.congr hf fun v => h (v 0)

theorem Recursive2.congr {f g : Nat → Nat → Nat} (hf : Recursive2 f)
    (h : ∀ a b, f a b = g a b) : Recursive2 g := RecursiveV.congr hf fun v => h (v 0) (v 1)

theorem RecursiveV.proj {k : Nat} (i : Fin k) : RecursiveV (fun v : Vec k => v i) :=
  ⟨.proj i, fun _ => .proj i⟩

theorem Recursive1.id : Recursive1 fun n => n := RecursiveV.proj 0

theorem Recursive2.fstArg : Recursive2 fun a _ => a := RecursiveV.proj 0

theorem Recursive2.sndArg : Recursive2 fun _ b => b := RecursiveV.proj 1

/-- Code for the constant function `c`. -/
def constCode (k c : Nat) : RecCode k :=
  match c with
  | 0 => .zero
  | c + 1 => .comp .succ fun _ => constCode k c

theorem evalConst (k c : Nat) (v : Vec k) : Eval (constCode k c) v c := by
  induction c with
  | zero => exact .zero
  | succ c ih => exact .comp (fun _ => c) (fun _ => ih) .succ

theorem RecursiveV.const (k c : Nat) : RecursiveV (fun _ : Vec k => c) :=
  ⟨constCode k c, fun v => evalConst k c v⟩

theorem Recursive1.const (c : Nat) : Recursive1 fun _ => c := RecursiveV.const 1 c

/-- Closure under composition (general form). -/
theorem RecursiveV.comp {k m : Nat} {f : Vec m → Nat} {gs : Fin m → Vec k → Nat}
    (hf : RecursiveV f) (hgs : ∀ j, RecursiveV (gs j)) :
    RecursiveV (fun v => f fun j => gs j v) := by
  obtain ⟨cf, hcf⟩ := hf
  exact ⟨.comp cf (fun j => Classical.choose (hgs j)),
    fun v => .comp (fun j => gs j v) (fun j => Classical.choose_spec (hgs j) v) (hcf _)⟩

theorem Recursive1.comp {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => g (f n) :=
  RecursiveV.comp (f := fun w : Vec 1 => g (w 0)) (gs := fun _ v => f (v 0)) hg fun _ => hf

/-- Unary post-composition at any arity. -/
theorem RecursiveV.comp1 {k : Nat} {F : Nat → Nat} {f : Vec k → Nat}
    (hF : Recursive1 F) (hf : RecursiveV f) : RecursiveV (fun v => F (f v)) :=
  RecursiveV.comp (f := fun w : Vec 1 => F (w 0)) (gs := fun _ v => f v) hF fun _ => hf

/-- Binary combination at any arity: from a recursive binary `H` and recursive
    arguments, `v ↦ H (f v) (g v)` is recursive. -/
theorem RecursiveV.comp2 {k : Nat} {H : Nat → Nat → Nat} {f g : Vec k → Nat}
    (hH : Recursive2 H) (hf : RecursiveV f) (hg : RecursiveV g) :
    RecursiveV (fun v => H (f v) (g v)) := by
  obtain ⟨cH, hcH⟩ := hH
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨cg, hcg⟩ := hg
  refine ⟨.comp cH (fun j => if j.val = 0 then cf else cg), fun v => ?_⟩
  refine .comp (vcons (f v) (fun _ => g v)) (fun j => ?_) ?_
  · rcases j with ⟨jv, hj⟩
    match jv, hj with
    | 0, _ => exact hcf v
    | 1, _ => exact hcg v
  · exact hcH (vcons (f v) fun _ => g v)

theorem Recursive1.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat}
    (hH : Recursive2 H) (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => H (f n) (g n) :=
  RecursiveV.comp2 (f := fun v : Vec 1 => f (v 0)) (g := fun v : Vec 1 => g (v 0)) hH hf hg

theorem Recursive2.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat → Nat}
    (hH : Recursive2 H) (hf : Recursive2 f) (hg : Recursive2 g) :
    Recursive2 fun a b => H (f a b) (g a b) :=
  RecursiveV.comp2 (f := fun v : Vec 2 => f (v 0) (v 1)) (g := fun v : Vec 2 => g (v 0) (v 1))
    hH hf hg

theorem Recursive2.swap {f : Nat → Nat → Nat} (hf : Recursive2 f) :
    Recursive2 fun a b => f b a :=
  Recursive2.comp2 hf Recursive2.sndArg Recursive2.fstArg

theorem Recursive2.ofFst {f : Nat → Nat} (hf : Recursive1 f) : Recursive2 fun a _ => f a :=
  RecursiveV.comp1 (f := fun v : Vec 2 => v 0) hf (RecursiveV.proj 0)

theorem Recursive2.ofSnd {f : Nat → Nat} (hf : Recursive1 f) : Recursive2 fun _ b => f b :=
  RecursiveV.comp1 (f := fun v : Vec 2 => v 1) hf (RecursiveV.proj 1)

/-! ### Arithmetic base: addition, predecessor, truncated subtraction, multiplication -/

/-- Addition code: recursion on the first argument, `add (n+1) b = add n b + 1`. -/
def addCode : RecCode 2 := .prec (.proj 0) (.comp .succ fun _ => .proj 1)

theorem evalAdd_aux : ∀ (n : Nat) (w : Vec 1), Eval addCode (vcons n w) (w 0 + n) := by
  intro n w
  induction n with
  | zero => exact .prec_zero rfl (.proj 0)
  | succ n ih =>
    exact .prec_succ rfl ih (.comp (fun _ => w 0 + n) (fun _ => .proj 1) .succ)

theorem evalAdd (v : Vec 2) : Eval addCode v (v 1 + v 0) := by
  have := evalAdd_aux (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

theorem Recursive2.add : Recursive2 fun a b => a + b := by
  refine RecursiveV.congr (g := fun v : Vec 2 => v 0 + v 1) ⟨addCode, fun v => evalAdd v⟩ ?_
  intro v
  exact Nat.add_comm (v 1) (v 0)

/-- Predecessor code (unary): `pred 0 = 0`, `pred (n+1) = n`. -/
def predCode : RecCode 1 := .prec .zero (.proj 0)

theorem evalPred_aux : ∀ (n : Nat) (w : Vec 0), Eval predCode (vcons n w) (n - 1) := by
  intro n w
  cases n with
  | zero => exact .prec_zero rfl .zero
  | succ n => exact .prec_succ rfl (evalPred_aux n w) (.proj 0)

theorem evalPred (v : Vec 1) : Eval predCode v (v 0 - 1) := by
  have := evalPred_aux (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

/-- Truncated subtraction, recursion on the FIRST argument: `rsub n a = a - n`. -/
def rsubCode : RecCode 2 := .prec (.proj 0) (.comp predCode fun _ => .proj 1)

theorem evalRsub_aux : ∀ (n : Nat) (w : Vec 1), Eval rsubCode (vcons n w) (w 0 - n) := by
  intro n w
  induction n with
  | zero => exact .prec_zero rfl (.proj 0)
  | succ n ih =>
    have hstep : Eval (.comp predCode fun _ => .proj 1)
        (vcons n (vcons (w 0 - n) w)) (w 0 - (n + 1)) := by
      have : w 0 - (n + 1) = (w 0 - n) - 1 := by omega
      rw [this]
      exact .comp (fun _ => w 0 - n) (fun _ => .proj (1 : Fin 3)) (evalPred _)
    exact .prec_succ rfl ih hstep

theorem Recursive2.sub : Recursive2 fun a b => a - b := by
  have h : Recursive2 fun a b => b - a :=
    ⟨rsubCode, fun v => by
      have := evalRsub_aux (v 0) (vtail v)
      rwa [vcons_head_tail v] at this⟩
  exact Recursive2.swap h

/-- Multiplication code: `mul 0 b = 0`, `mul (n+1) b = mul n b + b`. -/
def mulCode : RecCode 2 :=
  .prec .zero (.comp addCode fun j => if j.val = 0 then .proj 1 else .proj 2)

theorem evalMul_aux : ∀ (n : Nat) (w : Vec 1), Eval mulCode (vcons n w) (n * w 0) := by
  intro n w
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    exact .prec_zero rfl .zero
  | succ n ih =>
    have hstep : Eval (.comp addCode fun j : Fin 2 => if j.val = 0 then .proj 1 else .proj 2)
        (vcons n (vcons (n * w 0) w)) ((n + 1) * w 0) := by
      refine .comp (vcons (n * w 0) fun _ => w 0) (fun j => ?_) ?_
      · rcases j with ⟨jv, hj⟩
        match jv, hj with
        | 0, _ => exact .proj (1 : Fin 3)
        | 1, _ => exact .proj (2 : Fin 3)
      · have : (n + 1) * w 0 = w 0 + n * w 0 := by
          rw [Nat.succ_mul, Nat.add_comm]
        rw [this]
        exact evalAdd _
    exact .prec_succ rfl ih hstep

theorem Recursive2.mul : Recursive2 fun a b => a * b :=
  ⟨mulCode, fun v => by
    have := evalMul_aux (v 0) (vtail v)
    rwa [vcons_head_tail v] at this⟩

/-! ### Derived pointwise combinators (unary level) -/

theorem Recursive1.add {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n + g n := Recursive1.comp2 Recursive2.add hf hg

theorem Recursive1.mul {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n * g n := Recursive1.comp2 Recursive2.mul hf hg

theorem Recursive1.sub {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n - g n := Recursive1.comp2 Recursive2.sub hf hg

/-- The equality indicator `1` if `a = b` else `0`, arithmetically:
    `1 - ((a-b)+(b-a))`. -/
def eqInd (a b : Nat) : Nat := 1 - ((a - b) + (b - a))

theorem eqInd_eq {a b : Nat} (h : a = b) : eqInd a b = 1 := by simp [eqInd, h]

theorem eqInd_ne {a b : Nat} (h : a ≠ b) : eqInd a b = 0 := by
  unfold eqInd; omega

theorem Recursive2.eqInd : Recursive2 Rcat.eqInd :=
  Recursive2.comp2 (H := fun a b => a - b) Recursive2.sub
    (Recursive2.comp2 (H := fun _ _ => (1 : Nat)) (Recursive2.ofFst (Recursive1.const 1))
      Recursive2.fstArg Recursive2.sndArg)
    (Recursive2.comp2 Recursive2.add Recursive2.sub (Recursive2.swap Recursive2.sub))

/-- `if n = c then a else w n` is recursive when `w` is (constant-case update). -/
theorem Recursive1.ifEqConst (c a : Nat) {w : Nat → Nat} (hw : Recursive1 w) :
    Recursive1 fun n => if n = c then a else w n := by
  have hind : Recursive1 fun n => eqInd n c :=
    Recursive1.comp2 Recursive2.eqInd Recursive1.id (Recursive1.const c)
  have harith : Recursive1 fun n => a * eqInd n c + w n * (1 - eqInd n c) :=
    Recursive1.add (Recursive1.mul (Recursive1.const a) hind)
      (Recursive1.mul hw (Recursive1.sub (Recursive1.const 1) hind))
  refine harith.congr fun n => ?_
  by_cases h : n = c
  · rw [if_pos h, eqInd_eq h]; simp
  · rw [if_neg h, eqInd_ne h]; simp

/-- Any finite lookup table (0 outside its domain) is recursive.  This is the
    formal content of the book's "any function from a finite natural number is
    understood to be recursive". -/
theorem Recursive1.finTable (m : Nat) (t : Fin m → Nat) :
    Recursive1 fun j => if h : j < m then t ⟨j, h⟩ else 0 := by
  induction m with
  | zero =>
    refine (Recursive1.const 0).congr fun n => ?_
    rw [dif_neg (by omega)]
  | succ m ih =>
    have prev := ih fun i => t i.castSucc
    have := Recursive1.ifEqConst m (t ⟨m, Nat.lt_succ_self m⟩) prev
    refine this.congr fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      rw [if_pos rfl, dif_pos (Nat.lt_succ_self j)]
    · rw [if_neg hjm]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (Nat.lt_succ_of_lt hj)]
        rfl
      · rw [dif_neg hj, dif_neg (by omega)]

/-- Closure under total minimization: if `t` is a recursive binary test and `f n`
    is the least `i` with `t i n = 0` (which always exists), then `f` is recursive.
    This is the only place unbounded search enters. -/
theorem Recursive1.mu {t : Nat → Nat → Nat} (ht : Recursive2 t) {f : Nat → Nat}
    (hzero : ∀ n, t (f n) n = 0) (hpos : ∀ n i, i < f n → t i n ≠ 0) : Recursive1 f := by
  obtain ⟨ct, hct⟩ := ht
  refine ⟨.mu ct, fun v => ?_⟩
  refine .mu (fun i => t i (v 0) - 1) ?_ ?_
  · have h := hct (vcons (f (v 0)) v)
    simpa [hzero (v 0)] using h
  · intro i hi
    have h := hct (vcons i v)
    have hne := hpos (v 0) i hi
    have : t i (v 0) - 1 + 1 = t i (v 0) := by omega
    rw [this]
    simpa using h

/-! ## Part 2: least elements, primitive recursion helper, Cantor pairing, div/mod -/

/-- Every inhabited predicate on ℕ has a least witness (classical, no decidability). -/
theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ i, i < n → ¬P i := by
  obtain ⟨n, hn⟩ := h
  have aux : ∀ b, (∃ i, i ≤ b ∧ P i) → ∃ m, P m ∧ ∀ i, i < m → ¬P i := by
    intro b
    induction b with
    | zero =>
      rintro ⟨i, hi, hPi⟩
      have : i = 0 := by omega
      subst this
      exact ⟨0, hPi, by omega⟩
    | succ b ih =>
      rintro ⟨i, hi, hPi⟩
      rcases Classical.em (∃ j, j ≤ b ∧ P j) with hj | hj
      · exact ih hj
      · have hib : i = b + 1 := by
          rcases Nat.lt_or_ge i (b + 1) with h' | h'
          · exact absurd ⟨i, by omega, hPi⟩ hj
          · omega
        subst hib
        exact ⟨b + 1, hPi, fun j hjlt hPj => hj ⟨j, by omega, hPj⟩⟩
  exact aux n ⟨n, Nat.le_refl n, hn⟩

/-- The least witness of an inhabited predicate. -/
noncomputable def theLeast (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  Classical.choose (exists_least h)

theorem theLeast_mem (P : Nat → Prop) (h : ∃ n, P n) : P (theLeast P h) :=
  (Classical.choose_spec (exists_least h)).1

theorem theLeast_min (P : Nat → Prop) (h : ∃ n, P n) :
    ∀ i, i < theLeast P h → ¬P i :=
  (Classical.choose_spec (exists_least h)).2

theorem theLeast_le (P : Nat → Prop) (h : ∃ n, P n) {n : Nat} (hn : P n) :
    theLeast P h ≤ n := by
  rcases Nat.lt_or_ge n (theLeast P h) with h' | h'
  · exact absurd hn (theLeast_min P h n h')
  · exact h'

/-- The least witness is unique: anything satisfying the least-characterization is it. -/
theorem theLeast_unique (P : Nat → Prop) (h : ∃ n, P n) {n : Nat}
    (hn : P n) (hmin : ∀ i, i < n → ¬P i) : theLeast P h = n := by
  have h₁ := theLeast_le P h hn
  rcases Nat.lt_or_ge (theLeast P h) n with h' | h'
  · exact absurd (theLeast_mem P h) (hmin _ h')
  · omega

/-! ### Unary primitive recursion -/

/-- Unary primitive recursion: `natIter g0 H 0 = g0`, `natIter g0 H (n+1) = H n (natIter g0 H n)`. -/
def natIter (g0 : Nat) (H : Nat → Nat → Nat) : Nat → Nat
  | 0 => g0
  | n + 1 => H n (natIter g0 H n)

theorem Recursive1.natIter (g0 : Nat) {H : Nat → Nat → Nat} (hH : Recursive2 H) :
    Recursive1 (Rcat.natIter g0 H) := by
  obtain ⟨cH, hcH⟩ := hH
  refine ⟨.prec (constCode 0 g0) cH, fun v => ?_⟩
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

/-! ### Cantor pairing -/

/-- Triangular numbers: `tri s = 0 + 1 + ⋯ + s`. -/
def tri : Nat → Nat := natIter 0 fun s r => r + (s + 1)

@[simp] theorem tri_zero : tri 0 = 0 := rfl

@[simp] theorem tri_succ (s : Nat) : tri (s + 1) = tri s + (s + 1) := rfl

theorem Recursive1.tri : Recursive1 Rcat.tri :=
  Recursive1.natIter 0 (Recursive2.comp2 Recursive2.add Recursive2.sndArg
    (Recursive2.comp2 Recursive2.add Recursive2.fstArg
      (Recursive2.ofFst (Recursive1.const 1))))

theorem le_tri (s : Nat) : s ≤ tri s := by
  cases s with
  | zero => exact Nat.le_refl 0
  | succ s => rw [tri_succ]; omega

theorem tri_mono {s t : Nat} (h : s ≤ t) : tri s ≤ tri t := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h' | h'
    · have := ih (by omega)
      rw [tri_succ]; omega
    · have : s = t + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Cantor pairing: `cp a b = tri (a+b) + b`, a bijection ℕ×ℕ → ℕ. -/
def cp (a b : Nat) : Nat := tri (a + b) + b

theorem Recursive2.cp : Recursive2 Rcat.cp := by
  have h : Recursive2 fun a b => Rcat.tri (a + b) + b :=
    Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 (Recursive2.ofSnd Recursive1.tri) Recursive2.fstArg Recursive2.add)
      Recursive2.sndArg
  exact h.congr fun _ _ => rfl

/-- The "weight" of a code: the least `s` with `c < tri (s+1)`; equals `a+b` for `c = cp a b`. -/
noncomputable def cw (c : Nat) : Nat :=
  theLeast (fun s => c < tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩

theorem cw_lt (c : Nat) : c < tri (cw c + 1) :=
  theLeast_mem (fun s => c < tri (s + 1)) _

theorem tri_cw_le (c : Nat) : tri (cw c) ≤ c := by
  cases hcw : cw c with
  | zero => rw [tri_zero]; omega
  | succ s =>
    have hmin : ¬c < tri (s + 1) :=
      theLeast_min (fun s => c < tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩ s
        (show s < cw c by omega)
    omega

theorem cw_cp (a b : Nat) : cw (cp a b) = a + b := by
  refine theLeast_unique _ _ ?_ ?_
  · show cp a b < tri (a + b + 1)
    rw [tri_succ]
    unfold cp
    omega
  · intro s hs
    show ¬cp a b < tri (s + 1)
    have : tri (s + 1) ≤ tri (a + b) := tri_mono (by omega)
    unfold cp
    omega

/-- Second Cantor projection. -/
noncomputable def csnd (c : Nat) : Nat := c - tri (cw c)

/-- First Cantor projection. -/
noncomputable def cfst (c : Nat) : Nat := cw c - csnd c

theorem csnd_cp (a b : Nat) : csnd (cp a b) = b := by
  unfold csnd
  rw [cw_cp]
  unfold cp
  omega

theorem cfst_cp (a b : Nat) : cfst (cp a b) = a := by
  unfold cfst
  rw [csnd_cp, cw_cp]
  omega

theorem csnd_le_cw (c : Nat) : csnd c ≤ cw c := by
  have h1 := cw_lt c
  have h2 := tri_cw_le c
  rw [tri_succ] at h1
  unfold csnd
  omega

theorem cp_surj (c : Nat) : cp (cfst c) (csnd c) = c := by
  have h1 := tri_cw_le c
  have h2 := csnd_le_cw c
  unfold cp cfst
  have : cw c - csnd c + csnd c = cw c := by omega
  rw [this]
  unfold csnd
  omega

theorem Recursive1.cw : Recursive1 Rcat.cw := by
  refine Recursive1.mu (t := fun s c => (c + 1) - Rcat.tri (s + 1)) ?_ ?_ ?_
  · exact Recursive2.comp2 Recursive2.sub
      (Recursive2.comp2 Recursive2.add Recursive2.sndArg (Recursive2.ofFst (Recursive1.const 1)))
      (Recursive2.ofFst (Recursive1.comp (f := fun s => s + 1)
        (Recursive1.add Recursive1.id (Recursive1.const 1)) Recursive1.tri))
  · intro c
    show (c + 1) - Rcat.tri (Rcat.cw c + 1) = 0
    have := cw_lt c
    omega
  · intro c s hs
    show (c + 1) - Rcat.tri (s + 1) ≠ 0
    have hmin : ¬c < Rcat.tri (s + 1) :=
      theLeast_min (fun s => c < Rcat.tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩ s hs
    omega

theorem Recursive1.csnd : Recursive1 Rcat.csnd :=
  (Recursive1.sub Recursive1.id (Recursive1.comp Recursive1.cw Recursive1.tri)).congr
    fun _ => rfl

theorem Recursive1.cfst : Recursive1 Rcat.cfst :=
  (Recursive1.sub Recursive1.cw Recursive1.csnd).congr fun _ => rfl

/-! ### Division and remainder by a positive constant -/

theorem Recursive1.divConst (m : Nat) : Recursive1 fun c => c / (m + 1) := by
  refine Recursive1.mu (t := fun q c => (c + 1) - (m + 1) * (q + 1)) ?_ ?_ ?_
  · exact Recursive2.comp2 Recursive2.sub
      (Recursive2.comp2 Recursive2.add Recursive2.sndArg (Recursive2.ofFst (Recursive1.const 1)))
      (Recursive2.comp2 Recursive2.mul (Recursive2.ofFst (Recursive1.const (m + 1)))
        (Recursive2.comp2 Recursive2.add Recursive2.fstArg
          (Recursive2.ofFst (Recursive1.const 1))))
  · intro c
    show (c + 1) - (m + 1) * (c / (m + 1) + 1) = 0
    have h1 := Nat.div_add_mod c (m + 1)
    have h2 := Nat.mod_lt c (y := m + 1) (by omega)
    have h3 : (m + 1) * (c / (m + 1) + 1) = (m + 1) * (c / (m + 1)) + (m + 1) :=
      Nat.mul_succ _ _
    omega
  · intro c q hq
    show (c + 1) - (m + 1) * (q + 1) ≠ 0
    have h1 : (q + 1) * (m + 1) ≤ (c / (m + 1)) * (m + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (c / (m + 1)) * (m + 1) ≤ c := Nat.div_mul_le_self c (m + 1)
    have h3 : (m + 1) * (q + 1) = (q + 1) * (m + 1) := Nat.mul_comm _ _
    omega

theorem Recursive1.modConst (m : Nat) : Recursive1 fun c => c % (m + 1) := by
  have h : Recursive1 fun c => c - (c / (m + 1)) * (m + 1) :=
    Recursive1.sub Recursive1.id
      (Recursive1.mul (Recursive1.divConst m) (Recursive1.const (m + 1)))
  refine h.congr fun c => ?_
  have h1 := Nat.div_add_mod c (m + 1)
  have h3 : (m + 1) * (c / (m + 1)) = (c / (m + 1)) * (m + 1) := Nat.mul_comm _ _
  omega

end Freyd.Rcat
