/-
  Freyd & Scedrov, *Categories, Allegories* §2.153 — the PARTIAL-RECURSIVE modulus
  system, and the concrete non-effectiveness of `Rel(Assembly Krec)`.

  `Fredy/S2_153_Assemblies.lean` builds the category of assemblies over an ABSTRACT
  modulus system `K` (a set `mem` of partial endofunctions of ℕ closed under identity,
  composition, a Cantor-style pairing `pairC`, and a tagged definition-by-cases
  `casesC`).  Its only concrete instance is `ModulusSystem.allPartial` (`mem = True`),
  over which the halting relation is total and the effective reflection IS AC.

  `Fredy/S2_153_NonEffective.lean` proves the REDUCTION
  `asmReflection_not_ac_of_nonsplitting`: a non-splitting equivalence relation on some
  assembly over `K` gives `¬ CoversSplit (AsmEffReflection K)`.

  This file supplies the missing concrete witness: `Krec`, the modulus system whose
  `mem` is `PartRec` = "graph of a partial recursive function", built on the Kleene
  codes `RecCode` / big-step `Eval` of `Fredy/S1_572_Recursive.lean` and the
  arithmetized checker of `Fredy/S1_572b_NotEffective.lean`.

  Layering (see the module tail for the exact status of each):
  * **L1** `PartRec` — the `mem` predicate.
  * **L2** its closures (`ModulusSystem` fields): identity, COMPOSITION, `pairC`,
    the total projection/tag data, and the tagged `casesC`.
  * **L3** a concrete non-splitting halting relation on an assembly over `Krec`.
  * **L4** the headline `¬ CoversSplit (AsmEffReflection Krec)`.

  MATHLIB-FREE.  Composition in DIAGRAM ORDER.
-/
import Fredy.S2_153_NonEffective
import Fredy.S1_572b_NotEffective

namespace Freyd

open Rcat

/-! ## Layer 1: partial-recursive graphs

  `PartRec φ` says the graph of the partial endofunction `φ` is computed by a single
  unary Kleene code `c`: for all `n, m`, `φ` is defined at `n` with value `m` exactly
  when `c` halts on the one-entry input `[n]` with output `m`.  Because `Eval` is
  single-valued (`Eval.det`) this is automatically functional, matching `ModFun`. -/

/-- The `mem` predicate of the partial-recursive modulus system. -/
def PartRec (φ : ModFun) : Prop :=
  ∃ c : RecCode 1, ∀ n m, φ.graph n m ↔ Eval c (fun _ => n) m

/-- A `Vec 1` is the constant vector at its single entry. -/
theorem vec1_eta (w : Vec 1) : w = fun _ => w 0 := by
  funext i
  rcases i with ⟨v, hv⟩
  have : v = 0 := by omega
  subst this
  rfl

/-- Every TOTAL recursive function's `ofFun` graph is partial recursive. -/
theorem partRec_ofFun {f : Nat → Nat} (hf : Recursive1 f) : PartRec (ModFun.ofFun f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun n m => ?_⟩
  have hcn : Eval c (fun _ => n) (f n) := hc (fun _ => n)
  constructor
  · intro h; rw [show m = f n from h]; exact hcn
  · intro h; exact (Eval.det hcn h).symm

/-- The identity graph is partial recursive (book (i)). -/
theorem partRec_ident : PartRec ModFun.ident := by
  refine ⟨.proj 0, fun n m => ?_⟩
  have h0 : Eval (.proj (0 : Fin 1)) (fun _ => n) n := Eval.proj 0
  constructor
  · intro h; rw [show m = n from h]; exact h0
  · intro h; exact (Eval.det h0 h).symm

/-- **COMPOSITION** of partial-recursive graphs is partial recursive.  Diagram order:
    `(φ.comp ψ)(n) = ψ(φ(n))`; the code is `comp cψ [cφ]` — run `cφ` on `[n]`, feed the
    result to `cψ`.  Partiality is handled by `Eval`'s `comp` clause (no dovetailing:
    the two runs are sequential). -/
theorem partRec_comp {φ ψ : ModFun} (hφ : PartRec φ) (hψ : PartRec ψ) :
    PartRec (φ.comp ψ) := by
  obtain ⟨cφ, hcφ⟩ := hφ
  obtain ⟨cψ, hcψ⟩ := hψ
  refine ⟨.comp cψ (fun _ : Fin 1 => cφ), fun n m => ?_⟩
  constructor
  · rintro ⟨j, hnj, hjm⟩
    refine Eval.comp (fun _ => j) (fun _ => (hcφ n j).mp hnj) ?_
    have := (hcψ j m).mp hjm
    rwa [vec1_eta (fun _ : Fin 1 => j)]
  · intro h
    cases h with
    | comp w hg hf =>
      refine ⟨w 0, (hcφ n (w 0)).mpr (hg 0), (hcψ (w 0) m).mpr ?_⟩
      rw [vec1_eta w] at hf; exact hf

/-! ## Layer 2 data: the Cantor coding, projections and tags

  The pairing `code` of `Krec` is the Cantor pairing `cp` (§1.572), with projections
  `cfst`/`csnd` and their laws `cfst_cp`/`csnd_cp`; tags are `2·` and `2·+1`.  All are
  total recursive, hence partial recursive via `partRec_ofFun`. -/

/-- `cfst` as a partial-recursive graph (ℓ). -/
theorem partRec_cfst : PartRec (ModFun.ofFun cfst) := partRec_ofFun Recursive1.cfst
/-- `csnd` as a partial-recursive graph (ϰ). -/
theorem partRec_csnd : PartRec (ModFun.ofFun csnd) := partRec_ofFun Recursive1.csnd

/-- The left tag `2·` is total recursive. -/
theorem rec_inL : Recursive1 fun k => 2 * k :=
  Recursive1.mul (Recursive1.const 2) Recursive1.id
/-- The right tag `2·+1` is total recursive. -/
theorem rec_inR : Recursive1 fun k => 2 * k + 1 :=
  Recursive1.add rec_inL (Recursive1.const 1)

theorem partRec_inL : PartRec (ModFun.ofFun fun k => 2 * k) := partRec_ofFun rec_inL
theorem partRec_inR : PartRec (ModFun.ofFun fun k => 2 * k + 1) := partRec_ofFun rec_inR

/-- **PAIRING** `pairC cp φ ψ`: `n ↦ cp (φ n) (ψ n)`, defined on the common domain.
    The code runs `cφ` and `cψ` on `[n]` and Cantor-pairs the outputs. -/
theorem partRec_pairC {φ ψ : ModFun} (hφ : PartRec φ) (hψ : PartRec ψ) :
    PartRec (ModFun.pairC cp φ ψ) := by
  obtain ⟨cφ, hcφ⟩ := hφ
  obtain ⟨cψ, hcψ⟩ := hψ
  obtain ⟨ccp, hccp⟩ := Recursive2.cp
  refine ⟨.comp ccp (fun j : Fin 2 => if j.val = 0 then cφ else cψ), fun n m => ?_⟩
  constructor
  · rintro ⟨a, b, hna, hnb, rfl⟩
    refine Eval.comp (vcons a (fun _ => b)) (fun j => ?_) ?_
    · rcases j with ⟨jv, hj⟩
      match jv, hj with
      | 0, _ => exact (hcφ n a).mp hna
      | 1, _ => exact (hcψ n b).mp hnb
    · have := hccp (vcons a (fun _ => b))
      simpa using this
  · intro h
    cases h with
    | comp w hg hf =>
      have hcpw : Eval ccp w (cp (w 0) (w 1)) := hccp w
      have hw0 : Eval cφ (fun _ => n) (w 0) := by
        have := hg ⟨0, by omega⟩; simpa using this
      have hw1 : Eval cψ (fun _ => n) (w 1) := by
        have := hg ⟨1, by omega⟩; simpa using this
      refine ⟨w 0, w 1, (hcφ n (w 0)).mpr hw0, (hcψ n (w 1)).mpr hw1, ?_⟩
      exact (Eval.det hcpw hf).symm

/-! ## Layer 2, the crux: a UNIVERSAL MACHINE for the tagged `casesC`

  `casesC` dispatches between two PARTIAL codes `cφ`, `cψ` on a total selector (the
  parity of `csnd n`).  There is no elementary `RecCode` combinator that runs one of
  two partial codes without forcing the other, so we build the universal machine: run
  the code whose Gödel number is `cfst er` on input `[csnd er]` by μ-searching the
  arithmetized-derivation checker of §1.572b.

  `acceptOn er wit` accepts iff `wit = (W, i)` is a checked derivation whose node `i`
  claims "code number `cfst er` on input list `[csnd er]` evaluates". -/

/-- Universal accept predicate: `er = cp e r` packs the code number `e` and input `r`. -/
noncomputable def acceptOn (er wit : Nat) : Nat :=
  bAllN (fun j => nodeOK j (cfst wit)) (csnd wit + 1)
  * eqInd (codeOf (nthN (csnd wit) (cfst wit))) (cfst er)
  * eqInd (insOf (nthN (csnd wit) (cfst wit))) (consN (csnd er) 0)

/-- The claimed output of an accepting witness (depends only on `wit`). -/
noncomputable def uOut (er wit : Nat) : Nat := outOf (nthN (csnd wit) (cfst wit))

/-- The output extractor as a UNARY recursive function of `wit` alone. -/
noncomputable def uOutW (wit : Nat) : Nat := outOf (nthN (csnd wit) (cfst wit))

theorem uOut_eq (er wit : Nat) : uOut er wit = uOutW wit := rfl

theorem Recursive1_uOutW : Recursive1 uOutW :=
  Recursive1.comp (f := fun wit => nthN (csnd wit) (cfst wit))
    (Recursive1.comp2 Recursive2.nthN Recursive1.csnd Recursive1.cfst) Recursive1.outOf

/-- `acceptOn` is a recursive function of R (mirror of `Recursive2.acceptN`). -/
theorem Recursive2_acceptOn : Recursive2 acceptOn := by
  unfold acceptOn
  have hF : Recursive3 fun j _ wit => nodeOK j (cfst wit) :=
    Recursive3.comp2 Recursive2.nodeOK Recursive3.p1
      (Recursive3.comp1 (F := cfst) Recursive1.cfst Recursive3.p3)
  have hb : Recursive2 fun _ wit => csnd wit + 1 :=
    Recursive2.comp2 Recursive2.add (Recursive2.ofSnd Recursive1.csnd) (Recursive2.const 1)
  have hball' : Recursive2 fun _ wit =>
      bAllN (fun j => nodeOK j (cfst wit)) (csnd wit + 1) :=
    RecursiveV.bAllComp hF hb
  have hroot : Recursive2 fun _ wit => nthN (csnd wit) (cfst wit) :=
    Recursive2.comp2 Recursive2.nthN (Recursive2.ofSnd Recursive1.csnd)
      (Recursive2.ofSnd Recursive1.cfst)
  have a2 : Recursive2 fun er wit =>
      eqInd (codeOf (nthN (csnd wit) (cfst wit))) (cfst er) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := codeOf) Recursive1.codeOf hroot)
      (Recursive2.ofFst Recursive1.cfst)
  have a3 : Recursive2 fun er wit =>
      eqInd (insOf (nthN (csnd wit) (cfst wit))) (consN (csnd er) 0) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := insOf) Recursive1.insOf hroot)
      (Recursive2.comp2 Recursive2.consN (Recursive2.ofFst Recursive1.csnd) (Recursive2.const 0))
  exact Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul hball' a2) a3

/-- `uOut` is a recursive function of R. -/
theorem Recursive2_uOut : Recursive2 uOut := by
  have h1 : Recursive1 fun wit => nthN (csnd wit) (cfst wit) :=
    Recursive1.comp2 Recursive2.nthN Recursive1.csnd Recursive1.cfst
  exact Recursive2.ofSnd (Recursive1.comp h1 Recursive1.outOf)

/-- SOUNDNESS: an accepted witness for a REAL unary code `c` numbered `cfst er`
    certifies a real evaluation of `c` on input `[csnd er]`, with value `uOut er wit`. -/
theorem acceptOn_sound {er wit : Nat} (h : acceptOn er wit = 1)
    {c : RecCode 1} (hc : cfst er = encCode c) :
    Eval c (fun _ => csnd er) (uOut er wit) := by
  unfold acceptOn at h
  obtain ⟨h, hins⟩ := mul_eq_one_iff.mp h
  obtain ⟨hall, hcode⟩ := mul_eq_one_iff.mp h
  have hval : ∀ j, j < csnd wit + 1 → nodeOK j (cfst wit) = 1 := of_bAllN_eq_one hall
  have hcode' : codeOf (nthN (csnd wit) (cfst wit)) = encCode c := by
    rw [eqInd_one_iff.mp hcode, hc]
  have hins' : insOf (nthN (csnd wit) (cfst wit)) = encVec (fun _ : Fin 1 => csnd er) := by
    rw [eqInd_one_iff.mp hins, encVec_one]
  exact checkSound (csnd wit + 1) (cfst wit) hval (csnd wit) (Nat.lt_succ_self _)
    c _ hcode' hins'

/-- COMPLETENESS: a real evaluation `Eval c [r] y` is certified by some witness for
    the packed input `cp (encCode c) r`, with claimed output exactly `y`. -/
theorem acceptOn_complete {c : RecCode 1} {r y : Nat} (h : Eval c (fun _ => r) y) :
    ∃ wit, acceptOn (cp (encCode c) r) wit = 1 ∧ uOut (cp (encCode c) r) wit = y := by
  obtain ⟨L', hval, i, hlen, hcode, hins, hout⟩ := checkComplete h [] allValidL_nil
  rw [List.nil_append] at hval hlen hcode hins hout
  refine ⟨cp (encListN L') i, ?_, ?_⟩
  · unfold acceptOn
    rw [cfst_cp, csnd_cp, cfst_cp, csnd_cp]
    have hval' : ∀ j, j < i + 1 → nodeOK j (encListN L') = 1 := fun j hj => hval j (by omega)
    rw [bAllN_eq_one hval', hcode, hins, encVec_one, eqInd_eq rfl, eqInd_eq rfl]
  · unfold uOut
    rw [cfst_cp, csnd_cp, hout]

/-- **The universal machine, correct on genuine code numbers.**  There is a single
    unary Kleene code `cU` that, on the packed input `cp (encCode c) r`, halts with
    exactly the values of `c` on `[r]`: it μ-searches `acceptOn` for a checked
    derivation and extracts its output.  (Correctness needs `cfst er` to be a genuine
    code number — always the case in the `casesC` application below.) -/
theorem universal_genuine : ∃ cU : RecCode 1, ∀ (c : RecCode 1) (r m : Nat),
    (Eval cU (fun _ => cp (encCode c) r) m ↔ Eval c (fun _ => r) m) := by
  -- inner μ-test: 0 exactly at accepting witnesses
  have innerRec : Recursive2 (fun wit er => 1 - eqInd (acceptOn er wit) 1) :=
    Recursive2.comp2 Recursive2.sub (Recursive2.const 1)
      (Recursive2.comp2 Recursive2.eqInd (Recursive2.swap Recursive2_acceptOn)
        (Recursive2.const 1))
  obtain ⟨cInner, hInner⟩ := innerRec
  obtain ⟨cExt, hExt⟩ := Recursive1_uOutW
  refine ⟨.comp cExt (fun _ : Fin 1 => .mu cInner), fun c r m => ?_⟩
  obtain ⟨er, her⟩ : ∃ er, er = cp (encCode c) r := ⟨_, rfl⟩
  rw [← her]
  have hcf : cfst er = encCode c := by rw [her]; exact cfst_cp _ _
  have hcs : csnd er = r := by rw [her]; exact csnd_cp _ _
  -- μ-inversion: a value of `.mu cInner` on `[er]` is an accepting witness
  have mu_acc : ∀ w, Eval (.mu cInner) (fun _ => er) w → acceptOn er w = 1 := by
    intro w hw
    cases hw with
    | mu r' hy _ =>
      have hspec := hInner (vcons w (fun _ => er))
      simp only [vcons_zero, vcons_one] at hspec
      have hv : (1 - eqInd (acceptOn er w) 1) = 0 := Eval.det hspec hy
      have hle := eqInd_le_one (acceptOn er w) 1
      have : eqInd (acceptOn er w) 1 = 1 := by omega
      exact eqInd_one_iff.mp this
  constructor
  · -- forward: run the universal machine, extract, apply soundness
    intro h
    cases h with
    | comp w hg hf =>
      have hmu : Eval (.mu cInner) (fun _ => er) (w 0) := hg 0
      have hacc : acceptOn er (w 0) = 1 := mu_acc _ hmu
      have hm : uOutW (w 0) = m := Eval.det (hExt w) hf
      have hs := acceptOn_sound hacc (c := c) hcf
      rw [hcs, uOut_eq, hm] at hs
      exact hs
  · -- backward: completeness gives an accepting witness; μ finds the least
    intro h
    obtain ⟨wit, hacc, _⟩ := acceptOn_complete (c := c) (r := r) (y := m) h
    have hex : ∃ w, acceptOn er w = 1 := ⟨wit, by rw [her]; exact hacc⟩
    obtain ⟨wit0, hmem, hmin⟩ :
        ∃ w0, acceptOn er w0 = 1 ∧ ∀ i, i < w0 → ¬ acceptOn er i = 1 :=
      ⟨theLeast _ hex, theLeast_mem _ hex, theLeast_min _ hex⟩
    have hmu : Eval (.mu cInner) (fun _ => er) wit0 := by
      refine Eval.mu (fun _ => 0) ?_ (fun i hi => ?_)
      · have hspec := hInner (vcons wit0 (fun _ => er))
        simp only [vcons_zero, vcons_one] at hspec
        have hv : (1 - eqInd (acceptOn er wit0) 1) = 0 := by
          have := eqInd_eq hmem; omega
        rwa [hv] at hspec
      · have hspec := hInner (vcons i (fun _ => er))
        simp only [vcons_zero, vcons_one] at hspec
        have hv : (1 - eqInd (acceptOn er i) 1) = 0 + 1 := by
          have := eqInd_ne (hmin i hi); omega
        rwa [hv] at hspec
    have hval : uOutW wit0 = m := by
      have hs := acceptOn_sound hmem (c := c) hcf
      rw [hcs, uOut_eq] at hs
      exact Eval.det hs h
    refine Eval.comp (fun _ => wit0) (fun _ => ?_) ?_
    · exact hmu
    · have hh := hExt (fun _ => wit0)
      simp only [] at hh
      rwa [hval] at hh

/-! ### The tagged `casesC` closure

  `casesC` dispatches on the parity of `csnd n`: even `2y` runs `φ` on `cp (cfst n) y`,
  odd `2y+1` runs `ψ`.  We preprocess `n` into the packed universal input
  `cp (Gödel# of the selected code) (cp (cfst n) (csnd n / 2))` (total recursive), then
  run the universal machine `cU`.  Both Gödel numbers are genuine, so `universal_genuine`
  applies. -/

/-- The Gödel number of the code selected by the parity bit `s`. -/
noncomputable def branchNum (Nf Ng s : Nat) : Nat := if s = 0 then Nf else Ng

theorem branchNum_zero (Nf Ng : Nat) : branchNum Nf Ng 0 = Nf := if_pos rfl

theorem rec_branchNum (Nf Ng : Nat) : Recursive1 (branchNum Nf Ng) :=
  (Recursive1.ifEqConst 0 Nf (Recursive1.const Ng)).congr fun n => rfl

/-- The universal-input preprocessing: pack the selected code number with the recoded
    argument `cp (cfst n) (csnd n / 2)`. -/
noncomputable def preIdx (Nf Ng n : Nat) : Nat :=
  cp (branchNum Nf Ng (csnd n % 2)) (cp (cfst n) (csnd n / 2))

theorem rec_preIdx (Nf Ng : Nat) : Recursive1 (preIdx Nf Ng) := by
  unfold preIdx
  exact Recursive1.comp2 Recursive2.cp
    (Recursive1.comp (Recursive1.comp Recursive1.csnd (Recursive1.modConst 1))
      (rec_branchNum Nf Ng))
    (Recursive1.comp2 Recursive2.cp Recursive1.cfst
      (Recursive1.comp Recursive1.csnd (Recursive1.divConst 1)))

theorem preIdx_left {Nf Ng n y : Nat} (h : csnd n = 2 * y) :
    preIdx Nf Ng n = cp Nf (cp (cfst n) y) := by
  unfold preIdx
  rw [show csnd n % 2 = 0 from by omega, show csnd n / 2 = y from by omega, branchNum_zero]

theorem preIdx_right {Nf Ng n y : Nat} (h : csnd n = 2 * y + 1) :
    preIdx Nf Ng n = cp Ng (cp (cfst n) y) := by
  unfold preIdx
  rw [show csnd n % 2 = 1 from by omega, show csnd n / 2 = y from by omega,
    show branchNum Nf Ng 1 = Ng from if_neg (by omega)]

/-- **The `casesC` closure.**  Definition-by-cases on the tag between two
    partial-recursive graphs is partial recursive (via the universal machine). -/
theorem partRec_casesC {φ ψ : ModFun} (hφ : PartRec φ) (hψ : PartRec ψ)
    (hL : ∀ {a b : Nat}, 2 * a = 2 * b → a = b)
    (hR : ∀ {a b : Nat}, 2 * a + 1 = 2 * b + 1 → a = b)
    (hLR : ∀ a b, 2 * a ≠ 2 * b + 1) :
    PartRec (ModFun.casesC cfst csnd cp (fun k => 2 * k) (fun k => 2 * k + 1) hL hR hLR φ ψ) := by
  obtain ⟨cφ, hcφ⟩ := hφ
  obtain ⟨cψ, hcψ⟩ := hψ
  obtain ⟨cU, hU⟩ := universal_genuine
  obtain ⟨cPre, hcPre⟩ := rec_preIdx (encCode cφ) (encCode cψ)
  refine ⟨.comp cU (fun _ : Fin 1 => cPre), fun n m => ?_⟩
  -- `Eval (comp cU [cPre]) [n] m ↔ Eval cU [preIdx n] m`
  have step : Eval (.comp cU (fun _ : Fin 1 => cPre)) (fun _ => n) m
      ↔ Eval cU (fun _ => preIdx (encCode cφ) (encCode cψ) n) m := by
    constructor
    · intro h
      cases h with
      | comp w hg hf =>
        have hw0 : w 0 = preIdx (encCode cφ) (encCode cψ) n :=
          Eval.det (hg 0) (hcPre (fun _ => n))
        rw [vec1_eta w, hw0] at hf; exact hf
    · intro h
      exact Eval.comp (fun _ => preIdx (encCode cφ) (encCode cψ) n)
        (fun _ => hcPre (fun _ => n)) h
  rw [step]
  constructor
  · rintro (⟨y, hy, hgr⟩ | ⟨y, hy, hgr⟩)
    · rw [preIdx_left hy]
      exact (hU cφ (cp (cfst n) y) m).mpr ((hcφ (cp (cfst n) y) m).mp hgr)
    · rw [preIdx_right hy]
      exact (hU cψ (cp (cfst n) y) m).mpr ((hcψ (cp (cfst n) y) m).mp hgr)
  · intro h
    have hpar : csnd n % 2 = 0 ∨ csnd n % 2 = 1 := by omega
    rcases hpar with h2 | h2
    · refine Or.inl ⟨csnd n / 2, by show csnd n = 2 * (csnd n / 2); omega, ?_⟩
      rw [preIdx_left (by omega : csnd n = 2 * (csnd n / 2))] at h
      exact (hcφ (cp (cfst n) (csnd n / 2)) m).mpr
        ((hU cφ (cp (cfst n) (csnd n / 2)) m).mp h)
    · refine Or.inr ⟨csnd n / 2, by show csnd n = 2 * (csnd n / 2) + 1; omega, ?_⟩
      rw [preIdx_right (by omega : csnd n = 2 * (csnd n / 2) + 1)] at h
      exact (hcψ (cp (cfst n) (csnd n / 2)) m).mpr
        ((hU cψ (cp (cfst n) (csnd n / 2)) m).mp h)

/-! ## Layer 2 headline: the PARTIAL-RECURSIVE modulus system

  All `ModulusSystem` fields are now satisfiable by `PartRec`, with the Cantor pairing
  `cp` as `code`, `cfst`/`csnd` as the projections, and `2·`/`2·+1` as tags — every
  closure proved above with no holes.  This is the concrete recursive `K` the book names in
  the §2.153 bracket ("K may be the collection of all partial recursive functions"), over
  which the halting obstruction is real (unlike `allPartial`). -/
noncomputable def Krec : ModulusSystem where
  mem := PartRec
  id_mem := partRec_ident
  comp_mem := partRec_comp
  code := cp
  proj₁ := cfst
  proj₂ := csnd
  proj₁_mem := partRec_cfst
  proj₂_mem := partRec_csnd
  code_proj₁ := cfst_cp
  code_proj₂ := csnd_cp
  pair_mem := partRec_pairC
  inL k := 2 * k
  inR k := 2 * k + 1
  inL_mem := partRec_inL
  inR_mem := partRec_inR
  inL_inj h := by omega
  inR_inj h := by omega
  inLR_ne a b := by omega
  cases_mem hφ hψ := partRec_casesC hφ hψ _ _ _

/-! ## Status of Layers 3–4 (the concrete non-splitting relation) — CLOSED in `S2_153f`

  Layers 1–2 above are complete and hole-free: `Krec : ModulusSystem` is the genuine
  partial-recursive modulus system, its `casesC` closure powered by the universal machine
  `universal_genuine`.  Layers 3–4 (a concrete non-splitting equivalence relation on an
  assembly over `Krec`, then `¬ CoversSplit (AsmEffReflection Krec)` via
  `Freyd.Alg.asmReflection_not_ac_of_nonsplitting`) are NOT closed here, and the obvious
  route — transport §1.572b's halting relation `ERel` — provably does NOT work:

  * The R non-effectiveness `Freyd.Rcat.ERel_not_effective` derives its contradiction from
    `cover_split` (covers split in R: R is AC).  Assemblies over `Krec` are NOT AC (that is
    the whole point), so this step has no assembly analogue.

  * Concretely, on the singleton-caucus assembly `A` (carrier ℕ, `caucus n = {n}`) the
    halting relation `haltRel = {(a,b) : ESet a b}` IS effective: the quotient assembly
    `Q = A/ESet` with `caucus n := {[n]}` and quotient map `x : n ↦ [n]` (tracked by the
    identity modulus) is a cover whose level is exactly `ESet`.  Then
    `SplitsAsMap (relGraph x) (relClass haltRel)` HOLDS, so the `hno` hypothesis of the
    reduction is FALSE for this witness.

  Hence §2.153 non-effectiveness for assemblies needs a DIFFERENT relation, not a transport
  of `ERel`.  CLOSED in `Fredy/S2_153f_ParityWitness.lean`: the parity relation on `∇ℕ`
  (classes `2k ~ 2k+1`, caucus at `m` = diagonal ∪ classes ≤ m) has no map-splitting — by
  UNIFORMITY OF NAMING, with no recursion theory at all, so the headline holds over `Krec`
  AND over `ModulusSystem.allPartial`. -/

end Freyd
