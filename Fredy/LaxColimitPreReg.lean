/-
  §1.543 — PRE-REGULARITY of the FILTERED lax colimit `ratCapCat P` (the §1.547 relative
  capitalization `A*`).

  ════════════════════════════════════════════════════════════════════════════════════════════
  GOAL.  `CapitalizationLaxColimit.lean` builds, sorry-free, the §1.547 relative capitalization
  `A* = ratCapCat P : Cat (Obj (laxOfProjSystem' P))` — the FILTERED lax colimit of the slices
  `A/(∏U) = Over (listProd U)` over the filtered index of finite ws-lists, with BASE-CHANGE
  transitions (a pseudofunctor, coherence supplied as natural isos `F_refl_iso`/`F_trans_iso`,
  never strict equalities).  Each fibre `Over (listProd U)` is `PreRegularCategory`
  (`overPreRegular`, `SliceRegular.lean`).

  This file transfers PRE-REGULARITY to the colimit:  `PreRegularCategory (ratCapCat P)`.  The
  principle is "FILTERED colimits commute with FINITE limits": a finite diagram in the colimit,
  pushed along transitions to a COMMON upper stage (filtered: any finite index set has a bound),
  lives in a single fibre, where the fibre's finite limit is computed and then included.

  It MIRRORS the STRICT analogue `Colim.colimitPreRegular` (`CatColimitRegular.lean:2450`), which
  proves exactly this for the STRICT colimit, replacing strict `castHom`/object-equalities with the
  lax `pushHom`/coherence-isos.  The crucial SIMPLIFICATION over the strict file: the lax colimit's
  objects are the bare `Σ i, A i` (`Obj L`), so every object is LITERALLY `objIncl i x = ⟨i,x⟩` —
  there is NO `colimOut`/`Quotient.out` representative-section to fight (the strict file's pervasive
  `colimOut`/`colimOut_spec` machinery simply vanishes).

  ADAPTATION PLAN from `colimitPreRegular` (the strict assembly takes per-fibre limit existence
  PLUS the transitions' finite-limit PRESERVATION; the lax version takes the same):

    * `HasTerminal`  — strict `colimitHasTerminal` needs `ht i` + `hpres : F hij one = one`
      (strict).  Lax: the pushed terminal `F hij (ht i).one` is again TERMINAL (true for
      base-change: `g* ⟨pr i, id⟩ ≅ ⟨pr j, id⟩`); state that as the preservation hypothesis and the
      whole proof goes through with `homInclL`/`pushHom` in place of `homIncl`/`castHom`.  DONE here.
    * `HasBinaryProducts`/`HasEqualizers`/`HasPullbacks` — push the two/one objects to a common
      stage, take the fibre limit, include; universal property via the germ colimit + the fibres'
      limit-preservation across transitions.  (Mirrors `colimitHasBinaryProducts`/`…Equalizers`/
      `…Pullbacks`.)  NEXT.
    * `PullbacksTransferCovers` — a colimit cover + pullback align to a common fibre where the
      fibre's PTC applies; transfer back (mirrors `colimitPullbacksTransferCovers`).
    * assemble `PreRegularCategory (ratCapCat P)` (mirrors `colimitPreRegular`).

  Mathlib-free; built on the repo's own `Cat` + `Freyd.LaxColim` (`CapitalizationLaxColimit.lean`).
-/
import Fredy.CapitalizationLaxColimit

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## §M3a (lax) — the terminal object of the lax colimit category

  Mirrors `Colim.colimitHasTerminal`.  Pick any stage `i₀` (filtered ⇒ nonempty needed) and let the
  colimit terminal be `objIncl i₀ (ht i₀).one`.  Unlike the strict version there is NO `colimOut`:
  the terminal IS literally `⟨i₀, (ht i₀).one⟩`.

  The preservation hypothesis is the LAX analogue of the strict `hpres : F hij one = one`.  In the
  lax world `F hij (ht i).one` is only ISO to `(ht j).one`, so the strict equation is false; instead
  we ask that the pushed terminal is again a TERMINAL OBJECT (its own `HasTerminal`-witness in
  `L.A j`).  This is exactly what base-change supplies (`g*` of the slice terminal is the slice
  terminal up to iso, and an isomorph of a terminal is terminal), and it is all the proof needs. -/
section LaxTerminal

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-- LAX terminal-preservation: each fibre has a terminal `ht i`, and the pushed terminal
    `L.F hij (ht i).one` is again terminal in the target fibre `L.A j` (an isomorph of `(ht j).one`).
    For base-change this holds: `g*` carries the slice terminal `⟨pr i, id⟩` to `⟨pr j, id⟩` up to
    iso, and any isomorph of a terminal is terminal. -/
structure LaxTerminalData where
  /-- each fibre has a terminal -/
  ht : ∀ i, HasTerminal (L.A i)
  /-- the unique map of any object to the pushed terminal -/
  pushTrm : ∀ {i j} (hij : D.le i j) (X : L.A j), X ⟶ L.F hij (ht i).one
  /-- pushed terminal is terminal: maps into it are unique -/
  pushUniq : ∀ {i j} (hij : D.le i j) {X : L.A j}
    (f g : X ⟶ L.F hij (ht i).one), f = g

/-- **§M3a (lax): the lax colimit category has a terminal.**  The terminal is `objIncl i₀ one` for a
    chosen stage `i₀`.  The unique map from `⟨jX, xX⟩` pushes both to a common bound `k`, mapping
    `xX` to the pushed terminal via `pushTrm`; uniqueness is `pushUniq` after pushing two germ
    representatives to a common bound (and absorbing the level shift by `pushHom`/germ equivalence). -/
noncomputable def laxColimHasTerminal [hne : Nonempty ι] (T : LaxTerminalData L) :
    @HasTerminal (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  let i₀ : ι := Classical.choice hne
  let one : Obj L := objIncl L i₀ (T.ht i₀).one
  refine @HasTerminal.mk (Obj L) (laxColimCat L hL) one ?_ ?_
  · -- trm: a morphism `⟨jX, xX⟩ ⟶ one` for every object `X`.
    intro X
    obtain ⟨jX, xX⟩ := X
    -- common bound `k` of `jX` and `i₀` (chosen by `D.bound`; `trm` returns a `Type`, so `choose`).
    let bd := D.bound jX i₀
    let k := Classical.choose bd
    have hk : D.le jX k ∧ D.le i₀ k := Classical.choose_spec bd
    -- the germ of `pushTrm : F (jX≤k) xX ⟶ F (i₀≤k) one` at the upper bound `⟨k, hk.1, hk.2⟩`.
    exact homInclL L hL xX (T.ht i₀).one ⟨k, hk.1, hk.2⟩ (T.pushTrm hk.2 (L.F hk.1 xX))
  · -- uniq: any two germs `⟨jX,xX⟩ ⟶ one` are equal.
    intro X f g
    obtain ⟨jX, xX⟩ := X
    refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
    -- push both representatives to a common bound `k'` of `a.1`, `b.1`; there the targets are the
    -- pushed terminal `F (trans a.2.2 …) one`, so `pushUniq` equates them.
    apply Quotient.sound
    obtain ⟨k', hak', hbk'⟩ := D.bound a.1 b.1
    -- witness the germ relation at the upper bound `⟨k', …⟩` of `⟨jX, xX⟩, ⟨i₀, one⟩`.
    refine ⟨⟨k', D.trans a.2.1 hak', D.trans a.2.2 hak'⟩, hak', hbk', ?_⟩
    -- both `pushHom … fa` and `pushHom … gb` are arrows into the pushed terminal
    -- `F (D.trans a.2.2 hak') one = F (D.trans b.2.2 hbk') one` (proof-irrelevant `D.le i₀ k'`).
    exact T.pushUniq (D.trans a.2.2 hak') _ _

end LaxTerminal

end Freyd.LaxColim
