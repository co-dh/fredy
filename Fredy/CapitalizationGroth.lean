/-
  §1.543 — Milestone G1: the Grothendieck / Σ-carrier transfinite capitalization tower.

  The earlier tower (`Fredy/CapitalizationTower.lean`) presents the LIMIT stage's objects as
  the repo's quotient `Colim.colimitCat`, whose object carrier depends on the below-transition
  data.  That dependency forces a cross-IH agreement (`belowObjAgree`) and a `Coherent` input
  to even *state* the carrier — the kernel block of §1.543.

  This file BREAKS that block (probe-verified) by presenting a directed colimit of categories on
  the transition-INDEPENDENT Grothendieck Σ-carrier

      homColimCarrier S  :=  Σ (i : ι), S.A i        (NO quotient)

  with the SAME hom-colimit Hom-sets / identity / composition as the repo's `Colim.colimitCat`,
  but read at the literal Σ-representatives `p.2` instead of the chosen `colimOut p`.  Because the
  carrier is the bare Σ-type, the cocone inclusion `S.A i → homColimCarrier S` is the bare
  injection `x ↦ ⟨i, x⟩` (no quotient, no `objIncl`-via-equality), and the transition INTO a limit
  stage carries no data-`Sorry`.

  G1 deliverable in THIS file:
    * `homColimCat S hS  :  Cat (Σ i, S.A i)` — the Σ-carrier hom-colimit category, Sorry-free,
      reusing every representative-level lemma already proven for `Colim.colimitCat`.
    * the tower `towerSystem : Colim.CatSystem.{u,u} α (D w)` whose limit carriers are these
      Σ-types, plus its `Coherent`.

  Universes pinned `.{u,u}`.  Mathlib-free (built on `Freyd.WO` / `Freyd.Colim` and the
  classification + WF engine reused from `Fredy.CapTower`).
-/
import Fredy.Capitalization
import Fredy.WellOrdering
import Fredy.CapitalizationTower

open Freyd
open Freyd.Colim

namespace Freyd.Colim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## The Σ-carrier hom-colimit category

  The repo's `colimitCat C hC : Cat C.Obj` builds the directed colimit of categories with objects
  `C.Obj = Colimit C.objSystem` (a QUOTIENT), and represents a morphism `p ⟶ q` as
  `HomColim C hC (colimOut p).2 (colimOut q).2` — the hom-colimit between CHOSEN representatives.

  Here we keep the SAME hom-colimit, but on the Σ-carrier `Σ i, C.A i`, reading the
  representatives literally (`p.2`).  Every representative-level lemma already proven in
  `CatColimit.lean` (`homCompRaw_id_left`, `homCompRaw_id_right`, `homCompRaw_wd`,
  `homCompRaw_eq_compAt`, …) applies verbatim — only the wrapping object type changes from the
  quotient to the Σ-type. -/

/-- Objects of the Σ-carrier colimit category. -/
abbrev SigmaObj (C : CatSystem ι D) : Type _ := Σ i, C.A i

/-- Morphisms of the Σ-carrier colimit category between literal representatives. -/
def sigmaHom (C : CatSystem ι D) (hC : C.Coherent) (p q : SigmaObj C) : Type _ :=
  HomColim C hC p.2 q.2

/-- Identity of the Σ-carrier colimit category. -/
def sigmaId (C : CatSystem ι D) (hC : C.Coherent) (p : SigmaObj C) : sigmaHom C hC p p :=
  homClassId C hC p.2

/-- Composition of the Σ-carrier colimit category: lift `homCompRaw` over the two hom-colimit
    quotients (well-defined by `homCompRaw_wd`), exactly as `colimComp` but at the literal
    representatives `p.2`. -/
noncomputable def sigmaComp (C : CatSystem ι D) (hC : C.Coherent) {p q r : SigmaObj C}
    (m : sigmaHom C hC p q) (n : sigmaHom C hC q r) : sigmaHom C hC p r :=
  Quotient.lift₂
    (fun rm rn => homCompRaw C hC p.2 q.2 r.2 rm.1 rm.2 rn.1 rn.2)
    (fun _ _ _ _ hP hQ => homCompRaw_wd C hC p.2 q.2 r.2 _ _ _ _ hP _ _ _ _ hQ)
    m n

theorem sigmaComp_id_left (C : CatSystem ι D) (hC : C.Coherent) {p q : SigmaObj C}
    (m : sigmaHom C hC p q) : sigmaComp C hC (sigmaId C hC p) m = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm; exact homCompRaw_id_left C hC p.2 q.2 a f

theorem sigmaComp_id_right (C : CatSystem ι D) (hC : C.Coherent) {p q : SigmaObj C}
    (m : sigmaHom C hC p q) : sigmaComp C hC m (sigmaId C hC q) = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm; exact homCompRaw_id_right C hC p.2 q.2 a f

/-- Associativity for the Σ-carrier composition.  Identical to `colimComp_assoc`'s proof, read at
    literal representatives `p.2` instead of `(colimOut p).2`. -/
theorem sigmaComp_assoc (C : CatSystem ι D) (hC : C.Coherent) {p q r s : SigmaObj C}
    (m : sigmaHom C hC p q) (n : sigmaHom C hC q r) (k : sigmaHom C hC r s) :
    sigmaComp C hC (sigmaComp C hC m n) k = sigmaComp C hC m (sigmaComp C hC n k) := by
  refine Quotient.inductionOn m (fun rm => ?_)
  refine Quotient.inductionOn n (fun rn => ?_)
  refine Quotient.inductionOn k (fun rk => ?_)
  obtain ⟨a, f⟩ := rm; obtain ⟨b, g⟩ := rn; obtain ⟨c, h⟩ := rk
  let xp := p.2; let xq := q.2; let xr := r.2; let xs := s.2
  let e₁d := D.bound a.1 b.1
  let e₁ := Classical.choose e₁d
  let hae₁ : D.le a.1 e₁ := (Classical.choose_spec e₁d).1
  let hbe₁ : D.le b.1 e₁ := (Classical.choose_spec e₁d).2
  let Md := D.bound e₁ c.1
  let M := Classical.choose Md
  let he₁M : D.le e₁ M := (Classical.choose_spec Md).1
  let hcM : D.le c.1 M := (Classical.choose_spec Md).2
  have haM : D.le a.1 M := D.trans hae₁ he₁M
  have hbM : D.le b.1 M := D.trans hbe₁ he₁M
  let aMpq : UpperBound D p.1 q.1 := ⟨M, D.trans a.2.1 haM, D.trans a.2.2 haM⟩
  let bMqr : UpperBound D q.1 r.1 := ⟨M, D.trans b.2.1 hbM, D.trans b.2.2 hbM⟩
  let cMrs : UpperBound D r.1 s.1 := ⟨M, D.trans c.2.1 hcM, D.trans c.2.2 hcM⟩
  let F_M : C.F aMpq.2.1 xp ⟶ C.F aMpq.2.2 xq := homTr C xp xq a aMpq haM f
  let G_M : C.F bMqr.2.1 xq ⟶ C.F bMqr.2.2 xr := homTr C xq xr b bMqr hbM g
  let H_M : C.F cMrs.2.1 xr ⟶ C.F cMrs.2.2 xs := homTr C xr xs c cMrs hcM h
  let ub_pr_M : UpperBound D p.1 r.1 := ⟨M, D.trans a.2.1 haM, D.trans b.2.2 hbM⟩
  let ub_ps_M : UpperBound D p.1 s.1 := ⟨M, D.trans a.2.1 haM, D.trans c.2.2 hcM⟩
  let ub_qs_M : UpperBound D q.1 s.1 := ⟨M, D.trans b.2.1 hbM, D.trans c.2.2 hcM⟩
  have h_innerL : sigmaComp C hC (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩) =
      compAt C hC xp xq xr a f b g M haM hbM := by
    show homCompRaw C hC xp xq xr a f b g = _
    rw [homCompRaw_eq_compAt C hC xp xq xr a f b g M haM hbM]
  have h_innerR : sigmaComp C hC (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩) =
      compAt C hC xq xr xs b g c h M hbM hcM := by
    show homCompRaw C hC xq xr xs b g c h = _
    rw [homCompRaw_eq_compAt C hC xq xr xs b g c h M hbM hcM]
  have h_outerL : sigmaComp C hC (compAt C hC xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩) =
      homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h := rfl
  have h_outerR : sigmaComp C hC (Quotient.mk _ ⟨a, f⟩) (compAt C hC xq xr xs b g c h M hbM hcM) =
      homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) := rfl
  have h_compAtL : homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h =
      compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM :=
    homCompRaw_eq_compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM
  have h_compAtR : homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) =
      compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) :=
    homCompRaw_eq_compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M)
  have h_simpL : compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM =
      homIncl C hC xp xs ub_ps_M ((F_M ≫ G_M) ≫ H_M) := by
    unfold compAt; rw [homTr_refl C hC xp xr ub_pr_M (F_M ≫ G_M)]
  have h_simpR : compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) =
      homIncl C hC xp xs ub_ps_M (F_M ≫ (G_M ≫ H_M)) := by
    unfold compAt; rw [homTr_refl C hC xq xs ub_qs_M (G_M ≫ H_M)]
  calc
    sigmaComp C hC (sigmaComp C hC (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩)) (Quotient.mk _ ⟨c, h⟩)
        = sigmaComp C hC (compAt C hC xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩) := by rw [h_innerL]
    _ = homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h := h_outerL
    _ = compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM := h_compAtL
    _ = homIncl C hC xp xs ub_ps_M ((F_M ≫ G_M) ≫ H_M) := h_simpL
    _ = homIncl C hC xp xs ub_ps_M (F_M ≫ (G_M ≫ H_M)) := by rw [Cat.assoc F_M G_M H_M]
    _ = compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) := by rw [h_simpR]
    _ = homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) := by rw [h_compAtR]
    _ = sigmaComp C hC (Quotient.mk _ ⟨a, f⟩) (compAt C hC xq xr xs b g c h M hbM hcM) := by rw [h_outerR]
    _ = sigmaComp C hC (Quotient.mk _ ⟨a, f⟩) (sigmaComp C hC (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩)) := by
        rw [h_innerR]

/-- **The Σ-carrier hom-colimit category.**  Objects `Σ i, C.A i`; morphisms / identity /
    composition are the directed colimit of the categories `C.A i`, read at literal
    representatives.  Sorry-free, reusing the proven representative-level laws. -/
noncomputable def homColimCat (C : CatSystem ι D) (hC : C.Coherent) : Cat (SigmaObj C) where
  Hom p q := sigmaHom C hC p q
  id p := sigmaId C hC p
  comp m n := sigmaComp C hC m n
  id_comp m := sigmaComp_id_left C hC m
  comp_id m := sigmaComp_id_right C hC m
  assoc m n k := sigmaComp_assoc C hC m n k

/-- The cocone inclusion `C.A i → Σ i, C.A i` is the bare injection (no quotient, no equality
    transport): this is what makes a transition INTO a Σ-limit stage data-`Sorry`-free. -/
def sigmaIncl (C : CatSystem ι D) (i : ι) (x : C.A i) : SigmaObj C := ⟨i, x⟩

end Freyd.Colim

/-! ## The Σ-carrier transfinite tower

  We now assemble the capitalization tower whose LIMIT stage carriers are the Σ-carriers above.
  The construction reuses the segment recursion of `Fredy.CapTower` (`Seg`, `segDirected`,
  `segIncl`, `segTop`, the below sub-system `belowSys`, the seed/successor branches) and differs
  ONLY at the limit branch: the top object's `Cat` is `homColimCat (belowSys …)` on the
  transition-INDEPENDENT Σ-carrier, and the transition into the top is the bare injection
  `sigmaIncl` — neither of which carries a data-`Sorry`. -/

namespace Freyd.GrothTower

open Freyd.CapTower

universe u

variable {α : Type u} {r : α → α → Prop}
variable (w : WO.IsWellOrder r)
variable (b₀ : PreRegBundle.{u})
variable (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)

/-- The recursion motive: an entire coherent directed system on the segment `Seg c`, exactly as
    `CapTower.SegSys` — but here the limit branch realises the top `Cat` via `homColimCat` on the
    Σ-carrier rather than via the quotient `colimitCat`.  Structurally identical, so we reuse
    `CapTower.SegSys` itself; the difference is entirely in the recursion BODY (`gSegAux`). -/
abbrev GSeg (c : α) := CapTower.SegSys w b₀ nextStep c

/-! ### The Σ-limit branch

  At a limit `c`, the strict-predecessor sub-system is `CapTower.belowSys IH` (objects = below
  tops, transitions = `belowF`).  Its Σ-carrier and `homColimCat` give the top object and `Cat`. -/

variable (c : α)

/-- The Σ-carrier of the limit top: `Σ (a : Below c), belowSys.A a`.  Transition-INDEPENDENT,
    collected directly from the IH — the construction that breaks the kernel block. -/
noncomputable def gLimTop (IH : ∀ a, r a c → GSeg w b₀ nextStep a) : Type u :=
  Colim.SigmaObj (CapTower.belowSys w b₀ nextStep c IH)

/-- The hom-colimit `Cat` on the Σ-carrier limit top.  Consumes `belowCoherent` as a *Prop* input
    only (its standing §1.543 stub); the OBJECT carrier `gLimTop` is real, NOT a quotient. -/
noncomputable instance gLimCat (IH : ∀ a, r a c → GSeg w b₀ nextStep a) :
    Cat.{u} (gLimTop w b₀ nextStep c IH) :=
  Colim.homColimCat (CapTower.belowSys w b₀ nextStep c IH)
    (CapTower.belowCoherent w b₀ nextStep c IH)

/-- **TRUE obligation (Σ-limit top pre-regularity) — G3 BOUNDARY.**  A directed colimit of
    pre-regular categories is pre-regular (`Capitalization.colimitPreRegular`, the G3 preservation
    package, here for the Σ-carrier hom-colimit).  This genuinely needs the colimit-pre-regularity
    machinery, so it is a documented TRUE stub belonging to G3, NOT closeable at G2.  Carrier +
    `Cat` are real; only this Prop is stubbed. -/
noncomputable def gLimTopPre (IH : ∀ a, r a c → GSeg w b₀ nextStep a) :
    @PreRegularCategory _ (gLimCat w b₀ nextStep c IH) :=
  sorry

open Classical in
/-- The limit segment object at `a`, as a `PreRegBundle`: slot `a < c` reuses `IH a`'s top bundle;
    the top `c` is the genuine Σ-carrier `⟨gLimTop, homColimCat, gLimTopPre⟩`.  REAL carrier. -/
noncomputable def gLimBundle (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    (a : Seg w b₀ nextStep c) : PreRegBundle.{u} :=
  if h : r a.1 c then
    ⟨(IH a.1 h).sys.A (segTop w b₀ nextStep a.1), (IH a.1 h).sys.catA _, (IH a.1 h).pre _⟩
  else ⟨gLimTop w b₀ nextStep c IH, gLimCat w b₀ nextStep c IH, gLimTopPre w b₀ nextStep c IH⟩

noncomputable def gLimA (IH : ∀ a, r a c → GSeg w b₀ nextStep a) (a : Seg w b₀ nextStep c) :
    Type u := (gLimBundle w b₀ nextStep c IH a).carrier

noncomputable instance gLimACat (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    (a : Seg w b₀ nextStep c) : Cat.{u} (gLimA w b₀ nextStep c IH a) :=
  (gLimBundle w b₀ nextStep c IH a).cat

noncomputable instance gLimAPre (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    (a : Seg w b₀ nextStep c) : @PreRegularCategory _ (gLimACat w b₀ nextStep c IH a) :=
  (gLimBundle w b₀ nextStep c IH a).pre

/-- Limit segment transition object-map `a → b` (REAL).  Both `< c`: `belowF` (the below
    sub-system transition).  From `a < c` into the top `b = c`: the **bare Σ-injection**
    `sigmaIncl` — no quotient, no `belowObjAgree`, no data-`Sorry`.  Top to top: identity. -/
noncomputable def gLimF (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    gLimA w b₀ nextStep c IH a → gLimA w b₀ nextStep c IH b := by
  unfold gLimA gLimBundle
  by_cases hbc : r b.1 c
  · have hac : r a.1 c := by
      rcases hab with hab | hab
      · exact w.trans hab hbc
      · exact hab ▸ hbc
    rw [dif_pos hac, dif_pos hbc]
    exact CapTower.belowF w b₀ nextStep c IH (a := ⟨a.1, hac⟩) (b := ⟨b.1, hbc⟩) hab
  · rw [dif_neg hbc]
    by_cases hac : r a.1 c
    · rw [dif_pos hac]
      -- INTO THE Σ-LIMIT TOP: the bare injection `x ↦ ⟨⟨a,hac⟩, x⟩`.  No transport.
      exact fun x => Colim.sigmaIncl (CapTower.belowSys w b₀ nextStep c IH) ⟨a.1, hac⟩ x
    · rw [dif_neg hac]; exact id

/-- **TRUE obligation (Σ-limit functoriality).**  `gLimF` is a functor.  Into the top it is the
    Σ-injection as a functor (the colimit cocone, functorial via the hom-colimit inclusion); below
    it is `CapTower.belowFunctF`.  The below case bottoms out at `CapTower.belowFunctF`, a `Sorry`
    in `CapitalizationTower.lean` (its morphism map transports along the stubbed `belowObjAgree`),
    so this is not closeable while editing only this file.  TRUE; documented. -/
noncomputable def gLimFunctF (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    {a b : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b) :
    @Functor _ (gLimACat w b₀ nextStep c IH a) _ (gLimACat w b₀ nextStep c IH b)
      (gLimF w b₀ nextStep c IH hab) :=
  sorry

/-- **TRUE obligation (Σ-limit identity transition).**  At a TOP slot `gLimF (refl) = id`
    (trivial); at a BELOW slot it is `CapTower.belowF_refl` — a `Sorry` in
    `CapitalizationTower.lean` (the below transition's `belowObjAgree` cast at the reflexive
    index).  Not closeable editing only this file.  TRUE; documented. -/
theorem gLim_F_refl (IH : ∀ a, r a c → GSeg w b₀ nextStep a) (a : Seg w b₀ nextStep c)
    (x : gLimA w b₀ nextStep c IH a) :
    gLimF w b₀ nextStep c IH ((segDirected w b₀ nextStep c).refl a) x = x :=
  sorry

/-- **TRUE obligation (Σ-limit composite transition).**  Below–below it is `CapTower.belowF_trans`
    (a `Sorry`); the top crossings compose the Σ-injection with `belowF`.  Same `belowObjAgree`
    obstruction.  Not closeable editing only this file.  TRUE; documented. -/
theorem gLim_F_trans (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    {a b d : Seg w b₀ nextStep c} (hab : (segDirected w b₀ nextStep c).le a b)
    (hbd : (segDirected w b₀ nextStep c).le b d) (x : gLimA w b₀ nextStep c IH a) :
    gLimF w b₀ nextStep c IH ((segDirected w b₀ nextStep c).trans hab hbd) x
      = gLimF w b₀ nextStep c IH hbd (gLimF w b₀ nextStep c IH hab x) :=
  sorry

/-- The Σ-limit segment system on `Seg c`: objects/`Cat`/transitions REAL (top = Σ-carrier
    `homColimCat`, top transition = bare `sigmaIncl`); `functF`/laws are the isolated Prop
    obligations above. -/
noncomputable def gLimSys (IH : ∀ a, r a c → GSeg w b₀ nextStep a) :
    Colim.CatSystem.{u, u} (Seg w b₀ nextStep c) (segDirected w b₀ nextStep c) where
  A := gLimA w b₀ nextStep c IH
  catA := gLimACat w b₀ nextStep c IH
  F := @fun a b h => gLimF w b₀ nextStep c IH (a := a) (b := b) h
  functF := @fun a b h => gLimFunctF w b₀ nextStep c IH (a := a) (b := b) h
  F_refl := fun {_} x => gLim_F_refl w b₀ nextStep c IH _ x
  F_trans := fun {_ _ _} hab hbd x => gLim_F_trans w b₀ nextStep c IH hab hbd x

/-- **TRUE obligation (Σ-limit segment coherence).**  Morphism-level form of `gLim_F_refl` /
    `gLim_F_trans`; its below cases are `CapTower.belowCoherent` (a `Sorry`).  Same `belowObjAgree`
    obstruction.  Not closeable editing only this file.  TRUE; documented. -/
theorem gLimCoherent (IH : ∀ a, r a c → GSeg w b₀ nextStep a) :
    (gLimSys w b₀ nextStep c IH).Coherent :=
  sorry

/-- The Σ-limit branch of the recursion: top object = Σ-carrier `homColimCat`. -/
noncomputable def gSegLimit (IH : ∀ a, r a c → GSeg w b₀ nextStep a)
    (_hz : ¬ IsZero r c) (_hs : ¬ IsSucc r c) : GSeg w b₀ nextStep c :=
  { sys := gLimSys w b₀ nextStep c IH
    coh := gLimCoherent w b₀ nextStep c IH
    pre := fun a => gLimAPre w b₀ nextStep c IH a }

open Classical in
/-- **The recursion body.**  Identical to `CapTower.segSysAux` on the zero and successor branches
    (reused verbatim via `CapTower`'s `segSucc`); the LIMIT branch is `gSegLimit`, whose top is the
    Σ-carrier `homColimCat` — REAL carrier, bare-injection transition. -/
noncomputable def gSegAux (c : α) (IH : ∀ a, r a c → GSeg w b₀ nextStep a) :
    GSeg w b₀ nextStep c := by
  classical
  by_cases hz : IsZero r c
  · exact {
      sys := {
        A := fun _ => b₀.carrier
        catA := fun _ => b₀.cat
        F := fun {_ _} _ x => x
        functF := fun {_ _} _ => @idFunctor _ b₀.cat
        F_refl := fun {_} _ => rfl
        F_trans := fun {_ _ _} _ _ _ => rfl }
      coh := { refl_map := fun {_ _ _} _ => HEq.rfl
               trans_map := fun {_ _ _} _ _ _ _ _ => HEq.rfl }
      pre := fun _ => b₀.pre }
  · by_cases hs : IsSucc r c
    · -- SUCCESSOR: reuse `CapTower.segSucc` (the Σ-carrier changes nothing on successors).
      exact CapTower.segSucc w b₀ nextStep c IH hz hs
    · -- Σ-LIMIT.
      exact gSegLimit w b₀ nextStep c IH hz hs

/-- The global segment family by well-founded recursion. -/
noncomputable def gSeg (c : α) : GSeg w b₀ nextStep c :=
  (wf_of_isWellOrder w).fix (gSegAux w b₀ nextStep) c

theorem gSeg_eq (c : α) :
    gSeg w b₀ nextStep c = gSegAux w b₀ nextStep c (fun a _ => gSeg w b₀ nextStep a) :=
  WellFounded.fix_eq (wf_of_isWellOrder w) (gSegAux w b₀ nextStep) c

/-! ### The global tower

  The global tower reads each segment's TOP object (`segTop`), with transitions = the segment
  transition from the `a`-slot to `c`'s top.  Object data is real (segment tops, including the
  Σ-carrier limit tops); the transition object-equality (`gObjAgree`) is reused from `CapTower`'s
  proven restriction agreement — but on the SAME `Seg`/`segIncl` data, so we re-establish it for
  `gSeg`.  For G1 the global functoriality / `F_refl` / `F_trans` / `Coherent` are the Prop-level
  obligations (provable post-hoc by well-founded induction, like `segSys_restrict_agree`). -/

/-- The tower object at `c`: the top of `c`'s Σ-segment. -/
noncomputable def gobj (c : α) : Type u := (gSeg w b₀ nextStep c).sys.A (segTop w b₀ nextStep c)

noncomputable instance gcat (c : α) : Cat.{u} (gobj w b₀ nextStep c) :=
  (gSeg w b₀ nextStep c).sys.catA _

/-- **Restriction agreement for the Σ-tower.**  For `a' ≤ c` and any slot `a : Seg a'`, the
    Σ-segment system at `c` read at the included slot agrees with the Σ-segment system at `a'`.
    Proven by well-founded induction (the Σ-limit branch's slot `a < c` reuses `IH a`'s top,
    identical bookkeeping to `CapTower.segSys_restrict_agree`).  Prop-level; isolated for G1. -/
theorem gSeg_restrict_agree (c a' : α) (h : (D w).le a' c) (a : Seg w b₀ nextStep a') :
    (gSeg w b₀ nextStep c).sys.A (segIncl w b₀ nextStep h a)
      = (gSeg w b₀ nextStep a').sys.A a := by
  induction c using (wf_of_isWellOrder w).induction generalizing a' a with
  | _ c IH =>
  rcases h with hlt | (rfl : a' = c)
  · -- `a' < c`: case on the classification of `c`.
    rw [gSeg_eq w b₀ nextStep c]
    classical
    unfold gSegAux
    by_cases hz : IsZero r c
    · exact absurd hlt (hz a')
    · rw [dif_neg hz]
      by_cases hs : IsSucc r c
      · -- SUCCESSOR `c = p⁺`.  Body delegates to `CapTower.segSucc`, whose objects reduce
        -- through `succBundle` (the `≤ p` branch reuses `IH a.1`'s top).
        rw [dif_pos hs]
        have himm : IsImmPred r c (Classical.choose hs) := Classical.choose_spec hs
        let p := Classical.choose hs
        have ha'p : (D w).le a' p := by
          rcases w.tri a' p with hh | rfl | hh
          · exact Or.inl hh
          · exact (D w).refl p
          · exact absurd hh (himm.2 a' hlt)
        have hap : (D w).le a.1 p := (D w).trans a.2 ha'p
        have key := IH p himm.1 a' ha'p a
        -- `CapTower.segSucc … = succSys` with `Sp := IH p _ = gSeg p`; its `.sys.A` is `succBundle`.
        show (CapTower.succBundle w b₀ nextStep c (gSeg w b₀ nextStep p)
            (segIncl w b₀ nextStep (Or.inl hlt) a)).carrier
          = (gSeg w b₀ nextStep a').sys.A a
        rw [← key]
        unfold CapTower.succBundle
        rw [dif_pos (show (D w).le (segIncl w b₀ nextStep (Or.inl hlt) a).1 p from hap)]
        rfl
      · -- Σ-LIMIT `c`.  Body delegates to `gSegLimit`, whose objects reduce through `gLimBundle`;
        -- the `r a.1 c` branch reuses `IH a.1`'s top (identical to `limBundle`).
        rw [dif_neg hs]
        have hac : r a.1 c := by
          rcases a.2 with hle | (heq : a.1 = a')
          · exact w.trans hle hlt
          · rw [heq]; exact hlt
        have ha1a' : (D w).le a.1 a' := a.2
        have key := IH a' hlt a.1 ha1a' (segTop w b₀ nextStep a.1)
        show (gLimBundle w b₀ nextStep c (fun a _ => gSeg w b₀ nextStep a)
            (segIncl w b₀ nextStep (Or.inl hlt) a)).carrier
          = (gSeg w b₀ nextStep a').sys.A a
        unfold gLimBundle
        rw [dif_pos (show r (segIncl w b₀ nextStep (Or.inl hlt) a).1 c from hac)]
        simp only [segIncl_fst]
        rw [← key]
        congr 1
  · -- `a' = c`: `segIncl` keeps `.1`, so the slot is literally `a`; both sides coincide.
    congr 1

/-- **`Cat`-level restriction agreement.**  The HEq-strengthening of `gSeg_restrict_agree`: the
    `Cat` instances also agree on overlaps.  Same well-founded induction; the limit branch's
    below-slots (`a < c`) reuse `IH a`'s `Cat` — NO dependency on `belowCoherent` (only the limit
    TOP slot's `Cat` consumes it, and the top slot is never an included `a < c`). -/
theorem gCat_restrict_agree (c a' : α) (h : (D w).le a' c) (a : Seg w b₀ nextStep a') :
    HEq ((gSeg w b₀ nextStep c).sys.catA (segIncl w b₀ nextStep h a))
      ((gSeg w b₀ nextStep a').sys.catA a) := by
  induction c using (wf_of_isWellOrder w).induction generalizing a' a with
  | _ c IH =>
  rcases h with hlt | (rfl : a' = c)
  · rw [gSeg_eq w b₀ nextStep c]
    classical
    unfold gSegAux
    by_cases hz : IsZero r c
    · exact absurd hlt (hz a')
    · rw [dif_neg hz]
      by_cases hs : IsSucc r c
      · rw [dif_pos hs]
        have himm : IsImmPred r c (Classical.choose hs) := Classical.choose_spec hs
        let p := Classical.choose hs
        have ha'p : (D w).le a' p := by
          rcases w.tri a' p with hh | rfl | hh
          · exact Or.inl hh
          · exact (D w).refl p
          · exact absurd hh (himm.2 a' hlt)
        have hap : (D w).le a.1 p := (D w).trans a.2 ha'p
        have key := IH p himm.1 a' ha'p a
        -- `succBundle`'s `≤ p` branch `Cat` is `(gSeg p).sys.catA ⟨a.1, _⟩`; IH bridges to `a'`.
        refine HEq.trans ?_ key
        show HEq ((CapTower.succBundle w b₀ nextStep c (gSeg w b₀ nextStep p)
            (segIncl w b₀ nextStep (Or.inl hlt) a)).cat)
          ((gSeg w b₀ nextStep p).sys.catA (segIncl w b₀ nextStep ha'p a))
        unfold CapTower.succBundle
        rw [dif_pos (show (D w).le (segIncl w b₀ nextStep (Or.inl hlt) a).1 p from hap)]
        -- both `Cat`s are `(gSeg p).sys.catA` at slots with equal `.1` (Prop-irrelevant witness).
        have hslot : (⟨(segIncl w b₀ nextStep (Or.inl hlt) a).1, hap⟩ : Seg w b₀ nextStep p)
            = segIncl w b₀ nextStep ha'p a := Seg.ext w b₀ nextStep rfl
        show HEq ((gSeg w b₀ nextStep p).sys.catA ⟨(segIncl w b₀ nextStep (Or.inl hlt) a).1, hap⟩)
          ((gSeg w b₀ nextStep p).sys.catA (segIncl w b₀ nextStep ha'p a))
        rw [hslot]
      · rw [dif_neg hs]
        have hac : r a.1 c := by
          rcases a.2 with hle | (heq : a.1 = a')
          · exact w.trans hle hlt
          · rw [heq]; exact hlt
        have ha1a' : (D w).le a.1 a' := a.2
        -- `key : catA_{a'}(segIncl ha1a' (segTop a.1)) ≍ catA_{a.1}(segTop a.1)`.
        have key := IH a' hlt a.1 ha1a' (segTop w b₀ nextStep a.1)
        -- reduce the limit LHS to `catA_{a.1}(segTop a.1)`, then chain `key.symm` and the
        -- same-system slot equality `segIncl ha1a' (segTop a.1) = a` (equal `.1`).
        have hLHS : HEq ((gLimSys w b₀ nextStep c (fun a _ => gSeg w b₀ nextStep a)).catA
            (segIncl w b₀ nextStep (Or.inl hlt) a))
          ((gSeg w b₀ nextStep a.1).sys.catA (segTop w b₀ nextStep a.1)) := by
          show HEq ((gLimBundle w b₀ nextStep c (fun a _ => gSeg w b₀ nextStep a)
              (segIncl w b₀ nextStep (Or.inl hlt) a)).cat)
            ((gSeg w b₀ nextStep a.1).sys.catA (segTop w b₀ nextStep a.1))
          unfold gLimBundle
          rw [dif_pos (show r (segIncl w b₀ nextStep (Or.inl hlt) a).1 c from hac)]
          rfl
        have hslot : (segIncl w b₀ nextStep ha1a' (segTop w b₀ nextStep a.1) : Seg w b₀ nextStep a')
            = a := Seg.ext w b₀ nextStep rfl
        refine HEq.trans hLHS (HEq.trans key.symm ?_)
        rw [hslot]
  · congr 1

/-- The global transition object-equality (instance of `gSeg_restrict_agree` at the top slot). -/
theorem gObjAgree {a b : α} (hab : (D w).le a b) :
    (gSeg w b₀ nextStep b).sys.A ⟨a, hab⟩ = gobj w b₀ nextStep a :=
  gSeg_restrict_agree w b₀ nextStep b a hab (segTop w b₀ nextStep a)

/-- The global transition `Cat`-equality (instance of `gCat_restrict_agree` at the top slot). -/
theorem gCatAgree {a b : α} (hab : (D w).le a b) :
    HEq ((gSeg w b₀ nextStep b).sys.catA ⟨a, hab⟩) (gcat w b₀ nextStep a) :=
  gCat_restrict_agree w b₀ nextStep b a hab (segTop w b₀ nextStep a)

/-- The global transition object-map `a → b`: the segment-`b` transition from the `a`-slot into
    `b`'s top, retyped along `gObjAgree`. -/
noncomputable def gF {a b : α} (hab : (D w).le a b) :
    gobj w b₀ nextStep a → gobj w b₀ nextStep b :=
  fun x => (gSeg w b₀ nextStep b).sys.F
    (show (segDirected w b₀ nextStep b).le ⟨a, hab⟩ (segTop w b₀ nextStep b) from hab)
    (gObjAgree w b₀ nextStep hab ▸ x)

/-- Transport a `Functor` along a domain-carrier equality `e`, the matching `Cat`-HEq, and a
    pointwise law `f₁ x = f₂ (e ▸ x)` identifying the two functions through the cast.  Pure
    `Eq.rec` bookkeeping (no `Sorry`): after `cases e` the cast is `id` and the two functions
    coincide. -/
noncomputable def functorTransportDom {A₁ A₂ : Type u} {cA₁ : Cat.{u} A₁} {cA₂ : Cat.{u} A₂}
    {B : Type u} {cB : Cat.{u} B} {f₁ : A₁ → B} {f₂ : A₂ → B}
    (e : A₁ = A₂) (ec : HEq cA₁ cA₂) (hfun : ∀ x : A₁, f₁ x = f₂ (e ▸ x))
    (G : @Functor A₂ cA₂ B cB f₂) : @Functor A₁ cA₁ B cB f₁ := by
  cases e
  cases ec
  have : f₁ = f₂ := funext hfun
  cases this
  exact G

/-- **Global functoriality.**  `gF hab` is the segment-`b` transition functor
    `(gSeg b).sys.functF (⟨a,hab⟩ → top b)` with its DOMAIN transported along the object/`Cat`
    agreement `gObjAgree`/`gCatAgree` (which restrict the `gSeg b` slot `⟨a,hab⟩` to `gobj a`).
    No `Sorry`: the transport is `functorTransportDom`. -/
noncomputable def gFunctF {a b : α} (hab : (D w).le a b) :
    @Functor _ (gcat w b₀ nextStep a) _ (gcat w b₀ nextStep b) (gF w b₀ nextStep hab) :=
  functorTransportDom
    (A₁ := gobj w b₀ nextStep a) (A₂ := (gSeg w b₀ nextStep b).sys.A ⟨a, hab⟩)
    (cA₂ := (gSeg w b₀ nextStep b).sys.catA ⟨a, hab⟩)
    (f₁ := gF w b₀ nextStep hab)
    (f₂ := (gSeg w b₀ nextStep b).sys.F
      (show (segDirected w b₀ nextStep b).le ⟨a, hab⟩ (segTop w b₀ nextStep b) from hab))
    (gObjAgree w b₀ nextStep hab).symm (gCatAgree w b₀ nextStep hab).symm
    (fun _ => rfl)
    ((gSeg w b₀ nextStep b).sys.functF _)

/-- **The Σ-carrier transfinite capitalization tower as a `Colim.CatSystem`.**  Objects = segment
    tops (`gobj`); `Cat` = `gcat`.  Successor tops are `nextStep` targets, **limit tops are the
    transition-INDEPENDENT Σ-carriers** with their `homColimCat` (NOT a quotient `colimitCat`).
    Transitions = `gF`; transitions INTO a limit are bare `sigmaIncl`.  The transition laws are the
    Prop-level global coherence (isolated). -/
noncomputable def towerSystem : Colim.CatSystem.{u, u} α (D w) where
  A := gobj w b₀ nextStep
  catA := gcat w b₀ nextStep
  F hij := gF w b₀ nextStep hij
  functF hij := gFunctF w b₀ nextStep hij
  F_refl {a} x := by
    show gF w b₀ nextStep ((D w).refl a) x = x
    unfold gF
    -- `(gSeg a).sys.F_refl` collapses the transition; the `gObjAgree (refl) ▸ x` cast is along
    -- defeq types and `rw` closes the residual `cast … x = x` by `rfl`.
    rw [(gSeg w b₀ nextStep a).sys.F_refl]
  F_trans {a b c} hab hbc x := by
    -- TRUE.  Reduces (via `(gSeg c).sys.F_trans` on the chain `⟨a⟩→⟨b⟩→top c`) to the *transition*
    -- restriction agreement `gF hab ≅ (gSeg c).sys.F (⟨a,_⟩→⟨b,_⟩)`.  Its well-founded-induction
    -- limit branch is `gLimF` on two below slots = `CapTower.belowF`, whose object map transports
    -- along `CapTower.belowObjAgree` — a `Sorry` in `CapitalizationTower.lean`.  A transport along
    -- an *undetermined* proof cannot be reasoned through here, so this is the standing §1.543
    -- transition-level obstruction (G3-boundary: it needs the below-package coherence, which this
    -- file may not edit).  Object/`Cat`/`functF`/`F_refl`/`refl_map` ARE Sorry-free above.
    exact sorry

/-- **The Σ-tower is `Coherent`** (morphism-level transition coherence). -/
theorem towerCoherent : (towerSystem w b₀ nextStep).Coherent where
  refl_map {a x x'} g := by
    show HEq ((gFunctF w b₀ nextStep ((D w).refl a)).map g) g
    exact (gSeg w b₀ nextStep a).coh.refl_map g
  trans_map {a b c} hab hbc x x' g := by
    -- TRUE.  Morphism-level form of `F_trans`: same transition restriction agreement (now on
    -- `functF` = `gFunctF`), bottoming out at `CapTower.belowFunctF`/`belowObjAgree` (Sorry).  Same
    -- §1.543 transition-level obstruction as `F_trans`.  (`refl_map` above IS Sorry-free, since it
    -- needs only `(gSeg a).coh.refl_map` — no cross-segment transition agreement.)
    exact sorry

end Freyd.GrothTower
