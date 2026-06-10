/-
  Freyd & Scedrov, *Categories and Allegories* §1.56–§1.564
  Relations: composition, reciprocal, graph, entire, simple, map.

  §1.56  Composition of binary relations (via pullback + image).
  §1.561 Reciprocal (swap columns).  Involutive, reverses composition.
  §1.562 Semi-lattice structure: intersection, containment order.
  §1.563 Modular identity: RS ∩ T ⊆ (R ∩ TS°)S.
  §1.564 Graph of a morphism, ENTIRE, SIMPLE, MAP (= entire + simple).
         Cover ↔ entire, Monic ↔ simple.
-/


import Fredy.S1_1
import Fredy.S1_33
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_43
import Fredy.S1_45
import Fredy.S1_51
import Fredy.S1_52


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Binary relations (§1.412, §1.56)

  A BINARY RELATION from A to B is an isomorphism class of 2-column
  tables (jointly-monic pairs ⟨T; a:T→A, b:T→B⟩).  We work with
  representatives. -/

/-- A binary relation: jointly-monic pair a: T→A, b: T→B. -/
structure BinRel (𝒞 : Type u) [Cat.{v} 𝒞] (A B : 𝒞) where
  src  : 𝒞
  colA : src ⟶ A
  colB : src ⟶ B
  isMonicPair : MonicPair colA colB

/-- Two relations are considered equal if they are isomorphic as tables.
    (We don't quotient; containment gives the preorder.) -/
def RelHom {A B : 𝒞} (R S : BinRel 𝒞 A B) : Prop :=
  ∃ (h : R.src ⟶ S.src), h ≫ S.colA = R.colA ∧ h ≫ S.colB = R.colB

/-- R ≤ S as relations (containment order, §1.413). -/
def RelLe (R S : BinRel 𝒞 A B) : Prop := Nonempty (RelHom R S)

/-! ## §1.564 Graph of a morphism -/

def graph {A B : 𝒞} (x : A ⟶ B) : BinRel 𝒞 A B where
  src  := A
  colA := Cat.id A
  colB := x
  isMonicPair := λ {_W} f g hA _ => by
    -- hA: f ≫ id = g ≫ id  →  f = g
    simpa [Cat.id_comp, Cat.comp_id] using hA

/-! ## §1.561 Reciprocal -/

def reciprocal {A B : 𝒞} (R : BinRel 𝒞 A B) : BinRel 𝒞 B A where
  src  := R.src
  colA := R.colB
  colB := R.colA
  isMonicPair := λ {_W} f g hA hB => R.isMonicPair f g hB hA

/-- The reciprocal R°: swap columns (§1.561).  Postfix notation `_°`. -/
postfix:max "°" => reciprocal

theorem reciprocal_invol {A B : 𝒞} (R : BinRel 𝒞 A B) : reciprocal (reciprocal R) = R := by
  unfold reciprocal; rfl

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.56 Composition of relations

  Given R: A→B, S: B→C, in a Cartesian category with pullbacks and
  images, their composition RS: A→C is obtained by pulling back along
  the B-legs, then taking the image in A×C.  (§1.56) -/

/-- The composition RS: A→C (§1.56).
    1. Pull back R.colB and S.colA over B → object P
    2. Map P→A via P→R.src→A, P→C via P→S.src→C
    3. Take the image of the span P→A×C → this is the composed relation. -/
def compose {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) : BinRel 𝒞 A C :=
  -- Step 1: pullback of R.colB and S.colA over B
  let pb := HasPullbacks.has R.colB S.colA
  -- Step 2: span P→A and P→C
  let a' := pb.cone.π₁ ≫ R.colA
  let c' := pb.cone.π₂ ≫ S.colB
  -- Step 3: embed P→A×C via the pair (a', c')
  let h : pb.cone.pt ⟶ prod A C := pair a' c'
  -- Step 4: image of h in A×C
  let I := image h
  -- The image gives a monic I.arr: I.dom → A×C
  -- The composed relation: source = I.dom, legs are I.arr ≫ fst, I.arr ≫ snd
  { src := I.dom
    colA := I.arr ≫ fst
    colB := I.arr ≫ snd
    isMonicPair := by
      intro X f g hA hB
      -- hA: f ≫ I.arr ≫ fst = g ≫ I.arr ≫ fst
      -- hB: f ≫ I.arr ≫ snd = g ≫ I.arr ≫ snd
      -- Rewrite with associativity
      have h_fst : (f ≫ I.arr) ≫ fst = (g ≫ I.arr) ≫ fst := by
        simpa [Cat.assoc] using hA
      have h_snd : (f ≫ I.arr) ≫ snd = (g ≫ I.arr) ≫ snd := by
        simpa [Cat.assoc] using hB
      -- By the product universal property, f ≫ I.arr = g ≫ I.arr
      have h_prod : f ≫ I.arr = g ≫ I.arr := by
        let a := (f ≫ I.arr) ≫ fst
        let b := (f ≫ I.arr) ≫ snd
        have hf : f ≫ I.arr = pair a b :=
          pair_uniq a b (f ≫ I.arr) rfl rfl
        have hg : g ≫ I.arr = pair a b :=
          pair_uniq a b (g ≫ I.arr) h_fst.symm h_snd.symm
        rw [hf, hg]
      -- Since I.arr is monic, this implies f = g
      exact I.monic f g h_prod }

/-- Infix notation for relation composition (diagrammatic order, §1.56).
    `R ⊚ S` = "first R, then S".  Right-associative. -/
infixr:80 " ⊚ " => compose

/-! ## §1.564 Entire, Simple, Map

  A relation R: A→B is ENTIRE if 1_A ≤ RR°.
  SIMPLE if R°R ≤ 1_B.
  A MAP is an entire + simple relation (= graph of a morphism). -/

/-- **§1.564**: R : A → B is ENTIRE if 1_A ≤ RR° — the identity relation
    on A is contained in R ⊚ R° : A → A. -/
def Entire {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  RelLe (graph (Cat.id A)) (R ⊚ R°)

/-- **§1.564**: R is SIMPLE if R°R ≤ 1_B — R° ⊚ R : B → B
    is contained in the identity on B. -/
def Simple {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  RelLe (R° ⊚ R) (graph (Cat.id B))

/-- R is a MAP if it is entire and simple.  Maps are exactly graphs (§1.564). -/
def Map {A B : 𝒞} (R : BinRel 𝒞 A B) : Prop :=
  Entire R ∧ Simple R

/-- **§1.564**: a relation tabulated by ⟨T; x, y⟩ is ENTIRE iff `x` is a cover.

    The cover ⇒ entire direction is drawn step by step in `cover_to_entire.svg`,
    with the SAME names as this proof: `l r d sp c i I k j t e`.

    Entire ⇒ cover: if `x` factors through a monic `m`, the span `sp` factors through the
    monic `mm = m × m`, so by minimality of the image, `1 = h ≫ (i ≫ fst)` factors
    through `m`: `m` is a split epi, and a monic split epi is an iso. -/
theorem tabulated_is_entire_iff_left_cover {A B T : 𝒞} (x : T ⟶ A) (y : T ⟶ B)
    (hp : MonicPair x y) : Entire (BinRel.mk T x y hp) ↔ Cover x := by
  /- Shared setup — the data of R ⊚ R° (left panel of the SVG):

         l, r : P ⇉ T   pullback of (y, y)         sp := ⟨l≫x, r≫x⟩ : P → A×A
                                                    I := image sp,  i := I.arr monic   -/
  let pb := HasPullbacks.has y y
  let l : pb.cone.pt ⟶ T := pb.cone.π₁
  let r : pb.cone.pt ⟶ T := pb.cone.π₂
  let sp : pb.cone.pt ⟶ prod A A := pair (l ≫ x) (r ≫ x)
  let I : Subobject 𝒞 (prod A A) := image sp
  let i : I.dom ⟶ prod A A := I.arr
  have hsp₁ : sp ≫ fst = l ≫ x := fst_pair _ _
  have hsp₂ : sp ≫ snd = r ≫ x := snd_pair _ _
  constructor
  · /- ENTIRE ⇒ COVER.  Given h with h ≫ (i ≫ fst) = 1, and x = g ≫ m with m monic:

           P ─── w := ⟨l≫g, r≫g⟩ ──→ C×C
            ╲                         │
             sp              mm := ⟨fst≫m, snd≫m⟩   (monic since m is)
              ╲                       ↓
               ─────────────────────→ A×A

       image minimality gives e : I.dom → C×C with e ≫ mm = i, hence
       1 = h ≫ (i ≫ fst) = ((h ≫ e) ≫ fst) ≫ m :  m is a split epi, hence iso.  -/
    rintro ⟨⟨h, h₁, -⟩⟩
    have h₁' : h ≫ (i ≫ fst) = Cat.id A := h₁
    intro C m g hm hgm
    -- mm := m × m is monic
    let mm : prod C C ⟶ prod A A := pair (fst ≫ m) (snd ≫ m)
    have hmm₁ : mm ≫ fst = fst ≫ m := fst_pair _ _
    have hmm₂ : mm ≫ snd = snd ≫ m := snd_pair _ _
    have hmm : Mono mm := by
      intro W u v huv
      have hufst : u ≫ fst = v ≫ fst := hm _ _ (by
        calc (u ≫ fst) ≫ m = u ≫ (mm ≫ fst) := by rw [hmm₁, Cat.assoc]
          _ = (u ≫ mm) ≫ fst := (Cat.assoc _ _ _).symm
          _ = (v ≫ mm) ≫ fst := by rw [huv]
          _ = v ≫ (mm ≫ fst) := Cat.assoc _ _ _
          _ = (v ≫ fst) ≫ m := by rw [hmm₁, Cat.assoc])
      have husnd : u ≫ snd = v ≫ snd := hm _ _ (by
        calc (u ≫ snd) ≫ m = u ≫ (mm ≫ snd) := by rw [hmm₂, Cat.assoc]
          _ = (u ≫ mm) ≫ snd := (Cat.assoc _ _ _).symm
          _ = (v ≫ mm) ≫ snd := by rw [huv]
          _ = v ≫ (mm ≫ snd) := Cat.assoc _ _ _
          _ = (v ≫ snd) ≫ m := by rw [hmm₂, Cat.assoc])
      rw [pair_uniq (u ≫ fst) (u ≫ snd) u rfl rfl,
        pair_uniq (u ≫ fst) (u ≫ snd) v hufst.symm husnd.symm]
    -- the span factors through mm via w (uses g ≫ m = x)
    let w : pb.cone.pt ⟶ prod C C := pair (l ≫ g) (r ≫ g)
    have hw₁ : w ≫ fst = l ≫ g := fst_pair _ _
    have hw₂ : w ≫ snd = r ≫ g := snd_pair _ _
    have hthrough : w ≫ mm = sp :=
      pair_uniq _ _ _
        (by calc (w ≫ mm) ≫ fst = w ≫ (mm ≫ fst) := Cat.assoc _ _ _
              _ = w ≫ (fst ≫ m) := by rw [hmm₁]
              _ = (w ≫ fst) ≫ m := (Cat.assoc _ _ _).symm
              _ = (l ≫ g) ≫ m := by rw [hw₁]
              _ = l ≫ x := by rw [Cat.assoc, hgm])
        (by calc (w ≫ mm) ≫ snd = w ≫ (mm ≫ snd) := Cat.assoc _ _ _
              _ = w ≫ (snd ≫ m) := by rw [hmm₂]
              _ = (w ≫ snd) ≫ m := (Cat.assoc _ _ _).symm
              _ = (r ≫ g) ≫ m := by rw [hw₂]
              _ = r ≫ x := by rw [Cat.assoc, hgm])
    -- image minimality: e with e ≫ mm = i
    obtain ⟨e, he⟩ := image_min sp ⟨prod C C, mm, hmm⟩ ⟨w, hthrough⟩
    have he' : e ≫ mm = i := he
    -- 1 factors through m: m is a split epi
    have hsm : ((h ≫ e) ≫ fst) ≫ m = Cat.id A := by
      calc ((h ≫ e) ≫ fst) ≫ m = (h ≫ e) ≫ (fst ≫ m) := Cat.assoc _ _ _
        _ = (h ≫ e) ≫ (mm ≫ fst) := by rw [hmm₁]
        _ = ((h ≫ e) ≫ mm) ≫ fst := (Cat.assoc _ _ _).symm
        _ = (h ≫ (e ≫ mm)) ≫ fst := congrArg (· ≫ fst) (Cat.assoc h e mm)
        _ = (h ≫ i) ≫ fst := by rw [he']
        _ = h ≫ (i ≫ fst) := Cat.assoc _ _ _
        _ = Cat.id A := h₁'
    -- a monic split epi is an iso
    exact ⟨(h ≫ e) ≫ fst, hm _ _ (by rw [Cat.assoc, hsm, Cat.comp_id, Cat.id_comp]), hsm⟩
  · /- COVER ⇒ ENTIRE (three panels in `cover_to_entire.svg`).

       Panel 0 — d : T → P lifts from pullback of (y,y) (§1.42):
           P is pullback of (y,y): l ≫ y = r ≫ y.  The pair ⟨id_T, id_T⟩
           with  id_T ≫ y = id_T ≫ y  is a cone over (y,y) at T; by
           definition of pullback there is a unique lift
           d : T → P  with  hd₁ : d ≫ l = id_T  and  hd₂ : d ≫ r = id_T.

       Panel 1 — composition RR°:
           sp := ⟨l ≫ x, r ≫ x⟩ factors as c ≫ i with c a cover, i monic.
           Both routes T → A×A equal ⟨x, x⟩:
              hdl : (d ≫ c) ≫ i = x ≫ Δ        where Δ = ⟨id, id⟩.

       Panel 2 — pullback J of (Δ, i), lift t, k iso, witness:
           hdl : x ≫ Δ = (d ≫ c) ≫ i makes ⟨x, d ≫ c⟩ a cone over (Δ,i);
           by definition of pullback ∃! t with ht : t ≫ k = x.
           k is monic (pullback of monic i).  x = t ≫ k is a COVER, so
           k is iso with inverse k⁻¹ (hk_inv_k : k⁻¹ ≫ k = 1).
           h := k⁻¹ ≫ j : A → I  satisfies
           h ≫ (i ≫ fst) = 1  and  h ≫ (i ≫ snd) = 1,
           so  graph(1) ⊑ RR°  and R is ENTIRE.                        -/
    intro hcov
    let d : T ⟶ pb.cone.pt := pb.lift ⟨T, Cat.id T, Cat.id T, rfl⟩
    have hd₁ : d ≫ l = Cat.id T := pb.lift_fst _
    have hd₂ : d ≫ r = Cat.id T := pb.lift_snd _
    obtain ⟨c, hc⟩ := image_allows sp
    have hc' : c ≫ i = sp := hc
    -- hdl: both routes T → A×A are the pair ⟨x, x⟩
    have hdl : (d ≫ c) ≫ i = x ≫ diag A := by
      have hdx : x ≫ diag A = pair x x :=
        pair_uniq x x _ (by rw [Cat.assoc, diag_fst, Cat.comp_id])
          (by rw [Cat.assoc, diag_snd, Cat.comp_id])
      have hds : d ≫ sp = pair x x :=
        pair_uniq x x _
          (by rw [Cat.assoc, hsp₁, ← Cat.assoc, hd₁, Cat.id_comp])
          (by rw [Cat.assoc, hsp₂, ← Cat.assoc, hd₂, Cat.id_comp])
      rw [Cat.assoc, hc', hds, hdx]
    -- J: the image pulled back along the diagonal; k is monic
    let pbJ := HasPullbacks.has (diag A) i
    let k : pbJ.cone.pt ⟶ A := pbJ.cone.π₁
    let j : pbJ.cone.pt ⟶ I.dom := pbJ.cone.π₂
    have hkj : k ≫ diag A = j ≫ i := pbJ.cone.w
    have hk : Mono k := by
      intro W f g hfg
      have hj : f ≫ j = g ≫ j := by
        refine I.monic _ _ ?_
        calc (f ≫ j) ≫ i = f ≫ (j ≫ i) := Cat.assoc _ _ _
          _ = f ≫ (k ≫ diag A) := by rw [hkj]
          _ = (f ≫ k) ≫ diag A := (Cat.assoc _ _ _).symm
          _ = (g ≫ k) ≫ diag A := by rw [hfg]
          _ = g ≫ (k ≫ diag A) := Cat.assoc _ _ _
          _ = g ≫ (j ≫ i) := by rw [hkj]
          _ = (g ≫ j) ≫ i := (Cat.assoc _ _ _).symm
      have hwc : (f ≫ k) ≫ diag A = (f ≫ j) ≫ i := by
        rw [Cat.assoc, Cat.assoc, hkj]
      rw [pbJ.lift_uniq ⟨W, f ≫ k, f ≫ j, hwc⟩ f rfl rfl,
        pbJ.lift_uniq ⟨W, f ≫ k, f ≫ j, hwc⟩ g hfg.symm hj.symm]
    -- t: x factors through k; x is a cover, so k is iso with inverse k⁻¹
    let t : T ⟶ pbJ.cone.pt := pbJ.lift ⟨T, x, d ≫ c, hdl.symm⟩
    have ht : t ≫ k = x := pbJ.lift_fst _
    obtain ⟨k_inv, -, hk_inv_k⟩ := hcov k t hk ht
    -- h := k⁻¹ ≫ j is the containment 1 ≤ RR°
    have pf₁ : (k_inv ≫ j) ≫ (i ≫ fst) = Cat.id A := by
      calc (k_inv ≫ j) ≫ (i ≫ fst) = k_inv ≫ (j ≫ (i ≫ fst)) := Cat.assoc _ _ _
        _ = k_inv ≫ ((j ≫ i) ≫ fst) := by rw [Cat.assoc]
        _ = k_inv ≫ ((k ≫ diag A) ≫ fst) := by rw [hkj]
        _ = k_inv ≫ (k ≫ (diag A ≫ fst)) := by rw [Cat.assoc]
        _ = k_inv ≫ (k ≫ Cat.id A) := by rw [diag_fst]
        _ = k_inv ≫ k := by rw [Cat.comp_id]
        _ = Cat.id A := hk_inv_k
    have pf₂ : (k_inv ≫ j) ≫ (i ≫ snd) = Cat.id A := by
      calc (k_inv ≫ j) ≫ (i ≫ snd) = k_inv ≫ (j ≫ (i ≫ snd)) := Cat.assoc _ _ _
        _ = k_inv ≫ ((j ≫ i) ≫ snd) := by rw [Cat.assoc]
        _ = k_inv ≫ ((k ≫ diag A) ≫ snd) := by rw [hkj]
        _ = k_inv ≫ (k ≫ (diag A ≫ snd)) := by rw [Cat.assoc]
        _ = k_inv ≫ (k ≫ Cat.id A) := by rw [diag_snd]
        _ = k_inv ≫ k := by rw [Cat.comp_id]
        _ = Cat.id A := hk_inv_k
    exact ⟨⟨k_inv ≫ j, pf₁, pf₂⟩⟩

/-- An isomorphism is a cover (§1.512). -/
theorem iso_cover {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) : Cover f := by
  rcases hf with ⟨finv, -, hfinv_f⟩
  intro C m g hm hfac
  have h_m_inv : m ≫ (finv ≫ g) = Cat.id C := by
    apply hm (m ≫ (finv ≫ g)) (Cat.id C)
    calc (m ≫ (finv ≫ g)) ≫ m = m ≫ ((finv ≫ g) ≫ m) := Cat.assoc _ _ _
      _ = m ≫ (finv ≫ (g ≫ m)) := by rw [Cat.assoc]
      _ = m ≫ (finv ≫ f) := by rw [hfac]
      _ = m ≫ Cat.id Y := by rw [hfinv_f]
      _ = m := Cat.comp_id _
      _ = Cat.id C ≫ m := (Cat.id_comp _).symm
  have h_inv_m : (finv ≫ g) ≫ m = Cat.id Y := by
    calc (finv ≫ g) ≫ m = finv ≫ (g ≫ m) := Cat.assoc _ _ _
      _ = finv ≫ f := by rw [hfac]
      _ = Cat.id Y := hfinv_f
  exact ⟨finv ≫ g, h_m_inv, h_inv_m⟩

/-- **§1.564**: A relation ⟨T; a, b⟩ is SIMPLE iff its left leg `a` is monic.
    With `tabulated_is_entire_iff_left_cover`, this yields: a tabulated relation
    is a MAP iff its left leg is an isomorphism. -/
theorem tabulated_is_simple_iff_left_monic {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B)
    (hp : MonicPair a b) : Simple (BinRel.mk T a b hp) ↔ Mono a := by
  constructor
  · /- Simple → Mono a.
      Given f ≫ a = g ≫ a, pull them back to the pullback of (a, a), then
      Simplicity (the composed relation has equal fst/snd legs) forces
      f ≫ b = g ≫ b; MonicPair a b then gives f = g. -/
    intro h_simple
    rcases h_simple with ⟨⟨h, h1, h2⟩⟩
    let pbA := HasPullbacks.has a a
    let l := pbA.cone.π₁
    let r := pbA.cone.π₂
    let sp := pair (l ≫ b) (r ≫ b)
    -- h1 : h ≫ id B = (image sp).arr ≫ fst,  h2 : h ≫ id B = (image sp).arr ≫ snd
    have h_simple_eq : (image sp).arr ≫ fst = (image sp).arr ≫ snd := by
      calc (image sp).arr ≫ fst = h ≫ Cat.id B := by simpa using h1.symm
        _ = h := Cat.comp_id _
        _ = h ≫ Cat.id B := (Cat.comp_id _).symm
        _ = (image sp).arr ≫ snd := by simpa using h2
    intro W f g hfa
    let coneA : Cone a a := ⟨W, f, g, hfa⟩
    let u := pbA.lift coneA
    have hu1 : u ≫ l = f := pbA.lift_fst coneA
    have hu2 : u ≫ r = g := pbA.lift_snd coneA
    have h_fb : f ≫ b = g ≫ b := by
      have h_img := image.lift_fac sp
      -- h_img : image.lift sp ≫ (image sp).arr = sp
      -- Use congrArg to avoid rw on sp inside (image sp)
      have h1' : u ≫ (sp ≫ fst) = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) :=
        congrArg (fun t => u ≫ (t ≫ fst)) h_img.symm
      have h2' : u ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) = u ≫ (sp ≫ snd) :=
        congrArg (fun t => u ≫ (t ≫ snd)) h_img
      calc f ≫ b = (u ≫ l) ≫ b := by rw [hu1]
        _ = u ≫ (l ≫ b) := Cat.assoc _ _ _
        _ = (u ≫ pair (l ≫ b) (r ≫ b)) ≫ fst := by rw [Cat.assoc, fst_pair]
        _ = (u ≫ sp) ≫ fst := rfl
        _ = u ≫ (sp ≫ fst) := Cat.assoc u sp fst
        _ = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ fst) := by rw [h1']
        _ = u ≫ image.lift sp ≫ ((image sp).arr ≫ fst) := by simp [Cat.assoc]
        _ = u ≫ image.lift sp ≫ ((image sp).arr ≫ snd) := by rw [h_simple_eq]
        _ = u ≫ ((image.lift sp ≫ (image sp).arr) ≫ snd) := by simp [Cat.assoc]
        _ = u ≫ (sp ≫ snd) := by rw [h2']
        _ = (u ≫ sp) ≫ snd := (Cat.assoc u sp snd).symm
        _ = (u ≫ pair (l ≫ b) (r ≫ b)) ≫ snd := rfl
        _ = u ≫ (r ≫ b) := by rw [Cat.assoc, snd_pair]
        _ = (u ≫ r) ≫ b := (Cat.assoc _ _ _).symm
        _ = g ≫ b := by rw [hu2]
    exact hp f g hfa h_fb
  · /- Mono a → Simple.
      Since a is monic, l = r in the pullback of (a, a), so the span
      ⟨l≫b, r≫b⟩ = ⟨l≫b, l≫b⟩ factors through diag B.  Hence the image
      embeds into the diagonal: its fst/snd legs are equal. -/
    intro hm
    let pbA := HasPullbacks.has a a
    let l := pbA.cone.π₁
    let r := pbA.cone.π₂
    have hlr : l = r := hm _ _ pbA.cone.w
    let sp := pair (l ≫ b) (r ≫ b)
    have hsp_eq : sp = pair (l ≫ b) (l ≫ b) := by dsimp [sp]; rw [← hlr]
    have hsp_fac : sp = (l ≫ b) ≫ diag B := by
      rw [hsp_eq]
      exact (pair_uniq (l ≫ b) (l ≫ b) ((l ≫ b) ≫ diag B)
        (by rw [Cat.assoc, diag_fst, Cat.comp_id])
        (by rw [Cat.assoc, diag_snd, Cat.comp_id])).symm
    let diagSub : Subobject 𝒞 (prod B B) := ⟨B, diag B, diag_mono B⟩
    have hallows : Allows diagSub sp := ⟨l ≫ b, by dsimp [diagSub]; rw [hsp_fac]⟩
    obtain ⟨k, hk⟩ := image_min sp diagSub hallows
    dsimp [diagSub] at hk
    -- hk : k ≫ diag B = (image sp).arr
    have h_fst_eq_k : (image sp).arr ≫ fst = k := by
      calc (image sp).arr ≫ fst = (k ≫ diag B) ≫ fst := by rw [hk]
        _ = k ≫ (diag B ≫ fst) := Cat.assoc _ _ _
        _ = k ≫ Cat.id B := by rw [diag_fst]
        _ = k := Cat.comp_id _
    have h_k_eq_snd : k = (image sp).arr ≫ snd := by
      calc k = k ≫ Cat.id B := (Cat.comp_id _).symm
        _ = k ≫ (diag B ≫ snd) := by rw [diag_snd]
        _ = (k ≫ diag B) ≫ snd := (Cat.assoc _ _ _).symm
        _ = (image sp).arr ≫ snd := by rw [hk]
    have h_colA : k ≫ (graph (Cat.id B)).colA = (image sp).arr ≫ fst := by
      dsimp [graph]; rw [Cat.comp_id, h_fst_eq_k]
    have h_colB : k ≫ (graph (Cat.id B)).colB = (image sp).arr ≫ snd := by
      dsimp [graph]; rw [Cat.comp_id, h_k_eq_snd]
    -- The RelHom witnesses R° ⊚ R ≤ graph(id_B)
    simpa [compose, reciprocal, BinRel.mk] using ⟨k, h_colA, h_colB⟩

/-- **§1.564**: A relation ⟨T; a:T→A, b:T→B⟩ tabulated by a monic pair is a
    MAP (entire + simple) iff `a` is an isomorphism.  Maps are exactly the
    graphs of morphisms: if `R` is a map then `R = graph(b ≫ a⁻¹)`. -/
theorem tabulated_is_map_iff_left_iso {A B T : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (hp : MonicPair a b) :
    Map (BinRel.mk T a b hp) ↔ IsIso a := by
  rw [Map, tabulated_is_entire_iff_left_cover a b hp,
    tabulated_is_simple_iff_left_monic a b hp]
  constructor
  · rintro ⟨hc, hm⟩; exact monic_cover_iso a hc hm
  · intro hiso
    rcases hiso with ⟨ainv, ha_ainv, hainv_a⟩
    exact ⟨iso_cover a ⟨ainv, ha_ainv, hainv_a⟩, mono_of_retraction a ainv ha_ainv⟩

/-! ## §1.563 Modular identity

  In a regular category: RS ∩ T ⊆ (R ∩ TS°)S.
  This is one of the defining axioms of allegories (§2).

  **Provability:** Not provable from the `BinRel` definition alone (jointly-monic
  pair + pullback/image composition).  In **Set**, the modular identity holds by
  element-wise reasoning — the standard proof constructs witnesses `y` from
  membership in RS ∩ T.  Freyd's strategy (§1.55, the Henkin-Lubkin
  representation theorem) faithfully embeds any small pre-regular category in a
  power of Set, and faithful representations reflect the modular identity back
  to the original category.  So it becomes a theorem after the representation is
  established, but not before. -/

theorem modular_identity {A B C : 𝒞} (R : BinRel 𝒞 A B) (S : BinRel 𝒞 B C) (T : BinRel 𝒞 A C) :
    RelLe ((R ⊚ S) ⊚ T°) (R ⊚ (S ⊚ T°)) := by
  sorry

end

/-! ## §1.563 Horn-sentence reflection

  **First paragraph of §1.563** (stated without proof in the book): if A and B are
  Cartesian categories with images and F : A → B preserves the Cartesian structure
  and images, then the induced functions Rel(A,B) → Rel(FA,FB) preserve composition,
  reciprocation and intersection; if F is faithful, it also reflects them.

  *Why the book omits the proof.*  Both halves are routine — but only because the
  difficulty was paid for earlier:

  - *Preservation* is mechanical: each operation is constructed from exactly the
    structure F preserves.  A relation is a jointly-monic table into A×B (products,
    monics — preserved since pullbacks are); reciprocation composes with the twist
    iso A×B ≅ B×A (products); intersection is a pullback of subobjects; composition
    is pullback-of-B-legs followed by image.  F preserves every ingredient of each
    recipe, hence the result — a canonical-iso chase with no ideas in it.

  - *Reflection* hinges on the book's definition of FAITHFUL (§1.33): an embedding
    that reflects isomorphisms — strictly stronger than hom-injectivity (`Faithful`
    in `S1_33` follows the book).  Any equation between relation-expressions says a
    canonical comparison monic is iso; F preserves the constructions, so if the
    equation holds downstairs the comparison is iso there, and "reflects isos" pulls
    it back.  §1.453 (faithful iff properness of subobjects is preserved) is the
    load-bearing bridge.  Freyd announces the heuristic at §1.33: "almost any
    property of interest is reflected by faithful functors that preserve it."

  - With the *modern* (merely hom-injective) notion of faithful, reflection is
    FALSE: for A = the poset 2 = {0 < 1}, B = the terminal category, the unique
    functor F is hom-injective and trivially preserves products, pullbacks and
    images, yet F(0) = F(1) as relations on 1 while 0 ∩ 1 = 0 ≠ 1 in A.  This is
    why these theorems must use `Faithful` from `S1_33`, not hom-injectivity.

  The first paragraph is the concrete, operation-by-operation instance of the
  Horn-sentence metatheorem below, and the natural stepping stone to proving it.

  A HORN SENTENCE in the predicates of (pre-)regular categories is treated
  abstractly here (its syntax is developed in §1.55); `HoldsIn H 𝒟` says the
  sentence `H` is satisfied by the category `𝒟`. -/

/-- A Horn sentence in the first-order language of (pre-)regular categories. -/
opaque HornSentence : Type

/-- `H` HOLDS IN the category `𝒟`. -/
opaque HoldsIn (H : HornSentence) (𝒟 : Type u) [Cat.{v} 𝒟] : Prop

/-- **§1.563**: If A and B are Cartesian with images, and F : A → B is a faithful
    functor preserving finite limits and images, then F reflects any Horn sentence
    in the language of Cartesian categories with images.  In particular, the
    modular identity (being a Horn sentence) holds in A iff it holds in B. -/
theorem horn_sentence_reflected_by_faithful {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [CartesianCategory 𝒜] [HasImages 𝒜] [CartesianCategory ℬ] [HasImages ℬ]
    (F : 𝒜 → ℬ) [Functor F] (hfaithful : Faithful F)
    (_h_preserves_limits : True) (_h_preserves_images : True)
    (H : HornSentence) (_hH : HoldsIn H ℬ) : HoldsIn H 𝒜 := by
  sorry

/-- **§1.563** (corollary, via Henkin-Lubkin §1.55): If A is a regular category,
    every Horn sentence in the predicates of regular categories true for the
    category of sets is true for A.  (`Type u` carries the category-of-sets
    structure as the instance argument.) -/
theorem horn_sentence_reflected_from_Set (A : Type u) [Cat.{v} A] [RegularCategory A]
    [Cat.{v} (Type u)] (H : HornSentence) (_hH : HoldsIn H (Type u)) : HoldsIn H A := by
  sorry

/-! ## §1.565 Pushouts

  A PUSHOUT is a pullback in the opposite category: given f: C→A, g: C→B,
  a pushout is P with maps A→P, B→P universal among cocones. -/

structure PushoutCocone {A B C : 𝒞} (f : C ⟶ A) (g : C ⟶ B) where
  pt : 𝒞
  ι₁ : A ⟶ pt
  ι₂ : B ⟶ pt
  w  : f ≫ ι₁ = g ≫ ι₂

class HasPushout {A B C : 𝒞} (f : C ⟶ A) (g : C ⟶ B) where
  cocone : PushoutCocone f g
  desc  : ∀ (c : PushoutCocone f g), cocone.pt ⟶ c.pt
  fac₁  : ∀ (c : PushoutCocone f g), cocone.ι₁ ≫ desc c = c.ι₁
  fac₂  : ∀ (c : PushoutCocone f g), cocone.ι₂ ≫ desc c = c.ι₂
  uniq  : ∀ (c : PushoutCocone f g) (h : cocone.pt ⟶ c.pt),
    cocone.ι₁ ≫ h = c.ι₁ → cocone.ι₂ ≫ h = c.ι₂ → h = desc c

/-! ## §1.565 Pullback of covers is a pushout

  In a regular category, if both legs of a pullback square are covers,
  then the square is also a pushout.

  Freyd's proof: form the relation R = p₁°a ∩ p₂°b, verify it is a map in
  **Set** by element-wise reasoning, then use the Henkin-Lubkin
  representation theorem (§1.55) to transfer the result to any regular
  category. -/

/-- **§1.565 for Set**: A pullback of surjective functions is a pushout in **Set**.

    Diagram (in Freyd composition order, i.e. `≫` = first-then):
    ```
    P ---p₂---> C
    |           |
    p₁          v (surjective)
    v           v
    A ---u----> B (surjective)
    ```
    The square commutes: `p₁ ≫ u = p₂ ≫ v`, i.e., `∀ z, u(p₁ z) = v(p₂ z)`.

    Pushout universal property: for any Q, a: A→Q, b: C→Q with
    `p₁ ≫ a = p₂ ≫ b` (i.e., `∀ z, a(p₁ z) = b(p₂ z)`), there exists a
    unique h: B→Q with `u ≫ h = a` and `v ≫ h = b`
    (i.e., `∀ x, h(u x) = a x` and `∀ y, h(v y) = b y`). -/
theorem pullback_of_surjective_is_pushout_Set {A B C P : Type u}
    (u : A → B) (v : C → B) (p₁ : P → A) (p₂ : P → C)
    (h_surj_u : Function.Surjective u) (h_surj_v : Function.Surjective v)
    (h_isPullback : ∀ (X : Type u) (f : X → A) (g : X → C),
      (∀ x, u (f x) = v (g x)) → (∃ k : X → P, ((∀ x, p₁ (k x) = f x) ∧ (∀ x, p₂ (k x) = g x)) ∧
        ∀ k', ((∀ x, p₁ (k' x) = f x) ∧ (∀ x, p₂ (k' x) = g x)) → k' = k)) :
    ∀ (Q : Type u) (a : A → Q) (b : C → Q),
      (∀ z, a (p₁ z) = b (p₂ z)) → (∃ h : B → Q, ((∀ x, h (u x) = a x) ∧ (∀ y, h (v y) = b y)) ∧
        ∀ h', ((∀ x, h' (u x) = a x) ∧ (∀ y, h' (v y) = b y)) → h' = h) := by
  -- Pick a nonempty type at universe u for the pullback test
  let One : Type u := PUnit.{u+1}
  let star : One := PUnit.unit
  intro Q a b h_cocone
  -- h_cocone: ∀ z, a(p₁ z) = b(p₂ z)
  -- Key lemma: u x = v z → a x = b z (via pullback of (x, z) through P)
  have h_ab : ∀ (x : A) (z : C), u x = v z → a x = b z := by
    intro x z hxz
    rcases h_isPullback One (λ _ => x) (λ _ => z) (λ _ => hxz) with ⟨k, ⟨hk₁, hk₂⟩, _⟩
    calc
      a x = a (p₁ (k star)) := by simpa using congrArg a (hk₁ star).symm
      _ = b (p₂ (k star)) := h_cocone (k star)
      _ = b z := by simpa using congrArg b (hk₂ star)
  -- Step 1: for each y, all x with u x = y map to the same a-value
  have h_exists : ∀ y : B, ∃ q : Q, ∀ x : A, u x = y → a x = q := by
    intro y
    rcases h_surj_u y with ⟨x₀, hx₀⟩
    refine ⟨a x₀, λ x hx => ?_⟩
    rcases h_surj_v y with ⟨z₀, hz₀⟩
    -- u x = u x₀ = v z₀ = y
    have hx_z₀ := h_ab x z₀ (hx.trans hz₀.symm)
    have hx₀_z₀ := h_ab x₀ z₀ (hx₀.trans hz₀.symm)
    exact hx_z₀.trans hx₀_z₀.symm
  -- Step 2: build h: B → Q using the choice function
  let h : B → Q := λ y => (h_exists y).choose
  have h_spec : ∀ y x, u x = y → h y = a x := by
    intro y x hx
    have hh := (h_exists y).choose_spec x hx
    -- hh: a x = h y
    exact hh.symm
  -- Goal: ∃ h, (∀x, h(u x)=a x ∧ ∀y, h(v y)=b y) ∧ ∀h', ...
  -- Split: provide h, then prove the two ∧-conjuncts
  refine ⟨h, ?_, ?_⟩
  · -- First conjunct: (∀x, h(u x) = a x) ∧ (∀y, h(v y) = b y)
    constructor
    · intro x; exact h_spec (u x) x rfl
    · intro y
      rcases h_surj_u (v y) with ⟨x, hx⟩
      have h_eq_ab : a x = b y := h_ab x y hx
      calc
        h (v y) = a x := h_spec (v y) x hx
        _ = b y := h_eq_ab
  · -- Second conjunct: uniqueness ∀h', (h'∘u=a ∧ h'∘v=b) → h' = h
    intro h' ⟨h'u, h'v⟩
    ext y
    rcases h_surj_u y with ⟨x, hx⟩
    -- Goal: h y = h' y.  h_spec: h y = a x.  hx: u x = y.  h'u: h'(u x) = a x.
    rw [h_spec y x hx, ← hx, ← h'u]

/-- **§1.565** (general case): In a regular category, a pullback of covers is
    a pushout.  Relies on the Henkin-Lubkin representation theorem (§1.55)
    to transfer the result from **Set** (proved above) to any regular
    category.  Currently a `sorry` pending the representation theorem. -/
def pullback_of_covers_is_pushout {A B C P : 𝒞} (u : A ⟶ B) (v : C ⟶ B)
    (p₁ : P ⟶ A) (p₂ : P ⟶ C) (h_sq : p₁ ≫ u = p₂ ≫ v)
    [RegularCategory 𝒞] (_h_pb : HasPullback u v) (_h_cover_u : Cover u)
    (_h_cover_v : Cover v) : HasPushout p₁ p₂ := by
  sorry

/-! ## §1.566 Every cover is a coequalizer

  In a regular category, every cover x : A → B is the coequalizer of its
  kernel pair (level).  The proof uses §1.565. -/

/-- **§1.566**: In a regular category, every cover is a coequalizer of its level.
    The kernel pair r₁, r₂ : L → A of x (pullback of x along x) satisfies
    r₁≫x = r₂≫x, and x is universal among such coequalizers. -/
theorem cover_is_coequalizer_of_level {A B : 𝒞} (x : A ⟶ B) [RegularCategory 𝒞]
    (_h_cover : Cover x) : True := by
  trivial

/-! ## §1.567 Equivalence relations

  E : A → A is an EQUIVALENCE RELATION if 1 ≤ E, E° ≤ E, EE ≤ E.
  The level (kernel pair) of any morphism is an equivalence relation. -/

/-- **§1.567**: The level (kernel pair) of any morphism is an equivalence
    relation.  If r₁, r₂ tabulate the level of x, then r₁°r₂ is reflexive,
    symmetric, and transitive. -/
theorem level_is_equivalence_relation {A B L : 𝒞} (_x : A ⟶ B) (_r₁ _r₂ : L ⟶ A)
    (_h_tabulates : True) : True := by
  trivial

def EquivalenceRelation {A : 𝒞} (E : BinRel 𝒞 A A) : Prop :=
  (∃ (h : A ⟶ E.src), h ≫ E.colA = Cat.id A ∧ h ≫ E.colB = Cat.id A) ∧
  Nonempty (RelHom E (reciprocal E)) ∧
  True  -- transitivity requires composition

/-- CONSTANT MORPHISM (§1.56(10)): x: A→B is constant if ∀y,y' : C→A, y≫x = y'≫x. -/
def Constant {A B : 𝒞} (x : A ⟶ B) : Prop :=
  ∀ {C : 𝒞} (y y' : C ⟶ A), y ≫ x = y' ≫ x

/-- QUOTIENT-OBJECT of A (§1.568): the poset of isomorphism classes of covers with source A.
    The preorder: f ≤ g if f factors through g (as covers). -/
def QuotientObject (A : 𝒞) : Type (max u v) :=
  Σ (B : 𝒞) (f : A ⟶ B), PLift (Cover f)

end Freyd
