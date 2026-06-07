/-
  Freyd & Scedrov, *Categories and Allegories* §1.52  Regular categories,
  well-supported, well-pointed, capital.  §1.52–§1.525.

  RegularCategory: Cartesian + images + pullbacks transfer covers.
  PreRegular: Cartesian + pullbacks transfer covers (images optional).
  WellSupported (§1.522), WellPointed (§1.523), Capital (§1.525).
-/


import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45
import Fredy.S1_51


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.52 Regular and pre-regular categories

  A REGULAR CATEGORY is Cartesian with images where pullbacks transfer
  covers.  A PRE-REGULAR CATEGORY drops the images requirement. -/

/-- A regular category: Cartesian, has images, pullbacks transfer covers (§1.52). -/
class RegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞 where
  pullbacks_transfer_covers : ∀ {A B C D : 𝒞} (f : A ⟶ B) (g : C ⟶ B)
    (p₁ : D ⟶ A) (p₂ : D ⟶ C), Cover f → p₁ ≫ f = p₂ ≫ g → Cover p₂

/-- A pre-regular category: Cartesian, pullbacks transfer covers (§1.52). -/
class PreRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞 where
  pullbacks_transfer_covers : ∀ {A B C D : 𝒞} (f : A ⟶ B) (g : C ⟶ B)
    (p₁ : D ⟶ A) (p₂ : D ⟶ C), Cover f → p₁ ≫ f = p₂ ≫ g → Cover p₂

variable [HasTerminal 𝒞]

/-- A is WELL-SUPPORTED if A → 1 is a cover (§1.522). -/
def WellSupported (A : 𝒞) : Prop := Cover (term A)

/-- A is WELL-POINTED (§1.523): the collection 1 → A jointly covers A.
    Every proper monic into A misses some point 1 → A. -/
def WellPointed (A : 𝒞) : Prop :=
  ∀ {D : 𝒞} (m : D ⟶ A), Mono m → ¬ IsIso m → ∃ (x : one ⟶ A), ¬ ∃ (y : one ⟶ D), y ≫ m = x

/-- Capital (§1.525): every well-supported object is well-pointed. -/
def Capital : Prop := ∀ (A : 𝒞), WellSupported A → WellPointed A

/-! ## Kernel-pair lemmas (requires products and pullbacks too) -/

variable [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

section
variable (S : 𝒞)

def _pb : HasPullback (term S) (term S) := hpull.has (term S) (term S)

def _kpCone : Cone (term S) (term S) := ⟨_, kp₁ (f:=term S), kp₂ (f:=term S), kp_sq⟩
def _prodCone : Cone (term S) (term S) := ⟨_, fst, snd, term_uniq _ _⟩

/-- kpProdIso : kernelPair(term S) → S×S via product universal property;
    kpProdInv in the other direction via pullback lift. -/
def kpProdIso : kernelPair (term S) ⟶ prod S S :=
  pair (kp₁ (f:=term S)) (kp₂ (f:=term S))

def kpProdInv : prod S S ⟶ kernelPair (term S) := (_pb S).lift (_prodCone S)

@[simp] theorem kpProdIso_fst : kpProdIso S ≫ fst = kp₁ (f:=term S) := fst_pair _ _
@[simp] theorem kpProdIso_snd : kpProdIso S ≫ snd = kp₂ (f:=term S) := snd_pair _ _
@[simp] theorem kpProdInv_fst : kpProdInv S ≫ kp₁ (f:=term S) = fst := (_pb S).lift_fst (_prodCone S)
@[simp] theorem kpProdInv_snd : kpProdInv S ≫ kp₂ (f:=term S) = snd := (_pb S).lift_snd (_prodCone S)

theorem kpProdIso_inv : kpProdIso S ≫ kpProdInv S = Cat.id (kernelPair (term S)) := by
  let u := kpProdIso S ≫ kpProdInv S
  have hu_fst : u ≫ kp₁ (f:=term S) = kp₁ (f:=term S) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_fst, kpProdIso_fst]
  have hu_snd : u ≫ kp₂ (f:=term S) = kp₂ (f:=term S) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_snd, kpProdIso_snd]
  have h_id_lift : (_pb S).lift (_kpCone S) = Cat.id (kernelPair (term S)) :=
    ((_pb S).lift_uniq (_kpCone S) (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm
  calc
    u = (_pb S).lift (_kpCone S) :=
      (_pb S).lift_uniq (_kpCone S) u hu_fst hu_snd
    _ = Cat.id (kernelPair (term S)) := h_id_lift

theorem kpProdInv_iso : kpProdInv S ≫ kpProdIso S = Cat.id (prod S S) := by
  have h := pair_uniq fst snd (kpProdInv S ≫ kpProdIso S)
    (by rw [Cat.assoc, kpProdIso_fst, kpProdInv_fst])
    (by rw [Cat.assoc, kpProdIso_snd, kpProdInv_snd])
  have hid : pair fst snd = Cat.id (prod S S) :=
    (pair_uniq fst snd (Cat.id (prod S S)) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])).symm
  rw [h, hid]

theorem kpProdIso_isIso : IsIso (kpProdIso S) :=
  ⟨kpProdInv S, kpProdIso_inv S, kpProdInv_iso S⟩

theorem kpProdInv_isIso : IsIso (kpProdInv S) :=
  ⟨kpProdIso S, kpProdInv_iso S, kpProdIso_inv S⟩

theorem kp_diag_prod : kp_diag (f:=term S) ≫ kpProdIso S = diag S := by
  let h := kp_diag (f:=term S) ≫ kpProdIso S
  have hfst : h ≫ fst = Cat.id S := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_fst, kp_diag_p₁]
  have hsnd : h ≫ snd = Cat.id S := by
    dsimp [h]; rw [Cat.assoc, kpProdIso_snd, kp_diag_p₂]
  have h_eq := pair_uniq (Cat.id S) (Cat.id S) h hfst hsnd
  simpa [h, diag] using h_eq

theorem wellSupported_prod_self (S : 𝒞) (hws : WellSupported S) : WellSupported (prod S S) := by
  intro C m g hm hgm
  have h_diag_term : diag S ≫ term (prod S S) = term S := term_uniq _ _
  have h_factor : (diag S ≫ g) ≫ m = term S := by
    rw [Cat.assoc, hgm, h_diag_term]
  exact hws m (diag S ≫ g) hm h_factor

end

/-- §1.525: in a capital category the terminator is projective.
    Every well-supported A has a point 1 → A. -/
theorem capital_implies_one_projective
    (hcap : Capital (𝒞 := 𝒞)) (A : 𝒞) (hws : WellSupported A) :
    Nonempty (one ⟶ A) := by
  -- 1. If A → 1 is iso, use the inverse.
  by_cases hiso : IsIso (term A)
  · obtain ⟨inv, _, _⟩ := hiso
    exact Nonempty.intro inv
  · -- 2. A → 1 is a cover but not iso.  By monic-cover-iso (1.512), it is not monic.
    have h_not_monic : ¬ Mono (term A) := by
      intro hm
      apply hiso
      exact monic_cover_iso (term A) hws hm
    -- 3. Hence kp_diag(term A) is not iso (1.453: monic_iff_kp_diag_iso).
    --    Via kpProdIso, diag A is also not iso — a proper monic.
    have h_not_iso_kp : ¬ IsIso (kp_diag (f:=term A)) :=
      mt ((monic_iff_kp_diag_iso (f:=term A)).mpr) h_not_monic
    have h_not_iso_diag : ¬ IsIso (diag A) := by
      intro hiso_diag; apply h_not_iso_kp
      have hkp : kp_diag (f:=term A) = diag A ≫ kpProdInv A := by
        rw [← kp_diag_prod A, Cat.assoc, kpProdIso_inv A, Cat.comp_id]
      rw [hkp]
      exact isIso_comp hiso_diag (kpProdInv_isIso A)
    have hm_diag : Mono (diag A) := diag_mono A
    -- 4. A×A is well-supported — via the diagonal, no pullbacks needed.
    have hwsAA : WellSupported (prod A A) := wellSupported_prod_self A hws
    -- 5. By capital, A×A is well-pointed.
    have hwpAA : WellPointed (prod A A) := hcap (prod A A) hwsAA
    -- 6. Apply well-pointed to the proper monic Δ : ∃ x:1→A×A.
    obtain ⟨x, _⟩ := hwpAA (diag A) hm_diag h_not_iso_diag
    -- 7. Compose x with π₁ : 1 → A.
    exact Nonempty.intro (x ≫ fst)
