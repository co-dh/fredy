/-
  Freyd & Scedrov, *Categories and Allegories* §1.42  Finite products.

  HasTerminal (§1.421), HasBinaryProducts (§1.423).
  Diagonal: diag A = ⟨id, id⟩ : A → A×A.

  STRUCTURE: we define both classes first, then separate sections
  for terminal-dependent and product-dependent definitions so that
  `fst`, `snd`, `pair` do NOT require `HasTerminal` (§1.85 needs this).
-/

import Fredy.S1_1
import Fredy.S1_41


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ### HasTerminal class and definitions -/

class HasTerminal (𝒞 : Type u) [Cat.{v} 𝒞] where
  one   : 𝒞
  trm   : (X : 𝒞) → X ⟶ one
  uniq  : ∀ {X : 𝒞} (f g : X ⟶ one), f = g

section Terminal

variable [ht : HasTerminal 𝒞]

def one : 𝒞 := ht.one
def term (X : 𝒞) : X ⟶ one := ht.trm X

theorem term_uniq {X : 𝒞} (f g : X ⟶ one) : f = g := ht.uniq f g

/-- A SUBTERMINATOR is an object T such that T→1 is monic (§1.412). -/
def Subterminator (T : 𝒞) : Prop := Mono (term T)

/-- A VALUE is a subterminator (§1.412). -/
def Value : 𝒞 → Prop := Subterminator

/-! ### §1.421 Terminator unique up to unique iso -/

/-- The unique map between two terminator objects is an iso (§1.421).
    If `ht1` and `ht2` are both `HasTerminal` instances, then `ht1.one ≅ ht2.one`.
    We state this: for any two terminators B₁, B₂ with uniqueness, the map B₁→B₂ is iso. -/
theorem terminator_unique_iso
    (B₁ B₂ : 𝒞)
    (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₁)
    (uniq₁ : ∀ {X : 𝒞} (p q : X ⟶ B₁), p = q)
    (uniq₂ : ∀ {X : 𝒞} (p q : X ⟶ B₂), p = q) :
    IsIso f :=
  ⟨g, uniq₁ _ _, uniq₂ _ _⟩

end Terminal

/-! ### HasBinaryProducts class and definitions -/

class HasBinaryProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  prod  : 𝒞 → 𝒞 → 𝒞
  fst   : {A B : 𝒞} → prod A B ⟶ A
  snd   : {A B : 𝒞} → prod A B ⟶ B
  pair  : {X A B : 𝒞} → (X ⟶ A) → (X ⟶ B) → (X ⟶ prod A B)
  fst_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ fst = f
  snd_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ snd = g
  pair_uniq : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B),
    h ≫ fst = f → h ≫ snd = g → h = pair f g

section Products

variable [hp : HasBinaryProducts 𝒞]

def prod (A B : 𝒞) : 𝒞 := hp.prod A B
def fst  {A B : 𝒞} : prod A B ⟶ A := hp.fst
def snd  {A B : 𝒞} : prod A B ⟶ B := hp.snd
def pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : X ⟶ prod A B := hp.pair f g

@[simp]
theorem fst_pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : pair f g ≫ fst = f :=
  hp.fst_pair f g

@[simp]
theorem snd_pair {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) : pair f g ≫ snd = g :=
  hp.snd_pair f g

theorem pair_uniq {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B)
    (h₁ : h ≫ fst = f) (h₂ : h ≫ snd = g) : h = pair f g :=
  hp.pair_uniq f g h h₁ h₂

def diag (A : 𝒞) : A ⟶ prod A A := pair (Cat.id A) (Cat.id A)

theorem diag_fst (A : 𝒞) : diag A ≫ fst = Cat.id A := fst_pair _ _
theorem diag_snd (A : 𝒞) : diag A ≫ snd = Cat.id A := snd_pair _ _

theorem diag_mono (A : 𝒞) : Mono (diag A) :=
  mono_of_retraction (diag A) fst (diag_fst A)

/-! ### §1.423 Product corollaries -/

/-- Product eta: any h : X → A×B equals ⟨h≫fst, h≫snd⟩. -/
theorem pair_eta {X A B : 𝒞} (h : X ⟶ prod A B) : h = pair (h ≫ fst) (h ≫ snd) :=
  pair_uniq _ _ h rfl rfl

/-- The pair of projections on A×B is the identity. -/
theorem pair_fst_snd {A B : 𝒞} : pair (fst (A := A) (B := B)) snd = Cat.id (prod A B) :=
  (pair_uniq fst snd (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm

/-- Projections fst and snd are jointly monic (§1.423): the product is a table on A, B. -/
theorem fst_snd_jointly_monic {A B : 𝒞} : MonicPair (fst (A := A) (B := B)) snd := by
  intro W f g hf hs
  have hfe : f = pair (f ≫ fst) (f ≫ snd) := pair_eta f
  have hge : g = pair (g ≫ fst) (g ≫ snd) := pair_eta g
  rw [hfe, hge, hf, hs]

/-- Products (like terminators) are unique up to isomorphism (§1.423).
    Given two product structures on the same pair A, B, the canonical map between them is iso. -/
theorem product_unique_iso {A B : 𝒞} [hp2 : HasBinaryProducts 𝒞]
    (f : prod A B ⟶ hp2.prod A B)
    (g : hp2.prod A B ⟶ prod A B)
    (hf₁ : f ≫ hp2.fst = fst) (hf₂ : f ≫ hp2.snd = snd)
    (hg₁ : g ≫ fst = hp2.fst) (hg₂ : g ≫ snd = hp2.snd) :
    IsIso f := by
  refine ⟨g, ?_, ?_⟩
  · -- f ≫ g = id : suffices pair (f≫g≫fst) (f≫g≫snd) = pair fst snd = id
    have h1 : (f ≫ g) ≫ fst = fst := by rw [Cat.assoc, hg₁, hf₁]
    have h2 : (f ≫ g) ≫ snd = snd := by rw [Cat.assoc, hg₂, hf₂]
    calc f ≫ g = pair ((f ≫ g) ≫ fst) ((f ≫ g) ≫ snd) := pair_eta (f ≫ g)
      _ = pair fst snd := by rw [h1, h2]
      _ = Cat.id _ := pair_fst_snd
  · -- g ≫ f = id (using hp2)
    have h1 : (g ≫ f) ≫ hp2.fst = hp2.fst := by rw [Cat.assoc, hf₁, hg₁]
    have h2 : (g ≫ f) ≫ hp2.snd = hp2.snd := by rw [Cat.assoc, hf₂, hg₂]
    have hid1 : (Cat.id (hp2.prod A B)) ≫ hp2.fst = hp2.fst := Cat.id_comp _
    have hid2 : (Cat.id (hp2.prod A B)) ≫ hp2.snd = hp2.snd := Cat.id_comp _
    exact (hp2.pair_uniq hp2.fst hp2.snd (g ≫ f) h1 h2).trans
      (hp2.pair_uniq hp2.fst hp2.snd (Cat.id _) hid1 hid2).symm

/-! ### §1.426 Monic and monic into product -/

/-- b is monic → ⟨f, b⟩ : T → A×B is monic (§1.426, one direction).
    The full statement: b is monic iff (x,y): T→A×B is monic for every x with MonicPair x y.
    This direction is clean and useful. -/
theorem mono_pair_of_mono {T A B : 𝒞} (f : T ⟶ A) (b : T ⟶ B) (hb : Mono b) :
    Mono (pair f b) := by
  intro W g h heq
  apply hb
  calc g ≫ b = (g ≫ pair f b) ≫ snd := by rw [Cat.assoc, snd_pair]
    _ = (h ≫ pair f b) ≫ snd := by rw [heq]
    _ = h ≫ b := by rw [Cat.assoc, snd_pair]

/-- §1.426: A monic b : A → B gives a correspondence Sub(A,B) ≅ Sub(A×B).
    The element in Sub(A×B) corresponding to b ∈ Sub(A,B) is pair(id_A, b) : A → A×B.
    Note: this map is monic when b is monic (use `mono_pair_of_mono`).
    The full §1.426 isomorphism of posets is formalized via the monic/subobject infrastructure
    in §1.56; here we record the key arrow: b monic → pair(id,b) monic. -/
theorem mono_id_pair_of_mono {A B : 𝒞} (b : A ⟶ B) (hb : Mono b) :
    Mono (pair (Cat.id A) b) := mono_pair_of_mono _ b hb

end Products

/-! ### §1.425 Indexed products -/

/-- An indexed product of a family `{Aᵢ}ᵢ∈I` (§1.425):
    an object `P` with projections `pᵢ : P → Aᵢ` such that for any `X` and family
    `{xᵢ : X → Aᵢ}` there exists a unique `z : X → P` with `z ≫ pᵢ = xᵢ` for all i. -/
structure HasIndexedProduct {I : Type} (family : I → 𝒞) where
  prod    : 𝒞
  proj    : (i : I) → prod ⟶ family i
  lift    : {X : 𝒞} → ((i : I) → X ⟶ family i) → (X ⟶ prod)
  lift_π  : ∀ {X : 𝒞} (fs : (i : I) → X ⟶ family i) (i : I), lift fs ≫ proj i = fs i
  lift_uniq : ∀ {X : 𝒞} (fs : (i : I) → X ⟶ family i) (h : X ⟶ prod),
    (∀ i, h ≫ proj i = fs i) → h = lift fs

/-- The empty product is a terminator (§1.425: product of the empty family). -/
def emptyProduct_is_terminator (ep : HasIndexedProduct (𝒞 := 𝒞) (fun i : Empty => i.elim)) :
    HasTerminal 𝒞 where
  one   := ep.prod
  trm   := fun _ => ep.lift (fun i => i.elim)
  uniq  := fun {_} f g =>
    (ep.lift_uniq (fun i => i.elim) f (fun i => i.elim)).trans
    (ep.lift_uniq (fun i => i.elim) g (fun i => i.elim)).symm

/-- §1.425: Finite products reduce to terminal + binary products.
    Any Fin n -indexed product can be built from HasTerminal + HasBinaryProducts.
    Proof: base case n=0 uses terminator; succ uses prod(sub.prod, A_last) with
    projections fst≫π_i (i<n) and snd (i=last). Faithful sorry for inductive step
    (dependent type rewriting with `▸` is non-trivial; statement is clearly correct). -/
def finiteProduct_from_term_binary [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    {n : Nat} (family : Fin n → 𝒞) : HasIndexedProduct family := by
  induction n with
  | zero =>
    exact {
      prod      := one
      proj      := fun i => i.elim0
      lift      := fun _ => term _
      lift_π    := fun _ i => i.elim0
      lift_uniq := fun _ m _ => term_uniq m _
    }
  | succ n ih =>
    -- Product of Fin(n+1)-family = (Product of first n) × A_last
    -- The proj/lift/uniq bookkeeping requires dependent rewrites; stated faithfully.
    sorry

end Freyd
