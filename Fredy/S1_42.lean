/-
  Freyd & Scedrov, *Categories and Allegories* §1.42  Finite products.

  HasTerminal (§1.421): the terminator 1 with unique map from every object.
  HasBinaryProducts (§1.423): binary products with projections and pairing.
  Diagonal: diag A = ⟨id, id⟩ : A → A×A.
-/

import Fredy.S1_1
import Fredy.S1_41

set_option linter.unusedSectionVars false

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

class HasTerminal (𝒞 : Type u) [Cat.{v} 𝒞] where
  one   : 𝒞
  trm   : (X : 𝒞) → X ⟶ one
  uniq  : ∀ {X : 𝒞} (f g : X ⟶ one), f = g

variable [ht : HasTerminal 𝒞]

def one : 𝒞 := ht.one
def term (X : 𝒞) : X ⟶ one := ht.trm X

theorem term_uniq {X : 𝒞} (f g : X ⟶ one) : f = g := ht.uniq f g

class HasBinaryProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  prod  : 𝒞 → 𝒞 → 𝒞
  fst   : {A B : 𝒞} → prod A B ⟶ A
  snd   : {A B : 𝒞} → prod A B ⟶ B
  pair  : {X A B : 𝒞} → (X ⟶ A) → (X ⟶ B) → (X ⟶ prod A B)
  fst_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ fst = f
  snd_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ snd = g
  pair_uniq : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B),
    h ≫ fst = f → h ≫ snd = g → h = pair f g

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

theorem diag_mono (A : 𝒞) : Mono (diag A) := by
  intro W f g h
  have hfst : f ≫ (diag A ≫ fst) = g ≫ (diag A ≫ fst) := by
    rw [← Cat.assoc, ← Cat.assoc, h]
  rw [diag_fst, Cat.comp_id, Cat.comp_id] at hfst
  exact hfst
