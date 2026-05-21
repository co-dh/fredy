# Freyd & Scedrov, *Categories, Allegories* — §1.49 and surroundings

Transcribed from photos of pages 54–55 (Chapter I, §1.4 Cartesian Categories).

---

## 1.49. τ-Categories

For the definition of τ-categories we will need two technical definitions.

### Short column

Given a table ⟨T; x₁, …, xₙ⟩ we say that xⱼ is a **SHORT COLUMN** if for
every f, g : X → T such that f xⱼ ≠ g xⱼ, there exists i < j such that
f xᵢ ≠ g xᵢ. (Equivalently: ⟨x₁, …, xⱼ₋₁⟩ is *as monic as* ⟨x₁, …, xⱼ₋₁, xⱼ⟩.)

Borrowing from the notation conventionally used in exterior algebra, we
use ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ to denote the family obtained by deleting xⱼ.
If xⱼ is a short column, then ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ is still a table.
But notice that just because ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ is still a table does
not imply that xⱼ is short column. (For any f : A → B, ⟨A; f, 1⟩ and
⟨A; f̂, 1⟩ are tables but f need not be short.)

### Composition of tables

Given tables ⟨T; x₁, …, xₘ⟩ and ⟨T'; y₁, …, yₙ⟩ where T' = xⱼ□ we define
their **COMPOSITION at j** as

  ⟨T; x₁, …, xₘ⟩ ∘ⱼ ⟨T'; y₁, …, yₙ⟩
  = ⟨T; x₁, …, xⱼ₋₁, xⱼy₁, …, xⱼyₙ, xⱼ₊₁, …, xₘ⟩.

(Note Freyd's notation: xⱼ□ means the codomain of xⱼ.)

---

## 1.491. τ-CATEGORY

A **τ-CATEGORY** is a cartesian category with a distinguished class of
tables, denoted here as τ, such that:

- **τ1.** Every table is isomorphic to a unique table in τ.
- **τ2.1.** ⟨T; 1_T⟩ ∈ τ, all T.
- **τ2.2.** If ⟨T; x₁, …, xₘ⟩ ∈ τ and ⟨T'; y₁, …, yₙ⟩ ∈ τ and T' = xⱼ□,
  then ⟨T; x₁, …, xₘ⟩ ∘ⱼ ⟨T'; y₁, …, yₙ⟩ ∈ τ.
- **τ3.** If ⟨T; x₁, …, xₙ⟩ ∈ τ and xⱼ is a short column, then
  ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ ∈ τ.

Axiom 1 says that τ is a set of representatives, 2 that it is closed
under the operations of "composition", 3 that it is closed under the
operations of pruning short columns.

---

## 1.492. Supporting and pruning

Given a table ⟨T; x₁, …, xₙ⟩, we will say that a subsequence i₁, …, iₘ
is **SUPPORTING** if ⟨T; xᵢ₁, …, xᵢₘ⟩ still satisfies the monic condition,
and we will call the latter table a **PRUNE** of the original. Note that
one can prune other than short columns.

---

## 1.493. The generic example

An example of a τ-category — and as we will see, a generic example — is
the category of ordinal lists, which will here be described as the
category whose objects are von Neumann ordinals and whose morphisms are
all functions. We define τ to be the class of tables ⟨T; f₁, …, fₙ⟩ such
that for x, y ∈ T and j = min{i | fᵢ(x) ≠ fᵢ(y)} it is the case that
fⱼ(x) < fⱼ(y).

We can easily restrict to any initial section or ordinals closed under
ordinal multiplication. Two cases will be of particular interest: **F**
the finite ordinals and **P** the ω-polynomials (i.e., those less than
ω^ω).

---

## 1.494. Resurfacing

**Axiom 1** says that for any table ⟨T; x₁, …, xₙ⟩ there exists a unique
isomorphism g : T' → T such that ⟨T'; gx₁, …, gxₙ⟩ ∈ τ. We will call g
the **RESURFACING** of ⟨T; x₁, …, xₙ⟩. A table is in τ iff its
resurfacing is an identity map.

A more algebraic definition of τ-structure is available by taking a
sequence of partial operations τ₀, τ₁, …, τₙ, …, where τₙ assigns
resurfacings to tables of length n.

### One-column corollary

If f : A → B is an isomorphism, then the resurfacing of ⟨A; f⟩ is f⁻¹.
Hence the only isomorphisms that appear as one-column tables in τ are
identity maps.

### Converse of axiom 3

Axiom 3 yields its own converse: Suppose ⟨T; x₁, …, xₙ⟩ is a table with
resurfacing g : T' → T and with a short column xⱼ. Then
⟨T'; gx₁, …, ĝxⱼ, …, gxₙ⟩ ∈ τ. Hence g is also the resurfacing of
⟨T; x₁, …, x̂ⱼ, …, xₙ⟩. And thus

  ⟨T; x₁, …, xₙ⟩ ∈ τ  iff  ⟨T; x₁, …, x̂ⱼ, …, xₙ⟩ ∈ τ.

### Expansion corollary

A corollary is that any expansion of a τ-table is a τ-table: If
⟨T; x₁, …, xₙ⟩ ∈ τ, then for any xₙ₊₁ such that T = □xₙ₊₁ we have
⟨T; x₁, …, xₙ, xₙ₊₁⟩ ∈ τ. In particular, ⟨A; 1, f⟩ ∈ τ for any f : A → B.

---

## 1.495. Diversion: asymmetry of axiom 3

Axiom 3 is, of course, asymmetric. If we symmetrized it we would also
obtain for any f : A → B that ⟨A; f, 1⟩ ∈ τ. If f is an isomorphism,
then ⟨A; 1, f⟩ and ⟨B; f⁻¹, 1⟩ are isomorphic τ-tables and hence must be
the same. The twist-map on C × C, for any object C, is consequently the
identity map and the projections are equal, therefore C is a
subterminator. That is, a symmetrized axiom 3 occurs only when the
category is a semi-lattice.

---

## 1.496. Unique terminator

If T is a subterminator in a τ-category then ⟨T; f⟩ ∈ τ for any f : T → T'
(since f is short) and thus if f is an isomorphism it is an identity
map. Isomorphic subterminators are equal. In particular, there is a
unique terminator.

---

## 1.497. The Cancellation Lemma

If ⟨T; x₁, …, xₘ⟩ ∘ⱼ ⟨T'; y₁, …, yₙ⟩ ∈ τ and ⟨T'; y₁, …, yₙ⟩ ∈ τ, then
⟨T; x₁, …, xₘ⟩ ∈ τ.

**Because:** Let g : T'' → T be the resurfacing of ⟨T; x₁, …, xₘ⟩. By
axiom τ2.2, ⟨T''; gx₁, …, gxₘ⟩ ∘ⱼ ⟨T'; y₁, …, yₙ⟩ ∈ τ, which makes g the
resurfacing of ⟨T; x₁, …, xₘ⟩ ∘ⱼ ⟨T'; y₁, …, yₙ⟩. By assumption, the
latter is a τ-table, hence g = 1_T.

---

# Earlier definitions referenced

## Table

A **TABLE** is an object T together with a finite sequence of morphisms
x₁, …, xₙ all sharing source T. Each xᵢ : T → Aᵢ may have a different
codomain. Notation: ⟨T; x₁, …, xₙ⟩.

## Monic pair / monic family

A pair (or family) ⟨x₁, …, xₙ⟩ with common source T is **MONIC** (jointly
monic) if for all parallel f, g : X → T,

  (∀ i. f xᵢ = g xᵢ)  ⟹  f = g.

In set-theoretic terms: the induced map T → A₁ × ⋯ × Aₙ is injective,
i.e., no two distinct rows of the table are equal.

## "As monic as"

⟨x₁, …, xₘ⟩ is **AS MONIC AS** ⟨y₁, …, yₙ⟩ if every parallel pair
distinguished by the second family is already distinguished by the first.

## Notational convention

Freyd composes left-to-right: x f means "x first, then f". For
xᵢ : T → Aᵢ and f : X → T, the composite f xᵢ : X → Aᵢ means
"apply f then xᵢ".

Lowercase letters are morphisms, uppercase are objects.
□x = domain of x, x□ = codomain of x.
x̂ⱼ means "omit xⱼ from the list" (exterior-algebra notation).
