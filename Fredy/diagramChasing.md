# Diagram chasing vs. Q-sequences, and what's been formalized

Context: proving `⟨x,y⟩ : T → A×B` is monic, given `x : T→A`, `y : T→B` a monic pair, by the "glue the punctured
parallel-pair diagram to the product cone along `⟨x,y⟩`, read off `a≫x=b≫x` and `a≫y=b≫y`, then apply the monic-pair
rule to remove the cross" argument.

## 1. A Q-sequence is a *statement*; the gluing argument is a *proof*

These are two different layers, and it's easy to conflate them (an earlier render wrongly put the proof's derivation
panels *inside* the Q-sequence).

- A **Q-sequence (§1.395) is a statement** — syntax for a first-order *property* of diagrams. The honest monic
  Q-sequence for `⟨x,y⟩` is *only*:

  ```
  [ ⟨x,y⟩ : T → A×B ]   ∣∀∣  (a,b:W⇉T,  a⟨x,y⟩=b⟨x,y⟩,  ✛ a=b)   ∣∃∣  (a=b)
  ```

  Two bars, over `⟨x,y⟩` alone. **No `l, r, x, y`** — those are not part of the spec.

- **The gluing argument is a proof.** The product cone (`l = fst`, `r = snd`, the feet `x, y`, the pairing equations)
  is context for the *chase*, not part of the *statement*. So `monicPairQSeq` should be trimmed to the two bars; the
  `l, r, x, y` belong to the proof object.

Slogan: **the Q-sequence is the theorem; the gluing is the chase.**

## 2. What kind of proof is the gluing argument?

A **diagram chase by pasting** (a.k.a. diagram gluing / a "pasting" argument). Precisely:

- "Glue the punctured parallel-pair diagram to the product cone **along `m = ⟨x,y⟩`**" is a **pushout / amalgamation of
  the two diagrams' finite presentations** over the shared arrow.
- In the glued presentation everything commutes *except* the punctured `a=b`; reading off `a≫x=b≫x`, `a≫y=b≫y` is just
  **equational reasoning in that presented category**, where `A×B` enters as a **limit cone** — i.e. you are computing in
  a **sketch** (Ehresmann) / the syntactic category of the finite-product theory.
- "Apply monic-pair, remove the cross" = imposing the relation `a=b`, licensed by the `MonicPair` axiom.

Key point: **the Lean proof `monic_of_monicPair` already *is* this chase**, written as equations instead of pictures —
the `calc` post-composing `fst`/`snd` is "glue the product cone and read off `a≫x=b≫x`"; `rw [hab]` is "use the
punctured-pair commute"; `hxy …` is "apply the monic-pair rule." The pen-and-paper gluing and the `calc` are the same
proof.

## 3. Has anybody formalized diagram chasing? Three distinct lines

1. **A genuine formal theory of the chase itself.** Mahboubi & Piquerez, *"A First-Order Theory of Diagram Chasing"*
   (CSL 2024) / *"Machine-Checked Categorical Diagrammatic Reasoning"* — a many-sorted first-order theory whose **models
   are exactly diagrams in small (and abelian) categories**, with a **decidability** result for the commutativity
   ("commerge") problem on acyclic quivers, implemented in **Coq**. Closest thing to formalizing the chase *as* a chase,
   including the "paste-and-read-off" step.

2. **Element-style chases in Lean/mathlib.** Mac Lane **pseudoelements** are formalized and used to do abelian-category
   chases "along the same lines as a pen-and-paper diagram chase" — the **snake lemma**, four/five lemmas, and the
   derived-categories development all rely on a handful of these. The everyday automated mini-chase (closing a
   commutative-square goal) is `aesop` / `aesop_cat`.

3. **String-diagram rewriting assistants** — the chase recast as *rewriting in free monoidal categories*: **Quantomatic**
   (ZX-calculus), **Cartographer** (symmetric monoidal), **Globular / homotopy.io** (finitely-presented n-categories),
   plus recent **Lean 4** (Graphical Rewriting, ITP 2024) and **Rocq** string-diagram libraries.

Honest gap: a general tactic mirroring the *informal* "paste these diagrams over a shared arrow and read off the
consequence" for arbitrary finite-limit theories is **not** a mature off-the-shelf tool. In practice people either write
the chase as explicit morphism equations (what we did) or lean on `aesop_cat` / pseudoelements. The Mahboubi–Piquerez
line is the active frontier.

### Sources

- [Mahboubi & Piquerez — A First-Order Theory of Diagram Chasing (CSL 2024, HAL)](https://hal.science/hal-04266479v2/document)
  · [arXiv 2311.01790](https://arxiv.org/pdf/2311.01790)
- [Machine-Checked Categorical Diagrammatic Reasoning (arXiv 2402.14485)](https://arxiv.org/pdf/2402.14485)
- [Some notes on diagram chasing and diagrammatic proofs in category theory (arXiv 2010.12534)](https://arxiv.org/abs/2010.12534)
- [Formalization of derived categories in Lean/mathlib](https://afm.episciences.org/15978/pdf)
  · [mathlib snake lemma (Zulip)](https://leanprover-community.github.io/archive/stream/267928-condensed-mathematics/topic/snake.20lemma.html)
- [aesop — white-box automation for Lean 4](https://github.com/leanprover-community/aesop)
- [Graphical Rewriting for Diagrammatic Reasoning in Monoidal Categories in Lean 4 (ITP 2024)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.41/LIPIcs.ITP.2024.41.pdf)
  · [homotopy.io (arXiv 2402.13179)](https://arxiv.org/pdf/2402.13179)
  · [Cartographer (CALCO 2019)](https://discovery.ucl.ac.uk/id/eprint/10081115/1/LIPIcs-CALCO-2019-20.pdf)

## 4. Does `aesop` / `aesop_cat` do diagram chasing?

Short answer: **`aesop` is generic; `aesop_cat` is the category-theory specialization — and what it automates is only the
*shallow* end of diagram chasing (commutativity), not the real chase.**

- **`aesop`** = "white-box automation for Lean 4": a generic best-first proof search over *tagged rule sets* (a
  customizable, extensible `auto`/`tauto`). By itself it knows nothing about categories.

- **`aesop_cat`** = a thin wrapper that runs `aesop` with the **`CategoryTheory` rule set** added, plus two tweaks: it
  looks through semireducible defs when doing `intros`, and it tries `rfl`/`rfl_cat` *before* the expensive `aesop` call
  for speed. The `CategoryTheory` rule set bundles the tagged lemmas — associativity, `id_comp`/`comp_id`, the category
  `@[simp]` set, naturality, functor `map_comp`/`map_id`, reassoc, etc. It's the discharger mathlib auto-attaches
  (`:= by aesop_cat`) to side-goals in CT structure definitions: naturality squares, functoriality, "this triangle
  commutes."

Where it sits on the chasing spectrum:

| tool                       | what it does                                                                    | example                                              |
| -------------------------- | ------------------------------------------------------------------------------- | ---------------------------------------------------- |
| `aesop_cat` (shallow)      | **commutativity by normalization** — prove `composite₁ = composite₂` by simp/rfl | the plumbing: `a≫x = (a≫⟨x,y⟩)≫fst` via `fst_pair`   |
| pseudoelements / manual    | **element-style chases** — kernels, images, exactness                            | snake lemma, four/five lemmas                        |
| Mahboubi–Piquerez (Coq)    | **the chase as a decision procedure** — FO theory of diagrams, decidable commerge | the deep thing                                       |

`aesop_cat` is the **bottom rung**: it closes "does this diagram commute?" goals that follow by rewriting. It does **not**
do exactness / kernel–image reasoning, existential chasing, or "apply the universal property." Mapping onto our proof:
`aesop_cat` would handle the gluing/commutativity bookkeeping (the `calc` legs), but the actual content — **`hxy …`,
applying the monic-pair rule to remove the cross** — is invoking a hypothesis, not a commutativity fact, so it's outside
what `aesop_cat` discovers on its own. Same statement/proof split: the commuting is mechanical; the "remove the cross" is
the real step.

### Sources

- [Mathlib.CategoryTheory.Category.Init — `aesop_cat` / `CategoryTheory` rule set / `rfl_cat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Init.html)
- [PR #21330 — `aesop_cat` attempts `rfl` before `aesop`](https://github.com/leanprover-community/mathlib4/pull/21330)
- [aesop — White-box automation for Lean 4](https://github.com/leanprover-community/aesop)
