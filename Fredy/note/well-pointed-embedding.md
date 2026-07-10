# Well-pointed objects, capitalization, and why Yoneda isn't enough

Conceptual notes spanning Freyd §1.523 (well-pointed), §1.525 (capital), §1.54 (capitalization),
and the comparison with the Yoneda embedding. Q&A distilled from a discussion.

## 0. Support (§1.522): the image of `A→1`

The **support** `𝒮pt(A)` is the **image of the unique map `A→1`** — always a **subobject of `1`**. `A` is
**well-supported** if `𝒮pt(A) = 1`; equivalently (pre-regular) `A→1` is a **cover**. Not well-supported
⟺ `A→1` factors through a *proper* subobject `U ⊊ 1` (§1.534: `A → U ↣ 1`).

Support lives among the **subobjects of `1`** (the "truth values" / support lattice). How many there are
controls how interesting the notion is:

| Category   | Subobjects of `1`   | `𝒮pt(A)` is…                | Not well-supported ⟺                 | Example                              |
|---         |---                  |---                          |---                                   |---                                   |
| Set        | just `∅`, `{∗}`     | `1` if `A≠∅`, else `∅`      | `A = ∅`                              | **`∅` — the unique one in Set**      |
| `Set/I`    | subsets of `I`      | image `p(A) ⊆ I` of `p:A→I` | `p` misses some `i∈I` (empty fiber)  | `I={0,1}`, `{∗}↦0`: support `{0}⊊I`  |
| `Sh(X)`    | open sets of `X`    | open set where sheaf ≠ ∅    | sheaf supported on proper open `U⊊X` | extend-by-∅ off `U`                  |

**Set picture** (`1 = {∗}` has only two subobjects):
```
A ≠ ∅  →  A→1 surjective  →  image = 1   →  well-supported
A = ∅  →  ∅→1 image = ∅ ⊊ 1              →  NOT well-supported
```
`∅` is also the *initial* object — being initial is *why* its image in `1` is the empty subobject. (No
zero object is involved: in Set initial `∅ ≠ {∗}` terminal.)

**Why it matters (ties to capitalization).** §1.534: if `B` is *not* well-supported (`B→U↣1`, `U⊊1`),
then `B×U → B×1` is already iso, so `Δ : A→A/B` collapses `U` with `1` and is **not faithful**. Hence
capitalization only ever slices over **well-supported** `B` (§1.533: `Δ` faithful ⟺ `B` well-supported).
In Set: "slice over nonempty `B`, never over `∅`." Well-supported is also the hypothesis of *capital*
(§1.525: every well-supported object is well-pointed) — see §1 below.

## 1. Well-pointed (§1.523)

`A` is **well-pointed** if the global points `1 → A` **jointly cover** `A`: the only subobject
containing every point `1 → A` is `A` itself. Elementary form: a mono `A′ ↣ A` through which *every*
point `1 → A` factors must be an isomorphism.

Set intuition: "`A` is covered by its elements" — nothing in `A` is invisible to the points.
(Distinct from but cousin to "1 is a separator" = `Hom(1,−)` faithful.)

## 2. Which categories are well-pointed

| Category               | WP?    | A point `1 → A` is…                    | Why / witness                                                                     |
|---                     |:--:    |---                                     |---                                                                                |
| Set, FinSet            | ✅ all | an element                             | a subset with every element *is* `A`. The canonical well-pointed topos.           |
| Grp                    | ❌     | hom from trivial group ⇒ identity only | zero object (`1≅0`); point lands in trivial subgroup. `ℤ/2`: only point hits `0`. |
| Ab, Vect_k, R-Mod, Mon | ❌     | the zero/identity element              | zero object ⇒ point blind to all but `0`.                                         |
| Set\* (pointed sets)   | ❌     | the basepoint                          | zero object = basepoint.                                                          |
| Ring/CRing (unital)    | ❌     | hom from zero ring ⇒ forces `1=0`      | nontrivial rings have **no points at all**.                                       |
| G-Set                  | ❌     | a **fixed point** (`g·a=a` ∀g)         | `A^G` rarely covers; free action has none. *A topos, yet not WP.*                 |
| Presheaves `Set^{Cᵒᵖ}` | ❌     | a **global section**                   | global sections miss local data.                                                  |
| Sheaves `Sh(X)`        | ❌     | a global section                       | non-constant sheaf's stalks unreached.                                            |

**Three ways to fail, one to succeed:**
1. **Zero object** (`1≅0`) → only point is identity/zero (Grp, Ab, Vect, Mod, Mon, Set\*).
2. **Terminal forces triviality** → nontrivial objects have *no* points (Ring).
3. **Points = invariant/global data** missing local structure (G-Set fixed points, sheaf/presheaf
   global sections).
Succeeds when points *are* the elements and elements separate everything: **Set** + well-pointed topoi.

## 3. "Set-like, and structure breaks it" — sharpened

The instinct (WP = Set-like; add structure, lose it) is right, with one correction: it's not *any*
structure — it's structure that **constrains maps out of `1`** so points stop reaching every element.
In Set, `1` is a *bare* point (maps anywhere). Structure replaces `1` with a *specific* one-element
object whose maps out are constrained:
- **a marked element** (identity/zero/basepoint) traps the point;
- **operations/morphisms tying elements together** (action, topology, restriction maps, an arrow) ⇒
  points = the globally-coherent/invariant part, missing local structure.

But **parallel** structure (no binding operation) stays WP:
```
Set × Set:  point of (A,B) is (a,b) ∈ A×B          → covers.            ✅ WP
Set^→ (one arrow f:X→Y): point is x∈X (f(x) forced) → misses Y∖im(f).  ❌ not WP
```
Same two sets — adding *a morphism between them* breaks it. Breaker = **binding** structure.

Clean statement: **WP ⟺ `1` is a bare point hitting every element (`1` is a generator/separator by
covers).** Programmer view: an object is WP iff `obj.points()` exposes everything; binding structure
adds **hidden state** (a forced identity, a fixed-point requirement, local data) points can't see.

## 4. Is it useful / does modern math have it?

It's a **characterization**, not a property you hope for — it pins down *when point-wise reasoning is
valid*. Its narrowness (as stated, **`1` alone** generates) is informative: it's the boundary of
"Set-like." Weaken to "**some** family generates" and it's ubiquitous:

| Modern name                | Where                                    | Meaning                                                        |
|---                         |---                                       |---                                                             |
| **Well-pointed topos**     | Lawvere **ETCS**, categorical set theory | `1` generator + 2-valued + nontrivial ⇒ a model of set theory  |
| **Generator / separator**  | module/abelian/Grothendieck categories   | `Hom(G,−)` faithful; Grothendieck cats *defined* by having one |
| **Enough points**          | topos/locale theory                      | points detect everything; some topoi have **none**             |
| **Enough global sections** | algebraic geometry                       | ampleness/affineness — `Γ=Hom(1,−)` sees the sheaf             |
| **Concretizable**          | general cat theory                       | faithful functor to Set; Freyd: `Ho(Top)` is **not**           |

## 5. "Just embed into Set" — three problems

1. **Sometimes impossible**: Freyd, *"Homotopy is not concrete"* — `Ho(Top)` has no faithful functor
   to Set.
2. **Faithful isn't enough**: transporting a proof needs the functor to **preserve** the structure
   chased (finite limits, monos, images, exactness = **exact/regular**) *and* **reflect** it
   (**conservative**). Bare faithfulness gives neither.
3. **Building such a functor *is* the theorem**: Freyd–Mitchell (abelian → R-Mod → Set), Barr
   (regular → Set). Capitalization is the machine that builds it. Not free.

**Concrete vs abstract**: `Grp` *comes with* a forgetful `U:Grp→Set` that is faithful, limit-
preserving, conservative — so element-chasing in groups is free. The problem is **abstract**
categories (abstract abelian/regular/topos) with **no** underlying-set functor; you must construct one.

**Yoneda alternative**: `A ↪ [Aᵒᵖ,Set]` always, fully faithfully — but into **presheaves** (not WP),
giving **generalized** elements (maps from representables, the functor-of-points), not honest points.

## 6. Why Yoneda isn't enough

Two reasons, one shallow, one deep:
- **Shallow**: target is presheaves, not well-pointed ⇒ generalized elements, not points from `1`.
- **Deep**: Yoneda is **continuous** (preserves & reflects limits) but **destroys colimits/exactness**.
  In `Ab`: `ℤ ↠ ℤ/2` is epi, but `Hom(−,ℤ) → Hom(−,ℤ/2)` is **not** epi in presheaves (a map `X→ℤ/2`
  needn't lift to `X→ℤ`). So an exact sequence need not stay exact ⇒ a chase in presheaves proves
  nothing about `A`. Yoneda is only *half*-exact.

|                                 | full+faithful | limits | **covers/colimits** | **into well-pointed Set** |
|---                              |:--:           |:--:    |:--:                 |:--:                       |
| Yoneda (free)                   | ✅            | ✅     | ❌                  | ❌ (presheaves)           |
| Freyd–Mitchell / Barr (theorem) | ✅            | ✅     | ✅                  | ✅                        |

The two checkmarks Yoneda lacks — preserving covers, reaching honest points — are exactly the
embedding theorems' content.

## 7. Why capitalization preserves exactness when Yoneda doesn't

The difference is **how points are added**.

- **Yoneda probes by mapping *into* objects** (`a ↦ Hom(−,a)`). `Hom(X,−)` is intrinsically
  limit-preserving / colimit-destroying ⇒ left-exact only; and it **leaves** the regular world for
  presheaves.
- **Capitalization stays inside the regular world and adds points by *slicing***: each rung is the
  pullback functor `Δ : A → A/B`, `X ↦ (X×B → B)` (base change along `B→1`).

The decisive fact is the **defining axiom of a regular category (§1.52): "pullbacks transfer covers"**
— covers are stable under pullback. So the slice functor, *being a pullback*, **automatically
preserves covers**, and (being a pullback) preserves finite limits. Finite-limits + covers = a
**representation of regular categories** ⇒ preserves images and **exactness**. Faithful when `B` is
well-supported (§1.532).

Capitalization is a transfinite tower `A → A/B → (A/B)/B′ → ⋯` of such rungs, each exact + faithful,
with colimit `A ⊂ A*` an **exact faithful** embedding that makes well-supported objects well-pointed.
Exactness is **inherited from pullback-stability of covers** — the very axiom that makes `A` regular.

**One line:** Yoneda probes with `Hom` (left-exact, leaves the world); capitalization enlarges with
**pullback** (cover-stable by the regularity axiom, fully exact, stays in the world). "Covers pull
back" is exactly what Hom-based Yoneda never uses and what makes slice-based point-adding exact.

(Repo: `Slice.lean` Σ reflects covers; `SliceRegular.lean` slice is pre-regular;
`RelativeCapitalization.lean` the per-`B` rung `A→A/B` as a faithful, point-acquiring CapStep.)

## 8. The construction concretely: Δ, rungs, "different B", faithful-not-full

How capitalization actually adds the points (§1.525–§1.547), with the Set pictures.

### Two stacked indexings — "rung" vs "layer"
- **Rung** = one slice step `Aα ──Δ──▶ Aα/B`. Inside one *relative capitalization* (§1.546) you take a
  transfinite ascending union of rungs `A = A₀ ⊂ A₁ ⊂ ⋯`, where each rung slices over **the first
  well-supported object `B` not yet pointed** (first w.r.t. a fixed well-order on objects). **B changes
  every rung.** When the layer closes, every well-supported object of the *original* `A` has its points.
- **Layer** = one relative capitalization. The outer tower `A ⊂ A* ⊂ A** ⊂ ⋯` (§1.545) stacks layers,
  because `A*` has **new** well-supported objects (built from the new points) that themselves need
  points. The union `A̲` of the ω-tower is **capital** (every well-supported object is well-pointed).

You do **not** iterate `A/B → (A/B)/B` on one fixed `B`; and nothing shrinks — every step is a faithful
*enlargement*, the towers are ascending unions climbing up to the richest category `A̲`.

### What Δ is (§1.546 names the functor `A →^Δ A/B`)
`Δ : A → A/B`, `X ↦ (X×B ──snd──▶ B)` = **base change along `B→1`**: since `A = A/1`, pulling the object
`X` (i.e. `X→1`) back along the unique `B→1` gives `X×B→B`. Repo: `RelativeCapitalization.lean`
`sliceEmbedObj B C := ⟨prod C B, snd⟩` is exactly `ΔC` (named `sliceEmbed*`, not `Δ`).

**Why it adds a point:** in `A/B` the terminal is `(B ═id═▶ B)`; a point of `ΔB = (B×B ─snd→ B)` is a
section of `snd`, and the **diagonal** `δ = ⟨id,id⟩` is one (`δ≫snd = id`). Through `fst`, `δ` *is* the
identity element of `B` — a "generic point of `B`" that didn't exist in `A`. Base-change functors
preserve finite limits and (regular axiom) covers ⇒ Δ is an exact representation (§1.543) — same
mechanism as §7.

### Δ is faithful, **not full** — and that *is* "slicing adds points"
Set picture, `B = {0,1}` so `Set/B ≅ Set×Set`, `Δ : X ↦ (X,X)`, `f ↦ (f,f)`:
- **Faithful** (loses no morphism): `f ↦ (f,f)` is injective — provided `B` is well-supported
  (`Hom(X,Y) ↪ Hom(X×B,Y)`, `f↦f∘fst`, injective iff `fst` epi iff `B→1` a cover; that's *why* you only
  slice over well-supported `B`, never over `∅`).
- **Not full** (the slice is strictly bigger): `Hom_{Set/B}(ΔX,ΔY) = Hom(X,Y)^{|B|}`, and `Δ` hits only
  the **diagonal** `Hom(X,Y) ↪ Hom(X,Y)^{|B|}`. Full ⟺ `B ≅ 1`. Capitalization slices over `B ≇ 1`, so
  Δ is *never* full there.

Minimal witness `Δ1 → ΔY`, `Y={0,1}` — a map over `B` = a section of `ΔY` = one `Y`-value per fiber,
**independently**:
```
ΔY = (Y×B → B),  fibers  Y | Y         maps Δ1→ΔY :  (0,0) (1,1) | (0,1) (1,0)   = Y² = 4
                       over0  over1                   └ Δ's image ┘ └ NOT in image ┘
                                                    "same both fibers"  "differs per fiber"
```
The 2 off-diagonal maps are **not** `Δh` for any point `h:1→Y` — *and* they are exactly the **new
points** of `ΔY` (`Y` had 2 points in Set; `ΔY` has `2²=4` in `Set/B`). So "Δ not full" ≡ "slicing
added points." **No zero object is involved** — Set has none (`∅ ≠ {∗}`); the extra freedom is per-fiber
independence, not anything mapping to `0`.

### Different B's "jointly prove something" (§1.547, §1.526)
One `B` gives `B` points; ranging over **all** `B` gives every object points; the union assembles the
capital `A̲`, where `Γ = Hom(1,−) : A̲ → Set` is **exact** (capital ⇒ `1` projective, §1.526). Faithful
is *joint*: the family `T_B : A →^Δ A/B → A̲/B →^Γ Set` (one per `B`) together separates morphisms and
detects every proper subobject — no single `B` suffices. That faithful exact `A ↪ A̲ ─Γ→ Set` is the
representation Yoneda couldn't give (§6–7). The outer embedding `A ↪ A̲` is itself only **faithful**, not
full (book claims faithful, §1.544) — same faithful-not-full pattern as each rung.
