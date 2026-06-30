import Fredy.S2_5

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.522 / §2.53.

  CLOSED QUOTIENTS ARE AMENABLE.

  §2.522  The CLOSED QUOTIENT with respect to `U : λ ⟶ λ` identifies `R, S : α ⟶ β`
  iff `R ∪ pα U pβ° = S ∪ pα U pβ°`.  It is the least congruence which identifies `U`
  with zero and respects binary unions.

  §2.53   Closed quotients are AMENABLE: the largest member of the class of `R` is
            `R⁺ = R ∪ pα U pβ°`.

  This file packages the closed-quotient congruence (already built in
  `Fredy/S2_5.lean` as `closedQuotientRel_is_congruence`) as an
  `AmenableCongruence`, with `largest R := R ∪ (p a ≫ U ≫ (p b)°)` — Freyd's `R⁺`.
-/



namespace Freyd.Alg

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The join of three elements regrouped: `(R ∪ K) ∪ (S ∪ K) = (R ∪ S) ∪ K`.
    Both sides are the least upper bound of `R`, `S`, `K`; proved by the
    union laws (associativity, commutativity, idempotence). -/
private theorem union_pull {a b : 𝒜} (R S K : a ⟶ b) :
    (R ∪ K) ∪ (S ∪ K) = (R ∪ S) ∪ K := by
  rw [DistributiveAllegory.union_assoc (R ∪ K) S K,
      ← DistributiveAllegory.union_assoc R K S,
      DistributiveAllegory.union_comm K S,
      DistributiveAllegory.union_assoc R S K,
      ← DistributiveAllegory.union_assoc (R ∪ S) K K,
      DistributiveAllegory.union_idem K]

/-! ## §2.53  The closed quotient is amenable

  We reuse the closed-quotient congruence `closedQuotientRel_is_congruence`
  (the *same* `U`/`p` data, with the same symmetry/ideal hypotheses) and
  exhibit, for each class, the largest member `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`.

  The three amenability obligations are pure union algebra:

  * `union_congr` — the relation is defined by a `∪`-equation, so it respects `∪`
    (regroup with `union_pull` and rewrite by the two hypotheses).
  * `largest_rel`  — `R ∪ K = (R ∪ K) ∪ K` by associativity + idempotence of `K`.
  * `largest_max`  — if `R ∪ K = S ∪ K` then `S ⊑ S ∪ K = R ∪ K = R⁺`. -/

/-- §2.53  CLOSED QUOTIENTS ARE AMENABLE.

    For a symmetric `U : T ⟶ T` on the unit, with the canonical projection family
    `p : ∀ a, a ⟶ T` and the two-sided ideal absorption laws `hL`, `hR'`
    (exactly the data of `closedQuotientRel_is_congruence`), the closed-quotient
    congruence is amenable, with largest-in-class operator the book's
    `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`. -/
def closedQuotient_amenable
    {T : 𝒜} (U : T ⟶ T) (p : ∀ (a : 𝒜), a ⟶ T) (hU : U° = U)
    (hL : ∀ {a b c : 𝒜} (R : a ⟶ b),
      R ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)°)
    (hR' : ∀ {a b c : 𝒜} (S : b ⟶ c),
      (p a ≫ U ≫ (p b)°) ≫ S ⊑ p a ≫ U ≫ (p c)°) :
    AmenableCongruence 𝒜 where
  cong := closedQuotientRel_is_congruence U p hU hL hR'
  union_congr {a b R S R' S'} hR hS := by
    -- `cong.rel X Y` is `X ∪ K = Y ∪ K` with `K = p a ≫ U ≫ (p b)°`.
    have hRe : R ∪ (p a ≫ U ≫ (p b)°) = R' ∪ (p a ≫ U ≫ (p b)°) := hR
    have hSe : S ∪ (p a ≫ U ≫ (p b)°) = S' ∪ (p a ≫ U ≫ (p b)°) := hS
    show closedQuotientRel U (p a) (p b) (R ∪ S) (R' ∪ S')
    simp only [closedQuotientRel]
    -- (R∪S)∪K = (R∪K)∪(S∪K) = (R'∪K)∪(S'∪K) = (R'∪S')∪K.
    rw [← union_pull R S (p a ≫ U ≫ (p b)°), ← union_pull R' S' (p a ≫ U ≫ (p b)°),
        hRe, hSe]
  largest {a b} R := R ∪ (p a ≫ U ≫ (p b)°)
  largest_rel {a b} R := by
    -- Goal: `R ∪ K = (R ∪ K) ∪ K`, by associativity + idempotence.
    show R ∪ (p a ≫ U ≫ (p b)°)
       = (R ∪ (p a ≫ U ≫ (p b)°)) ∪ (p a ≫ U ≫ (p b)°)
    rw [← DistributiveAllegory.union_assoc R (p a ≫ U ≫ (p b)°) (p a ≫ U ≫ (p b)°),
        DistributiveAllegory.union_idem]
  largest_max {a b R S} h := by
    -- h : R ∪ K = S ∪ K.  Goal: S ⊑ R ∪ K.  Use S ⊑ S ∪ K = R ∪ K.
    have he : R ∪ (p a ≫ U ≫ (p b)°) = S ∪ (p a ≫ U ≫ (p b)°) := h
    have hs : S ⊑ S ∪ (p a ≫ U ≫ (p b)°) := le_union_left S _
    rw [← he] at hs
    exact hs

/-- §2.53 headline: the closed quotient (w.r.t. a symmetric `U` with the
    canonical projections `p` and ideal-absorption laws `hL`, `hR'`) is amenable.
    Its largest-in-class operator is Freyd's `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`. -/
theorem closedQuotient_amenable_largest_eq
    {T : 𝒜} (U : T ⟶ T) (p : ∀ (a : 𝒜), a ⟶ T) (hU : U° = U)
    (hL : ∀ {a b c : 𝒜} (R : a ⟶ b),
      R ≫ (p b ≫ U ≫ (p c)°) ⊑ p a ≫ U ≫ (p c)°)
    (hR' : ∀ {a b c : 𝒜} (S : b ⟶ c),
      (p a ≫ U ≫ (p b)°) ≫ S ⊑ p a ≫ U ≫ (p c)°)
    {a b : 𝒜} (R : a ⟶ b) :
    (closedQuotient_amenable U p hU hL hR').largest R = R ∪ (p a ≫ U ≫ (p b)°) :=
  rfl

end Freyd.Alg
