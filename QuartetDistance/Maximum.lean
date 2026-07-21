import Mathlib

/-!
# Maxima of bounded natural-valued pair statistics

Phylogenetic trees are represented by a dependent inductive structure rather than by a
pre-existing finite type of graph isomorphism classes.  The set of possible quartet distances
is nevertheless a nonempty bounded set of natural numbers.  This file packages the elementary
`Nat.sSup` argument which turns pairwise bounds and witnesses into statements about its maximum.
-/

namespace QuartetDistance

/-- The possible values of a pair statistic, with `0` included to make the set nonempty even
when the carrier type is empty. -/
def pairValueSet (f : T → T → ℕ) : Set ℕ :=
  {d | d = 0 ∨ ∃ a b, d = f a b}

/-- Maximum of a bounded natural-valued pair statistic. -/
noncomputable def maxPairValue (f : T → T → ℕ) : ℕ := sSup (pairValueSet f)

theorem zero_mem_pairValueSet (f : T → T → ℕ) : 0 ∈ pairValueSet f := by
  exact Or.inl rfl

theorem value_mem_pairValueSet (f : T → T → ℕ) (a b : T) :
    f a b ∈ pairValueSet f := by
  exact Or.inr ⟨a, b, rfl⟩

theorem pairValueSet_bddAbove (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) : BddAbove (pairValueSet f) := by
  refine ⟨B, ?_⟩
  intro d hd
  rcases hd with rfl | ⟨a, b, rfl⟩
  · exact Nat.zero_le _
  · exact hB a b

theorem maxPairValue_le (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) : maxPairValue f ≤ B := by
  apply csSup_le ⟨0, zero_mem_pairValueSet f⟩
  intro d hd
  rcases hd with rfl | ⟨a, b, rfl⟩
  · exact Nat.zero_le _
  · exact hB a b

theorem value_le_maxPairValue (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) (a b : T) :
    f a b ≤ maxPairValue f := by
  exact le_csSup (pairValueSet_bddAbove f hB) (value_mem_pairValueSet f a b)

/-- The supremum is an actual value (or the deliberately adjoined zero). -/
theorem maxPairValue_eq_zero_or_exists (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) :
    maxPairValue f = 0 ∨ ∃ a b, maxPairValue f = f a b := by
  exact Nat.sSup_mem ⟨0, zero_mem_pairValueSet f⟩ (pairValueSet_bddAbove f hB)

theorem lower_bound_maxPairValue (f : T → T → ℕ) {B L : ℕ}
    (hB : ∀ a b, f a b ≤ B) {a b : T} (hL : L ≤ f a b) :
    L ≤ maxPairValue f :=
  hL.trans (value_le_maxPairValue f hB a b)

end QuartetDistance
