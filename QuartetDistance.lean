import QuartetDistance.Arithmetic
import QuartetDistance.CircularQuotient
import QuartetDistance.DihedralGroup
import QuartetDistance.GeneralRestriction
import QuartetDistance.GraphMaximum
import QuartetDistance.GraphRibbon
import QuartetDistance.Lower
import QuartetDistance.Maximum
import QuartetDistance.PermutonMass
import QuartetDistance.PermutonPatterns
import QuartetDistance.RibbonRestriction
import QuartetDistance.Splits
import QuartetDistance.TreeAdequacy
import QuartetDistance.TiedSampleCount
import QuartetDistance.Upper

/-!
# The Bandelt--Dress maximum quartet-distance theorem

This root module packages the pairwise results as statements about both the
recursive tree encoding and the independently defined conventional finite
degree-one/degree-three graph domain on `Fin n`; their maxima are proved
exactly equal for `n ≥ 4`.
The public theorem takes the published inequality for arbitrary Borel
permutons as its one explicit hypothesis.  The construction of the step
permuton, its uniform marginals, and the exact reduction to the finite
collision model are all proved inside the development; the lower bound is
unconditional.
-/

namespace QuartetDistance

/-- The maximum quartet distance between two binary phylogenetic trees on
`Fin n`.  `maxPairValue` uses the supremum of the bounded set of attainable
natural-number distances, so no artificial finiteness instance for tree
syntax is needed. -/
noncomputable def maximumQuartetDistance (n : ℕ) : ℕ :=
  maxPairValue (@Upper.quartetDistance n)

/-- The independently defined maximum over conventional finite connected
acyclic graphs with degree-one labelled leaves and degree-three internal
vertices is exactly the syntax maximum used by the counting proof. -/
theorem graphMaximumQuartetDistance_eq_maximum (n : ℕ) (hn : 4 ≤ n) :
    graphMaximumQuartetDistance n = maximumQuartetDistance n := by
  simpa only [maximumQuartetDistance] using
    graphMaximumQuartetDistance_eq_syntaxMaximum n hn

/-- Every attainable distance is at most the number of quartets. -/
theorem maximumQuartetDistance_le_choose (n : ℕ) :
    maximumQuartetDistance n ≤ Nat.choose n 4 := by
  exact maxPairValue_le (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n)

/-- Every concrete pair is bounded by the maximum. -/
theorem quartetDistance_le_maximum (n : ℕ)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    Upper.quartetDistance T₁ T₂ ≤ maximumQuartetDistance n := by
  exact value_le_maxPairValue (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n) T₁ T₂

/-- The maximum is attained by a concrete pair, apart from the harmless zero
case included in the generic supremum construction. -/
theorem maximumQuartetDistance_eq_zero_or_exists (n : ℕ) :
    maximumQuartetDistance n = 0 ∨
      ∃ T₁ T₂ : Tree.PhyloTree (Fin n),
        maximumQuartetDistance n = Upper.quartetDistance T₁ T₂ := by
  exact maxPairValue_eq_zero_or_exists (@Upper.quartetDistance n)
    (@Upper.quartetDistance_le_choose n)

/-- The exact cleared random-labelling lower bound
`(2/3) * choose n 4 ≤ Mₙ`. -/
theorem maximumQuartetDistance_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * maximumQuartetDistance n := by
  obtain ⟨T⟩ := Lower.nonempty_phyloTree_fin n hn
  obtain ⟨pi, hpi⟩ := Lower.exists_relabeling_two_thirds T T
  exact hpi.trans (Nat.mul_le_mul_left 3
    (quartetDistance_le_maximum n T (Lower.relabel pi T)))

theorem maximumQuartetDistance_pos (n : ℕ) (hn : 4 ≤ n) :
    0 < maximumQuartetDistance n := by
  have hchoose : 0 < Nat.choose n 4 := Nat.choose_pos hn
  have hlow := maximumQuartetDistance_lower_bound n hn
  omega

/-- For `n ≥ 4`, the supremum used in the definition is attained, so it is
literally a maximum over a concrete pair of trees. -/
theorem exists_maximizing_trees (n : ℕ) (hn : 4 ≤ n) :
    ∃ T₁ T₂ : Tree.PhyloTree (Fin n),
      maximumQuartetDistance n = Upper.quartetDistance T₁ T₂ := by
  rcases maximumQuartetDistance_eq_zero_or_exists n with hzero | htrees
  · exact False.elim ((maximumQuartetDistance_pos n hn).ne' hzero)
  · exact htrees

/-- The exact denominator-cleared nontrivial upper bound for the actual
maximum.  The only hypothesis is the published permuton inequality,
specialized to the `n`-strip step permutons. -/
theorem maximumQuartetDistance_cleared_upper_bound (n : ℕ)
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n) :
    9 * maximumQuartetDistance n ≤
      6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  rcases maximumQuartetDistance_eq_zero_or_exists n with hzero | ⟨T₁, T₂, hmax⟩
  · simp [hzero]
  · rw [hmax]
    exact Upper.quartetDistance_cleared_upper_bound hpublished hn T₁ T₂

/-- The complete finite theorem in an integer form with every denominator
cleared.  This packages the random-labelling lower bound, the trivial upper
bound, and the nontrivial permuton/rotation upper bound. -/
theorem bandelt_dress_finite_bounds_of_stepPermuton (n : ℕ)
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * maximumQuartetDistance n ∧
      maximumQuartetDistance n ≤ Nat.choose n 4 ∧
      9 * maximumQuartetDistance n ≤
        6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  exact ⟨maximumQuartetDistance_lower_bound n hn,
    maximumQuartetDistance_le_choose n,
    maximumQuartetDistance_cleared_upper_bound n hpublished hn⟩

/-- The nontrivial upper estimate in the paper, now over `ℝ`. -/
theorem maximumQuartetDistance_real_upper_bound (n : ℕ)
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n) :
    (maximumQuartetDistance n : ℝ) ≤
      (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) + additiveError (n : ℝ) := by
  let M := maximumQuartetDistance n
  have hupp := maximumQuartetDistance_cleared_upper_bound n hpublished hn
  have hp : 11 * n ≤ 6 * n ^ 2 := by nlinarith
  have hR : ((9 * M : ℕ) : ℝ) ≤
      ((6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) : ℕ) : ℝ) := by
    exact_mod_cast hupp
  simp only [Nat.cast_add, Nat.cast_mul] at hR
  rw [Nat.cast_sub hp] at hR
  norm_num at hR ⊢
  rw [additiveError]
  dsimp only [M] at hR ⊢
  linarith

/-- The theorem exactly as displayed in the paper: the maximum lies between
`(2/3) choose n 4` and the minimum of the trivial and nontrivial bounds. -/
theorem bandelt_dress_main_of_stepPermuton (n : ℕ)
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n) :
    (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) ≤
        (maximumQuartetDistance n : ℝ) ∧
      (maximumQuartetDistance n : ℝ) ≤
        min (Nat.choose n 4 : ℝ)
          ((2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) + additiveError (n : ℝ)) := by
  have hlow := maximumQuartetDistance_lower_bound n hn
  have hlowR : (2 : ℝ) * (Nat.choose n 4 : ℝ) ≤
      3 * (maximumQuartetDistance n : ℝ) := by
    exact_mod_cast hlow
  constructor
  · linarith
  · rw [le_min_iff]
    constructor
    · exact_mod_cast maximumQuartetDistance_le_choose n
    · exact maximumQuartetDistance_real_upper_bound n hpublished hn

/-- The equivalent normalized sandwich from the theorem statement. -/
theorem maximumQuartetDistance_normalized_bounds (n : ℕ)
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n) :
    (2 : ℝ) / 3 ≤
        (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ) ∧
      (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ) ≤
        normalizedUpperCoefficient (n : ℝ) := by
  let M := maximumQuartetDistance n
  have hlow := maximumQuartetDistance_lower_bound n hn
  have hupp := maximumQuartetDistance_cleared_upper_bound n hpublished hn
  have hCposN : 0 < Nat.choose n 4 := Nat.choose_pos hn
  have hCpos : (0 : ℝ) < (Nat.choose n 4 : ℝ) := by exact_mod_cast hCposN
  have hlowR : (2 : ℝ) * (Nat.choose n 4 : ℝ) ≤ 3 * (M : ℝ) := by
    exact_mod_cast hlow
  have hp : 11 * n ≤ 6 * n ^ 2 := by nlinarith
  have huppR : (M : ℝ) ≤ (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) +
      (n : ℝ) * (6 * (n : ℝ) ^ 2 - 11 * (n : ℝ) + 6) / 9 := by
    have hR : ((9 * M : ℕ) : ℝ) ≤
        ((6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) : ℕ) : ℝ) := by
      exact_mod_cast hupp
    simp only [Nat.cast_add, Nat.cast_mul] at hR
    rw [Nat.cast_sub hp] at hR
    norm_num at hR ⊢
    linarith
  constructor
  · rw [le_div_iff₀ hCpos]
    nlinarith
  · rw [div_le_iff₀ hCpos, normalizedUpperCoefficient]
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hx0 : (n : ℝ) ≠ 0 := by linarith
    have hx1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hx2 : (n : ℝ) - 2 ≠ 0 := by linarith
    have hx3 : (n : ℝ) - 3 ≠ 0 := by linarith
    have hfall : (24 : ℝ) * (Nat.choose n 4 : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
      have h := congrArg (fun k : ℕ => (k : ℝ)) (twentyFour_mul_quartetCount n)
      simp only [quartetCount, Nat.cast_mul] at h
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_sub (by omega : 3 ≤ n)] at h
      norm_num at h ⊢
      exact h
    have herrmul : normalizedError (n : ℝ) * (Nat.choose n 4 : ℝ) =
        (n : ℝ) * (6 * (n : ℝ) ^ 2 - 11 * (n : ℝ) + 6) / 9 := by
      rw [normalizedError]
      field_simp [hx0, hx1, hx2, hx3]
      nlinarith [hfall]
    rw [add_mul, herrmul]
    exact huppR

/-- The paper's displayed expansion, with an exact remainder term. -/
theorem normalizedUpperCoefficient_expansion (n : ℕ) (hn : 4 ≤ n) :
    normalizedUpperCoefficient (n : ℝ) =
      (2 : ℝ) / 3 + 16 / n + 200 / (3 * (n : ℝ) ^ 2) +
        normalizedRemainder (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rw [normalizedUpperCoefficient, normalizedError_expansion]
  · rw [normalizedRemainder]
    ring
  all_goals linarith

/-- Formal `O(1/n)` form of the Bandelt--Dress conclusion. -/
theorem maximumQuartetDistance_normalized_sub_two_thirds_isBigO_of_stepPermuton
    (hpublished : ∀ n, 4 ≤ n → Circular.StepPermutonTheorem n) :
    (fun n : ℕ => (maximumQuartetDistance n : ℝ) /
        (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 300
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hs := maximumQuartetDistance_normalized_bounds n (hpublished n hn) hn
  have hgap0 : 0 ≤ (maximumQuartetDistance n : ℝ) /
      (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3 := sub_nonneg.mpr hs.1
  have hgap_le : (maximumQuartetDistance n : ℝ) /
      (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3 ≤ normalizedError (n : ℝ) := by
    rw [normalizedUpperCoefficient] at hs
    linarith
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hgap0,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3 ≤
        normalizedError (n : ℝ) := hgap_le
    _ ≤ |normalizedError (n : ℝ)| := le_abs_self _
    _ ≤ 300 / (n : ℝ) := normalizedError_bound n hn
    _ = 300 * (n : ℝ)⁻¹ := by rw [div_eq_mul_inv]

/-- In particular, the normalized maximum quartet distance converges to
`2/3`, which is the Bandelt--Dress conjecture. -/
theorem maximumQuartetDistance_normalized_tendsto_of_stepPermuton
    (hpublished : ∀ n, 4 ≤ n → Circular.StepPermutonTheorem n) :
    Filter.Tendsto
      (fun n : ℕ => (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ))
      Filter.atTop (nhds ((2 : ℝ) / 3)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  exact
    (maximumQuartetDistance_normalized_sub_two_thirds_isBigO_of_stepPermuton
      hpublished).trans_tendsto
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))

/-! ## Final statements from the one published input -/

/-- The complete finite Bandelt--Dress bounds, assuming only the cited
inequality for arbitrary Borel permutons.  The specialization to finite step
permutons and its exact finite-sample normalization are proved in
`Permuton.lean` and `PermutonMass.lean`. -/
theorem bandelt_dress_finite_bounds_of_permutonEvent
    (hpublished : Permuton.PublishedPermutonInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * maximumQuartetDistance n ∧
      maximumQuartetDistance n ≤ Nat.choose n 4 ∧
      9 * maximumQuartetDistance n ≤
        6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  exact bandelt_dress_finite_bounds_of_stepPermuton n
    (Permuton.publishedPermutonInequality_implies_stepPermutonTheorem
      hn hpublished) hn

/-- The main theorem of the paper, with the cited arbitrary-permuton
inequality as its sole external mathematical hypothesis. -/
theorem bandelt_dress_main_of_permutonEvent
    (hpublished : Permuton.PublishedPermutonInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) ≤
        (maximumQuartetDistance n : ℝ) ∧
      (maximumQuartetDistance n : ℝ) ≤
        min (Nat.choose n 4 : ℝ)
          ((2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) + additiveError (n : ℝ)) := by
  exact bandelt_dress_main_of_stepPermuton n
    (Permuton.publishedPermutonInequality_implies_stepPermutonTheorem
      hn hpublished) hn

/-- The paper's normalized `O(1/n)` conclusion from the cited inequality. -/
theorem maximumQuartetDistance_normalized_sub_two_thirds_isBigO_of_permutonEvent
    (hpublished : Permuton.PublishedPermutonInequality) :
    (fun n : ℕ => (maximumQuartetDistance n : ℝ) /
        (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact maximumQuartetDistance_normalized_sub_two_thirds_isBigO_of_stepPermuton
    (fun n hn =>
      Permuton.publishedPermutonInequality_implies_stepPermutonTheorem
        hn hpublished)

/-- Hence the normalized maximum converges to `2/3`, the Bandelt--Dress
conjecture. -/
theorem maximumQuartetDistance_normalized_tendsto_of_permutonEvent
    (hpublished : Permuton.PublishedPermutonInequality) :
    Filter.Tendsto
      (fun n : ℕ => (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ))
      Filter.atTop (nhds ((2 : ℝ) / 3)) := by
  exact maximumQuartetDistance_normalized_tendsto_of_stepPermuton
    (fun n hn =>
      Permuton.publishedPermutonInequality_implies_stepPermutonTheorem
        hn hpublished)

/-! The principal API below uses the cited theorem in the paper's literal
form: the sum of the eight individual pattern densities is at least `1/3`. -/

/-- The complete finite bounds from the literal published pattern-sum
inequality. -/
theorem bandelt_dress_finite_bounds
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * maximumQuartetDistance n ∧
      maximumQuartetDistance n ≤ Nat.choose n 4 ∧
      9 * maximumQuartetDistance n ≤
        6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  exact bandelt_dress_finite_bounds_of_permutonEvent
    (PermutonPatterns.publishedPermutonPatternSumInequality_iff.mp hpublished)
    n hn

/-- The main finite theorem exactly as displayed in the paper, with its sole
external input stated as the literal eight-pattern permuton inequality. -/
theorem bandelt_dress_main
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) ≤
        (maximumQuartetDistance n : ℝ) ∧
      (maximumQuartetDistance n : ℝ) ≤
        min (Nat.choose n 4 : ℝ)
          ((2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) + additiveError (n : ℝ)) := by
  exact bandelt_dress_main_of_permutonEvent
    (PermutonPatterns.publishedPermutonPatternSumInequality_iff.mp hpublished)
    n hn

/-- The normalized `O(1/n)` conclusion from the literal published
pattern-sum inequality. -/
theorem maximumQuartetDistance_normalized_sub_two_thirds_isBigO
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality) :
    (fun n : ℕ => (maximumQuartetDistance n : ℝ) /
        (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact maximumQuartetDistance_normalized_sub_two_thirds_isBigO_of_permutonEvent
    (PermutonPatterns.publishedPermutonPatternSumInequality_iff.mp hpublished)

/-- The normalized maximum converges to `2/3`, in the literal external-input
form of the paper. -/
theorem maximumQuartetDistance_normalized_tendsto
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality) :
    Filter.Tendsto
      (fun n : ℕ => (maximumQuartetDistance n : ℝ) / (Nat.choose n 4 : ℝ))
      Filter.atTop (nhds ((2 : ℝ) / 3)) := by
  exact maximumQuartetDistance_normalized_tendsto_of_permutonEvent
    (PermutonPatterns.publishedPermutonPatternSumInequality_iff.mp hpublished)

/-! ## Final statements on the conventional graph-theoretic domain -/

/-- For `n ≥ 4`, the conventional graph maximum is attained by a concrete
pair of canonical finite graph presentations. -/
theorem exists_graph_maximizing_trees (n : ℕ) (hn : 4 ≤ n) :
    ∃ P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n),
      graphMaximumQuartetDistance n = graphQuartetDistance P₁ P₂ := by
  obtain ⟨T₁, T₂, hmax⟩ := exists_maximizing_trees n hn
  refine ⟨T₁.toCanonicalBinaryPhyloGraph,
    T₂.toCanonicalBinaryPhyloGraph, ?_⟩
  rw [graphQuartetDistance_toCanonical,
    graphMaximumQuartetDistance_eq_maximum n hn, hmax]

/-- The complete denominator-cleared finite bounds on the paper's literal
conventional graph domain. -/
theorem graph_bandelt_dress_finite_bounds
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * graphMaximumQuartetDistance n ∧
      graphMaximumQuartetDistance n ≤ Nat.choose n 4 ∧
      9 * graphMaximumQuartetDistance n ≤
        6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  rw [graphMaximumQuartetDistance_eq_maximum n hn]
  exact bandelt_dress_finite_bounds hpublished n hn

/-- The main finite theorem exactly as displayed in the paper, now stated
for the maximum over conventional finite binary phylogenetic graph trees. -/
theorem graph_bandelt_dress_main
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality)
    (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) ≤
        (graphMaximumQuartetDistance n : ℝ) ∧
      (graphMaximumQuartetDistance n : ℝ) ≤
        min (Nat.choose n 4 : ℝ)
          ((2 : ℝ) / 3 * (Nat.choose n 4 : ℝ) + additiveError (n : ℝ)) := by
  rw [graphMaximumQuartetDistance_eq_maximum n hn]
  exact bandelt_dress_main hpublished n hn

/-- The normalized conventional graph maximum differs from `2/3` by
`O(1/n)`. -/
theorem graphMaximumQuartetDistance_normalized_sub_two_thirds_isBigO
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality) :
    (fun n : ℕ => (graphMaximumQuartetDistance n : ℝ) /
        (Nat.choose n 4 : ℝ) - (2 : ℝ) / 3) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply (maximumQuartetDistance_normalized_sub_two_thirds_isBigO
    hpublished).congr'
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    rw [graphMaximumQuartetDistance_eq_maximum n hn]
  · exact Filter.EventuallyEq.rfl

/-- Hence the normalized conventional graph maximum converges to `2/3`,
which is the Bandelt--Dress conjecture in its original graph domain. -/
theorem graphMaximumQuartetDistance_normalized_tendsto
    (hpublished : PermutonPatterns.PublishedPermutonPatternSumInequality) :
    Filter.Tendsto
      (fun n : ℕ => (graphMaximumQuartetDistance n : ℝ) /
        (Nat.choose n 4 : ℝ))
      Filter.atTop (nhds ((2 : ℝ) / 3)) := by
  apply (maximumQuartetDistance_normalized_tendsto hpublished).congr'
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  rw [graphMaximumQuartetDistance_eq_maximum n hn]

end QuartetDistance
