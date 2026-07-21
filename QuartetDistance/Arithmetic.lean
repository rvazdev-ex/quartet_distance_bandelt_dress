import Mathlib

/-!
# Arithmetic used in the finite quartet-distance bound

This file isolates all numerical identities and asymptotic statements occurring in
`bandelt_dress_solution.tex`.  Keeping these facts separate makes it possible to state the
combinatorial proof with natural-number counts and only coerce to `ℝ` for the normalized
corollaries.
-/

namespace QuartetDistance

/-- The number of four-element subsets of an `n`-element set. -/
def quartetCount (n : ℕ) : ℕ := n.choose 4

/-- The elementary identity `24 * choose n 4 = (n)₄`. -/
theorem twentyFour_mul_quartetCount (n : ℕ) :
    24 * quartetCount n = n * (n - 1) * (n - 2) * (n - 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 4
  norm_num at h
  simpa [quartetCount, mul_assoc, mul_comm, mul_left_comm] using h.symm

/-- The collision polynomial in the step-permuton construction. -/
theorem fourth_power_sub_falling_four (x : ℤ) :
    x ^ 4 - x * (x - 1) * (x - 2) * (x - 3) =
      x * (6 * x ^ 2 - 11 * x + 6) := by
  ring

/-- The normalized additive error in the paper's upper bound. -/
noncomputable def normalizedError (x : ℝ) : ℝ :=
  8 * (6 * x ^ 2 - 11 * x + 6) / (3 * (x - 1) * (x - 2) * (x - 3))

/-- The normalized nontrivial upper coefficient `2/3 + error`. -/
noncomputable def normalizedUpperCoefficient (x : ℝ) : ℝ := 2 / 3 + normalizedError x

/-- A computable rational version, used for the two exact finite threshold checks. -/
def normalizedUpperCoefficientRat (n : ℕ) : ℚ :=
  let x : ℚ := n
  2 / 3 + 8 * (6 * x ^ 2 - 11 * x + 6) / (3 * (x - 1) * (x - 2) * (x - 3))

theorem normalizedUpperCoefficientRat_cast (n : ℕ) :
    (normalizedUpperCoefficientRat n : ℝ) = normalizedUpperCoefficient (n : ℝ) := by
  norm_num [normalizedUpperCoefficientRat, normalizedUpperCoefficient, normalizedError]

/-- Exact version of the displayed asymptotic expansion, including its remainder. -/
theorem normalizedError_expansion (x : ℝ)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    normalizedError x =
      16 / x + 200 / (3 * x ^ 2) +
        8 * (90 * x ^ 2 - 239 * x + 150) /
          (3 * x ^ 2 * (x - 1) * (x - 2) * (x - 3)) := by
  simp only [normalizedError]
  field_simp
  ring

/-- The exact remainder appearing in `normalizedError_expansion`. -/
noncomputable def normalizedRemainder (x : ℝ) : ℝ :=
  8 * (90 * x ^ 2 - 239 * x + 150) /
    (3 * x ^ 2 * (x - 1) * (x - 2) * (x - 3))

/-- An explicit `1/n³` bound for the remainder in the displayed expansion. -/
theorem normalizedRemainder_bound (n : ℕ) (hn : 4 ≤ n) :
    |normalizedRemainder (n : ℝ)| ≤ 5000 / (n : ℝ) ^ 3 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have h3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have hnum0 : (0 : ℝ) ≤ 90 * (n : ℝ) ^ 2 - 239 * n + 150 := by
    nlinarith [sq_nonneg ((n : ℝ) - 4)]
  have hnum : 8 * (90 * (n : ℝ) ^ 2 - 239 * n + 150) ≤
      800 * (n : ℝ) ^ 2 := by nlinarith
  have hd1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hd2 : (n : ℝ) / 2 ≤ (n : ℝ) - 2 := by linarith
  have hd3 : (n : ℝ) / 4 ≤ (n : ℝ) - 3 := by linarith
  have hprod : (n : ℝ) ^ 3 / 16 ≤
      ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hd2),
      mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)) (sub_nonneg.mpr hd3)]
  have hden : 3 * (n : ℝ) ^ 5 / 16 ≤
      3 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    have hm := mul_le_mul_of_nonneg_left hprod
      (show (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2 by positivity)
    nlinarith
  have hden0 : 0 <
      3 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    positivity
  have hrem0 : 0 ≤ normalizedRemainder (n : ℝ) := by
    rw [normalizedRemainder]
    exact div_nonneg (mul_nonneg (by norm_num) hnum0) hden0.le
  rw [abs_of_nonneg hrem0, normalizedRemainder]
  apply (div_le_iff₀ hden0).2
  have hcross :
      8 * (90 * (n : ℝ) ^ 2 - 239 * n + 150) * (n : ℝ) ^ 3 ≤
        5000 *
          (3 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
    have ha := mul_le_mul_of_nonneg_right hnum
      (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)
    have hb := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 5000)
    nlinarith
  calc
    8 * (90 * (n : ℝ) ^ 2 - 239 * n + 150) ≤
        (5000 *
          (3 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3))) /
            (n : ℝ) ^ 3 := (le_div_iff₀ (pow_pos hn0 3)).2 hcross
    _ = 5000 / (n : ℝ) ^ 3 *
          (3 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
            ring

/-- Formal meaning of the paper's `O(n⁻³)` remainder. -/
theorem normalizedRemainder_isBigO :
    (fun n : ℕ => normalizedRemainder (n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  apply Asymptotics.IsBigO.of_bound 5000
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  simp only [Real.norm_eq_abs]
  have hinv : |(n : ℝ)⁻¹| = (n : ℝ)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [abs_pow, hinv]
  simpa [div_eq_mul_inv] using normalizedRemainder_bound n hn

/-- The additive finite-size error in the unnormalized theorem. -/
noncomputable def additiveError (x : ℝ) : ℝ :=
  x * (6 * x ^ 2 - 11 * x + 6) / 9

theorem additiveError_bound (n : ℕ) (hn : 1 ≤ n) :
    |additiveError (n : ℝ)| ≤ (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpoly0 : (0 : ℝ) ≤ 6 * (n : ℝ) ^ 2 - 11 * n + 6 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpoly : 6 * (n : ℝ) ^ 2 - 11 * n + 6 ≤ 9 * (n : ℝ) ^ 2 := by
    nlinarith
  have herr0 : 0 ≤ additiveError (n : ℝ) := by
    rw [additiveError]
    positivity
  rw [abs_of_nonneg herr0, additiveError]
  have hm := mul_le_mul_of_nonneg_left hpoly hn0
  nlinarith

/-- Formal meaning of the remark that the additive error is `O(n³)`. -/
theorem additiveError_isBigO :
    (fun n : ℕ => additiveError (n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ 3) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_eq_abs, one_mul]
  have hpow : |(n : ℝ) ^ 3| = (n : ℝ) ^ 3 :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
  rw [hpow]
  exact additiveError_bound n hn

/-- A uniform explicit bound showing that the normalized error is `O(1/n)`. -/
theorem normalizedError_bound (n : ℕ) (hn : 4 ≤ n) :
    |normalizedError (n : ℝ)| ≤ 300 / (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have h3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have hnum0 : (0 : ℝ) ≤ 6 * (n : ℝ) ^ 2 - 11 * n + 6 := by nlinarith
  have hnum : 8 * (6 * (n : ℝ) ^ 2 - 11 * n + 6) ≤ 56 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hd1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hd2 : (n : ℝ) / 2 ≤ (n : ℝ) - 2 := by linarith
  have hd3 : (n : ℝ) / 4 ≤ (n : ℝ) - 3 := by linarith
  have hden : 3 * (n : ℝ) ^ 3 / 16 ≤
      3 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hd2),
      mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)) (sub_nonneg.mpr hd3)]
  have hden0 :
      0 < 3 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) := by positivity
  have herr0 : 0 ≤ normalizedError (n : ℝ) := by
    rw [normalizedError]
    exact div_nonneg (mul_nonneg (by norm_num) hnum0) hden0.le
  rw [abs_of_nonneg herr0, normalizedError]
  apply (div_le_iff₀ hden0).2
  have hcross : 8 * (6 * (n : ℝ) ^ 2 - 11 * n + 6) * (n : ℝ) ≤
      300 * (3 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
    nlinarith [mul_le_mul_of_nonneg_right hnum (le_of_lt hn0),
      mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 300)]
  calc
    8 * (6 * (n : ℝ) ^ 2 - 11 * n + 6) ≤
        (300 * (3 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3))) /
          (n : ℝ) := (le_div_iff₀ hn0).2 hcross
    _ = 300 / (n : ℝ) *
          (3 * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by ring

/-- Formal meaning of the paper's `O(1/n)` normalized error. -/
theorem normalizedError_isBigO :
    (fun n : ℕ => normalizedError (n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((n : ℝ)⁻¹)) := by
  apply Asymptotics.IsBigO.of_bound 300
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  simp only [Real.norm_eq_abs]
  have hinv : |(n : ℝ)⁻¹| = (n : ℝ)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [hinv]
  simpa [div_eq_mul_inv] using normalizedError_bound n hn

/-- The exact coefficient first improves on the trivial coefficient `1` at `n = 53`. -/
theorem first_trivial_improvement :
    normalizedUpperCoefficient 53 < 1 ∧
      ∀ n ∈ Finset.Icc (4 : ℕ) 52,
        1 ≤ normalizedUpperCoefficient (n : ℝ) := by
  constructor
  · norm_num [normalizedUpperCoefficient, normalizedError]
  · intro n hn
    have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn52 : n ≤ 52 := (Finset.mem_Icc.mp hn).2
    let x : ℝ := n
    let k : ℝ := x - 4
    have hx4 : 4 ≤ x := by dsimp [x]; exact_mod_cast hn4
    have hx52 : x ≤ 52 := by dsimp [x]; exact_mod_cast hn52
    have hk0 : 0 ≤ k := by dsimp [k]; linarith
    have hk48 : k ≤ 48 := by dsimp [k]; linarith
    have hcube : k ^ 3 ≤ 48 * k ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hk48) (sq_nonneg k)]
    have hquad : 0 ≤ 458 + 285 * k - 6 * k ^ 2 := by
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk48)]
    have hpoly : 0 ≤ -x ^ 3 + 54 * x ^ 2 - 99 * x + 54 := by
      have hid : -x ^ 3 + 54 * x ^ 2 - 99 * x + 54 =
          458 + 285 * k + 42 * k ^ 2 - k ^ 3 := by
        dsimp [k]
        ring
      rw [hid]
      nlinarith
    have hD : (x - 1) * (x - 2) * (x - 3) ≤
        8 * (6 * x ^ 2 - 11 * x + 6) := by
      nlinarith
    have hx1 : 0 < x - 1 := by linarith
    have hx2 : 0 < x - 2 := by linarith
    have hx3 : 0 < x - 3 := by linarith
    have hden : 0 < 3 * (x - 1) * (x - 2) * (x - 3) := by positivity
    have herr : (1 : ℝ) / 3 ≤ normalizedError x := by
      rw [normalizedError]
      apply (le_div_iff₀ hden).2
      nlinarith
    change 1 ≤ normalizedUpperCoefficient x
    rw [normalizedUpperCoefficient]
    linarith

/-- The exact coefficient first drops below `0.69` at `n = 690`. -/
theorem first_below_point_six_nine :
    normalizedUpperCoefficient 690 < (69 : ℝ) / 100 ∧
      ∀ n ∈ Finset.Icc (4 : ℕ) 689,
        (69 : ℝ) / 100 ≤ normalizedUpperCoefficient (n : ℝ) := by
  constructor
  · norm_num [normalizedUpperCoefficient, normalizedError]
  · intro n hn
    have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn689 : n ≤ 689 := (Finset.mem_Icc.mp hn).2
    let x : ℝ := n
    let k : ℝ := x - 4
    have hx4 : 4 ≤ x := by dsimp [x]; exact_mod_cast hn4
    have hx689 : x ≤ 689 := by dsimp [x]; exact_mod_cast hn689
    have hk0 : 0 ≤ k := by dsimp [k]; linarith
    have hk685 : k ≤ 685 := by dsimp [k]; linarith
    have hcube : 7 * k ^ 3 ≤ 4795 * k ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hk685) (sq_nonneg k)]
    have hquad : 0 ≤ 46358 + 29523 * k - 37 * k ^ 2 := by
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk685)]
    have hpoly : 0 ≤ -7 * x ^ 3 + 4842 * x ^ 2 - 8877 * x + 4842 := by
      have hid : -7 * x ^ 3 + 4842 * x ^ 2 - 8877 * x + 4842 =
          46358 + 29523 * k + 4758 * k ^ 2 - 7 * k ^ 3 := by
        dsimp [k]
        ring
      rw [hid]
      nlinarith
    have hD : 7 * ((x - 1) * (x - 2) * (x - 3)) ≤
        800 * (6 * x ^ 2 - 11 * x + 6) := by
      nlinarith
    have hx1 : 0 < x - 1 := by linarith
    have hx2 : 0 < x - 2 := by linarith
    have hx3 : 0 < x - 3 := by linarith
    have hden : 0 < 3 * (x - 1) * (x - 2) * (x - 3) := by positivity
    have herr : (7 : ℝ) / 300 ≤ normalizedError x := by
      rw [normalizedError]
      apply (le_div_iff₀ hden).2
      nlinarith
    change (69 : ℝ) / 100 ≤ normalizedUpperCoefficient x
    rw [normalizedUpperCoefficient]
    linarith

end QuartetDistance
