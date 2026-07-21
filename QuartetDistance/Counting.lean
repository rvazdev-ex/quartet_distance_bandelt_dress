import Mathlib

/-!
# Exact finite counting for the quartet-distance argument

This file contains the probability-free core of the Bandelt--Dress upper
bound.  `Q` is an arbitrary finite family of quartets, `S` is an arbitrary
three-element topology type, and `Ω₁ × Ω₂` is the product of the two finite
rotation sample spaces.  Thus independence is represented by counting the
cartesian product, while no independence between distinct quartets is used.

The hypotheses expose exactly the two inputs from the geometric parts of the
proof: the wrong-channel fiber counts and a pointwise circular lower bound.
All conclusions are integer identities or cleared inequalities.  The last
section also checks the local `8/24` random-relabelling enumeration and turns
pointwise uniformity into the usual `2/3` lower-bound argument.
-/

namespace QuartetDistance.Counting

open scoped BigOperators

variable {Q S Ω₁ Ω₂ : Type*}

/-- Number of points in a finite sample space which produce channel `s`. -/
def channelCount [Fintype Ω] [DecidableEq S] (out : Ω → S) (s : S) : ℕ :=
  (Finset.univ.filter fun ω => out ω = s).card

/-- Exact finite version of the wrong-channel law. -/
structure WrongChannelLaw [Fintype Ω] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) : Prop where
  true_count (q : Q) : channelCount (fun ω => out ω q) (truth q) = 0
  wrong_count (q : Q) (s : S) (hs : s ≠ truth q) :
    2 * channelCount (fun ω => out ω q) s = Fintype.card Ω

/-- Number of independent sample pairs agreeing at `q`. -/
def pairAgreementCount [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) (q : Q) : ℕ :=
  (Finset.univ.filter fun p : Ω₁ × Ω₂ => out₁ p.1 q = out₂ p.2 q).card

lemma pairAgreementCount_eq_sum [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) (q : Q) :
    pairAgreementCount out₁ out₂ q =
      ∑ s : S, channelCount (fun ω => out₁ ω q) s *
        channelCount (fun ω => out₂ ω q) s := by
  classical
  let A : Finset (Ω₁ × Ω₂) :=
    Finset.univ.filter fun p => out₁ p.1 q = out₂ p.2 q
  have hmap : (A : Set (Ω₁ × Ω₂)).MapsTo (fun p => out₁ p.1 q)
      (Finset.univ : Finset S) := by
    intro p hp
    simp
  rw [pairAgreementCount,
    show (Finset.univ.filter fun p : Ω₁ × Ω₂ => out₁ p.1 q = out₂ p.2 q) = A from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show (A.filter fun p => out₁ p.1 q = s) =
      (Finset.univ.filter fun a : Ω₁ => out₁ a q = s) ×ˢ
        (Finset.univ.filter fun b : Ω₂ => out₂ b q = s) by
    ext p
    simp [A]
    aesop]
  simp [channelCount]

lemma four_mul_pairAgreementCount_eq_filtered
    [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂) (q : Q) :
    4 * pairAgreementCount out₁ out₂ q =
      (Finset.univ.filter fun s : S => s ≠ truth₁ q ∧ s ≠ truth₂ q).card *
        (Fintype.card Ω₁ * Fintype.card Ω₂) := by
  classical
  rw [pairAgreementCount_eq_sum]
  rw [Finset.mul_sum]
  calc
    (∑ s : S, 4 *
        (channelCount (fun ω => out₁ ω q) s * channelCount (fun ω => out₂ ω q) s)) =
        ∑ s : S, if s ≠ truth₁ q ∧ s ≠ truth₂ q then
          Fintype.card Ω₁ * Fintype.card Ω₂ else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hs₁ : s = truth₁ q
      · subst s
        simp [h₁.true_count]
      · by_cases hs₂ : s = truth₂ q
        · subst s
          simp [h₂.true_count]
        · rw [if_pos ⟨hs₁, hs₂⟩]
          calc
            4 * (channelCount (fun ω => out₁ ω q) s *
                channelCount (fun ω => out₂ ω q) s) =
                (2 * channelCount (fun ω => out₁ ω q) s) *
                  (2 * channelCount (fun ω => out₂ ω q) s) := by ring
            _ = Fintype.card Ω₁ * Fintype.card Ω₂ := by
              rw [h₁.wrong_count q s hs₁, h₂.wrong_count q s hs₂]
    _ = (Finset.univ.filter fun s : S => s ≠ truth₁ q ∧ s ≠ truth₂ q).card *
          (Fintype.card Ω₁ * Fintype.card Ω₂) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_const_nat fun _ _ => rfl

lemma card_avoiding_one [Fintype S] [DecidableEq S]
    (hcard : Fintype.card S = 3) (a : S) :
    (Finset.univ.filter fun s : S => s ≠ a).card = 2 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a)]
  simpa using hcard

lemma card_avoiding_two [Fintype S] [DecidableEq S]
    (hcard : Fintype.card S = 3) {a b : S} (hab : a ≠ b) :
    (Finset.univ.filter fun s : S => s ≠ a ∧ s ≠ b).card = 1 := by
  rw [show (Finset.univ.filter fun s : S => s ≠ a ∧ s ≠ b) =
      (Finset.univ.erase a).erase b by ext s; simp [and_comm]]
  rw [Finset.card_erase_of_mem (by simp [hab.symm])]
  rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
  simp [hcard]

/-- Agreement at a quartet on which the true topologies coincide has count one half. -/
theorem two_mul_pairAgreementCount_of_truth_eq
    [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂)
    (q : Q) (hq : truth₁ q = truth₂ q) :
    2 * pairAgreementCount out₁ out₂ q = Fintype.card Ω₁ * Fintype.card Ω₂ := by
  have h4 := four_mul_pairAgreementCount_eq_filtered truth₁ truth₂ out₁ out₂ h₁ h₂ q
  rw [hq] at h4
  simp only [ne_eq, and_self] at h4
  rw [card_avoiding_one hcard] at h4
  omega

/-- Agreement at a quartet on which true topologies differ has count one quarter. -/
theorem four_mul_pairAgreementCount_of_truth_ne
    [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂)
    (q : Q) (hq : truth₁ q ≠ truth₂ q) :
    4 * pairAgreementCount out₁ out₂ q = Fintype.card Ω₁ * Fintype.card Ω₂ := by
  rw [four_mul_pairAgreementCount_eq_filtered truth₁ truth₂ out₁ out₂ h₁ h₂ q,
    card_avoiding_two hcard hq, one_mul]

/-- Number of quartets on which the two true topologies agree. -/
def truthAgreementCount [Fintype Q] [DecidableEq S]
    (truth₁ truth₂ : Q → S) : ℕ :=
  (Finset.univ.filter fun q => truth₁ q = truth₂ q).card

/-- Number of quartets on which the two true topologies differ. -/
def truthDistance [Fintype Q] [DecidableEq S]
    (truth₁ truth₂ : Q → S) : ℕ :=
  (Finset.univ.filter fun q => truth₁ q ≠ truth₂ q).card

lemma truthAgreementCount_add_truthDistance [Fintype Q] [DecidableEq S]
    (truth₁ truth₂ : Q → S) :
    truthAgreementCount truth₁ truth₂ + truthDistance truth₁ truth₂ = Fintype.card Q := by
  classical
  simpa [truthAgreementCount, truthDistance] using
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Q))
      (fun q => truth₁ q = truth₂ q)

/-- The finite random variable `K`: the number of channel agreements. -/
def sampledK [Fintype Q] [DecidableEq Q] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℕ :=
  (Finset.univ.filter fun q => out₁ ω₁ q = out₂ ω₂ q).card

/-- Sum of `K` over the independent product sample space. -/
def totalK [Fintype Q] [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Q] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) : ℕ :=
  ∑ p : Ω₁ × Ω₂, sampledK out₁ out₂ p.1 p.2

lemma totalK_eq_sum_pairAgreementCount
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) :
    totalK out₁ out₂ = ∑ q : Q, pairAgreementCount out₁ out₂ q := by
  classical
  simp_rw [totalK, sampledK, pairAgreementCount, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Exact integer form of `E K = (N+A)/4`. -/
theorem four_mul_totalK
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂) :
    4 * totalK out₁ out₂ =
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
        (Fintype.card Q + truthAgreementCount truth₁ truth₂) := by
  classical
  rw [totalK_eq_sum_pairAgreementCount, Finset.mul_sum]
  let M := Fintype.card Ω₁ * Fintype.card Ω₂
  calc
    (∑ q : Q, 4 * pairAgreementCount out₁ out₂ q) =
        ∑ q : Q, if truth₁ q = truth₂ q then 2 * M else M := by
      apply Finset.sum_congr rfl
      intro q hqmem
      by_cases hq : truth₁ q = truth₂ q
      · rw [if_pos hq]
        have hhalf := two_mul_pairAgreementCount_of_truth_eq hcard
          truth₁ truth₂ out₁ out₂ h₁ h₂ q hq
        dsimp only [M]
        omega
      · rw [if_neg hq]
        simpa only [M] using four_mul_pairAgreementCount_of_truth_ne hcard
          truth₁ truth₂ out₁ out₂ h₁ h₂ q hq
    _ = truthAgreementCount truth₁ truth₂ * (2 * M) +
          truthDistance truth₁ truth₂ * M := by
      rw [Finset.sum_ite]
      simp only [truthAgreementCount, truthDistance]
      congr 1 <;> exact Finset.sum_const_nat fun _ _ => rfl
    _ = M * (Fintype.card Q + truthAgreementCount truth₁ truth₂) := by
      have hpartition := truthAgreementCount_add_truthDistance truth₁ truth₂
      rw [← hpartition]
      ring

/-- Rational average of `K` over the independent product sample space. -/
noncomputable def expectedK [Fintype Q] [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Q] [DecidableEq S]
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) : ℚ :=
  (totalK out₁ out₂ : ℚ) / (Fintype.card Ω₁ * Fintype.card Ω₂ : ℕ)

/-- The paper's expectation identity, now as an actual rational average. -/
theorem expectedK_eq
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    [Nonempty Ω₁] [Nonempty Ω₂]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂) :
    expectedK out₁ out₂ =
      (Fintype.card Q + truthAgreementCount truth₁ truth₂ : ℕ) / 4 := by
  have h := congrArg (fun n : ℕ => (n : ℚ))
    (four_mul_totalK hcard truth₁ truth₂ out₁ out₂ h₁ h₂)
  have hM : (Fintype.card Ω₁ * Fintype.card Ω₂ : ℕ) ≠ 0 := by
    positivity
  rw [expectedK, div_eq_iff (by exact_mod_cast hM)]
  push_cast at h ⊢
  nlinarith

/-- A pointwise cleared lower bound for every pair of sampled circular orders. -/
def PointwiseLowerBound [Fintype Q] [DecidableEq Q] [DecidableEq S]
    (numerator denominator : ℕ)
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) : Prop :=
  ∀ ω₁ ω₂, numerator * Fintype.card Q ≤
    denominator * sampledK out₁ out₂ ω₁ ω₂

/-- The abstract double-counting upper bound.  It is the cleared form of
`D ≤ (2 - 4 numerator / denominator) N`. -/
theorem cleared_truthDistance_upper_bound
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    [Nonempty Ω₁] [Nonempty Ω₂]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂)
    (numerator denominator : ℕ)
    (hlower : PointwiseLowerBound numerator denominator out₁ out₂) :
    denominator * truthDistance truth₁ truth₂ +
        4 * numerator * Fintype.card Q ≤
      2 * denominator * Fintype.card Q := by
  have hsum :
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (numerator * Fintype.card Q) ≤
        denominator * totalK out₁ out₂ := by
    calc
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (numerator * Fintype.card Q) =
          ∑ p : Ω₁ × Ω₂, numerator * Fintype.card Q := by simp
      _ ≤ ∑ p : Ω₁ × Ω₂,
          denominator * sampledK out₁ out₂ p.1 p.2 := by
            exact Finset.sum_le_sum fun p hp => hlower p.1 p.2
      _ = denominator * totalK out₁ out₂ := by
        simp [totalK, Finset.mul_sum]
  have htotal := four_mul_totalK hcard truth₁ truth₂ out₁ out₂ h₁ h₂
  have hpartition := truthAgreementCount_add_truthDistance truth₁ truth₂
  have hM : 0 < Fintype.card Ω₁ * Fintype.card Ω₂ := by positivity
  have hproduct :
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (4 * numerator * Fintype.card Q) ≤
        (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator *
            (Fintype.card Q + truthAgreementCount truth₁ truth₂)) := by
    calc
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (4 * numerator * Fintype.card Q) =
          4 * ((Fintype.card Ω₁ * Fintype.card Ω₂) *
            (numerator * Fintype.card Q)) := by ring
      _ ≤ 4 * (denominator * totalK out₁ out₂) :=
        Nat.mul_le_mul_left 4 hsum
      _ = denominator * (4 * totalK out₁ out₂) := by ring
      _ = denominator * ((Fintype.card Ω₁ * Fintype.card Ω₂) *
            (Fintype.card Q + truthAgreementCount truth₁ truth₂)) := by
        rw [htotal]
      _ = (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator *
            (Fintype.card Q + truthAgreementCount truth₁ truth₂)) := by ring
  have hbase : 4 * numerator * Fintype.card Q ≤
      denominator * (Fintype.card Q + truthAgreementCount truth₁ truth₂) :=
    Nat.le_of_mul_le_mul_left hproduct hM
  calc
    denominator * truthDistance truth₁ truth₂ +
        4 * numerator * Fintype.card Q ≤
      denominator * truthDistance truth₁ truth₂ +
        denominator * (Fintype.card Q + truthAgreementCount truth₁ truth₂) :=
      Nat.add_le_add_left hbase _
    _ = 2 * denominator * Fintype.card Q := by
      rw [← hpartition]
      ring

/-- Pointwise circular lower bound with an additive cleared error.  This
form avoids truncated subtraction when the stated lower coefficient is
negative for small parameters. -/
def PointwiseLowerBoundWithError [Fintype Q] [DecidableEq Q] [DecidableEq S]
    (denominator error : ℕ)
    (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S) : Prop :=
  ∀ ω₁ ω₂, denominator * Fintype.card Q ≤
    denominator * sampledK out₁ out₂ ω₁ ω₂ + error * Fintype.card Q

/-- Double counting in the additive-error form. -/
theorem cleared_truthDistance_upper_bound_with_error
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    [Nonempty Ω₁] [Nonempty Ω₂]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂)
    (denominator error : ℕ)
    (hlower : PointwiseLowerBoundWithError denominator error out₁ out₂) :
    denominator * truthDistance truth₁ truth₂ +
        2 * denominator * Fintype.card Q ≤
      4 * error * Fintype.card Q := by
  have hsum :
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator * Fintype.card Q) ≤
        denominator * totalK out₁ out₂ +
          (Fintype.card Ω₁ * Fintype.card Ω₂) *
            (error * Fintype.card Q) := by
    calc
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator * Fintype.card Q) =
          ∑ p : Ω₁ × Ω₂, denominator * Fintype.card Q := by simp
      _ ≤ ∑ p : Ω₁ × Ω₂,
          (denominator * sampledK out₁ out₂ p.1 p.2 +
            error * Fintype.card Q) := by
          exact Finset.sum_le_sum fun p hp => hlower p.1 p.2
      _ = denominator * totalK out₁ out₂ +
          (Fintype.card Ω₁ * Fintype.card Ω₂) *
            (error * Fintype.card Q) := by
        simp [totalK, Finset.mul_sum, Finset.sum_add_distrib]
  have htotal := four_mul_totalK hcard truth₁ truth₂ out₁ out₂ h₁ h₂
  have hpartition := truthAgreementCount_add_truthDistance truth₁ truth₂
  have hM : 0 < Fintype.card Ω₁ * Fintype.card Ω₂ := by positivity
  have hproduct :
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (4 * denominator * Fintype.card Q) ≤
        (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator *
              (Fintype.card Q + truthAgreementCount truth₁ truth₂) +
            4 * error * Fintype.card Q) := by
    calc
      (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (4 * denominator * Fintype.card Q) =
          4 * ((Fintype.card Ω₁ * Fintype.card Ω₂) *
            (denominator * Fintype.card Q)) := by ring
      _ ≤ 4 * (denominator * totalK out₁ out₂ +
          (Fintype.card Ω₁ * Fintype.card Ω₂) *
            (error * Fintype.card Q)) := Nat.mul_le_mul_left 4 hsum
      _ = denominator * (4 * totalK out₁ out₂) +
          (Fintype.card Ω₁ * Fintype.card Ω₂) *
            (4 * error * Fintype.card Q) := by ring
      _ = denominator * ((Fintype.card Ω₁ * Fintype.card Ω₂) *
            (Fintype.card Q + truthAgreementCount truth₁ truth₂)) +
          (Fintype.card Ω₁ * Fintype.card Ω₂) *
            (4 * error * Fintype.card Q) := by rw [htotal]
      _ = (Fintype.card Ω₁ * Fintype.card Ω₂) *
          (denominator *
              (Fintype.card Q + truthAgreementCount truth₁ truth₂) +
            4 * error * Fintype.card Q) := by ring
  have hbase : 4 * denominator * Fintype.card Q ≤
      denominator * (Fintype.card Q + truthAgreementCount truth₁ truth₂) +
        4 * error * Fintype.card Q :=
    Nat.le_of_mul_le_mul_left hproduct hM
  have hmid :
      denominator * truthDistance truth₁ truth₂ +
          4 * denominator * Fintype.card Q ≤
        2 * denominator * Fintype.card Q +
          4 * error * Fintype.card Q := by
    calc
      denominator * truthDistance truth₁ truth₂ +
          4 * denominator * Fintype.card Q ≤
        denominator * truthDistance truth₁ truth₂ +
          (denominator *
              (Fintype.card Q + truthAgreementCount truth₁ truth₂) +
            4 * error * Fintype.card Q) := Nat.add_le_add_left hbase _
      _ = 2 * denominator * Fintype.card Q +
          4 * error * Fintype.card Q := by
        rw [← hpartition]
        ring
  apply Nat.le_of_add_le_add_left (a := 2 * denominator * Fintype.card Q)
  calc
    2 * denominator * Fintype.card Q +
        (denominator * truthDistance truth₁ truth₂ +
          2 * denominator * Fintype.card Q) =
      denominator * truthDistance truth₁ truth₂ +
        4 * denominator * Fintype.card Q := by ring
    _ ≤ 2 * denominator * Fintype.card Q +
          4 * error * Fintype.card Q := hmid

/-- The specialization used after the step-permuton estimate.  Here
`fallingFour` denotes the cancelled factor `(n - 1)(n - 2)(n - 3)` in
`stepAlpha n`; the supplied pointwise inequality is exactly the circular
lower bound after clearing its denominator. -/
theorem cleared_stepPermuton_truthDistance_upper_bound
    [Fintype Q] [Fintype Ω₁] [Fintype Ω₂] [Fintype S]
    [DecidableEq Q] [DecidableEq Ω₁] [DecidableEq Ω₂] [DecidableEq S]
    [Nonempty Ω₁] [Nonempty Ω₂]
    (hcard : Fintype.card S = 3)
    (truth₁ truth₂ : Q → S) (out₁ : Ω₁ → Q → S) (out₂ : Ω₂ → Q → S)
    (h₁ : WrongChannelLaw truth₁ out₁) (h₂ : WrongChannelLaw truth₂ out₂)
    (n fallingFour : ℕ)
    (hlower : PointwiseLowerBoundWithError (3 * fallingFour) (2 * n ^ 3)
      out₁ out₂) :
    3 * fallingFour * truthDistance truth₁ truth₂ +
        6 * fallingFour * Fintype.card Q ≤
      8 * n ^ 3 * Fintype.card Q := by
  have h := cleared_truthDistance_upper_bound_with_error hcard
    truth₁ truth₂ out₁ out₂ h₁ h₂ (3 * fallingFour) (2 * n ^ 3) hlower
  convert h using 1 <;> ring

/-- Exact uniformity law for random relabelling: every topology channel has
one third of the sample points. -/
structure UniformChannelLaw [Fintype Ω] [DecidableEq S]
    (out : Ω → Q → S) : Prop where
  channel_count (q : Q) (s : S) :
    3 * channelCount (fun ω => out ω q) s = Fintype.card Ω

/-- Number of relabellings disagreeing with a fixed topology at `q`. -/
def pointRelabelDisagreementCount [Fintype Ω] [DecidableEq Ω] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) (q : Q) : ℕ :=
  (Finset.univ.filter fun ω => truth q ≠ out ω q).card

lemma three_mul_pointRelabelDisagreementCount
    [Fintype Ω] [DecidableEq Ω] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) (h : UniformChannelLaw out) (q : Q) :
    3 * pointRelabelDisagreementCount truth out q = 2 * Fintype.card Ω := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Ω)) (fun ω => out ω q = truth q)
  have huniform := h.channel_count q (truth q)
  simp only [channelCount] at huniform
  simp only [pointRelabelDisagreementCount]
  have hpartition' :
      (Finset.univ.filter fun ω : Ω => out ω q = truth q).card +
        (Finset.univ.filter fun ω : Ω => truth q ≠ out ω q).card =
          Fintype.card Ω := by
    simpa [ne_eq, eq_comm] using hpartition
  omega

/-- Quartet distance after one relabelling. -/
def relabelDistance [Fintype Q] [DecidableEq Q] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun q => truth q ≠ out ω q).card

/-- Total distance over all relabellings. -/
def totalRelabelDistance [Fintype Q] [Fintype Ω]
    [DecidableEq Q] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) : ℕ :=
  ∑ ω : Ω, relabelDistance truth out ω

lemma totalRelabelDistance_eq_sum_point
    [Fintype Q] [Fintype Ω] [DecidableEq Q] [DecidableEq Ω] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) :
    totalRelabelDistance truth out =
      ∑ q : Q, pointRelabelDisagreementCount truth out q := by
  classical
  simp_rw [totalRelabelDistance, relabelDistance, pointRelabelDisagreementCount,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Exact integer form of the standard random-labelling expectation
`E distance = (2/3) N`. -/
theorem three_mul_totalRelabelDistance
    [Fintype Q] [Fintype Ω] [DecidableEq Q] [DecidableEq Ω] [DecidableEq S]
    (truth : Q → S) (out : Ω → Q → S) (h : UniformChannelLaw out) :
    3 * totalRelabelDistance truth out = 2 * Fintype.card Ω * Fintype.card Q := by
  rw [totalRelabelDistance_eq_sum_point, Finset.mul_sum]
  calc
    (∑ q : Q, 3 * pointRelabelDisagreementCount truth out q) =
        ∑ _q : Q, 2 * Fintype.card Ω := by
      apply Finset.sum_congr rfl
      intro q hq
      exact three_mul_pointRelabelDisagreementCount truth out h q
    _ = Fintype.card Q * (2 * Fintype.card Ω) :=
      Finset.sum_const_nat fun _ _ => rfl
    _ = 2 * Fintype.card Ω * Fintype.card Q := by ring

/-- Some relabelling attains at least the `2/3` average. -/
theorem exists_relabeling_two_thirds
    [Fintype Q] [Fintype Ω] [DecidableEq Q] [DecidableEq Ω] [DecidableEq S]
    [Nonempty Ω]
    (truth : Q → S) (out : Ω → Q → S) (h : UniformChannelLaw out) :
    ∃ ω : Ω, 2 * Fintype.card Q ≤ 3 * relabelDistance truth out ω := by
  have htotal := three_mul_totalRelabelDistance truth out h
  have hsum :
      (∑ _ω : Ω, 2 * Fintype.card Q) ≤
        ∑ ω : Ω, 3 * relabelDistance truth out ω := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← totalRelabelDistance]
    nlinarith
  obtain ⟨ω, hωmem, hω⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset Ω).Nonempty) hsum
  exact ⟨ω, hω⟩

namespace FourRelabeling

abbrev Four := Fin 4
abbrev Perm4 := Equiv.Perm Four

/-- A labelled topology is determined by the label paired with label `0`.
The subtype has the three possible partners `1`, `2`, and `3`. -/
abbrev Topology := {x : Four // x ≠ 0}

/-- The fixed pairing of the four leaf positions. -/
def opposite : Perm4 := (Equiv.swap 0 2).trans (Equiv.swap 1 3)

lemma opposite_ne_self (i : Four) : opposite i ≠ i := by
  revert i
  decide

/-- Put the four labels into four fixed quartet positions according to `π`,
and return the topology induced by the opposite-position pairing. -/
def topologyOfRelabeling (π : Perm4) : Topology :=
  ⟨π (opposite (π.symm 0)), by
    intro hzero
    have heq : π (opposite (π.symm 0)) = π (π.symm 0) := by
      simpa using hzero
    exact opposite_ne_self (π.symm 0) (π.injective heq)⟩

theorem card_permutations : Fintype.card Perm4 = 24 := by decide

theorem card_topologies : Fintype.card Topology = 3 := by decide

/-- The exact `8/24` enumeration: each of the three labelled quartet
topologies is induced by eight of the twenty-four assignments. -/
theorem topologyOfRelabeling_fiber_card (s : Topology) :
    channelCount topologyOfRelabeling s = 8 := by
  revert s
  decide

/-- Cleared uniformity statement corresponding to `8/24 = 1/3`. -/
theorem topologyOfRelabeling_uniform (s : Topology) :
    3 * channelCount topologyOfRelabeling s = Fintype.card Perm4 := by
  rw [topologyOfRelabeling_fiber_card, card_permutations]

end FourRelabeling

end QuartetDistance.Counting
