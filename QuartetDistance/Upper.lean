import QuartetDistance.Arithmetic
import QuartetDistance.Circular
import QuartetDistance.Counting
import QuartetDistance.Tree

/-!
# The finite Bandelt--Dress upper bound

This file glues the tree rotation law to the circular-order collision bound.
The only external input is `Circular.StepPermutonTheorem n`.
-/

namespace QuartetDistance.Upper

open scoped BigOperators

abbrev Quartet (n : ℕ) := {Q : Finset (Fin n) // Q.card = 4}

@[simp] theorem card_quartet (n : ℕ) :
    Fintype.card (Quartet n) = Nat.choose n 4 := by
  simp [Quartet]

/-! ## A fixed three-channel encoding of quartet splits -/

/-- The three perfect matchings of four canonical slots. -/
def canonicalTopology : Fin 3 → Circular.QuartetSplit Circular.Four :=
  ![Circular.splitOf 0 1 2 3,
    Circular.splitOf 0 2 1 3,
    Circular.splitOf 0 1 3 2]

theorem canonicalTopology_injective : Function.Injective canonicalTopology := by
  decide

/-- The increasing enumeration of a label quartet. -/
def quartetEmbedding (q : Quartet n) : Circular.Four ↪ Fin n :=
  Circular.enumerateFour q.1 q.2

/-- Decode one of the fixed three channels as a split of `q`. -/
def splitOfTopology (q : Quartet n) (i : Fin 3) :
    Circular.QuartetSplit (Fin n) :=
  Circular.mapSplit (quartetEmbedding q) (canonicalTopology i)

theorem splitOfTopology_injective (q : Quartet n) :
    Function.Injective (splitOfTopology q) := by
  intro i j hij
  exact canonicalTopology_injective (Circular.mapSplit_injective (quartetEmbedding q) hij)

/-- Encode a split as one of three channels.  On well-formed splits of `q`,
the final branch is exactly the third matching. -/
def topologyOfSplit (q : Quartet n) (s : Circular.QuartetSplit (Fin n)) : Fin 3 :=
  if s = splitOfTopology q 0 then 0
  else if s = splitOfTopology q 1 then 1
  else 2

@[simp] theorem topologyOfSplit_splitOfTopology (q : Quartet n) (i : Fin 3) :
    topologyOfSplit q (splitOfTopology q i) = i := by
  fin_cases i
  · simp [topologyOfSplit]
  · have h10 : splitOfTopology q 1 ≠ splitOfTopology q 0 :=
      (splitOfTopology_injective q).ne (by decide)
    simp [topologyOfSplit, h10]
  · have h20 : splitOfTopology q 2 ≠ splitOfTopology q 0 :=
      (splitOfTopology_injective q).ne (by decide)
    have h21 : splitOfTopology q 2 ≠ splitOfTopology q 1 :=
      (splitOfTopology_injective q).ne (by decide)
    simp [topologyOfSplit, h20, h21]

theorem topologyOfSplit_eq_iff_of_mem_range (q : Quartet n)
    {s : Circular.QuartetSplit (Fin n)}
    (hs : s ∈ Set.range (splitOfTopology q)) (i : Fin 3) :
    topologyOfSplit q s = i ↔ s = splitOfTopology q i := by
  obtain ⟨j, rfl⟩ := hs
  simp only [topologyOfSplit_splitOfTopology]
  exact (splitOfTopology_injective q).eq_iff.symm

/-- Regard any enumeration with range `q` as an equivalence onto `q`. -/
noncomputable def enumerationEquiv (q : Quartet n) (r : Circular.Four ↪ Fin n)
    (hr : q.1 = Finset.univ.map r) : Circular.Four ≃ q.1 :=
  Equiv.ofBijective
    (fun i => (⟨r i, by rw [hr]; simp⟩ : q.1))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      fun _ _ h => r.injective (Subtype.ext_iff.mp h), by simp [q.2]⟩)

/-- The permutation comparing an arbitrary enumeration of `q` with its
increasing enumeration. -/
noncomputable def enumerationPermutation (q : Quartet n) (r : Circular.Four ↪ Fin n)
    (hr : q.1 = Finset.univ.map r) : Circular.Perm4 :=
  (enumerationEquiv q r hr).trans (q.1.orderIsoOfFin q.2).toEquiv.symm

theorem enumeration_eq_permutation_trans (q : Quartet n)
    (r : Circular.Four ↪ Fin n) (hr : q.1 = Finset.univ.map r) :
    r = (enumerationPermutation q r hr).toEmbedding.trans (quartetEmbedding q) := by
  ext i
  simp [enumerationPermutation, enumerationEquiv, quartetEmbedding,
    Circular.enumerateFour]

theorem permutedCanonical_mem_range (σ : Circular.Perm4) :
    Circular.mapSplit σ.toEmbedding Circular.canonicalCrossing ∈
      Set.range canonicalTopology := by
  revert σ
  decide

/-- Every well-formed split of `q` is one of the fixed three channels. -/
theorem isQuartetSplit_mem_range (q : Quartet n)
    {s : Circular.QuartetSplit (Fin n)}
    (hs : Circular.IsQuartetSplit q.1 s) :
    s ∈ Set.range (splitOfTopology q) := by
  obtain ⟨r, hr, rfl⟩ := hs
  let σ := enumerationPermutation q r hr
  have her : r = σ.toEmbedding.trans (quartetEmbedding q) :=
    enumeration_eq_permutation_trans q r hr
  obtain ⟨i, hi⟩ := permutedCanonical_mem_range σ
  refine ⟨i, ?_⟩
  rw [her, Circular.crossing_comp, ← hi]
  rfl

/-! ## Circular orders as three-channel functions -/

theorem crossingOnLabels_isQuartetSplit (C : Circular.CircularOrder n)
    (q : Quartet n) :
    Circular.IsQuartetSplit q.1 (Circular.crossingOnLabels C q.1 q.2) := by
  let p := Circular.labelPositions C q.1
  let hp : p.card = 4 := by simp [p]
  let r : Circular.Four ↪ Fin n :=
    (Circular.enumerateFour p hp).trans C.toEmbedding
  have hrange : Finset.univ.map r = q.1 := by
    calc
      Finset.univ.map r =
          (Finset.univ.map (Circular.enumerateFour p hp)).map C.toEmbedding := by
            exact (Finset.map_map _ _ _).symm
      _ = p.map C.toEmbedding := by rw [Circular.range_enumerateFour]
      _ = q.1 := by
        ext x
        simp [p, Circular.labelPositions]
  exact ⟨r, hrange.symm, rfl⟩

/-- The channel selected by a circular order on a fixed label quartet. -/
noncomputable def crossingTopology (C : Circular.CircularOrder n)
    (q : Quartet n) : Fin 3 :=
  topologyOfSplit q (Circular.crossingOnLabels C q.1 q.2)

theorem crossingTopology_eq_iff (C C' : Circular.CircularOrder n)
    (q : Quartet n) :
    crossingTopology C q = crossingTopology C' q ↔
      Circular.crossingOnLabels C q.1 q.2 =
        Circular.crossingOnLabels C' q.1 q.2 := by
  have hC := isQuartetSplit_mem_range q (crossingOnLabels_isQuartetSplit C q)
  have hC' := isQuartetSplit_mem_range q (crossingOnLabels_isQuartetSplit C' q)
  obtain ⟨i, hi⟩ := hC
  obtain ⟨j, hj⟩ := hC'
  unfold crossingTopology
  rw [← hi, ← hj]
  simp [(splitOfTopology_injective q).eq_iff]

/-- Counting equal channels over the quartet subtype is exactly `Circular.K`. -/
theorem card_crossingTopology_eq_K (C C' : Circular.CircularOrder n) :
    (Finset.univ.filter fun q : Quartet n =>
      crossingTopology C q = crossingTopology C' q).card = Circular.K C C' := by
  classical
  rw [← Circular.labelK_eq_K]
  unfold Circular.labelK
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨q.2, ⟨q.2, (crossingTopology_eq_iff C C' q).mp hq⟩⟩
  · intro q₁ _ q₂ _ hq
    exact Subtype.ext hq
  · intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      at hQ
    let q : Quartet n := ⟨Q, hQ.1⟩
    refine ⟨q, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (crossingTopology_eq_iff C C' q).mpr hQ.2.choose_spec

/-! ## The circular lower bound in cleared natural-number form -/

/-- The numerator of `stepAlpha` after cancelling its leading factor `n`. -/
def cyclicFallingThree (n : ℕ) : ℕ := (n - 1) * (n - 2) * (n - 3)

theorem stepAlpha_eq_cyclicFallingThree_div (n : ℕ) (hn : 4 ≤ n) :
    Circular.stepAlpha n =
      (cyclicFallingThree n : ℚ) / (n : ℚ) ^ 3 := by
  simp only [Circular.stepAlpha, cyclicFallingThree, Nat.cast_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n)]
  norm_num

/-- The step-permuton circular estimate with all denominators cleared. -/
theorem circular_cleared_lower_bound {n : ℕ}
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n)
    (C C' : Circular.CircularOrder n) :
    3 * cyclicFallingThree n * Nat.choose n 4 ≤
      3 * cyclicFallingThree n * Circular.K C C' +
        2 * n ^ 3 * Nat.choose n 4 := by
  have hg : 0 < cyclicFallingThree n := by
    have h1 : 0 < n - 1 := by omega
    have h2 : 0 < n - 2 := by omega
    have h3 : 0 < n - 3 := by omega
    simp only [cyclicFallingThree]
    positivity
  have h := Circular.circularOrderBound hpublished C C' hn
  rw [stepAlpha_eq_cyclicFallingThree_div n hn] at h
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have hgq : (cyclicFallingThree n : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hcoeff :
      1 - 2 / (3 * ((cyclicFallingThree n : ℚ) / (n : ℚ) ^ 3)) =
        (3 * (cyclicFallingThree n : ℚ) - 2 * (n : ℚ) ^ 3) /
          (3 * (cyclicFallingThree n : ℚ)) := by
    field_simp [hnq, hgq]
  rw [hcoeff] at h
  have hden : (0 : ℚ) < 3 * (cyclicFallingThree n : ℚ) := by positivity
  have hq :
      3 * (cyclicFallingThree n : ℚ) * (Nat.choose n 4 : ℚ) ≤
        3 * (cyclicFallingThree n : ℚ) * (Circular.K C C' : ℚ) +
          2 * (n : ℚ) ^ 3 * (Nat.choose n 4 : ℚ) := by
    have hmul :
        (3 * (cyclicFallingThree n : ℚ) - 2 * (n : ℚ) ^ 3) *
            (Nat.choose n 4 : ℚ) ≤
          (3 * (cyclicFallingThree n : ℚ)) * (Circular.K C C' : ℚ) := by
      have hdiv :
          ((3 * (cyclicFallingThree n : ℚ) - 2 * (n : ℚ) ^ 3) *
              (Nat.choose n 4 : ℚ)) /
              (3 * (cyclicFallingThree n : ℚ)) ≤
            (Circular.K C C' : ℚ) := by
        convert h using 1 ; ring
      have h' := (div_le_iff₀ hden).mp hdiv
      simpa only [mul_comm] using h'
    linarith
  exact_mod_cast hq

theorem crossingTopology_pointwiseLowerBoundWithError
    {n : ℕ} {Ω₁ Ω₂ : Type*}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Ω₁] [DecidableEq Ω₂]
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n)
    (order₁ : Ω₁ → Circular.CircularOrder n)
    (order₂ : Ω₂ → Circular.CircularOrder n) :
    Counting.PointwiseLowerBoundWithError
      (Q := Quartet n) (S := Fin 3)
      (3 * cyclicFallingThree n) (2 * n ^ 3)
      (fun ω q => crossingTopology (order₁ ω) q)
      (fun ω q => crossingTopology (order₂ ω) q) := by
  intro ω₁ ω₂
  unfold Counting.sampledK
  rw [card_crossingTopology_eq_K]
  simpa only [card_quartet] using
    circular_cleared_lower_bound hpublished hn (order₁ ω₁) (order₂ ω₂)

/-! ## Arithmetic normalization to the displayed paper bound -/

theorem twentyFour_mul_choose_eq_n_mul_cyclicFallingThree (n : ℕ) :
    24 * Nat.choose n 4 = n * cyclicFallingThree n := by
  simpa only [quartetCount, cyclicFallingThree, mul_assoc] using
    twentyFour_mul_quartetCount n

theorem choose_add_collision_error (n : ℕ) (hn : 4 ≤ n) :
    24 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) = n ^ 4 := by
  have hp : 11 * n ≤ 6 * n ^ 2 := by nlinarith
  have hfallZ :
      (24 : ℤ) * (Nat.choose n 4 : ℤ) =
        (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
    have h := congrArg (fun k : ℕ => (k : ℤ))
      (twentyFour_mul_quartetCount n)
    simp only [quartetCount, Nat.cast_mul] at h
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_sub (by omega : 3 ≤ n)] at h
    norm_num at h ⊢
    exact h
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub hp]
  norm_num
  rw [hfallZ]
  ring

/-- Normalize the direct output of `Counting` to the integer inequality
displayed in the paper. -/
theorem paper_cleared_bound_of_counting_bound {n D : ℕ} (hn : 4 ≤ n)
    (hcount :
      3 * cyclicFallingThree n * D +
          6 * cyclicFallingThree n * Nat.choose n 4 ≤
        8 * n ^ 3 * Nat.choose n 4) :
    9 * D ≤
      6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) := by
  have hg : 0 < cyclicFallingThree n := by
    simp only [cyclicFallingThree]
    have h1 : 0 < n - 1 := by omega
    have h2 : 0 < n - 2 := by omega
    have h3 : 0 < n - 3 := by omega
    positivity
  have hfall := twentyFour_mul_choose_eq_n_mul_cyclicFallingThree n
  have hmul :
      cyclicFallingThree n *
          (9 * D + 18 * Nat.choose n 4) ≤
        cyclicFallingThree n * n ^ 4 := by
    calc
      cyclicFallingThree n * (9 * D + 18 * Nat.choose n 4) =
          3 * (3 * cyclicFallingThree n * D +
            6 * cyclicFallingThree n * Nat.choose n 4) := by ring
      _ ≤ 3 * (8 * n ^ 3 * Nat.choose n 4) := Nat.mul_le_mul_left 3 hcount
      _ = n ^ 3 * (24 * Nat.choose n 4) := by ring
      _ = cyclicFallingThree n * n ^ 4 := by rw [hfall]; ring
  have hcore : 9 * D + 18 * Nat.choose n 4 ≤ n ^ 4 :=
    Nat.le_of_mul_le_mul_left hmul hg
  have hid := choose_add_collision_error n hn
  omega

theorem paper_rational_bound_of_cleared {n D : ℕ} (hn : 4 ≤ n)
    (hcleared :
      9 * D ≤ 6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6)) :
    (D : ℚ) ≤
      (2 : ℚ) / 3 * (Nat.choose n 4 : ℚ) +
        (n : ℚ) * (6 * (n : ℚ) ^ 2 - 11 * (n : ℚ) + 6) / 9 := by
  have hp : 11 * n ≤ 6 * n ^ 2 := by nlinarith
  have hq :
      ((9 * D : ℕ) : ℚ) ≤
        ((6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) : ℕ) : ℚ) := by
    exact_mod_cast hcleared
  simp only [Nat.cast_add, Nat.cast_mul] at hq
  rw [Nat.cast_sub hp] at hq
  norm_num at hq ⊢
  linarith

/-! ## The concrete rotation sample of a phylogenetic tree -/

/-- A single global enumeration of the rotation multiset. -/
noncomputable def boundaryProfileVector (T : Tree.PhyloTree (Fin n)) :
    List.Vector (List (Fin n)) T.boundaryProfile.card :=
  ⟨T.boundaryProfile.toList, by simp⟩

/-- Rotation systems are positions in that one global enumeration. -/
abbrev RotationSample (T : Tree.PhyloTree (Fin n)) :=
  Fin T.boundaryProfile.card

/-- The boundary word at a sampled rotation system. -/
noncomputable def rotationWord (T : Tree.PhyloTree (Fin n)) (ω : RotationSample T) :
    List (Fin n) :=
  (boundaryProfileVector T).get ω

theorem rotationWord_mem_boundaryProfile (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) : rotationWord T ω ∈ T.boundaryProfile := by
  have hm : rotationWord T ω ∈ T.boundaryProfile.toList := by
    exact List.get_mem _ _
  simpa [Multiset.mem_toList] using hm

theorem rotationWord_nodup (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) : (rotationWord T ω).Nodup :=
  T.mem_boundaryProfile_nodup (rotationWord_mem_boundaryProfile T ω)

theorem rotationWord_complete (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) (x : Fin n) : x ∈ rotationWord T ω := by
  have hm := rotationWord_mem_boundaryProfile T ω
  simp only [Tree.PhyloTree.boundaryProfile, Multiset.mem_map] at hm
  obtain ⟨ys, hys, hword⟩ := hm
  rw [← hword]
  by_cases hx : x = T.root
  · simp [hx]
  · let y : {a : Fin n // a ≠ T.root} := ⟨x, hx⟩
    have hp := T.crown.mem_frontierProfile_perm hys
    have hy : y ∈ ys := hp.mem_iff.mpr (T.exhaustive y)
    simp only [List.mem_cons, List.mem_map]
    exact Or.inr ⟨y, hy, rfl⟩

@[simp] theorem rotationWord_length (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) : (rotationWord T ω).length = n := by
  have hfinset : (rotationWord T ω).toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => by
      simpa using rotationWord_complete T ω x
  calc
    (rotationWord T ω).length = (rotationWord T ω).toFinset.card :=
      (List.toFinset_card_of_nodup (rotationWord_nodup T ω)).symm
    _ = n := by rw [hfinset]; simp

/-- The actual circular order produced by a sampled rotation system. -/
noncomputable def rotationOrder (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) : Circular.CircularOrder n :=
  Circular.circularOrderOfList (rotationWord T ω)
    (rotationWord_nodup T ω) (rotationWord_complete T ω)
    (rotationWord_length T ω)

@[simp] theorem circularOrderList_rotationOrder (T : Tree.PhyloTree (Fin n))
    (ω : RotationSample T) :
    Circular.circularOrderList (rotationOrder T ω) = rotationWord T ω := by
  let l := rotationWord T ω
  let hlength : l.length = n := rotationWord_length T ω
  change List.ofFn
      (fun i : Fin n => l.get (Fin.cast hlength.symm i)) = l
  rw [← List.ofFn_congr hlength l.get]
  exact List.ofFn_get l

instance rotationSampleNonempty (T : Tree.PhyloTree (Fin n)) :
    Nonempty (RotationSample T) := by
  refine ⟨⟨0, ?_⟩⟩
  simp

/-- Fiber counts over the concrete `Fin` sample are multiset counts in the
global boundary profile. -/
theorem channelCount_rotationSample (T : Tree.PhyloTree (Fin n))
    {S : Type*} [DecidableEq S] (f : List (Fin n) → S) (s : S) :
    Counting.channelCount (fun ω : RotationSample T => f (rotationWord T ω)) s =
      (T.boundaryProfile.map f).count s := by
  have h := Fin.card_filter_univ_eq_vector_get_eq_count s
    ((boundaryProfileVector T).map f)
  have hcount :
      List.count s (List.map f T.boundaryProfile.toList) =
        (T.boundaryProfile.map f).count s := by
    rw [← Multiset.coe_count]
    congr 1
    change Multiset.map f (↑T.boundaryProfile.toList : Multiset (List (Fin n))) =
      Multiset.map f T.boundaryProfile
    exact congrArg (Multiset.map f) (Multiset.coe_toList T.boundaryProfile)
  simpa [Counting.channelCount, rotationWord, boundaryProfileVector, hcount] using h

theorem crossingList_isQuartetSplit {α : Type*} [DecidableEq α]
    (l : List α) (hlength : l.length = 4) (hnodup : l.Nodup) :
    Circular.IsQuartetSplit l.toFinset (Tree.FullTree.crossingList l) := by
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlength
  let r : Circular.Four ↪ α :=
    ⟨![a, b, c, d], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  refine ⟨r, ?_, ?_⟩
  · ext x
    simp [r]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  · simpa [r] using Tree.FullTree.crossingList_of_embedding r

theorem finRange_filter_mem_eq_sort (s : Finset (Fin n)) :
    (List.finRange n).filter (fun i => i ∈ s) = s.sort (· ≤ ·) := by
  have hp :
      List.Perm ((List.finRange n).filter (fun i => i ∈ s)) (s.sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange n).filter _) (Finset.sort_nodup s _)).2
    intro i
    simp
  have hslt : List.Pairwise (· < ·)
      ((List.finRange n).filter (fun i => i ∈ s)) :=
    (List.sortedLT_finRange n).pairwise.filter _
  have hsle : List.Pairwise (· ≤ ·)
      ((List.finRange n).filter (fun i => i ∈ s)) :=
    hslt.imp fun h => le_of_lt h
  exact hp.eq_of_sortedLE hsle.sortedLE (s.sortedLT_sort.sortedLE)

theorem ofFn_enumerateFour_eq_sort (s : Finset (Fin n)) (h : s.card = 4) :
    List.ofFn (Circular.enumerateFour s h) = s.sort (· ≤ ·) := by
  have hlength : (s.sort (· ≤ ·)).length = 4 := by simp [h]
  calc
    List.ofFn (Circular.enumerateFour s h) =
        List.ofFn (fun i : Fin 4 =>
          (s.sort (· ≤ ·)).get (Fin.cast hlength.symm i)) := by
      apply congrArg List.ofFn
      funext i
      simp [Circular.enumerateFour, Finset.orderEmbOfFin_apply]
    _ = List.ofFn (s.sort (· ≤ ·)).get :=
      (List.ofFn_congr hlength (s.sort (· ≤ ·)).get).symm
    _ = s.sort (· ≤ ·) := List.ofFn_get _

theorem restrict_circularOrderList_eq_ofFn_crossingEmbedding
    (C : Circular.CircularOrder n) (Q : Finset (Fin n)) (hQ : Q.card = 4) :
    Tree.FullTree.restrictList Q (Circular.circularOrderList C) =
      List.ofFn
        ((Circular.enumerateFour (Circular.labelPositions C Q)
          (by simpa using hQ)).trans C.toEmbedding) := by
  let p := Circular.labelPositions C Q
  have hp : p.card = 4 := by simpa [p] using hQ
  have hpred :
      (fun i : Fin n => decide (C i ∈ Q)) =
        (fun i : Fin n => decide (i ∈ p)) := by
    funext i
    simp [p, Circular.labelPositions]
  unfold Tree.FullTree.restrictList Circular.circularOrderList
  rw [List.ofFn_eq_map, List.filter_map]
  change List.map C ((List.finRange n).filter fun i => C i ∈ Q) = _
  rw [hpred, finRange_filter_mem_eq_sort]
  rw [← ofFn_enumerateFour_eq_sort p hp]
  exact List.ofFn_comp' _ _ |>.symm

theorem crossingOnLabels_eq_crossingList_restrict_circularOrderList
    (C : Circular.CircularOrder n) (Q : Finset (Fin n)) (hQ : Q.card = 4) :
    Circular.crossingOnLabels C Q hQ =
      Tree.FullTree.crossingList
        (Tree.FullTree.restrictList Q (Circular.circularOrderList C)) := by
  rw [restrict_circularOrderList_eq_ofFn_crossingEmbedding C Q hQ]
  let r : Circular.Four ↪ Fin n :=
    (Circular.enumerateFour (Circular.labelPositions C Q)
      (by simpa using hQ)).trans C.toEmbedding
  change Circular.crossing r =
    Tree.FullTree.crossingList [r 0, r 1, r 2, r 3]
  exact (Tree.FullTree.crossingList_of_embedding r).symm

@[simp] theorem crossingOnLabels_rotationOrder
    (T : Tree.PhyloTree (Fin n)) (ω : RotationSample T) (q : Quartet n) :
    Circular.crossingOnLabels (rotationOrder T ω) q.1 q.2 =
      Tree.FullTree.crossingList
        (Tree.FullTree.restrictList q.1 (rotationWord T ω)) := by
  rw [crossingOnLabels_eq_crossingList_restrict_circularOrderList,
    circularOrderList_rotationOrder]

theorem restrictedCrossing_isQuartetSplit (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) (ω : RotationSample T) :
    Circular.IsQuartetSplit q.1
      (Tree.FullTree.crossingList
        (Tree.FullTree.restrictList q.1 (rotationWord T ω))) := by
  let l := Tree.FullTree.restrictList q.1 (rotationWord T ω)
  have hlength : l.length = 4 :=
    T.restrictList_boundary_length q.1 q.2 (rotationWord_mem_boundaryProfile T ω)
  have hnodup : l.Nodup := (rotationWord_nodup T ω).filter _
  have hfinset : l.toFinset = q.1 := by
    ext x
    simp [l, Tree.FullTree.restrictList, rotationWord_complete T ω x]
  simpa only [l, hfinset] using crossingList_isQuartetSplit l hlength hnodup

theorem blockSplit_isQuartetSplit {α : Type*} [DecidableEq α]
    (a b c d : α) (h : [a, b, c, d].Nodup) :
    Circular.IsQuartetSplit ({a, b, c, d} : Finset α)
      (Tree.FullTree.blockSplit a b c d) := by
  let r : Circular.Four ↪ α :=
    ⟨![a, c, b, d], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  refine ⟨r, ?_, ?_⟩
  · ext x
    simp [r]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  · simp [r, Tree.FullTree.blockSplit, Circular.crossing,
      Circular.canonicalCrossing, Circular.mapSplit, Circular.splitOf,
      Circular.pair]

theorem displayedSplit_isQuartetSplit {α : Type*} [DecidableEq α]
    (t : Tree.FullTree α) (hlength : t.leaves.length = 4)
    (hnodup : t.leaves.Nodup) :
    Circular.IsQuartetSplit t.leaves.toFinset t.displayedSplit := by
  obtain ⟨a, b, c, d, hs⟩ := t.shape_of_leaves_length_eq_four hlength
  rcases hs with hs | hs | hs | hs | hs
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [Tree.FullTree.leaves] using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_three a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [Tree.FullTree.leaves] using hnodup
    have hn' : [a, d, b, c].Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hn ⊢
      aesop
    have hset : ({a, d, b, c} : Finset α) = {a, b, c, d} := by
      ext x
      simp
      aesop
    rw [Tree.FullTree.displayedSplit_shape_one_twone a b c d hn]
    have hi := blockSplit_isQuartetSplit a d b c hn'
    rw [hset] at hi
    simpa [Tree.FullTree.leaves] using hi
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [Tree.FullTree.leaves] using hnodup
    rw [Tree.FullTree.displayedSplit_shape_two_two a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [Tree.FullTree.leaves] using hnodup
    have hn' : [a, d, b, c].Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hn ⊢
      aesop
    have hset : ({a, d, b, c} : Finset α) = {a, b, c, d} := by
      ext x
      simp
      aesop
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one a b c d hn]
    have hi := blockSplit_isQuartetSplit a d b c hn'
    rw [hset] at hi
    simpa [Tree.FullTree.leaves] using hi
  · subst t
    have hn : [a, b, c, d].Nodup := by simpa [Tree.FullTree.leaves] using hnodup
    rw [Tree.FullTree.displayedSplit_shape_three_one a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn

theorem restrictedTree_leaves_toFinset (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) : (T.restrictedTree q.1 q.2).leaves.toFinset = q.1 := by
  rw [T.restrictedTree_leaves]
  ext x
  simp [Tree.FullTree.restrictList, T.mem_referenceLeaves x]

theorem displayedSplitOn_isQuartetSplit (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) :
    Circular.IsQuartetSplit q.1 (T.displayedSplitOn q.1 q.2) := by
  have h := displayedSplit_isQuartetSplit (T.restrictedTree q.1 q.2)
    (T.restrictedTree_leaves_length q.1 q.2)
    (T.restrictedTree_nodup q.1 q.2)
  simpa [Tree.PhyloTree.displayedSplitOn, restrictedTree_leaves_toFinset T q] using h

theorem mem_validSplitsOn_isQuartetSplit (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) {s : Circular.QuartetSplit (Fin n)}
    (hs : s ∈ T.validSplitsOn q.1 q.2) : Circular.IsQuartetSplit q.1 s := by
  let R := T.restrictedTree q.1 q.2
  obtain ⟨a, b, c, d, hleaves⟩ :=
    List.length_eq_four.mp (T.restrictedTree_leaves_length q.1 q.2)
  have hn : [a, b, c, d].Nodup := by
    rw [← hleaves]
    exact T.restrictedTree_nodup q.1 q.2
  have hset : ({a, b, c, d} : Finset (Fin n)) = q.1 := by
    calc
      ({a, b, c, d} : Finset (Fin n)) = [a, b, c, d].toFinset := by simp
      _ = (T.restrictedTree q.1 q.2).leaves.toFinset :=
        congrArg List.toFinset hleaves.symm
      _ = q.1 := restrictedTree_leaves_toFinset T q
  simp only [Tree.PhyloTree.validSplitsOn, Tree.FullTree.allQuartetSplits,
    hleaves, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · simpa [hset] using blockSplit_isQuartetSplit a b c d hn
  · have hn' : [a, c, b, d].Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hn ⊢
      aesop
    have hset' : ({a, c, b, d} : Finset (Fin n)) = q.1 := by
      calc
        ({a, c, b, d} : Finset (Fin n)) = {a, b, c, d} := by
          ext x
          simp
          aesop
        _ = q.1 := hset
    have hi := blockSplit_isQuartetSplit a c b d hn'
    rw [hset'] at hi
    exact hi
  · have hn' : [a, d, b, c].Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hn ⊢
      aesop
    have hset' : ({a, d, b, c} : Finset (Fin n)) = q.1 := by
      calc
        ({a, d, b, c} : Finset (Fin n)) = {a, b, c, d} := by
          ext x
          simp
          aesop
        _ = q.1 := hset
    have hi := blockSplit_isQuartetSplit a d b c hn'
    rw [hset'] at hi
    exact hi

theorem card_validSplitsOn (T : Tree.PhyloTree (Fin n)) (q : Quartet n) :
    (T.validSplitsOn q.1 q.2).card = 3 := by
  obtain ⟨a, b, c, d, hleaves⟩ :=
    List.length_eq_four.mp (T.restrictedTree_leaves_length q.1 q.2)
  have hn : [a, b, c, d].Nodup := by
    rw [← hleaves]
    exact T.restrictedTree_nodup q.1 q.2
  simp [Tree.PhyloTree.validSplitsOn, hleaves, Tree.FullTree.allQuartetSplits,
    Tree.FullTree.blockSplit_ab_ne_ac a b c d hn,
    Tree.FullTree.blockSplit_ab_ne_ad a b c d hn,
    Tree.FullTree.blockSplit_ac_ne_ad a b c d hn]

/-- The finset form of the fixed three-channel range. -/
def topologySplits (q : Quartet n) : Finset (Circular.QuartetSplit (Fin n)) :=
  Finset.univ.map ⟨splitOfTopology q, splitOfTopology_injective q⟩

@[simp] theorem card_topologySplits (q : Quartet n) :
    (topologySplits q).card = 3 := by simp [topologySplits]

theorem validSplitsOn_eq_topologySplits (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) : T.validSplitsOn q.1 q.2 = topologySplits q := by
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    obtain ⟨i, rfl⟩ := isQuartetSplit_mem_range q
      (mem_validSplitsOn_isQuartetSplit T q hs)
    simp [topologySplits]
  · rw [card_topologySplits, card_validSplitsOn]

theorem isQuartetSplit_mem_validSplitsOn (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) {s : Circular.QuartetSplit (Fin n)}
    (hs : Circular.IsQuartetSplit q.1 s) : s ∈ T.validSplitsOn q.1 q.2 := by
  rw [validSplitsOn_eq_topologySplits]
  obtain ⟨i, rfl⟩ := isQuartetSplit_mem_range q hs
  simp [topologySplits]

theorem canonicalTopology_eq_permutedCanonical (i : Fin 3) :
    ∃ σ : Circular.Perm4,
      canonicalTopology i =
        Circular.mapSplit σ.toEmbedding Circular.canonicalCrossing := by
  fin_cases i <;> decide

theorem splitOfTopology_isQuartetSplit (q : Quartet n) (i : Fin 3) :
    Circular.IsQuartetSplit q.1 (splitOfTopology q i) := by
  obtain ⟨σ, hσ⟩ := canonicalTopology_eq_permutedCanonical i
  let r : Circular.Four ↪ Fin n := σ.toEmbedding.trans (quartetEmbedding q)
  refine ⟨r, ?_, ?_⟩
  · rw [show Finset.univ.map r =
        (Finset.univ.map σ.toEmbedding).map (quartetEmbedding q) by
      exact (Finset.map_map _ _ _).symm]
    simp [quartetEmbedding, Circular.range_enumerateFour]
  · rw [show Circular.crossing r =
        Circular.mapSplit (quartetEmbedding q)
          (Circular.mapSplit σ.toEmbedding Circular.canonicalCrossing) by
      exact Circular.crossing_comp (quartetEmbedding q) σ]
    rw [← hσ]
    rfl

theorem mem_restrictedCrossingProfile_isQuartetSplit
    (T : Tree.PhyloTree (Fin n)) (q : Quartet n)
    {s : Circular.QuartetSplit (Fin n)}
    (hs : s ∈ T.restrictedCrossingProfile q.1) :
    Circular.IsQuartetSplit q.1 s := by
  simp only [Tree.PhyloTree.restrictedCrossingProfile, Multiset.mem_map] at hs
  obtain ⟨xs, hxs, rfl⟩ := hs
  let l := Tree.FullTree.restrictList q.1 xs
  have hlength : l.length = 4 :=
    T.restrictList_boundary_length q.1 q.2 hxs
  have hnodup : l.Nodup := (T.mem_boundaryProfile_nodup hxs).filter _
  have hfinset : l.toFinset = q.1 := by
    ext x
    simp [l, Tree.FullTree.restrictList, T.mem_boundaryProfile_complete hxs x]
  simpa only [l, hfinset] using crossingList_isQuartetSplit l hlength hnodup

theorem topologyOfSplit_injOn_restrictedCrossingProfile
    (T : Tree.PhyloTree (Fin n)) (q : Quartet n) :
    Set.InjOn (topologyOfSplit q)
      {s : Circular.QuartetSplit (Fin n) | s ∈ T.restrictedCrossingProfile q.1} := by
  intro s hs t ht heq
  obtain ⟨i, hi⟩ := isQuartetSplit_mem_range q
    (mem_restrictedCrossingProfile_isQuartetSplit T q hs)
  obtain ⟨j, hj⟩ := isQuartetSplit_mem_range q
    (mem_restrictedCrossingProfile_isQuartetSplit T q ht)
  rw [← hi, ← hj] at heq ⊢
  simpa only [topologyOfSplit_splitOfTopology] using
    congrArg (splitOfTopology q) heq

theorem count_mapped_restrictedCrossingProfile
    (T : Tree.PhyloTree (Fin n)) (q : Quartet n) (i : Fin 3) :
    ((T.restrictedCrossingProfile q.1).map (topologyOfSplit q)).count i =
      (T.restrictedCrossingProfile q.1).count (splitOfTopology q i) := by
  let B := T.restrictedCrossingProfile q.1
  by_cases hi : splitOfTopology q i ∈ B
  · have h := Multiset.count_map_eq_count (topologyOfSplit q) B
      (topologyOfSplit_injOn_restrictedCrossingProfile T q)
      (splitOfTopology q i) hi
    simpa only [topologyOfSplit_splitOfTopology] using h
  · rw [Multiset.count_eq_zero_of_notMem hi, Multiset.count_eq_zero]
    intro hm
    obtain ⟨s, hs, hsi⟩ := Multiset.mem_map.mp hm
    have hr := isQuartetSplit_mem_range q
      (mem_restrictedCrossingProfile_isQuartetSplit T q hs)
    have heq : s = splitOfTopology q i :=
      (topologyOfSplit_eq_iff_of_mem_range q hr i).mp hsi
    exact hi (heq ▸ hs)

theorem channelCount_rotationTopology (T : Tree.PhyloTree (Fin n))
    (q : Quartet n) (i : Fin 3) :
    Counting.channelCount
        (fun ω : RotationSample T => crossingTopology (rotationOrder T ω) q) i =
      (T.restrictedCrossingProfile q.1).count (splitOfTopology q i) := by
  let f : List (Fin n) → Fin 3 := fun xs =>
    topologyOfSplit q
      (Tree.FullTree.crossingList (Tree.FullTree.restrictList q.1 xs))
  calc
    Counting.channelCount
        (fun ω : RotationSample T => crossingTopology (rotationOrder T ω) q) i =
        Counting.channelCount (fun ω : RotationSample T => f (rotationWord T ω)) i := by
      congr 1
      funext ω
      simp [f, crossingTopology]
    _ = (T.boundaryProfile.map f).count i := channelCount_rotationSample T f i
    _ = ((T.restrictedCrossingProfile q.1).map (topologyOfSplit q)).count i := by
      simp [f, Tree.PhyloTree.restrictedCrossingProfile, Multiset.map_map]
    _ = (T.restrictedCrossingProfile q.1).count (splitOfTopology q i) :=
      count_mapped_restrictedCrossingProfile T q i

/-! ## Displayed topologies and quartet distance -/

/-- The displayed quartet split, encoded in the fixed `Fin 3` coordinates of
the increasing enumeration of the quartet. -/
def displayedTopology (T : Tree.PhyloTree (Fin n)) (q : Quartet n) : Fin 3 :=
  topologyOfSplit q (T.displayedSplitOn q.1 q.2)

/-- Quartet distance between two concrete phylogenetic trees. -/
def quartetDistance (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℕ :=
  Counting.truthDistance (displayedTopology T₁) (displayedTopology T₂)

theorem quartetDistance_le_choose (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    quartetDistance T₁ T₂ ≤ Nat.choose n 4 := by
  calc
    quartetDistance T₁ T₂ ≤ Fintype.card (Quartet n) := by
      unfold quartetDistance Counting.truthDistance
      exact Finset.card_filter_le (Finset.univ : Finset (Quartet n)) _
    _ = Nat.choose n 4 := card_quartet n

@[simp] theorem splitOfTopology_displayedTopology
    (T : Tree.PhyloTree (Fin n)) (q : Quartet n) :
    splitOfTopology q (displayedTopology T q) = T.displayedSplitOn q.1 q.2 := by
  obtain ⟨i, hi⟩ := isQuartetSplit_mem_range q
    (displayedSplitOn_isQuartetSplit T q)
  unfold displayedTopology
  rw [← hi, topologyOfSplit_splitOfTopology]

/-- The tree rotation lemma, now exactly in the abstract form consumed by
the finite double-counting theorem. -/
theorem rotationWrongChannelLaw (T : Tree.PhyloTree (Fin n)) :
    Counting.WrongChannelLaw (displayedTopology T)
      (fun ω : RotationSample T => fun q =>
        crossingTopology (rotationOrder T ω) q) := by
  constructor
  · intro q
    rw [channelCount_rotationTopology, splitOfTopology_displayedTopology]
    exact T.wrongChannelOn_true_count q.1 q.2
  · intro q i hi
    rw [channelCount_rotationTopology]
    have hne : splitOfTopology q i ≠ T.displayedSplitOn q.1 q.2 := by
      intro heq
      apply hi
      have h := congrArg (topologyOfSplit q) heq
      simpa only [topologyOfSplit_splitOfTopology, displayedTopology] using h
    simpa only [Fintype.card_fin] using
      T.wrongChannelOn_other_count q.1 q.2 (splitOfTopology q i)
        (isQuartetSplit_mem_validSplitsOn T q (splitOfTopology_isQuartetSplit q i)) hne

/-! ## The arbitrary-pair upper bound -/

/-- The direct natural-number inequality obtained by combining the rotation
law with the cleared step-permuton estimate and finite double counting. -/
theorem quartetDistance_counting_bound
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    3 * cyclicFallingThree n * quartetDistance T₁ T₂ +
        6 * cyclicFallingThree n * Nat.choose n 4 ≤
      8 * n ^ 3 * Nat.choose n 4 := by
  have hlower := crossingTopology_pointwiseLowerBoundWithError
    hpublished hn (rotationOrder T₁) (rotationOrder T₂)
  have hcount := Counting.cleared_stepPermuton_truthDistance_upper_bound
    (Q := Quartet n) (S := Fin 3)
    (by decide : Fintype.card (Fin 3) = 3)
    (displayedTopology T₁) (displayedTopology T₂)
    (fun ω : RotationSample T₁ => fun q => crossingTopology (rotationOrder T₁ ω) q)
    (fun ω : RotationSample T₂ => fun q => crossingTopology (rotationOrder T₂ ω) q)
    (rotationWrongChannelLaw T₁) (rotationWrongChannelLaw T₂)
    n (cyclicFallingThree n) hlower
  simpa only [quartetDistance, card_quartet] using hcount

/-- The denominator-cleared form of the Bandelt--Dress upper bound for an
arbitrary pair of `n`-leaf phylogenetic trees. -/
theorem quartetDistance_cleared_upper_bound
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    9 * quartetDistance T₁ T₂ ≤
      6 * Nat.choose n 4 + n * (6 * n ^ 2 - 11 * n + 6) :=
  paper_cleared_bound_of_counting_bound hn
    (quartetDistance_counting_bound hpublished hn T₁ T₂)

/-- The rational form of the Bandelt--Dress upper bound displayed in the
paper. -/
theorem quartetDistance_rational_upper_bound
    (hpublished : Circular.StepPermutonTheorem n) (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (quartetDistance T₁ T₂ : ℚ) ≤
      (2 : ℚ) / 3 * (Nat.choose n 4 : ℚ) +
        (n : ℚ) * (6 * (n : ℚ) ^ 2 - 11 * (n : ℚ) + 6) / 9 :=
  paper_rational_bound_of_cleared hn
    (quartetDistance_cleared_upper_bound hpublished hn T₁ T₂)

end QuartetDistance.Upper
