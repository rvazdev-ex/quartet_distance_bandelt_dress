import QuartetDistance.TiedSampleCount

/-!
# The analytic step-permuton bridge

This file separates the genuinely external permuton inequality from the
elementary construction to which it is applied.  A permuton is represented by
a probability measure on `ℝ × ℝ` whose two marginals are Lebesgue measure on
`(0,1]`.  The choice of half-open endpoint is immaterial and makes the finite
strip partition literally disjoint.
-/

namespace QuartetDistance.Permuton

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Lebesgue probability measure on the unit interval, viewed as a measure on
all of `ℝ`. -/
noncomputable def unitMeasure : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  refine ⟨?_⟩
  simp [unitMeasure, Real.volume_Ioc]

instance : NullSingletonClass unitMeasure := by
  unfold unitMeasure
  infer_instance

/-- A Borel probability measure on the unit square with uniform marginals.
The support condition follows from the two marginal identities and is not
needed as a separate field. -/
structure BorelPermuton where
  measure : Measure (ℝ × ℝ)
  isProbability : IsProbabilityMeasure measure
  fst_uniform : Measure.map Prod.fst measure = unitMeasure
  snd_uniform : Measure.map Prod.snd measure = unitMeasure

attribute [instance] BorelPermuton.isProbability

/-- The first coordinate of a permuton lies in the unit interval almost
everywhere.  This is a consequence of the first marginal identity, rather
than an additional support assumption. -/
theorem BorelPermuton.ae_fst_mem_unitInterval (μ : BorelPermuton) :
    ∀ᵐ z ∂μ.measure, z.1 ∈ Ioc (0 : ℝ) 1 := by
  rw [show (∀ᵐ z ∂μ.measure, z.1 ∈ Ioc (0 : ℝ) 1) ↔
      Prod.fst ⁻¹' Ioc (0 : ℝ) 1 ∈ ae μ.measure by rfl]
  rw [mem_ae_iff_prob_eq_one (measurableSet_Ioc.preimage measurable_fst)]
  rw [← Measure.map_apply measurable_fst measurableSet_Ioc, μ.fst_uniform]
  simp [unitMeasure, Real.volume_Ioc]

/-- The second coordinate of a permuton lies in the unit interval almost
everywhere, by the second marginal identity. -/
theorem BorelPermuton.ae_snd_mem_unitInterval (μ : BorelPermuton) :
    ∀ᵐ z ∂μ.measure, z.2 ∈ Ioc (0 : ℝ) 1 := by
  rw [show (∀ᵐ z ∂μ.measure, z.2 ∈ Ioc (0 : ℝ) 1) ↔
      Prod.snd ⁻¹' Ioc (0 : ℝ) 1 ∈ ae μ.measure by rfl]
  rw [mem_ae_iff_prob_eq_one (measurableSet_Ioc.preimage measurable_snd)]
  rw [← Measure.map_apply measurable_snd measurableSet_Ioc, μ.snd_uniform]
  simp [unitMeasure, Real.volume_Ioc]

/-- Both marginal identities force the whole permuton measure to be
concentrated on the unit square. -/
theorem BorelPermuton.ae_mem_unitSquare (μ : BorelPermuton) :
    ∀ᵐ z ∂μ.measure, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  filter_upwards [μ.ae_fst_mem_unitInterval, μ.ae_snd_mem_unitInterval]
    with z hz₁ hz₂
  exact ⟨hz₁, hz₂⟩

/-- A Borel permuton gives mass one to the unit square. -/
theorem BorelPermuton.measure_unitSquare (μ : BorelPermuton) :
    μ.measure (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) = 1 := by
  rw [← mem_ae_iff_prob_eq_one (measurableSet_Ioc.prod measurableSet_Ioc)]
  exact μ.ae_mem_unitSquare

/-- The `i`th half-open strip in the uniform `n`-partition of `(0,1]`. -/
def strip (n : ℕ) (i : Fin n) : Set ℝ :=
  Ioc ((i : ℝ) / n) (((i : ℕ) + 1 : ℕ) / (n : ℝ))

theorem measurableSet_strip (n : ℕ) (i : Fin n) : MeasurableSet (strip n i) :=
  measurableSet_Ioc

theorem strip_pairwise_disjoint (n : ℕ) :
    Pairwise (fun i j : Fin n => Disjoint (strip n i) (strip n j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hc : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
    have hn : (0 : ℝ) ≤ n := by positivity
    have hle : (((i : ℕ) + 1 : ℕ) : ℝ) / n ≤ (j : ℝ) / n := by
      gcongr
    exact (not_lt_of_ge (hxi.2.trans hle)) hxj.1
  · have hc : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
    have hn : (0 : ℝ) ≤ n := by positivity
    have hle : (((j : ℕ) + 1 : ℕ) : ℝ) / n ≤ (i : ℝ) / n := by
      gcongr
    exact (not_lt_of_ge (hxj.2.trans hle)) hxi.1

theorem iUnion_strip {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, strip n i) = Ioc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    constructor
    · exact lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (i : ℝ) / n) hi.1
    · calc
        x ≤ (((i : ℕ) + 1 : ℕ) : ℝ) / n := hi.2
        _ ≤ (n : ℝ) / n := by
          gcongr
          exact_mod_cast i.isLt
        _ = 1 := by field_simp
  · intro x hx
    have hcover := Ioc_subset_biUnion_Ioc n
      (fun k : ℕ => (k : ℝ) / n)
    have hx' : x ∈ ⋃ i ∈ Finset.range n,
        Ioc ((i : ℝ) / n) (((i + 1 : ℕ) : ℝ) / n) := by
      apply hcover
      simpa [hn.ne'] using hx
    simp only [mem_iUnion, Finset.mem_range] at hx' ⊢
    obtain ⟨i, hi, hxi⟩ := hx'
    exact ⟨⟨i, hi⟩, hxi⟩

/-- The strip restrictions sum to uniform Lebesgue measure on `(0,1]`. -/
theorem sum_restrict_strip {n : ℕ} (hn : 0 < n) :
    (∑ i : Fin n, volume.restrict (strip n i)) = unitMeasure := by
  rw [← Measure.sum_fintype,
    ← Measure.restrict_iUnion (strip_pairwise_disjoint n) (measurableSet_strip n),
    iUnion_strip hn]
  rfl

theorem volume_strip {n : ℕ} (hn : 0 < n) (i : Fin n) :
    volume (strip n i) = (n : ℝ≥0∞)⁻¹ := by
  rw [strip, Real.volume_Ioc]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiCast : ((((i : ℕ) + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by norm_num
  have hreal :
      (((i : ℕ) + 1 : ℕ) : ℝ) / n - (i : ℝ) / n = (n : ℝ)⁻¹ := by
    rw [hiCast]
    field_simp
    ring
  rw [hreal, ENNReal.ofReal_inv_of_pos hnR]
  simp

/-- The usual step measure: density `n` on the `n` squares
`strip i × strip (π i)` and zero elsewhere. -/
noncomputable def stepMeasure {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Measure (ℝ × ℝ) :=
  ∑ i : Fin n,
    (n : ℝ≥0∞) •
      ((volume.restrict (strip n i)).prod
        (volume.restrict (strip n (π i))))

theorem map_fst_stepMeasure {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    Measure.map Prod.fst (stepMeasure π) = unitMeasure := by
  rw [stepMeasure, Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_fst_prod]
  have hmass (i : Fin n) :
      (volume.restrict (strip n (π i))) univ = (n : ℝ≥0∞)⁻¹ := by
    rw [Measure.restrict_apply_univ, volume_strip hn]
  simp_rw [hmass, smul_smul]
  have hnE : (n : ℝ≥0∞) ≠ 0 := by positivity
  simp only [ENNReal.mul_inv_cancel hnE (by simp), one_smul]
  exact sum_restrict_strip hn

theorem map_snd_stepMeasure {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    Measure.map Prod.snd (stepMeasure π) = unitMeasure := by
  rw [stepMeasure, Measure.map_finset_sum' measurable_snd.aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_snd_prod]
  have hmass (i : Fin n) :
      (volume.restrict (strip n i)) univ = (n : ℝ≥0∞)⁻¹ := by
    rw [Measure.restrict_apply_univ, volume_strip hn]
  simp_rw [hmass, smul_smul]
  have hnE : (n : ℝ≥0∞) ≠ 0 := by positivity
  simp only [ENNReal.mul_inv_cancel hnE (by simp), one_smul]
  exact (Equiv.sum_comp π
    (fun i : Fin n => volume.restrict (strip n i))).trans (sum_restrict_strip hn)

theorem stepMeasure_isProbability {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) : IsProbabilityMeasure (stepMeasure π) := by
  refine ⟨?_⟩
  have hmap := map_fst_stepMeasure hn π
  calc
    stepMeasure π univ = Measure.map Prod.fst (stepMeasure π) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = unitMeasure univ := by rw [hmap]
    _ = 1 := measure_univ

/-- The concrete Borel step permuton associated with a finite permutation. -/
noncomputable def stepPermuton {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) : BorelPermuton where
  measure := stepMeasure π
  isProbability := stepMeasure_isProbability hn π
  fst_uniform := map_fst_stepMeasure hn π
  snd_uniform := map_snd_stepMeasure hn π

/-! ## Uniform ranks of four atomless iid samples -/

abbrev Four := Circular.Four
abbrev Perm4 := Circular.Perm4

/-- Four independent uniform real coordinates. -/
noncomputable def rankMeasure : Measure (Four → ℝ) :=
  Measure.pi fun _ : Four => unitMeasure

instance : IsProbabilityMeasure rankMeasure := by
  unfold rankMeasure
  infer_instance

/-- The chamber in which `σ` lists the four sample names in strictly
increasing order.  Adjacent inequalities suffice on `Fin 4`. -/
def rankChamber (σ : Perm4) : Set (Four → ℝ) :=
  {x | ∀ i : Fin 3, x (σ i.castSucc) < x (σ i.succ)}

theorem mem_rankChamber_iff (x : Four → ℝ) (σ : Perm4) :
    x ∈ rankChamber σ ↔ StrictMono (x ∘ σ) := by
  exact (Fin.strictMono_iff_lt_succ (f := x ∘ σ)).symm

theorem measurableSet_rankChamber (σ : Perm4) :
    MeasurableSet (rankChamber σ) := by
  rw [show rankChamber σ = ⋂ i : Fin 3,
      {x : Four → ℝ | x (σ i.castSucc) < x (σ i.succ)} by
    ext x
    simp [rankChamber]]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

theorem rankChamber_pairwise_disjoint :
    Pairwise (fun σ τ : Perm4 => Disjoint (rankChamber σ) (rankChamber τ)) := by
  intro σ τ hστ
  apply Set.disjoint_left.2
  intro x hxσ hxτ
  have hsσ : StrictMono (x ∘ σ) := (mem_rankChamber_iff x σ).mp hxσ
  have hsτ : StrictMono (x ∘ τ) := (mem_rankChamber_iff x τ).mp hxτ
  have hfun : x ∘ σ = x ∘ τ :=
    Tuple.unique_monotone hsσ.monotone hsτ.monotone
  have hxinj : Function.Injective x := by
    intro i j hij
    have hcomp : (x ∘ σ) (σ.symm i) = (x ∘ σ) (σ.symm j) := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact σ.symm.injective (hsσ.injective hcomp)
  apply hστ
  ext i
  exact congrArg Fin.val (hxinj (congrFun hfun i))

theorem injective_mem_iUnion_rankChamber {x : Four → ℝ}
    (hx : Function.Injective x) : x ∈ ⋃ σ : Perm4, rankChamber σ := by
  refine Set.mem_iUnion.2 ⟨Tuple.sort x, ?_⟩
  rw [mem_rankChamber_iff]
  exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)

theorem prod_diagonal_measure_zero (μ : Measure ℝ) [SFinite μ]
    [NullSingletonClass μ] :
    μ.prod μ (Set.diagonal ℝ) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  simp [Set.diagonal]

theorem rankMeasure_pair_eq_zero (i j : Four) (hij : i ≠ j) :
    rankMeasure {x | x i = x j} = 0 := by
  let X : (Four → ℝ) → ℝ := fun x => x i
  let Y : (Four → ℝ) → ℝ := fun x => x j
  have hind : ProbabilityTheory.IndepFun X Y rankMeasure := by
    exact (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Four => unitMeasure)
      (X := fun _ : Four => id) (fun _ => aemeasurable_id)).indepFun hij
  have hmapX : Measure.map X rankMeasure = unitMeasure := by
    exact (measurePreserving_eval (fun _ : Four => unitMeasure) i).map_eq
  have hmapY : Measure.map Y rankMeasure = unitMeasure := by
    exact (measurePreserving_eval (fun _ : Four => unitMeasure) j).map_eq
  have hmap : Measure.map (fun x => (X x, Y x)) rankMeasure =
      unitMeasure.prod unitMeasure := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hmapX, hmapY]
  have hdiag := prod_diagonal_measure_zero unitMeasure
  rw [← hmap] at hdiag
  rw [Measure.map_apply (by fun_prop) measurableSet_diagonal] at hdiag
  simpa [X, Y, Set.diagonal] using hdiag

theorem rankMeasure_noninjective_zero :
    rankMeasure {x : Four → ℝ | ¬ Function.Injective x} = 0 := by
  have hsubset : {x : Four → ℝ | ¬ Function.Injective x} ⊆
      ⋃ i : Four, ⋃ j : Four, ⋃ (_ : i ≠ j), {x | x i = x j} := by
    intro x hx
    simp only [Function.Injective] at hx
    push Not at hx
    obtain ⟨i, j, heq, hij⟩ := hx
    simp only [mem_iUnion]
    exact ⟨i, j, hij, heq⟩
  apply measure_mono_null hsubset
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, rankMeasure_pair_eq_zero i j]

theorem rankChamber_iUnion_ae_univ :
    (⋃ σ : Perm4, rankChamber σ) =ᵐ[rankMeasure] Set.univ := by
  apply ae_eq_univ.mpr
  apply measure_mono_null _ rankMeasure_noninjective_zero
  intro x hx
  by_contra hxin
  exact hx (injective_mem_iUnion_rankChamber (Classical.not_not.mp hxin))

/-- Reindexing iid coordinates by a permutation preserves their joint law. -/
theorem measurePreserving_reindex (σ : Perm4) :
    MeasurePreserving (fun x : Four → ℝ => x ∘ σ) rankMeasure rankMeasure := by
  unfold rankMeasure
  have h := measurePreserving_piCongrLeft
    (μ := fun _ : Four => unitMeasure) (α := fun _ : Four => ℝ) σ.symm
  convert h using 1
  funext x i
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Four => ℝ) σ.symm x (σ i)).symm

theorem rankChamber_measure_eq (σ τ : Perm4) :
    rankMeasure (rankChamber σ) = rankMeasure (rankChamber τ) := by
  let ρ : Perm4 := τ.symm.trans σ
  have hmp := measurePreserving_reindex ρ
  have hpre : (fun x : Four → ℝ => x ∘ ρ) ⁻¹' rankChamber τ = rankChamber σ := by
    ext x
    simp only [Set.mem_preimage, mem_rankChamber_iff, Function.comp_assoc]
    have hrho : τ.trans ρ = σ := by
      ext i
      simp [ρ]
    have hf : x ∘ ρ ∘ τ = x ∘ σ := by
      funext i
      change x ((τ.trans ρ) i) = x (σ i)
      rw [hrho]
    rw [hf]
  calc
    rankMeasure (rankChamber σ) =
        rankMeasure ((fun x : Four → ℝ => x ∘ ρ) ⁻¹' rankChamber τ) := by rw [hpre]
    _ = Measure.map (fun x : Four → ℝ => x ∘ ρ) rankMeasure (rankChamber τ) :=
      (Measure.map_apply hmp.measurable (measurableSet_rankChamber τ)).symm
    _ = rankMeasure (rankChamber τ) := by rw [hmp.map_eq]

/-- Every one of the `4!` strict rank chambers has probability `1/24`. -/
theorem rankChamber_measure (σ : Perm4) :
    rankMeasure (rankChamber σ) = (24 : ℝ≥0∞)⁻¹ := by
  have hunion : rankMeasure (⋃ τ : Perm4, rankChamber τ) = 1 := by
    rw [measure_congr rankChamber_iUnion_ae_univ, measure_univ]
  rw [measure_iUnion (fun i j hij => rankChamber_pairwise_disjoint hij)
    measurableSet_rankChamber, tsum_fintype] at hunion
  have hall : ∀ τ : Perm4,
      rankMeasure (rankChamber τ) = rankMeasure (rankChamber σ) := by
    intro τ
    exact rankChamber_measure_eq τ σ
  simp_rw [hall] at hunion
  simp only [Finset.sum_const, nsmul_eq_mul] at hunion
  rw [Finset.card_univ, Circular.card_perm4] at hunion
  have h24 : (24 : ℝ≥0∞) ≠ 0 := by norm_num
  have h24top : (24 : ℝ≥0∞) ≠ ∞ := by norm_num
  apply le_antisymm
  · rw [← ENNReal.mul_le_mul_iff_left h24 h24top,
      ENNReal.inv_mul_cancel h24 h24top]
    simpa [mul_comm] using hunion.le
  · rw [← ENNReal.mul_le_mul_iff_left h24 h24top,
      ENNReal.inv_mul_cancel h24 h24top]
    simpa [mul_comm] using hunion.ge

/-! ## A latent-variable realization of the step measure -/

/-- Affinely place a unit-interval coordinate in strip `i`. -/
noncomputable def affineStrip (n : ℕ) (i : Fin n) (u : ℝ) : ℝ :=
  ((i : ℝ) + u) / n

theorem measurable_affineStrip (n : ℕ) (i : Fin n) :
    Measurable (affineStrip n i) := by
  unfold affineStrip
  fun_prop

theorem affineStrip_preimage_strip {n : ℕ} (hn : 0 < n) (i : Fin n) :
    affineStrip n i ⁻¹' strip n i = Ioc (0 : ℝ) 1 := by
  ext u
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Set.mem_preimage, strip, mem_Ioc, affineStrip]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (i : ℝ) < (i : ℝ) + u :=
      (div_lt_div_iff_of_pos_right hnR).mp hlo
    have hiCast : ((((i : ℕ) + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by norm_num
    rw [hiCast] at hhi
    have hhi' : (i : ℝ) + u ≤ (i : ℝ) + 1 := by
      exact (div_le_div_iff_of_pos_right hnR).mp hhi
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_div_iff_of_pos_right hnR).2
      linarith
    · apply (div_le_div_iff_of_pos_right hnR).2
      norm_num
      linarith

theorem map_volume_affineStrip {n : ℕ} (hn : 0 < n) (i : Fin n) :
    Measure.map (affineStrip n i) volume = (n : ℝ≥0∞) • volume := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hscale : ((n : ℝ)⁻¹) ≠ 0 := inv_ne_zero hn0
  have hfun : affineStrip n i =
      (fun x : ℝ => x + (i : ℝ) / n) ∘ (fun x : ℝ => (n : ℝ)⁻¹ * x) := by
    funext x
    simp only [affineStrip, Function.comp_apply]
    field_simp
    ring
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left hscale, Measure.map_smul, map_add_right_eq_self]
  congr 1
  rw [inv_inv, abs_of_pos hnR, ENNReal.ofReal_natCast]

/-- A uniform unit coordinate, affinely placed in strip `i`, has density `n`
on that strip. -/
theorem map_unitMeasure_affineStrip {n : ℕ} (hn : 0 < n) (i : Fin n) :
    Measure.map (affineStrip n i) unitMeasure =
      (n : ℝ≥0∞) • volume.restrict (strip n i) := by
  have h := Measure.restrict_map (μ := volume) (measurable_affineStrip n i)
    (measurableSet_strip n i)
  rw [map_volume_affineStrip hn i, affineStrip_preimage_strip hn i] at h
  simpa only [unitMeasure, Measure.restrict_smul] using h.symm

/-- Uniform counting probability on the strip index set. -/
noncomputable def uniformFinMeasure (n : ℕ) [Nonempty (Fin n)] : Measure (Fin n) :=
  (PMF.uniformOfFintype (Fin n)).toMeasure

instance (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (uniformFinMeasure n) := by
  unfold uniformFinMeasure
  infer_instance

theorem uniformFinMeasure_singleton {n : ℕ} [Nonempty (Fin n)] (i : Fin n) :
    uniformFinMeasure n {i} = (n : ℝ≥0∞)⁻¹ := by
  rw [uniformFinMeasure, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton i)]
  simp

theorem uniformFinMeasure_eq_sum {n : ℕ} [Nonempty (Fin n)] :
    uniformFinMeasure n = ∑ i : Fin n, (n : ℝ≥0∞)⁻¹ • Measure.dirac i := by
  calc
    uniformFinMeasure n = Measure.sum fun i : Fin n =>
        uniformFinMeasure n {i} • Measure.dirac i :=
      (Measure.sum_smul_dirac (uniformFinMeasure n)).symm
    _ = Measure.sum fun i : Fin n =>
        (n : ℝ≥0∞)⁻¹ • Measure.dirac i := by
      congr 1
      funext i
      rw [uniformFinMeasure_singleton]
    _ = ∑ i : Fin n, (n : ℝ≥0∞)⁻¹ • Measure.dirac i :=
      Measure.sum_fintype _

/-- One latent step-permuton point consists of a uniform strip and two
independent uniform within-strip coordinates. -/
noncomputable def pointSourceMeasure (n : ℕ) [Nonempty (Fin n)] :
    Measure (Fin n × (ℝ × ℝ)) :=
  (uniformFinMeasure n).prod (unitMeasure.prod unitMeasure)

instance (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (pointSourceMeasure n) := by
  unfold pointSourceMeasure
  infer_instance

/-- Map latent strip/unit coordinates to the associated point of the step
permuton. -/
noncomputable def stepPointMap {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Fin n × (ℝ × ℝ) → ℝ × ℝ := fun z =>
  (affineStrip n z.1 z.2.1, affineStrip n (π z.1) z.2.2)

theorem measurable_stepPointMap {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Measurable (stepPointMap π) := by
  unfold stepPointMap
  apply Measurable.prodMk
  · unfold affineStrip
    exact (((measurable_of_finite (fun i : Fin n => (i : ℝ))).comp measurable_fst).add
      (measurable_fst.comp measurable_snd)).div_const _
  · unfold affineStrip
    exact (((measurable_of_finite (fun i : Fin n => (π i : ℝ))).comp measurable_fst).add
      (measurable_snd.comp measurable_snd)).div_const _

theorem map_stepPointMap_dirac_prod {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    Measure.map (stepPointMap π)
        ((Measure.dirac i).prod (unitMeasure.prod unitMeasure)) =
      (n : ℝ≥0∞) ^ 2 •
        ((volume.restrict (strip n i)).prod
          (volume.restrict (strip n (π i)))) := by
  rw [Measure.dirac_prod,
    Measure.map_map (measurable_stepPointMap π) (by fun_prop)]
  have hfun : stepPointMap π ∘ Prod.mk i =
      Prod.map (affineStrip n i) (affineStrip n (π i)) := by
    funext z
    rfl
  rw [hfun, ← Measure.map_prod_map unitMeasure unitMeasure
      (measurable_affineStrip n i) (measurable_affineStrip n (π i)),
    map_unitMeasure_affineStrip hn i,
    map_unitMeasure_affineStrip hn (π i),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two]

/-- The latent one-point construction has exactly the Borel step measure as
its pushforward law. -/
theorem map_stepPointMap_pointSourceMeasure {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    Measure.map (stepPointMap π) (pointSourceMeasure n) = stepMeasure π := by
  rw [pointSourceMeasure, uniformFinMeasure_eq_sum,
    ← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.map_finset_sum' (measurable_stepPointMap π).aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul,
    map_stepPointMap_dirac_prod hn π i, smul_smul]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by positivity
  have hntop : (n : ℝ≥0∞) ≠ ∞ := by simp
  rw [pow_two, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hntop, one_mul]

/-- Four independent strip indices. -/
noncomputable def stripVectorMeasure (n : ℕ) [Nonempty (Fin n)] :
    Measure (Circular.StripSample n) :=
  Measure.pi fun _ : Four => uniformFinMeasure n

instance (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (stripVectorMeasure n) := by
  unfold stripVectorMeasure
  infer_instance

/-- The grouped latent sample law: four strip indices, four independent
first-coordinate uniforms, and four independent second-coordinate uniforms. -/
noncomputable def latentFourMeasure (n : ℕ) [Nonempty (Fin n)] :
    Measure (Circular.StripSample n × ((Four → ℝ) × (Four → ℝ))) :=
  (stripVectorMeasure n).prod (rankMeasure.prod rankMeasure)

instance (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (latentFourMeasure n) := by
  unfold latentFourMeasure
  infer_instance

/-- Regroup four one-point latent samples into strip, `x`, and `y` vectors. -/
def groupPointSources {n : ℕ} :
    (Four → Fin n × (ℝ × ℝ)) →
      Circular.StripSample n × ((Four → ℝ) × (Four → ℝ)) := fun z =>
  (fun i => (z i).1, (fun i => (z i).2.1, fun i => (z i).2.2))

theorem measurePreserving_groupPointSources (n : ℕ) [Nonempty (Fin n)] :
    MeasurePreserving groupPointSources
      (Measure.pi fun _ : Four => pointSourceMeasure n)
      (latentFourMeasure n) := by
  let estrip := MeasurableEquiv.arrowProdEquivProdArrow (Fin n) (ℝ × ℝ) Four
  let ecoord := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ Four
  have h₁ := measurePreserving_arrowProdEquivProdArrow
    (Fin n) (ℝ × ℝ) Four
    (fun _ : Four => uniformFinMeasure n)
    (fun _ : Four => unitMeasure.prod unitMeasure)
  have hcoord := measurePreserving_arrowProdEquivProdArrow
    ℝ ℝ Four (fun _ : Four => unitMeasure) (fun _ : Four => unitMeasure)
  have h₂ := MeasurePreserving.prod
    (MeasurePreserving.id (stripVectorMeasure n)) hcoord
  have hcomp := h₂.comp h₁
  convert hcomp using 1
  · funext z
    rfl
  · congr 1
  · rfl

/-- The four actual points obtained from a grouped latent sample. -/
noncomputable def latentStepPoints {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Circular.StripSample n × ((Four → ℝ) × (Four → ℝ)) → Four → (ℝ × ℝ) := fun z i =>
  (affineStrip n (z.1 i) (z.2.1 i),
    affineStrip n (π (z.1 i)) (z.2.2 i))

theorem measurable_latentStepPoints {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Measurable (latentStepPoints π) := by
  rw [measurable_pi_iff]
  intro i
  unfold latentStepPoints affineStrip
  apply Measurable.prodMk
  · exact (((measurable_of_finite (fun j : Fin n => (j : ℝ))).comp
      ((measurable_pi_apply i).comp measurable_fst)).add
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).div_const _
  · exact (((measurable_of_finite (fun j : Fin n => (π j : ℝ))).comp
      ((measurable_pi_apply i).comp measurable_fst)).add
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))).div_const _

/-- Four grouped latent samples push forward to four iid draws from the
Borel step measure. -/
theorem map_latentStepPoints {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    Measure.map (latentStepPoints π) (latentFourMeasure n) =
      Measure.pi (fun _ : Four => stepMeasure π) := by
  have hgroup := measurePreserving_groupPointSources n
  have hpoint :
      (fun z : Four → Fin n × (ℝ × ℝ) => fun i => stepPointMap π (z i)) =
        latentStepPoints π ∘ groupPointSources := by
    rfl
  calc
    Measure.map (latentStepPoints π) (latentFourMeasure n) =
        Measure.map (latentStepPoints π)
          (Measure.map groupPointSources
            (Measure.pi fun _ : Four => pointSourceMeasure n)) := by rw [hgroup.map_eq]
    _ = Measure.map (latentStepPoints π ∘ groupPointSources)
          (Measure.pi fun _ : Four => pointSourceMeasure n) := by
      rw [Measure.map_map (measurable_latentStepPoints π) hgroup.measurable]
    _ = Measure.map (fun z : Four → Fin n × (ℝ × ℝ) =>
          fun i => stepPointMap π (z i))
          (Measure.pi fun _ : Four => pointSourceMeasure n) := by rw [hpoint]
    _ = Measure.pi (fun _ : Four => stepMeasure π) := by
      rw [Measure.pi_map_pi (fun _ => (measurable_stepPointMap π).aemeasurable)]
      congr 1
      funext i
      exact map_stepPointMap_pointSourceMeasure hn π

/-! ## Identifying real-coordinate ranks with the finite tied model -/

theorem tiedStripOrder_strictMono_key {n : ℕ} (f : Circular.StripSample n)
    (ranks : Perm4) :
    StrictMono (Circular.tiedStripKey f ranks ∘
      Circular.tiedStripOrder f ranks) := by
  exact (Tuple.monotone_sort (Circular.tiedStripKey f ranks)).strictMono_of_injective
    ((Circular.tiedStripKey_injective f ranks).comp
      (Circular.tiedStripOrder f ranks).injective)

/-- Every coordinate lies in the half-open unit interval used by the source
measure. -/
def InUnit (u : Four → ℝ) : Prop := ∀ i, u i ∈ Ioc (0 : ℝ) 1

theorem key_lt_imp_affine_lt {n : ℕ} (hn : 0 < n)
    (f : Circular.StripSample n) (u : Four → ℝ) (q : Perm4)
    (hu : InUnit u) (hq : u ∈ rankChamber q) {i j : Four}
    (hkey : Circular.tiedStripKey f q.symm i <
      Circular.tiedStripKey f q.symm j) :
    affineStrip n (f i) (u i) < affineStrip n (f j) (u j) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfi := (f i).isLt
  have hfj := (f j).isLt
  have hri := (q.symm i).isLt
  have hrj := (q.symm j).isLt
  have hcases : (f i).val < (f j).val ∨
      ((f i).val = (f j).val ∧ (q.symm i).val < (q.symm j).val) := by
    simp only [Circular.tiedStripKey] at hkey
    omega
  apply (div_lt_div_iff_of_pos_right hnR).2
  rcases hcases with hf | ⟨hf, hr⟩
  · have hgap : (f i).val + 1 ≤ (f j).val := by omega
    have hgapR : ((f i).val : ℝ) + 1 ≤ ((f j).val : ℝ) := by exact_mod_cast hgap
    have hui := hu i
    have huj := hu j
    simp only [mem_Ioc] at hui huj
    linarith
  · have hfFin : f i = f j := Fin.ext hf
    have hrFin : q.symm i < q.symm j := hr
    have hmono := (mem_rankChamber_iff u q).mp hq hrFin
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at hmono
    rw [hfFin]
    linarith

theorem strictMono_affine_comp_tiedStripOrder {n : ℕ} (hn : 0 < n)
    (f : Circular.StripSample n) (u : Four → ℝ) (q : Perm4)
    (hu : InUnit u) (hq : u ∈ rankChamber q) :
    StrictMono ((fun i => affineStrip n (f i) (u i)) ∘
      Circular.tiedStripOrder f q.symm) := by
  intro i j hij
  apply key_lt_imp_affine_lt hn f u q hu hq
  exact tiedStripOrder_strictMono_key f q.symm hij

/-- Sorting the actual real coordinates gives exactly the key-based tied
order used in `Circular.tiedCollisionPattern`. -/
theorem tiedStripOrder_eq_sort_affine {n : ℕ} (hn : 0 < n)
    (f : Circular.StripSample n) (u : Four → ℝ) (q : Perm4)
    (hu : InUnit u) (hq : u ∈ rankChamber q) :
    Circular.tiedStripOrder f q.symm =
      Tuple.sort (fun i => affineStrip n (f i) (u i)) := by
  let actual : Four → ℝ := fun i => affineStrip n (f i) (u i)
  let tied := Circular.tiedStripOrder f q.symm
  have htied : StrictMono (actual ∘ tied) :=
    strictMono_affine_comp_tiedStripOrder hn f u q hu hq
  have hactual : Function.Injective actual := by
    intro i j hij
    have hpos := htied.injective
      (show actual (tied (tied.symm i)) = actual (tied (tied.symm j)) by simpa using hij)
    exact tied.symm.injective hpos
  have hfun : actual ∘ tied = actual ∘ Tuple.sort actual :=
    Tuple.unique_monotone htied.monotone (Tuple.monotone_sort actual)
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact congrArg Fin.val (hactual (congrFun hfun i))

/-- If the four strip indices are distinct, sorting by `(strip,tie-rank)` is
just sorting by the strip index; in particular the result is independent of
the tie ranks. -/
theorem strictMono_strip_comp_tiedStripOrder_of_injective {n : ℕ}
    (f : Circular.StripSample n) (ranks : Perm4)
    (hf : Function.Injective f) :
    StrictMono (f ∘ Circular.tiedStripOrder f ranks) := by
  intro i j hij
  have hkey := tiedStripOrder_strictMono_key f ranks hij
  have hne : f (Circular.tiedStripOrder f ranks i) ≠
      f (Circular.tiedStripOrder f ranks j) := by
    intro heq
    exact (ne_of_lt hij) ((Circular.tiedStripOrder f ranks).injective (hf heq))
  simp only [Function.comp_apply, Circular.tiedStripKey] at hkey ⊢
  omega

/-- The increasing enumeration of the image of an injective strip sample is
the sample-name order obtained from `tiedStripOrder`. -/
theorem enumerateFour_map_eq_tiedStripOrder_of_injective {n : ℕ}
    (f : Circular.StripSample n) (ranks : Perm4)
    (hf : Function.Injective f) :
    Circular.enumerateFour
        (Finset.univ.map ⟨f, hf⟩) (by simp) =
      f ∘ Circular.tiedStripOrder f ranks := by
  let s : Finset (Fin n) := Finset.univ.map ⟨f, hf⟩
  let order := Circular.tiedStripOrder f ranks
  let g : Four → s := fun i =>
    ⟨f (order i), by simp [s]⟩
  have hgmono : StrictMono g := by
    intro i j hij
    change f (order i) < f (order j)
    exact strictMono_strip_comp_tiedStripOrder_of_injective f ranks hf hij
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    simp only [s, Finset.mem_map, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := order.surjective i
    refine ⟨j, ?_⟩
    apply Subtype.ext
    exact congrArg f hj
  let e : Four ≃o s := hgmono.orderIsoOfSurjective g hgsurj
  have he : e = s.orderIsoOfFin (by simp [s]) := Subsingleton.elim _ _
  funext i
  have hi := congrArg Subtype.val (DFunLike.congr_fun he i)
  simpa [Circular.enumerateFour, s, e, g, order, Function.comp_apply,
    StrictMono.coe_orderIsoOfSurjective] using hi.symm

/-- On distinct strips the concrete lexicographic pattern agrees pointwise
with the usual standardized restriction.  Thus the analytic latent model and
the finite model use the same convention even off the collision branch. -/
theorem tiedCollisionPattern_eq_relativePattern_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : Circular.TiedStripSample n)
    (hf : Function.Injective z.strips) :
    Circular.tiedCollisionPattern π z =
      Circular.relativePattern π
        (Finset.univ.map ⟨z.strips, hf⟩) (by simp) := by
  let sx : Finset (Fin n) := Finset.univ.map ⟨z.strips, hf⟩
  have hπf : Function.Injective (fun i => π (z.strips i)) :=
    π.injective.comp hf
  let sy : Finset (Fin n) :=
    Finset.univ.map ⟨(fun i => π (z.strips i)), hπf⟩
  have hsyeq : sx.map π.toEmbedding = sy := by
    ext a
    simp only [sx, sy, Finset.mem_map, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨b, ⟨i, hib⟩, hba⟩
      refine ⟨i, ?_⟩
      rw [← hba, ← hib]
      rfl
    · rintro ⟨i, hi⟩
      refine ⟨z.strips i, ⟨i, rfl⟩, ?_⟩
      exact hi
  have hx := enumerateFour_map_eq_tiedStripOrder_of_injective
    z.strips z.xRanks hf
  have hy := enumerateFour_map_eq_tiedStripOrder_of_injective
    (fun i => π (z.strips i)) z.yRanks hπf
  apply Equiv.ext
  intro i
  apply (Circular.tiedStripOrder
    (fun i => π (z.strips i)) z.yRanks).injective
  simp only [Circular.tiedCollisionPattern,
    Circular.relativePermutation_apply, Equiv.apply_symm_apply]
  apply hπf
  have hspec := Circular.relativePattern_spec π sx (by simp [sx]) i
  have hspec' :
      Circular.enumerateFour sy (by simp [sy])
          (Circular.relativePattern π sx (by simp [sx]) i) =
        π (Circular.enumerateFour sx (by simp [sx]) i) := by
    simpa only [hsyeq] using hspec
  have hxi := congrFun hx i
  have hyi := congrFun hy
    (Circular.relativePattern π sx (by simp [sx]) i)
  simpa only [sx, sy, Function.comp_apply] using
    (hyi.symm.trans (hspec'.trans (congrArg π hxi))).symm

theorem tiedCollisionPattern_eq_tiedStepPattern {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : Circular.TiedStripSample n) :
    Circular.tiedCollisionPattern π z = Circular.tiedStepPattern π z := by
  by_cases hf : Function.Injective z.strips
  · rw [Circular.tiedStepPattern_of_injective π z hf]
    exact tiedCollisionPattern_eq_relativePattern_of_injective π z hf
  · simp [Circular.tiedStepPattern, hf]

/-! ## The measurable four-point dihedral event -/

/-- The vector of first coordinates of four planar points. -/
def firstCoordinates (z : Four → ℝ × ℝ) : Four → ℝ :=
  fun i => (z i).1

/-- The vector of second coordinates of four planar points. -/
def secondCoordinates (z : Four → ℝ × ℝ) : Four → ℝ :=
  fun i => (z i).2

theorem measurable_firstCoordinates : Measurable firstCoordinates := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_fst.comp (measurable_pi_apply i)

theorem measurable_secondCoordinates : Measurable secondCoordinates := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_snd.comp (measurable_pi_apply i)

/-! ## Coordinate ties for an arbitrary permuton -/

/-- Two distinct iid samples from a Borel permuton have unequal values in
any measurable real coordinate whose marginal is uniform. -/
theorem iidPermuton_coordinate_pair_eq_zero (mu : BorelPermuton)
    (coord : (ℝ × ℝ) → ℝ) (hcoord : Measurable coord)
    (huniform : Measure.map coord mu.measure = unitMeasure)
    (i j : Four) (hij : i ≠ j) :
    (Measure.pi (fun _ : Four => mu.measure))
        {z | coord (z i) = coord (z j)} = 0 := by
  let nu : Measure (Four → ℝ × ℝ) :=
    Measure.pi fun _ : Four => mu.measure
  let X : (Four → ℝ × ℝ) → ℝ := fun z => coord (z i)
  let Y : (Four → ℝ × ℝ) → ℝ := fun z => coord (z j)
  have hind : ProbabilityTheory.IndepFun X Y nu := by
    exact (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Four => mu.measure)
      (X := fun _ : Four => coord)
      (fun _ => hcoord.aemeasurable)).indepFun hij
  have hmapEval (k : Four) :
      Measure.map (fun z : Four → ℝ × ℝ => z k) nu = mu.measure := by
    exact (measurePreserving_eval (fun _ : Four => mu.measure) k).map_eq
  have hmapX : Measure.map X nu = unitMeasure := by
    calc
      Measure.map X nu =
          Measure.map coord
            (Measure.map (fun z : Four → ℝ × ℝ => z i) nu) := by
        change Measure.map (coord ∘ fun z : Four → ℝ × ℝ => z i) nu = _
        rw [← Measure.map_map hcoord (measurable_pi_apply i)]
      _ = Measure.map coord mu.measure := by rw [hmapEval]
      _ = unitMeasure := huniform
  have hmapY : Measure.map Y nu = unitMeasure := by
    calc
      Measure.map Y nu =
          Measure.map coord
            (Measure.map (fun z : Four → ℝ × ℝ => z j) nu) := by
        change Measure.map (coord ∘ fun z : Four → ℝ × ℝ => z j) nu = _
        rw [← Measure.map_map hcoord (measurable_pi_apply j)]
      _ = Measure.map coord mu.measure := by rw [hmapEval]
      _ = unitMeasure := huniform
  have hmap : Measure.map (fun z => (X z, Y z)) nu =
      unitMeasure.prod unitMeasure := by
    have hXm : AEMeasurable X nu := by
      apply Measurable.aemeasurable
      change Measurable (coord ∘ fun z : Four → ℝ × ℝ => z i)
      exact hcoord.comp (measurable_pi_apply i)
    have hYm : AEMeasurable Y nu := by
      apply Measurable.aemeasurable
      change Measurable (coord ∘ fun z : Four → ℝ × ℝ => z j)
      exact hcoord.comp (measurable_pi_apply j)
    rw [hind.map_prod_eq_prod_map_map hXm hYm, hmapX, hmapY]
  have hdiag := prod_diagonal_measure_zero unitMeasure
  rw [← hmap] at hdiag
  have hpair : Measurable (fun z => (X z, Y z)) := by
    have hX : Measurable X := by
      change Measurable (coord ∘ fun z : Four → ℝ × ℝ => z i)
      exact hcoord.comp (measurable_pi_apply i)
    have hY : Measurable Y := by
      change Measurable (coord ∘ fun z : Four → ℝ × ℝ => z j)
      exact hcoord.comp (measurable_pi_apply j)
    exact hX.prodMk hY
  rw [Measure.map_apply hpair measurableSet_diagonal] at hdiag
  simpa [nu, X, Y, Set.diagonal] using hdiag

/-- The first-coordinate vector of four iid samples from any Borel permuton
is injective almost surely. -/
theorem iidPermuton_firstCoordinates_noninjective_zero (mu : BorelPermuton) :
    (Measure.pi (fun _ : Four => mu.measure))
        {z | ¬ Function.Injective (firstCoordinates z)} = 0 := by
  have hsubset : {z : Four → ℝ × ℝ |
      ¬ Function.Injective (firstCoordinates z)} ⊆
      ⋃ i : Four, ⋃ j : Four, ⋃ (_ : i ≠ j),
        {z | (z i).1 = (z j).1} := by
    intro z hz
    simp only [Function.Injective] at hz
    push Not at hz
    obtain ⟨i, j, heq, hij⟩ := hz
    simp only [mem_iUnion]
    exact ⟨i, j, hij, heq⟩
  apply measure_mono_null hsubset
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · rw [measure_iUnion_null_iff]
    intro _
    exact iidPermuton_coordinate_pair_eq_zero mu Prod.fst
      measurable_fst mu.fst_uniform i j hij

/-- The second-coordinate vector of four iid samples from any Borel
permuton is injective almost surely. -/
theorem iidPermuton_secondCoordinates_noninjective_zero (mu : BorelPermuton) :
    (Measure.pi (fun _ : Four => mu.measure))
        {z | ¬ Function.Injective (secondCoordinates z)} = 0 := by
  have hsubset : {z : Four → ℝ × ℝ |
      ¬ Function.Injective (secondCoordinates z)} ⊆
      ⋃ i : Four, ⋃ j : Four, ⋃ (_ : i ≠ j),
        {z | (z i).2 = (z j).2} := by
    intro z hz
    simp only [Function.Injective] at hz
    push Not at hz
    obtain ⟨i, j, heq, hij⟩ := hz
    simp only [mem_iUnion]
    exact ⟨i, j, hij, heq⟩
  apply measure_mono_null hsubset
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · rw [measure_iUnion_null_iff]
    intro _
    exact iidPermuton_coordinate_pair_eq_zero mu Prod.snd
      measurable_snd mu.snd_uniform i j hij

/-- The Borel event that the strict first- and second-coordinate orders of
four points have dihedral relative permutation.  Tied coordinates belong to
no rank chamber and hence are excluded. -/
def dihedralPointEvent : Set (Four → ℝ × ℝ) :=
  ⋃ qx : Perm4, ⋃ qy : Perm4,
    ⋃ (_ : Circular.IsDihedral4 (Circular.relativePermutation qx qy)),
      firstCoordinates ⁻¹' rankChamber qx ∩
        secondCoordinates ⁻¹' rankChamber qy

theorem measurableSet_dihedralPointEvent : MeasurableSet dihedralPointEvent := by
  unfold dihedralPointEvent
  apply MeasurableSet.iUnion
  intro qx
  apply MeasurableSet.iUnion
  intro qy
  apply MeasurableSet.iUnion
  intro h
  exact ((measurableSet_rankChamber qx).preimage measurable_firstCoordinates).inter
    ((measurableSet_rankChamber qy).preimage measurable_secondCoordinates)

theorem mem_dihedralPointEvent_iff (z : Four → ℝ × ℝ)
    (hx : Function.Injective (firstCoordinates z))
    (hy : Function.Injective (secondCoordinates z)) :
    z ∈ dihedralPointEvent ↔
      Circular.IsDihedral4
        (Circular.relativePermutation
          (Tuple.sort (firstCoordinates z))
          (Tuple.sort (secondCoordinates z))) := by
  have hxsort : firstCoordinates z ∈ rankChamber
      (Tuple.sort (firstCoordinates z)) := by
    rw [mem_rankChamber_iff]
    exact (Tuple.monotone_sort (firstCoordinates z)).strictMono_of_injective
      (hx.comp (Tuple.sort (firstCoordinates z)).injective)
  have hysort : secondCoordinates z ∈ rankChamber
      (Tuple.sort (secondCoordinates z)) := by
    rw [mem_rankChamber_iff]
    exact (Tuple.monotone_sort (secondCoordinates z)).strictMono_of_injective
      (hy.comp (Tuple.sort (secondCoordinates z)).injective)
  constructor
  · intro hz
    simp only [dihedralPointEvent, mem_iUnion, mem_inter_iff, mem_preimage] at hz
    obtain ⟨qx, qy, hd, hxq, hyq⟩ := hz
    have heqx : qx = Tuple.sort (firstCoordinates z) := by
      by_contra hne
      exact (Set.disjoint_left.1 (rankChamber_pairwise_disjoint hne) hxq hxsort)
    have heqy : qy = Tuple.sort (secondCoordinates z) := by
      by_contra hne
      exact (Set.disjoint_left.1 (rankChamber_pairwise_disjoint hne) hyq hysort)
    simpa [heqx, heqy] using hd
  · intro hd
    simp only [dihedralPointEvent, mem_iUnion, mem_inter_iff, mem_preimage]
    exact ⟨Tuple.sort (firstCoordinates z), Tuple.sort (secondCoordinates z),
      hd, hxsort, hysort⟩

/-- Under strict latent rank chambers, the analytic point event is exactly
the outcome in the finite tied-strip model. -/
theorem latentStepPoints_mem_dihedralPointEvent_iff {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n)
    (u v : Four → ℝ) (qx qy : Perm4)
    (hu : InUnit u) (hv : InUnit v)
    (hqx : u ∈ rankChamber qx) (hqy : v ∈ rankChamber qy) :
    latentStepPoints π (f, (u, v)) ∈ dihedralPointEvent ↔
      Circular.IsDihedral4
        (Circular.tiedStepPattern π ⟨f, qx.symm, qy.symm⟩) := by
  let ax : Four → ℝ := fun i => affineStrip n (f i) (u i)
  let ay : Four → ℝ := fun i => affineStrip n (π (f i)) (v i)
  let ox := Circular.tiedStripOrder f qx.symm
  let oy := Circular.tiedStripOrder (fun i => π (f i)) qy.symm
  have hmx : StrictMono (ax ∘ ox) :=
    strictMono_affine_comp_tiedStripOrder hn f u qx hu hqx
  have hmy : StrictMono (ay ∘ oy) :=
    strictMono_affine_comp_tiedStripOrder hn (fun i => π (f i)) v qy hv hqy
  have hix : Function.Injective ax := by
    intro i j hij
    apply ox.symm.injective
    apply hmx.injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
  have hiy : Function.Injective ay := by
    intro i j hij
    apply oy.symm.injective
    apply hmy.injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
  have hxcoords : firstCoordinates (latentStepPoints π (f, (u, v))) = ax := rfl
  have hycoords : secondCoordinates (latentStepPoints π (f, (u, v))) = ay := rfl
  rw [mem_dihedralPointEvent_iff _ (hxcoords.symm ▸ hix) (hycoords.symm ▸ hiy)]
  have hxsort := tiedStripOrder_eq_sort_affine hn f u qx hu hqx
  have hysort := tiedStripOrder_eq_sort_affine hn
    (fun i => π (f i)) v qy hv hqy
  change Circular.IsDihedral4
      (Circular.relativePermutation (Tuple.sort ax) (Tuple.sort ay)) ↔ _
  rw [← hxsort, ← hysort, ← tiedCollisionPattern_eq_tiedStepPattern]
  rfl

/-- Four-point dihedral density of a Borel permuton. -/
noncomputable def dihedralDensity (μ : BorelPermuton) : ℝ :=
  (Measure.pi (fun _ : Four => μ.measure) dihedralPointEvent).toReal

/-- The single external input from permuton theory: every permuton has
dihedral four-pattern density at least `1/3`.  This is a proposition to be
supplied by the cited result, not an axiom of the development. -/
def PublishedPermutonInequality : Prop :=
  ∀ μ : BorelPermuton, (1 : ℝ) / 3 ≤ dihedralDensity μ

/-! ## Exact mass of the latent finite partition -/

def inUnitSet : Set (Four → ℝ) := {u | InUnit u}

theorem inUnitSet_eq_pi :
    inUnitSet = Set.pi Set.univ (fun _ : Four => Ioc (0 : ℝ) 1) := by
  ext u
  simp [inUnitSet, InUnit]

theorem measurableSet_inUnitSet : MeasurableSet inUnitSet := by
  rw [inUnitSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem rankMeasure_inUnitSet : rankMeasure inUnitSet = 1 := by
  rw [inUnitSet_eq_pi, rankMeasure, Measure.pi_pi]
  simp [unitMeasure, Real.volume_Ioc]

theorem ae_inUnit : ∀ᵐ u ∂rankMeasure, InUnit u := by
  rw [show (∀ᵐ u ∂rankMeasure, InUnit u) ↔
      (∀ᵐ u ∂rankMeasure, u ∈ inUnitSet) by rfl]
  apply (ae_mem_iff_measure_eq measurableSet_inUnitSet.nullMeasurableSet).2
  rw [rankMeasure_inUnitSet, measure_univ]

/-- Every atom of the iid strip-vector law has mass `n⁻⁴`. -/
theorem stripVectorMeasure_singleton {n : ℕ} [Nonempty (Fin n)]
    (f : Circular.StripSample n) :
    stripVectorMeasure n {f} = ((n : ℝ≥0∞)⁻¹) ^ 4 := by
  rw [stripVectorMeasure, Measure.pi_singleton]
  simp only [uniformFinMeasure_singleton, Finset.prod_const]
  rw [Finset.card_univ, show Fintype.card Four = 4 from by decide]

/-- The iid strip-vector law is the uniform finite atomic measure. -/
theorem stripVectorMeasure_eq_sum {n : ℕ} [Nonempty (Fin n)] :
    stripVectorMeasure n =
      ∑ f : Circular.StripSample n,
        ((n : ℝ≥0∞)⁻¹) ^ 4 • Measure.dirac f := by
  calc
    stripVectorMeasure n = Measure.sum fun f : Circular.StripSample n =>
        stripVectorMeasure n {f} • Measure.dirac f :=
      (Measure.sum_smul_dirac (stripVectorMeasure n)).symm
    _ = Measure.sum fun f : Circular.StripSample n =>
        ((n : ℝ≥0∞)⁻¹) ^ 4 • Measure.dirac f := by
      congr 1
      funext f
      rw [stripVectorMeasure_singleton]
    _ = ∑ f : Circular.StripSample n,
        ((n : ℝ≥0∞)⁻¹) ^ 4 • Measure.dirac f := Measure.sum_fintype _

/-- The product of the two rank chambers corresponding to a pair of finite
tie-ranking permutations.  Inversion appears because a chamber permutation
lists sample names by rank, whereas a tie-ranking maps sample names to rank. -/
def rankPairCell (r : Perm4 × Perm4) :
    Set ((Four → ℝ) × (Four → ℝ)) :=
  rankChamber r.1.symm ×ˢ rankChamber r.2.symm

theorem measurableSet_rankPairCell (r : Perm4 × Perm4) :
    MeasurableSet (rankPairCell r) :=
  (measurableSet_rankChamber r.1.symm).prod
    (measurableSet_rankChamber r.2.symm)

theorem rankPairCell_pairwise_disjoint :
    Pairwise (fun r s : Perm4 × Perm4 =>
      Disjoint (rankPairCell r) (rankPairCell s)) := by
  intro r s hrs
  apply Set.disjoint_left.2
  rintro ⟨u, v⟩ hr hs
  rcases hr with ⟨hru, hrv⟩
  rcases hs with ⟨hsu, hsv⟩
  by_cases hfirst : r.1 = s.1
  · have hsecond : r.2 ≠ s.2 := by
      intro h
      exact hrs (Prod.ext hfirst h)
    have hsymm : r.2.symm ≠ s.2.symm := by
      intro h
      apply hsecond
      simpa using congrArg Equiv.symm h
    exact Set.disjoint_left.1 (rankChamber_pairwise_disjoint hsymm) hrv hsv
  · have hsymm : r.1.symm ≠ s.1.symm := by
      intro h
      apply hfirst
      simpa using congrArg Equiv.symm h
    exact Set.disjoint_left.1 (rankChamber_pairwise_disjoint hsymm) hru hsu

/-- The successful pairs of tie rankings over a fixed strip vector. -/
noncomputable def successfulRankPairs {n : ℕ}
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    Finset (Perm4 × Perm4) :=
  Finset.univ.filter fun r =>
    Circular.IsDihedral4
      (Circular.tiedStepPattern π ⟨f, r.1, r.2⟩)

/-- The union of the strict rank cells giving a dihedral outcome for a fixed
strip vector. -/
noncomputable def successfulRankSet {n : ℕ}
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    Set ((Four → ℝ) × (Four → ℝ)) :=
  ⋃ r : ↑(successfulRankPairs π f), rankPairCell r.1

theorem measurableSet_successfulRankSet {n : ℕ}
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    MeasurableSet (successfulRankSet π f) := by
  unfold successfulRankSet
  exact MeasurableSet.iUnion fun r => measurableSet_rankPairCell r.1

theorem successfulRankSet_measure {n : ℕ}
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    (rankMeasure.prod rankMeasure) (successfulRankSet π f) =
      (successfulRankPairs π f).card * ((24 : ℝ≥0∞)⁻¹) ^ 2 := by
  rw [successfulRankSet,
    measure_iUnion
      (fun r s hrs => rankPairCell_pairwise_disjoint (Subtype.coe_ne_coe.2 hrs))
      (fun r => measurableSet_rankPairCell r.1),
    tsum_fintype]
  simp only [rankPairCell, Measure.prod_prod, rankChamber_measure, pow_two,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]

/-- Unit-supported strict rank vectors, the full-measure part on which the
finite chamber label is defined uniquely. -/
def goodRankSet : Set (Four → ℝ) :=
  inUnitSet ∩ ⋃ q : Perm4, rankChamber q

theorem measurableSet_goodRankSet : MeasurableSet goodRankSet := by
  exact measurableSet_inUnitSet.inter
    (MeasurableSet.iUnion measurableSet_rankChamber)

theorem ae_goodRankSet : ∀ᵐ u ∂rankMeasure, u ∈ goodRankSet := by
  have hchambers : ∀ᵐ u ∂rankMeasure,
      u ∈ ⋃ q : Perm4, rankChamber q := by
    filter_upwards [rankChamber_iUnion_ae_univ] with u hu
    exact hu.mpr trivial
  filter_upwards [ae_inUnit, hchambers] with u hu hc
  exact ⟨hu, hc⟩

theorem goodRankSet_measure : rankMeasure goodRankSet = 1 := by
  have h := (ae_mem_iff_measure_eq
    measurableSet_goodRankSet.nullMeasurableSet).mp ae_goodRankSet
  simpa only [measure_univ] using h

theorem ae_prod_goodRankSet :
    ∀ᵐ uv ∂rankMeasure.prod rankMeasure,
      uv ∈ goodRankSet ×ˢ goodRankSet := by
  apply (ae_mem_iff_measure_eq
    (measurableSet_goodRankSet.prod measurableSet_goodRankSet).nullMeasurableSet).2
  simp [goodRankSet_measure]

/-- The analytic dihedral event in the rank-coordinate fiber above one fixed
strip vector. -/
def fixedStripEvent {n : ℕ} (π : Equiv.Perm (Fin n))
    (f : Circular.StripSample n) :
    Set ((Four → ℝ) × (Four → ℝ)) :=
  (fun uv => latentStepPoints π (f, uv)) ⁻¹' dihedralPointEvent

theorem measurableSet_fixedStripEvent {n : ℕ} (π : Equiv.Perm (Fin n))
    (f : Circular.StripSample n) : MeasurableSet (fixedStripEvent π f) := by
  exact measurableSet_dihedralPointEvent.preimage
    ((measurable_latentStepPoints π).comp (measurable_const.prodMk measurable_id))

theorem mem_fixedStripEvent_iff_successfulRankSet {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n)
    (u v : Four → ℝ) (hu : u ∈ goodRankSet) (hv : v ∈ goodRankSet) :
    (u, v) ∈ fixedStripEvent π f ↔
      (u, v) ∈ successfulRankSet π f := by
  have huunit : InUnit u := hu.1
  have hvunit : InUnit v := hv.1
  constructor
  · intro hevent
    simp only [goodRankSet, mem_inter_iff, mem_iUnion] at hu hv
    obtain ⟨qx, hqx⟩ := hu.2
    obtain ⟨qy, hqy⟩ := hv.2
    have hsuccess :=
      (latentStepPoints_mem_dihedralPointEvent_iff hn π f u v qx qy
        huunit hvunit hqx hqy).mp hevent
    simp only [successfulRankSet, mem_iUnion]
    let r : Perm4 × Perm4 := (qx.symm, qy.symm)
    have hr : r ∈ successfulRankPairs π f := by
      simp only [successfulRankPairs, Finset.mem_filter, Finset.mem_univ,
        true_and, r]
      exact hsuccess
    refine ⟨⟨r, hr⟩, ?_⟩
    simpa [rankPairCell, r] using And.intro hqx hqy
  · intro hsuccessSet
    simp only [successfulRankSet, mem_iUnion] at hsuccessSet
    obtain ⟨r, hrank⟩ := hsuccessSet
    have hsuccess : Circular.IsDihedral4
        (Circular.tiedStepPattern π ⟨f, r.1.1, r.1.2⟩) := by
      exact (Finset.mem_filter.mp r.2).2
    exact (latentStepPoints_mem_dihedralPointEvent_iff hn π f u v
      r.1.1.symm r.1.2.symm huunit hvunit
      (by simpa [rankPairCell] using hrank.1)
      (by simpa [rankPairCell] using hrank.2)).mpr (by simpa using hsuccess)

theorem fixedStripEvent_ae_eq_successfulRankSet {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    fixedStripEvent π f =ᵐ[rankMeasure.prod rankMeasure]
      successfulRankSet π f := by
  filter_upwards [ae_prod_goodRankSet] with uv huv
  exact propext
    (mem_fixedStripEvent_iff_successfulRankSet hn π f uv.1 uv.2 huv.1 huv.2)

theorem fixedStripEvent_measure {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    (rankMeasure.prod rankMeasure) (fixedStripEvent π f) =
      (successfulRankPairs π f).card * ((24 : ℝ≥0∞)⁻¹) ^ 2 := by
  rw [measure_congr (fixedStripEvent_ae_eq_successfulRankSet hn π f)]
  exact successfulRankSet_measure π f

/-- Successful rank pairs, fibered over the strip vector, are exactly the
literal successful tied samples. -/
noncomputable def successfulRankSigmaEquiv {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (Σ f : Circular.StripSample n, ↑(successfulRankPairs π f)) ≃
      {z : Circular.TiedStripSample n //
        Circular.IsDihedral4 (Circular.tiedStepPattern π z)} where
  toFun z :=
    ⟨⟨z.1, z.2.1.1, z.2.1.2⟩, (Finset.mem_filter.mp z.2.2).2⟩
  invFun z :=
    ⟨z.1.strips, ⟨(z.1.xRanks, z.1.yRanks), by
      simp only [successfulRankPairs, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact z.2⟩⟩
  left_inv z := by cases z with | mk f r => cases r with | mk r hr => cases r; rfl
  right_inv z := by cases z with | mk z hz => cases z; rfl

theorem sum_successfulRankPairs_card {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    ∑ f : Circular.StripSample n, (successfulRankPairs π f).card =
      Circular.tiedDihedralCount π := by
  calc
    ∑ f : Circular.StripSample n, (successfulRankPairs π f).card =
        ∑ f : Circular.StripSample n,
          Fintype.card ↑(successfulRankPairs π f) := by simp
    _ = Fintype.card
        (Σ f : Circular.StripSample n, ↑(successfulRankPairs π f)) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card
        {z : Circular.TiedStripSample n //
          Circular.IsDihedral4 (Circular.tiedStepPattern π z)} :=
      Fintype.card_congr (successfulRankSigmaEquiv π)
    _ = Circular.tiedDihedralCount π := by
      rw [Circular.tiedDihedralCount, ← Fintype.card_subtype]

/-- The analytic event pulled back to the grouped latent source. -/
def latentDihedralEvent {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Set (Circular.StripSample n × ((Four → ℝ) × (Four → ℝ))) :=
  latentStepPoints π ⁻¹' dihedralPointEvent

theorem measurableSet_latentDihedralEvent {n : ℕ}
    (π : Equiv.Perm (Fin n)) : MeasurableSet (latentDihedralEvent π) :=
  measurableSet_dihedralPointEvent.preimage (measurable_latentStepPoints π)

theorem latentFourMeasure_eq_sum {n : ℕ} [Nonempty (Fin n)] :
    latentFourMeasure n =
      ∑ f : Circular.StripSample n,
        ((n : ℝ≥0∞)⁻¹) ^ 4 •
          ((Measure.dirac f).prod (rankMeasure.prod rankMeasure)) := by
  rw [latentFourMeasure, stripVectorMeasure_eq_sum,
    ← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]
  simp only [Measure.prod_smul_left]

theorem dirac_prod_latentDihedralEvent {n : ℕ}
    (π : Equiv.Perm (Fin n)) (f : Circular.StripSample n) :
    ((Measure.dirac f).prod (rankMeasure.prod rankMeasure))
        (latentDihedralEvent π) =
      (rankMeasure.prod rankMeasure) (fixedStripEvent π f) := by
  rw [Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left (measurableSet_latentDihedralEvent π)]
  rfl

theorem latentDihedralEvent_measure {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) :
    latentFourMeasure n (latentDihedralEvent π) =
      (Circular.tiedDihedralCount π : ℝ≥0∞) *
        ((n : ℝ≥0∞)⁻¹) ^ 4 * ((24 : ℝ≥0∞)⁻¹) ^ 2 := by
  let w : ℝ≥0∞ := ((n : ℝ≥0∞)⁻¹) ^ 4
  let r : ℝ≥0∞ := ((24 : ℝ≥0∞)⁻¹) ^ 2
  rw [latentFourMeasure_eq_sum,
    Measure.finsetSum_apply Finset.univ (fun f : Circular.StripSample n =>
      w • (Measure.dirac f).prod (rankMeasure.prod rankMeasure))
      (latentDihedralEvent π)]
  simp_rw [Measure.smul_apply, dirac_prod_latentDihedralEvent,
    fixedStripEvent_measure hn]
  change (∑ f : Circular.StripSample n,
      w * ((successfulRankPairs π f).card * r)) = _
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hsum : (∑ f : Circular.StripSample n,
      ((successfulRankPairs π f).card : ℝ≥0∞)) =
      (Circular.tiedDihedralCount π : ℝ≥0∞) := by
    exact_mod_cast sum_successfulRankPairs_card π
  rw [hsum]
  simp only [w, r]
  ring

/-- Therefore four iid samples from the Borel step permuton have exactly the
same ENNReal event mass as the literal finite tied model. -/
theorem iidStepMeasure_dihedralPointEvent {n : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    (Measure.pi (fun _ : Four => stepMeasure π)) dihedralPointEvent =
      (Circular.tiedDihedralCount π : ℝ≥0∞) *
        ((n : ℝ≥0∞)⁻¹) ^ 4 * ((24 : ℝ≥0∞)⁻¹) ^ 2 := by
  rw [← map_latentStepPoints hn π,
    Measure.map_apply (measurable_latentStepPoints π)
      measurableSet_dihedralPointEvent]
  exact latentDihedralEvent_measure hn π

/-- The analytic density of a step permuton is the literal finite tied-sample
density (and hence the global density used by `Circular`). -/
theorem dihedralDensity_stepPermuton {n : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    dihedralDensity (stepPermuton hn π) =
      (Circular.globalTiedDihedralDensity π : ℝ) := by
  rw [dihedralDensity]
  change (Measure.pi (fun _ : Four => stepMeasure π)
    dihedralPointEvent).toReal = _
  rw [iidStepMeasure_dihedralPointEvent hn π]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow, ENNReal.toReal_inv]
  rw [Circular.globalTiedDihedralDensity,
    ← Circular.tiedDihedralCount_eq_globalTiedDihedralCount,
    ← Circular.card_tiedStripSample_eq_card_globalTiedSample,
    Circular.card_tiedStripSample_eq_total]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnR]
  ring

end QuartetDistance.Permuton
