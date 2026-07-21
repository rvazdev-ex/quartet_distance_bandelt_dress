import QuartetDistance.Circular

/-!
# The literal tied-sample count

This module identifies the global distinct/collision parametrization in
`Circular.lean` with the literal finite space of four strip choices and two
independent tie rankings.  In particular, it checks the multiplicity of the
injective branch rather than relying only on an equality of total cardinalities.
-/

namespace QuartetDistance.Circular

open Function

theorem fourSubset_card {n : ℕ} (q : FourSubset n) : q.1.card = 4 := by
  have h : True ∧ q.1.card = 4 := by
    simpa only [FourSubset, Finset.mem_powersetCard, Finset.subset_univ] using q.2
  exact h.2

/-- The unordered range of an injective four-tuple. -/
def stripRange {n : ℕ} (f : StripSample n) (hf : Function.Injective f) :
    FourSubset n :=
  ⟨Finset.univ.map ⟨f, hf⟩, by simp⟩

/-- Sorting an injective four-tuple gives its canonical increasing
enumeration. -/
theorem enumerateFour_stripRange {n : ℕ} (f : StripSample n)
    (hf : Function.Injective f) :
    (enumerateFour (stripRange f hf).1 (fourSubset_card (stripRange f hf)) :
        Four → Fin n) =
      f ∘ Tuple.sort f := by
  symm
  apply Finset.orderEmbOfFin_unique (fourSubset_card (stripRange f hf))
  · intro i
    simp [stripRange]
  · exact (Tuple.monotone_sort f).strictMono_of_injective
      (hf.comp (Tuple.sort f).injective)

/-- The sorted-position permutation attached to an injective strip sample. -/
def stripEnumerationPermutation {n : ℕ} (f : StripSample n)
    (_hf : Function.Injective f) : Perm4 :=
  Tuple.sort f

/-- Injective four-tuples are exactly an unordered four-set together with one
of its `24` enumerations. -/
noncomputable def injectiveStripSampleDataEquiv (n : ℕ) :
    {f : StripSample n // Function.Injective f} ≃ FourSubset n × Perm4 where
  toFun f := ⟨stripRange f.1 f.2, stripEnumerationPermutation f.1 f.2⟩
  invFun z :=
    ⟨fun i ↦ enumerateFour z.1.1 (fourSubset_card z.1) (z.2.symm i),
      (enumerateFour z.1.1 (fourSubset_card z.1)).injective.comp z.2.symm.injective⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    have henum := congrFun (enumerateFour_stripRange f.1 f.2)
      ((Tuple.sort f.1).symm i)
    simpa [stripEnumerationPermutation] using henum
  right_inv z := by
    rcases z with ⟨q, σ⟩
    apply Prod.ext
    · apply Subtype.ext
      ext x
      constructor
      · rintro hx
        simp only [stripRange, Finset.mem_map, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        exact enumerateFour_mem q.1 (fourSubset_card q) (σ.symm i)
      · intro hx
        have hrange :
            Finset.univ.map (enumerateFour q.1 (fourSubset_card q)) = q.1 :=
          range_enumerateFour q.1 (fourSubset_card q)
        have hx' : x ∈ Finset.univ.map (enumerateFour q.1 (fourSubset_card q)) := by
          rw [hrange]
          exact hx
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hx'
        obtain ⟨i, hi⟩ := hx'
        apply Finset.mem_map.mpr
        exact ⟨σ i, Finset.mem_univ _, by simpa using hi⟩
    · apply Equiv.ext
      intro i
      let g : Four → Fin n :=
        fun j ↦ enumerateFour q.1 (fourSubset_card q) (σ.symm j)
      have hg : Function.Injective g :=
        (enumerateFour q.1 (fourSubset_card q)).injective.comp σ.symm.injective
      have hsort : Tuple.sort g = σ := by
        symm
        apply Equiv.ext
        intro j
        apply hg
        have hmono : Monotone (g ∘ σ) := by
          intro a b hab
          dsimp only [g, Function.comp_apply]
          rw [σ.symm_apply_apply, σ.symm_apply_apply]
          change
            ((q.1.orderIsoOfFin (fourSubset_card q) a : q.1) : Fin n) ≤
              ((q.1.orderIsoOfFin (fourSubset_card q) b : q.1) : Fin n)
          exact (q.1.orderIsoOfFin (fourSubset_card q)).monotone hab
        have hcomp := (Tuple.comp_sort_eq_comp_iff_monotone (f := g) (σ := σ)).2 hmono
        exact congrFun hcomp j
      change Tuple.sort g i = σ i
      exact congrArg (fun τ : Perm4 ↦ τ i) hsort

/-! ## The pointwise tie-ranking bridge -/

/-- Sorting by `(strip,tie-rank)` makes the strip coordinate monotone. -/
theorem monotone_strips_comp_tiedStripOrder {n : ℕ} (f : StripSample n)
    (ranks : Perm4) : Monotone (f ∘ tiedStripOrder f ranks) := by
  intro i j hij
  have hkey := (Tuple.monotone_sort (tiedStripKey f ranks)) hij
  change (f (tiedStripOrder f ranks i)).val ≤
    (f (tiedStripOrder f ranks j)).val
  change
    4 * (f (tiedStripOrder f ranks i)).val +
        (ranks (tiedStripOrder f ranks i)).val ≤
      4 * (f (tiedStripOrder f ranks j)).val +
        (ranks (tiedStripOrder f ranks j)).val at hkey
  have hi := (ranks (tiedStripOrder f ranks i)).isLt
  have hj := (ranks (tiedStripOrder f ranks j)).isLt
  omega

/-- On distinct strips, lexicographic sorting is independent of the supplied
tie rankings. -/
theorem tiedStripOrder_eq_sort_of_injective {n : ℕ} (f : StripSample n)
    (ranks : Perm4) (hf : Function.Injective f) :
    tiedStripOrder f ranks = Tuple.sort f := by
  apply Equiv.ext
  intro i
  apply hf
  have hfun :
      f ∘ tiedStripOrder f ranks = f ∘ Tuple.sort f :=
    Tuple.unique_monotone (monotone_strips_comp_tiedStripOrder f ranks)
      (Tuple.monotone_sort f)
  exact congrFun hfun i

/-- The increasing enumeration of the image of an injective strip tuple
under a permutation is the sorted tuple of image values. -/
theorem enumerateFour_map_stripRange {n : ℕ} (f : StripSample n)
    (hf : Function.Injective f) (π : Equiv.Perm (Fin n)) :
    let s := (stripRange f hf).1
    let hs : s.card = 4 := fourSubset_card (stripRange f hf)
    let himage : (s.map π.toEmbedding).card = 4 := by
      simpa only [Finset.card_map] using hs
    (enumerateFour (s.map π.toEmbedding) himage : Four → Fin n) =
      (fun i ↦ π (f i)) ∘ Tuple.sort (fun i ↦ π (f i)) := by
  dsimp only
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    simp [stripRange]
  · exact (Tuple.monotone_sort (fun i ↦ π (f i))).strictMono_of_injective
      (π.injective.comp (hf.comp (Tuple.sort (fun i ↦ π (f i))).injective))

/-- On an injective strip tuple, the standardized relative pattern is the
relative permutation of the two sorting permutations. -/
theorem relativePattern_stripRange {n : ℕ} (π : Equiv.Perm (Fin n))
    (f : StripSample n) (hf : Function.Injective f) :
    relativePattern π (stripRange f hf).1 (fourSubset_card (stripRange f hf)) =
      relativePermutation (Tuple.sort f) (Tuple.sort (fun i ↦ π (f i))) := by
  let s := (stripRange f hf).1
  let hs : s.card = 4 := fourSubset_card (stripRange f hf)
  let himage : (s.map π.toEmbedding).card = 4 := by
    simpa only [Finset.card_map] using hs
  let ex := enumerateFour s hs
  let ey := enumerateFour (s.map π.toEmbedding) himage
  have hex : (ex : Four → Fin n) = f ∘ Tuple.sort f := by
    simpa only [s, hs, ex] using enumerateFour_stripRange f hf
  have hey : (ey : Four → Fin n) =
      (fun i ↦ π (f i)) ∘ Tuple.sort (fun i ↦ π (f i)) := by
    simpa only [s, hs, himage, ey] using enumerateFour_map_stripRange f hf π
  apply Equiv.ext
  intro i
  apply ey.injective
  change ey (relativePattern π s hs i) =
    ey (relativePermutation (Tuple.sort f) (Tuple.sort (fun i ↦ π (f i))) i)
  rw [show ey (relativePattern π s hs i) = π (ex i) from
    relativePattern_spec π s hs i]
  rw [congrFun hex i]
  change π ((f ∘ Tuple.sort f) i) =
    ey ((Tuple.sort (fun i ↦ π (f i))).symm (Tuple.sort f i))
  rw [congrFun hey
    ((Tuple.sort (fun i ↦ π (f i))).symm (Tuple.sort f i))]
  simp [Function.comp_apply]

/-- The uniform lexicographic formula and the piecewise `tiedStepPattern`
agree pointwise on the injective branch. -/
theorem tiedCollisionPattern_eq_tiedStepPattern_of_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n)
    (hz : Function.Injective z.strips) :
    tiedCollisionPattern π z = tiedStepPattern π z := by
  rw [tiedStepPattern_of_injective π z hz]
  rw [tiedCollisionPattern,
    tiedStripOrder_eq_sort_of_injective z.strips z.xRanks hz,
    tiedStripOrder_eq_sort_of_injective (fun i ↦ π (z.strips i)) z.yRanks
      (π.injective.comp hz)]
  exact (relativePattern_stripRange π z.strips hz).symm

/-- On the collision branch, `tiedStepPattern` uses the lexicographic formula
by definition. -/
theorem tiedCollisionPattern_eq_tiedStepPattern_of_not_injective {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n)
    (hz : ¬ Function.Injective z.strips) :
    tiedCollisionPattern π z = tiedStepPattern π z := by
  simp only [tiedStepPattern, dif_neg hz]

/-- The ostensibly piecewise step pattern is exactly the single natural
lexicographic pattern on every tied sample. -/
theorem tiedCollisionPattern_eq_tiedStepPattern {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n) :
    tiedCollisionPattern π z = tiedStepPattern π z := by
  classical
  by_cases hz : Function.Injective z.strips
  · exact tiedCollisionPattern_eq_tiedStepPattern_of_injective π z hz
  · exact tiedCollisionPattern_eq_tiedStepPattern_of_not_injective π z hz

theorem isDihedral4_tiedCollisionPattern_iff_tiedStepPattern {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n) :
    IsDihedral4 (tiedCollisionPattern π z) ↔
      IsDihedral4 (tiedStepPattern π z) := by
  rw [tiedCollisionPattern_eq_tiedStepPattern]

/-! ## Equivalence with the global distinct/collision parametrization -/

/-- Adding the two independent tie rankings to
`injectiveStripSampleDataEquiv` gives exactly `DistinctTiedSample`. -/
noncomputable def injectiveTiedSampleDataEquiv (n : ℕ) :
    {z : TiedStripSample n // Function.Injective z.strips} ≃
      DistinctTiedSample n :=
  (injectiveTiedStripSampleEquiv n).trans <|
    (Equiv.prodCongr (injectiveStripSampleDataEquiv n)
      (Equiv.refl (Perm4 × Perm4))).trans <|
        Equiv.prodAssoc (FourSubset n) Perm4 (Perm4 × Perm4)

@[simp] theorem injectiveTiedSampleDataEquiv_apply {n : ℕ}
    (z : TiedStripSample n) (hz : Function.Injective z.strips) :
    injectiveTiedSampleDataEquiv n ⟨z, hz⟩ =
      ⟨stripRange z.strips hz, Tuple.sort z.strips, z.xRanks, z.yRanks⟩ := by
  rfl

/-- The literal tied-sample space is equivalent to the global sample space:
injective tuples go to their four-set, enumeration, and two rankings, while
noninjective tuples retain their collision certificate. -/
noncomputable def tiedStripSampleGlobalEquiv (n : ℕ) :
    TiedStripSample n ≃ GlobalTiedSample n :=
  (Equiv.sumCompl (fun z : TiedStripSample n ↦ Function.Injective z.strips)).symm.trans <|
    Equiv.sumCongr (injectiveTiedSampleDataEquiv n)
      (Equiv.refl (CollisionTiedSample n))

theorem tiedStripSampleGlobalEquiv_apply_of_injective {n : ℕ}
    (z : TiedStripSample n) (hz : Function.Injective z.strips) :
    tiedStripSampleGlobalEquiv n z = Sum.inl
      ⟨stripRange z.strips hz, Tuple.sort z.strips, z.xRanks, z.yRanks⟩ := by
  classical
  simp [tiedStripSampleGlobalEquiv, hz]

theorem tiedStripSampleGlobalEquiv_apply_of_not_injective {n : ℕ}
    (z : TiedStripSample n) (hz : ¬ Function.Injective z.strips) :
    tiedStripSampleGlobalEquiv n z = Sum.inr ⟨z, hz⟩ := by
  classical
  simp [tiedStripSampleGlobalEquiv, hz]

/-- The success event is preserved pointwise by the global
reparametrization. -/
theorem isDihedral4_tiedStepPattern_iff_globalTiedDihedral {n : ℕ}
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n) :
    IsDihedral4 (tiedStepPattern π z) ↔
      GlobalTiedDihedral π (tiedStripSampleGlobalEquiv n z) := by
  classical
  by_cases hz : Function.Injective z.strips
  · rw [tiedStripSampleGlobalEquiv_apply_of_injective z hz]
    simp only [GlobalTiedDihedral]
    exact isDihedral4_tiedStepPattern_iff_of_injective π z hz
  · rw [tiedStripSampleGlobalEquiv_apply_of_not_injective z hz]
    rfl

/-- Equivalence between the literal successful samples and the successful
samples in the global parametrization. -/
noncomputable def tiedDihedralSampleEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) :
    {z : TiedStripSample n // IsDihedral4 (tiedStepPattern π z)} ≃
      {z : GlobalTiedSample n // GlobalTiedDihedral π z} :=
  Equiv.subtypeEquiv (tiedStripSampleGlobalEquiv n)
    (isDihedral4_tiedStepPattern_iff_globalTiedDihedral π)

/-- On the injective branch, successful tied samples are a successful
four-set together with the three independent `Perm4` choices. -/
noncomputable def injectiveTiedDihedralSampleEquiv {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    {z : {z : TiedStripSample n // Function.Injective z.strips} //
      IsDihedral4 (tiedStepPattern π z.1)} ≃
      {d : DistinctTiedSample n // DihedralOn π d.1.1} :=
  Equiv.subtypeEquiv (injectiveTiedSampleDataEquiv n) (fun z ↦ by
    change IsDihedral4 (tiedStepPattern π z.1) ↔
      DihedralOn π (stripRange z.1.strips z.2).1
    exact isDihedral4_tiedStepPattern_iff_of_injective π z.1 z.2)

/-- Exact multiplicity of the injective branch. -/
theorem card_injectiveTiedSample_eq_distinct (n : ℕ) :
    Fintype.card {z : TiedStripSample n // Function.Injective z.strips} =
      Nat.choose n 4 * 24 ^ 3 := by
  rw [card_injectiveTiedStripSample, ← twentyFour_mul_choose_eq_fallingFour]
  ring

/-- Exact successful multiplicity on the injective branch. -/
theorem card_injectiveTiedDihedralSample {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    Fintype.card
        {z : {z : TiedStripSample n // Function.Injective z.strips} //
          IsDihedral4 (tiedStepPattern π z.1)} =
      permutationK π * 24 ^ 3 := by
  rw [Fintype.card_congr (injectiveTiedDihedralSampleEquiv π)]
  change Fintype.card
    {d : FourSubset n × DistinctRankData // DihedralOn π d.1.1} = _
  rw [Fintype.card_congr
    (Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun q : FourSubset n ↦ DihedralOn π q.1))]
  rw [Fintype.card_prod]
  have hq : Fintype.card {q : FourSubset n // DihedralOn π q.1} =
      permutationK π := by
    rw [Fintype.card_congr (dihedralFourSubsetEquiv π), Fintype.card_coe]
    rfl
  rw [hq]
  simp [DistinctRankData, card_perm4]

/-- Literal filter count over all tied strip samples. -/
noncomputable def tiedDihedralCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun z : TiedStripSample n ↦
    IsDihedral4 (tiedStepPattern π z)).card

/-- The same literal count, stated using the uniform lexicographic pattern
that arises directly from sampling. -/
noncomputable def tiedCollisionDihedralCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun z : TiedStripSample n ↦
    IsDihedral4 (tiedCollisionPattern π z)).card

theorem tiedCollisionDihedralCount_eq_tiedDihedralCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    tiedCollisionDihedralCount π = tiedDihedralCount π := by
  classical
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isDihedral4_tiedCollisionPattern_iff_tiedStepPattern π z

/-- The literal all-samples filter count is exactly the count used by the
global finite model. -/
theorem tiedDihedralCount_eq_globalTiedDihedralCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    tiedDihedralCount π = globalTiedDihedralCount π := by
  classical
  rw [tiedDihedralCount, globalTiedDihedralCount,
    ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (tiedDihedralSampleEquiv π)

theorem tiedCollisionDihedralCount_eq_globalTiedDihedralCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    tiedCollisionDihedralCount π = globalTiedDihedralCount π := by
  rw [tiedCollisionDihedralCount_eq_tiedDihedralCount,
    tiedDihedralCount_eq_globalTiedDihedralCount]

/-- The literal all-samples density. -/
noncomputable def tiedDihedralDensity {n : ℕ}
    (π : Equiv.Perm (Fin n)) : ℚ :=
  (tiedDihedralCount π : ℚ) / Fintype.card (TiedStripSample n)

theorem tiedDihedralDensity_eq_globalTiedDihedralDensity {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    tiedDihedralDensity π = globalTiedDihedralDensity π := by
  rw [tiedDihedralDensity, globalTiedDihedralDensity,
    tiedDihedralCount_eq_globalTiedDihedralCount]
  rw [show Fintype.card (TiedStripSample n) =
      Fintype.card (GlobalTiedSample n) from
    Fintype.card_congr (tiedStripSampleGlobalEquiv n)]

/-- The literal and global sample spaces have exactly the same cardinality. -/
theorem card_tiedStripSample_eq_card_globalTiedSample (n : ℕ) :
    Fintype.card (TiedStripSample n) =
      Fintype.card (GlobalTiedSample n) :=
  Fintype.card_congr (tiedStripSampleGlobalEquiv n)

/-- Both presentations contain exactly `n^4 * 24^2` samples. -/
theorem card_tiedStripSample_eq_total (n : ℕ) :
    Fintype.card (TiedStripSample n) = n ^ 4 * 24 ^ 2 :=
  card_tiedStripSample n

theorem card_globalTiedSample_eq_tied_total (n : ℕ) :
    Fintype.card (GlobalTiedSample n) = n ^ 4 * 24 ^ 2 :=
  card_globalTiedSample_eq_total n

end QuartetDistance.Circular
