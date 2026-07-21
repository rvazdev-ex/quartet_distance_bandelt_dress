import Mathlib

/-!
# Circular orders, relative patterns, and the step-permuton collision bound

This file formalizes the finite circular-order part of the Bandelt--Dress
argument.  A `CircularOrder n` is a chosen linear representative of a circular
order on `Fin n`: it sends slots to labels.  All definitions used below are
invariant under changing the representative by a rotation or reversal, as is
captured on four points by `IsDihedral4`.

The only result imported from outside the elementary argument is represented
by the *proposition* `StepPermutonInequality π`.  It is not installed as an
axiom.  A caller supplies a proof of that proposition when applying
`circularCollisionBound`.  Its density is defined by a concrete finite sample
space, including explicit tie-rankings on the collision event; the remaining
theorems prove the finite reduction.
-/

namespace QuartetDistance.Circular

open scoped BigOperators

abbrev Four := Fin 4
abbrev Perm4 := Equiv.Perm Four

/-! ## Quartet splits and crossing splits -/

/-- A split is stored as a finite set of its (unordered) sides.  The
well-formedness predicate below says that it really is a `2+2` split of a
specified quartet. -/
abbrev QuartetSplit (X : Type*) := Finset (Finset X)

/-- The unordered pair containing `a` and `b`. -/
def pair [DecidableEq X] (a b : X) : Finset X := {a, b}

/-- The split `ac | bd`, written in the order in which the four arguments
occur around a circle. -/
def splitOf [DecidableEq X] (a b c d : X) : QuartetSplit X :=
  {pair a c, pair b d}

/-- Apply an embedding to every point of a quartet split. -/
def mapSplit [DecidableEq X] [DecidableEq Y] (f : X ↪ Y)
    (s : QuartetSplit X) : QuartetSplit Y :=
  s.map
    { toFun := fun A => A.map f
      inj' := Finset.map_injective f }

theorem mapSplit_injective [DecidableEq X] [DecidableEq Y] (f : X ↪ Y) :
    Function.Injective (mapSplit f) := by
  intro s t h
  exact Finset.map_injective _ h

@[simp] theorem mapSplit_mapSplit [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (f : X ↪ Y) (g : Y ↪ Z) (s : QuartetSplit X) :
    mapSplit g (mapSplit f s) = mapSplit (f.trans g) s := by
  ext B
  simp [mapSplit, Finset.map_map]

/-- The canonical split of four cyclic slots: positions `0,2` are opposite,
as are positions `1,3`. -/
def canonicalCrossing : QuartetSplit Four := splitOf 0 1 2 3

/-- The crossing split of four distinct labels in their circular order. -/
def crossing [DecidableEq X] (q : Four ↪ X) : QuartetSplit X :=
  mapSplit q canonicalCrossing

/-- A well-formed `2+2` split of `Q`.  Giving the four distinct elements in
an order whose opposite pairs are the desired sides is equivalent to the
usual two-disjoint-two-element-sides definition. -/
def IsQuartetSplit [DecidableEq X] (Q : Finset X) (s : QuartetSplit X) : Prop :=
  ∃ q : Four ↪ X, Q = Finset.univ.map q ∧ s = crossing q

theorem crossing_isQuartetSplit [DecidableEq X] (q : Four ↪ X) :
    IsQuartetSplit (Finset.univ.map q) (crossing q) := by
  exact ⟨q, rfl, rfl⟩

/-! ## The eight dihedral patterns -/

/-- A four-point permutation is dihedral when it preserves the canonical
pairing of opposite slots.  This semantic definition avoids any convention
about whether a one-line pattern or its inverse records the second order. -/
def IsDihedral4 (σ : Perm4) : Prop :=
  mapSplit σ.toEmbedding canonicalCrossing = canonicalCrossing

/-- Build a permutation of `Fin 4` from its one-line notation. -/
def perm4OfTuples (a b c d ia ib ic id : Four)
    (hl : Function.LeftInverse ![ia, ib, ic, id] ![a, b, c, d])
    (hr : Function.RightInverse ![ia, ib, ic, id] ![a, b, c, d]) : Perm4 where
  toFun := ![a, b, c, d]
  invFun := ![ia, ib, ic, id]
  left_inv := hl
  right_inv := hr

def p1234 : Perm4 := perm4OfTuples 0 1 2 3 0 1 2 3 (by decide) (by decide)
def p1432 : Perm4 := perm4OfTuples 0 3 2 1 0 3 2 1 (by decide) (by decide)
def p2143 : Perm4 := perm4OfTuples 1 0 3 2 1 0 3 2 (by decide) (by decide)
def p2341 : Perm4 := perm4OfTuples 1 2 3 0 3 0 1 2 (by decide) (by decide)
def p3214 : Perm4 := perm4OfTuples 2 1 0 3 2 1 0 3 (by decide) (by decide)
def p3412 : Perm4 := perm4OfTuples 2 3 0 1 2 3 0 1 (by decide) (by decide)
def p4123 : Perm4 := perm4OfTuples 3 0 1 2 1 2 3 0 (by decide) (by decide)
def p4321 : Perm4 := perm4OfTuples 3 2 1 0 3 2 1 0 (by decide) (by decide)

/-- The displayed eight-pattern set from the paper (using zero-based values
internally). -/
def dihedral4 : Finset Perm4 :=
  {p1234, p1432, p2143, p2341, p3214, p3412, p4123, p4321}

instance (σ : Perm4) : Decidable (IsDihedral4 σ) :=
  inferInstanceAs (Decidable (mapSplit σ.toEmbedding canonicalCrossing = canonicalCrossing))

theorem isDihedral4_iff_mem : ∀ σ : Perm4, IsDihedral4 σ ↔ σ ∈ dihedral4 := by
  decide

theorem card_dihedral4 : dihedral4.card = 8 := by decide

theorem isDihedral4_refl : IsDihedral4 (Equiv.refl Four) := by decide

theorem isDihedral4_inv (σ : Perm4) : IsDihedral4 σ.symm ↔ IsDihedral4 σ := by
  revert σ
  decide

theorem mem_dihedral4_inv (σ : Perm4) : σ.symm ∈ dihedral4 ↔ σ ∈ dihedral4 := by
  simpa only [← isDihedral4_iff_mem] using isDihedral4_inv σ

theorem crossing_comp (q : Four ↪ X) (σ : Perm4) [DecidableEq X] :
    crossing (σ.toEmbedding.trans q) = mapSplit q (mapSplit σ.toEmbedding canonicalCrossing) := by
  simp [crossing]

/-- Two four-point circular representatives have the same crossing split
exactly when their relative reindexing is one of the eight dihedral patterns. -/
theorem crossing_eq_iff_isDihedral4 [DecidableEq X] (q : Four ↪ X) (σ : Perm4) :
    crossing q = crossing (σ.toEmbedding.trans q) ↔ IsDihedral4 σ := by
  rw [crossing_comp, crossing, IsDihedral4]
  constructor
  · intro h
    exact mapSplit_injective q h.symm
  · intro h
    rw [h]

theorem crossing_eq_iff_mem_dihedral4 [DecidableEq X] (q : Four ↪ X) (σ : Perm4) :
    crossing q = crossing (σ.toEmbedding.trans q) ↔ σ ∈ dihedral4 := by
  rw [crossing_eq_iff_isDihedral4, isDihedral4_iff_mem]

/-! ## Full circular representatives and restricted relative patterns -/

/-- A complete, duplicate-free linear representative of a circular order on
`Fin n`.  An equivalence is the permutation version of a nodup complete list. -/
abbrev CircularOrder (n : ℕ) := Equiv.Perm (Fin n)

/-- Turn a duplicate-free exhaustive list into the corresponding circular
representative.  This is the list formulation of `CircularOrder`. -/
def circularOrderOfList (l : List (Fin n)) (hnodup : l.Nodup)
    (hcomplete : ∀ x : Fin n, x ∈ l) (hlength : l.length = n) : CircularOrder n :=
  (finCongr hlength.symm).trans (hnodup.getEquivOfForallMemList l hcomplete)

/-- The complete nodup list underlying a permutation representative. -/
def circularOrderList (C : CircularOrder n) : List (Fin n) := List.ofFn C

@[simp] theorem length_circularOrderList (C : CircularOrder n) :
    (circularOrderList C).length = n := by simp [circularOrderList]

theorem nodup_circularOrderList (C : CircularOrder n) :
    (circularOrderList C).Nodup := by
  simpa [circularOrderList] using List.nodup_ofFn.mpr C.injective

theorem mem_circularOrderList (C : CircularOrder n) (x : Fin n) :
    x ∈ circularOrderList C := by
  simpa [circularOrderList] using C.surjective x

/-- The position in `C'` of the label occupying position `i` in `C`. -/
def relativePermutation (C C' : CircularOrder n) : Equiv.Perm (Fin n) :=
  C.trans C'.symm

@[simp] theorem relativePermutation_apply (C C' : CircularOrder n) (i : Fin n) :
    relativePermutation C C' i = C'.symm (C i) := rfl

@[simp] theorem relativePermutation_self (C : CircularOrder n) :
    relativePermutation C C = Equiv.refl (Fin n) := by
  ext i
  simp [relativePermutation]

@[simp] theorem relativePermutation_symm (C C' : CircularOrder n) :
    (relativePermutation C C').symm = relativePermutation C' C := by
  ext i
  simp [relativePermutation]

/-- The increasing enumeration of a four-element subset. -/
def enumerateFour (s : Finset (Fin n)) (h : s.card = 4) : Four ↪ Fin n :=
  (s.orderIsoOfFin h).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem enumerateFour_mem (s : Finset (Fin n)) (h : s.card = 4) (i : Four) :
    enumerateFour s h i ∈ s :=
  (s.orderIsoOfFin h i).property

@[simp] theorem range_enumerateFour (s : Finset (Fin n)) (h : s.card = 4) :
    Finset.univ.map (enumerateFour s h) = s := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact enumerateFour_mem s h i
  · intro x hx
    let y : s := ⟨x, hx⟩
    let i : Four := (s.orderIsoOfFin h).symm y
    have hi : enumerateFour s h i = x := by
      change ((s.orderIsoOfFin h) i : s).1 = x
      simp [i, y]
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨i, hi⟩

/-- A permutation restricts to an equivalence between a subset and its image. -/
def imageSubsetEquiv (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    {x // x ∈ s} ≃ {y // y ∈ s.map π.toEmbedding} :=
  Equiv.subtypeEquiv π (by intro x; simp)

/-- Standardization of the values `π(i₁),...,π(i₄)`, where the `i`'s are the
increasing enumeration of `s`.  It maps an old rank to its new rank. -/
def relativePattern (π : Equiv.Perm (Fin n)) (s : Finset (Fin n))
    (h : s.card = 4) : Perm4 :=
  (s.orderIsoOfFin h).toEquiv.trans <|
    (imageSubsetEquiv π s).trans <|
      ((s.map π.toEmbedding).orderIsoOfFin
        (by simpa only [Finset.card_map] using h)).toEquiv.symm

/-- The defining property of standardization: enumerating the image at the
new rank gives the image under `π` of the old enumeration. -/
theorem relativePattern_spec (π : Equiv.Perm (Fin n)) (s : Finset (Fin n))
    (h : s.card = 4) (i : Four) :
    enumerateFour (s.map π.toEmbedding)
        (by simpa only [Finset.card_map] using h)
        (relativePattern π s h i) =
      π (enumerateFour s h i) := by
  simp [relativePattern, enumerateFour, imageSubsetEquiv]

/-- The crossing split selected by `C` on the labels whose positions belong
to `s`. -/
def crossingOn (C : CircularOrder n) (s : Finset (Fin n)) (h : s.card = 4) :
    QuartetSplit (Fin n) :=
  crossing ((enumerateFour s h).trans C.toEmbedding)

theorem crossingOn_congr (C : CircularOrder n) {s t : Finset (Fin n)}
    (hst : s = t) (hs : s.card = 4) (ht : t.card = 4) :
    crossingOn C s hs = crossingOn C t ht := by
  subst t
  rfl

/-- The same four labels, enumerated in `C'` order. -/
def crossingOnSecond (C C' : CircularOrder n) (s : Finset (Fin n))
    (h : s.card = 4) : QuartetSplit (Fin n) :=
  let π := relativePermutation C C'
  crossingOn C' (s.map π.toEmbedding)
    (by simpa only [Finset.card_map] using h)

theorem relativePattern_labels (C C' : CircularOrder n) (s : Finset (Fin n))
    (h : s.card = 4) (i : Four) :
    let π := relativePermutation C C'
    let h' : (s.map π.toEmbedding).card = 4 := by
      simpa only [Finset.card_map] using h
    C' (enumerateFour (s.map π.toEmbedding) h' (relativePattern π s h i)) =
      C (enumerateFour s h i) := by
  dsimp only
  rw [relativePattern_spec]
  simp [relativePermutation]

set_option maxHeartbeats 800000

/-- Paper Lemma (relative permutation), in representative form. -/
theorem crossingOn_eq_iff_relativePattern (C C' : CircularOrder n)
    (s : Finset (Fin n)) (h : s.card = 4) :
    crossingOn C s h = crossingOnSecond C C' s h ↔
      IsDihedral4 (relativePattern (relativePermutation C C') s h) := by
  let π := relativePermutation C C'
  let h' : (s.map π.toEmbedding).card = 4 := by
    simpa only [Finset.card_map] using h
  let q : Four ↪ Fin n := (enumerateFour (s.map π.toEmbedding) h').trans C'.toEmbedding
  let σ : Perm4 := relativePattern π s h
  have hq : σ.toEmbedding.trans q = (enumerateFour s h).trans C.toEmbedding := by
    ext i
    exact congrArg Fin.val (relativePattern_labels C C' s h i)
  change crossing ((enumerateFour s h).trans C.toEmbedding) = crossing q ↔ IsDihedral4 σ
  rw [← hq]
  simpa only [eq_comm] using crossing_eq_iff_isDihedral4 q σ

set_option maxHeartbeats 200000

/-- A four-subset of positions has a dihedral relative pattern. -/
def DihedralOn (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∃ h : s.card = 4, IsDihedral4 (relativePattern π s h)

noncomputable instance (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    Decidable (DihedralOn π s) :=
  Classical.dec _

/-- Number of four-subsets on which a relative permutation preserves the
crossing split. -/
noncomputable def permutationK (π : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ.powersetCard 4).filter (DihedralOn π)).card

/-- The paper's `K(C,C')`. -/
noncomputable def K (C C' : CircularOrder n) : ℕ :=
  permutationK (relativePermutation C C')

theorem permutationK_le_choose (π : Equiv.Perm (Fin n)) :
    permutationK π ≤ Nat.choose n 4 := by
  rw [permutationK]
  calc
    ((Finset.univ.powersetCard 4).filter (DihedralOn π)).card ≤
        (Finset.univ.powersetCard 4).card := Finset.card_filter_le _ _
    _ = Nat.choose n 4 := by simp [Finset.card_powersetCard]

theorem K_le_choose (C C' : CircularOrder n) : K C C' ≤ Nat.choose n 4 :=
  permutationK_le_choose _

/-! ### The label-subset form of `K` -/

/-- Positions occupied in `C` by a set of labels. -/
def labelPositions (C : CircularOrder n) (Q : Finset (Fin n)) : Finset (Fin n) :=
  Q.map C.symm.toEmbedding

@[simp] theorem card_labelPositions (C : CircularOrder n) (Q : Finset (Fin n)) :
    (labelPositions C Q).card = Q.card := by
  simp [labelPositions]

@[simp] theorem labelPositions_map_order (C : CircularOrder n) (s : Finset (Fin n)) :
    labelPositions C (s.map C.toEmbedding) = s := by
  ext i
  simp [labelPositions]

theorem labelPositions_second (C C' : CircularOrder n) (Q : Finset (Fin n)) :
    labelPositions C' Q =
      (labelPositions C Q).map (relativePermutation C C').toEmbedding := by
  ext i
  simp only [labelPositions, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqi⟩
    refine ⟨C.symm q, ⟨q, hq, rfl⟩, ?_⟩
    simpa [relativePermutation] using hqi
  · rintro ⟨a, ⟨q, hq, hqa⟩, hai⟩
    refine ⟨q, hq, ?_⟩
    subst a
    simpa [relativePermutation] using hai

/-- Crossing split of a fixed *label* quartet under a circular order. -/
def crossingOnLabels (C : CircularOrder n) (Q : Finset (Fin n))
    (h : Q.card = 4) : QuartetSplit (Fin n) :=
  crossingOn C (labelPositions C Q) (by simpa only [card_labelPositions] using h)

/-- Equality of crossing splits on a label quartet is detected by the
restricted relative permutation. -/
theorem crossingOnLabels_eq_iff_relativePattern (C C' : CircularOrder n)
    (Q : Finset (Fin n)) (h : Q.card = 4) :
    crossingOnLabels C Q h = crossingOnLabels C' Q h ↔
      IsDihedral4
        (relativePattern (relativePermutation C C') (labelPositions C Q)
          (by simpa only [card_labelPositions] using h)) := by
  let s := labelPositions C Q
  let hs : s.card = 4 := by simpa only [s, card_labelPositions] using h
  have hleft : crossingOnLabels C Q h = crossingOn C s hs := by
    rfl
  have hright : crossingOnLabels C' Q h = crossingOnSecond C C' s hs := by
    unfold crossingOnLabels crossingOnSecond
    dsimp only
    apply crossingOn_congr C'
    exact labelPositions_second C C' Q
  rw [hleft, hright]
  exact crossingOn_eq_iff_relativePattern C C' s hs

/-- Predicate that the two orders select the same crossing split on the fixed
label set `Q`. -/
def CrossingAgreesOnLabels (C C' : CircularOrder n) (Q : Finset (Fin n)) : Prop :=
  ∃ h : Q.card = 4, crossingOnLabels C Q h = crossingOnLabels C' Q h

noncomputable instance (C C' : CircularOrder n) (Q : Finset (Fin n)) :
    Decidable (CrossingAgreesOnLabels C C' Q) := Classical.dec _

theorem crossingAgreesOnLabels_iff (C C' : CircularOrder n)
    (Q : Finset (Fin n)) :
    CrossingAgreesOnLabels C C' Q ↔
      DihedralOn (relativePermutation C C') (labelPositions C Q) := by
  constructor
  · rintro ⟨h, hagree⟩
    refine ⟨by simpa only [card_labelPositions] using h, ?_⟩
    exact (crossingOnLabels_eq_iff_relativePattern C C' Q h).mp hagree
  · rintro ⟨hpos, hdih⟩
    have hQ : Q.card = 4 := by simpa only [card_labelPositions] using hpos
    exact ⟨hQ, (crossingOnLabels_eq_iff_relativePattern C C' Q hQ).mpr hdih⟩

/-- `K`, counted directly over fixed label quartets. -/
noncomputable def labelK (C C' : CircularOrder n) : ℕ :=
  ((Finset.univ.powersetCard 4).filter (CrossingAgreesOnLabels C C')).card

/-- The label-subset count is exactly the position-subset count used in the
step-permuton reduction. -/
theorem labelK_eq_K (C C' : CircularOrder n) : labelK C C' = K C C' := by
  classical
  unfold labelK K permutationK
  apply Finset.card_bij (fun Q _ => labelPositions C Q)
  · intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hQ ⊢
    exact ⟨by simpa only [card_labelPositions] using hQ.1,
      (crossingAgreesOnLabels_iff C C' Q).mp hQ.2⟩
  · intro Q₁ hQ₁ Q₂ hQ₂ heq
    exact Finset.map_injective C.symm.toEmbedding heq
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
    let Q := s.map C.toEmbedding
    have hQcard : Q.card = 4 := by simpa [Q] using hs.1
    have hpositions : labelPositions C Q = s := by simp [Q]
    refine ⟨Q, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      refine ⟨hQcard, ?_⟩
      rw [crossingAgreesOnLabels_iff, hpositions]
      exact hs.2
    · exact hpositions

theorem crossingAgreesOnLabels_comm (C C' : CircularOrder n) (Q : Finset (Fin n)) :
    CrossingAgreesOnLabels C C' Q ↔ CrossingAgreesOnLabels C' C Q := by
  constructor <;> rintro ⟨h, heq⟩
  · exact ⟨h, heq.symm⟩
  · exact ⟨h, heq.symm⟩

theorem labelK_comm (C C' : CircularOrder n) : labelK C C' = labelK C' C := by
  classical
  unfold labelK
  congr 1
  ext Q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hQ, hagree⟩
    exact ⟨hQ, (crossingAgreesOnLabels_comm C C' Q).mp hagree⟩
  · rintro ⟨hQ, hagree⟩
    exact ⟨hQ, (crossingAgreesOnLabels_comm C C' Q).mpr hagree⟩

theorem K_comm (C C' : CircularOrder n) : K C C' = K C' C := by
  rw [← labelK_eq_K, ← labelK_eq_K, labelK_comm]

theorem labelK_self (C : CircularOrder n) : labelK C C = Nat.choose n 4 := by
  classical
  unfold labelK
  rw [Finset.filter_eq_self.2]
  · simp [Finset.card_powersetCard]
  · intro Q hQ
    have hcard : Q.card = 4 := by
      simpa only [Finset.mem_powersetCard, Finset.subset_univ, true_and] using hQ
    exact ⟨hcard, rfl⟩

theorem K_self (C : CircularOrder n) : K C C = Nat.choose n 4 := by
  rw [← labelK_eq_K]
  exact labelK_self C

/-! ## The step-permuton input and the finite collision bound -/

/-- Probability that four independent uniform strip indices are distinct.
This is `(n-1)(n-2)(n-3)/n^3`, after cancelling the first factor `n`. -/
def stepAlpha (n : ℕ) : ℚ :=
  ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / (n : ℚ) ^ 3

/-- Four independent choices of a strip, before conditioning on distinctness. -/
abbrev StripSample (n : ℕ) := Four → Fin n

/-- Injective strip samples are equivalently embeddings of four slots. -/
def injectiveStripSampleEquiv (n : ℕ) :
    {f : StripSample n // Function.Injective f} ≃ (Four ↪ Fin n) where
  toFun f := ⟨f.1, f.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The falling factorial `(n)₄`. -/
def fallingFour (n : ℕ) : ℕ := n * (n - 1) * (n - 2) * (n - 3)

theorem card_injectiveStripSample (n : ℕ) :
    Fintype.card {f : StripSample n // Function.Injective f} = fallingFour n := by
  rw [Fintype.card_congr (injectiveStripSampleEquiv n), Fintype.card_embedding_eq]
  simp [fallingFour, Nat.descFactorial_succ]
  ac_rfl

/-- Hence `stepAlpha` really is the fraction of the `n^4` strip samples that
have four distinct indices. -/
theorem stepAlpha_eq_injectiveStripFraction {n : ℕ} (hn : 4 ≤ n) :
    stepAlpha n =
      (Fintype.card {f : StripSample n // Function.Injective f} : ℚ) /
        (Fintype.card (StripSample n) : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  rw [card_injectiveStripSample]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  simp only [fallingFour, Nat.cast_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n)]
  unfold stepAlpha
  field_simp [hn0]
  ring

/-- The density of the eight dihedral patterns on distinct strips. -/
noncomputable def distinctDihedralDensity (π : Equiv.Perm (Fin n)) : ℚ :=
  (permutationK π : ℚ) / (Nat.choose n 4 : ℚ)

/-! ### A concrete finite model for the collision event

Conditional on their strip indices, four points sampled from the step
permuton have independent uniform coordinates inside their strips.  A uniform
permutation of the four sample names records the relative ranks of those
coordinates.  We use one such permutation for the first coordinates and an
independent one for the second coordinates.  Sorting by `(strip, tie-rank)` is
implemented by the numerical key `4 * strip + tie-rank`.
-/

/-- Four strip indices together with independent tie-rankings for the two
coordinates. -/
structure TiedStripSample (n : ℕ) where
  strips : StripSample n
  xRanks : Perm4
  yRanks : Perm4
deriving DecidableEq, Fintype

/-- Numerical lexicographic key for a strip and its within-strip tie rank. -/
def tiedStripKey (f : StripSample n) (ranks : Perm4) (i : Four) : ℕ :=
  4 * (f i).val + (ranks i).val

theorem tiedStripKey_injective (f : StripSample n) (ranks : Perm4) :
    Function.Injective (tiedStripKey f ranks) := by
  intro i j hij
  apply ranks.injective
  apply Fin.ext
  have hi := (ranks i).isLt
  have hj := (ranks j).isLt
  simp only [tiedStripKey] at hij
  omega

/-- The permutation from increasing lexicographic key rank to sample name. -/
def tiedStripOrder (f : StripSample n) (ranks : Perm4) : Perm4 :=
  Tuple.sort (tiedStripKey f ranks)

/-- The four sample names, in the order selected by strip number and tie
rank. -/
def tiedStripOrderList (f : StripSample n) (ranks : Perm4) : List Four :=
  List.ofFn (tiedStripOrder f ranks)

theorem tiedStripOrderList_nodup (f : StripSample n) (ranks : Perm4) :
    (tiedStripOrderList f ranks).Nodup := by
  exact List.nodup_ofFn.mpr (tiedStripOrder f ranks).injective

theorem mem_tiedStripOrderList (f : StripSample n) (ranks : Perm4) (i : Four) :
    i ∈ tiedStripOrderList f ranks := by
  rw [tiedStripOrderList, List.mem_ofFn']
  exact (tiedStripOrder f ranks).surjective i

@[simp] theorem length_tiedStripOrderList (f : StripSample n) (ranks : Perm4) :
    (tiedStripOrderList f ranks).length = 4 := by
  simp [tiedStripOrderList]

/-- The lexicographically sorted pattern used on the collision event. -/
def tiedCollisionPattern (π : Equiv.Perm (Fin n)) (z : TiedStripSample n) : Perm4 :=
  relativePermutation
    (tiedStripOrder z.strips z.xRanks)
    (tiedStripOrder (fun i => π (z.strips i)) z.yRanks)

/-- The four-point pattern produced by a step permutation.  On injective strip
samples it is the ordinary standardized restriction of `π`, so tie ranks are
definitionally irrelevant.  On the collision event it uses the explicit
lexicographic tie-ranking model above. -/
noncomputable def tiedStepPattern (π : Equiv.Perm (Fin n))
    (z : TiedStripSample n) : Perm4 :=
  if h : Function.Injective z.strips then
    relativePattern π (Finset.univ.map ⟨z.strips, h⟩)
      (by simp)
  else
    tiedCollisionPattern π z

theorem tiedStepPattern_of_injective (π : Equiv.Perm (Fin n))
    (z : TiedStripSample n) (h : Function.Injective z.strips) :
    tiedStepPattern π z =
      relativePattern π (Finset.univ.map ⟨z.strips, h⟩) (by simp) := by
  simp only [tiedStepPattern, dif_pos h]

/-- On distinct strips the concrete tied-sample model is exactly the
`DihedralOn` event counted by `permutationK`. -/
theorem isDihedral4_tiedStepPattern_iff_of_injective
    (π : Equiv.Perm (Fin n)) (z : TiedStripSample n)
    (h : Function.Injective z.strips) :
    IsDihedral4 (tiedStepPattern π z) ↔
      DihedralOn π (Finset.univ.map ⟨z.strips, h⟩) := by
  rw [tiedStepPattern_of_injective π z h]
  constructor
  · intro hd
    exact ⟨by simp, hd⟩
  · rintro ⟨_, hd⟩
    exact hd

/-- The finite set of samples in which at least two first-coordinate strip
indices collide. -/
noncomputable def collisionSamples (n : ℕ) : Finset (TiedStripSample n) :=
  Finset.univ.filter fun z => ¬ Function.Injective z.strips

/-- Number of collision samples whose induced pattern is dihedral. -/
noncomputable def collisionDihedralCount (π : Equiv.Perm (Fin n)) : ℕ :=
  ((collisionSamples n).filter fun z => IsDihedral4 (tiedStepPattern π z)).card

/-- Conditional dihedral-pattern density on the collision event. -/
noncomputable def collisionDihedralDensity (π : Equiv.Perm (Fin n)) : ℚ :=
  (collisionDihedralCount π : ℚ) / (collisionSamples n).card

theorem collisionDihedralCount_le (π : Equiv.Perm (Fin n)) :
    collisionDihedralCount π ≤ (collisionSamples n).card := by
  exact Finset.card_filter_le _ _

theorem collisionSamples_card_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (collisionSamples n).card := by
  let f : StripSample n := fun _ => ⟨0, by omega⟩
  let z : TiedStripSample n :=
    ⟨f, Equiv.refl Four, Equiv.refl Four⟩
  apply Finset.card_pos.mpr
  refine ⟨z, ?_⟩
  simp only [collisionSamples, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hf
  have h01 : (0 : Four) = 1 := hf (show f 0 = f 1 by rfl)
  norm_num at h01

theorem collisionDihedralDensity_nonneg (π : Equiv.Perm (Fin n)) :
    0 ≤ collisionDihedralDensity π := by
  exact div_nonneg (by positivity) (by positivity)

theorem collisionDihedralDensity_le_one {n : ℕ} (π : Equiv.Perm (Fin n))
    (hn : 1 ≤ n) : collisionDihedralDensity π ≤ 1 := by
  have hden : (0 : ℚ) < ((collisionSamples n).card : ℚ) := by
    exact_mod_cast collisionSamples_card_pos hn
  apply (div_le_one₀ hden).2
  exact_mod_cast collisionDihedralCount_le π

/-! ### One global finite sample space -/

/-- A four-subset, represented as an element of the standard powerset
finset. -/
abbrev FourSubset (n : ℕ) :=
  ↑((Finset.univ : Finset (Fin n)).powersetCard 4)

/-- The three independent permutations attached to a distinct-strip sample:
one enumerates the four strip indices and two are the (irrelevant) tie
rankings. -/
abbrev DistinctRankData := Perm4 × (Perm4 × Perm4)

/-- A distinct-strip sample, parametrized by its unordered four-set, its
enumeration, and the two tie-rankings. -/
abbrev DistinctTiedSample (n : ℕ) := FourSubset n × DistinctRankData

/-- A collision sample with its noninjectivity certificate. -/
abbrev CollisionTiedSample (n : ℕ) :=
  {z : TiedStripSample n // ¬ Function.Injective z.strips}

/-- A single finite sample space combining the distinct and collision
branches with exactly their original multiplicities. -/
abbrev GlobalTiedSample (n : ℕ) :=
  DistinctTiedSample n ⊕ CollisionTiedSample n

/-- Dihedral outcome on the global sample space. -/
noncomputable def GlobalTiedDihedral (π : Equiv.Perm (Fin n)) : GlobalTiedSample n → Prop
  | Sum.inl z => DihedralOn π z.1.1
  | Sum.inr z => IsDihedral4 (tiedStepPattern π z.1)

noncomputable instance globalTiedDihedralDecidable
    (π : Equiv.Perm (Fin n)) (z : GlobalTiedSample n) :
    Decidable (GlobalTiedDihedral π z) :=
  Classical.dec _

/-- Number of dihedral outcomes in the one global tied-sample space. -/
noncomputable def globalTiedDihedralCount (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (GlobalTiedDihedral π)).card

/-- The literal filter-card density on the one global finite sample space. -/
noncomputable def globalTiedDihedralDensity (π : Equiv.Perm (Fin n)) : ℚ :=
  (globalTiedDihedralCount π : ℚ) / Fintype.card (GlobalTiedSample n)

theorem card_perm4 : Fintype.card Perm4 = 24 := by decide

noncomputable def dihedralFourSubsetEquiv (π : Equiv.Perm (Fin n)) :
    {q : FourSubset n // DihedralOn π q.1} ≃
      ↑(((Finset.univ : Finset (Fin n)).powersetCard 4).filter (DihedralOn π)) where
  toFun q := ⟨q.1.1, Finset.mem_filter.mpr ⟨q.1.2, q.2⟩⟩
  invFun q :=
    ⟨⟨q.1, (Finset.mem_filter.mp q.2).1⟩, (Finset.mem_filter.mp q.2).2⟩
  left_inv q := by rfl
  right_inv q := by rfl

noncomputable def dihedralCollisionSampleEquiv (π : Equiv.Perm (Fin n)) :
    {z : CollisionTiedSample n // IsDihedral4 (tiedStepPattern π z.1)} ≃
      ↑((collisionSamples n).filter fun z => IsDihedral4 (tiedStepPattern π z)) where
  toFun z := ⟨z.1.1, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.1.2⟩, z.2⟩⟩
  invFun z :=
    ⟨⟨z.1, (Finset.mem_filter.mp (Finset.mem_filter.mp z.2).1).2⟩,
      (Finset.mem_filter.mp z.2).2⟩
  left_inv z := by rfl
  right_inv z := by rfl

noncomputable def dihedralGlobalCollisionSampleEquiv
    (π : Equiv.Perm (Fin n)) :
    {z : CollisionTiedSample n // GlobalTiedDihedral π (Sum.inr z)} ≃
      ↑((collisionSamples n).filter fun z => IsDihedral4 (tiedStepPattern π z)) where
  toFun z := ⟨z.1.1, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.1.2⟩,
      (show IsDihedral4 (tiedStepPattern π z.1.1) from z.2)⟩⟩
  invFun z :=
    ⟨⟨z.1, (Finset.mem_filter.mp (Finset.mem_filter.mp z.2).1).2⟩,
      (show GlobalTiedDihedral π
          (Sum.inr ⟨z.1, (Finset.mem_filter.mp (Finset.mem_filter.mp z.2).1).2⟩)
        from (Finset.mem_filter.mp z.2).2)⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact success-count decomposition of the global sample into its distinct
and collision branches. -/
theorem globalTiedDihedralCount_eq (π : Equiv.Perm (Fin n)) :
    globalTiedDihedralCount π =
      permutationK π * 24 ^ 3 + collisionDihedralCount π := by
  classical
  rw [globalTiedDihedralCount, ← Fintype.card_subtype]
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  have hleft :
      Fintype.card
          {z : DistinctTiedSample n // GlobalTiedDihedral π (Sum.inl z)} =
        permutationK π * 24 ^ 3 := by
    simp only [GlobalTiedDihedral]
    change Fintype.card
      {z : FourSubset n × DistinctRankData // DihedralOn π z.1.1} = _
    rw [Fintype.card_congr
      (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun q : FourSubset n => DihedralOn π q.1))]
    rw [Fintype.card_prod]
    have hq : Fintype.card {q : FourSubset n // DihedralOn π q.1} =
        permutationK π := by
      rw [Fintype.card_congr (dihedralFourSubsetEquiv π), Fintype.card_coe]
      rfl
    rw [hq]
    simp [DistinctRankData, card_perm4]
  have hright :
      Fintype.card
          {z : CollisionTiedSample n // GlobalTiedDihedral π (Sum.inr z)} =
        collisionDihedralCount π := by
    rw [Fintype.card_congr (dihedralGlobalCollisionSampleEquiv π)]
    exact Fintype.card_coe _
  rw [hleft, hright]

def tiedStripSampleEquiv (n : ℕ) :
    TiedStripSample n ≃ StripSample n × (Perm4 × Perm4) where
  toFun z := ⟨z.strips, z.xRanks, z.yRanks⟩
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

def injectiveTiedStripSampleEquiv (n : ℕ) :
    {z : TiedStripSample n // Function.Injective z.strips} ≃
      {f : StripSample n // Function.Injective f} × (Perm4 × Perm4) where
  toFun z := ⟨⟨z.1.strips, z.2⟩, z.1.xRanks, z.1.yRanks⟩
  invFun z := ⟨⟨z.1.1, z.2.1, z.2.2⟩, z.1.2⟩
  left_inv z := by cases z with | mk z hz => cases z; rfl
  right_inv z := by cases z with | mk z ranks => cases ranks; cases z; rfl

noncomputable def collisionTiedSampleEquiv (n : ℕ) :
    CollisionTiedSample n ≃ ↑(collisionSamples n) where
  toFun z := ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩
  invFun z := ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
  left_inv z := by rfl
  right_inv z := by rfl

theorem card_tiedStripSample (n : ℕ) :
    Fintype.card (TiedStripSample n) = n ^ 4 * 24 ^ 2 := by
  rw [Fintype.card_congr (tiedStripSampleEquiv n), Fintype.card_prod]
  simp [StripSample, card_perm4]

theorem card_injectiveTiedStripSample (n : ℕ) :
    Fintype.card {z : TiedStripSample n // Function.Injective z.strips} =
      fallingFour n * 24 ^ 2 := by
  rw [Fintype.card_congr (injectiveTiedStripSampleEquiv n), Fintype.card_prod,
    card_injectiveStripSample]
  simp [card_perm4]

theorem injective_add_collision_card (n : ℕ) :
    fallingFour n * 24 ^ 2 + (collisionSamples n).card = n ^ 4 * 24 ^ 2 := by
  classical
  have hcompl := Fintype.card_subtype_compl
    (fun z : TiedStripSample n => Function.Injective z.strips)
  have hle :
      Fintype.card {z : TiedStripSample n // Function.Injective z.strips} ≤
        Fintype.card (TiedStripSample n) := Fintype.card_subtype_le _
  have hcollision : Fintype.card (CollisionTiedSample n) =
      (collisionSamples n).card := by
    rw [Fintype.card_congr (collisionTiedSampleEquiv n), Fintype.card_coe]
  rw [card_injectiveTiedStripSample, card_tiedStripSample] at hcompl hle
  have hadd := Nat.sub_add_cancel hle
  rw [← hcompl] at hadd
  rw [hcollision] at hadd
  simpa only [Nat.add_comm] using hadd

theorem twentyFour_mul_choose_eq_fallingFour (n : ℕ) :
    24 * Nat.choose n 4 = fallingFour n := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 4
  norm_num at h
  simpa [fallingFour, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

theorem distinct_add_collision_card (n : ℕ) :
    Nat.choose n 4 * 24 ^ 3 + (collisionSamples n).card = n ^ 4 * 24 ^ 2 := by
  have h := injective_add_collision_card n
  rw [← twentyFour_mul_choose_eq_fallingFour n] at h
  nlinarith

theorem card_globalTiedSample (n : ℕ) :
    Fintype.card (GlobalTiedSample n) =
      Nat.choose n 4 * 24 ^ 3 + (collisionSamples n).card := by
  rw [Fintype.card_sum, Fintype.card_prod]
  have hfour : Fintype.card (FourSubset n) = Nat.choose n 4 := by
    rw [Fintype.card_coe]
    simp [Finset.card_powersetCard]
  have hcollision : Fintype.card (CollisionTiedSample n) =
      (collisionSamples n).card := by
    rw [Fintype.card_congr (collisionTiedSampleEquiv n), Fintype.card_coe]
  rw [hfour, hcollision]
  simp [DistinctRankData, card_perm4]

theorem card_globalTiedSample_eq_total (n : ℕ) :
    Fintype.card (GlobalTiedSample n) = n ^ 4 * 24 ^ 2 := by
  rw [card_globalTiedSample, distinct_add_collision_card]

/-- Total dihedral density of the step-permuton sampling model: the
distinct-strip and collision events are combined with their exact weights. -/
noncomputable def stepDihedralDensity (π : Equiv.Perm (Fin n)) : ℚ :=
  stepAlpha n * distinctDihedralDensity π +
    (1 - stepAlpha n) * collisionDihedralDensity π

theorem stepAlpha_pos {n : ℕ} (hn : 4 ≤ n) : 0 < stepAlpha n := by
  have h4 : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (0 : ℚ) < (n : ℚ) := by linarith
  have h1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have h2 : (0 : ℚ) < (n : ℚ) - 2 := by linarith
  have h3 : (0 : ℚ) < (n : ℚ) - 3 := by linarith
  unfold stepAlpha
  exact div_pos (mul_pos (mul_pos h1 h2) h3) (pow_pos hn0 _)

theorem stepAlpha_le_one {n : ℕ} (hn : 4 ≤ n) : stepAlpha n ≤ 1 := by
  have h4 : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hlin : (0 : ℚ) ≤ 6 * (n : ℚ) - 11 := by linarith
  have hprod : (0 : ℚ) ≤ (n : ℚ) * (6 * (n : ℚ) - 11) :=
    mul_nonneg hn0 hlin
  unfold stepAlpha
  apply (div_le_one₀ (by positivity : (0 : ℚ) < (n : ℚ) ^ 3)).2
  nlinarith

theorem one_sub_stepAlpha {n : ℕ} (hn : 4 ≤ n) :
    1 - stepAlpha n =
      (6 * (n : ℚ) ^ 2 - 11 * (n : ℚ) + 6) / (n : ℚ) ^ 3 := by
  have hn0 : (n : ℚ) ≠ 0 := by
    have h4 : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  unfold stepAlpha
  field_simp [hn0]
  ring

theorem choose_four_pos {n : ℕ} (hn : 4 ≤ n) :
    (0 : ℚ) < (Nat.choose n 4 : ℚ) := by
  exact_mod_cast Nat.choose_pos hn

/-- The filter-card density on the single global sample space is exactly the
distinct/collision mixture used in the finite reduction. -/
theorem globalTiedDihedralDensity_eq_stepDihedralDensity {n : ℕ}
    (π : Equiv.Perm (Fin n)) (hn : 4 ≤ n) :
    globalTiedDihedralDensity π = stepDihedralDensity π := by
  let N : ℕ := Nat.choose n 4
  let Kπ : ℕ := permutationK π
  let C : ℕ := (collisionSamples n).card
  let R : ℕ := collisionDihedralCount π
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hN0 : (N : ℚ) ≠ 0 := by
    have h := choose_four_pos hn
    exact ne_of_gt (by simpa only [N] using h)
  have hCpos : 0 < C := by
    simpa only [C] using collisionSamples_card_pos (n := n) (by omega)
  have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hTpos : 0 < N * 24 ^ 3 + C := by omega
  have hT0 : ((N * 24 ^ 3 + C : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hTpos.ne'
  have hfallQ : (fallingFour n : ℚ) = 24 * (N : ℚ) := by
    exact_mod_cast (twentyFour_mul_choose_eq_fallingFour n).symm
  have htotalQ :
      (N : ℚ) * 24 ^ 3 + (C : ℚ) = (n : ℚ) ^ 4 * 24 ^ 2 := by
    exact_mod_cast distinct_add_collision_card n
  have halpha0 :
      stepAlpha n = (fallingFour n : ℚ) / (n : ℚ) ^ 4 := by
    rw [stepAlpha, fallingFour]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_sub (by omega : 3 ≤ n)]
    field_simp [hn0]
    ring
  have halpha :
      stepAlpha n =
        ((N : ℚ) * 24 ^ 3) / ((N : ℚ) * 24 ^ 3 + (C : ℚ)) := by
    rw [halpha0, hfallQ, htotalQ]
    field_simp [hn0]
  rw [globalTiedDihedralDensity, globalTiedDihedralCount_eq,
    card_globalTiedSample, stepDihedralDensity, distinctDihedralDensity,
    collisionDihedralDensity]
  push_cast
  change
    ((Kπ : ℚ) * 24 ^ 3 + (R : ℚ)) /
        ((N : ℚ) * 24 ^ 3 + (C : ℚ)) =
      stepAlpha n * ((Kπ : ℚ) / (N : ℚ)) +
        (1 - stepAlpha n) * ((R : ℚ) / (C : ℚ))
  rw [halpha]
  field_simp [hN0, hC0, hT0]
  ring

/-- The exact specialization of the published permuton inequality needed for
the step permuton of `π`.  The density is the literal filter-card density on
the explicit global finite sampling model; only its `1/3` lower bound is
external. -/
def StepPermutonInequality (π : Equiv.Perm (Fin n)) : Prop :=
  (1 : ℚ) / 3 ≤ globalTiedDihedralDensity π

/-- The published input, simultaneously for all `n`-point step permutons. -/
def StepPermutonTheorem (n : ℕ) : Prop :=
  ∀ π : Equiv.Perm (Fin n), StepPermutonInequality π

/-- Elementary collision reduction.  No measure theory or independence
between different four-subsets is used here. -/
theorem collisionReduction {α p r : ℚ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hr : r ≤ 1) (hpermuton : (1 : ℚ) / 3 ≤ α * p + (1 - α) * r) :
    1 - 2 / (3 * α) ≤ p := by
  have hcollision : (1 - α) * r ≤ 1 - α := by
    exact mul_le_of_le_one_right (sub_nonneg.mpr hα1) hr
  have hcore : α - (2 : ℚ) / 3 ≤ α * p := by
    linarith
  have hid : α * (1 - 2 / (3 * α)) = α - (2 : ℚ) / 3 := by
    field_simp [ne_of_gt hα]
  apply (mul_le_mul_iff_of_pos_left hα).mp
  rw [hid]
  exact hcore

/-- The finite distinct-strip density bound obtained from the step-permuton
inequality by charging every collision as potentially dihedral. -/
theorem distinctDihedralDensity_bound {n : ℕ} (π : Equiv.Perm (Fin n))
    (hn : 4 ≤ n) (hstep : StepPermutonInequality π) :
    1 - 2 / (3 * stepAlpha n) ≤ distinctDihedralDensity π := by
  exact collisionReduction (stepAlpha_pos hn) (stepAlpha_le_one hn)
    (collisionDihedralDensity_le_one π (by omega))
    (by
      have hglobal : (1 : ℚ) / 3 ≤ globalTiedDihedralDensity π := hstep
      rw [globalTiedDihedralDensity_eq_stepDihedralDensity π hn] at hglobal
      simpa only [stepDihedralDensity] using hglobal)

/-- Finite collision bound for a relative permutation. -/
theorem permutationCollisionBound {n : ℕ} (π : Equiv.Perm (Fin n))
    (hn : 4 ≤ n) (hstep : StepPermutonInequality π) :
    (1 - 2 / (3 * stepAlpha n)) * (Nat.choose n 4 : ℚ) ≤
      (permutationK π : ℚ) := by
  have hN := choose_four_pos hn
  exact (le_div_iff₀ hN).mp (distinctDihedralDensity_bound π hn hstep)

/-- The paper's circular-order bound
`K(C,C') ≥ (1 - 2/(3 αₙ)) * choose n 4`. -/
theorem circularCollisionBound {n : ℕ} (C C' : CircularOrder n)
    (hn : 4 ≤ n) (hstep : StepPermutonInequality (relativePermutation C C')) :
    (1 - 2 / (3 * stepAlpha n)) * (Nat.choose n 4 : ℚ) ≤ (K C C' : ℚ) := by
  exact permutationCollisionBound (relativePermutation C C') hn hstep

/-- Uniform version when the published inequality is supplied for every step
permuton of size `n`. -/
theorem circularOrderBound {n : ℕ} (hpublished : StepPermutonTheorem n)
    (C C' : CircularOrder n) (hn : 4 ≤ n) :
    (1 - 2 / (3 * stepAlpha n)) * (Nat.choose n 4 : ℚ) ≤ (K C C' : ℚ) := by
  exact circularCollisionBound C C' hn (hpublished (relativePermutation C C'))

end QuartetDistance.Circular
