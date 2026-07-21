import QuartetDistance.RibbonRestriction

/-!
# Restriction to an arbitrary nonempty leaf set

The quartet development only needs restriction to four leaves.  This file
packages the same pruning and suppression construction for every nonempty
finite set of leaves.  In particular, it gives the literal pointwise content
of the paper's boundary-order restriction lemma for every set of at least two
leaves.

The induced tree is represented as a `Tree.FullTree`: branches containing no
selected leaf are deleted and unary forks are suppressed by
`Tree.FullTree.prune`.  A boundary word of the original unrooted tree filters
to a frontier word of this induced tree.  Conversely, every induced frontier
has a lift to a global boundary word up to cyclic rotation, which is the
appropriate equality notion for circular boundary orders.
-/

namespace QuartetDistance.GeneralRestriction

open Tree

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pruning the restored full tree to a nonempty set of leaves cannot produce
the empty optional tree. -/
theorem prune_asFullTree_isSome_of_nonempty (T : PhyloTree α)
    (Y : Finset α) (hY : Y.Nonempty) :
    (T.asFullTree.prune Y).isSome = true := by
  rw [← Option.ne_none_iff_isSome]
  intro hnone
  obtain ⟨a, ha⟩ := hY
  have hempty := FullTree.restrictList_eq_nil_of_prune_eq_none
    T.asFullTree Y hnone
  have hmem : a ∈ FullTree.restrictList Y T.asFullTree.leaves := by
    simp [FullTree.restrictList, ha, T.mem_referenceLeaves a]
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

/-- The subtree induced by a nonempty leaf set, with empty branches removed
and every resulting unary fork suppressed. -/
def inducedTree (T : PhyloTree α) (Y : Finset α) (hY : Y.Nonempty) :
    FullTree α :=
  (T.asFullTree.prune Y).get (prune_asFullTree_isSome_of_nonempty T Y hY)

theorem prune_asFullTree_eq_inducedTree (T : PhyloTree α)
    (Y : Finset α) (hY : Y.Nonempty) :
    T.asFullTree.prune Y = some (inducedTree T Y hY) := by
  generalize h : T.asFullTree.prune Y = o
  cases o with
  | none =>
      have hi := prune_asFullTree_isSome_of_nonempty T Y hY
      rw [h] at hi
      simp at hi
  | some u => simp [inducedTree, h]

/-- The leaf word of the induced tree is exactly the original reference leaf
word filtered to the selected set. -/
theorem inducedTree_leaves (T : PhyloTree α) (Y : Finset α)
    (hY : Y.Nonempty) :
    (inducedTree T Y hY).leaves =
      FullTree.restrictList Y T.asFullTree.leaves :=
  FullTree.prune_leaves _ _ _ (prune_asFullTree_eq_inducedTree T Y hY)

/-- Consequently, the set of leaves of the induced tree is literally `Y`. -/
theorem inducedTree_leaves_toFinset (T : PhyloTree α) (Y : Finset α)
    (hY : Y.Nonempty) :
    (inducedTree T Y hY).leaves.toFinset = Y := by
  rw [inducedTree_leaves]
  ext a
  simp [FullTree.restrictList, T.mem_referenceLeaves a]

/-- Restriction preserves the absence of repeated leaf labels. -/
theorem inducedTree_leaves_nodup (T : PhyloTree α) (Y : Finset α)
    (hY : Y.Nonempty) :
    (inducedTree T Y hY).leaves.Nodup := by
  rw [inducedTree_leaves]
  exact T.asFullTree_nodup.filter _

/-- The induced tree has exactly as many leaf occurrences as `Y` has
elements. -/
theorem inducedTree_leaves_length (T : PhyloTree α) (Y : Finset α)
    (hY : Y.Nonempty) :
    (inducedTree T Y hY).leaves.length = Y.card := by
  calc
    (inducedTree T Y hY).leaves.length =
        (inducedTree T Y hY).leaves.toFinset.card :=
      (List.toFinset_card_of_nodup (inducedTree_leaves_nodup T Y hY)).symm
    _ = Y.card := congrArg Finset.card (inducedTree_leaves_toFinset T Y hY)

/-- Pointwise restriction of the boundary order: for every deterministic
rotation outcome of `T`, deleting the labels outside `Y` gives a frontier of
the induced pruned-and-suppressed tree.  This applies, in particular, whenever
`2 ≤ Y.card`, as in the paper. -/
theorem restrict_boundary_mem_inducedTree_frontier (T : PhyloTree α)
    (Y : Finset α) (hY : Y.Nonempty) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    FullTree.restrictList Y word ∈ (inducedTree T Y hY).frontierProfile := by
  have hfull :=
    RibbonRestriction.mem_asFullTree_frontierProfile_of_mem_boundaryProfile
      T hword
  have hpruned :=
    RibbonRestriction.restrictList_mem_optionProfile_of_mem_frontier
      T.asFullTree Y hfull
  rw [prune_asFullTree_eq_inducedTree T Y hY] at hpruned
  exact hpruned

/-- Conversely, every frontier of the induced tree is obtained from some
global boundary word after restriction, up to cyclic rotation.  The possible
rotation is precisely the harmless choice of putting the distinguished root
leaf at the beginning rather than at the end of the restored full-tree
frontier. -/
theorem exists_boundary_lift_isRotated (T : PhyloTree α)
    (Y : Finset α) (hY : Y.Nonempty) {restricted : List α}
    (hrestricted : restricted ∈ (inducedTree T Y hY).frontierProfile) :
    ∃ word, word ∈ T.boundaryProfile ∧
      FullTree.restrictList Y word ~r restricted := by
  have hoptional : restricted ∈
      FullTree.optionProfile (T.asFullTree.prune Y) := by
    rw [prune_asFullTree_eq_inducedTree T Y hY]
    exact hrestricted
  obtain ⟨fullWord, hfullWord, hfilter⟩ :=
    RibbonRestriction.exists_frontier_lift_of_mem_optionProfile
      T.asFullTree Y hoptional
  rw [T.asFullTree_frontierProfile] at hfullWord
  simp only [Multiset.mem_bind] at hfullWord
  obtain ⟨crownWord, hcrownWord, hfullWord⟩ := hfullWord
  have hfullWord' :
      fullWord = T.root :: crownWord.map Subtype.val ∨
        fullWord = crownWord.map Subtype.val ++ [T.root] := by
    simpa using hfullWord
  let word := T.root :: crownWord.map Subtype.val
  have hword : word ∈ T.boundaryProfile := by
    simp only [PhyloTree.boundaryProfile, Multiset.mem_map]
    exact ⟨crownWord, hcrownWord, rfl⟩
  refine ⟨word, hword, ?_⟩
  rcases hfullWord' with hfront | hback
  · rw [hfront] at hfilter
    rw [← hfilter]
  · rw [hback] at hfilter
    by_cases hroot : T.root ∈ Y
    · have hrotate :
          FullTree.restrictList Y word ~r
            FullTree.restrictList Y
              (crownWord.map Subtype.val ++ [T.root]) := by
        simpa [word, FullTree.restrictList, hroot] using
          (List.isRotated_concat T.root
            (FullTree.restrictList Y (crownWord.map Subtype.val))).symm
      rw [hfilter] at hrotate
      exact hrotate
    · have heq :
          FullTree.restrictList Y word =
            FullTree.restrictList Y
              (crownWord.map Subtype.val ++ [T.root]) := by
        simp [word, FullTree.restrictList, hroot]
      rw [← hfilter, heq]

end QuartetDistance.GeneralRestriction
