import QuartetDistance.GraphQuartet
import QuartetDistance.RibbonRestriction

/-!
# Actual graph edges are circular intervals in every boundary word

This file joins the graph-theoretic edge positions of `GraphQuartet` to the
ribbon interval lemmas of `RibbonRestriction`.  The final statement is about
an arbitrary actual edge of `TreeAdequacy.PhyloTree.graph`: each of its two
delete-edge components contributes a circular interval of labels in every
boundary word.
-/

namespace QuartetDistance
namespace GraphRibbon

open SimpleGraph Tree
open GraphQuartet

/-! ## Edge positions as subtrees of the restored full tree -/

theorem isSubtree_map_of_properSubtree {α β : Type}
    {t : Tree.FullTree α} (p : GraphQuartet.FullTree.ProperSubtree t)
    (f : α → β) :
    RibbonRestriction.IsSubtree (p.tree.map f) (t.map f) := by
  induction p with
  | left l r =>
      exact .left (r.map f) (.here (l.map f))
  | right l r =>
      exact .right (l.map f) (.here (r.map f))
  | @inLeft l r p ih =>
      exact .left (r.map f) ih
  | @inRight l r p ih =>
      exact .right (l.map f) ih

namespace EdgePosition

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The ordinary full tree on the labels below an oriented graph edge. -/
def asFullSubtree {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) : Tree.FullTree α :=
  p.tree.map Subtype.val

/-- Every oriented graph edge supplies an actual subtree occurrence in the
restored full tree. -/
theorem asFullSubtree_isSubtree {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    RibbonRestriction.IsSubtree (asFullSubtree p) T.asFullTree := by
  cases p with
  | crown =>
      exact .right (.leaf T.root) (.here (T.crown.map Subtype.val))
  | inside q =>
      exact .right (.leaf T.root)
        (isSubtree_map_of_properSubtree q Subtype.val)

/-- The leaf set of the restored subtree is exactly the graph edge cluster. -/
@[simp] theorem asFullSubtree_leaves_toFinset {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    (asFullSubtree p).leaves.toFinset = p.cluster := by
  ext a
  simp [asFullSubtree, GraphQuartet.PhyloTree.EdgePosition.cluster]

/-- The descendant side of every oriented edge is a circular interval in
every boundary word. -/
theorem cluster_circularInterval {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval p.cluster word := by
  have hlinear := RibbonRestriction.boundary_linearInterval_edgeSide
    T (asFullSubtree_isSubtree p) hword
  rw [asFullSubtree_leaves_toFinset p] at hlinear
  exact hlinear.circular

/-- The complementary side of every oriented edge is also a circular
interval, possibly crossing the cut in the displayed boundary word. -/
theorem complement_circularInterval {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval (Finset.univ \ p.cluster) word := by
  have h := RibbonRestriction.boundary_circularInterval_oppositeEdgeSide
    T (asFullSubtree_isSubtree p) hword
  rwa [asFullSubtree_leaves_toFinset p] at h

end EdgePosition

/-! ## Literal delete-edge components -/

namespace PhyloTree

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Labels in the component of `x` after deleting the actual edge `xy`. -/
noncomputable def edgeSide (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.PhyloTree.Vertex T) : Finset α :=
  by
    classical
    exact Finset.univ.filter fun a =>
      ∃ z : TreeAdequacy.PhyloTree.Vertex T,
        TreeAdequacy.PhyloTree.label? T z = some a ∧
          ((TreeAdequacy.PhyloTree.graph T).deleteEdges {s(x, y)}).Reachable x z

theorem mem_edgeSide_iff (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.PhyloTree.Vertex T) (a : α) :
    a ∈ edgeSide T x y ↔
      ∃ z : TreeAdequacy.PhyloTree.Vertex T,
        TreeAdequacy.PhyloTree.label? T z = some a ∧
          ((TreeAdequacy.PhyloTree.graph T).deleteEdges
            {s(x, y)}).Reachable x z := by
  classical
  simp [edgeSide]

/-- The child component of a positioned edge has exactly its finite leaf
cluster as labels. -/
theorem edgeSide_child_parent_eq_cluster {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    edgeSide T p.child p.parent = p.cluster := by
  ext a
  rw [mem_edgeSide_iff]
  have hedge : ({s(p.child, p.parent)} :
      Set (Sym2 (TreeAdequacy.PhyloTree.Vertex T))) =
      {s(p.parent, p.child)} := by
    rw [Sym2.eq_swap]
  rw [hedge]
  exact p.exists_label_reachable_iff a

/-- The parent component carries precisely the complementary cluster. -/
theorem edgeSide_parent_child_eq_complement {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    edgeSide T p.parent p.child = Finset.univ \ p.cluster := by
  ext a
  rw [mem_edgeSide_iff]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact p.exists_label_parent_reachable_iff a

/-- For every actual graph edge, the two label sets defined by delete-edge
reachability are complementary. -/
theorem edgeSide_reverse_eq_complement (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y) :
    edgeSide T y x = Finset.univ \ edgeSide T x y := by
  obtain ⟨p, hp | hp⟩ :=
    GraphQuartet.PhyloTree.exists_edgePosition_of_adj T hxy
  · rw [hp.1, hp.2, edgeSide_child_parent_eq_cluster,
      edgeSide_parent_child_eq_complement]
    ext a
    simp
  · rw [hp.1, hp.2, edgeSide_parent_child_eq_complement,
      edgeSide_child_parent_eq_cluster]

/-- **Literal edge-interval lemma.**  For every actual edge `xy` of the
phylogenetic realization and every boundary word, the labels in the
delete-edge component of `x` and the labels in the delete-edge component of
`y` are both circular intervals. -/
theorem edgeSides_circularIntervals (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y)
    {word : List α} (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval (edgeSide T x y) word ∧
      RibbonRestriction.CircularInterval (edgeSide T y x) word := by
  obtain ⟨p, hp | hp⟩ :=
    GraphQuartet.PhyloTree.exists_edgePosition_of_adj T hxy
  · rw [hp.1, hp.2, edgeSide_parent_child_eq_complement,
      edgeSide_child_parent_eq_cluster]
    exact ⟨EdgePosition.complement_circularInterval p hword,
      EdgePosition.cluster_circularInterval p hword⟩
  · rw [hp.1, hp.2, edgeSide_child_parent_eq_cluster,
      edgeSide_parent_child_eq_complement]
    exact ⟨EdgePosition.cluster_circularInterval p hword,
      EdgePosition.complement_circularInterval p hword⟩

end PhyloTree

end GraphRibbon
end QuartetDistance
