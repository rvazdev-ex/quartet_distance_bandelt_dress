import QuartetDistance.TreeAdequacy
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Graph-theoretic quartet splits of the syntax realization

For the finite tree graph associated with a syntactic phylogenetic tree, an
edge displays a quartet split when deleting it places the two labels on each
side in the two resulting reachable components.  This file identifies that
definition with the restriction-and-suppression topology used by the
counting development.
-/

namespace QuartetDistance
namespace GraphQuartet

open SimpleGraph

/-! ## A generic edge-separation predicate -/

/-- The component of `u` after deleting `uv` contains all labels in `A` and
no label in `B`.  The universal condition on `B` makes the definition robust
for a partial label map even before label uniqueness is known. -/
def ComponentSeparatesAt {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (label? : V → Option α) (u v : V)
    (A B : Finset α) : Prop :=
  (∀ a ∈ A, ∃ x : V, label? x = some a ∧
      (G.deleteEdges {s(u, v)}).Reachable u x) ∧
    (∀ b ∈ B, ∀ x : V, label? x = some b →
      ¬ (G.deleteEdges {s(u, v)}).Reachable u x)

/-- An edge of `G` separates the labels in `A` from the labels in `B`.
Either of the two components may be named first, so this predicate is
intrinsically symmetric in `A` and `B`. -/
def EdgeSeparates {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (label? : V → Option α)
    (A B : Finset α) : Prop :=
  ∃ u v : V, G.Adj u v ∧
    (ComponentSeparatesAt G label? u v A B ∨
      ComponentSeparatesAt G label? u v B A)

theorem edgeSeparates_comm {α V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (label? : V → Option α) (A B : Finset α) :
    EdgeSeparates G label? A B ↔ EdgeSeparates G label? B A := by
  constructor
  · rintro ⟨u, v, huv, h | h⟩
    · exact ⟨u, v, huv, Or.inr h⟩
    · exact ⟨u, v, huv, Or.inl h⟩
  · rintro ⟨u, v, huv, h | h⟩
    · exact ⟨u, v, huv, Or.inr h⟩
    · exact ⟨u, v, huv, Or.inl h⟩

/-- After deleting one edge, every vertex originally reachable from an
endpoint remains reachable from at least one of the two endpoints. -/
theorem reachable_endpoint_or_endpoint_after_delete {V : Type*}
    (G : SimpleGraph V) (u v x : V) (hux : G.Reachable u x) :
    (G.deleteEdges {s(u, v)}).Reachable u x ∨
      (G.deleteEdges {s(u, v)}).Reachable v x := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hux
  induction hux with
  | refl => exact Or.inl (by rfl)
  | @tail b c hab hbc ih =>
      by_cases he : s(b, c) = s(u, v)
      · rw [Sym2.eq_iff] at he
        rcases he with ⟨hbu, hcv⟩ | ⟨hbv, hcu⟩
        · subst b
          subst c
          exact Or.inr (by rfl)
        · subst b
          subst c
          exact Or.inl (by rfl)
      · have hdel : (G.deleteEdges {s(u, v)}).Adj b c := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hbc, by simpa using he⟩
        rcases ih with hu | hv
        · exact Or.inl (hu.trans hdel.reachable)
        · exact Or.inr (hv.trans hdel.reachable)
/-! ## Positions of the rooted subtrees carried by graph edges -/

namespace FullTree

open Tree TreeAdequacy

/-- Every non-root subtree occurrence corresponds to its parent edge. -/
inductive ProperSubtree : (t : Tree.FullTree α) → Type
  | left (l r : Tree.FullTree α) : ProperSubtree (.fork l r)
  | right (l r : Tree.FullTree α) : ProperSubtree (.fork l r)
  | inLeft {l r : Tree.FullTree α} : ProperSubtree l → ProperSubtree (.fork l r)
  | inRight {l r : Tree.FullTree α} : ProperSubtree r → ProperSubtree (.fork l r)

/-- The syntax tree rooted at a proper-subtree position. -/
def ProperSubtree.tree : {t : Tree.FullTree α} → ProperSubtree t → Tree.FullTree α
  | .fork l _, .left _ _ => l
  | .fork _ r, .right _ _ => r
  | .fork _ _, .inLeft p => p.tree
  | .fork _ _, .inRight p => p.tree

@[simp] theorem ProperSubtree.tree_left (l r : Tree.FullTree α) :
    (ProperSubtree.left l r).tree = l := rfl

@[simp] theorem ProperSubtree.tree_right (l r : Tree.FullTree α) :
    (ProperSubtree.right l r).tree = r := rfl

@[simp] theorem ProperSubtree.tree_inLeft {l r : Tree.FullTree α}
    (p : ProperSubtree l) : (p.inLeft (r := r)).tree = p.tree := rfl

@[simp] theorem ProperSubtree.tree_inRight {l r : Tree.FullTree α}
    (p : ProperSubtree r) : (p.inRight (l := l)).tree = p.tree := rfl

/-- Embed all vertices of a subtree occurrence into the ambient realization. -/
def ProperSubtree.embed : {t : Tree.FullTree α} → (p : ProperSubtree t) →
    TreeAdequacy.FullTree.Vertex p.tree → TreeAdequacy.FullTree.Vertex t
  | .fork _ _, .left _ _, x => .inl (.inr x)
  | .fork _ _, .right _ _, x => .inr x
  | .fork _ _, .inLeft p, x => .inl (.inr (p.embed x))
  | .fork _ _, .inRight p, x => .inr (p.embed x)

/-- Endpoint of the parent edge inside the subtree occurrence. -/
def ProperSubtree.child {t : Tree.FullTree α} (p : ProperSubtree t) :
    TreeAdequacy.FullTree.Vertex t :=
  p.embed (TreeAdequacy.FullTree.rootVertex p.tree)

/-- Endpoint of the parent edge outside the subtree occurrence. -/
def ProperSubtree.parent : {t : Tree.FullTree α} →
    ProperSubtree t → TreeAdequacy.FullTree.Vertex t
  | .fork _ _, .left _ _ => TreeAdequacy.FullTree.rootVertex _
  | .fork _ _, .right _ _ => TreeAdequacy.FullTree.rootVertex _
  | .fork _ _, .inLeft p => .inl (.inr p.parent)
  | .fork _ _, .inRight p => .inr p.parent

/-- Vertices lying below the parent edge. -/
def ProperSubtree.Below {t : Tree.FullTree α} (p : ProperSubtree t)
    (x : TreeAdequacy.FullTree.Vertex t) : Prop :=
  x ∈ Set.range p.embed

theorem ProperSubtree.embed_injective {t : Tree.FullTree α}
    (p : ProperSubtree t) : Function.Injective p.embed := by
  induction p with
  | left =>
      intro x y h
      change Sum.inl (Sum.inr x) = Sum.inl (Sum.inr y) at h
      exact Sum.inr.inj (Sum.inl.inj h)
  | right =>
      intro x y h
      change Sum.inr x = Sum.inr y at h
      exact Sum.inr.inj h
  | inLeft p ih =>
      intro x y h
      change Sum.inl (Sum.inr (p.embed x)) =
        Sum.inl (Sum.inr (p.embed y)) at h
      exact ih (Sum.inr.inj (Sum.inl.inj h))
  | inRight p ih =>
      intro x y h
      change Sum.inr (p.embed x) = Sum.inr (p.embed y) at h
      exact ih (Sum.inr.inj h)

@[simp] theorem ProperSubtree.child_below {t : Tree.FullTree α}
    (p : ProperSubtree t) : p.Below p.child := by
  exact ⟨TreeAdequacy.FullTree.rootVertex p.tree, rfl⟩

@[simp] theorem ProperSubtree.parent_not_below {t : Tree.FullTree α}
    (p : ProperSubtree t) : ¬ p.Below p.parent := by
  induction p with
  | left l r =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.parent, ProperSubtree.embed,
        TreeAdequacy.FullTree.rootVertex] at hx
  | right l r =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.parent, ProperSubtree.embed,
        TreeAdequacy.FullTree.rootVertex] at hx
  | inLeft p ih =>
      rintro ⟨x, hx⟩
      apply ih
      refine ⟨x, ?_⟩
      change Sum.inl (Sum.inr (p.embed x)) =
        Sum.inl (Sum.inr p.parent) at hx
      exact Sum.inr.inj (Sum.inl.inj hx)
  | inRight p ih =>
      rintro ⟨x, hx⟩
      apply ih
      refine ⟨x, ?_⟩
      change Sum.inr (p.embed x) = Sum.inr p.parent at hx
      exact Sum.inr.inj hx

@[simp] theorem ProperSubtree.root_not_below {t : Tree.FullTree α}
    (p : ProperSubtree t) :
    ¬ p.Below (TreeAdequacy.FullTree.rootVertex t) := by
  induction p with
  | left l r =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.embed, TreeAdequacy.FullTree.rootVertex] at hx
  | right l r =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.embed, TreeAdequacy.FullTree.rootVertex] at hx
  | inLeft p ih =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.embed, TreeAdequacy.FullTree.rootVertex] at hx
  | inRight p ih =>
      rintro ⟨x, hx⟩
      simp [ProperSubtree.embed, TreeAdequacy.FullTree.rootVertex] at hx

theorem ProperSubtree.adj_parent_child {t : Tree.FullTree α}
    (p : ProperSubtree t) :
    (TreeAdequacy.FullTree.graph t).Adj p.parent p.child := by
  induction p with
  | left l r => simp [ProperSubtree.parent, ProperSubtree.child,
      ProperSubtree.embed, TreeAdequacy.FullTree.graph,
      TreeAdequacy.FullTree.rootVertex, SimpleGraph.edge]
  | right l r => simp [ProperSubtree.parent, ProperSubtree.child,
      ProperSubtree.embed, TreeAdequacy.FullTree.graph,
      TreeAdequacy.FullTree.rootVertex, SimpleGraph.edge]
  | inLeft p ih =>
      simp only [ProperSubtree.parent, ProperSubtree.child,
        ProperSubtree.embed, TreeAdequacy.FullTree.graph,
        SimpleGraph.sup_adj, SimpleGraph.sum_adj_inl]
      exact Or.inl (Or.inl (by simpa [ProperSubtree.child] using ih))
  | inRight p ih =>
      simp only [ProperSubtree.parent, ProperSubtree.child,
        ProperSubtree.embed, TreeAdequacy.FullTree.graph,
        SimpleGraph.sup_adj, SimpleGraph.sum_adj_inr]
      exact Or.inl (by simpa [ProperSubtree.child] using ih)

@[simp] theorem graph_fork_adj_left_left (l r : Tree.FullTree α)
    (x y : TreeAdequacy.FullTree.Vertex l) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inr x)) (.inl (.inr y)) ↔
      (TreeAdequacy.FullTree.graph l).Adj x y := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_right_right (l r : Tree.FullTree α)
    (x y : TreeAdequacy.FullTree.Vertex r) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj (.inr x) (.inr y) ↔
      (TreeAdequacy.FullTree.graph r).Adj x y := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_left_root (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex l) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inr x)) (.inl (.inl ())) ↔
      x = TreeAdequacy.FullTree.rootVertex l := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_root_left (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex l) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inl ())) (.inl (.inr x)) ↔
      x = TreeAdequacy.FullTree.rootVertex l := by
  rw [SimpleGraph.adj_comm, graph_fork_adj_left_root]

@[simp] theorem graph_fork_adj_right_root (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex r) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inr x) (.inl (.inl ())) ↔
      x = TreeAdequacy.FullTree.rootVertex r := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_root_right (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex r) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inl ())) (.inr x) ↔
      x = TreeAdequacy.FullTree.rootVertex r := by
  rw [SimpleGraph.adj_comm, graph_fork_adj_right_root]

@[simp] theorem not_graph_fork_adj_left_right (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex l)
    (y : TreeAdequacy.FullTree.Vertex r) :
    ¬ (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inr x)) (.inr y) := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem not_graph_fork_adj_right_left (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex r)
    (y : TreeAdequacy.FullTree.Vertex l) :
    ¬ (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inr x) (.inl (.inr y)) := by
  rw [SimpleGraph.adj_comm]
  exact not_graph_fork_adj_left_right l r y x

/-- The parent edge is the only graph edge leaving a subtree occurrence. -/
theorem ProperSubtree.adj_boundary {t : Tree.FullTree α}
    (p : ProperSubtree t) {x y : TreeAdequacy.FullTree.Vertex t}
    (hx : p.Below x) (hy : ¬ p.Below y)
    (hxy : (TreeAdequacy.FullTree.graph t).Adj x y) :
    x = p.child ∧ y = p.parent := by
  induction p with
  | left l r =>
      rcases hx with ⟨z, rfl⟩
      rcases y with ((u | y) | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hz := (graph_fork_adj_left_root l r z).mp hxy
        constructor
        · rw [hz]
          rfl
        · rfl
      · exact False.elim (hy ⟨y, rfl⟩)
      · exact False.elim (not_graph_fork_adj_left_right l r z y hxy)
  | right l r =>
      rcases hx with ⟨z, rfl⟩
      rcases y with ((u | y) | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hz := (graph_fork_adj_right_root l r z).mp hxy
        constructor
        · rw [hz]
          rfl
        · rfl
      · exact False.elim (not_graph_fork_adj_right_left l r z y hxy)
      · exact False.elim (hy ⟨y, rfl⟩)
  | inLeft p ih =>
      rcases hx with ⟨z, rfl⟩
      rcases y with ((u | y) | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hroot : p.embed z = TreeAdequacy.FullTree.rootVertex _ :=
          (graph_fork_adj_left_root _ _ _).mp hxy
        exact False.elim (p.root_not_below ⟨z, hroot⟩)
      · have hy' : ¬ p.Below y := by
          intro hy'
          rcases hy' with ⟨w, rfl⟩
          exact hy ⟨w, rfl⟩
        have hxy' : (TreeAdequacy.FullTree.graph _).Adj (p.embed z) y :=
          (graph_fork_adj_left_left _ _ _ _).mp hxy
        obtain ⟨hz, hypar⟩ := ih ⟨z, rfl⟩ hy' hxy'
        constructor
        · change Sum.inl (Sum.inr (p.embed z)) =
            Sum.inl (Sum.inr p.child)
          rw [hz]
        · rw [hypar]
          rfl
      · exact False.elim (not_graph_fork_adj_left_right _ _ _ _ hxy)
  | inRight p ih =>
      rcases hx with ⟨z, rfl⟩
      rcases y with ((u | y) | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hroot : p.embed z = TreeAdequacy.FullTree.rootVertex _ :=
          (graph_fork_adj_right_root _ _ _).mp hxy
        exact False.elim (p.root_not_below ⟨z, hroot⟩)
      · exact False.elim (not_graph_fork_adj_right_left _ _ _ _ hxy)
      · have hy' : ¬ p.Below y := by
          intro hy'
          rcases hy' with ⟨w, rfl⟩
          exact hy ⟨w, rfl⟩
        have hxy' : (TreeAdequacy.FullTree.graph _).Adj (p.embed z) y :=
          (graph_fork_adj_right_right _ _ _ _).mp hxy
        obtain ⟨hz, hypar⟩ := ih ⟨z, rfl⟩ hy' hxy'
        constructor
        · change Sum.inr (p.embed z) = Sum.inr p.child
          rw [hz]
        · rw [hypar]
          rfl

/-- Internal adjacency is preserved by the vertex embedding of a subtree
occurrence. -/
theorem ProperSubtree.map_adj {t : Tree.FullTree α}
    (p : ProperSubtree t) {x y : TreeAdequacy.FullTree.Vertex p.tree}
    (hxy : (TreeAdequacy.FullTree.graph p.tree).Adj x y) :
    (TreeAdequacy.FullTree.graph t).Adj (p.embed x) (p.embed y) := by
  induction p with
  | left l r => exact (graph_fork_adj_left_left l r x y).2 hxy
  | right l r => exact (graph_fork_adj_right_right l r x y).2 hxy
  | inLeft p ih => exact (graph_fork_adj_left_left _ _ _ _).2 (ih hxy)
  | inRight p ih => exact (graph_fork_adj_right_right _ _ _ _).2 (ih hxy)

/-- The subtree graph maps into the ambient graph after its parent edge has
been deleted. -/
def ProperSubtree.embedDeletedHom {t : Tree.FullTree α}
    (p : ProperSubtree t) :
    TreeAdequacy.FullTree.graph p.tree →g
      (TreeAdequacy.FullTree.graph t).deleteEdges {s(p.parent, p.child)} where
  toFun := p.embed
  map_rel' {x y} hxy := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨p.map_adj hxy, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hx, _⟩ | ⟨_, hy⟩)
    · exact p.parent_not_below ⟨x, hx⟩
    · exact p.parent_not_below ⟨y, hy⟩

/-- Every vertex below a parent edge stays reachable from the child endpoint
after that edge is deleted. -/
theorem ProperSubtree.reachable_of_below {t : Tree.FullTree α}
    (p : ProperSubtree t) {x : TreeAdequacy.FullTree.Vertex t}
    (hx : p.Below x) :
    ((TreeAdequacy.FullTree.graph t).deleteEdges {s(p.parent, p.child)}).Reachable
      p.child x := by
  rcases hx with ⟨z, rfl⟩
  have hconn := (TreeAdequacy.FullTree.graph_isTree p.tree).connected
  have hreach : (TreeAdequacy.FullTree.graph p.tree).Reachable
      (TreeAdequacy.FullTree.rootVertex p.tree) z := hconn _ _
  have hmapped := hreach.map p.embedDeletedHom
  change ((TreeAdequacy.FullTree.graph t).deleteEdges
    {s(p.parent, p.child)}).Reachable p.child (p.embed z) at hmapped
  exact hmapped

/-- Conversely, a walk from the child endpoint that avoids the parent edge
cannot leave the subtree occurrence. -/
theorem ProperSubtree.below_of_reachable {t : Tree.FullTree α}
    (p : ProperSubtree t) {x : TreeAdequacy.FullTree.Vertex t}
    (hx : ((TreeAdequacy.FullTree.graph t).deleteEdges
      {s(p.parent, p.child)}).Reachable p.child x) : p.Below x := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact p.child_below
  | tail hreach hbc ih =>
      by_contra hc
      have hadj := (SimpleGraph.deleteEdges_adj.mp hbc).1
      have hnotedge := (SimpleGraph.deleteEdges_adj.mp hbc).2
      obtain ⟨hb, hcparent⟩ := p.adj_boundary ih hc hadj
      apply hnotedge
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      exact Or.inr ⟨hb, hcparent⟩

theorem ProperSubtree.reachable_iff_below {t : Tree.FullTree α}
    (p : ProperSubtree t) (x : TreeAdequacy.FullTree.Vertex t) :
    ((TreeAdequacy.FullTree.graph t).deleteEdges {s(p.parent, p.child)}).Reachable
      p.child x ↔ p.Below x :=
  ⟨p.below_of_reachable, p.reachable_of_below⟩

/-- A label seen at a realization vertex occurs in the syntax leaf list. -/
theorem label_mem_leaves (t : Tree.FullTree α)
    {x : TreeAdequacy.FullTree.Vertex t} {a : α}
    (hx : TreeAdequacy.FullTree.label? t x = some a) : a ∈ t.leaves := by
  induction t with
  | leaf b =>
      have hba : b = a := by simpa [TreeAdequacy.FullTree.label?] using hx
      subst a
      simp
  | fork l r ihl ihr =>
      rcases x with ((u | x) | x)
      · simp [TreeAdequacy.FullTree.label?] at hx
      · rw [Tree.FullTree.leaves_fork, List.mem_append]
        exact Or.inl (ihl hx)
      · rw [Tree.FullTree.leaves_fork, List.mem_append]
        exact Or.inr (ihr hx)

/-- With duplicate-free syntax leaves, a label occurs at only one graph
vertex. -/
theorem label_vertex_unique_of_nodup (t : Tree.FullTree α)
    (ht : t.leaves.Nodup) {x y : TreeAdequacy.FullTree.Vertex t} {a : α}
    (hx : TreeAdequacy.FullTree.label? t x = some a)
    (hy : TreeAdequacy.FullTree.label? t y = some a) : x = y := by
  induction t with
  | leaf b => exact Subsingleton.elim _ _
  | fork l r ihl ihr =>
      rcases x with ((ux | x) | x) <;> rcases y with ((uy | y) | y)
      · simp [TreeAdequacy.FullTree.label?] at hx
      · simp [TreeAdequacy.FullTree.label?] at hx
      · simp [TreeAdequacy.FullTree.label?] at hx
      · simp [TreeAdequacy.FullTree.label?] at hy
      · exact congrArg (fun z => Sum.inl (Sum.inr z))
          (ihl ht.of_append_left hx hy)
      · have hxl : a ∈ l.leaves := label_mem_leaves l hx
        have hyr : a ∈ r.leaves := label_mem_leaves r hy
        exact False.elim (List.disjoint_left.mp ht.disjoint hxl hyr)
      · simp [TreeAdequacy.FullTree.label?] at hy
      · have hxr : a ∈ r.leaves := label_mem_leaves r hx
        have hyl : a ∈ l.leaves := label_mem_leaves l hy
        exact False.elim (List.disjoint_left.mp ht.disjoint hyl hxr)
      · exact congrArg Sum.inr (ihr ht.of_append_right hx hy)

/-- The subtree embedding preserves the partial leaf label map. -/
theorem ProperSubtree.label_embed {t : Tree.FullTree α}
    (p : ProperSubtree t) (x : TreeAdequacy.FullTree.Vertex p.tree) :
    TreeAdequacy.FullTree.label? t (p.embed x) =
      TreeAdequacy.FullTree.label? p.tree x := by
  induction p with
  | left => rfl
  | right => rfl
  | inLeft p ih => exact ih x
  | inRight p ih => exact ih x

/-- Labels in the child component of an oriented parent edge are exactly the
leaves of the corresponding syntax subtree. -/
theorem ProperSubtree.exists_label_below_iff {t : Tree.FullTree α}
    (p : ProperSubtree t) (a : α) :
    (∃ x : TreeAdequacy.FullTree.Vertex t,
      TreeAdequacy.FullTree.label? t x = some a ∧ p.Below x) ↔
      a ∈ p.tree.leaves := by
  constructor
  · rintro ⟨x, hx, ⟨z, rfl⟩⟩
    apply label_mem_leaves p.tree
    rw [← p.label_embed]
    exact hx
  · intro ha
    obtain ⟨z, hz⟩ := TreeAdequacy.FullTree.exists_vertex_label_of_mem p.tree ha
    exact ⟨p.embed z, p.label_embed z ▸ hz, ⟨z, rfl⟩⟩

theorem ProperSubtree.exists_label_reachable_iff {t : Tree.FullTree α}
    (p : ProperSubtree t) (a : α) :
    (∃ x : TreeAdequacy.FullTree.Vertex t,
      TreeAdequacy.FullTree.label? t x = some a ∧
      ((TreeAdequacy.FullTree.graph t).deleteEdges
        {s(p.parent, p.child)}).Reachable p.child x) ↔
      a ∈ p.tree.leaves := by
  simp only [p.reachable_iff_below]
  exact p.exists_label_below_iff a

/-- Every graph edge of a full-tree realization is the parent edge of a
unique syntax subtree occurrence, up to orientation.  Existence is the part
needed for quartet separation. -/
theorem exists_properSubtree_of_adj (t : Tree.FullTree α)
    {x y : TreeAdequacy.FullTree.Vertex t}
    (hxy : (TreeAdequacy.FullTree.graph t).Adj x y) :
    ∃ p : ProperSubtree t,
      (x = p.parent ∧ y = p.child) ∨ (x = p.child ∧ y = p.parent) := by
  induction t with
  | leaf a => simp [TreeAdequacy.FullTree.graph] at hxy
  | fork l r ihl ihr =>
      rcases x with ((ux | x) | x) <;> rcases y with ((uy | y) | y)
      · have hux : ux = () := Subsingleton.elim _ _
        have huy : uy = () := Subsingleton.elim _ _
        subst ux
        subst uy
        exact False.elim (hxy.ne rfl)
      · have hroot := (graph_fork_adj_root_left l r y).mp
          (by simpa [show ux = () from Subsingleton.elim _ _] using hxy)
        refine ⟨.left l r, Or.inl ⟨?_, ?_⟩⟩
        · simp [ProperSubtree.parent, TreeAdequacy.FullTree.rootVertex,
            show ux = () from Subsingleton.elim _ _]
        · rw [hroot]
          rfl
      · have hroot := (graph_fork_adj_root_right l r y).mp
          (by simpa [show ux = () from Subsingleton.elim _ _] using hxy)
        refine ⟨.right l r, Or.inl ⟨?_, ?_⟩⟩
        · simp [ProperSubtree.parent, TreeAdequacy.FullTree.rootVertex,
            show ux = () from Subsingleton.elim _ _]
        · rw [hroot]
          rfl
      · have hroot := (graph_fork_adj_left_root l r x).mp
          (by simpa [show uy = () from Subsingleton.elim _ _] using hxy)
        refine ⟨.left l r, Or.inr ⟨?_, ?_⟩⟩
        · rw [hroot]
          rfl
        · simp [ProperSubtree.parent, TreeAdequacy.FullTree.rootVertex,
            show uy = () from Subsingleton.elim _ _]
      · obtain ⟨p, hp | hp⟩ := ihl ((graph_fork_adj_left_left l r x y).mp hxy)
        · refine ⟨p.inLeft, Or.inl ⟨?_, ?_⟩⟩
          · rw [hp.1]
            rfl
          · rw [hp.2]
            rfl
        · refine ⟨p.inLeft, Or.inr ⟨?_, ?_⟩⟩
          · rw [hp.1]
            rfl
          · rw [hp.2]
            rfl
      · exact False.elim (not_graph_fork_adj_left_right l r x y hxy)
      · have hroot := (graph_fork_adj_right_root l r x).mp
          (by simpa [show uy = () from Subsingleton.elim _ _] using hxy)
        refine ⟨.right l r, Or.inr ⟨?_, ?_⟩⟩
        · rw [hroot]
          rfl
        · simp [ProperSubtree.parent, TreeAdequacy.FullTree.rootVertex,
            show uy = () from Subsingleton.elim _ _]
      · exact False.elim (not_graph_fork_adj_right_left l r x y hxy)
      · obtain ⟨p, hp | hp⟩ := ihr ((graph_fork_adj_right_right l r x y).mp hxy)
        · refine ⟨p.inRight, Or.inl ⟨?_, ?_⟩⟩
          · rw [hp.1]
            rfl
          · rw [hp.2]
            rfl
        · refine ⟨p.inRight, Or.inr ⟨?_, ?_⟩⟩
          · rw [hp.1]
            rfl
          · rw [hp.2]
            rfl

theorem ProperSubtree.leaves_subset [DecidableEq α] {t : Tree.FullTree α}
    (p : ProperSubtree t) : p.tree.leaves.toFinset ⊆ t.leaves.toFinset := by
  induction p with
  | left l r => simp [Tree.FullTree.leaves]
  | right l r => simp [Tree.FullTree.leaves]
  | inLeft p ih => exact ih.trans (by simp [Tree.FullTree.leaves])
  | inRight p ih => exact ih.trans (by simp [Tree.FullTree.leaves])

theorem ProperSubtree.leaves_nodup {t : Tree.FullTree α}
    (p : ProperSubtree t) (ht : t.leaves.Nodup) : p.tree.leaves.Nodup := by
  induction p with
  | left => exact ht.of_append_left
  | right => exact ht.of_append_right
  | inLeft p ih => exact ih ht.of_append_left
  | inRight p ih => exact ih ht.of_append_right

private theorem leaves_finset_disjoint [DecidableEq α] (l r : Tree.FullTree α)
    (h : (Tree.FullTree.leaves (.fork l r)).Nodup) :
    Disjoint l.leaves.toFinset r.leaves.toFinset := by
  rw [Finset.disjoint_left]
  intro a hal har
  exact List.disjoint_left.mp h.disjoint (by simpa using hal) (by simpa using har)

/-- Leaf clusters of two rooted subtree occurrences are laminar. -/
theorem ProperSubtree.clusters_laminar [DecidableEq α] {t : Tree.FullTree α}
    (p q : ProperSubtree t) (ht : t.leaves.Nodup) :
    p.tree.leaves.toFinset ⊆ q.tree.leaves.toFinset ∨
      q.tree.leaves.toFinset ⊆ p.tree.leaves.toFinset ∨
      Disjoint p.tree.leaves.toFinset q.tree.leaves.toFinset := by
  induction p with
  | left l r =>
      cases q with
      | left => exact Or.inl (by simp)
      | right => exact Or.inr (Or.inr (leaves_finset_disjoint l r ht))
      | inLeft q => exact Or.inr (Or.inl q.leaves_subset)
      | inRight q =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a hal haq
          exact Finset.disjoint_left.1 (leaves_finset_disjoint l r ht)
            hal (q.leaves_subset haq)
  | right l r =>
      cases q with
      | left => exact Or.inr (Or.inr (leaves_finset_disjoint l r ht).symm)
      | right => exact Or.inl (by simp)
      | inLeft q =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a har haq
          exact Finset.disjoint_left.1 (leaves_finset_disjoint l r ht).symm
            har (q.leaves_subset haq)
      | inRight q => exact Or.inr (Or.inl q.leaves_subset)
  | inLeft p ih =>
      cases q with
      | left => exact Or.inl p.leaves_subset
      | right =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a hap har
          exact Finset.disjoint_left.1 (leaves_finset_disjoint _ _ ht)
            (p.leaves_subset hap) har
      | inLeft q => exact ih q ht.of_append_left
      | inRight q =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a hap haq
          exact Finset.disjoint_left.1 (leaves_finset_disjoint _ _ ht)
            (p.leaves_subset hap) (q.leaves_subset haq)
  | inRight p ih =>
      cases q with
      | left =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a hap hal
          exact Finset.disjoint_left.1 (leaves_finset_disjoint _ _ ht).symm
            (p.leaves_subset hap) hal
      | right => exact Or.inl p.leaves_subset
      | inLeft q =>
          refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
          intro a hap haq
          exact Finset.disjoint_left.1 (leaves_finset_disjoint _ _ ht).symm
            (p.leaves_subset hap) (q.leaves_subset haq)
      | inRight q => exact ih q ht.of_append_right

end FullTree

/-! ## Oriented edges of the unrooted phylogenetic realization -/

namespace PhyloTree

variable {α : Type} [DecidableEq α]

theorem isQuartetSplit_side_card {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A : Finset α} (hA : A ∈ s) : A.card = 2 := by
  rcases hs with ⟨q, rfl, rfl⟩
  simp [Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair] at hA
  rcases hA with rfl | rfl
  · simp [q.injective.eq_iff]
  · simp [q.injective.eq_iff]

theorem isQuartetSplit_side_subset {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A : Finset α} (hA : A ∈ s) : A ⊆ Q := by
  rcases hs with ⟨q, rfl, rfl⟩
  simp [Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair] at hA
  rcases hA with rfl | rfl
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp

theorem isQuartetSplit_eq_pair_of_mem {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A B : Finset α} (hA : A ∈ s) (hB : B ∈ s) (hne : A ≠ B) :
    s = {A, B} := by
  rcases hs with ⟨q, rfl, rfl⟩
  simp [Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact False.elim (hne rfl)
  · simp [Circular.crossing, Circular.canonicalCrossing,
      Circular.mapSplit, Circular.splitOf, Circular.pair]
  · simp [Circular.crossing, Circular.canonicalCrossing,
      Circular.mapSplit, Circular.splitOf, Circular.pair, Finset.pair_comm]
  · exact False.elim (hne rfl)

theorem isQuartetSplit_sides_disjoint {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A B : Finset α} (hA : A ∈ s) (hB : B ∈ s) (hne : A ≠ B) :
    Disjoint A B := by
  rcases hs with ⟨q, rfl, rfl⟩
  simp [Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact False.elim (hne rfl)
  · simp [Finset.disjoint_left, q.injective.eq_iff]
  · simp [Finset.disjoint_left, q.injective.eq_iff]
  · exact False.elim (hne rfl)

theorem isQuartetSplit_union_sides {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A B : Finset α} (hA : A ∈ s) (hB : B ∈ s) (hne : A ≠ B) :
    A ∪ B = Q := by
  rcases hs with ⟨q, rfl, rfl⟩
  simp [Circular.crossing, Circular.canonicalCrossing,
    Circular.mapSplit, Circular.splitOf, Circular.pair] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact False.elim (hne rfl)
  · ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ((rfl | rfl) | (rfl | rfl)) <;> simp
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  · ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ((rfl | rfl) | (rfl | rfl)) <;> simp
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  · exact False.elim (hne rfl)

theorem isQuartetSplit_other_eq_sdiff {Q : Finset α}
    {s : Circular.QuartetSplit α} (hs : Circular.IsQuartetSplit Q s)
    {A B : Finset α} (hA : A ∈ s) (hB : B ∈ s) (hne : A ≠ B) :
    B = Q \ A := by
  have hdisj := isQuartetSplit_sides_disjoint hs hA hB hne
  have hunion := isQuartetSplit_union_sides hs hA hB hne
  ext x
  constructor
  · intro hxB
    apply Finset.mem_sdiff.mpr
    exact ⟨isQuartetSplit_side_subset hs hB hxB,
      fun hxA => Finset.disjoint_left.mp hdisj hxA hxB⟩
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxUnion : x ∈ A ∪ B := by
      rw [hunion]
      exact hx'.1
    rcases Finset.mem_union.mp hxUnion with hxA | hxB
    · exact False.elim (hx'.2 hxA)
    · exact hxB

/-- Every two-element subset of a four-element set, paired with its
complement, is a well-formed quartet split. -/
theorem pair_sdiff_isQuartetSplit (Q A : Finset α)
    (hQ : Q.card = 4) (hAQ : A ⊆ Q) (hAcard : A.card = 2) :
    Circular.IsQuartetSplit Q
      ({A, Q \ A} : Circular.QuartetSplit α) := by
  have hMcard : (Q \ A).card = 2 := by
    rw [Finset.card_sdiff_of_subset hAQ, hQ, hAcard]
  obtain ⟨a, c, hac, hA⟩ := Finset.card_eq_two.mp hAcard
  obtain ⟨b, d, hbd, hM⟩ := Finset.card_eq_two.mp hMcard
  have hM' : Q \ {a, c} = {b, d} := by simpa [← hA] using hM
  have hdisj : Disjoint A (Q \ A) := Finset.disjoint_sdiff
  let q : Circular.Four ↪ α :=
    ⟨![a, b, c, d], by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Finset.disjoint_left]⟩
  refine ⟨q, ?_, ?_⟩
  · rw [← Finset.sdiff_union_of_subset hAQ, hA, hM']
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ((rfl | rfl) | (rfl | rfl))
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [q]
  · simp [q, Circular.crossing, Circular.canonicalCrossing,
      Circular.mapSplit, Circular.splitOf, Circular.pair, hA, hM']

/-- Two `2+2` partitions of the same quartet agree up to exchanging their
sides whenever their chosen sides arise by restricting laminar clusters. -/
theorem pair_sdiff_eq_of_laminar (Q A L : Finset α)
    (hQ : Q.card = 4) (hAQ : A ⊆ Q) (hLQ : L ⊆ Q)
    (hAcard : A.card = 2) (hLcard : L.card = 2)
    (hlam : A ⊆ L ∨ L ⊆ A ∨ Disjoint A L) :
    ({A, Q \ A} : Circular.QuartetSplit α) = {L, Q \ L} := by
  rcases hlam with hAL | hLA | hdisj
  · have hEq : A = L := Finset.eq_of_subset_of_card_le hAL (by omega)
    rw [hEq]
  · have hEq : L = A := Finset.eq_of_subset_of_card_le hLA (by omega)
    rw [hEq]
  · have hUnionSub : A ∪ L ⊆ Q := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxA | hxL
      · exact hAQ hxA
      · exact hLQ hxL
    have hUnionCard : (A ∪ L).card = Q.card := by
      rw [Finset.card_union_of_disjoint hdisj, hAcard, hLcard, hQ]
    have hUnion : A ∪ L = Q :=
      Finset.eq_of_subset_of_card_le hUnionSub (by omega)
    have hAcomp : A = Q \ L := by
      ext x
      constructor
      · intro hxA
        apply Finset.mem_sdiff.mpr
        exact ⟨hAQ hxA, fun hxL => Finset.disjoint_left.mp hdisj hxA hxL⟩
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        have hxUnion : x ∈ A ∪ L := by
          rw [hUnion]
          exact hx'.1
        rcases Finset.mem_union.mp hxUnion with hxA | hxL
        · exact hxA
        · exact False.elim (hx'.2 hxL)
    have hdouble : Q \ (Q \ L) = L := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        by_contra hxL
        exact hx'.2 (Finset.mem_sdiff.mpr ⟨hx'.1, hxL⟩)
      · intro hxL
        apply Finset.mem_sdiff.mpr
        exact ⟨hLQ hxL, fun hx => (Finset.mem_sdiff.mp hx).2 hxL⟩
    rw [hAcomp, hdouble, Finset.pair_comm]

variable [Fintype α]

/-- The edge incident with the distinguished root leaf, or an edge internal
to the crown. -/
inductive EdgePosition (T : Tree.PhyloTree α) : Type
  | crown : EdgePosition T
  | inside : FullTree.ProperSubtree T.crown → EdgePosition T

def EdgePosition.tree {T : Tree.PhyloTree α} :
    EdgePosition T → Tree.FullTree {a : α // a ≠ T.root}
  | .crown => T.crown
  | .inside p => p.tree

@[simp] theorem EdgePosition.tree_crown (T : Tree.PhyloTree α) :
    (EdgePosition.crown (T := T)).tree = T.crown := rfl

@[simp] theorem EdgePosition.tree_inside {T : Tree.PhyloTree α}
    (p : FullTree.ProperSubtree T.crown) :
    (EdgePosition.inside p).tree = p.tree := rfl

def EdgePosition.embed {T : Tree.PhyloTree α} (p : EdgePosition T) :
    TreeAdequacy.FullTree.Vertex p.tree → TreeAdequacy.PhyloTree.Vertex T :=
  match p with
  | .crown => fun x => .inr x
  | .inside q => fun x => .inr (q.embed x)

def EdgePosition.child {T : Tree.PhyloTree α} (p : EdgePosition T) :
    TreeAdequacy.PhyloTree.Vertex T :=
  p.embed (TreeAdequacy.FullTree.rootVertex p.tree)

def EdgePosition.parent {T : Tree.PhyloTree α} :
    EdgePosition T → TreeAdequacy.PhyloTree.Vertex T
  | .crown => .inl ()
  | .inside p => .inr p.parent

def EdgePosition.Below {T : Tree.PhyloTree α} (p : EdgePosition T)
    (x : TreeAdequacy.PhyloTree.Vertex T) : Prop :=
  x ∈ Set.range p.embed

@[simp] theorem EdgePosition.child_below {T : Tree.PhyloTree α}
    (p : EdgePosition T) : p.Below p.child :=
  ⟨TreeAdequacy.FullTree.rootVertex p.tree, rfl⟩

@[simp] theorem EdgePosition.parent_not_below {T : Tree.PhyloTree α}
    (p : EdgePosition T) : ¬ p.Below p.parent := by
  cases p with
  | crown => simp [EdgePosition.Below, EdgePosition.parent, EdgePosition.embed]
  | inside p =>
      rintro ⟨x, hx⟩
      change Sum.inr (p.embed x) = Sum.inr p.parent at hx
      exact p.parent_not_below ⟨x, Sum.inr.inj hx⟩

@[simp] theorem graph_adj_root_crown (T : Tree.PhyloTree α)
    (x : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inl ()) (.inr x) ↔
      x = TreeAdequacy.FullTree.rootVertex T.crown := by
  simp [TreeAdequacy.PhyloTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_adj_crown_root (T : Tree.PhyloTree α)
    (x : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inr x) (.inl ()) ↔
      x = TreeAdequacy.FullTree.rootVertex T.crown := by
  rw [SimpleGraph.adj_comm, graph_adj_root_crown]

@[simp] theorem graph_adj_crown_crown (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inr x) (.inr y) ↔
      (TreeAdequacy.FullTree.graph T.crown).Adj x y := by
  simp [TreeAdequacy.PhyloTree.graph, SimpleGraph.edge_adj]

theorem EdgePosition.adj_parent_child {T : Tree.PhyloTree α}
    (p : EdgePosition T) :
    (TreeAdequacy.PhyloTree.graph T).Adj p.parent p.child := by
  cases p with
  | crown => exact (graph_adj_root_crown T _).2 rfl
  | inside p => exact (graph_adj_crown_crown T _ _).2 p.adj_parent_child

/-- The oriented parent edge is the only edge leaving the represented crown
subtree. -/
theorem EdgePosition.adj_boundary {T : Tree.PhyloTree α}
    (p : EdgePosition T) {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hx : p.Below x) (hy : ¬ p.Below y)
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y) :
    x = p.child ∧ y = p.parent := by
  cases p with
  | crown =>
      rcases hx with ⟨z, rfl⟩
      rcases y with (u | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hz := (graph_adj_crown_root T z).mp hxy
        constructor
        · rw [hz]
          rfl
        · rfl
      · exact False.elim (hy ⟨y, rfl⟩)
  | inside p =>
      rcases hx with ⟨z, rfl⟩
      rcases y with (u | y)
      · have hu : u = () := Subsingleton.elim _ _
        subst u
        have hroot := (graph_adj_crown_root T (p.embed z)).mp hxy
        exact False.elim (p.root_not_below ⟨z, hroot⟩)
      · have hy' : ¬ p.Below y := by
          intro hy'
          rcases hy' with ⟨w, rfl⟩
          exact hy ⟨w, rfl⟩
        have hxy' := (graph_adj_crown_crown T (p.embed z) y).mp hxy
        obtain ⟨hz, hypar⟩ := p.adj_boundary ⟨z, rfl⟩ hy' hxy'
        constructor
        · change Sum.inr (p.embed z) = Sum.inr p.child
          rw [hz]
        · change Sum.inr y = Sum.inr p.parent
          rw [hypar]

theorem EdgePosition.map_adj {T : Tree.PhyloTree α}
    (p : EdgePosition T) {x y : TreeAdequacy.FullTree.Vertex p.tree}
    (hxy : (TreeAdequacy.FullTree.graph p.tree).Adj x y) :
    (TreeAdequacy.PhyloTree.graph T).Adj (p.embed x) (p.embed y) := by
  cases p with
  | crown => exact (graph_adj_crown_crown T x y).2 hxy
  | inside p => exact (graph_adj_crown_crown T _ _).2 (p.map_adj hxy)

def EdgePosition.embedDeletedHom {T : Tree.PhyloTree α}
    (p : EdgePosition T) :
    TreeAdequacy.FullTree.graph p.tree →g
      (TreeAdequacy.PhyloTree.graph T).deleteEdges {s(p.parent, p.child)} where
  toFun := p.embed
  map_rel' {x y} hxy := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨p.map_adj hxy, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hx, _⟩ | ⟨_, hy⟩)
    · exact p.parent_not_below ⟨x, hx⟩
    · exact p.parent_not_below ⟨y, hy⟩

theorem EdgePosition.reachable_of_below {T : Tree.PhyloTree α}
    (p : EdgePosition T) {x : TreeAdequacy.PhyloTree.Vertex T}
    (hx : p.Below x) :
    ((TreeAdequacy.PhyloTree.graph T).deleteEdges {s(p.parent, p.child)}).Reachable
      p.child x := by
  rcases hx with ⟨z, rfl⟩
  have hreach : (TreeAdequacy.FullTree.graph p.tree).Reachable
      (TreeAdequacy.FullTree.rootVertex p.tree) z :=
    (TreeAdequacy.FullTree.graph_isTree p.tree).connected _ _
  have hmapped := hreach.map p.embedDeletedHom
  change ((TreeAdequacy.PhyloTree.graph T).deleteEdges
    {s(p.parent, p.child)}).Reachable p.child (p.embed z) at hmapped
  exact hmapped

theorem EdgePosition.below_of_reachable {T : Tree.PhyloTree α}
    (p : EdgePosition T) {x : TreeAdequacy.PhyloTree.Vertex T}
    (hx : ((TreeAdequacy.PhyloTree.graph T).deleteEdges
      {s(p.parent, p.child)}).Reachable p.child x) : p.Below x := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact p.child_below
  | tail hreach hbc ih =>
      by_contra hc
      have hadj := (SimpleGraph.deleteEdges_adj.mp hbc).1
      have hnotedge := (SimpleGraph.deleteEdges_adj.mp hbc).2
      obtain ⟨hb, hcparent⟩ := p.adj_boundary ih hc hadj
      apply hnotedge
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      exact Or.inr ⟨hb, hcparent⟩

theorem EdgePosition.reachable_iff_below {T : Tree.PhyloTree α}
    (p : EdgePosition T) (x : TreeAdequacy.PhyloTree.Vertex T) :
    ((TreeAdequacy.PhyloTree.graph T).deleteEdges {s(p.parent, p.child)}).Reachable
      p.child x ↔ p.Below x :=
  ⟨p.below_of_reachable, p.reachable_of_below⟩

/-- The other endpoint reaches precisely the complementary component. -/
theorem EdgePosition.parent_reachable_iff_not_below {T : Tree.PhyloTree α}
    (p : EdgePosition T) (x : TreeAdequacy.PhyloTree.Vertex T) :
    ((TreeAdequacy.PhyloTree.graph T).deleteEdges {s(p.parent, p.child)}).Reachable
      p.parent x ↔ ¬ p.Below x := by
  constructor
  · intro hparent hbelow
    have hchild := p.reachable_of_below hbelow
    have hcp : ((TreeAdequacy.PhyloTree.graph T).deleteEdges
        {s(p.parent, p.child)}).Reachable p.child p.parent :=
      hchild.trans hparent.symm
    exact p.parent_not_below (p.below_of_reachable hcp)
  · intro hbelow
    have hambient : (TreeAdequacy.PhyloTree.graph T).Reachable p.parent x :=
      (TreeAdequacy.PhyloTree.graph_isTree T).connected _ _
    rcases reachable_endpoint_or_endpoint_after_delete
      (TreeAdequacy.PhyloTree.graph T) p.parent p.child x hambient with hp | hc
    · exact hp
    · exact False.elim (hbelow (p.below_of_reachable hc))

/-- The partial label map of a syntactic phylogenetic graph is injective on
its labelled vertices. -/
theorem label_vertex_unique (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T} {a : α}
    (hx : TreeAdequacy.PhyloTree.label? T x = some a)
    (hy : TreeAdequacy.PhyloTree.label? T y = some a) : x = y := by
  rcases x with (ux | x) <;> rcases y with (uy | y)
  · exact congrArg Sum.inl (Subsingleton.elim ux uy)
  · change (TreeAdequacy.FullTree.label? T.crown y).map Subtype.val = some a at hy
    cases hlocal : TreeAdequacy.FullTree.label? T.crown y with
    | none => simp [hlocal] at hy
    | some b =>
        have hba : b.1 = a := by simpa [hlocal] using hy
        have hua : T.root = a := by simpa [TreeAdequacy.PhyloTree.label?] using hx
        exact False.elim (b.2 (hba.trans hua.symm))
  · change (TreeAdequacy.FullTree.label? T.crown x).map Subtype.val = some a at hx
    cases hlocal : TreeAdequacy.FullTree.label? T.crown x with
    | none => simp [hlocal] at hx
    | some b =>
        have hba : b.1 = a := by simpa [hlocal] using hx
        have hua : T.root = a := by simpa [TreeAdequacy.PhyloTree.label?] using hy
        exact False.elim (b.2 (hba.trans hua.symm))
  · change (TreeAdequacy.FullTree.label? T.crown x).map Subtype.val = some a at hx
    change (TreeAdequacy.FullTree.label? T.crown y).map Subtype.val = some a at hy
    cases hxl : TreeAdequacy.FullTree.label? T.crown x with
    | none => simp [hxl] at hx
    | some b =>
        cases hyl : TreeAdequacy.FullTree.label? T.crown y with
        | none => simp [hyl] at hy
        | some c =>
            have hba : b.1 = a := by simpa [hxl] using hx
            have hca : c.1 = a := by simpa [hyl] using hy
            have hbc : b = c := Subtype.ext (hba.trans hca.symm)
            subst c
            exact congrArg Sum.inr
              (FullTree.label_vertex_unique_of_nodup T.crown T.nodup_leaves hxl hyl)

/-- Taxon labels below an oriented edge. -/
def EdgePosition.cluster {T : Tree.PhyloTree α} (p : EdgePosition T) : Finset α :=
  p.tree.leaves.toFinset.image Subtype.val

theorem EdgePosition.label_embed {T : Tree.PhyloTree α}
    (p : EdgePosition T) (x : TreeAdequacy.FullTree.Vertex p.tree) :
    TreeAdequacy.PhyloTree.label? T (p.embed x) =
      (TreeAdequacy.FullTree.label? p.tree x).map Subtype.val := by
  cases p with
  | crown => rfl
  | inside p =>
      change (TreeAdequacy.FullTree.label? T.crown (p.embed x)).map Subtype.val = _
      simpa using congrArg (Option.map Subtype.val) (p.label_embed x)

theorem EdgePosition.exists_label_below_iff {T : Tree.PhyloTree α}
    (p : EdgePosition T) (a : α) :
    (∃ x : TreeAdequacy.PhyloTree.Vertex T,
      TreeAdequacy.PhyloTree.label? T x = some a ∧ p.Below x) ↔
      a ∈ p.cluster := by
  constructor
  · rintro ⟨x, hx, ⟨z, rfl⟩⟩
    have hmap : (TreeAdequacy.FullTree.label? p.tree z).map Subtype.val =
        some a := by rw [← p.label_embed]; exact hx
    cases hlocal : TreeAdequacy.FullTree.label? p.tree z with
    | none => simp [hlocal] at hmap
    | some b =>
        have hba : b.1 = a := by simpa [hlocal] using hmap
        rw [← hba]
        simp only [EdgePosition.cluster, Finset.mem_image]
        have hbmem : b ∈ p.tree.leaves := FullTree.label_mem_leaves p.tree hlocal
        exact ⟨b, by simpa using hbmem, rfl⟩
  · intro ha
    simp only [EdgePosition.cluster, Finset.mem_image] at ha
    obtain ⟨b, hb, hba⟩ := ha
    obtain ⟨z, hz⟩ := TreeAdequacy.FullTree.exists_vertex_label_of_mem p.tree
      (by simpa using hb)
    refine ⟨p.embed z, ?_, ⟨z, rfl⟩⟩
    rw [p.label_embed, hz]
    simpa using hba

theorem EdgePosition.exists_label_reachable_iff {T : Tree.PhyloTree α}
    (p : EdgePosition T) (a : α) :
    (∃ x : TreeAdequacy.PhyloTree.Vertex T,
      TreeAdequacy.PhyloTree.label? T x = some a ∧
      ((TreeAdequacy.PhyloTree.graph T).deleteEdges
        {s(p.parent, p.child)}).Reachable p.child x) ↔
      a ∈ p.cluster := by
  simp only [p.reachable_iff_below]
  exact p.exists_label_below_iff a

/-- The generic graph-component predicate has the expected finite cluster
description on every oriented edge of the syntax realization. -/
theorem componentSeparatesAt_position_iff {T : Tree.PhyloTree α}
    (p : EdgePosition T) (A B : Finset α) :
    ComponentSeparatesAt (TreeAdequacy.PhyloTree.graph T)
        (TreeAdequacy.PhyloTree.label? T) p.child p.parent A B ↔
      (∀ a ∈ A, a ∈ p.cluster) ∧ (∀ b ∈ B, b ∉ p.cluster) := by
  have hedge : ({s(p.child, p.parent)} :
      Set (Sym2 (TreeAdequacy.PhyloTree.Vertex T))) =
      {s(p.parent, p.child)} := by rw [Sym2.eq_swap]
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨x, hx, hr⟩ := hA a ha
      apply (p.exists_label_reachable_iff a).1
      exact ⟨x, hx, by simpa only [hedge] using hr⟩
    · intro b hb hbc
      obtain ⟨x, hx, hr⟩ := (p.exists_label_reachable_iff b).2 hbc
      exact hB b hb x hx (by simpa only [hedge] using hr)
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨x, hx, hr⟩ := (p.exists_label_reachable_iff a).2 (hA a ha)
      exact ⟨x, hx, by simpa only [hedge] using hr⟩
    · intro b hb x hx hr
      apply hB b hb
      apply (p.exists_label_reachable_iff b).1
      exact ⟨x, hx, by simpa only [hedge] using hr⟩

theorem EdgePosition.exists_label_parent_reachable_iff
    {T : Tree.PhyloTree α} (p : EdgePosition T) (a : α) :
    (∃ x : TreeAdequacy.PhyloTree.Vertex T,
      TreeAdequacy.PhyloTree.label? T x = some a ∧
      ((TreeAdequacy.PhyloTree.graph T).deleteEdges
        {s(p.parent, p.child)}).Reachable p.parent x) ↔
      a ∉ p.cluster := by
  constructor
  · rintro ⟨x, hx, hr⟩ hcluster
    obtain ⟨y, hy, hybelow⟩ := (p.exists_label_below_iff a).2 hcluster
    have hxy := label_vertex_unique T hx hy
    subst y
    exact (p.parent_reachable_iff_not_below x).1 hr hybelow
  · intro hcluster
    obtain ⟨x, hx⟩ := TreeAdequacy.PhyloTree.exists_vertex_label T a
    refine ⟨x, hx, (p.parent_reachable_iff_not_below x).2 ?_⟩
    intro hxbelow
    apply hcluster
    apply (p.exists_label_below_iff a).1
    exact ⟨x, hx, hxbelow⟩

theorem componentSeparatesAt_parent_iff {T : Tree.PhyloTree α}
    (p : EdgePosition T) (A B : Finset α) :
    ComponentSeparatesAt (TreeAdequacy.PhyloTree.graph T)
        (TreeAdequacy.PhyloTree.label? T) p.parent p.child A B ↔
      (∀ a ∈ A, a ∉ p.cluster) ∧ (∀ b ∈ B, b ∈ p.cluster) := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨x, hx, hr⟩ := hA a ha
      exact (p.exists_label_parent_reachable_iff a).1 ⟨x, hx, hr⟩
    · intro b hb
      by_contra hbc
      obtain ⟨x, hx, hr⟩ := (p.exists_label_parent_reachable_iff b).2 hbc
      exact hB b hb x hx hr
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      exact (p.exists_label_parent_reachable_iff a).2 (hA a ha)
    · intro b hb x hx hr
      have hnot := (p.exists_label_parent_reachable_iff b).1 ⟨x, hx, hr⟩
      exact hnot (hB b hb)

/-- Every edge of the unrooted realization has one of the above rooted
positions, up to orientation. -/
theorem exists_edgePosition_of_adj (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y) :
    ∃ p : EdgePosition T,
      (x = p.parent ∧ y = p.child) ∨ (x = p.child ∧ y = p.parent) := by
  rcases x with (ux | x) <;> rcases y with (uy | y)
  · have hux : ux = () := Subsingleton.elim _ _
    have huy : uy = () := Subsingleton.elim _ _
    subst ux
    subst uy
    exact False.elim (hxy.ne rfl)
  · have hroot := (graph_adj_root_crown T y).mp
      (by simpa [show ux = () from Subsingleton.elim _ _] using hxy)
    refine ⟨.crown, Or.inl ⟨?_, ?_⟩⟩
    · simp [EdgePosition.parent, show ux = () from Subsingleton.elim _ _]
    · rw [hroot]
      rfl
  · have hroot := (graph_adj_crown_root T x).mp
      (by simpa [show uy = () from Subsingleton.elim _ _] using hxy)
    refine ⟨.crown, Or.inr ⟨?_, ?_⟩⟩
    · rw [hroot]
      rfl
    · simp [EdgePosition.parent, show uy = () from Subsingleton.elim _ _]
  · obtain ⟨p, hp | hp⟩ :=
      FullTree.exists_properSubtree_of_adj T.crown
        ((graph_adj_crown_crown T x y).mp hxy)
    · refine ⟨.inside p, Or.inl ⟨?_, ?_⟩⟩
      · rw [hp.1]
        rfl
      · rw [hp.2]
        rfl
    · refine ⟨.inside p, Or.inr ⟨?_, ?_⟩⟩
      · rw [hp.1]
        rfl
      · rw [hp.2]
        rfl

/-- Edge separation in the actual graph is exactly separation by the leaf
cluster of one syntax subtree occurrence. -/
theorem edgeSeparates_iff_exists_position_cluster (T : Tree.PhyloTree α)
    (A B : Finset α) :
    EdgeSeparates (TreeAdequacy.PhyloTree.graph T)
        (TreeAdequacy.PhyloTree.label? T) A B ↔
      ∃ p : EdgePosition T,
        ((∀ a ∈ A, a ∈ p.cluster) ∧ (∀ b ∈ B, b ∉ p.cluster)) ∨
        ((∀ b ∈ B, b ∈ p.cluster) ∧ (∀ a ∈ A, a ∉ p.cluster)) := by
  constructor
  · rintro ⟨u, v, huv, hcomp | hcomp⟩
    · obtain ⟨p, hp | hp⟩ := exists_edgePosition_of_adj T huv
      · rw [hp.1, hp.2] at hcomp
        have h := (componentSeparatesAt_parent_iff p A B).1 hcomp
        exact ⟨p, Or.inr ⟨h.2, h.1⟩⟩
      · rw [hp.1, hp.2] at hcomp
        have h := (componentSeparatesAt_position_iff p A B).1 hcomp
        exact ⟨p, Or.inl h⟩
    · obtain ⟨p, hp | hp⟩ := exists_edgePosition_of_adj T huv
      · rw [hp.1, hp.2] at hcomp
        have h := (componentSeparatesAt_parent_iff p B A).1 hcomp
        exact ⟨p, Or.inl ⟨h.2, h.1⟩⟩
      · rw [hp.1, hp.2] at hcomp
        have h := (componentSeparatesAt_position_iff p B A).1 hcomp
        exact ⟨p, Or.inr h⟩
  · rintro ⟨p, h | h⟩
    · refine ⟨p.child, p.parent, p.adj_parent_child.symm, Or.inl ?_⟩
      exact (componentSeparatesAt_position_iff p A B).2 h
    · refine ⟨p.child, p.parent, p.adj_parent_child.symm, Or.inr ?_⟩
      exact (componentSeparatesAt_position_iff p B A).2 h

/-- Oriented edge clusters are laminar because all edges are oriented away
from the distinguished root leaf. -/
theorem EdgePosition.clusters_laminar {T : Tree.PhyloTree α}
    (p q : EdgePosition T) :
    p.cluster ⊆ q.cluster ∨ q.cluster ⊆ p.cluster ∨
      Disjoint p.cluster q.cluster := by
  cases p with
  | crown =>
      cases q with
      | crown => exact Or.inl (by simp)
      | inside q =>
          refine Or.inr (Or.inl ?_)
          exact Finset.image_mono Subtype.val q.leaves_subset
  | inside p =>
      cases q with
      | crown => exact Or.inl (Finset.image_mono Subtype.val p.leaves_subset)
      | inside q =>
          rcases p.clusters_laminar q T.nodup_leaves with h | h | h
          · exact Or.inl (Finset.image_mono Subtype.val h)
          · exact Or.inr (Or.inl (Finset.image_mono Subtype.val h))
          · refine Or.inr (Or.inr (Finset.disjoint_left.2 ?_))
            intro a hap haq
            simp only [EdgePosition.cluster, Finset.mem_image] at hap haq
            obtain ⟨b, hbp, hba⟩ := hap
            obtain ⟨c, hcq, hca⟩ := haq
            have hbc : b = c := Subtype.ext (hba.trans hca.symm)
            subst c
            exact Finset.disjoint_left.1 h hbp hcq

end PhyloTree

namespace FullTree

open Tree

/-- On a four-leaf full tree, the side selected by `displayedSplit` is the
leaf set below an actual syntax edge.  This is the local quartet fact that
will be transported back through pruning. -/
theorem exists_position_for_displayedSplit [DecidableEq α]
    (t : Tree.FullTree α) (hlen : t.leaves.length = 4) :
    ∃ p : ProperSubtree t,
      t.displayedSplit =
        {p.tree.leaves.toFinset, t.leaves.toFinset \ p.tree.leaves.toFinset} ∧
      p.tree.leaves.length = 2 := by
  obtain ⟨a, b, c, d, hshape⟩ := t.shape_of_leaves_length_eq_four hlen
  rcases hshape with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(ProperSubtree.right (Tree.FullTree.leaf b)
        (Tree.FullTree.fork (Tree.FullTree.leaf c) (Tree.FullTree.leaf d))).inRight,
      by simp [Tree.FullTree.displayedSplit, Tree.FullTree.cherry?,
        Tree.FullTree.leaves], by simp⟩
  · exact ⟨(ProperSubtree.left
        (Tree.FullTree.fork (Tree.FullTree.leaf b) (Tree.FullTree.leaf c))
        (Tree.FullTree.leaf d)).inRight,
      by simp [Tree.FullTree.displayedSplit, Tree.FullTree.cherry?,
        Tree.FullTree.leaves], by simp⟩
  · exact ⟨ProperSubtree.left
        (Tree.FullTree.fork (Tree.FullTree.leaf a) (Tree.FullTree.leaf b))
        (Tree.FullTree.fork (Tree.FullTree.leaf c) (Tree.FullTree.leaf d)),
      by simp [Tree.FullTree.displayedSplit, Tree.FullTree.cherry?,
        Tree.FullTree.leaves], by simp⟩
  · exact ⟨(ProperSubtree.right (Tree.FullTree.leaf a)
        (Tree.FullTree.fork (Tree.FullTree.leaf b) (Tree.FullTree.leaf c))).inLeft,
      by simp [Tree.FullTree.displayedSplit, Tree.FullTree.cherry?,
        Tree.FullTree.leaves], by simp⟩
  · exact ⟨(ProperSubtree.left
        (Tree.FullTree.fork (Tree.FullTree.leaf a) (Tree.FullTree.leaf b))
        (Tree.FullTree.leaf c)).inLeft,
      by simp [Tree.FullTree.displayedSplit, Tree.FullTree.cherry?,
        Tree.FullTree.leaves], by simp⟩

private theorem prune_leaves_toFinset_eq_inter [DecidableEq α]
    {t u : Tree.FullTree α} (S : Finset α)
    (h : t.prune S = some u) :
    u.leaves.toFinset = S ∩ t.leaves.toFinset := by
  rw [Tree.FullTree.prune_leaves t u S h]
  ext a
  simp [Tree.FullTree.restrictList, and_comm]

/-- Every proper subtree position after pruning is induced by a proper
subtree position before pruning, with exactly the expected restricted leaf
cluster.  This explicitly accounts for the unary forks suppressed by
`FullTree.prune`. -/
theorem ProperSubtree.exists_lift_of_prune [DecidableEq α]
    {t u : Tree.FullTree α} (S : Finset α)
    (h : t.prune S = some u) (q : ProperSubtree u) :
    ∃ p : ProperSubtree t,
      q.tree.leaves.toFinset = S ∩ p.tree.leaves.toFinset := by
  induction t generalizing u with
  | leaf a =>
      simp only [Tree.FullTree.prune_leaf] at h
      by_cases ha : a ∈ S
      · simp only [ha, if_true, Option.some.injEq] at h
        subst u
        cases q
      · simp [ha] at h
  | fork l r ihl ihr =>
      simp only [Tree.FullTree.prune] at h
      generalize hl : l.prune S = ol at h
      generalize hr : r.prune S = or at h
      cases ol with
      | none =>
          cases or with
          | none => simp at h
          | some r' =>
              simp only [Option.some.injEq] at h
              subst u
              obtain ⟨p, hp⟩ := ihr hr q
              exact ⟨p.inRight, hp⟩
      | some l' =>
          cases or with
          | none =>
              simp only [Option.some.injEq] at h
              subst u
              obtain ⟨p, hp⟩ := ihl hl q
              exact ⟨p.inLeft, hp⟩
          | some r' =>
              simp only [Option.some.injEq] at h
              subst u
              cases q with
              | left =>
                  exact ⟨.left l r, prune_leaves_toFinset_eq_inter S hl⟩
              | right =>
                  exact ⟨.right l r, prune_leaves_toFinset_eq_inter S hr⟩
              | inLeft q =>
                  obtain ⟨p, hp⟩ := ihl hl q
                  exact ⟨p.inLeft, hp⟩
              | inRight q =>
                  obtain ⟨p, hp⟩ := ihr hr q
                  exact ⟨p.inRight, hp⟩

/-- Forget a leaf relabelling while retaining the same syntactic subtree
occurrence. -/
def ProperSubtree.unmap (f : α → β) :
    {t : Tree.FullTree α} → ProperSubtree (t.map f) → ProperSubtree t
  | .leaf _, p => nomatch p
  | .fork l r, .left _ _ => .left l r
  | .fork l r, .right _ _ => .right l r
  | .fork _ _, .inLeft p => (p.unmap f).inLeft
  | .fork _ _, .inRight p => (p.unmap f).inRight

@[simp] theorem ProperSubtree.tree_unmap (f : α → β)
    {t : Tree.FullTree α} (p : ProperSubtree (t.map f)) :
    (p.unmap f).tree.map f = p.tree := by
  induction t with
  | leaf a => cases p
  | fork l r ihl ihr =>
      cases p with
      | left => rfl
      | right => rfl
      | inLeft p =>
          change (p.unmap f).tree.map f = p.tree
          exact ihl p
      | inRight p =>
          change (p.unmap f).tree.map f = p.tree
          exact ihr p

theorem leaves_map_toFinset [DecidableEq α] [DecidableEq β]
    (f : α → β) (t : Tree.FullTree α) :
    (t.map f).leaves.toFinset = t.leaves.toFinset.image f := by
  ext b
  simp only [Tree.FullTree.leaves_map, List.mem_toFinset,
    List.mem_map, Finset.mem_image]

@[simp] theorem ProperSubtree.image_unmap_leaves
    [DecidableEq α] [DecidableEq β] (f : α → β)
    {t : Tree.FullTree α} (p : ProperSubtree (t.map f)) :
    (p.unmap f).tree.leaves.toFinset.image f = p.tree.leaves.toFinset := by
  have hleaves := congrArg Tree.FullTree.leaves (p.tree_unmap f)
  rw [Tree.FullTree.leaves_map] at hleaves
  ext b
  simp only [Finset.mem_image, List.mem_toFinset]
  rw [← hleaves]
  simp only [List.mem_map]

end FullTree

namespace PhyloTree

variable {α : Type} [Fintype α] [DecidableEq α]

@[simp] theorem restrictedTree_leaves_toFinset (T : Tree.PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    (T.restrictedTree Q hQ).leaves.toFinset = Q := by
  rw [T.restrictedTree_leaves Q hQ]
  ext a
  simp [Tree.FullTree.restrictList, T.mem_referenceLeaves a]

/-- The cherry edge of the suppressed four-leaf restriction lifts to a
genuine edge of the original unrooted graph. -/
theorem exists_position_for_displayedSplitOn (T : Tree.PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    ∃ p : EdgePosition T,
      T.displayedSplitOn Q hQ =
          {Q ∩ p.cluster, Q \ (Q ∩ p.cluster)} ∧
        (Q ∩ p.cluster).card = 2 := by
  let R := T.restrictedTree Q hQ
  obtain ⟨q, hsplit, hlen⟩ :=
    FullTree.exists_position_for_displayedSplit R
      (T.restrictedTree_leaves_length Q hQ)
  have hqnodup : q.tree.leaves.Nodup :=
    q.leaves_nodup (T.restrictedTree_nodup Q hQ)
  have hqcard : q.tree.leaves.toFinset.card = 2 := by
    rw [List.toFinset_card_of_nodup hqnodup]
    exact hlen
  have hdisplay : T.displayedSplitOn Q hQ =
      {q.tree.leaves.toFinset, Q \ q.tree.leaves.toFinset} := by
    simpa [Tree.PhyloTree.displayedSplitOn, R,
      restrictedTree_leaves_toFinset T Q hQ] using hsplit
  obtain ⟨r, hr⟩ := q.exists_lift_of_prune Q
    (T.prune_asFullTree_eq_restrictedTree Q hQ)
  change FullTree.ProperSubtree
    (.fork (.leaf T.root) (T.crown.map Subtype.val)) at r
  cases r with
  | left =>
      have hsub : q.tree.leaves.toFinset ⊆ {T.root} := by
        intro a ha
        rw [hr] at ha
        have haroot := (Finset.mem_inter.mp ha).2
        change a ∈ (Tree.FullTree.leaf T.root).leaves.toFinset at haroot
        simpa using haroot
      have hcardle := Finset.card_le_card hsub
      simp at hcardle
      omega
  | right =>
      let p : EdgePosition T := .crown
      have hr' : q.tree.leaves.toFinset = Q ∩ p.cluster := by
        apply hr.trans
        congr 1
        change (T.crown.map Subtype.val).leaves.toFinset =
          T.crown.leaves.toFinset.image Subtype.val
        exact FullTree.leaves_map_toFinset Subtype.val T.crown
      refine ⟨p, ?_, ?_⟩
      · rw [hdisplay, hr']
      · rw [← hr']
        exact hqcard
  | inLeft r => cases r
  | inRight r =>
      let p : EdgePosition T := .inside (r.unmap Subtype.val)
      have hr' : q.tree.leaves.toFinset = Q ∩ p.cluster := by
        apply hr.trans
        congr 1
        change r.tree.leaves.toFinset =
          (r.unmap Subtype.val).tree.leaves.toFinset.image Subtype.val
        exact (r.image_unmap_leaves Subtype.val).symm
      refine ⟨p, ?_, ?_⟩
      · rw [hdisplay, hr']
      · rw [← hr']
        exact hqcard

/-- A split is displayed by the syntax tree's graph when it is a genuine
split of `Q` and two distinct sides lie in the two components obtained by
deleting some edge. -/
def GraphDisplaysSplit (T : Tree.PhyloTree α) (Q : Finset α)
    (s : Circular.QuartetSplit α) : Prop :=
  Circular.IsQuartetSplit Q s ∧
    ∃ A ∈ s, ∃ B ∈ s, A ≠ B ∧
      EdgeSeparates (TreeAdequacy.PhyloTree.graph T)
        (TreeAdequacy.PhyloTree.label? T) A B

omit [Fintype α] in
private theorem side_eq_inter_of_union {A B Q C : Finset α}
    (hunion : A ∪ B = Q)
    (hin : ∀ a ∈ A, a ∈ C) (hout : ∀ b ∈ B, b ∉ C) :
    A = Q ∩ C := by
  ext x
  constructor
  · intro hxA
    apply Finset.mem_inter.mpr
    constructor
    · rw [← hunion]
      exact Finset.mem_union_left B hxA
    · exact hin x hxA
  · intro hx
    have hx' := Finset.mem_inter.mp hx
    have hxUnion : x ∈ A ∪ B := by
      rw [hunion]
      exact hx'.1
    rcases Finset.mem_union.mp hxUnion with hxA | hxB
    · exact hxA
    · exact False.elim (hout x hxB hx'.2)

omit [Fintype α] in
private theorem inter_laminar {Q C D : Finset α}
    (h : C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) :
    Q ∩ C ⊆ Q ∩ D ∨ Q ∩ D ⊆ Q ∩ C ∨
      Disjoint (Q ∩ C) (Q ∩ D) := by
  rcases h with hCD | hDC | hdisj
  · exact Or.inl (Finset.inter_subset_inter (by rfl) hCD)
  · exact Or.inr (Or.inl (Finset.inter_subset_inter (by rfl) hDC))
  · exact Or.inr (Or.inr
      (hdisj.mono Finset.inter_subset_right Finset.inter_subset_right))

private theorem graphSplit_eq_displayed_of_position
    (T : Tree.PhyloTree α) (Q : Finset α) (hQ : Q.card = 4)
    (s : Circular.QuartetSplit α) (hs : Circular.IsQuartetSplit Q s)
    (A B : Finset α) (hA : A ∈ s) (hB : B ∈ s) (hne : A ≠ B)
    (p : EdgePosition T)
    (hin : ∀ a ∈ A, a ∈ p.cluster)
    (hout : ∀ b ∈ B, b ∉ p.cluster) :
    s = T.displayedSplitOn Q hQ := by
  have hunion := isQuartetSplit_union_sides hs hA hB hne
  have hAeq : A = Q ∩ p.cluster :=
    side_eq_inter_of_union hunion hin hout
  have hBcomp := isQuartetSplit_other_eq_sdiff hs hA hB hne
  have hspair := isQuartetSplit_eq_pair_of_mem hs hA hB hne
  obtain ⟨q, hdisplay, hqcard⟩ :=
    exists_position_for_displayedSplitOn T Q hQ
  have hAcard : A.card = 2 := isQuartetSplit_side_card hs hA
  have hAQ : A ⊆ Q := isQuartetSplit_side_subset hs hA
  have hqQ : Q ∩ q.cluster ⊆ Q := Finset.inter_subset_left
  have hlam := inter_laminar (Q := Q) (p.clusters_laminar q)
  have hpairs : ({A, Q \ A} : Circular.QuartetSplit α) =
      {Q ∩ q.cluster, Q \ (Q ∩ q.cluster)} := by
    apply pair_sdiff_eq_of_laminar Q A (Q ∩ q.cluster) hQ hAQ hqQ
      hAcard hqcard
    simpa [hAeq] using hlam
  calc
    s = {A, B} := hspair
    _ = {A, Q \ A} := by rw [hBcomp]
    _ = {Q ∩ q.cluster, Q \ (Q ∩ q.cluster)} := hpairs
    _ = T.displayedSplitOn Q hQ := hdisplay.symm

/-- The direct delete-edge definition selects exactly the recursive
restriction-and-suppression quartet topology. -/
theorem graphDisplaysSplit_iff_eq_displayedSplitOn
    (T : Tree.PhyloTree α) (Q : Finset α) (hQ : Q.card = 4)
    (s : Circular.QuartetSplit α) :
    GraphDisplaysSplit T Q s ↔ s = T.displayedSplitOn Q hQ := by
  constructor
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    obtain ⟨p, hp | hp⟩ :=
      (edgeSeparates_iff_exists_position_cluster T A B).mp hsep
    · exact graphSplit_eq_displayed_of_position T Q hQ s hs A B hA hB hne
        p hp.1 hp.2
    · exact graphSplit_eq_displayed_of_position T Q hQ s hs B A hB hA
        hne.symm p hp.1 hp.2
  · intro hs
    subst s
    obtain ⟨p, hdisplay, hpCard⟩ :=
      exists_position_for_displayedSplitOn T Q hQ
    let A := Q ∩ p.cluster
    let B := Q \ A
    have hAQ : A ⊆ Q := Finset.inter_subset_left
    have hvalid : Circular.IsQuartetSplit Q
        (T.displayedSplitOn Q hQ) := by
      rw [hdisplay]
      exact pair_sdiff_isQuartetSplit Q A hQ hAQ hpCard
    have hne : A ≠ B := by
      intro heq
      have hdisj : Disjoint A B := by
        exact Finset.disjoint_sdiff
      rw [← heq] at hdisj
      have hempty : A = ∅ := disjoint_self.mp hdisj
      have hAcard : A.card = 2 := hpCard
      rw [hempty] at hAcard
      simp at hAcard
    refine ⟨hvalid, A, ?_, B, ?_, hne, ?_⟩
    · rw [hdisplay]
      change A ∈ ({A, B} : Circular.QuartetSplit α)
      simp
    · rw [hdisplay]
      change B ∈ ({A, B} : Circular.QuartetSplit α)
      simp
    · apply (edgeSeparates_iff_exists_position_cluster T A B).mpr
      refine ⟨p, Or.inl ⟨?_, ?_⟩⟩
      · intro a ha
        exact (Finset.mem_inter.mp ha).2
      · intro b hb
        have hb' := Finset.mem_sdiff.mp hb
        intro hbcluster
        exact hb'.2 (Finset.mem_inter.mpr ⟨hb'.1, hbcluster⟩)

/-- The unique graph-theoretic quartet split, chosen from the direct
delete-edge predicate. -/
noncomputable def graphQuartetSplit (T : Tree.PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) : Circular.QuartetSplit α :=
  Classical.choose
    (show ∃ s, GraphDisplaysSplit T Q s from
      ⟨T.displayedSplitOn Q hQ,
        (graphDisplaysSplit_iff_eq_displayedSplitOn T Q hQ _).mpr rfl⟩)

theorem graphQuartetSplit_graphDisplaysSplit (T : Tree.PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    GraphDisplaysSplit T Q (graphQuartetSplit T Q hQ) :=
  Classical.choose_spec
    (show ∃ s, GraphDisplaysSplit T Q s from
      ⟨T.displayedSplitOn Q hQ,
        (graphDisplaysSplit_iff_eq_displayedSplitOn T Q hQ _).mpr rfl⟩)

@[simp] theorem graphQuartetSplit_eq_displayedSplitOn
    (T : Tree.PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    graphQuartetSplit T Q hQ = T.displayedSplitOn Q hQ :=
  (graphDisplaysSplit_iff_eq_displayedSplitOn T Q hQ _).mp
    (graphQuartetSplit_graphDisplaysSplit T Q hQ)

end PhyloTree

end GraphQuartet
end QuartetDistance
