import QuartetDistance.Tree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Graph-theoretic adequacy of the tree syntax

The counting proof represents an unrooted binary phylogenetic tree by cutting
it at one labelled leaf.  This file verifies, independently of that proof,
that every such syntax tree has the usual graph-theoretic realization: a
finite connected acyclic simple graph, with the labels precisely on vertices
of degree one and every other vertex of degree three.
-/

namespace QuartetDistance
namespace TreeAdequacy

open SimpleGraph

/- A finite ambient vertex type makes every neighbor set finite.  We keep
this instance local to this adequacy module to avoid imposing decidability
choices on the combinatorial development. -/
noncomputable local instance finiteNeighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) := Fintype.ofFinite _

/-! ## Joining two finite trees by one edge -/

private theorem card_edgeSet_sum
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    Nat.card (G.sum H).edgeSet = Nat.card G.edgeSet + Nat.card H.edgeSet := by
  classical
  rw [Nat.card_congr (SimpleGraph.edgeSetSumEquiv (G := G) (H := H))]
  exact Nat.card_sum

/-- Connecting two finite trees by one edge again gives a tree. -/
theorem isTree_sum_sup_edge
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W)
    (hG : G.IsTree) (hH : H.IsTree) :
    (G.sum H ⊔ SimpleGraph.edge (.inl v) (.inr w)).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact hG.connected.sum_sup_edge hH.connected
  · have hadd : Nat.card
        (G.sum H ⊔ SimpleGraph.edge (.inl v) (.inr w)).edgeSet =
        Nat.card (G.sum H).edgeSet + 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ← SimpleGraph.edgeFinset_card, ← SimpleGraph.edgeFinset_card]
      apply SimpleGraph.card_edgeFinset_sup_edge <;> simp
    have hGc := (SimpleGraph.isTree_iff_connected_and_card (G := G)).mp hG |>.2
    have hHc := (SimpleGraph.isTree_iff_connected_and_card (G := H)).mp hH |>.2
    rw [hadd, card_edgeSet_sum, Nat.card_sum]
    omega

/-! The corresponding local degree bookkeeping. -/

/-- Degree expressed without carrying a particular `Fintype` witness. -/
private noncomputable def graphDegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  Nat.card (G.neighborSet v)

private theorem degree_eq_natCard_neighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    G.degree v = Nat.card (G.neighborSet v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Nat.card_eq_fintype_card]

private theorem degree_sum_inl
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) :
    graphDegree (G.sum H) (.inl v) = graphDegree G v := by
  rw [graphDegree, graphDegree, SimpleGraph.neighborSet_sum_inl]
  exact Nat.card_image_of_injective Sum.inl_injective _

private theorem degree_sum_inr
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (w : W) :
    graphDegree (G.sum H) (.inr w) = graphDegree H w := by
  rw [graphDegree, graphDegree, SimpleGraph.neighborSet_sum_inr]
  exact Nat.card_image_of_injective Sum.inr_injective _

private theorem degree_sup_edge_left
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) :
    graphDegree (G ⊔ SimpleGraph.edge s t) s = graphDegree G s + 1 := by
  have hneighbors : (G ⊔ SimpleGraph.edge s t).neighborSet s =
      insert t (G.neighborSet s) := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, Set.mem_insert_iff]
    constructor <;> aesop
  rw [graphDegree, graphDegree, hneighbors]
  exact Set.ncard_insert_of_notMem hnadj

private theorem degree_sup_edge_right
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : V)
    (hne : s ≠ t) (hnadj : ¬ G.Adj s t) :
    graphDegree (G ⊔ SimpleGraph.edge s t) t = graphDegree G t + 1 := by
  rw [SimpleGraph.edge_comm]
  exact degree_sup_edge_left G t s hne.symm (by simpa [SimpleGraph.adj_comm] using hnadj)

private theorem degree_sup_edge_of_ne
    {V : Type*} [Fintype V] (G : SimpleGraph V) (s t x : V)
    (hxs : x ≠ s) (hxt : x ≠ t) :
    graphDegree (G ⊔ SimpleGraph.edge s t) x = graphDegree G x := by
  have hneighbors : (G ⊔ SimpleGraph.edge s t).neighborSet x =
      G.neighborSet x := by
    ext y
    simp [SimpleGraph.edge_adj, hxs, hxt]
  rw [graphDegree, graphDegree, hneighbors]

/-! ## The graph carried by a full binary tree -/

namespace FullTree

/-- Vertices of the geometric realization, including forks. -/
@[reducible] def Vertex : Tree.FullTree α → Type
  | .leaf _ => Unit
  | .fork l r => (Unit ⊕ Vertex l) ⊕ Vertex r

@[reducible] private def fintypeVertex : (t : Tree.FullTree α) → Fintype (Vertex t)
  | .leaf _ => by
      change Fintype Unit
      infer_instance
  | .fork l r =>
      letI := fintypeVertex l
      letI := fintypeVertex r
      show Fintype ((Unit ⊕ Vertex l) ⊕ Vertex r) from inferInstance

instance instFintypeVertex (t : Tree.FullTree α) : Fintype (Vertex t) :=
  fintypeVertex t

private def decidableEqVertex : (t : Tree.FullTree α) → DecidableEq (Vertex t)
  | .leaf _ => by
      change DecidableEq Unit
      infer_instance
  | .fork l r =>
      letI := decidableEqVertex l
      letI := decidableEqVertex r
      show DecidableEq ((Unit ⊕ Vertex l) ⊕ Vertex r) from inferInstance

instance instDecidableEqVertex (t : Tree.FullTree α) : DecidableEq (Vertex t) :=
  decidableEqVertex t

/-- The root vertex of a full tree. -/
def rootVertex : (t : Tree.FullTree α) → Vertex t
  | .leaf _ => ()
  | .fork _ _ => .inl (.inl ())

/-- The ordinary simple graph underlying a full tree. -/
def graph : (t : Tree.FullTree α) → SimpleGraph (Vertex t)
  | .leaf _ => ⊥
  | .fork l r =>
      let leftJoined :=
        ((⊥ : SimpleGraph Unit).sum (graph l) ⊔
          SimpleGraph.edge (.inl ()) (.inr (rootVertex l)))
      leftJoined.sum (graph r) ⊔
        SimpleGraph.edge (.inl (.inl ())) (.inr (rootVertex r))

/-- The leaf label carried by a vertex; fork vertices carry no label. -/
def label? : (t : Tree.FullTree α) → Vertex t → Option α
  | .leaf a, _ => some a
  | .fork _ _, .inl (.inl _) => none
  | .fork l _, .inl (.inr v) => label? l v
  | .fork _ r, .inr v => label? r v

/-- Every full binary syntax tree realizes to a finite graph-theoretic tree. -/
theorem graph_isTree (t : Tree.FullTree α) : (graph t).IsTree := by
  induction t with
  | leaf a =>
      change (⊥ : SimpleGraph Unit).IsTree
      exact SimpleGraph.IsTree.of_subsingleton
  | fork l r ihl ihr =>
      simp only [graph]
      exact isTree_sum_sup_edge _ _ _ _
        (isTree_sum_sup_edge _ _ _ _
          (SimpleGraph.IsTree.of_subsingleton (G := (⊥ : SimpleGraph Unit))) ihl)
        ihr

private theorem degree_root_fork (l r : Tree.FullTree α) :
    graphDegree (graph (.fork l r)) (rootVertex (.fork l r)) = 2 := by
  simp only [graph, rootVertex]
  rw [degree_sup_edge_left, degree_sum_inl, degree_sup_edge_left,
    degree_sum_inl]
  · have hzero : graphDegree (⊥ : SimpleGraph Unit) () = 0 := by
      simp [graphDegree]
    omega
  all_goals simp

private theorem degree_left_fork (l r : Tree.FullTree α) (v : Vertex l) :
    graphDegree (graph (.fork l r)) (.inl (.inr v)) =
      graphDegree (graph l) v + if v = rootVertex l then 1 else 0 := by
  simp only [graph]
  rw [degree_sup_edge_of_ne, degree_sum_inl]
  · by_cases hv : v = rootVertex l
    · subst v
      rw [if_pos rfl, degree_sup_edge_right, degree_sum_inr]
      all_goals simp
    · rw [if_neg hv, degree_sup_edge_of_ne, degree_sum_inr]
      all_goals simp [hv]
  all_goals simp

private theorem degree_right_fork (l r : Tree.FullTree α) (v : Vertex r) :
    graphDegree (graph (.fork l r)) (.inr v) =
      graphDegree (graph r) v + if v = rootVertex r then 1 else 0 := by
  simp only [graph]
  by_cases hv : v = rootVertex r
  · subst v
    rw [if_pos rfl, degree_sup_edge_right, degree_sum_inr]
    all_goals simp
  · rw [if_neg hv, degree_sup_edge_of_ne, degree_sum_inr]
    all_goals simp [hv]

/-- Supplying the one parent edge missing at the root gives degree one at
labelled leaves and degree three at forks. -/
theorem augmented_degree (t : Tree.FullTree α) (v : Vertex t) :
    graphDegree (graph t) v + (if v = rootVertex t then 1 else 0) =
      if (label? t v).isSome then 1 else 3 := by
  induction t with
  | leaf a =>
      have hv : v = () := Subsingleton.elim _ _
      subst v
      simp [graphDegree, graph, rootVertex, label?]
  | fork l r ihl ihr =>
      rcases v with (u | v)
      · rcases u with (u | v)
        · have hu : u = () := Subsingleton.elim _ _
          subst u
          rw [if_pos (by rfl)]
          rw [if_neg (by simp [label?])]
          have hd : graphDegree (graph (.fork l r)) (.inl (.inl ())) = 2 := by
            simpa only [rootVertex] using degree_root_fork l r
          omega
        · have hne : (Sum.inl (Sum.inr v) : Vertex (.fork l r)) ≠
              rootVertex (.fork l r) := by simp [rootVertex]
          rw [if_neg hne, degree_left_fork]
          change graphDegree (graph l) v +
              (if v = rootVertex l then 1 else 0) =
            if (label? l v).isSome then 1 else 3
          exact ihl v
      · have hne : (Sum.inr v : Vertex (.fork l r)) ≠
            rootVertex (.fork l r) := by simp [rootVertex]
        rw [if_neg hne, degree_right_fork]
        change graphDegree (graph r) v +
            (if v = rootVertex r then 1 else 0) =
          if (label? r v).isSome then 1 else 3
        exact ihr v

/-- Every syntactic leaf occurrence supplies its label to a graph vertex. -/
theorem exists_vertex_label_of_mem (t : Tree.FullTree α) {a : α}
    (ha : a ∈ t.leaves) : ∃ v : Vertex t, label? t v = some a := by
  induction t with
  | leaf b =>
      simp only [Tree.FullTree.leaves_leaf, List.mem_singleton] at ha
      subst a
      exact ⟨(), rfl⟩
  | fork l r ihl ihr =>
      rw [Tree.FullTree.leaves_fork, List.mem_append] at ha
      rcases ha with ha | ha
      · obtain ⟨v, hv⟩ := ihl ha
        exact ⟨.inl (.inr v), hv⟩
      · obtain ⟨v, hv⟩ := ihr ha
        exact ⟨.inr v, hv⟩

end FullTree

/-! ## The standard unrooted realization -/

namespace PhyloTree

variable [Fintype α] [DecidableEq α]

/-- Vertices of the unrooted realization: the distinguished leaf and all
vertices of the cut-open crown. -/
abbrev Vertex (T : Tree.PhyloTree α) := Unit ⊕ FullTree.Vertex T.crown

/-- The standard unrooted simple graph obtained by attaching the
distinguished leaf back to the crown root. -/
def graph (T : Tree.PhyloTree α) : SimpleGraph (Vertex T) :=
  (⊥ : SimpleGraph Unit).sum (FullTree.graph T.crown) ⊔
    SimpleGraph.edge (.inl ()) (.inr (FullTree.rootVertex T.crown))

/-- Labels live exactly on the syntax leaves. -/
def label? (T : Tree.PhyloTree α) : Vertex T → Option α
  | .inl _ => some T.root
  | .inr v => (FullTree.label? T.crown v).map Subtype.val

/-- The realization really is a connected acyclic simple graph. -/
theorem graph_isTree (T : Tree.PhyloTree α) : (graph T).IsTree := by
  simpa [graph] using isTree_sum_sup_edge
    (⊥ : SimpleGraph Unit) (FullTree.graph T.crown) ()
      (FullTree.rootVertex T.crown)
    SimpleGraph.IsTree.of_subsingleton (FullTree.graph_isTree T.crown)

private theorem graphDegree_profile (T : Tree.PhyloTree α) (v : Vertex T) :
    graphDegree (graph T) v = if (label? T v).isSome then 1 else 3 := by
  rcases v with (u | v)
  · have hu : u = () := Subsingleton.elim _ _
    subst u
    have hd : graphDegree (graph T) (.inl ()) =
        graphDegree ((⊥ : SimpleGraph Unit).sum (FullTree.graph T.crown)) (.inl ()) + 1 := by
      apply degree_sup_edge_left <;> simp
    rw [hd, degree_sum_inl]
    have hzero : graphDegree (⊥ : SimpleGraph Unit) () = 0 := by
      simp [graphDegree]
    simp [hzero, label?]
  · have hd : graphDegree (graph T) (.inr v) =
        graphDegree (FullTree.graph T.crown) v +
          if v = FullTree.rootVertex T.crown then 1 else 0 := by
      by_cases hv : v = FullTree.rootVertex T.crown
      · subst v
        rw [if_pos rfl]
        simpa [graph, degree_sum_inr] using
          degree_sup_edge_right
            ((⊥ : SimpleGraph Unit).sum (FullTree.graph T.crown))
            (.inl ()) (.inr (FullTree.rootVertex T.crown)) (by simp) (by simp)
      · rw [if_neg hv]
        calc
          graphDegree (graph T) (.inr v) =
              graphDegree ((⊥ : SimpleGraph Unit).sum (FullTree.graph T.crown)) (.inr v) := by
            apply degree_sup_edge_of_ne <;> simp [hv]
          _ = graphDegree (FullTree.graph T.crown) v :=
            degree_sum_inr _ _ _
    rw [hd]
    simpa [label?] using FullTree.augmented_degree T.crown v

/-- Graph-theoretic degree profile: labelled vertices have degree one and
every unlabelled (internal) vertex has degree three. -/
theorem degree_profile (T : Tree.PhyloTree α) (v : Vertex T) :
    (graph T).degree v = if (label? T v).isSome then 1 else 3 := by
  rw [degree_eq_natCard_neighborSet]
  exact graphDegree_profile T v

theorem degree_eq_one_iff (T : Tree.PhyloTree α) (v : Vertex T) :
    (graph T).degree v = 1 ↔ (label? T v).isSome := by
  rw [degree_profile]
  cases h : label? T v <;> simp

theorem degree_eq_three_iff (T : Tree.PhyloTree α) (v : Vertex T) :
    (graph T).degree v = 3 ↔ ¬ (label? T v).isSome := by
  rw [degree_profile]
  cases h : label? T v <;> simp

/-- Every taxon labels a degree-one vertex of the realization. -/
theorem exists_vertex_label (T : Tree.PhyloTree α) (a : α) :
    ∃ v : Vertex T, label? T v = some a := by
  by_cases ha : a = T.root
  · subst a
    exact ⟨.inl (), rfl⟩
  · obtain ⟨v, hv⟩ := FullTree.exists_vertex_label_of_mem T.crown
      (T.exhaustive ⟨a, ha⟩)
    refine ⟨.inr v, ?_⟩
    simp [label?, hv]

/-- In particular, each taxon occurs on an actual graph-theoretic leaf. -/
theorem exists_degree_one_vertex (T : Tree.PhyloTree α) (a : α) :
    ∃ v : Vertex T, (graph T).degree v = 1 ∧ label? T v = some a := by
  obtain ⟨v, hv⟩ := exists_vertex_label T a
  refine ⟨v, ?_, hv⟩
  rw [degree_eq_one_iff]
  simp [hv]

end PhyloTree

end TreeAdequacy
end QuartetDistance
