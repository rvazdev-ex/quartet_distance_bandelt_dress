import QuartetDistance.GraphModel
import QuartetDistance.GraphQuartet
import QuartetDistance.Maximum
import QuartetDistance.Upper

/-!
# The conventional graph domain for quartet distance

This file packages finite graph-theoretic binary phylogenetic trees whose
vertex types may have different cardinalities.  Each vertex type is put in
the canonical form `Fin m`; this avoids existential typeclass packaging while
still representing every finite graph up to a label-preserving isomorphism.

It then proves invariance of edge separation under label-preserving graph
isomorphisms, uniqueness of the directly displayed quartet topology, equality
of graph and syntax quartet distances under both encodings, and exact equality
of their maxima for `n ≥ 4`.
-/

namespace QuartetDistance

open SimpleGraph

noncomputable local instance finiteNeighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) :=
  Fintype.ofFinite _

/-- A conventional finite binary phylogenetic tree with a canonical finite
vertex type.  Different values of this type may have different vertex counts. -/
structure CanonicalBinaryPhyloGraph (α : Type*) [Fintype α] where
  vertexCount : ℕ
  tree : GraphModel.BinaryPhyloGraph α (Fin vertexCount)

namespace GraphModel.BinaryPhyloGraph

variable {α V : Type*} [Fintype α] [Fintype V] [DecidableEq V]

/-- The canonical graph isomorphism from a finite vertex type to `Fin` of its
cardinality. -/
noncomputable def canonicalIso (P : BinaryPhyloGraph α V) :
    P.G ≃g P.G.overFin rfl :=
  P.G.overFinIso rfl

/-- Put an independently defined finite binary phylogenetic graph on the
canonical vertex type `Fin (Fintype.card V)`. -/
noncomputable def canonicalize (P : BinaryPhyloGraph α V) :
    CanonicalBinaryPhyloGraph α where
  vertexCount := Fintype.card V
  tree :=
    { G := P.G.overFin rfl
      isTree := (P.canonicalIso.isTree_iff).mp P.isTree
      leafEquiv := P.leafEquiv.trans <|
        P.canonicalIso.toEquiv.subtypeEquiv fun v => by
          change P.G.degree v = 1 ↔
            (P.G.overFin rfl).degree (P.canonicalIso v) = 1
          rw [P.canonicalIso.degree_eq]
      internal_degree := by
        intro w hw
        obtain ⟨v, rfl⟩ := P.canonicalIso.surjective w
        rw [P.canonicalIso.degree_eq] at hw ⊢
        exact P.internal_degree v hw }

omit [DecidableEq V] in
@[simp] theorem canonicalize_vertexCount (P : BinaryPhyloGraph α V) :
    P.canonicalize.vertexCount = Fintype.card V :=
  rfl

omit [DecidableEq V] in
@[simp] theorem canonicalize_graph (P : BinaryPhyloGraph α V) :
    P.canonicalize.tree.G = P.G.overFin rfl :=
  rfl

omit [DecidableEq V] in
/-- Canonicalization preserves each labelled leaf, not merely the underlying
unlabelled graph. -/
@[simp] theorem canonicalIso_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.canonicalIso (P.leafVertex a) = P.canonicalize.tree.leafVertex a :=
  rfl

/-- The partial labelling carried by the degree-one vertices of a conventional
phylogenetic graph. -/
noncomputable def leafLabel? (P : BinaryPhyloGraph α V) (v : V) : Option α :=
  if hv : P.G.degree v = 1 then some (P.labelOfLeaf v hv) else none

omit [Fintype α] in
@[simp] theorem leafLabel?_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.leafLabel? (P.leafVertex a) = some a := by
  simp [leafLabel?, P.degree_leafVertex]

omit [Fintype α] in
theorem leafLabel?_eq_some_iff (P : BinaryPhyloGraph α V) (v : V) (a : α) :
    P.leafLabel? v = some a ↔ v = P.leafVertex a := by
  classical
  unfold leafLabel?
  split_ifs with hv
  · constructor
    · intro h
      have ha : P.labelOfLeaf v hv = a := Option.some.inj h
      rw [← ha, P.leafVertex_labelOfLeaf]
    · intro h
      subst v
      simp
  · constructor
    · intro h
      cases h
    · intro h
      subst v
      exact hv (P.degree_leafVertex a)

/-- The canonical graph isomorphism also preserves the induced partial leaf
labelling pointwise. -/
@[simp] theorem leafLabel?_canonicalIso (P : BinaryPhyloGraph α V) (v : V) :
    P.canonicalize.tree.leafLabel? (P.canonicalIso v) = P.leafLabel? v := by
  classical
  apply Option.ext
  intro a
  simp only [leafLabel?_eq_some_iff]
  rw [← P.canonicalIso_leafVertex]
  exact P.canonicalIso.injective.eq_iff

end GraphModel.BinaryPhyloGraph

namespace Tree.PhyloTree

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The degree-one labelling recovered from the graph realization is exactly
the original syntax labelling at every vertex. -/
theorem toBinaryPhyloGraph_leafLabel? (T : Tree.PhyloTree α)
    (v : TreeAdequacy.PhyloTree.Vertex T) :
    T.toBinaryPhyloGraph.leafLabel? v =
      TreeAdequacy.PhyloTree.label? T v := by
  apply Option.ext
  intro a
  rw [GraphModel.BinaryPhyloGraph.leafLabel?_eq_some_iff,
    T.toBinaryPhyloGraph_leafVertex]
  constructor
  · rintro rfl
    exact T.label_labelledVertex a
  · intro h
    exact T.label_unique h (T.label_labelledVertex a)

/-- The canonical conventional graph associated with a syntax tree. -/
noncomputable def toCanonicalBinaryPhyloGraph (T : Tree.PhyloTree α) :
    CanonicalBinaryPhyloGraph α :=
  T.toBinaryPhyloGraph.canonicalize

/-- The syntax realization is label-preservingly isomorphic to its canonical
`Fin`-vertex presentation. -/
noncomputable def toCanonicalGraphIso (T : Tree.PhyloTree α) :
    TreeAdequacy.PhyloTree.graph T ≃g T.toCanonicalBinaryPhyloGraph.tree.G :=
  T.toBinaryPhyloGraph.canonicalIso

theorem toCanonicalGraphIso_leafLabel? (T : Tree.PhyloTree α)
    (v : TreeAdequacy.PhyloTree.Vertex T) :
    T.toCanonicalBinaryPhyloGraph.tree.leafLabel?
        (T.toCanonicalGraphIso v) =
      TreeAdequacy.PhyloTree.label? T v := by
  calc
    T.toCanonicalBinaryPhyloGraph.tree.leafLabel?
        (T.toCanonicalGraphIso v) =
        T.toBinaryPhyloGraph.leafLabel? v :=
      GraphModel.BinaryPhyloGraph.leafLabel?_canonicalIso
        T.toBinaryPhyloGraph v
    _ = TreeAdequacy.PhyloTree.label? T v :=
      T.toBinaryPhyloGraph_leafLabel? v

end Tree.PhyloTree

namespace CanonicalBinaryPhyloGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Encode a canonical conventional graph after choosing the leaf at which
to cut it open. -/
noncomputable def encodeAt (P : CanonicalBinaryPhyloGraph α) (rootLabel : α) :
    Tree.PhyloTree α :=
  P.tree.encode rootLabel

/-- The encoding of a canonical conventional graph realizes to the original
graph on `Fin P.vertexCount`. -/
noncomputable def encodeGraphIsoAt (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α) :
    TreeAdequacy.PhyloTree.graph (P.encodeAt rootLabel) ≃g P.tree.G :=
  P.tree.encodeGraphIso rootLabel

@[simp] theorem encodeGraphIsoAt_label (P : CanonicalBinaryPhyloGraph α)
    (rootLabel a : α)
    (x : TreeAdequacy.PhyloTree.Vertex (P.encodeAt rootLabel)) :
    P.tree.leafLabel? (P.encodeGraphIsoAt rootLabel x) = some a ↔
      TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel) x = some a := by
  rw [GraphModel.BinaryPhyloGraph.leafLabel?_eq_some_iff]
  exact (P.tree.encodeGraphIso_label_iff rootLabel a x).symm

/-- The graph isomorphism from the syntax encoding preserves the entire
partial taxon labelling. -/
theorem encodeGraphIsoAt_leafLabel? (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α)
    (x : TreeAdequacy.PhyloTree.Vertex (P.encodeAt rootLabel)) :
    P.tree.leafLabel? (P.encodeGraphIsoAt rootLabel x) =
      TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel) x := by
  apply Option.ext
  intro a
  exact P.encodeGraphIsoAt_label rootLabel a x

/-- A split is displayed by a conventional graph when it is a well-formed
split of `Q` and some two distinct sides are separated by a graph edge. -/
def GraphDisplaysSplit (P : CanonicalBinaryPhyloGraph α)
    (Q : Finset α) (s : Circular.QuartetSplit α) : Prop :=
  Circular.IsQuartetSplit Q s ∧
    ∃ A ∈ s, ∃ B ∈ s, A ≠ B ∧
      GraphQuartet.EdgeSeparates P.tree.G P.tree.leafLabel? A B

/-- Direct graph-theoretic display of one of the three channels on a labelled
quartet. -/
def GraphDisplaysTopology (P : CanonicalBinaryPhyloGraph (Fin n))
    (q : Upper.Quartet n) (i : Fin 3) : Prop :=
  P.GraphDisplaysSplit q.1 (Upper.splitOfTopology q i)

/-- Choose a root label canonically from the quartet itself.  This avoids any
global nonemptiness assumption and is available exactly where a displayed
quartet is being queried. -/
def quartetRoot (q : Upper.Quartet n) : Fin n :=
  Upper.quartetEmbedding q 0

/-- The syntax encoding rooted at one of the four labels under consideration. -/
noncomputable def encodeForQuartet
    (P : CanonicalBinaryPhyloGraph (Fin n)) (q : Upper.Quartet n) :
    Tree.PhyloTree (Fin n) :=
  P.encodeAt (quartetRoot q)

end CanonicalBinaryPhyloGraph

namespace GraphQuartet

variable {α V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Deleting corresponding edges commutes with a graph isomorphism. -/
def deleteEdgeIso (e : G ≃g H) (u v : V) :
    G.deleteEdges {s(u, v)} ≃g
      H.deleteEdges {s(e u, e v)} where
  __ := e.toEquiv
  map_rel_iff' := by
    intro x y
    simp only [deleteEdges_adj, Set.mem_singleton_iff]
    change (H.Adj (e x) (e y) ∧ ¬s(e x, e y) = s(e u, e v)) ↔
      (G.Adj x y ∧ ¬s(x, y) = s(u, v))
    rw [e.map_rel_iff]
    constructor
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, fun heq => hne ?_⟩
      change Sym2.map e s(x, y) = Sym2.map e s(u, v)
      exact congrArg (Sym2.map e) heq
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, fun heq => hne ?_⟩
      apply Sym2.map.injective e.injective
      simpa only [Sym2.map_mk] using heq

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem deleteEdgeIso_apply (e : G ≃g H) (u v x : V) :
    deleteEdgeIso e u v x = e x :=
  rfl

omit [DecidableEq V] [DecidableEq W] in
/-- Reachability after deleting an edge is invariant under a graph
isomorphism. -/
theorem deleteEdge_reachable_iff (e : G ≃g H) (u v x y : V) :
    (H.deleteEdges {s(e u, e v)}).Reachable (e x) (e y) ↔
      (G.deleteEdges {s(u, v)}).Reachable x y :=
  SimpleGraph.Iso.reachable_iff (φ := deleteEdgeIso e u v)

/-- `ComponentSeparatesAt` is invariant under a pointwise
label-preserving graph isomorphism. -/
theorem componentSeparatesAt_iff_of_iso
    (e : G ≃g H) (labelV : V → Option α) (labelW : W → Option α)
    (hlabel : ∀ x, labelW (e x) = labelV x)
    (u v : V) (A B : Finset α) :
    ComponentSeparatesAt H labelW (e u) (e v) A B ↔
      ComponentSeparatesAt G labelV u v A B := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨y, hy, hry⟩ := hA a ha
      let x := e.symm y
      refine ⟨x, ?_, ?_⟩
      · calc
          labelV x = labelW (e x) := (hlabel x).symm
          _ = labelW y := by simp [x]
          _ = some a := hy
      · have := (deleteEdge_reachable_iff e u v u x).mp ?_
        · exact this
        · simpa [x] using hry
    · intro b hb x hx hrx
      have hxe : labelW (e x) = some b := by simpa [hlabel] using hx
      exact hB b hb (e x) hxe
        ((deleteEdge_reachable_iff e u v u x).mpr hrx)
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨x, hx, hrx⟩ := hA a ha
      exact ⟨e x, by simpa [hlabel] using hx,
        (deleteEdge_reachable_iff e u v u x).mpr hrx⟩
    · intro b hb y hy hry
      let x := e.symm y
      have hx : labelV x = some b := by
        calc
          labelV x = labelW (e x) := (hlabel x).symm
          _ = labelW y := by simp [x]
          _ = some b := hy
      apply hB b hb x hx
      apply (deleteEdge_reachable_iff e u v u x).mp
      simpa [x] using hry

/-- The generic edge-separation predicate is invariant under every
label-preserving graph isomorphism. -/
theorem edgeSeparates_iff_of_iso
    (e : G ≃g H) (labelV : V → Option α) (labelW : W → Option α)
    (hlabel : ∀ x, labelW (e x) = labelV x)
    (A B : Finset α) :
    EdgeSeparates H labelW A B ↔ EdgeSeparates G labelV A B := by
  constructor
  · rintro ⟨u', v', huv, hsep⟩
    let u := e.symm u'
    let v := e.symm v'
    refine ⟨u, v, ?_, ?_⟩
    · apply e.map_rel_iff.mp
      simpa [u, v] using huv
    · rcases hsep with hsep | hsep
      · left
        apply (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v A B).mp
        simpa [u, v] using hsep
      · right
        apply (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v B A).mp
        simpa [u, v] using hsep
  · rintro ⟨u, v, huv, hsep⟩
    refine ⟨e u, e v, e.map_rel_iff.mpr huv, ?_⟩
    rcases hsep with hsep | hsep
    · left
      exact (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v A B).mpr hsep
    · right
      exact (componentSeparatesAt_iff_of_iso e labelV labelW hlabel u v B A).mpr hsep

end GraphQuartet

namespace GraphModel.BinaryPhyloGraph

variable {α V : Type*} [Fintype α] [Fintype V] [DecidableEq V]

/-- Canonicalizing an arbitrary finite vertex type preserves every
edge-separated pair of labelled taxon sets. -/
theorem edgeSeparates_canonicalize_iff (P : BinaryPhyloGraph α V)
    (A B : Finset α) :
    GraphQuartet.EdgeSeparates P.canonicalize.tree.G
        P.canonicalize.tree.leafLabel? A B ↔
      GraphQuartet.EdgeSeparates P.G P.leafLabel? A B := by
  exact GraphQuartet.edgeSeparates_iff_of_iso P.canonicalIso
    P.leafLabel? P.canonicalize.tree.leafLabel?
    P.leafLabel?_canonicalIso A B

end GraphModel.BinaryPhyloGraph

namespace CanonicalBinaryPhyloGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Edge separation in a canonical conventional graph is exactly edge
separation in any of its cut-open syntax encodings. -/
theorem edgeSeparates_encodeAt_iff (P : CanonicalBinaryPhyloGraph α)
    (rootLabel : α) (A B : Finset α) :
    GraphQuartet.EdgeSeparates P.tree.G P.tree.leafLabel? A B ↔
      GraphQuartet.EdgeSeparates
        (TreeAdequacy.PhyloTree.graph (P.encodeAt rootLabel))
        (TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel)) A B := by
  exact GraphQuartet.edgeSeparates_iff_of_iso
    (P.encodeGraphIsoAt rootLabel)
    (TreeAdequacy.PhyloTree.label? (P.encodeAt rootLabel))
    P.tree.leafLabel?
    (P.encodeGraphIsoAt_leafLabel? rootLabel) A B

end CanonicalBinaryPhyloGraph

namespace Tree.PhyloTree

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Passing from syntax to its canonical conventional realization preserves
every edge-separated pair of taxon sets. -/
theorem edgeSeparates_toCanonical_iff (T : Tree.PhyloTree α)
    (A B : Finset α) :
    GraphQuartet.EdgeSeparates T.toCanonicalBinaryPhyloGraph.tree.G
        T.toCanonicalBinaryPhyloGraph.tree.leafLabel? A B ↔
      GraphQuartet.EdgeSeparates (TreeAdequacy.PhyloTree.graph T)
        (TreeAdequacy.PhyloTree.label? T) A B := by
  exact GraphQuartet.edgeSeparates_iff_of_iso T.toCanonicalGraphIso
    (TreeAdequacy.PhyloTree.label? T)
    T.toCanonicalBinaryPhyloGraph.tree.leafLabel?
    T.toCanonicalGraphIso_leafLabel? A B

end Tree.PhyloTree

namespace CanonicalBinaryPhyloGraph

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The direct display predicate on a conventional graph agrees with the
same direct predicate on every cut-open syntax encoding. -/
theorem graphDisplaysSplit_encodeAt_iff
    (P : CanonicalBinaryPhyloGraph α) (rootLabel : α)
    (Q : Finset α) (s : Circular.QuartetSplit α) :
    P.GraphDisplaysSplit Q s ↔
      GraphQuartet.PhyloTree.GraphDisplaysSplit
        (P.encodeAt rootLabel) Q s := by
  constructor
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (P.edgeSeparates_encodeAt_iff rootLabel A B).mp hsep⟩
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (P.edgeSeparates_encodeAt_iff rootLabel A B).mpr hsep⟩

/-- Edge separation in a conventional graph selects exactly the recursive
displayed split of any syntax encoding of that graph. -/
theorem graphDisplaysSplit_iff_eq_displayedSplitOn
    (P : CanonicalBinaryPhyloGraph α) (rootLabel : α)
    (Q : Finset α) (hQ : Q.card = 4)
    (s : Circular.QuartetSplit α) :
    P.GraphDisplaysSplit Q s ↔
      s = (P.encodeAt rootLabel).displayedSplitOn Q hQ := by
  exact (P.graphDisplaysSplit_encodeAt_iff rootLabel Q s).trans
    (GraphQuartet.PhyloTree.graphDisplaysSplit_iff_eq_displayedSplitOn
      (P.encodeAt rootLabel) Q hQ s)

/-- Channel form of the graph/syntax displayed-split characterization. -/
theorem graphDisplaysTopology_iff_eq_displayedTopology
    (P : CanonicalBinaryPhyloGraph (Fin n)) (rootLabel : Fin n)
    (q : Upper.Quartet n) (i : Fin 3) :
    P.GraphDisplaysTopology q i ↔
      i = Upper.displayedTopology (P.encodeAt rootLabel) q := by
  rw [GraphDisplaysTopology,
    P.graphDisplaysSplit_iff_eq_displayedSplitOn rootLabel q.1 q.2]
  rw [← Upper.splitOfTopology_displayedTopology]
  exact (Upper.splitOfTopology_injective q).eq_iff

/-- Every labelled quartet in a conventional binary phylogenetic graph has
exactly one of the three direct edge-separation topologies. -/
theorem graphDisplaysTopology_existsUnique
    (P : CanonicalBinaryPhyloGraph (Fin n)) (q : Upper.Quartet n) :
    ∃! i : Fin 3, P.GraphDisplaysTopology q i := by
  let rootLabel := quartetRoot q
  let T := P.encodeAt rootLabel
  refine ⟨Upper.displayedTopology T q, ?_, ?_⟩
  · exact (P.graphDisplaysTopology_iff_eq_displayedTopology rootLabel q _).mpr rfl
  · intro i hi
    exact (P.graphDisplaysTopology_iff_eq_displayedTopology rootLabel q i).mp hi

end CanonicalBinaryPhyloGraph

/-- The graph-theoretically displayed quartet topology, chosen from its
proved existence and uniqueness. -/
noncomputable def graphDisplayedTopology
    (P : CanonicalBinaryPhyloGraph (Fin n))
    (q : Upper.Quartet n) : Fin 3 :=
  Classical.choose (P.graphDisplaysTopology_existsUnique q).exists

theorem graphDisplayedTopology_graphDisplaysTopology
    (P : CanonicalBinaryPhyloGraph (Fin n)) (q : Upper.Quartet n) :
    P.GraphDisplaysTopology q (graphDisplayedTopology P q) :=
  Classical.choose_spec (P.graphDisplaysTopology_existsUnique q).exists

/-- The chosen graph topology agrees with every cut-open syntax encoding;
in particular, it is independent of the chosen root leaf. -/
theorem graphDisplayedTopology_eq_encodeAt
    (P : CanonicalBinaryPhyloGraph (Fin n)) (rootLabel : Fin n)
    (q : Upper.Quartet n) :
    graphDisplayedTopology P q =
      Upper.displayedTopology (P.encodeAt rootLabel) q :=
  (P.graphDisplaysTopology_iff_eq_displayedTopology rootLabel q _).mp
    (graphDisplayedTopology_graphDisplaysTopology P q)

namespace Tree.PhyloTree

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Direct graph display is unchanged when a syntax tree is transported to
its canonical conventional graph presentation. -/
theorem graphDisplaysSplit_toCanonical_iff (T : Tree.PhyloTree α)
    (Q : Finset α) (s : Circular.QuartetSplit α) :
    T.toCanonicalBinaryPhyloGraph.GraphDisplaysSplit Q s ↔
      GraphQuartet.PhyloTree.GraphDisplaysSplit T Q s := by
  constructor
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (T.edgeSeparates_toCanonical_iff A B).mp hsep⟩
  · rintro ⟨hs, A, hA, B, hB, hne, hsep⟩
    exact ⟨hs, A, hA, B, hB, hne,
      (T.edgeSeparates_toCanonical_iff A B).mpr hsep⟩

theorem graphDisplaysTopology_toCanonical_iff
    (T : Tree.PhyloTree (Fin n)) (q : Upper.Quartet n) (i : Fin 3) :
    T.toCanonicalBinaryPhyloGraph.GraphDisplaysTopology q i ↔
      i = Upper.displayedTopology T q := by
  rw [CanonicalBinaryPhyloGraph.GraphDisplaysTopology,
    T.graphDisplaysSplit_toCanonical_iff,
    GraphQuartet.PhyloTree.graphDisplaysSplit_iff_eq_displayedSplitOn
      T q.1 q.2]
  rw [← Upper.splitOfTopology_displayedTopology]
  exact (Upper.splitOfTopology_injective q).eq_iff

/-- Realizing a syntax tree as a canonical conventional graph preserves its
displayed topology pointwise. -/
theorem graphDisplayedTopology_toCanonical (T : Tree.PhyloTree (Fin n))
    (q : Upper.Quartet n) :
    graphDisplayedTopology T.toCanonicalBinaryPhyloGraph q =
      Upper.displayedTopology T q :=
  (T.graphDisplaysTopology_toCanonical_iff q _).mp
    (graphDisplayedTopology_graphDisplaysTopology
      T.toCanonicalBinaryPhyloGraph q)

end Tree.PhyloTree

/-- Quartet distance on the conventional graph domain. -/
noncomputable def graphQuartetDistance
    (P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n)) : ℕ :=
  Counting.truthDistance (graphDisplayedTopology P₁)
    (graphDisplayedTopology P₂)

theorem graphQuartetDistance_le_choose
    (P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n)) :
    graphQuartetDistance P₁ P₂ ≤ Nat.choose n 4 := by
  calc
    graphQuartetDistance P₁ P₂ ≤ Fintype.card (Upper.Quartet n) := by
      unfold graphQuartetDistance Counting.truthDistance
      exact Finset.card_filter_le Finset.univ _
    _ = Nat.choose n 4 := Upper.card_quartet n

/-- Encoding each conventional graph at one fixed leaf preserves the entire
quartet distance, not just one quartet at a time. -/
theorem graphQuartetDistance_eq_encodeAt
    (P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n))
    (root₁ root₂ : Fin n) :
    graphQuartetDistance P₁ P₂ =
      Upper.quartetDistance (P₁.encodeAt root₁) (P₂.encodeAt root₂) := by
  unfold graphQuartetDistance Upper.quartetDistance
  congr 1
  · funext q
    exact graphDisplayedTopology_eq_encodeAt P₁ root₁ q
  · funext q
    exact graphDisplayedTopology_eq_encodeAt P₂ root₂ q

/-- The canonical conventional realizations of two syntax trees have exactly
their original quartet distance. -/
theorem graphQuartetDistance_toCanonical
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    graphQuartetDistance T₁.toCanonicalBinaryPhyloGraph
        T₂.toCanonicalBinaryPhyloGraph =
      Upper.quartetDistance T₁ T₂ := by
  unfold graphQuartetDistance Upper.quartetDistance
  congr 1
  · funext q
    exact T₁.graphDisplayedTopology_toCanonical q
  · funext q
    exact T₂.graphDisplayedTopology_toCanonical q

/-- Maximum quartet distance over all canonical finite conventional graph
presentations.  Different arguments may have different vertex counts. -/
noncomputable def graphMaximumQuartetDistance (n : ℕ) : ℕ :=
  maxPairValue (@graphQuartetDistance n)

theorem graphMaximumQuartetDistance_le_choose (n : ℕ) :
    graphMaximumQuartetDistance n ≤ Nat.choose n 4 := by
  exact maxPairValue_le (@graphQuartetDistance n)
    (@graphQuartetDistance_le_choose n)

theorem graphQuartetDistance_le_graphMaximum (n : ℕ)
    (P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n)) :
    graphQuartetDistance P₁ P₂ ≤ graphMaximumQuartetDistance n := by
  exact value_le_maxPairValue (@graphQuartetDistance n)
    (@graphQuartetDistance_le_choose n) P₁ P₂

theorem graphMaximumQuartetDistance_eq_zero_or_exists (n : ℕ) :
    graphMaximumQuartetDistance n = 0 ∨
      ∃ P₁ P₂ : CanonicalBinaryPhyloGraph (Fin n),
        graphMaximumQuartetDistance n = graphQuartetDistance P₁ P₂ := by
  exact maxPairValue_eq_zero_or_exists (@graphQuartetDistance n)
    (@graphQuartetDistance_le_choose n)

/-- The genuine conventional-graph maximum is the syntax maximum used by the
counting proof.  A single fixed root leaf is used for every quartet of each
graph; no quartet-dependent rooting enters this equality. -/
theorem graphMaximumQuartetDistance_eq_syntaxMaximum
    (n : ℕ) (hn : 4 ≤ n) :
    graphMaximumQuartetDistance n =
      maxPairValue (@Upper.quartetDistance n) := by
  let rootLabel : Fin n := ⟨0, by omega⟩
  apply Nat.le_antisymm
  · rcases graphMaximumQuartetDistance_eq_zero_or_exists n with
      hzero | ⟨P₁, P₂, hmax⟩
    · rw [hzero]
      exact Nat.zero_le _
    · rw [hmax, graphQuartetDistance_eq_encodeAt P₁ P₂ rootLabel rootLabel]
      exact value_le_maxPairValue (@Upper.quartetDistance n)
        (@Upper.quartetDistance_le_choose n)
        (P₁.encodeAt rootLabel) (P₂.encodeAt rootLabel)
  · rcases maxPairValue_eq_zero_or_exists (@Upper.quartetDistance n)
      (@Upper.quartetDistance_le_choose n) with
      hzero | ⟨T₁, T₂, hmax⟩
    · rw [hzero]
      exact Nat.zero_le _
    · rw [hmax, ← graphQuartetDistance_toCanonical T₁ T₂]
      exact graphQuartetDistance_le_graphMaximum n
        T₁.toCanonicalBinaryPhyloGraph T₂.toCanonicalBinaryPhyloGraph

end QuartetDistance
