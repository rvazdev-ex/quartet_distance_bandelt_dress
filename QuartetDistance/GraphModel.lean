import QuartetDistance.TreeAdequacy
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Independent graph model for binary phylogenetic trees

This file starts from the usual graph-theoretic definition: a finite tree,
whose degree-one vertices are bijectively labelled by the taxa and whose
other vertices have degree three.  It orients the graph away from a chosen
labelled leaf.  The resulting parent/children decomposition is the bridge to
the cut-open `Tree.PhyloTree` syntax.
-/

namespace QuartetDistance
namespace GraphModel

open SimpleGraph

set_option linter.unusedSectionVars false

noncomputable local instance finiteNeighborSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Fintype (G.neighborSet v) := Fintype.ofFinite _

/-- The standard independent graph definition of an unrooted binary
phylogenetic tree.  `leafEquiv` says precisely that the degree-one vertices,
and no others, are labelled. -/
structure BinaryPhyloGraph (α V : Type*) [Fintype V] where
  G : SimpleGraph V
  isTree : G.IsTree
  leafEquiv : α ≃ {v : V // G.degree v = 1}
  internal_degree : ∀ v : V, G.degree v ≠ 1 → G.degree v = 3

namespace BinaryPhyloGraph

variable {α V : Type*} [Fintype V] [DecidableEq V]

/-- The graph vertex carrying a taxon label. -/
def leafVertex (P : BinaryPhyloGraph α V) (a : α) : V :=
  (P.leafEquiv a).1

@[simp] theorem degree_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.G.degree (P.leafVertex a) = 1 :=
  (P.leafEquiv a).2

theorem leafVertex_injective (P : BinaryPhyloGraph α V) :
    Function.Injective P.leafVertex := by
  intro a b h
  apply P.leafEquiv.injective
  exact Subtype.ext h

/-- Recover the unique taxon at a degree-one vertex. -/
def labelOfLeaf (P : BinaryPhyloGraph α V) (v : V)
    (hv : P.G.degree v = 1) : α :=
  P.leafEquiv.symm ⟨v, hv⟩

@[simp] theorem leafVertex_labelOfLeaf (P : BinaryPhyloGraph α V) (v : V)
    (hv : P.G.degree v = 1) :
    P.leafVertex (P.labelOfLeaf v hv) = v := by
  exact congrArg Subtype.val (P.leafEquiv.apply_symm_apply ⟨v, hv⟩)

@[simp] theorem labelOfLeaf_leafVertex (P : BinaryPhyloGraph α V) (a : α) :
    P.labelOfLeaf (P.leafVertex a) (P.degree_leafVertex a) = a := by
  exact P.leafEquiv.symm_apply_apply a

/-- Neighbors farther from the chosen root. -/
noncomputable def children (P : BinaryPhyloGraph α V) (root v : V) : Finset V :=
  (P.G.neighborFinset v).filter fun w =>
    P.G.dist root v < P.G.dist root w

theorem mem_children_iff (P : BinaryPhyloGraph α V) (root v w : V) :
    w ∈ P.children root v ↔
      P.G.Adj v w ∧ P.G.dist root w = P.G.dist root v + 1 := by
  classical
  simp only [children, Finset.mem_filter, P.G.mem_neighborFinset]
  constructor
  · rintro ⟨hadj, hlt⟩
    refine ⟨hadj, ?_⟩
    rcases P.isTree.dist_eq_dist_add_one_of_adj root hadj with hback | hforward
    · omega
    · exact hforward
  · rintro ⟨hadj, hdist⟩
    exact ⟨hadj, by omega⟩

/-- A parent is the (necessarily unique) adjacent vertex one step closer to
the chosen root. -/
def IsParent (P : BinaryPhyloGraph α V) (root v w : V) : Prop :=
  P.G.Adj v w ∧ P.G.dist root w + 1 = P.G.dist root v

theorem exists_parent (P : BinaryPhyloGraph α V) {root v : V}
    (hne : v ≠ root) : ∃ w, P.IsParent root v w := by
  obtain ⟨p, hp, hlen⟩ := P.isTree.connected.exists_path_of_dist root v
  have hpnon : ¬ p.Nil := by
    intro hnil
    exact hne hnil.eq.symm
  refine ⟨p.penultimate, p.adj_penultimate hpnon |>.symm, ?_⟩
  have hdropdist : p.dropLast.length = P.G.dist root p.penultimate := by
    exact length_eq_dist_of_subwalk hlen (Walk.isSubwalk_rfl p).dropLast
  rw [← hdropdist, ← hlen]
  exact p.length_dropLast_add_one hpnon

theorem parent_unique (P : BinaryPhyloGraph α V) {root v w₁ w₂ : V}
    (h₁ : P.IsParent root v w₁) (h₂ : P.IsParent root v w₂) : w₁ = w₂ := by
  obtain ⟨p₁, hp₁, hlen₁⟩ := P.isTree.connected.exists_path_of_dist root w₁
  obtain ⟨p₂, hp₂, hlen₂⟩ := P.isTree.connected.exists_path_of_dist root w₂
  let q₁ : P.G.Walk root v := p₁.concat h₁.1.symm
  let q₂ : P.G.Walk root v := p₂.concat h₂.1.symm
  have hq₁len : q₁.length = P.G.dist root v := by
    simp only [q₁, Walk.length_concat, hlen₁]
    exact h₁.2
  have hq₂len : q₂.length = P.G.dist root v := by
    simp only [q₂, Walk.length_concat, hlen₂]
    exact h₂.2
  have hq₁path : q₁.IsPath := q₁.isPath_of_length_eq_dist hq₁len
  have hq₂path : q₂.IsPath := q₂.isPath_of_length_eq_dist hq₂len
  have hq : q₁ = q₂ := by
    exact (P.isTree.existsUnique_path root v).unique hq₁path hq₂path
  have hpen := congrArg Walk.penultimate hq
  simpa [q₁, q₂] using hpen

theorem existsUnique_parent (P : BinaryPhyloGraph α V) {root v : V}
    (hne : v ≠ root) : ∃! w, P.IsParent root v w := by
  obtain ⟨w, hw⟩ := P.exists_parent hne
  exact ⟨w, hw, fun y hy => P.parent_unique hy hw⟩

theorem neighborFinset_eq_insert_children (P : BinaryPhyloGraph α V)
    {root v parent : V} (_hv : v ≠ root) (hp : P.IsParent root v parent) :
    P.G.neighborFinset v = insert parent (P.children root v) := by
  classical
  ext w
  simp only [P.G.mem_neighborFinset, Finset.mem_insert, mem_children_iff]
  constructor
  · intro hadj
    rcases P.isTree.dist_eq_dist_add_one_of_adj root hadj with hcloser | hfarther
    · left
      exact P.parent_unique ⟨hadj, hcloser.symm⟩ hp
    · exact Or.inr ⟨hadj, hfarther⟩
  · rintro (rfl | ⟨hadj, _⟩)
    · exact hp.1
    · exact hadj

theorem parent_not_mem_children (P : BinaryPhyloGraph α V)
    {root v parent : V} (hp : P.IsParent root v parent) :
    parent ∉ P.children root v := by
  rw [mem_children_iff]
  rintro ⟨_, hfarther⟩
  have hcloser := hp.2
  omega

theorem degree_eq_card_children_add_one (P : BinaryPhyloGraph α V)
    {root v parent : V} (hv : v ≠ root) (hp : P.IsParent root v parent) :
    P.G.degree v = (P.children root v).card + 1 := by
  rw [← P.G.card_neighborFinset_eq_degree,
    P.neighborFinset_eq_insert_children hv hp,
    Finset.card_insert_of_notMem (P.parent_not_mem_children hp)]

theorem card_children_of_degree_one (P : BinaryPhyloGraph α V)
    {root v : V} (hv : v ≠ root) (hdeg : P.G.degree v = 1) :
    (P.children root v).card = 0 := by
  obtain ⟨parent, hp⟩ := P.exists_parent hv
  have h := P.degree_eq_card_children_add_one hv hp
  omega

theorem card_children_of_internal (P : BinaryPhyloGraph α V)
    {root v : V} (hv : v ≠ root) (hdeg : P.G.degree v ≠ 1) :
    (P.children root v).card = 2 := by
  obtain ⟨parent, hp⟩ := P.exists_parent hv
  have h := P.degree_eq_card_children_add_one hv hp
  have hthree := P.internal_degree v hdeg
  omega

theorem dist_lt_card (P : BinaryPhyloGraph α V) (root v : V) :
    P.G.dist root v < Fintype.card V := by
  obtain ⟨p, hp, hlen⟩ := P.isTree.connected.exists_path_of_dist root v
  rw [← hlen]
  exact hp.length_lt

/-- The edge orientation away from `root`, viewed as a recursion relation:
`childRel root w v` means that `w` is a child of `v`. -/
def childRel (P : BinaryPhyloGraph α V) (root : V) (w v : V) : Prop :=
  w ∈ P.children root v

theorem childRel_height_decreases (P : BinaryPhyloGraph α V) (root : V)
    {w v : V} (h : P.childRel root w v) :
    Fintype.card V - P.G.dist root w <
      Fintype.card V - P.G.dist root v := by
  have hdist := (P.mem_children_iff root v w).mp h |>.2
  have hwbound := P.dist_lt_card root w
  omega

theorem childRel_wellFounded (P : BinaryPhyloGraph α V) (root : V) :
    WellFounded (P.childRel root) := by
  exact Subrelation.wf (fun h => P.childRel_height_decreases root h)
    (measure (fun v => Fintype.card V - P.G.dist root v)).wf

/-- Descendants of `v` in the orientation away from `root`. -/
abbrev Descendants (P : BinaryPhyloGraph α V) (root v : V) :=
  {w : V // Relation.ReflTransGen (P.childRel root) w v}

theorem dist_le_of_descendant (P : BinaryPhyloGraph α V) (root : V)
    {w v : V} (h : Relation.ReflTransGen (P.childRel root) w v) :
    P.G.dist root v ≤ P.G.dist root w := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hbc hchild ih =>
      have hstep := (P.mem_children_iff root _ _).mp hchild |>.2
      omega

theorem eq_of_descendant_of_dist_eq (P : BinaryPhyloGraph α V) (root : V)
    {w v : V} (h : Relation.ReflTransGen (P.childRel root) w v)
    (hdist : P.G.dist root w = P.G.dist root v) : w = v := by
  cases h with
  | refl => rfl
  | @tail b c hbc hchild =>
      have hle := P.dist_le_of_descendant root hbc
      have hstep := (P.mem_children_iff root v b).mp hchild |>.2
      omega

theorem childRel_rightUnique (P : BinaryPhyloGraph α V) (root : V) :
    Relator.RightUnique (P.childRel root) := by
  intro child parent₁ parent₂ h₁ h₂
  have hp₁ : P.IsParent root child parent₁ := by
    have h := (P.mem_children_iff root parent₁ child).mp h₁
    exact ⟨h.1.symm, h.2.symm⟩
  have hp₂ : P.IsParent root child parent₂ := by
    have h := (P.mem_children_iff root parent₂ child).mp h₂
    exact ⟨h.1.symm, h.2.symm⟩
  exact P.parent_unique hp₁ hp₂

theorem descendant_branch_unique (P : BinaryPhyloGraph α V) (root : V)
    {w c₁ c₂ v : V}
    (hw₁ : Relation.ReflTransGen (P.childRel root) w c₁)
    (hw₂ : Relation.ReflTransGen (P.childRel root) w c₂)
    (hc₁ : P.childRel root c₁ v) (hc₂ : P.childRel root c₂ v) :
    c₁ = c₂ := by
  have hdist₁ := (P.mem_children_iff root v c₁).mp hc₁ |>.2
  have hdist₂ := (P.mem_children_iff root v c₂).mp hc₂ |>.2
  rcases hw₁.total_of_right_unique (P.childRel_rightUnique root) hw₂ with h | h
  · exact P.eq_of_descendant_of_dist_eq root h (by omega)
  · exact (P.eq_of_descendant_of_dist_eq root h (by omega)).symm

theorem descendant_of_child_ne_parent (P : BinaryPhyloGraph α V) (root : V)
    {w child parent : V}
    (hw : Relation.ReflTransGen (P.childRel root) w child)
    (hc : P.childRel root child parent) : w ≠ parent := by
  intro heq
  subst w
  have hle := P.dist_le_of_descendant root hw
  have hstep := (P.mem_children_iff root parent child).mp hc |>.2
  omega

/-- Assemble a parent vertex and the descendant sets below each immediate
child into the whole descendant set. -/
noncomputable def assembleDescendants (P : BinaryPhyloGraph α V)
    (root v : V) :
    Unit ⊕ (Σ c : ↑(P.children root v), P.Descendants root c.1) →
      P.Descendants root v
  | .inl _ => ⟨v, .refl⟩
  | .inr z => ⟨z.2.1, z.2.2.trans (.single z.1.2)⟩

theorem assembleDescendants_surjective (P : BinaryPhyloGraph α V)
    (root v : V) : Function.Surjective (P.assembleDescendants root v) := by
  intro w
  rcases w.2.cases_tail with heq | ⟨c, hwc, hcv⟩
  · refine ⟨.inl (), ?_⟩
    apply Subtype.ext
    exact heq
  · refine ⟨.inr ⟨⟨c, hcv⟩, ⟨w.1, hwc⟩⟩, ?_⟩
    rfl

theorem assembleDescendants_injective (P : BinaryPhyloGraph α V)
    (root v : V) : Function.Injective (P.assembleDescendants root v) := by
  rintro (u | z) (u' | z') h
  · rfl
  · exfalso
    have hv : v = z'.2.1 := congrArg Subtype.val h
    exact P.descendant_of_child_ne_parent root z'.2.2 z'.1.2 hv.symm
  · exfalso
    have hv : z.2.1 = v := congrArg Subtype.val h
    exact P.descendant_of_child_ne_parent root z.2.2 z.1.2 hv
  · have hw : z.2.1 = z'.2.1 := congrArg Subtype.val h
    have hc : z.1.1 = z'.1.1 := P.descendant_branch_unique root
      z.2.2 (hw ▸ z'.2.2) z.1.2 z'.1.2
    apply congrArg Sum.inr
    cases z with
    | mk c z =>
      cases z' with
      | mk c' z' =>
        have hcc : c = c' := Subtype.ext hc
        subst c'
        have hzz : z = z' := Subtype.ext hw
        subst z'
        rfl

/-- Canonical decomposition of descendants into the root vertex and the
branches below its immediate children. -/
noncomputable def descendantsEquiv (P : BinaryPhyloGraph α V) (root v : V) :
    Unit ⊕ (Σ c : ↑(P.children root v), P.Descendants root c.1) ≃
      P.Descendants root v :=
  Equiv.ofBijective (P.assembleDescendants root v)
    ⟨P.assembleDescendants_injective root v,
      P.assembleDescendants_surjective root v⟩

theorem adj_iff_childRel (P : BinaryPhyloGraph α V) (root x y : V) :
    P.G.Adj x y ↔ P.childRel root x y ∨ P.childRel root y x := by
  constructor
  · intro hxy
    rcases P.isTree.dist_eq_dist_add_one_of_adj root hxy with h | h
    · left
      exact (P.mem_children_iff root y x).mpr ⟨hxy.symm, h⟩
    · right
      exact (P.mem_children_iff root x y).mpr ⟨hxy, h⟩
  · rintro (h | h)
    · exact ((P.mem_children_iff root y x).mp h).1.symm
    · exact ((P.mem_children_iff root x y).mp h).1

theorem adj_parent_descendant_iff (P : BinaryPhyloGraph α V) (root : V)
    {child parent w : V}
    (hc : P.childRel root child parent)
    (hw : Relation.ReflTransGen (P.childRel root) w child) :
    P.G.Adj parent w ↔ w = child := by
  constructor
  · intro hadj
    rcases (P.adj_iff_childRel root parent w).mp hadj with hpw | hwp
    · have hle := P.dist_le_of_descendant root hw
      have hcstep := (P.mem_children_iff root parent child).mp hc |>.2
      have hpwstep := (P.mem_children_iff root w parent).mp hpw |>.2
      omega
    · exact (P.descendant_branch_unique root hw
        Relation.ReflTransGen.refl hc hwp).symm
  · intro heq
    subst w
    exact ((P.mem_children_iff root parent child).mp hc).1

theorem not_adj_descendants_of_distinct_children
    (P : BinaryPhyloGraph α V) (root : V)
    {c₁ c₂ parent x y : V} (hc₁ : P.childRel root c₁ parent)
    (hc₂ : P.childRel root c₂ parent) (hne : c₁ ≠ c₂)
    (hx : Relation.ReflTransGen (P.childRel root) x c₁)
    (hy : Relation.ReflTransGen (P.childRel root) y c₂) :
    ¬ P.G.Adj x y := by
  intro hadj
  rcases (P.adj_iff_childRel root x y).mp hadj with hxy | hyx
  · have hxc₂ : Relation.ReflTransGen (P.childRel root) x c₂ :=
      (Relation.ReflTransGen.single hxy).trans hy
    exact hne (P.descendant_branch_unique root hx hxc₂ hc₁ hc₂)
  · have hyc₁ : Relation.ReflTransGen (P.childRel root) y c₁ :=
      (Relation.ReflTransGen.single hyx).trans hx
    exact hne (P.descendant_branch_unique root hyc₁ hy hc₁ hc₂)

/-- Every vertex has a parent chain to the chosen root. -/
theorem descendant_root (P : BinaryPhyloGraph α V) (root w : V) :
    Relation.ReflTransGen (P.childRel root) w root := by
  generalize hd : P.G.dist root w = d
  induction d using Nat.strong_induction_on generalizing w with
  | h d ih =>
      by_cases hwr : w = root
      · subst w
        exact .refl
      · obtain ⟨parent, hp⟩ := P.exists_parent hwr
        have hparentdist : P.G.dist root parent < d := by
          have hpdist := hp.2
          omega
        have hchild : P.childRel root w parent := by
          apply (P.mem_children_iff root parent w).mpr
          exact ⟨hp.1.symm, hp.2.symm⟩
        exact (ih (P.G.dist root parent) hparentdist parent rfl).head hchild

/-- The unique neighbor of a labelled root leaf. -/
noncomputable def rootNeighbor (P : BinaryPhyloGraph α V) (a : α) : V :=
  (degree_eq_one_iff_existsUnique_adj.mp (P.degree_leafVertex a)).choose

theorem root_adj_rootNeighbor (P : BinaryPhyloGraph α V) (a : α) :
    P.G.Adj (P.leafVertex a) (P.rootNeighbor a) :=
  (degree_eq_one_iff_existsUnique_adj.mp (P.degree_leafVertex a)).choose_spec.1

theorem rootNeighbor_ne_root (P : BinaryPhyloGraph α V) (a : α) :
    P.rootNeighbor a ≠ P.leafVertex a :=
  (P.root_adj_rootNeighbor a).ne.symm

theorem root_isParent_rootNeighbor (P : BinaryPhyloGraph α V) (a : α) :
    P.IsParent (P.leafVertex a) (P.rootNeighbor a) (P.leafVertex a) := by
  refine ⟨(P.root_adj_rootNeighbor a).symm, ?_⟩
  have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr (P.root_adj_rootNeighbor a)
  simpa using hdist.symm

theorem childRel_root_iff (P : BinaryPhyloGraph α V) (a : α) (v : V) :
    P.childRel (P.leafVertex a) v (P.leafVertex a) ↔
      v = P.rootNeighbor a := by
  rw [childRel, mem_children_iff]
  constructor
  · rintro ⟨hadj, _⟩
    exact (degree_eq_one_iff_existsUnique_adj.mp (P.degree_leafVertex a)).choose_spec.2
      v hadj
  · rintro rfl
    refine ⟨P.root_adj_rootNeighbor a, ?_⟩
    have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr (P.root_adj_rootNeighbor a)
    simpa using hdist

/-- The crown rooted at the neighbor of the distinguished leaf contains
exactly all graph vertices other than that leaf. -/
theorem mem_descendants_rootNeighbor_iff (P : BinaryPhyloGraph α V)
    (a : α) (w : V) :
    Relation.ReflTransGen (P.childRel (P.leafVertex a)) w (P.rootNeighbor a) ↔
      w ≠ P.leafVertex a := by
  constructor
  · intro hw heq
    subst w
    have hle := P.dist_le_of_descendant (P.leafVertex a) hw
    have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr (P.root_adj_rootNeighbor a)
    simp only [SimpleGraph.dist_self] at hle
    omega
  · intro hwne
    have hroot := P.descendant_root (P.leafVertex a) w
    rcases hroot.cases_tail with heq | ⟨c, hwc, hcroot⟩
    · exact (hwne heq.symm).elim
    · have hc : c = P.rootNeighbor a :=
        (P.childRel_root_iff a c).mp hcroot
      simpa [hc] using hwc

/-! ## Recursive graph-preserving encoding -/

section Encoding

variable [Fintype α] [DecidableEq α]

theorem descendant_eq_of_degree_one (P : BinaryPhyloGraph α V)
    {root v w : V} (hv : v ≠ root) (hdeg : P.G.degree v = 1)
    (hw : Relation.ReflTransGen (P.childRel root) w v) : w = v := by
  rcases hw.cases_tail with heq | ⟨c, _, hcv⟩
  · exact heq.symm
  · have hcard := P.card_children_of_degree_one hv hdeg
    have hempty : P.children root v = ∅ := Finset.card_eq_zero.mp hcard
    rw [childRel, hempty] at hcv
    simp at hcv

/-- A subtree encoding carries the graph isomorphism, its root image, and
the exact labelled-leaf invariant needed to build a `PhyloTree`. -/
structure SubtreeEncoding (P : BinaryPhyloGraph α V) (rootLabel : α)
    (v : V) where
  tree : Tree.FullTree {a : α // a ≠ rootLabel}
  graphIso :
    TreeAdequacy.FullTree.graph tree ≃g
      P.G.induce {w : V |
        Relation.ReflTransGen (P.childRel (P.leafVertex rootLabel)) w v}
  root_eq : (graphIso (TreeAdequacy.FullTree.rootVertex tree)).1 = v
  label_iff : ∀ (x : TreeAdequacy.FullTree.Vertex tree)
      (a : {a : α // a ≠ rootLabel}),
    TreeAdequacy.FullTree.label? tree x = some a ↔
      (graphIso x).1 = P.leafVertex a.1
  nodup_leaves : tree.leaves.Nodup
  mem_leaves_iff : ∀ a : {a : α // a ≠ rootLabel},
    a ∈ tree.leaves ↔
      Relation.ReflTransGen (P.childRel (P.leafVertex rootLabel))
        (P.leafVertex a.1) v

/-- A two-element child set can be enumerated by `Bool`. -/
noncomputable def childrenBoolEquiv (P : BinaryPhyloGraph α V)
    (root v : V) (hcard : (P.children root v).card = 2) :
    Bool ≃ ↑(P.children root v) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_bool, Fintype.card_coe, hcard])

/-- The sigma type over two child branches is their ordinary sum. -/
noncomputable def twoBranchEquiv
    {C : Type*} [Fintype C] [DecidableEq C]
    (e : Bool ≃ C) (F : C → Type*) :
    F (e false) ⊕ F (e true) ≃ Σ c : C, F c :=
  (Equiv.sumEquivSigmaBool (F (e false)) (F (e true))).trans <|
    (Equiv.sigmaCongrRight fun b => by cases b <;> exact Equiv.refl _).trans <|
      Equiv.sigmaCongrLeft e

/-- A child is strictly farther from the root, hence is not the root. -/
theorem child_ne_root (P : BinaryPhyloGraph α V) {root v : V}
    {c : ↑(P.children root v)} : c.1 ≠ root := by
  intro hc
  have hdist := (P.mem_children_iff root v c.1).mp c.2 |>.2
  rw [hc, SimpleGraph.dist_self] at hdist
  omega

/-- Vertex equivalence used when two recursively encoded child branches are
joined below a new fork vertex. -/
noncomputable def forkVertexEquiv (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1) :
    TreeAdequacy.FullTree.Vertex
        (.fork (E (e false)).tree (E (e true)).tree) ≃
      P.Descendants (P.leafVertex rootLabel) v :=
  (Equiv.sumAssoc Unit
      (TreeAdequacy.FullTree.Vertex (E (e false)).tree)
      (TreeAdequacy.FullTree.Vertex (E (e true)).tree)).trans <|
    (Equiv.sumCongr (Equiv.refl Unit)
      (twoBranchEquiv e fun c =>
        TreeAdequacy.FullTree.Vertex (E c).tree)).trans <|
      (Equiv.sumCongr (Equiv.refl Unit)
        (Equiv.sigmaCongrRight fun c => (E c).graphIso.toEquiv)).trans <|
        P.descendantsEquiv (P.leafVertex rootLabel) v

@[simp] theorem forkVertexEquiv_root (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1) :
    P.forkVertexEquiv rootLabel v e E (.inl (.inl ())) =
      ⟨v, Relation.ReflTransGen.refl⟩ := by
  rfl

@[simp] theorem forkVertexEquiv_left (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1)
    (x : TreeAdequacy.FullTree.Vertex (E (e false)).tree) :
    P.forkVertexEquiv rootLabel v e E (.inl (.inr x)) =
      ⟨((E (e false)).graphIso x).1,
        ((E (e false)).graphIso x).2.trans
          (.single (e false).2)⟩ := by
  rfl

@[simp] theorem forkVertexEquiv_right (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1)
    (x : TreeAdequacy.FullTree.Vertex (E (e true)).tree) :
    P.forkVertexEquiv rootLabel v e E (.inr x) =
      ⟨((E (e true)).graphIso x).1,
        ((E (e true)).graphIso x).2.trans
          (.single (e true).2)⟩ := by
  rfl

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

@[simp] theorem graph_fork_adj_root_left (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex l) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inl ())) (.inl (.inr x)) ↔
      x = TreeAdequacy.FullTree.rootVertex l := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_left_root (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex l) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inr x)) (.inl (.inl ())) ↔
      x = TreeAdequacy.FullTree.rootVertex l := by
  rw [SimpleGraph.adj_comm, graph_fork_adj_root_left]

@[simp] theorem graph_fork_adj_root_right (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex r) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inl (.inl ())) (.inr x) ↔
      x = TreeAdequacy.FullTree.rootVertex r := by
  simp [TreeAdequacy.FullTree.graph, SimpleGraph.edge_adj]

@[simp] theorem graph_fork_adj_right_root (l r : Tree.FullTree α)
    (x : TreeAdequacy.FullTree.Vertex r) :
    (TreeAdequacy.FullTree.graph (.fork l r)).Adj
        (.inr x) (.inl (.inl ())) ↔
      x = TreeAdequacy.FullTree.rootVertex r := by
  rw [SimpleGraph.adj_comm, graph_fork_adj_root_right]

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

noncomputable def leafSubtreeEncoding (P : BinaryPhyloGraph α V)
    (rootLabel : α) {v : V} (hv : v ≠ P.leafVertex rootLabel)
    (hdeg : P.G.degree v = 1) : P.SubtreeEncoding rootLabel v := by
  let a : α := P.labelOfLeaf v hdeg
  have haVertex : P.leafVertex a = v := P.leafVertex_labelOfLeaf v hdeg
  have ha : a ≠ rootLabel := by
    intro haroot
    apply hv
    rw [← haVertex, haroot]
  let b : {x : α // x ≠ rootLabel} := ⟨a, ha⟩
  let e : Unit ≃ P.Descendants (P.leafVertex rootLabel) v :=
    { toFun := fun _ => ⟨v, Relation.ReflTransGen.refl⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun w => by
        apply Subtype.ext
        exact (P.descendant_eq_of_degree_one hv hdeg w.2).symm }
  let gi : TreeAdequacy.FullTree.graph (.leaf b) ≃g
      P.G.induce {w : V |
        Relation.ReflTransGen (P.childRel (P.leafVertex rootLabel)) w v} :=
    { e with
      map_rel_iff' := by
        intro x y
        simp [TreeAdequacy.FullTree.graph, e] }
  refine
    { tree := .leaf b
      graphIso := gi
      root_eq := by rfl
      label_iff := ?_
      nodup_leaves := by simp
      mem_leaves_iff := ?_ }
  · intro x c
    have hx : x = () := Subsingleton.elim _ _
    subst x
    change some b = some c ↔ v = P.leafVertex c.1
    constructor
    · intro hbc
      have hbc' : b = c := Option.some.inj hbc
      subst c
      simpa [b] using haVertex.symm
    · intro hvc
      have hbc : b = c := by
        apply Subtype.ext
        apply P.leafVertex_injective
        calc
          P.leafVertex b.1 = v := by simpa [b] using haVertex
          _ = P.leafVertex c.1 := hvc
      simp [hbc]
  intro c
  simp only [Tree.FullTree.leaves_leaf, List.mem_singleton]
  constructor
  · intro hcb
    subst c
    change Relation.ReflTransGen
      (P.childRel (P.leafVertex rootLabel)) (P.leafVertex a) v
    rw [haVertex]
  · intro hc
    apply Subtype.ext
    apply P.leafVertex_injective
    calc
      P.leafVertex c.1 = v := P.descendant_eq_of_degree_one hv hdeg hc
      _ = P.leafVertex b.1 := by simpa [b] using haVertex.symm

/-- Join two encoded child branches at their parent, preserving the graph
exactly (including the two new parent-child edges). -/
noncomputable def forkGraphIso (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1) :
    TreeAdequacy.FullTree.graph
        (.fork (E (e false)).tree (E (e true)).tree) ≃g
      P.G.induce {w : V |
        Relation.ReflTransGen
          (P.childRel (P.leafVertex rootLabel)) w v} := by
  let ve := P.forkVertexEquiv rootLabel v e E
  refine { ve with map_rel_iff' := ?_ }
  intro x y
  have hne : (e false).1 ≠ (e true).1 := by
    intro h
    have heq : e false = e true := Subtype.ext h
    exact Bool.false_ne_true (e.injective heq)
  rcases x with ((ux | x) | x) <;> rcases y with ((uy | y) | y)
  · have hux : ux = () := Subsingleton.elim _ _
    have huy : uy = () := Subsingleton.elim _ _
    subst ux
    subst uy
    simp [ve]
  · have hux : ux = () := Subsingleton.elim _ _
    subst ux
    simp only [ve,
      SimpleGraph.induce_adj, graph_fork_adj_root_left]
    change P.G.Adj v ((E (e false)).graphIso y).1 ↔
      y = TreeAdequacy.FullTree.rootVertex (E (e false)).tree
    rw [P.adj_parent_descendant_iff (P.leafVertex rootLabel)
      (e false).2 ((E (e false)).graphIso y).2]
    constructor
    · intro hy
      apply (E (e false)).graphIso.injective
      apply Subtype.ext
      exact hy.trans (E (e false)).root_eq.symm
    · rintro rfl
      exact (E (e false)).root_eq
  · have hux : ux = () := Subsingleton.elim _ _
    subst ux
    simp only [ve,
      SimpleGraph.induce_adj, graph_fork_adj_root_right]
    change P.G.Adj v ((E (e true)).graphIso y).1 ↔
      y = TreeAdequacy.FullTree.rootVertex (E (e true)).tree
    rw [P.adj_parent_descendant_iff (P.leafVertex rootLabel)
      (e true).2 ((E (e true)).graphIso y).2]
    constructor
    · intro hy
      apply (E (e true)).graphIso.injective
      apply Subtype.ext
      exact hy.trans (E (e true)).root_eq.symm
    · rintro rfl
      exact (E (e true)).root_eq
  · have huy : uy = () := Subsingleton.elim _ _
    subst uy
    simp only [ve,
      SimpleGraph.induce_adj, graph_fork_adj_left_root]
    change P.G.Adj ((E (e false)).graphIso x).1 v ↔
      x = TreeAdequacy.FullTree.rootVertex (E (e false)).tree
    rw [SimpleGraph.adj_comm,
      P.adj_parent_descendant_iff (P.leafVertex rootLabel)
        (e false).2 ((E (e false)).graphIso x).2]
    constructor
    · intro hx
      apply (E (e false)).graphIso.injective
      apply Subtype.ext
      exact hx.trans (E (e false)).root_eq.symm
    · rintro rfl
      exact (E (e false)).root_eq
  · simp only [ve, SimpleGraph.induce_adj, graph_fork_adj_left_left]
    exact (E (e false)).graphIso.map_rel_iff'
  · simp only [ve,
      SimpleGraph.induce_adj, not_graph_fork_adj_left_right, iff_false]
    exact P.not_adj_descendants_of_distinct_children
      (P.leafVertex rootLabel) (e false).2 (e true).2 hne
      ((E (e false)).graphIso x).2 ((E (e true)).graphIso y).2
  · have huy : uy = () := Subsingleton.elim _ _
    subst uy
    simp only [ve,
      SimpleGraph.induce_adj, graph_fork_adj_right_root]
    change P.G.Adj ((E (e true)).graphIso x).1 v ↔
      x = TreeAdequacy.FullTree.rootVertex (E (e true)).tree
    rw [SimpleGraph.adj_comm,
      P.adj_parent_descendant_iff (P.leafVertex rootLabel)
        (e true).2 ((E (e true)).graphIso x).2]
    constructor
    · intro hx
      apply (E (e true)).graphIso.injective
      apply Subtype.ext
      exact hx.trans (E (e true)).root_eq.symm
    · rintro rfl
      exact (E (e true)).root_eq
  · simp only [ve,
      SimpleGraph.induce_adj, not_graph_fork_adj_right_left, iff_false]
    exact P.not_adj_descendants_of_distinct_children
      (P.leafVertex rootLabel) (e true).2 (e false).2 hne.symm
      ((E (e true)).graphIso x).2 ((E (e false)).graphIso y).2
  · simp only [ve, SimpleGraph.induce_adj, graph_fork_adj_right_right]
    exact (E (e true)).graphIso.map_rel_iff'

/-- At an internal vertex, a labelled leaf is a descendant exactly when it
is a descendant of one of the two children. -/
theorem leaf_descendant_iff_exists_child (P : BinaryPhyloGraph α V)
    (root : V) {v : V} (hdeg : P.G.degree v ≠ 1) (a : α) :
    Relation.ReflTransGen (P.childRel root) (P.leafVertex a) v ↔
      ∃ c : ↑(P.children root v),
        Relation.ReflTransGen (P.childRel root) (P.leafVertex a) c.1 := by
  constructor
  · intro h
    rcases h.cases_tail with heq | ⟨c, hac, hcv⟩
    · exfalso
      apply hdeg
      rw [heq, P.degree_leafVertex]
    · exact ⟨⟨c, hcv⟩, hac⟩
  · rintro ⟨c, hac⟩
    exact hac.trans (.single c.2)

/-- The internal-node constructor for the recursive encoding. -/
noncomputable def forkSubtreeEncoding (P : BinaryPhyloGraph α V)
    (rootLabel : α) {v : V} (hdeg : P.G.degree v ≠ 1)
    (e : Bool ≃ ↑(P.children (P.leafVertex rootLabel) v))
    (E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
      P.SubtreeEncoding rootLabel c.1) :
    P.SubtreeEncoding rootLabel v := by
  let L := E (e false)
  let R := E (e true)
  let gi := P.forkGraphIso rootLabel v e E
  have hne : (e false).1 ≠ (e true).1 := by
    intro h
    have heq : e false = e true := Subtype.ext h
    exact Bool.false_ne_true (e.injective heq)
  refine
    { tree := .fork L.tree R.tree
      graphIso := gi
      root_eq := ?_
      label_iff := ?_
      nodup_leaves := ?_
      mem_leaves_iff := ?_ }
  · rfl
  · intro x a
    rcases x with ((u | x) | x)
    · have hu : u = () := Subsingleton.elim _ _
      subst u
      change none = some a ↔ v = P.leafVertex a.1
      constructor
      · intro h
        cases h
      · intro hva
        exfalso
        apply hdeg
        rw [hva, P.degree_leafVertex]
    · change TreeAdequacy.FullTree.label? L.tree x = some a ↔
        (L.graphIso x).1 = P.leafVertex a.1
      exact L.label_iff x a
    · change TreeAdequacy.FullTree.label? R.tree x = some a ↔
        (R.graphIso x).1 = P.leafVertex a.1
      exact R.label_iff x a
  · rw [Tree.FullTree.leaves_fork, List.nodup_append]
    refine ⟨L.nodup_leaves, R.nodup_leaves, ?_⟩
    intro a ha b hb hab
    subst b
    have haL := (L.mem_leaves_iff a).mp ha
    have haR := (R.mem_leaves_iff a).mp hb
    exact hne <| P.descendant_branch_unique (P.leafVertex rootLabel)
      haL haR (e false).2 (e true).2
  · intro a
    rw [Tree.FullTree.leaves_fork, List.mem_append]
    constructor
    · rintro (ha | ha)
      · exact ((L.mem_leaves_iff a).mp ha).trans (.single (e false).2)
      · exact ((R.mem_leaves_iff a).mp ha).trans (.single (e true).2)
    · intro ha
      obtain ⟨c, hac⟩ :=
        (P.leaf_descendant_iff_exists_child
          (P.leafVertex rootLabel) hdeg a.1).mp ha
      obtain ⟨b, rfl⟩ := e.surjective c
      cases b with
      | false => exact Or.inl ((L.mem_leaves_iff a).mpr hac)
      | true => exact Or.inr ((R.mem_leaves_iff a).mpr hac)

/-- Well-founded recursion down the distance orientation produces an exact
encoding of every non-root descendant subtree. -/
theorem exists_subtreeEncoding (P : BinaryPhyloGraph α V)
    (rootLabel : α) (v : V) (hv : v ≠ P.leafVertex rootLabel) :
    Nonempty (P.SubtreeEncoding rootLabel v) := by
  revert hv
  apply (P.childRel_wellFounded (P.leafVertex rootLabel)).induction v
  intro v ih hv
  by_cases hdeg : P.G.degree v = 1
  · exact ⟨P.leafSubtreeEncoding rootLabel hv hdeg⟩
  · have hcard := P.card_children_of_internal hv hdeg
    let e := P.childrenBoolEquiv (P.leafVertex rootLabel) v hcard
    let E : ∀ c : ↑(P.children (P.leafVertex rootLabel) v),
        P.SubtreeEncoding rootLabel c.1 := fun c =>
      Classical.choice (ih c.1 c.2 (P.child_ne_root (c := c)))
    exact ⟨P.forkSubtreeEncoding rootLabel hdeg e E⟩

/-- The encoded crown obtained by deleting the distinguished labelled leaf. -/
noncomputable def crownEncoding (P : BinaryPhyloGraph α V)
    (rootLabel : α) : P.SubtreeEncoding rootLabel (P.rootNeighbor rootLabel) :=
  Classical.choice <| P.exists_subtreeEncoding rootLabel
    (P.rootNeighbor rootLabel) (P.rootNeighbor_ne_root rootLabel)

/-- Convert an independently presented binary phylogenetic graph into the
cut-open syntax used by the counting development. -/
noncomputable def encode (P : BinaryPhyloGraph α V) (rootLabel : α) :
    Tree.PhyloTree α where
  root := rootLabel
  crown := (P.crownEncoding rootLabel).tree
  nodup_leaves := (P.crownEncoding rootLabel).nodup_leaves
  exhaustive := by
    intro a
    apply ((P.crownEncoding rootLabel).mem_leaves_iff a).mpr
    apply (P.mem_descendants_rootNeighbor_iff rootLabel
      (P.leafVertex a.1)).mpr
    intro h
    exact a.2 (P.leafVertex_injective h)

/-- Adjoin a singled-out point to its complement. -/
def attachRootEquiv (root : V) : Unit ⊕ {w : V // w ≠ root} ≃ V where
  toFun
    | .inl _ => root
    | .inr w => w.1
  invFun w := if h : w = root then .inl () else .inr ⟨w, h⟩
  left_inv x := by
    rcases x with (u | w)
    · have hu : u = () := Subsingleton.elim _ _
      subst u
      simp
    · simp [w.2]
  right_inv w := by
    by_cases h : w = root
    · simp [h]
    · simp [h]

/-- The recursively built crown realizes exactly the induced subgraph on
all vertices other than the distinguished root leaf. -/
noncomputable def crownGraphIso (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    TreeAdequacy.FullTree.graph (P.encode rootLabel).crown ≃g
      P.G.induce {w : V | w ≠ P.leafVertex rootLabel} := by
  let C := P.crownEncoding rootLabel
  have hp : (fun w : V =>
      Relation.ReflTransGen (P.childRel (P.leafVertex rootLabel)) w
        (P.rootNeighbor rootLabel)) =
      (fun w : V => w ≠ P.leafVertex rootLabel) := by
    funext w
    exact propext (P.mem_descendants_rootNeighbor_iff rootLabel w)
  let se : P.Descendants (P.leafVertex rootLabel)
        (P.rootNeighbor rootLabel) ≃
      {w : V // w ≠ P.leafVertex rootLabel} :=
    Equiv.subtypeEquivProp hp
  let ve := C.graphIso.toEquiv.trans se
  refine { ve with map_rel_iff' := ?_ }
  intro x y
  change P.G.Adj (C.graphIso x).1 (C.graphIso y).1 ↔
    (TreeAdequacy.FullTree.graph C.tree).Adj x y
  exact C.graphIso.map_rel_iff'

@[simp] theorem crownGraphIso_root (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    ((P.crownGraphIso rootLabel)
      (TreeAdequacy.FullTree.rootVertex (P.encode rootLabel).crown)).1 =
      P.rootNeighbor rootLabel := by
  exact (P.crownEncoding rootLabel).root_eq

theorem adj_root_iff_rootNeighbor (P : BinaryPhyloGraph α V)
    (a : α) (w : V) :
    P.G.Adj (P.leafVertex a) w ↔ w = P.rootNeighbor a := by
  constructor
  · exact (degree_eq_one_iff_existsUnique_adj.mp
      (P.degree_leafVertex a)).choose_spec.2 w
  · rintro rfl
    exact P.root_adj_rootNeighbor a

/-- Vertex equivalence underlying the final graph isomorphism. -/
noncomputable def encodeVertexEquiv (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    TreeAdequacy.PhyloTree.Vertex (P.encode rootLabel) ≃ V :=
  (Equiv.sumCongr (Equiv.refl Unit)
    (P.crownGraphIso rootLabel).toEquiv).trans
      (attachRootEquiv (P.leafVertex rootLabel))

@[simp] theorem encodeVertexEquiv_root (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    P.encodeVertexEquiv rootLabel (.inl ()) = P.leafVertex rootLabel := by
  rfl

@[simp] theorem encodeVertexEquiv_crown (P : BinaryPhyloGraph α V)
    (rootLabel : α)
    (x : TreeAdequacy.FullTree.Vertex (P.encode rootLabel).crown) :
    P.encodeVertexEquiv rootLabel (.inr x) =
      ((P.crownGraphIso rootLabel) x).1 := by
  rfl

@[simp] theorem phyloGraph_adj_root_crown (T : Tree.PhyloTree α)
    (x : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inl ()) (.inr x) ↔
      x = TreeAdequacy.FullTree.rootVertex T.crown := by
  simp [TreeAdequacy.PhyloTree.graph, SimpleGraph.edge_adj]

@[simp] theorem phyloGraph_adj_crown_root (T : Tree.PhyloTree α)
    (x : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inr x) (.inl ()) ↔
      x = TreeAdequacy.FullTree.rootVertex T.crown := by
  rw [SimpleGraph.adj_comm, phyloGraph_adj_root_crown]

@[simp] theorem phyloGraph_adj_crown_crown (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.FullTree.Vertex T.crown) :
    (TreeAdequacy.PhyloTree.graph T).Adj (.inr x) (.inr y) ↔
      (TreeAdequacy.FullTree.graph T.crown).Adj x y := by
  simp [TreeAdequacy.PhyloTree.graph, SimpleGraph.edge_adj]

/-- Main closure theorem: the syntax obtained from an independent finite
binary phylogenetic graph realizes to a graph isomorphic to the original. -/
noncomputable def encodeGraphIso (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    TreeAdequacy.PhyloTree.graph (P.encode rootLabel) ≃g P.G := by
  let ve := P.encodeVertexEquiv rootLabel
  refine { ve with map_rel_iff' := ?_ }
  intro x y
  rcases x with (ux | x) <;> rcases y with (uy | y)
  · have hux : ux = () := Subsingleton.elim _ _
    have huy : uy = () := Subsingleton.elim _ _
    subst ux
    subst uy
    simp [ve]
  · have hux : ux = () := Subsingleton.elim _ _
    subst ux
    simp only [ve, phyloGraph_adj_root_crown]
    change P.G.Adj (P.leafVertex rootLabel)
        ((P.crownGraphIso rootLabel) y).1 ↔
      y = TreeAdequacy.FullTree.rootVertex (P.encode rootLabel).crown
    rw [P.adj_root_iff_rootNeighbor rootLabel]
    constructor
    · intro hy
      apply (P.crownGraphIso rootLabel).injective
      apply Subtype.ext
      exact hy.trans (P.crownGraphIso_root rootLabel).symm
    · rintro rfl
      exact P.crownGraphIso_root rootLabel
  · have huy : uy = () := Subsingleton.elim _ _
    subst uy
    simp only [ve, phyloGraph_adj_crown_root]
    change P.G.Adj ((P.crownGraphIso rootLabel) x).1
        (P.leafVertex rootLabel) ↔
      x = TreeAdequacy.FullTree.rootVertex (P.encode rootLabel).crown
    rw [SimpleGraph.adj_comm, P.adj_root_iff_rootNeighbor rootLabel]
    constructor
    · intro hx
      apply (P.crownGraphIso rootLabel).injective
      apply Subtype.ext
      exact hx.trans (P.crownGraphIso_root rootLabel).symm
    · rintro rfl
      exact P.crownGraphIso_root rootLabel
  · simp only [ve, phyloGraph_adj_crown_crown]
    exact (P.crownGraphIso rootLabel).map_rel_iff'

@[simp] theorem encodeGraphIso_root (P : BinaryPhyloGraph α V)
    (rootLabel : α) :
    P.encodeGraphIso rootLabel (.inl ()) = P.leafVertex rootLabel := by
  rfl

@[simp] theorem encodeGraphIso_crown (P : BinaryPhyloGraph α V)
    (rootLabel : α)
    (x : TreeAdequacy.FullTree.Vertex (P.encode rootLabel).crown) :
    P.encodeGraphIso rootLabel (.inr x) =
      ((P.crownGraphIso rootLabel) x).1 := by
  rfl

/-- The final graph isomorphism preserves every taxon label, not merely the
unlabelled graph structure. -/
theorem encodeGraphIso_label_iff (P : BinaryPhyloGraph α V)
    (rootLabel a : α)
    (x : TreeAdequacy.PhyloTree.Vertex (P.encode rootLabel)) :
    TreeAdequacy.PhyloTree.label? (P.encode rootLabel) x = some a ↔
      P.encodeGraphIso rootLabel x = P.leafVertex a := by
  rcases x with (u | x)
  · have hu : u = () := Subsingleton.elim _ _
    subst u
    change some rootLabel = some a ↔
      P.leafVertex rootLabel = P.leafVertex a
    constructor
    · intro h
      have ha : rootLabel = a := Option.some.inj h
      exact congrArg P.leafVertex ha
    · intro h
      exact congrArg some (P.leafVertex_injective h)
  · change
      (TreeAdequacy.FullTree.label?
        (P.crownEncoding rootLabel).tree x).map Subtype.val = some a ↔
        ((P.crownGraphIso rootLabel) x).1 = P.leafVertex a
    by_cases ha : a = rootLabel
    · subst a
      constructor
      · intro hlabel
        rw [Option.map_eq_some_iff] at hlabel
        obtain ⟨b, -, hb⟩ := hlabel
        exact (b.2 hb).elim
      · intro hroot
        exact ((P.crownGraphIso rootLabel) x).2 hroot |>.elim
    · let b : {a : α // a ≠ rootLabel} := ⟨a, ha⟩
      have hmap :
          (TreeAdequacy.FullTree.label?
            (P.crownEncoding rootLabel).tree x).map Subtype.val = some a ↔
          TreeAdequacy.FullTree.label?
            (P.crownEncoding rootLabel).tree x = some b := by
        constructor
        · intro h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨c, hc, hca⟩ := h
          have hcb : c = b := Subtype.ext hca
          simpa [hcb] using hc
        · intro h
          rw [h]
          rfl
      rw [hmap]
      change TreeAdequacy.FullTree.label?
          (P.crownEncoding rootLabel).tree x = some b ↔
        ((P.crownEncoding rootLabel).graphIso x).1 =
          P.leafVertex b.1
      exact (P.crownEncoding rootLabel).label_iff x b

end Encoding

end BinaryPhyloGraph
end GraphModel
end QuartetDistance

namespace QuartetDistance
namespace GraphModel
namespace Syntax

open SimpleGraph

variable {α : Type*}

/-- A vertex carrying a full-tree label witnesses membership of that label
in the syntactic leaf list. -/
theorem fullTree_label_mem_leaves (t : Tree.FullTree α)
    {x : TreeAdequacy.FullTree.Vertex t} {a : α}
    (hx : TreeAdequacy.FullTree.label? t x = some a) :
    a ∈ t.leaves := by
  induction t with
  | leaf b =>
      have hba : b = a := Option.some.inj hx
      simp [hba]
  | fork l r ihl ihr =>
      rcases x with ((u | x) | x)
      · cases hx
      · rw [Tree.FullTree.leaves_fork, List.mem_append]
        exact Or.inl (ihl hx)
      · rw [Tree.FullTree.leaves_fork, List.mem_append]
        exact Or.inr (ihr hx)

/-- With no repeated leaves, a full-tree label occurs at a unique graph
vertex. -/
theorem fullTree_label_unique_of_nodup (t : Tree.FullTree α)
    (hn : t.leaves.Nodup)
    {x y : TreeAdequacy.FullTree.Vertex t} {a : α}
    (hx : TreeAdequacy.FullTree.label? t x = some a)
    (hy : TreeAdequacy.FullTree.label? t y = some a) : x = y := by
  induction t with
  | leaf b => exact Subsingleton.elim _ _
  | fork l r ihl ihr =>
      rw [Tree.FullTree.leaves_fork, List.nodup_append] at hn
      rcases hn with ⟨hnl, hnr, hcross⟩
      rcases x with ((ux | x) | x) <;> rcases y with ((uy | y) | y)
      · rfl
      · cases hx
      · cases hx
      · cases hy
      · exact congrArg (fun z => Sum.inl (Sum.inr z))
          (ihl hnl hx hy)
      · exfalso
        exact hcross a (fullTree_label_mem_leaves l hx)
          a (fullTree_label_mem_leaves r hy) rfl
      · cases hy
      · exfalso
        exact hcross a (fullTree_label_mem_leaves l hy)
          a (fullTree_label_mem_leaves r hx) rfl
      · exact congrArg Sum.inr (ihr hnr hx hy)

end Syntax
end GraphModel

namespace Tree
namespace PhyloTree

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable local instance syntaxFiniteNeighborSet
    {W : Type*} [Fintype W] (G : SimpleGraph W) (v : W) :
    Fintype (G.neighborSet v) := Fintype.ofFinite _

/-- Labels in a valid phylogenetic syntax tree occur at unique realization
vertices. -/
theorem label_unique (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T} {a : α}
    (hx : TreeAdequacy.PhyloTree.label? T x = some a)
    (hy : TreeAdequacy.PhyloTree.label? T y = some a) : x = y := by
  rcases x with (ux | x) <;> rcases y with (uy | y)
  · rfl
  · have hux : ux = () := Subsingleton.elim _ _
    subst ux
    change some T.root = some a at hx
    change (TreeAdequacy.FullTree.label? T.crown y).map Subtype.val =
      some a at hy
    have haroot : a = T.root := (Option.some.inj hx).symm
    rw [Option.map_eq_some_iff] at hy
    obtain ⟨b, -, hba⟩ := hy
    exact (b.2 (hba.trans haroot)).elim
  · have huy : uy = () := Subsingleton.elim _ _
    subst uy
    change (TreeAdequacy.FullTree.label? T.crown x).map Subtype.val =
      some a at hx
    change some T.root = some a at hy
    have haroot : a = T.root := (Option.some.inj hy).symm
    rw [Option.map_eq_some_iff] at hx
    obtain ⟨b, -, hba⟩ := hx
    exact (b.2 (hba.trans haroot)).elim
  · change (TreeAdequacy.FullTree.label? T.crown x).map Subtype.val =
      some a at hx
    change (TreeAdequacy.FullTree.label? T.crown y).map Subtype.val =
      some a at hy
    rw [Option.map_eq_some_iff] at hx hy
    obtain ⟨b, hxb, hba⟩ := hx
    obtain ⟨c, hyc, hca⟩ := hy
    have hbc : b = c := Subtype.ext (hba.trans hca.symm)
    subst c
    exact congrArg Sum.inr <|
      GraphModel.Syntax.fullTree_label_unique_of_nodup
        T.crown T.nodup_leaves hxb hyc

/-- The realization vertex carrying a given taxon. -/
noncomputable def labelledVertex (T : Tree.PhyloTree α) (a : α) :
    TreeAdequacy.PhyloTree.Vertex T :=
  Classical.choose (TreeAdequacy.PhyloTree.exists_vertex_label T a)

@[simp] theorem label_labelledVertex (T : Tree.PhyloTree α) (a : α) :
    TreeAdequacy.PhyloTree.label? T (T.labelledVertex a) = some a :=
  Classical.choose_spec (TreeAdequacy.PhyloTree.exists_vertex_label T a)

theorem labelledVertex_injective (T : Tree.PhyloTree α) :
    Function.Injective T.labelledVertex := by
  intro a b hab
  have h := T.label_labelledVertex a
  rw [hab, T.label_labelledVertex b] at h
  exact (Option.some.inj h).symm

/-- Taxa are equivalent to precisely the degree-one vertices of the syntax
realization. -/
noncomputable def leafEquiv (T : Tree.PhyloTree α) :
    α ≃ {v : TreeAdequacy.PhyloTree.Vertex T //
      (TreeAdequacy.PhyloTree.graph T).degree v = 1} :=
  Equiv.ofBijective
    (fun a => ⟨T.labelledVertex a,
      (TreeAdequacy.PhyloTree.degree_eq_one_iff T _).mpr
        (by rw [T.label_labelledVertex a]; rfl)⟩)
    ⟨fun a b h => T.labelledVertex_injective (congrArg Subtype.val h), by
      intro v
      have hs := (TreeAdequacy.PhyloTree.degree_eq_one_iff T v.1).mp v.2
      rw [Option.isSome_iff_exists] at hs
      obtain ⟨a, ha⟩ := hs
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact T.label_unique (T.label_labelledVertex a) ha⟩

@[simp] theorem leafEquiv_val (T : Tree.PhyloTree α) (a : α) :
    (T.leafEquiv a).1 = T.labelledVertex a := by
  rfl

@[simp] theorem label_leafEquiv (T : Tree.PhyloTree α) (a : α) :
    TreeAdequacy.PhyloTree.label? T (T.leafEquiv a).1 = some a := by
  exact T.label_labelledVertex a

/-- Every syntactic phylogenetic tree is an independent binary phylogenetic
graph, with no loss or permutation of labels. -/
noncomputable def toBinaryPhyloGraph (T : Tree.PhyloTree α) :
    GraphModel.BinaryPhyloGraph α (TreeAdequacy.PhyloTree.Vertex T) where
  G := TreeAdequacy.PhyloTree.graph T
  isTree := TreeAdequacy.PhyloTree.graph_isTree T
  leafEquiv := T.leafEquiv
  internal_degree := by
    intro v hv
    rw [TreeAdequacy.PhyloTree.degree_profile]
    by_cases hlabel : (TreeAdequacy.PhyloTree.label? T v).isSome
    · exfalso
      apply hv
      rw [TreeAdequacy.PhyloTree.degree_profile, if_pos hlabel]
    · rw [if_neg hlabel]

@[simp] theorem toBinaryPhyloGraph_G (T : Tree.PhyloTree α) :
    T.toBinaryPhyloGraph.G = TreeAdequacy.PhyloTree.graph T := rfl

@[simp] theorem toBinaryPhyloGraph_leafVertex (T : Tree.PhyloTree α)
    (a : α) :
    T.toBinaryPhyloGraph.leafVertex a = T.labelledVertex a := rfl

@[simp] theorem toBinaryPhyloGraph_label (T : Tree.PhyloTree α)
    (a : α) :
    TreeAdequacy.PhyloTree.label? T
      (T.toBinaryPhyloGraph.leafVertex a) = some a := by
  exact T.label_labelledVertex a

end PhyloTree
end Tree
end QuartetDistance
