import QuartetDistance.Upper

/-!
# The random-labelling lower bound

This file proves the elementary lower half of the Bandelt--Dress estimate.
Relabelling is defined on the concrete rooted-tree model, and a three-cycle
supported on a fixed quartet gives a free cyclic action on its three displayed
topology channels.  Consequently every fixed quartet has the exact uniform
`8/24` local law (and its global-permutation analogue), so one relabelling has
distance at least two thirds of all quartets.
-/

namespace QuartetDistance.Lower

open Tree

universe u v w

/-! ## Relabelling concrete rooted phylogenetic trees -/

/-- An equivalence carries the labels different from `r` to the labels
different from `e r`. -/
def awayEquiv (e : α ≃ β) (r : α) :
    {a : α // a ≠ r} ≃ {b : β // b ≠ e r} where
  toFun a := ⟨e a.1, fun h => a.2 (e.injective h)⟩
  invFun b := ⟨e.symm b.1, fun h => b.2 (by simpa using congrArg e h)⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp

@[simp] theorem awayEquiv_coe (e : α ≃ β) (r : α) (a : {a : α // a ≠ r}) :
    (awayEquiv e r a : β) = e a := rfl

/-- Relabel every leaf of a rooted phylogenetic tree by an equivalence. -/
def relabel [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (T : PhyloTree α) : PhyloTree β where
  root := e T.root
  crown := T.crown.map (awayEquiv e T.root)
  nodup_leaves := by
    rw [Tree.FullTree.leaves_map]
    exact T.nodup_leaves.map (awayEquiv e T.root).injective
  exhaustive := by
    intro b
    let a : {a : α // a ≠ T.root} := (awayEquiv e T.root).symm b
    have ha := T.exhaustive a
    rw [Tree.FullTree.leaves_map, List.mem_map]
    exact ⟨a, ha, (awayEquiv e T.root).apply_symm_apply b⟩

@[simp] theorem relabel_root [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α) :
    (relabel e T).root = e T.root := rfl

private theorem fullTree_map_congr {α : Type u} {β : Type v} {f g : α → β}
    (h : ∀ a, f a = g a) (t : FullTree α) : t.map f = t.map g := by
  induction t with
  | leaf a => simp [Tree.FullTree.map, h a]
  | fork l r ihl ihr => simp [Tree.FullTree.map, ihl, ihr]

private theorem fullTree_map_map {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g : β → γ)
    (t : FullTree α) : (t.map f).map g = t.map (g ∘ f) := by
  induction t with
  | leaf => rfl
  | fork l r ihl ihr => simp [Tree.FullTree.map, ihl, ihr]

private theorem fullTree_map_id (t : FullTree α) : t.map id = t := by
  induction t with
  | leaf => rfl
  | fork l r ihl ihr => simp [Tree.FullTree.map, ihl, ihr]

@[simp] theorem relabel_refl [Fintype α] [DecidableEq α]
    (T : PhyloTree α) : relabel (Equiv.refl α) T = T := by
  cases T with
  | mk root crown nodup exhaustive =>
      simp only [relabel]
      congr 1
      calc
        crown.map (awayEquiv (Equiv.refl α) root) = crown.map id := by
          apply fullTree_map_congr
          intro a
          exact Subtype.ext (by rfl)
        _ = crown := fullTree_map_id crown

theorem relabel_trans [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (e : α ≃ β) (f : β ≃ γ) (T : PhyloTree α) :
    relabel f (relabel e T) = relabel (e.trans f) T := by
  cases T with
  | mk root crown nodup exhaustive =>
      simp only [relabel]
      congr 1
      rw [fullTree_map_map]
      apply fullTree_map_congr
      intro a
      exact Subtype.ext (by rfl)

/-! ## Naturality of restriction and displayed quartet splits -/

theorem prune_map_equiv [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (t : FullTree α) (S : Finset α) :
    (t.map e).prune (S.map e.toEmbedding) =
      (t.prune S).map (fun u => u.map e) := by
  induction t with
  | leaf a => simp [Tree.FullTree.map, Tree.FullTree.prune]
  | fork l r ihl ihr =>
      simp only [Tree.FullTree.map, Tree.FullTree.prune, ihl, ihr]
      cases l.prune S <;> cases r.prune S <;> rfl

theorem asFullTree_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α) :
    (relabel e T).asFullTree = T.asFullTree.map e := by
  cases T with
  | mk root crown nodup exhaustive =>
      simp only [relabel, Tree.PhyloTree.asFullTree, Tree.FullTree.map]
      congr 1
      rw [fullTree_map_map, fullTree_map_map]
      apply fullTree_map_congr
      intro a
      rfl

theorem mapSplit_blockSplit [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b c d : α) :
    Circular.mapSplit e.toEmbedding (Tree.FullTree.blockSplit a b c d) =
      Tree.FullTree.blockSplit (e a) (e b) (e c) (e d) := by
  ext A
  simp [Tree.FullTree.blockSplit, Circular.mapSplit, Circular.splitOf,
    Circular.pair]

/-- On a genuine four-leaf tree, applying an equivalence to all leaf labels
applies the same equivalence to its displayed split. -/
theorem displayedSplit_map_equiv [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (t : FullTree α)
    (hlen : t.leaves.length = 4) (hnodup : t.leaves.Nodup) :
    (t.map e).displayedSplit =
      Circular.mapSplit e.toEmbedding t.displayedSplit := by
  obtain ⟨a, b, c, d, hs⟩ := Tree.FullTree.shape_of_leaves_length_eq_four t hlen
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_three a b c d hn]
    rw [show (FullTree.fork (FullTree.leaf a)
        (FullTree.fork (FullTree.leaf b) (FullTree.fork (FullTree.leaf c)
          (FullTree.leaf d)))).map e =
        FullTree.fork (FullTree.leaf (e a))
          (FullTree.fork (FullTree.leaf (e b))
            (FullTree.fork (FullTree.leaf (e c)) (FullTree.leaf (e d)))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_one_three]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_twone a b c d hn]
    rw [show (FullTree.fork (FullTree.leaf a)
        (FullTree.fork (FullTree.fork (FullTree.leaf b) (FullTree.leaf c))
          (FullTree.leaf d))).map e =
        FullTree.fork (FullTree.leaf (e a))
          (FullTree.fork (FullTree.fork (FullTree.leaf (e b))
            (FullTree.leaf (e c))) (FullTree.leaf (e d))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_one_twone]
    · exact (mapSplit_blockSplit e a d b c).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_two_two a b c d hn]
    rw [show (FullTree.fork (FullTree.fork (FullTree.leaf a) (FullTree.leaf b))
        (FullTree.fork (FullTree.leaf c) (FullTree.leaf d))).map e =
        FullTree.fork (FullTree.fork (FullTree.leaf (e a)) (FullTree.leaf (e b)))
          (FullTree.fork (FullTree.leaf (e c)) (FullTree.leaf (e d))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_two_two]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one a b c d hn]
    rw [show (FullTree.fork
        (FullTree.fork (FullTree.leaf a)
          (FullTree.fork (FullTree.leaf b) (FullTree.leaf c)))
        (FullTree.leaf d)).map e =
        FullTree.fork
          (FullTree.fork (FullTree.leaf (e a))
            (FullTree.fork (FullTree.leaf (e b)) (FullTree.leaf (e c))))
          (FullTree.leaf (e d)) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one]
    · exact (mapSplit_blockSplit e a d b c).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_three_one a b c d hn]
    rw [show (FullTree.fork
        (FullTree.fork (FullTree.fork (FullTree.leaf a) (FullTree.leaf b))
          (FullTree.leaf c)) (FullTree.leaf d)).map e =
        FullTree.fork
          (FullTree.fork (FullTree.fork (FullTree.leaf (e a))
            (FullTree.leaf (e b))) (FullTree.leaf (e c)))
          (FullTree.leaf (e d)) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_three_one]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective

theorem restrictedTree_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    (relabel e T).restrictedTree (Q.map e.toEmbedding)
        (by simpa using hQ) =
      (T.restrictedTree Q hQ).map e := by
  have hm := prune_map_equiv e T.asFullTree Q
  rw [← asFullTree_relabel e T] at hm
  rw [(relabel e T).prune_asFullTree_eq_restrictedTree
      (Q.map e.toEmbedding) (by simpa using hQ),
    T.prune_asFullTree_eq_restrictedTree Q hQ] at hm
  simpa using hm

/-- Relabelling transports the true split on an image quartet. -/
theorem displayedSplitOn_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    (relabel e T).displayedSplitOn (Q.map e.toEmbedding)
        (by simpa using hQ) =
      Circular.mapSplit e.toEmbedding (T.displayedSplitOn Q hQ) := by
  unfold Tree.PhyloTree.displayedSplitOn
  rw [restrictedTree_relabel]
  exact displayedSplit_map_equiv e (T.restrictedTree Q hQ)
    (T.restrictedTree_leaves_length Q hQ) (T.restrictedTree_nodup Q hQ)

theorem blockSplit_isQuartetSplit [DecidableEq α] (a b c d : α)
    (hn : [a, b, c, d].Nodup) :
    Circular.IsQuartetSplit [a, b, c, d].toFinset
      (Tree.FullTree.blockSplit a b c d) := by
  have hn' : [a, c, b, d].Nodup := by
    simp only [List.nodup_cons] at hn ⊢
    aesop
  have h := Upper.crossingList_isQuartetSplit [a, c, b, d] (by simp) hn'
  have hset : [a, c, b, d].toFinset = [a, b, c, d].toFinset := by
    ext x
    simp
    aesop
  rw [hset] at h
  simpa [Tree.FullTree.crossingList, Tree.FullTree.blockSplit] using h

theorem displayedSplit_isQuartetSplit [DecidableEq α] (t : FullTree α)
    (hlen : t.leaves.length = 4) (hnodup : t.leaves.Nodup) :
    Circular.IsQuartetSplit t.leaves.toFinset t.displayedSplit := by
  obtain ⟨a, b, c, d, hs⟩ := Tree.FullTree.shape_of_leaves_length_eq_four t hlen
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_three a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_twone a b c d hn]
    have hn' : [a, d, b, c].Nodup := by
      simp only [List.nodup_cons] at hn ⊢
      aesop
    have h := blockSplit_isQuartetSplit a d b c hn'
    have hset : [a, d, b, c].toFinset = [a, b, c, d].toFinset := by
      ext x
      simp
      aesop
    rw [hset] at h
    simpa [Tree.FullTree.leaves] using h
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_two_two a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one a b c d hn]
    have hn' : [a, d, b, c].Nodup := by
      simp only [List.nodup_cons] at hn ⊢
      aesop
    have h := blockSplit_isQuartetSplit a d b c hn'
    have hset : [a, d, b, c].toFinset = [a, b, c, d].toFinset := by
      ext x
      simp
      aesop
    rw [hset] at h
    simpa [Tree.FullTree.leaves] using h
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_three_one a b c d hn]
    simpa [Tree.FullTree.leaves] using blockSplit_isQuartetSplit a b c d hn

theorem restrictedTree_toFinset [Fintype α] [DecidableEq α]
    (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    (T.restrictedTree Q hQ).leaves.toFinset = Q := by
  rw [T.restrictedTree_leaves Q hQ]
  ext a
  simp [Tree.FullTree.restrictList, T.mem_referenceLeaves a]

theorem displayedSplitOn_isQuartetSplit [Fintype α] [DecidableEq α]
    (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    Circular.IsQuartetSplit Q (T.displayedSplitOn Q hQ) := by
  have h := displayedSplit_isQuartetSplit (T.restrictedTree Q hQ)
    (T.restrictedTree_leaves_length Q hQ) (T.restrictedTree_nodup Q hQ)
  rw [restrictedTree_toFinset T Q hQ] at h
  exact h

/-! ## The three-cycle supported on one quartet -/

/-- Fix slot `0` and cycle the other three slots. -/
def slotCycle : Circular.Perm4 :=
  Circular.perm4OfTuples 0 2 3 1 0 3 1 2 (by decide) (by decide)

/-- The induced cycle of the three canonical topology channels. -/
def topologyCycle : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

theorem slotCycle_canonicalTopology (i : Fin 3) :
    Circular.mapSplit slotCycle.toEmbedding (Upper.canonicalTopology i) =
      Upper.canonicalTopology (topologyCycle i) := by
  fin_cases i <;> decide

/-- Extend `slotCycle` by the identity away from the range of `q`. -/
noncomputable def quartetCycle (q : Upper.Quartet n) : Equiv.Perm (Fin n) :=
  slotCycle.extendDomain (Upper.quartetEmbedding q).toEquivRange

@[simp] theorem quartetCycle_apply (q : Upper.Quartet n) (i : Circular.Four) :
    quartetCycle q (Upper.quartetEmbedding q i) =
      Upper.quartetEmbedding q (slotCycle i) := by
  exact Equiv.Perm.extendDomain_apply_image slotCycle
    (Upper.quartetEmbedding q).toEquivRange i

theorem quartetEmbedding_trans_quartetCycle (q : Upper.Quartet n) :
    (Upper.quartetEmbedding q).trans (quartetCycle q).toEmbedding =
      slotCycle.toEmbedding.trans (Upper.quartetEmbedding q) := by
  apply Function.Embedding.ext
  intro i
  exact quartetCycle_apply q i

theorem quartet_map_quartetCycle (q : Upper.Quartet n) :
    q.1.map (quartetCycle q).toEmbedding = q.1 := by
  calc
    q.1.map (quartetCycle q).toEmbedding =
        (Finset.univ.map (Upper.quartetEmbedding q)).map
          (quartetCycle q).toEmbedding := by
            exact congrArg (fun S : Finset (Fin n) =>
              S.map (quartetCycle q).toEmbedding)
              (Circular.range_enumerateFour q.1 q.2).symm
    _ = Finset.univ.map ((Upper.quartetEmbedding q).trans
          (quartetCycle q).toEmbedding) := Finset.map_map _ _ _
    _ = Finset.univ.map (slotCycle.toEmbedding.trans
          (Upper.quartetEmbedding q)) := by
            rw [quartetEmbedding_trans_quartetCycle]
    _ = (Finset.univ.map slotCycle.toEmbedding).map
          (Upper.quartetEmbedding q) := (Finset.map_map _ _ _).symm
    _ = Finset.univ.map (Upper.quartetEmbedding q) := by simp
    _ = q.1 := Circular.range_enumerateFour q.1 q.2

theorem quartetCycle_splitOfTopology (q : Upper.Quartet n) (i : Fin 3) :
    Circular.mapSplit (quartetCycle q).toEmbedding
        (Upper.splitOfTopology q i) =
      Upper.splitOfTopology q (topologyCycle i) := by
  unfold Upper.splitOfTopology
  rw [Circular.mapSplit_mapSplit, quartetEmbedding_trans_quartetCycle,
    ← Circular.mapSplit_mapSplit, slotCycle_canonicalTopology]

theorem displayedSplitOn_mem_topologyRange (T : PhyloTree (Fin n))
    (q : Upper.Quartet n) :
    T.displayedSplitOn q.1 q.2 ∈ Set.range (Upper.splitOfTopology q) :=
  Upper.isQuartetSplit_mem_range q
    (displayedSplitOn_isQuartetSplit T q.1 q.2)

@[simp] theorem splitOfTopology_displayedTopology (T : PhyloTree (Fin n))
    (q : Upper.Quartet n) :
    Upper.splitOfTopology q (Upper.displayedTopology T q) =
      T.displayedSplitOn q.1 q.2 := by
  obtain ⟨i, hi⟩ := displayedSplitOn_mem_topologyRange T q
  unfold Upper.displayedTopology
  rw [← hi, Upper.topologyOfSplit_splitOfTopology]

/-- The supported leaf three-cycle cyclically permutes the displayed
topology, with no reference to any probability space. -/
theorem displayedTopology_quartetCycle (T : PhyloTree (Fin n))
    (q : Upper.Quartet n) :
    Upper.displayedTopology (relabel (quartetCycle q) T) q =
      topologyCycle (Upper.displayedTopology T q) := by
  have hs := displayedSplitOn_relabel (quartetCycle q) T q.1 q.2
  have hs' :
      (relabel (quartetCycle q) T).displayedSplitOn q.1 q.2 =
        Circular.mapSplit (quartetCycle q).toEmbedding
          (T.displayedSplitOn q.1 q.2) := by
    simpa only [quartet_map_quartetCycle q] using hs
  rw [← splitOfTopology_displayedTopology T q,
    quartetCycle_splitOfTopology] at hs'
  change Upper.topologyOfSplit q
      ((relabel (quartetCycle q) T).displayedSplitOn q.1 q.2) =
    topologyCycle (Upper.topologyOfSplit q (T.displayedSplitOn q.1 q.2))
  rw [hs', Upper.topologyOfSplit_splitOfTopology]
  rfl

/-- The whole displayed-topology vector after a global relabelling. -/
def relabelTopologies (T : PhyloTree (Fin n))
    (pi : Equiv.Perm (Fin n)) (q : Upper.Quartet n) : Fin 3 :=
  Upper.displayedTopology (relabel pi T) q

/-- Right composition by a fixed permutation is a permutation of the global
relabelling sample space. -/
def rightTrans (g : Equiv.Perm α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun pi := pi.trans g
  invFun pi := pi.trans g.symm
  left_inv pi := by ext x; simp
  right_inv pi := by ext x; simp

theorem relabelTopologies_rightTrans_cycle (T : PhyloTree (Fin n))
    (q : Upper.Quartet n) (pi : Equiv.Perm (Fin n)) :
    relabelTopologies T (rightTrans (quartetCycle q) pi) q =
      topologyCycle (relabelTopologies T pi q) := by
  change Upper.displayedTopology (relabel (pi.trans (quartetCycle q)) T) q =
    topologyCycle (Upper.displayedTopology (relabel pi T) q)
  rw [← relabel_trans]
  exact displayedTopology_quartetCycle (relabel pi T) q

private theorem channelCount_equiv_cycle
    [Fintype Ω] [DecidableEq Ω] [Fintype S] [DecidableEq S]
    (F : Ω ≃ Ω) (c : S ≃ S) (out : Ω → S)
    (h : ∀ w, out (F w) = c (out w)) (s : S) :
    Counting.channelCount out (c s) = Counting.channelCount out s := by
  unfold Counting.channelCount
  symm
  apply Finset.card_bij (fun w _ => F w)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [h w, hw]
  · intro a _ b _ hab
    exact F.injective hab
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hpre : out (F.symm y) = s := by
      apply c.injective
      calc
        c (out (F.symm y)) = out (F (F.symm y)) := (h (F.symm y)).symm
        _ = out y := by rw [F.apply_symm_apply]
        _ = c s := hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpre

private theorem sum_channelCount [Fintype Ω] [DecidableEq Ω]
    [Fintype S] [DecidableEq S] (out : Ω → S) :
    ∑ s : S, Counting.channelCount out s = Fintype.card Ω := by
  classical
  simp_rw [Counting.channelCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem relabelTopology_channelCount_cycle (T : PhyloTree (Fin n))
    (q : Upper.Quartet n) (i : Fin 3) :
    Counting.channelCount (fun pi : Equiv.Perm (Fin n) =>
        relabelTopologies T pi q) (topologyCycle i) =
      Counting.channelCount (fun pi : Equiv.Perm (Fin n) =>
        relabelTopologies T pi q) i := by
  apply channelCount_equiv_cycle (rightTrans (quartetCycle q)) topologyCycle
  intro pi
  exact relabelTopologies_rightTrans_cycle T q pi

/-- Every fixed label quartet has exactly one third of all global
permutations in each displayed topology channel. -/
theorem relabelTopologies_uniform (T : PhyloTree (Fin n)) :
    Counting.UniformChannelLaw (relabelTopologies T) := by
  constructor
  intro q i
  let out : Equiv.Perm (Fin n) → Fin 3 := fun pi => relabelTopologies T pi q
  have hcycle (j : Fin 3) :
      Counting.channelCount out (topologyCycle j) =
        Counting.channelCount out j := by
    exact relabelTopology_channelCount_cycle T q j
  have hall (j : Fin 3) :
      Counting.channelCount out j = Counting.channelCount out 0 := by
    fin_cases j
    · rfl
    · simpa [topologyCycle] using (hcycle 1).symm
    · simpa [topologyCycle] using hcycle 0
  calc
    3 * Counting.channelCount out i =
        3 * Counting.channelCount out 0 := by rw [hall i]
    _ = ∑ j : Fin 3, Counting.channelCount out j := by
      simp [hall]
    _ = Fintype.card (Equiv.Perm (Fin n)) := sum_channelCount out

/-- On four leaves the preceding global statement is literally the local
`8/24` enumeration. -/
theorem four_relabeling_fiber_card (T : PhyloTree (Fin 4))
    (q : Upper.Quartet 4) (i : Fin 3) :
    Counting.channelCount (fun pi : Equiv.Perm (Fin 4) =>
      relabelTopologies T pi q) i = 8 := by
  have h := (relabelTopologies_uniform T).channel_count q i
  rw [Counting.FourRelabeling.card_permutations] at h
  omega

/-! ## Extracting a relabelling at least as good as the average -/

theorem exists_relabeling_two_thirds (T₁ T₂ : PhyloTree (Fin n)) :
    ∃ pi : Equiv.Perm (Fin n),
      2 * Nat.choose n 4 ≤ 3 * Upper.quartetDistance T₁ (relabel pi T₂) := by
  have h := Counting.exists_relabeling_two_thirds
    (truth := Upper.displayedTopology T₁)
    (out := relabelTopologies T₂) (relabelTopologies_uniform T₂)
  simpa [Counting.relabelDistance, Upper.quartetDistance,
    Counting.truthDistance, relabelTopologies, Upper.card_quartet] using h

/-! ## A concrete nonempty family of tree shapes -/

/-- The right-comb full tree with leaf word `a :: xs`. -/
def caterpillar : (a : α) → List α → FullTree α
  | a, [] => .leaf a
  | a, b :: xs => .fork (.leaf a) (caterpillar b xs)

@[simp] theorem caterpillar_leaves (a : α) (xs : List α) :
    (caterpillar a xs).leaves = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simp [caterpillar, ih]

/-- For every `n ≥ 4` the concrete rooted model is inhabited.  The witness
is the caterpillar whose distinguished root is `0` and whose crown starts at
`1`; the remaining labels are taken from the finite universe exactly once. -/
theorem nonempty_phyloTree_fin (n : ℕ) (hn : 4 ≤ n) :
    Nonempty (PhyloTree (Fin n)) := by
  let r : Fin n := ⟨0, by omega⟩
  let a₀ : {a : Fin n // a ≠ r} :=
    ⟨⟨1, by omega⟩, by
      intro h
      have := congrArg Fin.val h
      norm_num at this⟩
  let xs : List {a : Fin n // a ≠ r} :=
    ((Finset.univ : Finset {a : Fin n // a ≠ r}).erase a₀).toList
  refine ⟨⟨r, caterpillar a₀ xs, ?_, ?_⟩⟩
  · rw [caterpillar_leaves]
    rw [List.nodup_cons]
    constructor
    · simp [xs]
    · exact Finset.nodup_toList _
  · intro a
    rw [caterpillar_leaves]
    simp only [List.mem_cons]
    by_cases h : a = a₀
    · exact Or.inl h
    · right
      rw [show xs = ((Finset.univ : Finset {a : Fin n // a ≠ r}).erase a₀).toList
        from rfl, Finset.mem_toList]
      simp [h]

/-- The concrete lower-bound pair required in the maximum-distance theorem. -/
theorem exists_phyloTree_pair_two_thirds (n : ℕ) (hn : 4 ≤ n) :
    ∃ T₁ T₂ : PhyloTree (Fin n),
      2 * Nat.choose n 4 ≤ 3 * Upper.quartetDistance T₁ T₂ := by
  let T : PhyloTree (Fin n) := Classical.choice (nonempty_phyloTree_fin n hn)
  obtain ⟨pi, hpi⟩ := exists_relabeling_two_thirds T T
  exact ⟨T, relabel pi T, hpi⟩

end QuartetDistance.Lower
