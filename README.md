# Maximum quartet distance in Lean

This repository formalizes the mathematical argument in
`bandelt_dress_solution.tex` with Lean 4 and mathlib.  The development proves
the exact finite upper and lower bounds for maximum quartet distance on the
paper's conventional finite degree-one/degree-three graph domain, their
normalized form, the stated asymptotic estimate, and the two finite threshold
computations.  An independently defined recursive tree encoding is proved
label-preservingly graph-isomorphic to every conventional tree; the two
quartet distances and their maxima are then proved exactly equal for `n ≥ 4`.

The published permuton inequality of Chan--Král'--Noel--Pehova--Sharifzadeh--Volec is the sole external mathematical input.  It is represented by the
explicit proposition `PermutonPatterns.PublishedPermutonPatternSumInequality`
and is passed as a hypothesis to the main theorem; it is not declared as a
Lean axiom.  Individual pattern densities, their disjoint sum, the Borel step
permuton with uniform marginals and unit-square support, arbitrary-permuton
tie-nullity, exhaustion by all 24 strict patterns, and the exact finite
collision reduction are all formalized internally.

The project is pinned to Lean and mathlib `v4.32.0`.

```sh
lake update
lake exe cache get
lake build
lake build QuartetDistance.Audit
```

The paper-domain endpoints are `graph_bandelt_dress_finite_bounds`,
`graph_bandelt_dress_main`,
`graphMaximumQuartetDistance_normalized_sub_two_thirds_isBigO`, and
`graphMaximumQuartetDistance_normalized_tendsto`.

The source is divided into these modules:

- `Circular`: quartet splits, the eight dihedral patterns, relative
  permutations, and the step-permuton collision reduction;
- `Splits`: the explicit three quartet channels and their two-element
  wrong-channel supports;
- `CircularQuotient` and `DihedralGroup`: circular orders modulo rotation and
  reversal, invariance of crossing statistics, and the generated-subgroup
  characterization of the eight patterns;
- `Permuton`, `PermutonPatterns`, `PermutonMass`, and `TiedSampleCount`: Borel
  permutons, individual pattern densities, the concrete step measure, rank
  chambers, iid sampling, and the exact analytic-to-finite density identity;
- `Tree`: a rooted-at-one-leaf encoding of unrooted binary phylogenetic trees,
  rotation profiles, restriction/suppression, and the wrong-channel law;
- `RibbonRestriction` and `GeneralRestriction`: edge intervals and pointwise
  boundary restriction for arbitrary nonempty induced leaf sets;
- `TreeAdequacy`: a finite connected acyclic graph realization with exactly
  the required degree-one/degree-three profile;
- `GraphModel`: the independent conventional finite graph structure, the
  well-founded graph-to-syntax encoding, the reverse realization, and their
  label-preserving graph isomorphisms;
- `GraphQuartet`: delete-edge reachability, edge clusters, pruning/suppression
  transport, and equivalence between direct graph display and the induced
  recursive quartet split;
- `GraphRibbon`: the literal edge-interval lemma for both delete-edge
  components of every actual realization edge;
- `GraphMaximum`: canonical finite graph presentations, unique directly
  displayed topologies, graph quartet distance, and exact equality of the
  graph and syntax maxima;
- `Counting`: exact finite double counting and random-relabel counting;
- `Upper` and `Lower`: integration of the tree model with the two bounds;
- `Arithmetic`: binomial identities, normalized expansion, asymptotics, and
  the thresholds 53 and 690;
- `Maximum` and the root `QuartetDistance` module: both maxima and the final
  syntax- and conventional-graph versions of the paper theorem;
- `Audit`: kernel axiom reports for the principal analytic, combinatorial,
  graph-domain, finite, and asymptotic results.

The formalization contains no `sorry`, `admit`, custom axioms, or
`native_decide` proofs.  The final theorem's axiom audit uses only Lean's
standard logical foundations (`propext`, `Classical.choice`, and `Quot.sound`).
