# Formalization guide

This document describes the Lean 4 formalization accompanying
*Order closure, order adherence and Fatou norms* by A. Avilés,
M. A. Taylor, and P. Tradacete. The manuscript is included as
[`paper.pdf`](paper.pdf).

## Scope and status

The development covers the three principal parts of the paper:

1. the characterization of order-continuous Banach lattice norms through
   order and unbounded-order adherence of sublattices;
2. the Gao--Leung counterexamples and the construction of solid sets whose
   order adherence requires arbitrarily many iterations; and
3. the construction of a weakly Fatou Banach lattice norm that is not
   equivalent to any Fatou lattice norm.

All declarations have checked Lean proofs. The project contains no `sorry`,
`admit`, or project-specific axioms. The source modules follow the order of the
paper as closely as Lean's dependency structure permits.

## Module organization

The root module [`OrderClosures.lean`](OrderClosures.lean) imports the complete
development. The mathematical content is organized as follows.

| Module | Contents |
|---|---|
| [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) | Shared definitions and general results about order convergence, unbounded-order convergence, adherence, solidity, transfinite adherence towers, density character, and Fatou properties. |
| [`GaoLeungCharacterization.lean`](OrderClosures/GaoLeungCharacterization.lean) | The Gao--Leung characterization of order-continuous norms. |
| [`Solovay.lean`](OrderClosures/Solovay.lean) | Solovay's complete Boolean algebra, its Stone space, and the analytic ingredients used in the Gao--Leung counterexample. |
| [`GaoLeungProblem/Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean) | The Gao--Leung counterexample and the cardinal bounds for order adherence. |
| [`GaoLeungProblem/CNFOrder.lean`](OrderClosures/GaoLeungProblem/CNFOrder.lean) | The Cantor-normal-form extension order used in the transfinite construction. |
| [`GaoLeungProblem/OrdinalSpace.lean`](OrderClosures/GaoLeungProblem/OrdinalSpace.lean) | The compact ordinal space, coordinate projections, and their order properties. |
| [`GaoLeungProblem/StageFormula.lean`](OrderClosures/GaoLeungProblem/StageFormula.lean) | The one-step and transfinite formulas for the Gao adherence stages. |
| [`GaoLeungProblem/Iterations.lean`](OrderClosures/GaoLeungProblem/Iterations.lean) | The global product construction and the theorem on arbitrarily long adherence iterations. |
| [`WeaklyFatou/Reductions.lean`](OrderClosures/WeaklyFatou/Reductions.lean) | Abstract reductions from Fatou properties to adherence estimates and from sequential to net formulations. |
| [`WeaklyFatou/FiniteTree.lean`](OrderClosures/WeaklyFatou/FiniteTree.lean) | The finite tree, its topology, cylinder functions, and parent-disjointness. |
| [`WeaklyFatou/TreeNorm.lean`](OrderClosures/WeaklyFatou/TreeNorm.lean) | The tree seminorm and the component Banach lattice. |
| [`WeaklyFatou/Bands.lean`](OrderClosures/WeaklyFatou/Bands.lean) | Band projections, the upshift operation, sharp subsequences, and trimming. |
| [`WeaklyFatou/Moderated.lean`](OrderClosures/WeaklyFatou/Moderated.lean) | Thinning, transient bands, moderatedness, and the component weak Fatou estimate. |
| [`WeaklyFatou/FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) | Component adherence and the final `c₀`-sum counterexample. |

[`GaoLeungProblem.lean`](OrderClosures/GaoLeungProblem.lean) and
[`WeaklyFatou.lean`](OrderClosures/WeaklyFatou.lean) are umbrella modules that
retain convenient stable import paths for their respective developments.

## Paper-to-Lean correspondence

The table records the main paper-facing declarations. Supporting definitions
and technical lemmas are located in the same module as the result they serve.

| Paper topic or result | Lean declaration(s) | Module |
|---|---|---|
| Order convergence, uo-convergence, adherence, closure, and closedness | BanLat `OrderConvergesTo`; `UOConvergesTo`, `orderAdherence`, `uoAdherence`, `orderClosure`, `IsOrderClosed`, `IsUOClosed` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Gao--Leung Theorem 2.7 | `gaoLeung_orderContinuous_characterization` | [`GaoLeungCharacterization.lean`](OrderClosures/GaoLeungCharacterization.lean) |
| Gao--Leung Lemma 2.1 and its consequences | `orderAdherence_subset_uoAdherence_subset`, `uoAdherence_eq_orderClosure_of_isOrderClosed`, `uoAdherence_eq_double_orderAdherence_and_stabilizes` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Gao--Leung Problem 2.5 | `GaoLeungProperty` | [`Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean) |
| Negative answer to the Gao--Leung problem | `gao_counterexample` and the Solovay/Stone-space construction | [`Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean), [`Solovay.lean`](OrderClosures/Solovay.lean) |
| Cardinality bound for arbitrary order adherence | `orderAdherence_cardinality_bound` | [`Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean) |
| Solid order adherence and finite iteration | `directedPositiveAdherence`, `solidOrderAdherence`, `iteratedOrderAdherence`, `orderAdherence_eq_solidOrderAdherence` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Solid hull and solid generator number | `solidHull`, `solidHull_eq_iUnion_Icc`, `solidGeneratorNumber` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Solid sets with large first order adherence | `exists_solid_large_orderAdherence` | [`Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean) |
| Cardinality bound for solid order adherence | `signedPositiveSubsetSuprema`, `signedPositiveSubsetSuprema_isOrderClosed`, `solid_orderAdherence_cardinality_bound` | [`Counterexample.lean`](OrderClosures/GaoLeungProblem/Counterexample.lean) |
| Transfinite adherence towers | `OrderAdherenceTower`, `NeedsOrderAdherenceIterations` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Solid sets requiring arbitrarily many iterations | `solid_sets_require_arbitrarily_many_iterations` | [`Iterations.lean`](OrderClosures/GaoLeungProblem/Iterations.lean) |
| Cantor-normal-form relation and its order properties | `cnfExtensionLT`, `cnfExtensionLE`, `cnfExtensionLE_partialOrder_and_subrelation`, `cnfExtensionLT_linear_above` | [`CNFOrder.lean`](OrderClosures/GaoLeungProblem/CNFOrder.lean) |
| Compact ordinal space, projections, and stage sets | `GaoIndex`, `GaoCompactSpace`, `ordinalProjection`, `leastCNFExponent`, `GaoStageIndices`, `GaoStageSet` | [`OrdinalSpace.lean`](OrderClosures/GaoLeungProblem/OrdinalSpace.lean) |
| Infimum and chain-supremum claims for projections | `ordinalProjection_incomparable_iInf`, `ordinalProjection_chain_iSup` | [`OrdinalSpace.lean`](OrderClosures/GaoLeungProblem/OrdinalSpace.lean) |
| Formula for the transfinite Gao stages | `gao_orderAdherence_stage_formula`, `ordinalProjection_strict_stage` | [`StageFormula.lean`](OrderClosures/GaoLeungProblem/StageFormula.lean) |
| Adherence of a solidly generated set | `solid_generated_orderAdherence` | [`Iterations.lean`](OrderClosures/GaoLeungProblem/Iterations.lean) |
| Fatou and weak Fatou properties | `PaperLatticeNorm`, `HasFatouProperty`, `HasWeakFatouProperty`, `EquivalentNorms` | [`OrderAdherence.lean`](OrderClosures/OrderAdherence.lean) |
| Fremlin's problem and the main counterexample | `FremlinProperty`, `exists_weaklyFatou_not_equivalent_fatou` | [`Reductions.lean`](OrderClosures/WeaklyFatou/Reductions.lean), [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |
| Basic adherence and scaling reduction | `iteratedOrderAdherence_mono_and_scale` | [`Reductions.lean`](OrderClosures/WeaklyFatou/Reductions.lean) |
| Fatou and weak Fatou unit-ball reductions | `weakFatou_iterated_unitBall`, `fatou_iterated_unitBall` | [`Reductions.lean`](OrderClosures/WeaklyFatou/Reductions.lean) |
| Sequential and net Nakano properties | `IsWeakSequentialNakanoConstant`, `IsWeakNakanoConstant`, `separable_weakSequentialNakano_implies_weakNakano` | [`Reductions.lean`](OrderClosures/WeaklyFatou/Reductions.lean) |
| Finite tree, product space, cylinders, and tree functions | `TreeNode`, `TreeProduct`, `treeCylinder`, `treeFunction` | [`FiniteTree.lean`](OrderClosures/WeaklyFatou/FiniteTree.lean) |
| Basic tree-function identities | `treeCylinder_isClopen`, `treeFunction_child_properties` | [`FiniteTree.lean`](OrderClosures/WeaklyFatou/FiniteTree.lean) |
| Finite cylinder cover | `treeCylinder_finite_cover` | [`FiniteTree.lean`](OrderClosures/WeaklyFatou/FiniteTree.lean) |
| Parent-disjoint infimum lemma | `ParentDisjoint`, `finiteCylinderUnion`, `finiteTreeSup`, `parentDisjoint_treeFunctions_iInf` | [`FiniteTree.lean`](OrderClosures/WeaklyFatou/FiniteTree.lean) |
| Tree coefficients, basis, mass, and operator | `TreeCoefficients`, `treeBasis`, `treeRho`, `treeOperator` | [`TreeNorm.lean`](OrderClosures/WeaklyFatou/TreeNorm.lean) |
| Tree seminorm and its principal estimates | `treeSeminorm`, `treeLatticeSeminorm`, `treeSeminorm_norm_comparison`, `treeSeminorm_exact_basis` | [`TreeNorm.lean`](OrderClosures/WeaklyFatou/TreeNorm.lean) |
| Component lattice and root-vector estimates | `treeSublattice`, `TreeComponent`, `componentLatticeNorm`, `componentRoot`, `componentTreeFunction`, `component_basic` | [`TreeNorm.lean`](OrderClosures/WeaklyFatou/TreeNorm.lean) |
| Bands and finite band projections | `TreeBandIndex`, `treeBandSupport`, `treeBandProjection`, `finiteBandProjection` | [`Bands.lean`](OrderClosures/WeaklyFatou/Bands.lean) |
| Upshift lemma | `treeUpshift`, `treeUpshift_basic` | [`Bands.lean`](OrderClosures/WeaklyFatou/Bands.lean) |
| Sharp subsequence and trimming lemmas | `tree_sharp_subsequence`, `recurrentBands`, `tree_trim` | [`Bands.lean`](OrderClosures/WeaklyFatou/Bands.lean) |
| Thinning and transient-band lemmas | `tree_thinning`, `tree_transient` | [`Moderated.lean`](OrderClosures/WeaklyFatou/Moderated.lean) |
| Component moderatedness and weak Fatou property | `component_moderated`, `component_weakFatou` | [`Moderated.lean`](OrderClosures/WeaklyFatou/Moderated.lean) |
| Terminal functions and component adherence | `terminalTreeFunctions`, `component_large_iterated_adherence` | [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |
| Final `c₀`-sum and its norm | `ComponentProduct`, `componentVanishes`, `componentC0Sublattice`, `FinalSpace`, `finalNormValue`, `finalLatticeNorm` | [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |
| Weak Fatou property of the final space | `finalSpace_weakFatou` | [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |
| Large-coordinate witnesses | `finalLargeVector`, `finalLargeVector_properties` | [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |
| Failure of every equivalent Fatou lattice norm | `finalSpace_not_equivalent_fatou`, `exists_weaklyFatou_not_equivalent_fatou` | [`FinalSpace.lean`](OrderClosures/WeaklyFatou/FinalSpace.lean) |

## Library interfaces

The formalization reuses BanLat's `OrderConvergesTo`, vector-lattice hierarchy,
`SigmaConditionallyCompleteLattice`, `IsOrderContinuousNorm`,
`VectorSublattice`, and `LatticeSeminorm`. Mathlib supplies the set-theoretic,
topological, cardinal, ordinal, continuous-function, and finitely supported
function infrastructure.

Definitions specific to the paper are introduced in this repository. These
include uo-convergence and uo-adherence, the Fatou and weak Fatou predicates,
the explicit paper lattice norms, Nakano constants, density character, and
the transfinite adherence tower.

## Modeling decisions and explicit hypotheses

- A second norm on an already normed type is represented by
  `PaperLatticeNorm` instead of installing competing global `Norm` instances.
  Completeness, Fatou properties, and norm equivalence therefore take the
  chosen norm explicitly.
- `IsOrderComplete` records the nonempty-bounded-supremum property used in the
  paper. `conditionallyCompleteLatticeOfIsOrderComplete` bridges it to
  BanLat's order-complete lattice interface when that structure is needed.
- `densityCharacter` is defined as the infimum of the cardinalities of dense
  subsets.
- `OrderAdherenceTower` makes the zero, successor, and nonzero-limit stages
  explicit. `NeedsOrderAdherenceIterations A ξ` states that every adherence
  step below `ξ` is proper.
- The long-iteration theorem assumes `Cardinal.aleph0 ≤ κ`, making explicit
  that the construction is for infinite cardinals. Its witness is universe
  lifted because `GaoCompactSpace ξ` lives one universe above `ξ`.
- The trimming lemma explicitly assumes nonnegative coefficients and the
  sharpness convergence selected immediately before it in the paper. The
  transient-band lemma explicitly requires the chosen persistent family to
  contain the root band. These hypotheses are supplied by the construction
  used in `component_moderated`.

## Reproducing the checks

The project is pinned to Lean `v4.30.0`, Mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, and BanLat commit
`b00e59836016aa1099b8011add6b07385e66428e`. From the repository root, run:

```bash
lake exe cache get
lake build
rg -n '\b(sorry|admit)\b|sorryAx' --glob '*.lean' .
```

The build should succeed, and the final command should produce no matches.
