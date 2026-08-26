# Phase II proof status (2026-08-26)

The completed Phase II scope comprises `OrderClosures/OrderAdherence.lean`,
`OrderClosures/GaoLeungProblem.lean`, and `OrderClosures/WeaklyFatou.lean`.
All 25 original obligations associated with the first two files have genuine
proofs, and all 73 literal placeholders from the original
`WeaklyFatou.lean` (spread across 43 declarations and structure fields) have
also been replaced by proofs.

## Paper-ordered module layout

The two largest implementation files have been split while preserving their
original import paths as compatibility umbrellas. Every implementation module
has between 400 and 1000 lines:

- `GaoLeungProblem/Counterexample.lean` (counterexample and cardinal bounds),
  `CNFOrder.lean` (the Cantor-normal-form extension order),
  `OrdinalSpace.lean` (compact ordinal space and coordinate projections),
  `StageFormula.lean` (one-step and transfinite adherence formulas), and
  `Iterations.lean` (the product construction and final iteration theorems);
- `WeaklyFatou/Reductions.lean` (abstract reductions), `FiniteTree.lean`
  (tree topology and parent-disjointness), `TreeNorm.lean` (the seminorm and
  component lattice), `Bands.lean` (band projections, upshift, and trimming),
  `Moderated.lean` (thinning, transientness, and moderatedness), and
  `FinalSpace.lean` (component adherence and the final `c₀`-sum).

Declarations retain their paper order apart from the namespace/import
boundaries required by Lean. The former top-level modules import these files
in order, so downstream imports require no changes.

## Weakly Fatou completion

The formalization now proves the paper's entire tree construction and final
`c₀`-sum argument. The completed groups are:

- the order-adherence, scaling, Fatou, and sequential-to-net reductions;
- the finite-tree topology, cylinder partitions, parent-disjointness, and
  weighted tree seminorm estimates;
- the component vector-lattice and normed-lattice structures, including
  completeness, separability, the exact basis computation, and the root
  vector estimates;
- the sharp-subsequence, trimming, thinning, transient-band, moderatedness,
  and weak-Fatou arguments;
- the component adherence construction and the final `c₀`-sum lattice norm;
- completeness and weak Fatou for the final space, the large-coordinate
  witnesses, and the proof that no equivalent Fatou lattice norm exists.

The principal supporting definitions and lemmas added for these proofs are
the generic implications `weakNakano_of_weakSequentialNakano_p` and
`weakFatou_of_weakNakano_p`; the band partition API around `treeBandOfNode`,
`treeBandParent`, `bandsAt`, and finite band projections; the nonnegative tree
operator and weighted-`ρ` inequalities; the finite parent-support argument
for upshifted coefficients; `treeOperator_mem_treeSublattice`; and the final
single-coordinate embedding, including preservation of order convergence and
iterated order adherence.

## Completed obligations

- `orderAdherence_eq_solidOrderAdherence`
- `subset_orderAdherence`
- `orderAdherence_mono`
- `subset_uoAdherence`
- `OrderConvergesTo.uoConvergesTo`
- `orderAdherence_subset_uoAdherence_subset`
- `uoAdherence_eq_orderClosure_of_isOrderClosed`
- `uoAdherence_eq_double_orderAdherence_and_stabilizes`
- `isSolid_orderAdherence`
- `solidHull_eq_iUnion_Icc`
- `orderAdherence_cardinality_bound`
- `signedPositiveSubsetSuprema_isOrderClosed`
- `solid_orderAdherence_cardinality_bound`
- the continuity field of `ordinalProjection`
- `exists_solid_large_orderAdherence`
- `cnfExtensionLE_partialOrder_and_subrelation`
- `cnfExtensionLT_linear_above`
- `ordinalProjection_incomparable_iInf`
- `ordinalProjection_strict_stage`
- `solid_generated_orderAdherence`
- `gao_counterexample`
- `gaoLeung_orderContinuous_characterization`
- `ordinalProjection_chain_iSup`
- `gao_orderAdherence_stage_formula`
- `solid_sets_require_arbitrarily_many_iterations`

The principal local helpers are the domination lemma for order-convergent
nets, the order convergence of lattice clamps under uo-convergence, the
order-closedness of `positiveSubsetSuprema`, and the injective encodings used
for the two cardinal estimates. The ordinal development additionally uses a
list model of the CNF extension relation (`CNFStep`, `CNFListLT`, and
`cnfValue`), proves its transitivity and upper-cone trichotomy, extracts finite
coordinate neighborhoods in the Cantor cube, and characterizes domination of
coordinate projections by CNF extension. The proofs reuse BanLat's
`OrderConvergesTo` algebra/continuity API and Mathlib's solid-closure,
cardinal-powerset, continuous-evaluation, and ordinal interfaces. The
previously requested bridge
`conditionallyCompleteLatticeOfIsOrderComplete` remains in
`OrderAdherence.lean`.

For Claim 2, the formalization develops the missing Cantor-normal-form
machinery needed to show that the ordinary ordinal supremum of a nonempty
`cnfExtensionLE`-chain remains above every chain member. The principal helpers
are `cnfExtensionLE_chain_lub`, the singleton-CNF lemmas, and
`leastCNFExponent_chain_lub_le`.

For Claim 3, finite minimal dominators are extracted from each directed
positive family, coherently followed along a cofinal tail, and replaced by
their chain supremum. The reverse inclusion uses the explicit
`singletonCNFBelow` approximation. These arguments yield the one-step formula
`orderAdherence_gaoStage` and then the transfinite formula by ordinal limit
recursion.

The endpoint `ξ = κ⁺` is handled by one dependent product containing every
smaller Gao component. A κ-indexed diagonal family generates the global solid
set. Coordinate projection and single-coordinate inclusion preserve order
convergence, so each component transfers its strict stage to the global tower.
An auxiliary padding coordinate makes the diagonal generators irredundant and
proves the stronger exact equality of the solid generator number with κ.

The new module `OrderClosures/Solovay.lean` formalizes Solovay's proof of the
Gaifman--Hales theorem for the required complete Boolean algebra of regular
open sets. It also constructs its compact Hausdorff Stone spectrum, proves
that the spectrum is extremally disconnected, proves order completeness of
its real continuous-function lattice, embeds the Boolean algebra as clopen
indicators, establishes the density-character bound, and constructs the
closed separable vector sublattice used by `gao_counterexample`.

The new module `OrderClosures/GaoLeungCharacterization.lean` gives a genuine
proof of Gao--Leung Theorem 2.7.  It formalizes the cycle `(3) → (1) → (2) →
(3)`.  The reverse implication uses the standard disjoint-sequence criterion
for failure of order continuity, constructs the corresponding lattice
embedding of bounded functions on `ℕ × ℕ`, and uses the row-limit sublattice
to exhibit a point in uo-adherence but not in order adherence.  The theorem's
typeclass binder was also made coherent: `SigmaConditionallyCompleteLattice X`
now supplies the unique lattice structure, rather than coexisting with a
second, potentially different, explicit `Lattice X` instance.  This changes
no intended mathematical hypothesis.

## Phase-I statement corrections

The declaration `solid_sets_require_arbitrarily_many_iterations` permits
`κ = 0` and `ξ = 1`. Its hypothesis then holds because Lean simplifies

```lean
(1 : Ordinal) ≤ Cardinal.ord (Order.succ (0 : Cardinal))
```

to a true proposition, but its conclusion is false. A checked Lean
counterproof establishes:

1. for a solid set `S`, `solidGeneratorNumber S = 0` forces `S = ∅` (using
   `Cardinal.sInf_eq_zero_iff` and `Cardinal.mk_set_eq_zero_iff`);
2. `orderAdherence (∅ : Set X) = ∅`;
3. consequently `NeedsOrderAdherenceIterations (∅ : Set X) 1` is false.

Thus the current theorem would contradict a proof using only standard Lean
foundations. The paper's construction is an infinite-cardinal construction;
the statement has therefore been corrected, with the user's authorization, by
adding the hypothesis `Cardinal.aleph0 ≤ κ`.

Two further minimal corrections were required while completing the proof.
First, the paper proves that every adherence stage below `ξ` is proper; it
does not prove that the stage at `ξ` is already order closed (in particular,
the endpoint product argument only supplies a lower bound). Accordingly,
`NeedsOrderAdherenceIterations A ξ` now expresses exactly this “at least ξ
iterations” property and no longer adds terminal closedness. Second,
`GaoCompactSpace ξ` and its continuous-function lattice live in `Type (u+1)`
when `ξ : Ordinal.{u}`. The final theorem's witness universe, generator
cardinal, and ordinal were therefore lifted by one universe. These are
logical/universe corrections only; the mathematical claim is unchanged.

Two hypotheses implicit in the paper's setup were also restored in the tree
lemmas. The trimming lemma `tree_trim` now assumes that its coefficient
vectors are nonnegative and that the sequence is already *sharp*, meaning
that the `ρ`-mass of every band converges. In the paper the vectors lie in the
positive cone and a sharp subsequence is selected immediately before the
trimming lemma. Without the sharpness hypothesis, mass may rotate through
infinitely many bands and the former Lean statement is false. The transient
lemma `tree_transient` now assumes that the selected finite family of
persistent bands contains the root band. This is also how the family is
chosen in the paper and is needed because nodes in distinct non-root bands
can otherwise have the root as their common parent. The calls from
`component_moderated` supply both restored hypotheses.

## Validation

- Lean: `leanprover/lean4:v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- BanLat: `b00e59836016aa1099b8011add6b07385e66428e`.
- `lake env lean OrderClosures/OrderAdherence.lean`: succeeds with no
  placeholder warnings.
- `lake env lean OrderClosures/GaoLeungCharacterization.lean`: succeeds with no
  placeholder warnings.
- `lake env lean OrderClosures/GaoLeungProblem.lean`: succeeds with no
  placeholder warnings.
- `lake env lean OrderClosures/WeaklyFatou.lean`: succeeds without warnings or
  placeholders.
- `lake build OrderClosures.GaoLeungProblem`: succeeds (3353 jobs).
- `lake build OrderClosures.WeaklyFatou`: succeeds (3317 jobs).
- `lake build`: succeeds (3362 jobs).
- `rg -n '\b(sorry|admit)\b|sorryAx' --glob '*.lean' .`: no matches in the
  project Lean sources.
- `#print axioms` on `ordinalProjection_chain_iSup`,
  `gao_orderAdherence_stage_formula`, and
  `solid_sets_require_arbitrarily_many_iterations` reports only `propext`,
  `Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or a custom
  project axiom.
- `#print axioms` on `tree_trim`, `tree_transient`, `component_moderated`,
  `component_weakFatou`, `finalSpace_weakFatou`,
  `finalLargeVector_properties`, `finalSpace_not_equivalent_fatou`, and
  `exists_weaklyFatou_not_equivalent_fatou` likewise reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `git diff --check`: succeeds.

# Historical Phase I formalization report

This report covers the whole mathematical scope of `paper.tex`. Phase I is an
interface pass: mathematical data is implemented, every paper result is stated,
and every proof obligation is deliberately left as an explicit `sorry`.

## Revisions and validation

- Lean: `leanprover/lean4:v4.30.0` (`lean-toolchain`).
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
  (inherited from the BanLat manifest, input revision `v4.30.0`).
- BanLat: `b00e59836016aa1099b8011add6b07385e66428e`
  (exact pin in `lakefile.toml`).
- Repository base revision: `4b2c4049281c7b8b55afedb0907b7ae82abadc58`.
- Validation: `lake build` completed successfully with 3319 jobs on 2026-08-24.
- Audit: 98 literal `sorry` occurrences, grouped into 68 declarations below.
  There are no elaboration errors. The warnings are the expected Phase I
  `declaration uses sorry` warnings.

## Paper-to-Lean inventory

All entries have status **interface complete / proof deferred** unless marked as
a definition, in which case their non-proof data is implemented.

| Paper item | Lean declaration(s) | File |
|---|---|---|
| Definitions of order convergence, uo-convergence, adherence, closure, and closedness | BanLat `OrderConvergesTo`; `UOConvergesTo`, `orderAdherence`, `uoAdherence`, `orderClosure`, `IsOrderClosed`, `IsUOClosed` | `OrderAdherence.lean` |
| Theorem `ND` (Gao--Leung Theorem 2.7) | `gaoLeung_orderContinuous_characterization` | `GaoLeungCharacterization.lean` |
| Gao--Leung Lemma 2.1 and its consequences | `orderAdherence_subset_uoAdherence_subset`, `uoAdherence_eq_orderClosure_of_isOrderClosed`, `uoAdherence_eq_double_orderAdherence_and_stabilizes` | `OrderAdherence.lean` |
| Gao--Leung Problem 2.5 | `GaoLeungProperty` | `GaoLeungProblem.lean` |
| Fatou and weak Fatou definitions | `HasFatouProperty`, `HasWeakFatouProperty` | `OrderAdherence.lean` |
| Fremlin Problem AB | `FremlinProperty` | `WeaklyFatou.lean` |
| Proposition `prop:gao-counterexample` | `gao_counterexample` and its Solovay/Stone helpers | `GaoLeungProblem.lean`, `Solovay.lean` |
| Remark `rem:gao-cardinality` | `orderAdherence_cardinality_bound` | `GaoLeungProblem.lean` |
| Solid order-adherence definition and finite iteration | `directedPositiveAdherence`, `solidOrderAdherence`, `iteratedOrderAdherence`, `orderAdherence_eq_solidOrderAdherence` | `OrderAdherence.lean` |
| Solid hull and `solidgen` | `solidHull`, `solidHull_eq_iUnion_Icc`, `solidGeneratorNumber` | `OrderAdherence.lean` |
| Proposition `prop:solid-large-order-closure` | `exists_solid_large_orderAdherence` | `GaoLeungProblem.lean` |
| Proposition `prop:cardinalitybound` | `positiveSubsetSuprema`, `signedPositiveSubsetSuprema`, `signedPositiveSubsetSuprema_isOrderClosed`, `solid_orderAdherence_cardinality_bound` | `GaoLeungProblem.lean` |
| Theorem `thm:solid-iterations` | `OrderAdherenceTower`, `NeedsOrderAdherenceIterations`, `solid_sets_require_arbitrarily_many_iterations` | `OrderAdherence.lean`, `GaoLeungProblem.lean` |
| Cantor-normal-form relation and P1/P2 in that proof | `cnfExtensionLT`, `cnfExtensionLE`, `cnfExtensionLE_partialOrder_and_subrelation`, `cnfExtensionLT_linear_above` | `GaoLeungProblem.lean` |
| Compact ordinal space, projections, `Z_β`, and `S_β` | `GaoIndex`, `GaoCompactSpace`, `ordinalProjection`, `leastCNFExponent`, `GaoStageIndices`, `GaoStageSet` | `GaoLeungProblem.lean` |
| Claims 1--3 and strict-stage witness | `ordinalProjection_incomparable_iInf`, `ordinalProjection_chain_iSup`, `gao_orderAdherence_stage_formula`, `ordinalProjection_strict_stage` | `GaoLeungProblem.lean` |
| Lemma `lem:solid-generated-order-adh` | `solid_generated_orderAdherence` | `GaoLeungProblem.lean` |
| Theorem `thm:fremlin-main` | `exists_weaklyFatou_not_equivalent_fatou`; concrete witness theorem `finalSpace_not_equivalent_fatou` | `WeaklyFatou.lean` |
| Lemma `lem:order-basic` | `iteratedOrderAdherence_mono_and_scale` | `WeaklyFatou.lean` |
| Lemma `lem:fatou-order` | `weakFatou_iterated_unitBall`, `fatou_iterated_unitBall` | `WeaklyFatou.lean` |
| Weak sequential/full Nakano definitions | `IsWeakSequentialNakanoConstant`, `IsWeakNakanoConstant` | `WeaklyFatou.lean` |
| Proposition `prop:separable-reduction` | `separable_weakSequentialNakano_implies_weakNakano` | `WeaklyFatou.lean` |
| `G_n`, `H_n`, root, child, parent, restriction, and `I_n` | `TreeNode`, `TreeNonterminal`, `TreeNode.root`, `TreeNode.child`, `TreeNode.parent`, `TreeNode.restrict`, `strictPrefix`, `TreeProduct` | `WeaklyFatou.lean` |
| Cylinders `E_t` and tree functions `s_t` | `treeCylinder`, `treeFunction` | `WeaklyFatou.lean` |
| Lemma `lem:basic-tree` | `treeCylinder_isClopen`, `treeFunction_child_properties` | `WeaklyFatou.lean` |
| Lemma `lem:finite-cover` | `treeCylinder_finite_cover` | `WeaklyFatou.lean` |
| Parent-disjointness definition | `ParentDisjoint` | `WeaklyFatou.lean` |
| Lemma `lem:pi-disjoint` | `finiteCylinderUnion`, `finiteTreeSup`, `parentDisjoint_treeFunctions_iInf` | `WeaklyFatou.lean` |
| `W_n`, `e_t`, `ρ_n`, and `T_n` | `TreeCoefficients`, `treeBasis`, `treeRho`, `treeOperator` | `WeaklyFatou.lean` |
| Infimum formula for `p_n` | `treeSeminorm`, bundled `treeLatticeSeminorm` | `WeaklyFatou.lean` |
| Lemma `lem:pn-seminorm` | proof fields of `treeLatticeSeminorm` | `WeaklyFatou.lean` |
| Lemma `lem:norm-comparison` | `treeSeminorm_norm_comparison` | `WeaklyFatou.lean` |
| Lemma `lem:exact-basis` | `treeSeminorm_exact_basis` | `WeaklyFatou.lean` |
| Closed generated component `X_n` with restricted `p_n` | `treeSublattice`, `TreeComponent`, `componentLatticeNorm`, `componentRoot`, `componentTreeFunction` | `WeaklyFatou.lean` |
| Corollary `cor:Yn-basic` | `component_basic` | `WeaklyFatou.lean` |
| Root/sibling bands and finite projections | `TreeBandIndex`, `treeBandSupport`, `treeBandProjection`, `finiteBandProjection` | `WeaklyFatou.lean` |
| Up-shift and Lemma `lem:upshift-basic` | `treeUpshift`, `treeUpshift_basic` | `WeaklyFatou.lean` |
| Lemma `lem:sharp-subsequence` | `tree_sharp_subsequence` | `WeaklyFatou.lean` |
| Lemma `lem:trim` | `recurrentBands`, `tree_trim` | `WeaklyFatou.lean` |
| Lemma `lem:thinning` | `tree_thinning` | `WeaklyFatou.lean` |
| Lemma `lem:transient` | `tree_transient` | `WeaklyFatou.lean` |
| Proposition `prop:moderated` | `component_moderated` | `WeaklyFatou.lean` |
| Corollary `cor:weak-fatou` | `component_weakFatou` | `WeaklyFatou.lean` |
| Terminal family `L_n` | `terminalTreeFunctions` | `WeaklyFatou.lean` |
| Proposition `prop:component` | `component_large_iterated_adherence` | `WeaklyFatou.lean` |
| Concrete `c₀(X_n)` and its supremum norm | `ComponentProduct`, `componentVanishes`, `componentC0Sublattice`, `FinalSpace`, `finalNormValue`, `finalLatticeNorm` | `WeaklyFatou.lean` |
| Lemma `lem:c0-weak-fatou` | `finalSpace_weakFatou` | `WeaklyFatou.lean` |
| Vectors `z_n` and Proposition `prop:zn` | `finalLargeVector`, `finalLargeVector_properties` | `WeaklyFatou.lean` |

This accounts for all 33 theorem/lemma/proposition/corollary/remark/definition/question
environments in the paper. The Lean modules contain 131 declarations in total,
including the auxiliary data and typeclass interfaces needed to state them.

## Exact library matches

The following installed declarations were checked before defining the paper layer.

### BanLat

- `OrderConvergesTo` — `BanLat/Convergences/Order.lean`; used verbatim for order
  convergence and inside uo-convergence.
- `VectorLattice`, `NormedVectorLattice`, `BanachLattice` —
  `BanLat/Basic.lean` and `BanLat/Normed.lean`; ambient lattice hierarchy.
- `SigmaConditionallyCompleteLattice` — `BanLat/OrderComplete.lean`; the
  σ-order-completeness assumption in Theorem `ND`.
- `IsOrderContinuousNorm` — `BanLat/OrderContinuous/Basic.lean`; statement (iii)
  of Theorem `ND`.
- `VectorSublattice`, `VectorSublattice.generated`,
  `VectorSublattice.topologicalClosure`, `VectorSublattice.sup_mem`, and
  `VectorSublattice.inf_mem` — `BanLat/Substructures/Sublattice.lean`; used for
  all sublattices and for the closed generated components.
- `LatticeSeminorm` — `BanLat/LocallySolid/WithSeminorms.lean`; used to bundle
  the paper's `p_n`.

BanLat has no installed paper-equivalent definitions of uo-convergence,
order/uo-adherence, Fatou norms, weak Fatou norms, Nakano constants, or density
character, so those are introduced locally.

### Mathlib

- `LatticeOrderedAddCommGroup.IsSolid` and
  `LatticeOrderedAddCommGroup.solidClosure` —
  `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean`.
- `Set.DirectedOn`, `IsLUB`, and `IsGLB` — used for directed positive suprema
  and the tree/ordinal claims.
- `BoundedContinuousFunction` and `BoundedContinuousFunction.indicator` — used
  for `C_b(I_n)` and the clopen cylinder indicators.
- `ContinuousMap` and notation `C(K, ℝ)` — used for the compact Hausdorff
  counterexample.
- `Finsupp`, `Finsupp.single`, `Finsupp.sum`, `Finsupp.filter`, and
  `Finsupp.mapDomain` — used for `c₀₀(G_n)`, band projections, and upshift.
- `Ordinal.CNF`, `Ordinal.omega0`, and `Ordinal.lift` —
  `Mathlib/SetTheory/Ordinal/CantorNormalForm.lean` and ordinal arithmetic;
  used for the relation `≺` and the stage construction.
- `Cardinal.mk`, cardinal exponentiation, `Order.succ`, and `Cardinal.ord` —
  used in all cardinal bounds and in the interpretation of `κ⁺`.

Mathlib provides the pointwise ordered algebra and solid norm on
`BoundedContinuousFunction A ℝ`, but the installed BanLat revision does not
provide the corresponding `NormedVectorLattice` instance. The local
`boundedContinuousFunctionNormedVectorLattice` declaration supplies only the
missing proof field and reuses all existing non-proof operations.

## Modeling decisions, deviations, and source issues

- A second norm on an already normed type is represented by `PaperLatticeNorm`
  rather than by competing global `Norm` instances. `IsCompleteFor`,
  `HasFatouProperty`, `HasWeakFatouProperty`, and `EquivalentNorms` therefore
  take the norm explicitly. This preserves every quantified scalar and norm
  comparison in the paper.
- `IsOrderComplete` is the paper's explicit nonempty-bounded-supremum predicate.
  It avoids installing an additional lattice instance on `C(K)`.
- No exact density-character declaration was found in the installed libraries;
  `densityCharacter` is defined as the infimum of cardinalities of dense sets.
- `OrderAdherenceTower` exposes zero, successor, and nonzero-limit stages.
  The paper's `ξ ≤ κ⁺` is rendered as
  `ξ ≤ Cardinal.ord (Order.succ κ)`.
- The definition of `cnfExtensionLT` is the literal list decomposition of the
  two Cantor normal forms: a common prefix, the last term of the upper ordinal,
  and the two alternatives stated in the paper. This records the intended
  interpretation of the special `m = 1` clause.
- `TreeComponent` and `FinalSpace` use the carrier of the relevant underlying
  submodule. BanLat's `VectorSublattice` currently has no inherited subtype
  lattice instances, so the pointwise lattice operations are exposed locally;
  their only missing parts are proof laws.
- The proof of Theorem `thm:solid-iterations` contains a displayed
  contradiction `1 < 0` after describing coordinates with values 1 and 0.
  This is read as the intended contradiction arising from
  `π_{ω^γ} ≤ π_ζ`; no false inequality is put into the interface.
- Order/uo-adherence quantify their witnessing net index in the same universe
  as the ambient vector lattice. A later generalization can universe-lift the
  index without changing any paper-facing declarations.

## Explicit proof-gap audit

Counts are literal `sorry` occurrences. A count greater than one means a
structure/instance has several independent proof-law fields; all non-proof data
in those declarations is explicit.

### `OrderClosures/OrderAdherence.lean` — 10

- One each: `orderAdherence_eq_solidOrderAdherence`, `subset_orderAdherence`,
  `orderAdherence_mono`, `subset_uoAdherence`,
  `OrderConvergesTo.uoConvergesTo`,
  `orderAdherence_subset_uoAdherence_subset`,
  `uoAdherence_eq_orderClosure_of_isOrderClosed`,
  `uoAdherence_eq_double_orderAdherence_and_stabilizes`,
  `isSolid_orderAdherence`, `solidHull_eq_iUnion_Icc`.

### `OrderClosures/GaoLeungProblem.lean` — 15

- One each: `gaoLeung_orderContinuous_characterization`, `gao_counterexample`,
  `orderAdherence_cardinality_bound`, `exists_solid_large_orderAdherence`,
  `solid_orderAdherence_cardinality_bound`,
  `signedPositiveSubsetSuprema_isOrderClosed`,
  `cnfExtensionLE_partialOrder_and_subrelation`,
  `cnfExtensionLT_linear_above`, `ordinalProjection` (continuity field),
  `ordinalProjection_incomparable_iInf`, `ordinalProjection_chain_iSup`,
  `gao_orderAdherence_stage_formula`, `ordinalProjection_strict_stage`,
  `solid_sets_require_arbitrarily_many_iterations`,
  `solid_generated_orderAdherence`.

### `OrderClosures/WeaklyFatou.lean` — 73

- Five each: `treeLatticeSeminorm`, `componentLatticeNorm`, `finalLatticeNorm`.
- Nine each: `treeComponentLattice`, `finalSpaceLattice`.
- Four: `componentC0Sublattice`.
- One definition/instance proof each: `TreeNode.child`, `TreeNode.parent`,
  `TreeNode.restrict`, `strictPrefix`,
  `boundedContinuousFunctionNormedVectorLattice`, `finiteTreeSup`,
  `treeComponentIsOrderedAddMonoid`, `treeComponentVectorLattice`,
  `componentRoot`, `componentTreeFunction`, `finalSpaceIsOrderedAddMonoid`,
  `finalSpaceVectorLattice`, `finalLargeVector`.
- One theorem proof each: `iteratedOrderAdherence_mono_and_scale`,
  `weakFatou_iterated_unitBall`, `fatou_iterated_unitBall`,
  `separable_weakSequentialNakano_implies_weakNakano`,
  `treeCylinder_isClopen`, `treeFunction_child_properties`,
  `treeCylinder_finite_cover`, `parentDisjoint_treeFunctions_iInf`,
  `treeSeminorm_norm_comparison`, `treeSeminorm_exact_basis`, `component_basic`,
  `treeUpshift_basic`, `tree_sharp_subsequence`, `tree_trim`, `tree_thinning`,
  `tree_transient`, `component_moderated`, `component_weakFatou`,
  `component_large_iterated_adherence`, `finalSpace_weakFatou`,
  `finalLargeVector_properties`, `finalSpace_not_equivalent_fatou`,
  `exists_weaklyFatou_not_equivalent_fatou`.

## Recommended proof order

1. Prove the local ordered-structure fields for bounded continuous functions,
   component subspaces, and the final subspace; then discharge the elementary
   tree-node membership and continuity fields.
2. Develop the shared adherence API: extensivity, monotonicity, solidity,
   order-to-uo convergence, the directed-positive characterization, and scaling.
3. Prove Gao--Leung Lemma 2.1 and the unit-ball Fatou reductions.
4. Prove the solid-set cardinality bound and the generated-solid-set lemma.
5. Prove P1/P2 for `cnfExtensionLT`, Claims 1--3, and then the transfinite
   iteration theorem; keep the Boolean/Stone-space counterexample independent.
6. Prove the finite-tree topology and combinatorics (`basic-tree`, finite cover,
   parent-disjoint infimum).
7. Prove the seminorm laws, norm comparison, exact basis values, completeness,
   and separability of each component.
8. Prove upshift, diagonal subsequence, trim, thinning, transient, and moderated
   in that order, then the component weak Fatou corollary.
9. Prove the component iteration result, the `c₀`-sum completeness/weak Fatou
   lemma, the `z_n` proposition, and finally the Fremlin counterexample.
10. Finish with imported-result-facing restatements (`ND`) and the two existential
    headline counterexamples once their construction lemmas are available.
