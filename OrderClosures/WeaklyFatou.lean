import OrderClosures.OrderAdherence

/-!
# Weakly Fatou norms

Formalization of the paper's construction of a weakly Fatou Banach lattice norm that is
not equivalent to any lattice norm with the Fatou property.
-/

namespace OrderClosures

open Set Filter Topology
open scoped NNReal Topology

universe u

/-! ## The two reductions -/

section Reductions

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Paper Lemma `lem:order-basic`. -/
theorem iteratedOrderAdherence_mono_and_scale
    {A B : Set X} (hA : LatticeOrderedAddCommGroup.IsSolid A)
    (hB : LatticeOrderedAddCommGroup.IsSolid B) {c : ℝ} (hc : 0 < c) :
    (A ⊆ B → ∀ m, iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m) ∧
      (orderAdherence (scaleSet c A) = scaleSet c (orderAdherence A) ∧
        ∀ m, iteratedOrderAdherence (scaleSet c A) m =
          scaleSet c (iteratedOrderAdherence A m)) := by
  sorry

/-- Paper Lemma `lem:fatou-order`, part (a). -/
theorem weakFatou_iterated_unitBall
    (p : PaperLatticeNorm X) {K : ℝ} (hK : HasWeakFatouProperty p K) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m ⊆
      scaleSet (K ^ m) (unitBallFor p) := by
  sorry

/-- Paper Lemma `lem:fatou-order`, part (b). -/
theorem fatou_iterated_unitBall
    (p : PaperLatticeNorm X) (hp : HasFatouProperty p) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
  sorry

/-- Weak sequential Nakano constant, Definition 3(a) in the paper. -/
def IsWeakSequentialNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (x : ℕ → X), Monotone x → (∀ m, 0 ≤ x m) →
    BddAbove (Set.range x) → (∀ m, p (x m) ≤ 1) →
      ∀ ε > 0, ∃ y : X, 0 ≤ y ∧ (∀ m, x m ≤ y) ∧ p y ≤ K + ε

/-- Weak Nakano constant, Definition 3(b) in the paper. -/
def IsWeakNakanoConstant (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ A : Set X, A ⊆ Ici 0 → DirectedOn (· ≤ ·) A → BddAbove A →
    (∀ x ∈ A, p x ≤ 1) → ∀ ε > 0,
      ∃ y : X, 0 ≤ y ∧ (∀ x ∈ A, x ≤ y) ∧ p y ≤ K + ε

/-- Fremlin's question, as a predicate on a vector lattice: every complete
weakly Fatou lattice norm admits an equivalent Fatou lattice norm. -/
def FremlinProperty : Prop :=
  ∀ p : PaperLatticeNorm X, IsCompleteFor p →
    (∃ K, HasWeakFatouProperty p K) →
      ∃ q : PaperLatticeNorm X, HasFatouProperty q ∧ EquivalentNorms p q

/-- Paper Proposition `prop:separable-reduction`. -/
theorem separable_weakSequentialNakano_implies_weakNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (hK : 1 ≤ K)
    (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K ∧
      HasWeakFatouProperty (norm : Y → ℝ) K := by
  sorry

end Reductions

/-! ## The finite tree -/

/-- Nodes of the finite-height tree `G_n = ⋃_{k ≤ n} ℕ^k`. -/
def TreeNode (n : ℕ) := {t : List ℕ // t.length ≤ n}

namespace TreeNode

/-- Level of a node. -/
def level {n : ℕ} (t : TreeNode n) : ℕ := t.1.length

/-- The root `∅`. -/
def root (n : ℕ) : TreeNode n := ⟨[], by simp⟩

/-- The child `t⌢m`. -/
def child {n : ℕ} (t : TreeNode n) (h : level t < n) (m : ℕ) : TreeNode n :=
  ⟨t.1 ++ [m], by
    sorry⟩

/-- The parent map, fixing the root. -/
def parent {n : ℕ} (t : TreeNode n) : TreeNode n :=
  ⟨t.1.dropLast, by
    sorry⟩

/-- Restriction `t|j`. -/
def restrict {n : ℕ} (t : TreeNode n) (j : ℕ) : TreeNode n :=
  ⟨t.1.take j, by
    sorry⟩

end TreeNode

/-- Non-terminal nodes `H_n`. -/
def TreeNonterminal (n : ℕ) := {t : TreeNode n // TreeNode.level t < n}

/-- The product space `I_n = ℕ^{H_n}`. -/
abbrev TreeProduct (n : ℕ) := TreeNonterminal n → ℕ

/-- The strict prefix `t|j`, regarded as a non-terminal node. -/
def strictPrefix {n : ℕ} (t : TreeNode n) (j : Fin (TreeNode.level t)) :
    TreeNonterminal n :=
  ⟨TreeNode.restrict t j, by
    sorry⟩

/-- The cylinder `E_t`. -/
def treeCylinder (n : ℕ) (t : TreeNode n) : Set (TreeProduct n) :=
  {α | ∀ j : Fin (TreeNode.level t), α (strictPrefix t j) ≤ t.1.get j}

/-- Paper Lemma `lem:basic-tree`, part (a). -/
theorem treeCylinder_isClopen (n : ℕ) (t : TreeNode n) :
    IsClopen (treeCylinder n t) := by
  sorry

/-- The characteristic function `s_t = χ_{E_t}`. -/
noncomputable def treeFunction (n : ℕ) (t : TreeNode n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (treeCylinder n t) (treeCylinder_isClopen n t)

/-- BanLat's vector-lattice structure is supplied here for real-valued bounded
continuous functions; all non-proof data comes from Mathlib's pointwise instances. -/
noncomputable instance boundedContinuousFunctionNormedVectorLattice
    (A : Type u) [TopologicalSpace A] :
    NormedVectorLattice (BoundedContinuousFunction A ℝ) where
  smul_le_smul_of_nonneg_left := by
    sorry

/-- Paper Lemma `lem:basic-tree`, parts (b) and (c). -/
theorem treeFunction_child_properties
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) :
    (∀ m, treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t ∧
      treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t) ∧
    Monotone (fun m ↦ treeFunction n (TreeNode.child t ht m)) ∧
      IsLUB (Set.range fun m ↦ treeFunction n (TreeNode.child t ht m))
        (treeFunction n t) := by
  sorry

/-- Paper Lemma `lem:finite-cover`. -/
theorem treeCylinder_finite_cover
    (n : ℕ) (t : TreeNode n) (F : Finset (TreeNode n))
    (hcover : ∀ α ∈ treeCylinder n t, ∃ u ∈ F, α ∈ treeCylinder n u) :
    ∃ u ∈ F, treeCylinder n t ⊆ treeCylinder n u := by
  sorry

/-- Parent-disjointness (`π`-disjointness in the source). -/
def ParentDisjoint {n : ℕ} (A B : Set (TreeNode n)) : Prop :=
  TreeNode.parent '' A ∩ TreeNode.parent '' B = ∅

/-- The finite union of the cylinders indexed by `F`. -/
def finiteCylinderUnion (n : ℕ) (F : Finset (TreeNode n)) : Set (TreeProduct n) :=
  ⋃ t : F, treeCylinder n t.1

/-- The finite supremum of the tree functions, represented by the indicator
of the corresponding finite union. -/
noncomputable def finiteTreeSup (n : ℕ) (F : Finset (TreeNode n)) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (finiteCylinderUnion n F) (by
    sorry)

/-- Paper Lemma `lem:pi-disjoint`. -/
theorem parentDisjoint_treeFunctions_iInf
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n)) (F j : Set (TreeNode n))) :
    IsGLB (Set.range fun m ↦ finiteTreeSup n (F m)) 0 := by
  sorry

/-! ## The induced seminorm -/

/-- `W_n = c₀₀(G_n)`. -/
abbrev TreeCoefficients (n : ℕ) := TreeNode n →₀ ℝ

/-- The basis vector `e_t`. -/
noncomputable def treeBasis {n : ℕ} (t : TreeNode n) : TreeCoefficients n :=
  Finsupp.single t 1

/-- The weighted `ℓ¹` functional `ρ_n`. -/
noncomputable def treeRho (n : ℕ) (w : TreeCoefficients n) : ℝ :=
  w.sum fun t a ↦ (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |a|

/-- The positive operator `T_n`. -/
noncomputable def treeOperator (n : ℕ) (w : TreeCoefficients n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  w.sum fun t a ↦ a • treeFunction n t

/-- The infimum formula defining `p_n`. -/
noncomputable def treeSeminorm (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ w : TreeCoefficients n,
    0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}

/-- Paper Lemma `lem:pn-seminorm`, bundled using BanLat's `LatticeSeminorm`. -/
noncomputable def treeLatticeSeminorm (n : ℕ) :
    LatticeSeminorm (BoundedContinuousFunction (TreeProduct n) ℝ) where
  toFun := treeSeminorm n
  map_zero' := by
    sorry
  add_le' := by
    sorry
  neg' := by
    sorry
  smul' := by
    sorry
  monotone_abs' := by
    sorry

/-- Paper Lemma `lem:norm-comparison`. -/
theorem treeSeminorm_norm_comparison
    (n : ℕ) (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n x ≤ ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ n * treeSeminorm n x := by
  sorry

/-- Paper Lemma `lem:exact-basis`. -/
theorem treeSeminorm_exact_basis (n : ℕ) (t : TreeNode n) :
    (∀ w : TreeCoefficients n, 0 ≤ w → treeFunction n t ≤ treeOperator n w →
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) ≤ treeRho n w) ∧
    treeSeminorm n (treeFunction n t) =
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  sorry

/-- The closed vector sublattice generated by the tree functions. -/
noncomputable def treeSublattice (n : ℕ) :
    VectorSublattice (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  (VectorSublattice.generated (Set.range (treeFunction n))).topologicalClosure

/-- The component space `X_n`, using the underlying submodule carrier. -/
abbrev TreeComponent (n : ℕ) := ↥(treeSublattice n).toSubmodule

/-- Pointwise lattice operations on the component subspace. -/
noncomputable instance treeComponentLattice (n : ℕ) : Lattice (TreeComponent n) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := by
    sorry
  le_trans := by
    sorry
  le_antisymm := by
    sorry
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, (treeSublattice n).sup_mem x.2 y.2⟩
  le_sup_left := by
    sorry
  le_sup_right := by
    sorry
  sup_le := by
    sorry
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, (treeSublattice n).inf_mem x.2 y.2⟩
  inf_le_left := by
    sorry
  inf_le_right := by
    sorry
  le_inf := by
    sorry

/-- Compatibility of the inherited addition with the pointwise order. -/
instance treeComponentIsOrderedAddMonoid (n : ℕ) :
    IsOrderedAddMonoid (TreeComponent n) where
  add_le_add_left := by
    sorry

/-- The component subspace is a real vector lattice. -/
noncomputable instance treeComponentVectorLattice (n : ℕ) :
    VectorLattice (TreeComponent n) where
  smul_le_smul_of_nonneg_left := by
    sorry

/-- The norm `p_n` restricted to `X_n`. -/
noncomputable def componentLatticeNorm (n : ℕ) : PaperLatticeNorm (TreeComponent n) where
  toFun := fun x ↦ treeSeminorm n x.1
  nonneg := by
    sorry
  eq_zero_iff := by
    sorry
  add_le := by
    sorry
  smul := by
    sorry
  solid := by
    sorry

/-- The constant function `1`, as an element of `X_n`. -/
noncomputable def componentRoot (n : ℕ) : TreeComponent n :=
  ⟨treeFunction n (TreeNode.root n), by
    sorry⟩

/-- Any tree function, viewed in the generated component. -/
noncomputable def componentTreeFunction (n : ℕ) (t : TreeNode n) : TreeComponent n :=
  ⟨treeFunction n t, by
    sorry⟩

/-- Paper Corollary `cor:Yn-basic`. -/
theorem component_basic (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      componentLatticeNorm n (componentRoot n) = 1 ∧
      (∀ t : TreeNode n, TreeNode.level t = n →
        componentLatticeNorm n (componentTreeFunction n t) =
          (2 : ℝ) ^ (-(n : ℤ))) := by
  sorry

/-! ## Bands, upshift, and the weak Fatou estimate -/

/-- Indexing the root band and the sibling bands. -/
abbrev TreeBandIndex (n : ℕ) := Option (TreeNonterminal n)

/-- Support of a sibling band, with `none` denoting the root band. -/
def treeBandSupport (n : ℕ) : TreeBandIndex n → Set (TreeNode n)
  | none => {TreeNode.root n}
  | some u => {t | TreeNode.parent t = u.1 ∧ t ≠ TreeNode.root n}

/-- Coordinate projection onto a sibling band. -/
noncomputable def treeBandProjection (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ t ∈ treeBandSupport n B

/-- Projection onto a finite family of sibling bands. -/
noncomputable def finiteBandProjection (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) : TreeCoefficients n :=
  by
    classical
    exact w.filter fun t ↦ ∃ B ∈ Λ, t ∈ treeBandSupport n B

/-- The upshift `S_n`, merging coefficients at their parents. -/
noncomputable def treeUpshift (n : ℕ) (w : TreeCoefficients n) : TreeCoefficients n :=
  w.mapDomain TreeNode.parent

/-- Paper Lemma `lem:upshift-basic`. -/
theorem treeUpshift_basic (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    treeRho n (treeUpshift n w) ≤ 2 * treeRho n w ∧
      treeOperator n w ≤ treeOperator n (treeUpshift n w) := by
  sorry

/-- Paper Lemma `lem:sharp-subsequence`. -/
theorem tree_sharp_subsequence
    (n : ℕ) (w : ℕ → TreeCoefficients n) (C : ℝ)
    (hw : ∀ m, treeRho n (w m) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : TreeBandIndex n,
      ∃ l : ℝ, Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w (φ m))))
        atTop (nhds l) := by
  sorry

/-- The bands occurring in infinitely many supports of a sequence. -/
def recurrentBands (n : ℕ) (w : ℕ → TreeCoefficients n) : Set (TreeBandIndex n) :=
  {B | Set.Infinite {m | (treeBandProjection n B (w m)).support.Nonempty}}

/-- Paper Lemma `lem:trim`. -/
theorem tree_trim
    (n : ℕ) (x : ℕ → TreeComponent n) (w : ℕ → TreeCoefficients n)
    {ε : ℝ} (hε : 0 < ε)
    (hdom : ∀ m, (x m).1 ≤ treeOperator n (w m))
    (hrho : ∀ m, treeRho n (w m) < 1 + ε / 4) :
    ∃ w' : ℕ → TreeCoefficients n,
      (∀ m, 0 ≤ w' m ∧ (x m).1 ≤ treeOperator n (w' m) ∧
        treeRho n (w' m) < 1 + ε / 2) ∧
      (recurrentBands n w').Finite := by
  sorry

/-- Paper Lemma `lem:thinning`. -/
theorem tree_thinning
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hΛ : recurrentBands n w ⊆ (Λ : Set (TreeBandIndex n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w (φ m))).support.Nonempty}.Subsingleton := by
  sorry

/-- Paper Lemma `lem:transient`. -/
theorem tree_transient
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hdis : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w m)).support.Nonempty}.Subsingleton) :
    let v := fun m ↦ w m - finiteBandProjection n Λ (w m)
    (Pairwise fun i j ↦ ParentDisjoint ((v i).support : Set (TreeNode n))
      ((v j).support : Set (TreeNode n))) ∧
    ∀ z : BoundedContinuousFunction (TreeProduct n) ℝ,
      0 ≤ z → (∀ m, z ≤ treeOperator n (v m)) → z = 0 := by
  sorry

/-- Paper Proposition `prop:moderated`. -/
theorem component_moderated
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧
      (∀ m, (x m).1 ≤ treeOperator n w) ∧ treeRho n w ≤ 2 + ε := by
  sorry

/-- Paper Corollary `cor:weak-fatou`. -/
theorem component_weakFatou (n : ℕ) :
    IsWeakNakanoConstant (componentLatticeNorm n) 2 ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 := by
  sorry

/-! ## Component spaces and the final `c₀`-sum -/

/-- Terminal tree functions `L_n`. -/
def terminalTreeFunctions (n : ℕ) : Set (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  treeFunction n '' {t : TreeNode n | TreeNode.level t = n}

/-- Paper Proposition `prop:component`. -/
theorem component_large_iterated_adherence (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 ∧
      ((2 : ℝ) ^ n • componentRoot n) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n ∧
      componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) = (2 : ℝ) ^ n := by
  sorry

/-- The ambient product of all component spaces. -/
abbrev ComponentProduct := ∀ n : ℕ, TreeComponent n

/-- The usual `c₀` condition for the component norms. -/
def componentVanishes (x : ComponentProduct) : Prop :=
  Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0)

/-- The concrete `c₀`-sum as a vector sublattice of the component product. -/
noncomputable def componentC0Sublattice : VectorSublattice ComponentProduct where
  carrier := {x | componentVanishes x}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry
  sup_mem' := by
    sorry

/-- The final space `X = c₀(X_n)`, using the underlying submodule carrier. -/
abbrev FinalSpace := ↥componentC0Sublattice.toSubmodule

/-- Pointwise lattice operations on the final `c₀`-sum. -/
noncomputable instance finalSpaceLattice : Lattice FinalSpace where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := by
    sorry
  le_trans := by
    sorry
  le_antisymm := by
    sorry
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, componentC0Sublattice.sup_mem x.2 y.2⟩
  le_sup_left := by
    sorry
  le_sup_right := by
    sorry
  sup_le := by
    sorry
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, componentC0Sublattice.inf_mem x.2 y.2⟩
  inf_le_left := by
    sorry
  inf_le_right := by
    sorry
  le_inf := by
    sorry

/-- Compatibility of addition and order on the final space. -/
instance finalSpaceIsOrderedAddMonoid : IsOrderedAddMonoid FinalSpace where
  add_le_add_left := by
    sorry

/-- The final `c₀`-sum is a real vector lattice. -/
noncomputable instance finalSpaceVectorLattice : VectorLattice FinalSpace where
  smul_le_smul_of_nonneg_left := by
    sorry

/-- The supremum norm on the final `c₀`-sum. -/
noncomputable def finalNormValue (x : FinalSpace) : ℝ :=
  sSup (Set.range fun n ↦ componentLatticeNorm n (x.1 n))

/-- The final lattice norm, with all its laws exposed as proof obligations. -/
noncomputable def finalLatticeNorm : PaperLatticeNorm FinalSpace where
  toFun := finalNormValue
  nonneg := by
    sorry
  eq_zero_iff := by
    sorry
  add_le := by
    sorry
  smul := by
    sorry
  solid := by
    sorry

/-- Paper Lemma `lem:c0-weak-fatou`. -/
theorem finalSpace_weakFatou :
    IsCompleteFor finalLatticeNorm ∧ HasWeakFatouProperty finalLatticeNorm 2 := by
  sorry

/-- The vector `z_n`, supported in coordinate `n`. -/
noncomputable def finalLargeVector (n : ℕ) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0, by
    sorry⟩

/-- Paper Proposition `prop:zn`. -/
theorem finalLargeVector_properties (n : ℕ) :
    finalLargeVector n ∈ iteratedOrderAdherence (unitBallFor finalLatticeNorm) n ∧
      finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n := by
  sorry

/-- The constructed `c₀`-sum admits no equivalent Fatou lattice norm. -/
theorem finalSpace_not_equivalent_fatou :
    ∀ q : PaperLatticeNorm FinalSpace,
      HasFatouProperty q → ¬ EquivalentNorms finalLatticeNorm q := by
  sorry

/-- Paper Theorem `thm:fremlin-main`. -/
theorem exists_weaklyFatou_not_equivalent_fatou :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ p : PaperLatticeNorm X, IsCompleteFor p ∧ HasWeakFatouProperty p 2 ∧
        ∀ q : PaperLatticeNorm X, HasFatouProperty q → ¬ EquivalentNorms p q := by
  sorry

end OrderClosures
