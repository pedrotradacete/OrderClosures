import OrderClosures.OrderAdherence
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# The Gao--Leung problem

Formalization of the paper's counterexamples concerning order and unbounded-order
adherences of sublattices and solid sets.
-/

namespace OrderClosures

open Set

universe u v

section GaoLeungTheorem

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X] [SigmaConditionallyCompleteLattice X]

/-- Gao--Leung, Theorem 2.7 (paper Theorem `ND`). -/
theorem gaoLeung_orderContinuous_characterization :
    ((∀ Y : VectorSublattice X, IsOrderClosed (orderAdherence (Y : Set X))) ↔
      (∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X))) ∧
    ((∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X)) ↔
      IsOrderContinuousNorm X) := by
  sorry

/-- The Gao--Leung question, as a predicate on an ambient vector lattice. -/
def GaoLeungProperty (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop :=
  ∀ Y : VectorSublattice X, IsOrderClosed (uoAdherence (Y : Set X))

end GaoLeungTheorem

section Counterexample

/-- Paper Proposition `prop:gao-counterexample`: the Gao--Leung question has
a counterexample of arbitrarily large density character. -/
theorem gao_counterexample (κ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K),
      IsOrderComplete C(K, ℝ) ∧ κ ≤ densityCharacter C(K, ℝ) ∧
      ∃ Y : VectorSublattice C(K, ℝ),
        IsClosed (Y : Set C(K, ℝ)) ∧
          TopologicalSpace.IsSeparable (Y : Set C(K, ℝ)) ∧
          ∀ Z : VectorSublattice C(K, ℝ),
            Y ≤ Z → IsOrderClosed (Z : Set C(K, ℝ)) → Z = ⊤ := by
  sorry

/-- Paper Remark `rem:gao-cardinality`: cardinality of an arbitrary order adherence. -/
theorem orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (D : Set X) :
    Cardinal.mk (orderAdherence D) ≤
      (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
  sorry

/-- Paper Proposition `prop:solid-large-order-closure`. -/
theorem exists_solid_large_orderAdherence (κ : Cardinal.{u}) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.aleph0 ∧
        κ ≤ solidGeneratorNumber (orderAdherence S) := by
  sorry

/-- Paper Proposition `prop:cardinalitybound`. -/
theorem solid_orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    Cardinal.mk (orderAdherence S) ≤ (2 : Cardinal) ^ Cardinal.mk S := by
  sorry

/-- The class of all suprema of subsets of the positive part of `S`, used in
the proof of Proposition `prop:cardinalitybound`. -/
def positiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (S : Set X) : Set X :=
  {x | ∃ A : Set X, A ⊆ S ∩ Ici 0 ∧ IsLUB A x}

/-- The order-closed envelope used for the cardinality estimate. -/
def signedPositiveSubsetSuprema
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    (S : Set X) : Set X :=
  {x | x⁺ ∈ positiveSubsetSuprema S ∧ x⁻ ∈ positiveSubsetSuprema S}

/-- Unnumbered assertion in the proof of `prop:cardinalitybound`. -/
theorem signedPositiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (signedPositiveSubsetSuprema S) := by
  sorry

end Counterexample

section OrdinalConstruction

/-- The relation `≺` from the proof of Theorem `thm:solid-iterations`, expressed
directly using Mathlib's Cantor normal form at base `ω`. -/
def cnfExtensionLT (ζ ζ' : Ordinal.{u}) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u})) (β c γ d : Ordinal.{u}),
    Ordinal.CNF Ordinal.omega0 ζ = pre ++ (β, c) :: tail ∧
      Ordinal.CNF Ordinal.omega0 ζ' = pre ++ [(γ, d)] ∧
      ((γ = β ∧ c < d) ∨
        (β < γ ∧
          (pre = [] ∨ ∃ δ e, pre.getLast? = some (δ, e) ∧ γ < δ)))

/-- Reflexive closure of the paper's relation `≺`. -/
def cnfExtensionLE (ζ ζ' : Ordinal.{u}) : Prop := ζ = ζ' ∨ cnfExtensionLT ζ ζ'

/-- Property P1 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLE_partialOrder_and_subrelation :
    IsPartialOrder (Ordinal.{u}) cnfExtensionLE ∧
      ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLE ζ ζ' → ζ ≤ ζ' := by
  sorry

/-- Property P2 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLT_linear_above (ζ : Ordinal.{u}) :
    ∀ {η η' : Ordinal.{u}}, cnfExtensionLT ζ η → cnfExtensionLT ζ η' →
      (cnfExtensionLT η η' ↔ η < η') := by
  sorry

/-- Coordinate indices in the compact ordinal construction. -/
abbrev GaoIndex (ξ : Ordinal.{u}) := Set.Iic (Ordinal.omega0 ^ ξ + 1)

/-- The closed subspace of the Cantor cube used in the proof of
`thm:solid-iterations`. -/
def GaoCompactSpace (ξ : Ordinal.{u}) :=
  {x : GaoIndex ξ → Bool |
    ∀ a b : GaoIndex ξ, cnfExtensionLT a.1 b.1 → x a ≤ x b}

/-- Coordinate projection `π_ζ` on the Gao compact space. -/
noncomputable def ordinalProjection (ξ : Ordinal.{u}) (ζ : GaoIndex ξ) :
    C(GaoCompactSpace ξ, ℝ) where
  toFun := fun x ↦ if x.1 ζ then 1 else 0
  continuous_toFun := by
    sorry

/-- The least exponent in the Cantor normal form of an ordinal (zero at the
empty normal form). -/
noncomputable def leastCNFExponent (ζ : Ordinal.{u}) : Ordinal.{u} :=
  ((Ordinal.CNF Ordinal.omega0 ζ).getLast?.map Prod.fst).getD 0

/-- The index set `Z_β` from Claim 3. -/
def GaoStageIndices (ξ β : Ordinal.{u}) : Set (GaoIndex ξ) :=
  {ζ | ζ.1 ≤ Ordinal.omega0 ^ ξ ∧ leastCNFExponent ζ.1 < β}

/-- The solid set `S_β` from Claim 3. -/
def GaoStageSet (ξ β : Ordinal.{u}) : Set C(GaoCompactSpace ξ, ℝ) :=
  {f | ∃ ζ ∈ GaoStageIndices ξ β, |f| ≤ ordinalProjection ξ ζ}

/-- Claim 1 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_incomparable_iInf
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (hZ : Z.Infinite)
    (hinc : Z.Pairwise fun ζ ζ' ↦ ¬ cnfExtensionLE ζ.1 ζ'.1) :
    IsGLB (ordinalProjection ξ '' Z) 0 := by
  sorry

/-- Claim 2 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_chain_iSup
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    IsLUB (ordinalProjection ξ '' Z) (ordinalProjection ξ α) := by
  sorry

/-- Claim 3 in the proof of Theorem `thm:solid-iterations`. -/
theorem gao_orderAdherence_stage_formula
    (ξ : Ordinal.{u}) (T : OrderAdherenceTower (GaoStageSet ξ 1)) :
    ∀ β ≤ ξ, T.stage (Ordinal.lift.{u + 1, u} β) = GaoStageSet ξ (1 + β) := by
  sorry

/-- The strict witness separating consecutive stages in Claim 3. -/
theorem ordinalProjection_strict_stage
    (ξ γ : Ordinal.{u}) (hγ : γ ≤ ξ) :
    ∃ ζ : GaoIndex ξ,
      ordinalProjection ξ ζ ∈ GaoStageSet ξ (γ + 1) ∧
        ordinalProjection ξ ζ ∉ GaoStageSet ξ γ := by
  sorry

/-- Paper Theorem `thm:solid-iterations`. Here `κ⁺` is represented by the
initial ordinal of the successor cardinal. -/
theorem solid_sets_require_arbitrarily_many_iterations
    (κ : Cardinal.{u}) (ξ : Ordinal.{u})
    (hξ : ξ ≤ Cardinal.ord (Order.succ κ)) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X)
      (_ : IsOrderedAddMonoid X) (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = κ ∧ NeedsOrderAdherenceIterations S ξ := by
  sorry

/-- Paper Lemma `lem:solid-generated-order-adh`. -/
theorem solid_generated_orderAdherence
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {G : Set X} (hG : G ⊆ Ici 0) :
    orderAdherence (solidHull G) =
      {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (a : ι → X),
        (∀ i, a i ∈ G) ∧
          OrderConvergesTo (fun i ↦ |x| ⊓ a i) |x| ∧
          IsLUB (Set.range fun i ↦ |x| ⊓ a i) |x|} := by
  sorry

end OrdinalConstruction

end OrderClosures
