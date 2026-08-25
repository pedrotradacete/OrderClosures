import BanLat
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Order adherence

Shared definitions and results about order convergence, unbounded-order convergence,
solid hulls, and iterated order adherence used throughout the formalization.
-/

open Set

namespace OrderClosures

universe u v

section Convergence

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- Unbounded-order convergence, defined using BanLat's `OrderConvergesTo`. -/
def UOConvergesTo {ι : Type v} [Preorder ι] (f : ι → X) (x : X) : Prop :=
  ∀ a : X, 0 ≤ a → OrderConvergesTo (fun i ↦ |f i - x| ⊓ a) 0

/-- The order adherence of a set: limits of order-convergent nets in the set. -/
def orderAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ OrderConvergesTo f x}

/-- The unbounded-order adherence of a set. -/
def uoAdherence (A : Set X) : Set X :=
  {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι),
    ∃ f : ι → X, (∀ i, f i ∈ A) ∧ UOConvergesTo f x}

/-- A set is order closed when it contains the order limits of all its nets. -/
def IsOrderClosed (A : Set X) : Prop := orderAdherence A ⊆ A

/-- A set is unbounded-order closed when it contains the uo-limits of all its nets. -/
def IsUOClosed (A : Set X) : Prop := uoAdherence A ⊆ A

/-- The least order-closed set containing `A`. -/
def orderClosure (A : Set X) : Set X :=
  ⋂₀ {B : Set X | A ⊆ B ∧ IsOrderClosed B}

/-- The paper's directed-supremum description of the positive part of order adherence. -/
def directedPositiveAdherence (A : Set X) : Set X :=
  {x | 0 ≤ x ∧ ∃ B : Set X,
    B ⊆ A ∩ {y | 0 ≤ y} ∧ B.Nonempty ∧ DirectedOn (· ≤ ·) B ∧ IsLUB B x}

/-- For a solid set, order adherence is the solid hull of its directed positive suprema. -/
def solidOrderAdherence (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure (directedPositiveAdherence A)

/-- Finite iteration of order adherence. -/
def iteratedOrderAdherence (A : Set X) : ℕ → Set X
  | 0 => A
  | n + 1 => orderAdherence (iteratedOrderAdherence A n)

/-- A transfinite order-adherence tower. At limit stages it is the union of earlier stages. -/
structure OrderAdherenceTower (A : Set X) where
  stage : Ordinal.{u} → Set X
  stage_zero : stage 0 = A
  stage_succ : ∀ ξ, stage (Order.succ ξ) = orderAdherence (stage ξ)
  stage_limit : ∀ ξ, Order.IsSuccLimit ξ →
    stage ξ = ⋃ η : Set.Iio ξ, stage η.1

/-- Exactly `ξ` stages are needed when all earlier stages are proper and stage `ξ` is closed. -/
def NeedsOrderAdherenceIterations (A : Set X) (ξ : Ordinal.{u}) : Prop :=
  ∃ T : OrderAdherenceTower A,
    (∀ η < ξ, T.stage η ⊂ T.stage (Order.succ η)) ∧ IsOrderClosed (T.stage ξ)

/-- The generic net definition and the directed-positive definition agree for solid sets. -/
theorem orderAdherence_eq_solidOrderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    orderAdherence A = solidOrderAdherence A := by
  sorry

/-- Order adherence is extensive. -/
theorem subset_orderAdherence (A : Set X) : A ⊆ orderAdherence A := by
  sorry

/-- Order adherence is monotone. -/
theorem orderAdherence_mono : Monotone (orderAdherence : Set X → Set X) := by
  sorry

/-- Uo-adherence is extensive. -/
theorem subset_uoAdherence (A : Set X) : A ⊆ uoAdherence A := by
  sorry

/-- Order convergence implies unbounded-order convergence. -/
theorem OrderConvergesTo.uoConvergesTo {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {f : ι → X} {x : X}
    (h : OrderConvergesTo f x) : UOConvergesTo f x := by
  sorry

/-- Gao--Leung, Lemma 2.1: the two adherences lie within two order-adherence steps. -/
theorem orderAdherence_subset_uoAdherence_subset {Y : VectorSublattice X} :
    orderAdherence (Y : Set X) ⊆ uoAdherence (Y : Set X) ∧
      uoAdherence (Y : Set X) ⊆ orderAdherence (orderAdherence (Y : Set X)) := by
  sorry

/-- If the uo-adherence is order closed, it is the order closure. -/
theorem uoAdherence_eq_orderClosure_of_isOrderClosed {Y : VectorSublattice X}
    (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderClosure (Y : Set X) := by
  sorry

/-- The remaining equalities and stabilization stated after Gao--Leung Lemma 2.1. -/
theorem uoAdherence_eq_double_orderAdherence_and_stabilizes
    {Y : VectorSublattice X} (hY : IsOrderClosed (uoAdherence (Y : Set X))) :
    uoAdherence (Y : Set X) = orderAdherence (orderAdherence (Y : Set X)) ∧
      orderAdherence (orderAdherence (orderAdherence (Y : Set X))) =
        orderAdherence (orderAdherence (Y : Set X)) := by
  sorry

/-- The order adherence of a solid set is solid. -/
theorem isSolid_orderAdherence {A : Set X}
    (hA : LatticeOrderedAddCommGroup.IsSolid A) :
    LatticeOrderedAddCommGroup.IsSolid (orderAdherence A) := by
  sorry

end Convergence

section Solidity

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- The least solid set containing `A`, using Mathlib's solid closure. -/
abbrev solidHull (A : Set X) : Set X :=
  LatticeOrderedAddCommGroup.solidClosure A

/-- The interval-union description of the solid hull used in the paper. -/
theorem solidHull_eq_iUnion_Icc (A : Set X) :
    solidHull A = ⋃ a ∈ A, Set.Icc (-|a|) |a| := by
  sorry

/-- The least cardinality of a set whose solid hull is `S`. -/
noncomputable def solidGeneratorNumber (S : Set X) : Cardinal :=
  sInf {κ : Cardinal | ∃ A : Set X, Cardinal.mk A = κ ∧ solidHull A = S}

/-- Scalar dilation of a set. -/
def scaleSet (a : ℝ) (A : Set X) [SMul ℝ X] : Set X :=
  (fun x ↦ a • x) '' A

/-- A set-theoretic unit ball for a specified real-valued norm. -/
def unitBallFor (p : X → ℝ) : Set X := {x | p x ≤ 1}

end Solidity

section CompletenessAndNorms

/-- Order completeness, stated without installing a second lattice instance. -/
def IsOrderComplete (X : Type u) [Preorder X] : Prop :=
  ∀ A : Set X, A.Nonempty → BddAbove A → ∃ x, IsLUB A x

/-- Density character: the least cardinality of a dense subset. -/
noncomputable def densityCharacter (X : Type u) [TopologicalSpace X] : Cardinal :=
  sInf {κ : Cardinal | ∃ D : Set X, Dense D ∧ Cardinal.mk D = κ}

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [Module ℝ X]

/-- A real lattice norm recorded independently of the ambient typeclass norm. -/
structure PaperLatticeNorm (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [Module ℝ X] where
  toFun : X → ℝ
  nonneg : ∀ x, 0 ≤ toFun x
  eq_zero_iff : ∀ x, toFun x = 0 ↔ x = 0
  add_le : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
  smul : ∀ (a : ℝ) x, toFun (a • x) = |a| * toFun x
  solid : ∀ {x y}, |x| ≤ |y| → toFun x ≤ toFun y

instance : CoeFun (PaperLatticeNorm X) (fun _ ↦ X → ℝ) := ⟨PaperLatticeNorm.toFun⟩

/-- Sequential completeness for the metric induced by `p`. -/
def IsCompleteFor (p : X → ℝ) : Prop :=
  ∀ f : ℕ → X,
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, p (f m - f n) < ε) →
      ∃ x, ∀ ε > 0, ∃ N, ∀ n ≥ N, p (f n - x) < ε

/-- Fatou's property for a specified lattice norm. -/
def HasFatouProperty (p : X → ℝ) : Prop :=
  ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → IsLUB (p '' Set.range f) (p x)

/-- Weak Fatou property with constant `K` for a specified lattice norm. -/
def HasWeakFatouProperty (p : X → ℝ) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → X) (x : X), Monotone f → (∀ i, 0 ≤ f i) →
      IsLUB (Set.range f) x → ∀ c, (∀ i, p (f i) ≤ c) → p x ≤ K * c

/-- Equivalence of two norms through two positive comparison constants. -/
def EquivalentNorms (p q : X → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * p x ≤ q x ∧ q x ≤ C * p x

/-- The ambient norm as a paper lattice norm. -/
noncomputable def ambientLatticeNorm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] : PaperLatticeNorm Y where
  toFun := norm
  nonneg := norm_nonneg
  eq_zero_iff := fun _ ↦ norm_eq_zero
  add_le := norm_add_le
  smul := norm_smul
  solid := fun h ↦ HasSolidNorm.solid h

end CompletenessAndNorms

end OrderClosures
