import OrderClosures.Solovay
import OrderClosures.GaoLeungCharacterization
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# The Gao--Leung problem and counterexamples

Formalization of the paper's counterexamples concerning order and unbounded-order
adherences of sublattices and solid sets.
-/

namespace OrderClosures

open Set

universe u v

section GaoLeungTheorem

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
  induction κ using Cardinal.inductionOn with
  | _ Gamma =>
    classical
    obtain ⟨lin, wf⟩ := exists_wellFoundedLT Gamma
    letI : LinearOrder Gamma := lin
    letI : WellFoundedLT Gamma := wf
    letI : TopologicalSpace Gamma := ⊥
    letI : DiscreteTopology Gamma := ⟨rfl⟩
    let B := RegularOpen (SolovayProduct Gamma)
    let K := BooleanStone B
    refine ⟨K, inferInstance, inferInstance, inferInstance,
      isOrderComplete_continuousMap K, ?_,
      solovayVectorSublattice Gamma,
      isClosed_solovayVectorSublattice Gamma,
      isSeparable_solovayVectorSublattice Gamma, ?_⟩
    · calc
        Cardinal.mk Gamma ≤ Cardinal.mk B :=
          Cardinal.mk_le_of_injective (solovayA_injective Gamma 0)
        _ ≤ densityCharacter C(K, ℝ) :=
          cardinalMk_le_densityCharacter_booleanStoneContinuousMap B
    · intro Z hYZ hZorder
      exact solovayVectorSublattice_maximalOrderClosed Gamma Z hYZ hZorder

/-- Paper Remark `rem:gao-cardinality`: cardinality of an arbitrary order adherence. -/
theorem orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (D : Set X) :
    Cardinal.mk (orderAdherence D) ≤
      (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
  let Φ : orderAdherence D → Set (Set D) := fun x ↦
    {A | x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A)}
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    rcases x.2 with ⟨ι, hpre, hdir, hnon, f, hfD, hfx⟩
    letI : Preorder ι := hpre
    letI : IsDirected ι (· ≤ ·) := hdir
    letI : Nonempty ι := hnon
    rcases hfx with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnonneg, hrglb, hbound⟩
    letI : Preorder κ := hκpre
    letI : IsDirected κ (· ≤ ·) := hκdir
    letI : Nonempty κ := hκnon
    have hk : ∃ k, ¬ |x.1 - y.1| ≤ r k := by
      by_contra hk
      push Not at hk
      have hlower : |x.1 - y.1| ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        exact hk k
      have habs : |x.1 - y.1| = 0 :=
        le_antisymm (hrglb.2 hlower) (abs_nonneg _)
      exact hne (sub_eq_zero.mp ((abs_eq_zero_iff_zero _).mp habs))
    obtain ⟨k, hk⟩ := hk
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (hbound k)
    let fD : ι → D := fun i ↦ ⟨f i, hfD i⟩
    let A : Set D := Set.range (fun i : Set.Ici i₀ ↦ fD i.1)
    have hIci : DirectedOn (· ≤ ·) (Set.Ici i₀) := by
      intro a ha b hb
      obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
      exact ⟨c, ha.trans hac, hac, hbc⟩
    letI : IsDirectedOrder (Set.Ici i₀) := hIci.isDirectedOrder
    letI : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
    have hrestrict : OrderConvergesTo (fun i : Set.Ici i₀ ↦ f i.1) x.1 := by
      refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnonneg,
        hrglb, ?_⟩
      intro l
      obtain ⟨i₁, hi₁⟩ := Filter.eventually_atTop.mp (hbound l)
      obtain ⟨m, hi₀m, hi₁m⟩ := directed_of (· ≤ ·) i₀ i₁
      apply Filter.eventually_atTop.mpr
      refine ⟨⟨m, hi₀m⟩, ?_⟩
      intro j hj
      exact hi₁ j.1 (hi₁m.trans hj)
    have hxA : x.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) := by
      refine ⟨Set.Ici i₀, inferInstance, inferInstance, inferInstance,
        fun i ↦ f i.1, ?_, hrestrict⟩
      intro i
      exact ⟨fD i.1, ⟨i, rfl⟩, rfl⟩
    have hxA' : A ∈ Φ x := hxA
    have hyA' : A ∈ Φ y := by
      rw [← hxy]
      exact hxA'
    change y.1 ∈ orderAdherence ((fun z : D ↦ z.1) '' A) at hyA'
    rcases hyA' with ⟨τ, hτpre, hτdir, hτnon, a, haA, hay⟩
    letI : Preorder τ := hτpre
    letI : IsDirected τ (· ≤ ·) := hτdir
    letI : Nonempty τ := hτnon
    have habound : ∀ j, |a j - x.1| ≤ r k := by
      intro j
      rcases haA j with ⟨z, ⟨i, rfl⟩, hza⟩
      rw [← hza]
      exact hi₀ i.1 i.2
    have hybound : |y.1 - x.1| ≤ r k :=
      (hay.sub (orderConvergesTo_const x.1)).abs.le_of_forall_le habound
    exact hk (by simpa [abs_sub_comm] using hybound)
  calc
    Cardinal.mk (orderAdherence D) ≤ Cardinal.mk (Set (Set D)) :=
      Cardinal.mk_le_of_injective hΦ
    _ = (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.mk D) := by
      rw [Cardinal.mk_set, Cardinal.mk_set]

/-- Paper Proposition `prop:solid-large-order-closure`. -/
theorem exists_solid_large_orderAdherence (κ : Cardinal.{u}) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.aleph0 ∧
        κ ≤ solidGeneratorNumber (orderAdherence S) := by
  induction κ using Cardinal.inductionOn with
  | _ Γ =>
    let X := Option Γ → ℕ → ℝ
    let g : ℕ → X := fun n _ m ↦ if m ≤ n then (n + 1 : ℕ) else 0
    let S : Set X := solidHull (Set.range g)
    refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, S,
      LatticeOrderedAddCommGroup.isSolid_solidClosure _, ?_, ?_⟩
    · apply le_antisymm
      · calc
          solidGeneratorNumber S ≤ Cardinal.mk (Set.range g) := by
            apply csInf_le'
            exact ⟨Set.range g, rfl, rfl⟩
          _ ≤ Cardinal.aleph0 := by
            simpa [Cardinal.mk_nat] using Cardinal.mk_range_le_lift (f := g)
      · apply le_csInf
        · exact ⟨Cardinal.mk (Set.range g), Set.range g, rfl, rfl⟩
        · intro c hc
          rcases hc with ⟨A, hAc, hAS⟩
          rw [← hAc]
          by_contra hAfin
          have hAlt : Cardinal.mk A < Cardinal.aleph0 := lt_of_not_ge hAfin
          letI : Finite A := Cardinal.mk_lt_aleph0_iff.mp hAlt
          have hchoice : ∀ a : A, ∃ n, |a.1| ≤ |g n| := by
            intro a
            have haS : a.1 ∈ S := by
              rw [← hAS]
              exact ⟨a.1, a.2, le_rfl⟩
            rcases haS with ⟨b, ⟨n, rfl⟩, hab⟩
            exact ⟨n, hab⟩
          choose N hN using hchoice
          obtain ⟨M, hM⟩ := Finite.exists_le N
          have hgS : g (M + 1) ∈ S := ⟨g (M + 1), ⟨M + 1, rfl⟩, le_rfl⟩
          rw [← hAS] at hgS
          rcases hgS with ⟨a, haA, hga⟩
          let aa : A := ⟨a, haA⟩
          have ha0 := hN aa (none : Option Γ) (M + 1)
          have hga0 := hga (none : Option Γ) (M + 1)
          have hNM := hM aa
          dsimp [g, X] at ha0 hga0
          rw [if_neg (by omega)] at ha0
          simp only [abs_zero] at ha0
          rw [if_pos (by omega)] at hga0
          norm_num at hga0
          change |a none (M + 1)| ≤ 0 at ha0
          have hpos : (0 : ℝ) < |(M : ℝ) + 1 + 1| := by positivity
          linarith
    · have hadh : orderAdherence S = Set.univ := by
        ext f
        simp only [Set.mem_univ, iff_true]
        have hsolid : LatticeOrderedAddCommGroup.IsSolid (orderAdherence S) := by
          rw [orderAdherence_eq_solidOrderAdherence
            (LatticeOrderedAddCommGroup.isSolid_solidClosure (Set.range g))]
          exact LatticeOrderedAddCommGroup.isSolid_solidClosure _
        apply hsolid (x := |f|) (y := f)
        · let I := ULift.{u} ℕ
          let p : I → X := fun n ↦ |f| ⊓ g n.down
          have hg_nonneg : ∀ n, 0 ≤ g n := by
            intro n γ m
            simp only [g, X]
            split_ifs <;> positivity
          have hg_mono : Monotone g := by
            intro n k hnk γ m
            simp only [g, X]
            by_cases hmn : m ≤ n
            · rw [if_pos hmn, if_pos (hmn.trans hnk)]
              exact_mod_cast Nat.succ_le_succ hnk
            · rw [if_neg hmn]
              split_ifs <;> positivity
          have hp_mono : Monotone p := fun _ _ hnk ↦
            inf_le_inf_left _ (hg_mono hnk)
          have hp_lub : IsLUB (Set.range p) |f| := by
            constructor
            · rintro _ ⟨n, rfl⟩
              exact inf_le_left
            · intro c hc γ m
              obtain ⟨k, hk⟩ := exists_nat_ge |f γ m|
              let n := max m k
              have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_max_right m k
              have hfn : |f γ m| ≤ (n + 1 : ℕ) := by
                norm_num
                linarith
              have hcn := hc ⟨ULift.up n, rfl⟩ γ m
              dsimp [p, g, X, n] at hcn
              rw [if_pos (Nat.le_max_left m k)] at hcn
              rw [inf_eq_left.mpr (by simpa [n] using hfn)] at hcn
              simpa [abs_of_nonneg] using hcn
          refine ⟨I, inferInstance, inferInstance, inferInstance, p, ?_,
            orderConvergesTo_of_monotone_isLUB hp_mono hp_lub⟩
          intro n
          refine ⟨g n.down, ⟨n.down, rfl⟩, ?_⟩
          have hp_nonneg : 0 ≤ p n := le_inf (abs_nonneg f) (hg_nonneg n.down)
          rw [abs_of_nonneg hp_nonneg, abs_of_nonneg (hg_nonneg n.down)]
          exact (inf_le_right : |f| ⊓ g n.down ≤ g n.down)
        · simp
      rw [hadh]
      apply le_csInf
      · refine ⟨Cardinal.mk (Set.univ : Set X), Set.univ, rfl, ?_⟩
        ext x
        constructor
        · exact fun _ ↦ Set.mem_univ x
        · intro _
          exact ⟨x, Set.mem_univ x, le_rfl⟩
      · intro c hc
        rcases hc with ⟨A, hAc, hAuniv⟩
        rw [← hAc]
        by_contra hsmall
        have hlt : Cardinal.mk A < Cardinal.mk Γ := lt_of_not_ge hsmall
        obtain ⟨e⟩ := (Cardinal.le_def A Γ).mp hlt.le
        let d : Γ → ℝ := Function.extend e
          (fun a : A ↦ |a.1 (some (e a)) 0| + 1) (fun _ ↦ 0)
        let f : X := fun γ m ↦ match γ, m with
          | some δ, 0 => d δ
          | _, _ => 0
        have hfA : f ∈ solidHull A := by
          rw [hAuniv]
          exact Set.mem_univ f
        rcases hfA with ⟨a, haA, hfa⟩
        let aa : A := ⟨a, haA⟩
        have hcoord := hfa (some (e aa)) 0
        change |f (some (e aa)) 0| ≤ |a (some (e aa)) 0| at hcoord
        dsimp [f, d] at hcoord
        rw [Function.Injective.extend_apply e.injective] at hcoord
        rw [abs_of_nonneg (by positivity)] at hcoord
        linarith [abs_nonneg (a (some (e aa)) 0)]

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

private theorem positiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (positiveSubsetSuprema S) := by
  have hnonneg : ∀ {z : X}, z ∈ positiveSubsetSuprema S → 0 ≤ z := by
    intro z hz
    rcases hz with ⟨A, hAS, hAlub⟩
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      exact (hAS ha).2.trans (hAlub.1 ha)
    · have hupper : z ≤ z + z := hAlub.2 fun a ha ↦ (hA ⟨a, ha⟩).elim
      exact nonneg_of_le_add_right hupper
  have hdown : ∀ {y z : X}, 0 ≤ y → y ≤ z →
      z ∈ positiveSubsetSuprema S → y ∈ positiveSubsetSuprema S := by
    intro y z hy0 hyz hz
    rcases hz with ⟨A, hAS, hAlub⟩
    let B : Set X := (fun a ↦ a ⊓ y) '' A
    refine ⟨B, ?_, ?_⟩
    · rintro b ⟨a, ha, rfl⟩
      have ha0 : 0 ≤ a := (hAS ha).2
      have hab0 : 0 ≤ a ⊓ y := le_inf ha0 hy0
      have habs : |a ⊓ y| ≤ |a| := by
        simp [abs_of_nonneg hab0, abs_of_nonneg ha0]
      exact ⟨hS (hAS ha).1 habs, hab0⟩
    · constructor
      · rintro b ⟨a, ha, rfl⟩
        exact inf_le_right
      · intro w hw
        have hupperA : z + w - y ∈ upperBounds A := by
          intro a ha
          have haz : a ≤ z := hAlub.1 ha
          have haw : a ⊓ y ≤ w := hw ⟨a, ha, rfl⟩
          change a ≤ z + w - y
          calc
            a = (a - a ⊓ y) + (a ⊓ y) := by abel
            _ ≤ (z - y) + w := add_le_add (by
              rw [sub_inf_eq_posPart]
              exact (posPart_mono (sub_le_sub_right haz y)).trans_eq
                (posPart_of_nonneg (sub_nonneg.mpr hyz))) haw
            _ = z + w - y := by abel
        have hzw := hAlub.2 hupperA
        change y ≤ w
        apply sub_nonpos.mp
        have hcancel := sub_le_sub_left hzw z
        convert hcancel using 1 <;> abel
  intro x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  letI : Preorder ι := hpre
  letI : IsDirected ι (· ≤ ·) := hdir
  letI : Nonempty ι := hne
  have hf0 : ∀ i, 0 ≤ f i := fun i ↦ hnonneg (hf i)
  have hx0 : 0 ≤ x := hfx.nonneg hf0
  rcases hfx with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκne
  let y : κ → X := fun k ↦ (x - r k)⁺
  have hy_lub : IsLUB (Set.range y) x := by
    constructor
    · rintro _ ⟨k, rfl⟩
      exact show (x - r k) ⊔ 0 ≤ x from
        sup_le (sub_le_self _ (hrnonneg k)) hx0
    · intro c hc
      have hlow : x - c ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        have hraw : x - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
        exact sub_le_iff_le_add.mpr (by
          simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
      exact sub_nonpos.mp (hrglb.2 hlow)
  have hy : ∀ k, y k ∈ positiveSubsetSuprema S := by
    intro k
    obtain ⟨i, hi⟩ := (hbound k).exists
    have hyfi : y k ≤ f i := by
      dsimp [y]
      have hi' : |x - f i| ≤ r k := by simpa [abs_sub_comm] using hi
      have hsub : x - f i ≤ r k := (le_abs_self _).trans hi'
      have hraw : x - r k ≤ f i := sub_le_iff_le_add.mpr (by
        simpa [add_comm] using (sub_le_iff_le_add.mp hsub))
      exact sup_le hraw (hf0 i)
    exact hdown (posPart_nonneg _) hyfi (hf i)
  choose A hAS hAlub using hy
  let B : Set X := {a | ∃ k, a ∈ A k}
  refine ⟨B, ?_, ?_⟩
  · rintro a ⟨k, ha⟩
    exact hAS k ha
  · constructor
    · rintro a ⟨k, ha⟩
      exact (hAlub k).1 ha |>.trans (hy_lub.1 ⟨k, rfl⟩)
    · intro c hc
      apply hy_lub.2
      rintro _ ⟨k, rfl⟩
      exact (hAlub k).2 fun a ha ↦ hc ⟨k, ha⟩

/-- Unnumbered assertion in the proof of `prop:cardinalitybound`. -/
theorem signedPositiveSubsetSuprema_isOrderClosed
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    IsOrderClosed (signedPositiveSubsetSuprema S) := by
  intro x
  rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
  letI : Preorder ι := hpre
  letI : IsDirected ι (· ≤ ·) := hdir
  letI : Nonempty ι := hne
  have hpos : OrderConvergesTo (fun i ↦ (f i)⁺) x⁺ := by
    simpa [posPart] using hfx.sup (orderConvergesTo_const (0 : X))
  have hneg : OrderConvergesTo (fun i ↦ (f i)⁻) x⁻ := by
    simpa [negPart, posPart] using hfx.neg.sup (orderConvergesTo_const (0 : X))
  constructor
  · exact positiveSubsetSuprema_isOrderClosed hS
      ⟨ι, inferInstance, inferInstance, inferInstance, fun i ↦ (f i)⁺,
        fun i ↦ (hf i).1, hpos⟩
  · exact positiveSubsetSuprema_isOrderClosed hS
      ⟨ι, inferInstance, inferInstance, inferInstance, fun i ↦ (f i)⁻,
        fun i ↦ (hf i).2, hneg⟩

/-- Paper Proposition `prop:cardinalitybound`. -/
theorem solid_orderAdherence_cardinality_bound
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {S : Set X} (hS : LatticeOrderedAddCommGroup.IsSolid S) :
    Cardinal.mk (orderAdherence S) ≤ (2 : Cardinal) ^ Cardinal.mk S := by
  let E := signedPositiveSubsetSuprema S
  have hSE : S ⊆ E := by
    intro s hs
    constructor
    · refine ⟨{s⁺}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hspos : |s⁺| ≤ |s| := by
        rw [abs_of_nonneg (posPart_nonneg s)]
        exact posPart_le_abs s
      exact ⟨hS hs hspos, posPart_nonneg s⟩
    · refine ⟨{s⁻}, ?_, isLUB_singleton⟩
      rintro a rfl
      have hsneg : |s⁻| ≤ |s| := by
        rw [abs_of_nonneg (negPart_nonneg s)]
        exact negPart_le_abs s
      exact ⟨hS hs hsneg, negPart_nonneg s⟩
  have hadhE : orderAdherence S ⊆ E := fun _ hx ↦
    signedPositiveSubsetSuprema_isOrderClosed hS (orderAdherence_mono hSE hx)
  let Aplus : E → Set X := fun x ↦ Classical.choose x.2.1
  let Aminus : E → Set X := fun x ↦ Classical.choose x.2.2
  have hAplus : ∀ x : E,
      Aplus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aplus x) x.1⁺ := fun x ↦
    Classical.choose_spec x.2.1
  have hAminus : ∀ x : E,
      Aminus x ⊆ S ∩ Ici 0 ∧ IsLUB (Aminus x) x.1⁻ := fun x ↦
    Classical.choose_spec x.2.2
  let Ψ : E → Set S := fun x ↦
    {s | s.1 ∈ Aplus x ∨ -s.1 ∈ Aminus x}
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have hplus_le : x.1⁺ ≤ y.1⁺ := (hAplus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simpa [ha0] using posPart_nonneg y.1
      · have haS : a ∈ S := ((hAplus x).1 ha).1
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := Or.inl ha
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hay | hnega
        · exact (hAplus y).2.1 hay
        · have hnega0 : 0 ≤ -a := ((hAminus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus x).1 ha).2
          exact (ha0 this).elim
    have hplus_ge : y.1⁺ ≤ x.1⁺ := (hAplus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simpa [ha0] using posPart_nonneg x.1
      · have haS : a ∈ S := ((hAplus y).1 ha).1
        have haΨy : (⟨a, haS⟩ : S) ∈ Ψ y := Or.inl ha
        have haΨx : (⟨a, haS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hax | hnega
        · exact (hAplus x).2.1 hax
        · have hnega0 : 0 ≤ -a := ((hAminus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAplus y).1 ha).2
          exact (ha0 this).elim
    have hminus_le : x.1⁻ ≤ y.1⁻ := (hAminus x).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simpa [ha0] using negPart_nonneg y.1
      · have haS : a ∈ S := ((hAminus x).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          right
          simpa using ha
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          rw [← hxy]
          exact haΨx
        rcases haΨy with hnega | hay
        · have hnega0 : 0 ≤ -a := ((hAplus y).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus x).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus y).2.1 (by simpa using hay)
    have hminus_ge : y.1⁻ ≤ x.1⁻ := (hAminus y).2.2 fun a ha ↦ by
      by_cases ha0 : a = 0
      · simpa [ha0] using negPart_nonneg x.1
      · have haS : a ∈ S := ((hAminus y).1 ha).1
        have hnegS : -a ∈ S := hS haS (by simp)
        have haΨy : (⟨-a, hnegS⟩ : S) ∈ Ψ y := by
          right
          simpa using ha
        have haΨx : (⟨-a, hnegS⟩ : S) ∈ Ψ x := by
          rw [hxy]
          exact haΨy
        rcases haΨx with hnega | hax
        · have hnega0 : 0 ≤ -a := ((hAplus x).1 hnega).2
          have : a = 0 := le_antisymm (by simpa using hnega0) ((hAminus y).1 ha).2
          exact (ha0 this).elim
        · exact (hAminus x).2.1 (by simpa using hax)
    apply Subtype.ext
    calc
      x.1 = x.1⁺ - x.1⁻ := (posPart_sub_negPart x.1).symm
      _ = y.1⁺ - y.1⁻ := by
        rw [le_antisymm hplus_le hplus_ge, le_antisymm hminus_le hminus_ge]
      _ = y.1 := posPart_sub_negPart y.1
  let θ : orderAdherence S → E := fun x ↦ ⟨x.1, hadhE x.2⟩
  have hθ : Function.Injective θ := fun x y hxy ↦ by
    apply Subtype.ext
    dsimp [θ] at hxy
    exact congrArg (fun z : E ↦ z.1) hxy
  calc
    Cardinal.mk (orderAdherence S) ≤ Cardinal.mk E := Cardinal.mk_le_of_injective hθ
    _ ≤ Cardinal.mk (Set S) := Cardinal.mk_le_of_injective hΨ
    _ = (2 : Cardinal) ^ Cardinal.mk S := Cardinal.mk_set

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

private def CNFStep (pre : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}) : Prop :=
  (y.1 = x.1 ∧ x.2 < y.2) ∨
    (x.1 < y.1 ∧
      (pre = [] ∨ ∃ z, pre.getLast? = some z ∧ y.1 < z.1))

private def CNFListLT (l l' : List (Ordinal.{u} × Ordinal.{u})) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}),
    l = pre ++ x :: tail ∧ l' = pre ++ [y] ∧ CNFStep pre x y

private noncomputable def cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u})) : Ordinal.{u} :=
  l.foldr (fun p r ↦ Ordinal.omega0 ^ p.1 * p.2 + r) 0

private theorem cnfValue_append
    (l m : List (Ordinal.{u} × Ordinal.{u})) :
    cnfValue (l ++ m) = cnfValue l + cnfValue m := by
  induction l with
  | nil => simp [cnfValue]
  | cons p l ih =>
      change Ordinal.omega0 ^ p.1 * p.2 + cnfValue (l ++ m) =
        (Ordinal.omega0 ^ p.1 * p.2 + cnfValue l) + cnfValue m
      rw [ih, add_assoc]

private theorem cnfValue_lt_opow
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hcoeff : ∀ p ∈ l, p.2 < Ordinal.omega0)
    {e : Ordinal.{u}} (hexp : ∀ p ∈ l, p.1 < e) :
    cnfValue l < Ordinal.omega0 ^ e := by
  induction l generalizing e with
  | nil =>
      simpa [cnfValue] using Ordinal.opow_pos e Ordinal.omega0_pos
  | cons a l ih =>
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htail : cnfValue l < Ordinal.omega0 ^ a.1 := by
        apply ih hsorted.2
        · intro p hp
          exact hcoeff p (List.mem_cons_of_mem a hp)
        · intro p hp
          exact hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      rw [cnfValue, List.foldr_cons]
      exact Ordinal.opow_mul_add_lt_opow
        (hcoeff a (by simp)) htail (hexp a (by simp))

private theorem CNF_cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0 (cnfValue l) = l := by
  induction l with
  | nil => simp [cnfValue]
  | cons p l ih =>
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailPos : ∀ q ∈ l, 0 < q.2 := fun q hq ↦
        hpos q (List.mem_cons_of_mem p hq)
      have htailLt : ∀ q ∈ l, q.2 < Ordinal.omega0 := fun q hq ↦
        hlt q (List.mem_cons_of_mem p hq)
      have htailExp : ∀ q ∈ l, q.1 < p.1 := fun q hq ↦
        hsorted.1 q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have htailValue : cnfValue l < Ordinal.omega0 ^ p.1 :=
        cnfValue_lt_opow l hsorted.2 htailLt htailExp
      change Ordinal.CNF Ordinal.omega0
        (Ordinal.omega0 ^ p.1 * p.2 + cnfValue l) = p :: l
      rw [Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0
          (hpos p (by simp)).ne' (hlt p (by simp)) htailValue,
        ih hsorted.2 htailPos htailLt]

private noncomputable def cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    List (Ordinal.{u} × Ordinal.{u}) :=
  match l with
  | [] => [(γ, d)]
  | (δ, e) :: tail =>
      if γ < δ then (δ, e) :: cnfAddMonomial tail γ d
      else if γ = δ then [(δ, e + d)] else [(γ, d)]

private theorem cnfValue_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hd : 0 < d) :
    cnfValue (cnfAddMonomial l γ d) =
      cnfValue l + Ordinal.omega0 ^ γ * d := by
  induction l with
  | nil => simp [cnfAddMonomial, cnfValue]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      have htailExp : ∀ p ∈ l, p.1 < δ := fun p hp ↦
        hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have htailValue : cnfValue l < Ordinal.omega0 ^ δ :=
        cnfValue_lt_opow l hsorted.2 htailLt htailExp
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
        change Ordinal.omega0 ^ δ * e + cnfValue (cnfAddMonomial l γ d) =
          (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ γ * d
        rw [ih hsorted.2 htailLt, add_assoc]
      · by_cases hγeqδ : γ = δ
        · subst γ
          simp only [cnfAddMonomial, hγδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          change Ordinal.omega0 ^ δ * (e + d) =
            (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ δ * d
          rw [mul_add, add_assoc,
            Ordinal.add_of_omega0_opow_le htailValue
              (Ordinal.le_mul_left _ hd)]
        · have hδγ : δ < γ :=
            lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
          have hallExp : ∀ p ∈ (δ, e) :: l, p.1 < γ := by
            intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with hp | hp
            · simpa only [hp] using hδγ
            · exact (htailExp p hp).trans hδγ
          have hvalue : cnfValue ((δ, e) :: l) < Ordinal.omega0 ^ γ :=
            cnfValue_lt_opow ((δ, e) :: l)
              (by simpa only [List.map_cons, List.pairwise_cons] using hsorted)
              hlt hallExp
          simp only [cnfAddMonomial, hγδ, hγeqδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          exact (Ordinal.add_of_omega0_opow_le hvalue
            (Ordinal.le_mul_left _ hd)).symm

private theorem cnfAddMonomial_exponents_lt
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d δ : Ordinal.{u})
    (hl : ∀ p ∈ l, p.1 < δ) (hγ : γ < δ) :
    ∀ p ∈ cnfAddMonomial l γ d, p.1 < δ := by
  induction l with
  | nil => simpa [cnfAddMonomial] using hγ
  | cons p l ih =>
      rcases p with ⟨e, c⟩
      have he : e < δ := hl (e, c) (by simp)
      have htail : ∀ p ∈ l, p.1 < δ := fun p hp ↦
        hl p (List.mem_cons_of_mem (e, c) hp)
      by_cases hγe : γ < e
      · simp only [cnfAddMonomial, hγe, ↓reduceIte]
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact he
        · exact ih htail p hp
      · by_cases hγeqe : γ = e
        · subst γ
          simpa [cnfAddMonomial, hγe] using he
        · simpa [cnfAddMonomial, hγe, hγeqe] using hγ

private theorem cnfAddMonomial_lastExponent
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    ((cnfAddMonomial l γ d).getLast?.map Prod.fst).getD 0 = γ := by
  induction l with
  | nil => simp [cnfAddMonomial]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
        cases l with
        | nil => simp [cnfAddMonomial]
        | cons q l =>
            have hout : cnfAddMonomial (q :: l) γ d ≠ [] := by
              rcases q with ⟨qδ, qe⟩
              by_cases hγq : γ < qδ
              · simp [cnfAddMonomial, hγq]
              · by_cases hγeq : γ = qδ
                · simp [cnfAddMonomial, hγeq]
                · simp [cnfAddMonomial, hγq, hγeq]
            rw [show (δ, e) :: cnfAddMonomial (q :: l) γ d =
                [(δ, e)] ++ cnfAddMonomial (q :: l) γ d by rfl,
              List.getLast?_append_of_ne_nil _ hout]
            exact ih
      · by_cases hγeqδ : γ = δ
        · subst γ
          simp [cnfAddMonomial]
        · simp [cnfAddMonomial, hγδ, hγeqδ]

private theorem cnfAddMonomial_eq_append_of_lt_all
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u})
    (hγ : ∀ p ∈ l, γ < p.1) :
    cnfAddMonomial l γ d = l ++ [(γ, d)] := by
  induction l with
  | nil => simp [cnfAddMonomial]
  | cons p l ih =>
      have hγp := hγ p (by simp)
      simp only [cnfAddMonomial, hγp, ↓reduceIte, List.cons_append]
      rw [ih (fun q hq ↦ hγ q (List.mem_cons_of_mem p hq))]

private theorem cnfAddMonomial_valid
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    let out := cnfAddMonomial l γ d
    (out.map Prod.fst).Pairwise (fun a b ↦ b < a) ∧
      (∀ p ∈ out, 0 < p.2) ∧
      (∀ p ∈ out, p.2 < Ordinal.omega0) := by
  induction l with
  | nil => simp [cnfAddMonomial, hdpos, hdlt]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailPos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
        hpos p (List.mem_cons_of_mem (δ, e) hp)
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      obtain ⟨ihsorted, ihpos, ihlt⟩ :=
        ih hsorted.2 htailPos htailLt
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte, List.map_cons,
          List.pairwise_cons]
        refine ⟨⟨?_, ihsorted⟩, ?_, ?_⟩
        · intro e' he'
          rw [List.mem_map] at he'
          obtain ⟨p, hp, rfl⟩ := he'
          exact cnfAddMonomial_exponents_lt l γ d δ
            (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)) hγδ p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hpos (δ, e) (by simp)
          · exact ihpos p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hlt (δ, e) (by simp)
          · exact ihlt p hp
      · by_cases hγeqδ : γ = δ
        · subst γ
          have hepos : 0 < e := hpos (δ, e) (by simp)
          have helt : e < Ordinal.omega0 := hlt (δ, e) (by simp)
          have hsumpos : 0 < e + d := hepos.trans_le (le_self_add)
          have hsumlt : e + d < Ordinal.omega0 := by
            obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp helt
            obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
            rw [← Nat.cast_add]
            exact Ordinal.natCast_lt_omega0 (m + n)
          simp [cnfAddMonomial, hsumpos, hsumlt]
        · simp [cnfAddMonomial, hγδ, hγeqδ, hdpos, hdlt]

private theorem CNF_cnfValue_add_monomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0
      (cnfValue l + Ordinal.omega0 ^ γ * d) = cnfAddMonomial l γ d := by
  rw [← cnfValue_cnfAddMonomial l hsorted hlt γ d hdpos]
  obtain ⟨hsorted', hpos', hlt'⟩ :=
    cnfAddMonomial_valid l hsorted hpos hlt γ d hdpos hdlt
  exact CNF_cnfValue _ hsorted' hpos' hlt'

private theorem CNFStep.cons_prefix
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y : Ordinal.{u} × Ordinal.{u}} {δ e : Ordinal.{u}}
    (h : CNFStep pre x y) (hy : y.1 < δ) :
    CNFStep ((δ, e) :: pre) x y := by
  rcases h with hsame | ⟨hxy, hpre⟩
  · exact Or.inl hsame
  · refine Or.inr ⟨hxy, Or.inr ?_⟩
    cases pre with
    | nil => exact ⟨(δ, e), by simp, hy⟩
    | cons p pre =>
        rcases hpre with hfalse | ⟨z, hz, hyz⟩
        · simp at hfalse
        · exact ⟨z, by simpa using hz, hyz⟩

private theorem CNFListLT_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (hne : l ≠ [])
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (β c : Ordinal.{u}) (hlast : l.getLast? = some (β, c))
    (γ d : Ordinal.{u}) (hdpos : 0 < d)
    (hβγ : β ≤ γ) :
    CNFListLT l (cnfAddMonomial l γ d) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          rcases hlast with ⟨rfl, rfl⟩
          by_cases hγeqβ : γ = β
          · subst γ
            refine ⟨[], [], (β, c), (β, c + d), by simp,
              by simp [cnfAddMonomial], ?_⟩
            exact Or.inl ⟨rfl, lt_add_of_pos_right c hdpos⟩
          · have hβγ' : β < γ := lt_of_le_of_ne hβγ (Ne.symm hγeqβ)
            refine ⟨[], [], (β, c), (γ, d), by simp,
              by simp [cnfAddMonomial, hβγ'.not_gt, hγeqβ], ?_⟩
            exact Or.inr ⟨hβγ', Or.inl rfl⟩
      | cons q l =>
          simp only [List.map_cons, List.pairwise_cons] at hsorted
          have htailPos : ∀ p ∈ q :: l, 0 < p.2 := fun p hp ↦
            hpos p (List.mem_cons_of_mem (δ, e) hp)
          have htailLt : ∀ p ∈ q :: l, p.2 < Ordinal.omega0 := fun p hp ↦
            hlt p (List.mem_cons_of_mem (δ, e) hp)
          have htailSorted : (List.map Prod.fst (q :: l)).Pairwise
              (fun a b ↦ b < a) := by
            simpa only [List.map_cons, List.pairwise_cons] using hsorted.2
          have hlastTail : (q :: l).getLast? = some (β, c) := by
            simpa using hlast
          by_cases hγδ : γ < δ
          · rcases ih (by simp) htailSorted htailPos htailLt hlastTail with
              ⟨pre, tail, x, y, hin, hout, hstep⟩
            have hyMem : y ∈ cnfAddMonomial (q :: l) γ d := by
              rw [hout]
              exact List.mem_append_right _ (by simp)
            have hyδ : y.1 < δ :=
              cnfAddMonomial_exponents_lt (q :: l) γ d δ
                (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
                hγδ y hyMem
            refine ⟨(δ, e) :: pre, tail, x, y, ?_, ?_,
              CNFStep.cons_prefix hstep hyδ⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons (δ, e)) hin
            · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
              simpa only [List.cons_append] using
                congrArg (List.cons (δ, e)) hout
          · by_cases hγeqδ : γ = δ
            · subst γ
              refine ⟨[], q :: l, (δ, e), (δ, e + d), by simp,
                by simp [cnfAddMonomial], ?_⟩
              exact Or.inl ⟨rfl, lt_add_of_pos_right e hdpos⟩
            · have hδγ : δ < γ :=
                lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
              refine ⟨[], q :: l, (δ, e), (γ, d), by simp,
                by simp [cnfAddMonomial, hγδ, hγeqδ], ?_⟩
              exact Or.inr ⟨hδγ, Or.inl rfl⟩

private theorem cnfValue_append_lt_append
    (pre l l' : List (Ordinal.{u} × Ordinal.{u}))
    (h : cnfValue l < cnfValue l') :
    cnfValue (pre ++ l) < cnfValue (pre ++ l') := by
  induction pre with
  | nil => simpa using h
  | cons p pre ih =>
      simp only [List.cons_append, cnfValue, List.foldr_cons]
      exact (add_lt_add_iff_left _).2 ih

private theorem CNFListLT.ordinal_lt {ζ ζ' : Ordinal.{u}}
    (h : CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
      (Ordinal.CNF Ordinal.omega0 ζ')) : ζ < ζ' := by
  rcases h with ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
  have hsorted := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  rw [hζ, List.map_append, List.map_cons, List.pairwise_append] at hsorted
  have hsuffix : ((β, c) :: tail).map Prod.fst |>.Pairwise (fun a b ↦ b < a) :=
    hsorted.2.1
  rw [List.map_cons, List.pairwise_cons] at hsuffix
  have hcoeff : ∀ p ∈ tail, p.2 < Ordinal.omega0 := by
    intro p hp
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have htail : cnfValue tail < Ordinal.omega0 ^ β :=
    cnfValue_lt_opow tail hsuffix.2 hcoeff (fun p hp ↦
      hsuffix.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hc : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (o := ζ) (x := (β, c)) Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ List.mem_cons_self
  have hd : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := ζ') (x := (γ, d))
    rw [hζ']
    exact List.mem_append_right _ (by simp)
  have hdiv : cnfValue ((β, c) :: tail) < cnfValue [(γ, d)] := by
    rcases hstep with ⟨rfl, hcd⟩ | ⟨hβγ, _⟩
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact Ordinal.opow_mul_add_lt_opow_mul htail hcd
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact (Ordinal.opow_mul_add_lt_opow hc htail hβγ).trans_le
        (Ordinal.le_mul_left _ hd)
  rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ,
    ← Ordinal.CNF.foldr Ordinal.omega0 ζ']
  change cnfValue (Ordinal.CNF Ordinal.omega0 ζ) <
    cnfValue (Ordinal.CNF Ordinal.omega0 ζ')
  rw [hζ, hζ']
  exact cnfValue_append_lt_append pre _ _ hdiv

private theorem cnfExtensionLT_iff_CNFListLT {ζ ζ' : Ordinal.{u}} :
    cnfExtensionLT ζ ζ' ↔
      CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
        (Ordinal.CNF Ordinal.omega0 ζ') := by
  constructor
  · rintro ⟨pre, tail, β, c, γ, d, hζ, hζ', hstep⟩
    refine ⟨pre, tail, (β, c), (γ, d), hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨δ, e, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨(δ, e), hlast, hγδ⟩
  · rintro ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
    refine ⟨pre, tail, β, c, γ, d, hζ, hζ', ?_⟩
    rcases hstep with hstep | ⟨hβγ, hpre⟩
    · exact Or.inl hstep
    · refine Or.inr ⟨hβγ, ?_⟩
      rcases hpre with rfl | ⟨⟨δ, e⟩, hlast, hγδ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨δ, e, hlast, hγδ⟩

private theorem cnfExtensionLT_add_singleton_of_last
    {ζ q γ d β c : Ordinal.{u}}
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    (hζ : Ordinal.CNF Ordinal.omega0 ζ = pre ++ [(β, c)])
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hβγ : β ≤ γ) : cnfExtensionLT ζ (ζ + q) := by
  let l := Ordinal.CNF Ordinal.omega0 ζ
  have hl : l = pre ++ [(β, c)] := hζ
  have hlne : l ≠ [] := by rw [hl]; simp
  have hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a) :=
    (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  have hpos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
    Ordinal.CNF.snd_pos hp
  have hlt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
    Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hp
  have hlast : l.getLast? = some (β, c) := by rw [hl]; simp
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hζvalue : cnfValue l = ζ := Ordinal.CNF.foldr Ordinal.omega0 ζ
  have hqvalue : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  apply cnfExtensionLT_iff_CNFListLT.mpr
  rw [← hζvalue, hqvalue,
    CNF_cnfValue_add_monomial l hsorted hpos hlt γ d hdpos hdlt,
    CNF_cnfValue l hsorted hpos hlt]
  exact CNFListLT_cnfAddMonomial l hlne hsorted hpos hlt β c hlast
    γ d hdpos hβγ

private theorem CNFStep.trans {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hyz : CNFStep pre y z) : CNFStep pre x z := by
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact Or.inl ⟨hyz.1.trans hxy.1, hxy.2.trans hyz.2⟩
  · exact Or.inr ⟨hxy.1 ▸ hyz.1, hyz.2⟩
  · refine Or.inr ⟨hxy.1.trans_eq hyz.1.symm, ?_⟩
    rcases hxy.2 with hp | ⟨w, hw, hb⟩
    · exact Or.inl hp
    · exact Or.inr ⟨w, hw, by simpa only [hyz.1] using hb⟩
  · exact Or.inr ⟨hxy.1.trans hyz.1, hyz.2⟩

private theorem CNFStep.trichotomy {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hxz : CNFStep pre x z) :
    y = z ∨ CNFStep pre y z ∨ CNFStep pre z y := by
  rcases x with ⟨β, c⟩
  rcases y with ⟨γ, d⟩
  rcases z with ⟨δ, e⟩
  simp only [CNFStep] at hxy hxz ⊢
  rcases hxy with ⟨rfl, hcd⟩ | ⟨hβγ, hγ⟩ <;>
    rcases hxz with ⟨rfl, hce⟩ | ⟨hβδ, hδ⟩
  · rcases lt_trichotomy d e with hde | rfl | hed
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hβδ, hδ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hβγ, hγ⟩))
  · rcases lt_trichotomy γ δ with hγδ | hγδ | hδγ
    · exact Or.inr (Or.inl (Or.inr ⟨hγδ, hδ⟩))
    · subst δ
      rcases lt_trichotomy d e with hde | rfl | hed
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hδγ, hγ⟩))

private theorem CNFListLT.trans {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hmn : CNFListLT m n) : CNFListLT l n := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hmn with ⟨q, s, y', z, hm', hn, hyz⟩
  have heq : p ++ [y] = q ++ y' :: s := hm.symm.trans hm'
  have hlen : q.length ≤ p.length := by
    have h : p.length + 1 = q.length + s.length + 1 := by
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        using congrArg List.length heq
    omega
  have hqp : q <+: p := by
    apply (List.isPrefix_append_of_length hlen).mp
    exact ⟨y' :: s, heq.symm⟩
  rcases hqp with ⟨r, hpr⟩
  rw [← hpr] at hl hm hxy heq
  have hr : r ++ [y] = y' :: s :=
    List.append_cancel_left (by simpa only [List.append_assoc] using heq)
  cases r with
  | nil =>
      simp only [List.append_nil] at hl hm hxy
      simp only [List.nil_append] at hr
      simp only [List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨q, t, x, z, by simpa only [List.nil_append] using hl,
        hn, CNFStep.trans hxy hyz⟩
  | cons w r =>
      simp only [List.cons_append, List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      refine ⟨q, r ++ x :: t, w, z, ?_, hn, hyz⟩
      simpa only [List.cons_append, List.append_assoc] using hl

private theorem CNFListLT.upper_trichotomy
    {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hln : CNFListLT l n) :
    m = n ∨ CNFListLT m n ∨ CNFListLT n m := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hln with ⟨q, s, x', z, hl', hn, hxz⟩
  have hpref : p <+: l := ⟨x :: t, hl.symm⟩
  have qpref : q <+: l := ⟨x' :: s, hl'.symm⟩
  rcases lt_trichotomy p.length q.length with hpq | hpq | hqp
  · have hprefq : p <+: q := by
      apply (List.isPrefix_append_of_length hpq.le).mp
      rw [hl'] at hpref
      exact hpref
    rcases hprefq with ⟨r, hqr⟩
    rw [← hqr] at hl' hn hxz
    cases r with
    | nil =>
        simp only [List.append_nil] at hqr
        exact (hpq.ne (congrArg List.length hqr)).elim
    | cons w r =>
        have heq : w :: r ++ x' :: s = x :: t :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl'.symm.trans hl)
        have hw : w = x := (List.cons.inj heq).1
        have hr : r ++ x' :: s = t := (List.cons.inj heq).2
        subst w
        subst t
        refine Or.inr (Or.inr ⟨p, r ++ [z], x, y, ?_, hm, hxy⟩)
        simpa only [List.cons_append, List.append_assoc] using hn
  · have hpqeq : p = q := by
      rw [List.prefix_iff_eq_take] at hpref qpref
      rw [hpref, qpref, hpq]
    subst q
    have heq : x :: t = x' :: s :=
      List.append_cancel_left (hl.symm.trans hl')
    have hxx' : x = x' := (List.cons.inj heq).1
    have hts : t = s := (List.cons.inj heq).2
    subst x'
    subst s
    rcases CNFStep.trichotomy hxy hxz with rfl | hyz | hzy
    · exact Or.inl (hm.trans hn.symm)
    · exact Or.inr (Or.inl ⟨p, [], y, z, hm, hn, hyz⟩)
    · exact Or.inr (Or.inr ⟨p, [], z, y, hn, hm, hzy⟩)
  · have qprefp : q <+: p := by
      apply (List.isPrefix_append_of_length hqp.le).mp
      rw [hl] at qpref
      exact qpref
    rcases qprefp with ⟨r, hpr⟩
    rw [← hpr] at hl hm hxy
    cases r with
    | nil =>
        simp only [List.append_nil] at hpr
        exact (hqp.ne (congrArg List.length hpr)).elim
    | cons w r =>
        have heq : w :: r ++ x :: t = x' :: s :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl.symm.trans hl')
        have hw : w = x' := (List.cons.inj heq).1
        have hr : r ++ x :: t = s := (List.cons.inj heq).2
        subst w
        subst s
        refine Or.inr (Or.inl ⟨q, r ++ [y], x', z, ?_, hn, hxz⟩)
        simpa only [List.cons_append, List.append_assoc] using hm

/-- Property P1 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLE_partialOrder_and_subrelation :
    IsPartialOrder (Ordinal.{u}) cnfExtensionLE ∧
      ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLE ζ ζ' → ζ ≤ ζ' := by
  have hlt : ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLT ζ ζ' → ζ < ζ' := by
    intro ζ ζ' h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  have htrans : ∀ a b c : Ordinal.{u}, cnfExtensionLT a b →
      cnfExtensionLT b c → cnfExtensionLT a c := by
    intro a b c hab hbc
    apply cnfExtensionLT_iff_CNFListLT.mpr
    exact CNFListLT.trans (cnfExtensionLT_iff_CNFListLT.mp hab)
      (cnfExtensionLT_iff_CNFListLT.mp hbc)
  letI : IsPreorder (Ordinal.{u}) cnfExtensionLE := {
    refl := fun _ ↦ Or.inl rfl
    trans := fun a b c hab hbc ↦ by
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (htrans a b c hab hbc)
    }
  letI : Std.Antisymm
      (cnfExtensionLE : Ordinal.{u} → Ordinal.{u} → Prop) := ⟨by
    intro a b hab hba
    rcases hab with rfl | hab
    · rfl
    rcases hba with rfl | hba
    · rfl
    · exact ((hlt hab).asymm (hlt hba)).elim
    ⟩
  constructor
  · exact IsPartialOrder.mk
  · intro ζ ζ' h
    rcases h with rfl | h
    · exact le_rfl
    · exact (hlt h).le

/-- Property P2 of the ordinal relation in the proof of `thm:solid-iterations`. -/
theorem cnfExtensionLT_linear_above (ζ : Ordinal.{u}) :
    ∀ {η η' : Ordinal.{u}}, cnfExtensionLT ζ η → cnfExtensionLT ζ η' →
      (cnfExtensionLT η η' ↔ η < η') := by
  intro η η' hη hη'
  constructor
  · intro h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  · intro hlt
    rcases CNFListLT.upper_trichotomy
      (cnfExtensionLT_iff_CNFListLT.mp hη)
      (cnfExtensionLT_iff_CNFListLT.mp hη') with heq | h | h
    · have hηeq : η = η' := by
        rw [← Ordinal.CNF.foldr Ordinal.omega0 η,
          ← Ordinal.CNF.foldr Ordinal.omega0 η', heq]
      exact (hlt.ne hηeq).elim
    · exact cnfExtensionLT_iff_CNFListLT.mpr h
    · exact ((CNFListLT.ordinal_lt h).asymm hlt).elim

private theorem cnfExtensionLE_linear_above (ζ : Ordinal.{u})
    {η η' : Ordinal.{u}} (hη : cnfExtensionLE ζ η)
    (hη' : cnfExtensionLE ζ η') :
    cnfExtensionLE η η' ∨ cnfExtensionLE η' η := by
  rcases hη with rfl | hη
  · exact Or.inl hη'
  rcases hη' with rfl | hη'
  · exact Or.inr (Or.inr hη)
  rcases lt_trichotomy η η' with hlt | heq | hgt
  · exact Or.inl (Or.inr ((cnfExtensionLT_linear_above ζ hη hη').mpr hlt))
  · exact Or.inl (Or.inl heq)
  · exact Or.inr (Or.inr ((cnfExtensionLT_linear_above ζ hη' hη).mpr hgt))

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
    exact (continuous_of_discreteTopology :
      Continuous (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
        ((continuous_apply ζ).comp continuous_subtype_val)

private theorem continuousMap_exists_finite_coordinates
    {I : Type u} {K : Set (I → Bool)} (f : C(K, ℝ)) (x : K)
    {V : Set ℝ} (hV : IsOpen V) (hxV : f x ∈ V) :
    ∃ F : Finset I, ∀ y : K, (∀ i ∈ F, y.1 i = x.1 i) → f y ∈ V := by
  have hopen : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  rcases isOpen_induced_iff.mp hopen with ⟨W, hW, hWeq⟩
  have hxW : x.1 ∈ W := by
    have : x ∈ f ⁻¹' V := hxV
    rw [← hWeq] at this
    exact this
  rcases isOpen_pi_iff.mp hW x.1 hxW with ⟨F, v, hv, hvW⟩
  refine ⟨F, fun y hy ↦ ?_⟩
  have hyv : y.1 ∈ (F : Set I).pi v := by
    intro i hi
    rw [hy i (Finset.mem_coe.mp hi)]
    exact (hv i (Finset.mem_coe.mp hi)).2
  have hyW := hvW hyv
  have : y ∈ Subtype.val ⁻¹' W := hyW
  rw [hWeq] at this
  exact this

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

private theorem isSolid_gaoStageSet (ξ β : Ordinal.{u}) :
    LatticeOrderedAddCommGroup.IsSolid (GaoStageSet ξ β) := by
  intro f hf g hgf
  obtain ⟨ζ, hζ, hfζ⟩ := hf
  exact ⟨ζ, hζ, hgf.trans hfζ⟩

/-- Claim 1 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_incomparable_iInf
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (hZ : Z.Infinite)
    (hinc : Z.Pairwise fun ζ ζ' ↦ ¬ cnfExtensionLE ζ.1 ζ'.1) :
    IsGLB (ordinalProjection ξ '' Z) 0 := by
  classical
  constructor
  · rintro p ⟨ζ, _, rfl⟩ x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  · intro f hf x
    by_contra hfx
    have hfxpos : 0 < f x := lt_of_not_ge hfx
    obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
      isOpen_Ioi hfxpos
    let bad : Set (GaoIndex ξ) := ⋃ i ∈ (F : Set (GaoIndex ξ)),
      {ζ | ζ ∈ Z ∧ x.1 i = true ∧ cnfExtensionLE i.1 ζ.1}
    have hbad : bad.Finite := by
      apply F.finite_toSet.biUnion
      intro i _
      apply Set.Subsingleton.finite
      intro ζ hζ ζ' hζ'
      rcases hζ with ⟨hζZ, _, hiζ⟩
      rcases hζ' with ⟨hζ'Z, _, hiζ'⟩
      by_contra hne
      have hnot := hinc hζZ hζ'Z hne
      rcases hiζ with hiζ | hiζ
      · have : i = ζ := Subtype.ext hiζ
        subst i
        exact hnot hiζ'
      rcases hiζ' with hiζ' | hiζ'
      · have : i = ζ' := Subtype.ext hiζ'
        subst i
        exact (hinc hζ'Z hζZ (Ne.symm hne)) (Or.inr hiζ)
      · rcases lt_trichotomy ζ.1 ζ'.1 with hlt | heq | hgt
        · exact hnot (Or.inr
            ((cnfExtensionLT_linear_above i.1 hiζ hiζ').mpr hlt))
        · exact hne (Subtype.ext heq)
        · exact (hinc hζ'Z hζZ (Ne.symm hne))
            (Or.inr ((cnfExtensionLT_linear_above i.1 hiζ' hiζ).mpr hgt))
    obtain ⟨ζ, hζZ, hζbad⟩ := hZ.exists_notMem_finite hbad
    let y : GaoIndex ξ → Bool := fun a ↦
      if cnfExtensionLE a.1 ζ.1 then false else x.1 a
    have hy_mono : ∀ a b : GaoIndex ξ,
        cnfExtensionLT a.1 b.1 → y a ≤ y b := by
      intro a b hab
      dsimp [y]
      by_cases ha : cnfExtensionLE a.1 ζ.1
      · rw [if_pos ha]
        exact Bool.false_le _
      · rw [if_neg ha]
        by_cases hb : cnfExtensionLE b.1 ζ.1
        · exact (ha (cnfExtensionLE_partialOrder_and_subrelation.1.trans
            a.1 b.1 ζ.1 (Or.inr hab) hb)).elim
        · rw [if_neg hb]
          exact x.2 a b hab
    let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
    have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
      intro i hi
      dsimp [yK, y]
      by_cases hxi : x.1 i = true
      · rw [if_neg]
        intro hiζ
        apply hζbad
        simp only [bad, Set.mem_iUnion]
        exact ⟨i, Finset.mem_coe.mpr hi, hζZ, hxi, hiζ⟩
      · have hxi' : x.1 i = false := Bool.eq_false_of_not_eq_true hxi
        by_cases hiζ : cnfExtensionLE i.1 ζ.1
        · rw [if_pos hiζ, hxi']
        · rw [if_neg hiζ, hxi']
    have hfy : 0 < f yK := hF yK hyF
    have hfζ := hf ⟨ζ, hζZ, rfl⟩ yK
    have hyζ : yK.1 ζ = false := by
      dsimp [yK, y]
      rw [if_pos (show cnfExtensionLE ζ.1 ζ.1 from Or.inl rfl)]
    simp only [ordinalProjection, hyζ, Bool.false_eq_true, ↓reduceIte] at hfζ
    exact not_lt_of_ge hfζ hfy

private theorem ordinalProjection_le_iff
    (ξ : Ordinal.{u}) (a b : GaoIndex ξ) :
    ordinalProjection ξ a ≤ ordinalProjection ξ b ↔ cnfExtensionLE a.1 b.1 := by
  classical
  constructor
  · intro hab
    by_contra hrel
    let x : GaoIndex ξ → Bool := fun c ↦
      if cnfExtensionLE a.1 c.1 then true else false
    have hxmono : ∀ c d : GaoIndex ξ,
        cnfExtensionLT c.1 d.1 → x c ≤ x d := by
      intro c d hcd
      dsimp [x]
      by_cases hac : cnfExtensionLE a.1 c.1
      · rw [if_pos hac, if_pos]
        exact cnfExtensionLE_partialOrder_and_subrelation.1.trans
          a.1 c.1 d.1 hac (Or.inr hcd)
      · rw [if_neg hac]
        exact Bool.false_le _
    let xK : GaoCompactSpace ξ := ⟨x, hxmono⟩
    have habx := hab xK
    have hxa : xK.1 a = true := by
      simp [xK, x, cnfExtensionLE]
    have hxb : xK.1 b = false := by
      simp [xK, x, hrel]
    simp only [ordinalProjection, hxa, hxb, Bool.false_eq_true, ↓reduceIte] at habx
    norm_num at habx
  · intro hab x
    rcases hab with hab | hab
    · have : a = b := Subtype.ext hab
      subst b
      exact le_rfl
    · dsimp [ordinalProjection]
      by_cases hxa : x.1 a = true
      · have hxb : x.1 b = true := by
          have hx := Bool.le_iff_imp.mp (x.2 a b hab)
          have hx' : True → x.1 b = true := by
            simpa only [hxa, Bool.true_eq] using hx
          exact hx' trivial
        simp only [hxa, hxb, if_true]
        norm_num
      · simp only [hxa]
        positivity

private noncomputable def leadingCNFTerm (a : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a *
    (a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)

private theorem cnf_singleton_le_leadingCNFTerm
    {q a γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) (hqa : q ≤ a) :
    q ≤ leadingCNFTerm a := by
  have hqeq : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hlogq : Ordinal.log Ordinal.omega0 q = γ := by
    rw [hqeq, Ordinal.log_opow_mul Ordinal.one_lt_omega0 γ hdpos.ne',
      Ordinal.log_eq_zero hdlt, add_zero]
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hlogle := Ordinal.log_mono_right Ordinal.omega0 hqa
  rw [hlogq] at hlogle
  rcases hlogle.eq_or_lt with hloge | hloglt
  · rw [leadingCNFTerm, ← hloge, hqeq]
    apply mul_le_mul_right
    exact (Ordinal.mul_le_iff_le_div
      (Ordinal.opow_ne_zero γ Ordinal.omega0_ne_zero)).mp (hqeq ▸ hqa)
  · have hqpow : q < Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hq0).2 (by
        simpa only [hlogq] using hloglt)
    exact hqpow.le.trans (by
      rw [leadingCNFTerm]
      exact Ordinal.le_mul_left _
        (Ordinal.div_opow_log_pos Ordinal.omega0 ha0))

private theorem cnf_singleton_spec
    {q γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) :
    q = Ordinal.omega0 ^ γ * d ∧ 0 < d ∧ d < Ordinal.omega0 ∧
      Ordinal.log Ordinal.omega0 q = γ := by
  have hqeq : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  refine ⟨hqeq, hdpos, hdlt, ?_⟩
  rw [hqeq, Ordinal.log_opow_mul Ordinal.one_lt_omega0 γ hdpos.ne',
    Ordinal.log_eq_zero hdlt, add_zero]

private theorem cnf_eq_singleton_of_isLUB
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u}) (hQ : Q.Nonempty)
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) :
    ∃ γ d, Ordinal.CNF Ordinal.omega0 a = [(γ, d)] := by
  obtain ⟨q, hqQ⟩ := hQ
  obtain ⟨γ, d, hq⟩ := hsingle q hqQ
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hqa : q ≤ a := hlub.1 hqQ
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hleadUpper : leadingCNFTerm a ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨e, c, hr⟩ := hsingle r hrQ
    exact cnf_singleton_le_leadingCNFTerm hr (hlub.1 hrQ)
  have halead : a ≤ leadingCNFTerm a := hlub.2 hleadUpper
  have hleada : leadingCNFTerm a ≤ a := by
    exact Ordinal.mul_div_le a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
  have hleadeq : leadingCNFTerm a = a := le_antisymm hleada halead
  have hmod : a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = 0 := by
    have hdiv := Ordinal.div_add_mod a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
    change leadingCNFTerm a +
      a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = a at hdiv
    apply add_left_cancel (a := leadingCNFTerm a)
    calc
      leadingCNFTerm a + a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) =
          a := hdiv
      _ = leadingCNFTerm a + 0 := by rw [add_zero, hleadeq]
  refine ⟨Ordinal.log Ordinal.omega0 a,
    a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a, ?_⟩
  rw [Ordinal.CNF.ne_zero ha0, hmod, Ordinal.CNF.zero_right]

private theorem cnf_singleton_exponent_lt_of_isLUB_not_mem
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u})
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) (haQ : a ∉ Q)
    {q β c γ d : Ordinal.{u}} (hqQ : q ∈ Q)
    (hq : Ordinal.CNF Ordinal.omega0 q = [(β, c)])
    (ha : Ordinal.CNF Ordinal.omega0 a = [(γ, d)]) : β < γ := by
  obtain ⟨hqeq, hcpos, hclt, hlogq⟩ := cnf_singleton_spec hq
  obtain ⟨haeq, hdpos, hdlt, hloga⟩ := cnf_singleton_spec ha
  have hqa : q ≤ a := hlub.1 hqQ
  have hqne : q ≠ a := fun h ↦ haQ (h ▸ hqQ)
  have hqalt : q < a := lt_of_le_of_ne hqa hqne
  have hβγ : β ≤ γ := by
    have := Ordinal.log_mono_right Ordinal.omega0 hqa
    simpa only [hlogq, hloga] using this
  apply hβγ.lt_of_ne
  intro hβγeq
  subst β
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hclt
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
  have hmpos : 0 < m := by exact_mod_cast hcpos
  have hnpos : 0 < n := by exact_mod_cast hdpos
  have hmn : m < n := by
    by_contra h
    have hnm : n ≤ m := le_of_not_gt h
    have hmul : Ordinal.omega0 ^ γ * (n : Ordinal) ≤
        Ordinal.omega0 ^ γ * (m : Ordinal) :=
      mul_le_mul_right (by exact_mod_cast hnm) _
    have hmulLt : Ordinal.omega0 ^ γ * (m : Ordinal) <
        Ordinal.omega0 ^ γ * (n : Ordinal) := by
      rw [← hβγeq, ← hqeq, hβγeq, ← haeq]
      exact hqalt
    exact (not_le_of_gt hmulLt) hmul
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hkpos : 0 < k := lt_of_lt_of_le hmpos (Nat.le_of_lt_succ hmn)
  let b : Ordinal.{u} := Ordinal.omega0 ^ γ * (k : Ordinal)
  have hbUpper : b ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨ε, e, hr⟩ := hsingle r hrQ
    obtain ⟨hreq, hepos, helt, hlogr⟩ := cnf_singleton_spec hr
    have hra : r ≤ a := hlub.1 hrQ
    have hrne : r ≠ a := fun h ↦ haQ (h ▸ hrQ)
    have hralt : r < a := lt_of_le_of_ne hra hrne
    have hεγ : ε ≤ γ := by
      have := Ordinal.log_mono_right Ordinal.omega0 hra
      simpa only [hlogr, hloga] using this
    rcases hεγ.eq_or_lt with rfl | hεγlt
    · obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.mp helt
      have hjlt : j < k + 1 := by
        by_contra h
        have hle : k + 1 ≤ j := le_of_not_gt h
        have hmul : Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) ≤
            Ordinal.omega0 ^ ε * (j : Ordinal) :=
          mul_le_mul_right (by exact_mod_cast hle) _
        have hmulLt : Ordinal.omega0 ^ ε * (j : Ordinal) <
            Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) := by
          rw [← hreq, ← haeq]
          exact hralt
        exact (not_le_of_gt hmulLt) hmul
      dsimp [b]
      rw [hreq]
      exact mul_le_mul_right (by exact_mod_cast (Nat.le_of_lt_succ hjlt)) _
    · have hr0 : r ≠ 0 := by
        intro hzero
        rw [hzero, Ordinal.CNF.zero_right] at hr
        simp at hr
      have hrpow : r < Ordinal.omega0 ^ γ :=
        (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).2 (by
          simpa only [hlogr] using hεγlt)
      exact hrpow.le.trans (by
        dsimp [b]
        exact Ordinal.le_mul_left _ (by exact_mod_cast hkpos))
  have hab : a ≤ b := hlub.2 hbUpper
  have hba : b < a := by
    dsimp [b]
    rw [haeq]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (Nat.lt_succ_self k))
      (Ordinal.opow_pos γ Ordinal.omega0_pos)
  exact (not_le_of_gt hba) hab

private theorem CNFListLT.eq_dropLast_of_length_eq
    {l m : List (Ordinal.{u} × Ordinal.{u})}
    (h : CNFListLT l m) (hlen : m.length = l.length) :
    ∃ x y, l = l.dropLast ++ [x] ∧ m = l.dropLast ++ [y] ∧
      CNFStep l.dropLast x y := by
  rcases h with ⟨pre, tail, x, y, hl, hm, hstep⟩
  have htail : tail = [] := by
    have hlength := congrArg List.length hl
    rw [hm] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength hlen
    have : tail.length = 0 := by omega
    simpa using this
  subst tail
  have hdrop : l.dropLast = pre := by simp [hl]
  exact ⟨x, y, by simp [hl], by simpa [hdrop] using hm,
    by simpa [hdrop] using hstep⟩

private theorem cnfExtensionLE_chain_lub
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    ∀ ζ ∈ Z, cnfExtensionLE ζ.1 α.1 := by
  classical
  intro ζ hζZ
  by_cases hαZ : α ∈ Z
  · rcases hchain hζZ hαZ with hζα | hαζ
    · exact hζα
    · exact Or.inl (le_antisymm
        (hsup.1 ⟨ζ, hζZ, rfl⟩)
        (cnfExtensionLE_partialOrder_and_subrelation.2 hαζ))
  have hζαle : ζ.1 ≤ α.1 := hsup.1 ⟨ζ, hζZ, rfl⟩
  have hζα : ζ.1 < α.1 := hζαle.lt_of_ne fun h ↦ by
    have hsub : ζ = α := Subtype.ext h
    exact hαZ (hsub ▸ hζZ)
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := by
    by_contra h
    have hαζle : α.1 ≤ ζ.1 := hsup.2 (by
      rintro _ ⟨η, hηZ, rfl⟩
      exact le_of_not_gt fun hζη ↦ h ⟨η, hηZ, hζη⟩)
    exact (not_le_of_gt hζα) hαζle
  obtain ⟨η₀, hη₀U, hη₀min⟩ :=
    exists_minimalFor_of_wellFoundedLT U
      (fun η : GaoIndex ξ ↦ (Ordinal.CNF Ordinal.omega0 η.1).length) hU
  have hζη₀ : cnfExtensionLT ζ.1 η₀.1 := by
    rcases hchain hζZ hη₀U.1 with h | h
    · rcases h with heq | hlt
      · exact (hη₀U.2.ne' heq.symm).elim
      · exact hlt
    · exact (not_le_of_gt hη₀U.2
        (cnfExtensionLE_partialOrder_and_subrelation.2 h)).elim
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀U.1, le_rfl⟩
  have hrelV : ∀ η ∈ V, cnfExtensionLE η₀.1 η.1 := by
    intro η hηV
    rcases hchain hη₀U.1 hηV.1 with h | h
    · exact h
    · have hOrd := cnfExtensionLE_partialOrder_and_subrelation.2 h
      have heq : η₀.1 = η.1 := le_antisymm hηV.2 hOrd
      exact Or.inl heq
  have hlenV : ∀ η ∈ V,
      (Ordinal.CNF Ordinal.omega0 η.1).length =
        (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · rw [heq]
    · have hle : (Ordinal.CNF Ordinal.omega0 η.1).length ≤
          (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
        rcases cnfExtensionLT_iff_CNFListLT.mp hlt with
          ⟨pre, tail, x, y, hη₀cnf, hηcnf, _⟩
        rw [hη₀cnf, hηcnf]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hηU : U η := ⟨hηV.1, hη₀U.2.trans_le hηV.2⟩
      exact le_antisymm hle (hη₀min hηU hle)
  let pre := (Ordinal.CNF Ordinal.omega0 η₀.1).dropLast
  have hη₀ne : Ordinal.CNF Ordinal.omega0 η₀.1 ≠ [] := by
    have hη₀pos : 0 < η₀.1 := (zero_le : (0 : Ordinal) ≤ ζ.1).trans_lt hη₀U.2
    intro h
    have := Ordinal.CNF.foldr Ordinal.omega0 η₀.1
    rw [h] at this
    exact hη₀pos.ne' this.symm
  have hcnfV : ∀ η ∈ V, ∃ γ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(γ, d)] := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · have hsub : η₀ = η := Subtype.ext heq
      subst η
      let p := (Ordinal.CNF Ordinal.omega0 η₀.1).getLast hη₀ne
      refine ⟨p.1, p.2, ?_⟩
      simpa only [pre, p] using (List.dropLast_append_getLast hη₀ne).symm
    · obtain ⟨x, y, _, hηcnf, _⟩ :=
        CNFListLT.eq_dropLast_of_length_eq
          (cnfExtensionLT_iff_CNFListLT.mp hlt) (hlenV η hηV)
      obtain ⟨γ, d⟩ := y
      exact ⟨γ, d, hηcnf⟩
  let ρ : Ordinal.{u} := cnfValue pre
  have residual_of_common : ∀ (η : GaoIndex ξ) (γ d : Ordinal.{u}),
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(γ, d)] →
      Ordinal.CNF Ordinal.omega0 (η.1 - ρ) = [(γ, d)] ∧
        ρ + (η.1 - ρ) = η.1 := by
    intro η γ d hηcnf
    have hηeq : ρ + cnfValue [(γ, d)] = η.1 := by
      rw [← Ordinal.CNF.foldr Ordinal.omega0 η.1]
      change ρ + cnfValue [(γ, d)] = cnfValue (Ordinal.CNF Ordinal.omega0 η.1)
      rw [hηcnf, cnfValue_append]
    have hρle : ρ ≤ η.1 := hηeq ▸ le_self_add
    have hsub : η.1 - ρ = cnfValue [(γ, d)] :=
      Ordinal.sub_eq_of_add_eq hηeq
    constructor
    · rw [hsub]
      apply CNF_cnfValue
      · simp
      · intro p hp
        have hpη : p ∈ Ordinal.CNF Ordinal.omega0 η.1 := by
          rw [hηcnf]
          exact List.mem_append_right _ hp
        exact Ordinal.CNF.snd_pos hpη
      · intro p hp
        have hpη : p ∈ Ordinal.CNF Ordinal.omega0 η.1 := by
          rw [hηcnf]
          exact List.mem_append_right _ hp
        exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hpη
    · exact Ordinal.add_sub_cancel_of_le hρle
  let Q : Set (Ordinal.{u}) :=
    (fun η : GaoIndex ξ ↦ η.1 - ρ) '' V
  have hQne : Q.Nonempty := ⟨η₀.1 - ρ, ⟨η₀, hη₀V, rfl⟩⟩
  have hsingleQ : ∀ q ∈ Q, ∃ γ d,
      Ordinal.CNF Ordinal.omega0 q = [(γ, d)] := by
    rintro q ⟨η, hηV, rfl⟩
    obtain ⟨γ, d, hηcnf⟩ := hcnfV η hηV
    exact ⟨γ, d, (residual_of_common η γ d hηcnf).1⟩
  obtain ⟨β, c, hη₀cnf⟩ := hcnfV η₀ hη₀V
  have hq₀cnf : Ordinal.CNF Ordinal.omega0 (η₀.1 - ρ) = [(β, c)] :=
    (residual_of_common η₀ β c hη₀cnf).1
  have hρaddη₀ : ρ + (η₀.1 - ρ) = η₀.1 :=
    (residual_of_common η₀ β c hη₀cnf).2
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hη₀αle : η₀.1 ≤ α.1 := hsup.1 ⟨η₀, hη₀U.1, rfl⟩
  have hρleα : ρ ≤ α.1 := hρleη₀.trans hη₀αle
  let a : Ordinal.{u} := α.1 - ρ
  have hρadda : ρ + a = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  have hlubQ : IsLUB Q a := by
    constructor
    · rintro q ⟨η, hηV, rfl⟩
      rw [Ordinal.sub_le]
      rw [hρadda]
      exact hsup.1 ⟨η, hηV.1, rfl⟩
    · intro b hb
      rw [Ordinal.sub_le]
      apply hsup.2
      rintro _ ⟨η, hηZ, rfl⟩
      rcases hchain hηZ hη₀U.1 with hηη₀ | hη₀η
      · have hηleη₀ := cnfExtensionLE_partialOrder_and_subrelation.2 hηη₀
        calc
          η.1 ≤ η₀.1 := hηleη₀
          _ = ρ + (η₀.1 - ρ) := hρaddη₀.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η₀, hη₀V, rfl⟩) ρ
      · have hη₀leη := cnfExtensionLE_partialOrder_and_subrelation.2 hη₀η
        have hηV : η ∈ V := ⟨hηZ, hη₀leη⟩
        obtain ⟨γ', d', hηcnf⟩ := hcnfV η hηV
        have hρaddη := (residual_of_common η γ' d' hηcnf).2
        calc
          η.1 = ρ + (η.1 - ρ) := hρaddη.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η, hηV, rfl⟩) ρ
  have haQ : a ∉ Q := by
    rintro ⟨η, hηV, hηsub⟩
    obtain ⟨γ', d', hηcnf⟩ := hcnfV η hηV
    have hρaddη := (residual_of_common η γ' d' hηcnf).2
    change η.1 - ρ = a at hηsub
    have hηα : η.1 = α.1 := by
      calc
        η.1 = ρ + (η.1 - ρ) := hρaddη.symm
        _ = ρ + a := by rw [hηsub]
        _ = α.1 := hρadda
    have hsub : η = α := Subtype.ext hηα
    exact hαZ (hsub ▸ hηV.1)
  obtain ⟨γ, d, hacnf⟩ :=
    cnf_eq_singleton_of_isLUB Q a hQne hsingleQ hlubQ
  have hβγ : β < γ := cnf_singleton_exponent_lt_of_isLUB_not_mem
    Q a hsingleQ hlubQ haQ ⟨η₀, hη₀V, rfl⟩ hq₀cnf hacnf
  obtain ⟨hq₀eq, _, _, hlogq₀⟩ := cnf_singleton_spec hq₀cnf
  obtain ⟨haeq, hdpos, _, _⟩ := cnf_singleton_spec hacnf
  have hq₀a : (η₀.1 - ρ) + a = a := by
    apply Ordinal.add_of_omega0_opow_le
    · apply (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 ?_).2
      · simpa only [hlogq₀] using hβγ
      · rw [hq₀eq]
        exact mul_ne_zero (Ordinal.opow_ne_zero β Ordinal.omega0_ne_zero)
          (ne_of_gt (cnf_singleton_spec hq₀cnf).2.1)
    · rw [haeq]
      exact Ordinal.le_mul_left _ hdpos
  have hη₀adda : η₀.1 + a = α.1 := by
    calc
      η₀.1 + a = (ρ + (η₀.1 - ρ)) + a := by rw [hρaddη₀]
      _ = ρ + ((η₀.1 - ρ) + a) := add_assoc _ _ _
      _ = ρ + a := by rw [hq₀a]
      _ = α.1 := hρadda
  have hη₀α : cnfExtensionLT η₀.1 α.1 := by
    rw [← hη₀adda]
    exact cnfExtensionLT_add_singleton_of_last hη₀cnf hacnf hβγ.le
  exact cnfExtensionLE_partialOrder_and_subrelation.1.trans
    ζ.1 η₀.1 α.1 (Or.inr hζη₀) (Or.inr hη₀α)

private theorem leastCNFExponent_chain_lub_le
    (ξ γ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1)
    (hleast : ∀ ζ ∈ Z, leastCNFExponent ζ.1 < γ) :
    leastCNFExponent α.1 ≤ γ := by
  classical
  by_cases hαZ : α ∈ Z
  · exact (hleast α hαZ).le
  obtain ⟨ζ, hζZ⟩ := hne
  have hζα : ζ.1 < α.1 := (hsup.1 ⟨ζ, hζZ, rfl⟩).lt_of_ne fun h ↦ by
    have hsub : ζ = α := Subtype.ext h
    exact hαZ (hsub ▸ hζZ)
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := by
    by_contra h
    have hαζ : α.1 ≤ ζ.1 := hsup.2 (by
      rintro _ ⟨η, hηZ, rfl⟩
      exact le_of_not_gt fun hζη ↦ h ⟨η, hηZ, hζη⟩)
    exact (not_le_of_gt hζα) hαζ
  obtain ⟨η₀, hη₀U, hη₀min⟩ := exists_minimalFor_of_wellFoundedLT U
    (fun η : GaoIndex ξ ↦ (Ordinal.CNF Ordinal.omega0 η.1).length) hU
  have hη₀Z : η₀ ∈ Z := hη₀U.1
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀Z, le_rfl⟩
  have hrelV : ∀ η ∈ V, cnfExtensionLE η₀.1 η.1 := by
    intro η hηV
    rcases hchain hη₀Z hηV.1 with h | h
    · exact h
    · exact Or.inl (le_antisymm hηV.2
        (cnfExtensionLE_partialOrder_and_subrelation.2 h))
  have hlenV : ∀ η ∈ V,
      (Ordinal.CNF Ordinal.omega0 η.1).length =
        (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · rw [heq]
    · have hle : (Ordinal.CNF Ordinal.omega0 η.1).length ≤
          (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
        rcases cnfExtensionLT_iff_CNFListLT.mp hlt with
          ⟨pre, tail, x, y, hη₀cnf, hηcnf, _⟩
        rw [hη₀cnf, hηcnf]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      exact le_antisymm hle
        (hη₀min ⟨hηV.1, hη₀U.2.trans_le hηV.2⟩ hle)
  let pre := (Ordinal.CNF Ordinal.omega0 η₀.1).dropLast
  have hη₀ne : Ordinal.CNF Ordinal.omega0 η₀.1 ≠ [] := by
    have hη₀pos : 0 < η₀.1 :=
      (zero_le : (0 : Ordinal) ≤ ζ.1).trans_lt hη₀U.2
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 η₀.1
    rw [h] at hfold
    exact hη₀pos.ne' hfold.symm
  have hcnfV : ∀ η ∈ V, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · have hsub : η₀ = η := Subtype.ext heq
      subst η
      let p := (Ordinal.CNF Ordinal.omega0 η₀.1).getLast hη₀ne
      refine ⟨p.1, p.2, ?_⟩
      simpa only [pre, p] using (List.dropLast_append_getLast hη₀ne).symm
    · obtain ⟨x, y, _, hηcnf, _⟩ :=
        CNFListLT.eq_dropLast_of_length_eq
          (cnfExtensionLT_iff_CNFListLT.mp hlt) (hlenV η hηV)
      exact ⟨y.1, y.2, hηcnf⟩
  let ρ : Ordinal.{u} := cnfValue pre
  have residual_of_common : ∀ (η : GaoIndex ξ) (δ d : Ordinal.{u}),
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] →
      Ordinal.CNF Ordinal.omega0 (η.1 - ρ) = [(δ, d)] ∧
        ρ + (η.1 - ρ) = η.1 := by
    intro η δ d hηcnf
    have hηeq : ρ + cnfValue [(δ, d)] = η.1 := by
      rw [← Ordinal.CNF.foldr Ordinal.omega0 η.1]
      change ρ + cnfValue [(δ, d)] = cnfValue (Ordinal.CNF Ordinal.omega0 η.1)
      rw [hηcnf, cnfValue_append]
    have hρle : ρ ≤ η.1 := hηeq ▸ le_self_add
    have hsub : η.1 - ρ = cnfValue [(δ, d)] :=
      Ordinal.sub_eq_of_add_eq hηeq
    constructor
    · rw [hsub]
      apply CNF_cnfValue
      · simp
      · intro p hp
        exact Ordinal.CNF.snd_pos (by
          rw [hηcnf]
          exact List.mem_append_right _ hp)
      · intro p hp
        exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
          rw [hηcnf]
          exact List.mem_append_right _ hp)
    · exact Ordinal.add_sub_cancel_of_le hρle
  let Q : Set (Ordinal.{u}) := (fun η : GaoIndex ξ ↦ η.1 - ρ) '' V
  have hQne : Q.Nonempty := ⟨η₀.1 - ρ, ⟨η₀, hη₀V, rfl⟩⟩
  have hsingleQ : ∀ q ∈ Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ := by
    rintro q ⟨η, hηV, rfl⟩
    obtain ⟨δ, d, hηcnf⟩ := hcnfV η hηV
    refine ⟨δ, d, (residual_of_common η δ d hηcnf).1, ?_⟩
    have := hleast η hηV.1
    simpa [leastCNFExponent, hηcnf] using this
  obtain ⟨δ₀, d₀, hη₀cnf⟩ := hcnfV η₀ hη₀V
  have hρaddη₀ := (residual_of_common η₀ δ₀ d₀ hη₀cnf).2
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hρleα : ρ ≤ α.1 := hρleη₀.trans (hsup.1 ⟨η₀, hη₀Z, rfl⟩)
  let a : Ordinal.{u} := α.1 - ρ
  have hρadda : ρ + a = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  have hlubQ : IsLUB Q a := by
    constructor
    · rintro _ ⟨η, hηV, rfl⟩
      rw [Ordinal.sub_le, hρadda]
      exact hsup.1 ⟨η, hηV.1, rfl⟩
    · intro b hb
      rw [Ordinal.sub_le]
      apply hsup.2
      rintro _ ⟨η, hηZ, rfl⟩
      rcases hchain hηZ hη₀Z with hηη₀ | hη₀η
      · calc
          η.1 ≤ η₀.1 := cnfExtensionLE_partialOrder_and_subrelation.2 hηη₀
          _ = ρ + (η₀.1 - ρ) := hρaddη₀.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η₀, hη₀V, rfl⟩) ρ
      · have hηV : η ∈ V := ⟨hηZ,
          cnfExtensionLE_partialOrder_and_subrelation.2 hη₀η⟩
        obtain ⟨δ, d, hηcnf⟩ := hcnfV η hηV
        have hρaddη := (residual_of_common η δ d hηcnf).2
        calc
          η.1 = ρ + (η.1 - ρ) := hρaddη.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η, hηV, rfl⟩) ρ
  obtain ⟨Γ, D, hacnf⟩ := cnf_eq_singleton_of_isLUB Q a hQne
    (fun q hq ↦ let ⟨δ, d, h, _⟩ := hsingleQ q hq; ⟨δ, d, h⟩) hlubQ
  have hpowUpper : Ordinal.omega0 ^ γ ∈ upperBounds Q := by
    intro q hq
    obtain ⟨δ, d, hqcnf, hδγ⟩ := hsingleQ q hq
    obtain ⟨_, _, _, hlogq⟩ := cnf_singleton_spec hqcnf
    exact ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
      obtain ⟨hqeq, hdpos, _, _⟩ := cnf_singleton_spec hqcnf
      rw [hqeq]
      exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
        hdpos.ne')).2 (by simpa only [hlogq] using hδγ)).le
  have haPow : a ≤ Ordinal.omega0 ^ γ := hlubQ.2 hpowUpper
  obtain ⟨haeq, hDpos, _, _⟩ := cnf_singleton_spec hacnf
  have hΓγ : Γ ≤ γ := by
    rw [haeq] at haPow
    have hΓa : Ordinal.omega0 ^ Γ ≤ Ordinal.omega0 ^ Γ * D :=
      Ordinal.le_mul_left _ hDpos
    exact (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp
      (hΓa.trans haPow)
  have hsortedPre : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 η₀.1).pairwise
    rw [hη₀cnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hposPre : ∀ p ∈ pre, 0 < p.2 := by
    intro p hp
    exact Ordinal.CNF.snd_pos (by rw [hη₀cnf]; exact List.mem_append_left _ hp)
  have hltPre : ∀ p ∈ pre, p.2 < Ordinal.omega0 := by
    intro p hp
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hη₀cnf]
      exact List.mem_append_left _ hp)
  have hαcnf : Ordinal.CNF Ordinal.omega0 α.1 = cnfAddMonomial pre Γ D := by
    rw [← hρadda, haeq]
    exact CNF_cnfValue_add_monomial pre hsortedPre hposPre hltPre Γ D hDpos
      (cnf_singleton_spec hacnf).2.2.1
  rw [leastCNFExponent, hαcnf, cnfAddMonomial_lastExponent]
  exact hΓγ

/-- Claim 2 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_chain_iSup
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    IsLUB (ordinalProjection ξ '' Z) (ordinalProjection ξ α) := by
  classical
  constructor
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact (ordinalProjection_le_iff ξ ζ α).2
      (cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ hζ)
  · intro f hf
    by_cases hαZ : α ∈ Z
    · exact hf ⟨α, hαZ, rfl⟩
    · intro x
      by_cases hx : x.1 α = true
      · change (if x.1 α = true then 1 else 0) ≤ f x
        rw [if_pos hx]
        by_contra hle
        have hfx : f x < 1 := lt_of_not_ge hle
        obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
          isOpen_Iio hfx
        have hαpos : 0 < α.1 := by
          rw [pos_iff_ne_zero]
          intro hαzero
          obtain ⟨ζ, hζ⟩ := hne
          have hζα : ζ.1 ≤ α.1 := hsup.1 ⟨ζ, hζ, rfl⟩
          have hζzero : ζ.1 = 0 :=
            le_antisymm (hαzero ▸ hζα) (zero_le : (0 : Ordinal) ≤ ζ.1)
          apply hαZ
          have hζeq : ζ = α := Subtype.ext (hζzero.trans hαzero.symm)
          exact hζeq ▸ hζ
        let Fα := F.filter fun i ↦ i.1 < α.1
        let δ : Ordinal.{u} := Fα.sup fun i ↦ i.1
        have hδα : δ < α.1 := by
          apply (Finset.sup_lt_iff hαpos).2
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have hex : ∃ ζ ∈ Z, δ < ζ.1 := by
          by_contra h
          push Not at h
          have hαδ : α.1 ≤ δ := hsup.2 (by
            rintro _ ⟨ζ, hζ, rfl⟩
            exact h ζ hζ)
          exact (not_le_of_gt hδα) hαδ
        obtain ⟨ζ₀, hζ₀Z, hδζ₀⟩ := hex
        let y : GaoIndex ξ → Bool := fun a ↦
          if cnfExtensionLE ζ₀.1 a.1 then true else x.1 a
        have hy_mono : ∀ a b : GaoIndex ξ,
            cnfExtensionLT a.1 b.1 → y a ≤ y b := by
          intro a b hab
          dsimp [y]
          by_cases ha : cnfExtensionLE ζ₀.1 a.1
          · have hb : cnfExtensionLE ζ₀.1 b.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.1.trans
                ζ₀.1 a.1 b.1 ha (Or.inr hab)
            rw [if_pos ha, if_pos hb]
          · rw [if_neg ha]
            by_cases hb : cnfExtensionLE ζ₀.1 b.1
            · rw [if_pos hb]
              exact Bool.le_true _
            · rw [if_neg hb]
              exact x.2 a b hab
        have hζ₀α : cnfExtensionLT ζ₀.1 α.1 := by
          rcases cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ₀ hζ₀Z with
            heq | hlt
          · have hsubeq : ζ₀ = α := Subtype.ext heq
            exact (hαZ (hsubeq ▸ hζ₀Z)).elim
          · exact hlt
        have hζ₀αOrd : ζ₀.1 < α.1 :=
          CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp hζ₀α)
        let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
        have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
          intro i hi
          dsimp [yK, y]
          by_cases hζ₀i : cnfExtensionLE ζ₀.1 i.1
          · rw [if_pos hζ₀i]
            have hζ₀iOrd : ζ₀.1 ≤ i.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.2 hζ₀i
            by_cases hiα : i.1 < α.1
            · have hiFα : i ∈ Fα := Finset.mem_filter.mpr ⟨hi, hiα⟩
              have hiδ : i.1 ≤ δ := Finset.le_sup (f := fun j ↦ j.1) hiFα
              exact (not_lt_of_ge hiδ (hδζ₀.trans_le hζ₀iOrd)).elim
            · have hαi : α.1 ≤ i.1 := le_of_not_gt hiα
              rcases hαi.eq_or_lt with hαeqi | hαi
              · have hsubeq : α = i := Subtype.ext hαeqi
                subst i
                exact hx.symm
              · have hζ₀iLT : cnfExtensionLT ζ₀.1 i.1 := by
                  rcases hζ₀i with hζ₀eqi | hζ₀i
                  · exact (not_lt_of_ge hαi.le (hζ₀eqi ▸ hζ₀αOrd)).elim
                  · exact hζ₀i
                have hαiLT : cnfExtensionLT α.1 i.1 :=
                  (cnfExtensionLT_linear_above ζ₀.1 hζ₀α hζ₀iLT).mpr hαi
                exact (Bool.le_iff_imp.mp (x.2 α i hαiLT) hx).symm
          · rw [if_neg hζ₀i]
        have hfy : f yK < 1 := hF yK hyF
        have hupper := hf ⟨ζ₀, hζ₀Z, rfl⟩ yK
        have hyζ₀ : yK.1 ζ₀ = true := by
          dsimp [yK, y]
          rw [if_pos (show cnfExtensionLE ζ₀.1 ζ₀.1 from Or.inl rfl)]
        change (if yK.1 ζ₀ = true then 1 else 0) ≤ f yK at hupper
        rw [if_pos hyζ₀] at hupper
        exact (not_lt_of_ge hupper hfy).elim
      · have hnonneg : 0 ≤ f x := by
          obtain ⟨ζ, hζ⟩ := hne
          have hproj : 0 ≤ ordinalProjection ξ ζ x := by
            change 0 ≤ if x.1 ζ = true then 1 else 0
            split_ifs <;> norm_num
          exact hproj.trans (hf ⟨ζ, hζ, rfl⟩ x)
        simp only [ordinalProjection, hx]
        exact hnonneg

private def gaoDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {ζ | ζ ∈ GaoStageIndices ξ γ ∧ b ≤ ordinalProjection ξ ζ}

private def gaoMinimalDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {μ | μ ∈ gaoDominators ξ γ b ∧
    ∀ η ∈ gaoDominators ξ γ b, cnfExtensionLE η.1 μ.1 → η = μ}

private theorem gaoDominators_nonempty
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hb : b ∈ GaoStageSet ξ γ) :
    (gaoDominators ξ γ b).Nonempty := by
  obtain ⟨ζ, hζ, hbζ⟩ := hb
  refine ⟨ζ, hζ, ?_⟩
  simpa only [abs_of_nonneg hb0] using hbζ

private theorem gaoDominator_above_minimal
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    {ζ : GaoIndex ξ} (hζ : ζ ∈ gaoDominators ξ γ b) :
    ∃ μ ∈ gaoMinimalDominators ξ γ b, cnfExtensionLE μ.1 ζ.1 := by
  classical
  let P : GaoIndex ξ → Prop := fun η ↦
    η ∈ gaoDominators ξ γ b ∧ cnfExtensionLE η.1 ζ.1
  obtain ⟨μ, hμP, hμmin⟩ := exists_minimalFor_of_wellFoundedLT P
    (fun η : GaoIndex ξ ↦ η.1) ⟨ζ, hζ, Or.inl rfl⟩
  refine ⟨μ, ⟨hμP.1, ?_⟩, hμP.2⟩
  intro η hη hημ
  have hηP : P η := ⟨hη,
    cnfExtensionLE_partialOrder_and_subrelation.1.trans
      η.1 μ.1 ζ.1 hημ hμP.2⟩
  have hηleμ := cnfExtensionLE_partialOrder_and_subrelation.2 hημ
  exact Subtype.ext (le_antisymm hηleμ (hμmin hηP hηleμ))

private theorem gaoMinimalDominators_pairwise
    (ξ γ : Ordinal.{u}) (b : C(GaoCompactSpace ξ, ℝ)) :
    (gaoMinimalDominators ξ γ b).Pairwise
      (fun μ ν ↦ ¬ cnfExtensionLE μ.1 ν.1) := by
  intro μ hμ ν hν hne hμν
  exact hne (hν.2 μ hμ.1 hμν)

private theorem gaoMinimalDominators_finite
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hbne : b ≠ 0) :
    (gaoMinimalDominators ξ γ b).Finite := by
  classical
  by_contra hinf
  have hMInf : (gaoMinimalDominators ξ γ b).Infinite := hinf
  have hglb := ordinalProjection_incomparable_iInf ξ
    (gaoMinimalDominators ξ γ b) hMInf
    (gaoMinimalDominators_pairwise ξ γ b)
  have hbLower : b ∈ lowerBounds
      (ordinalProjection ξ '' gaoMinimalDominators ξ γ b) := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact hμ.1.2
  have hb_le_zero : b ≤ 0 := hglb.2 hbLower
  exact hbne (le_antisymm hb_le_zero hb0)

private theorem directedPositive_gaoStage_dominated
    (ξ γ : Ordinal.{u}) {z : C(GaoCompactSpace ξ, ℝ)}
    (hz : z ∈ directedPositiveAdherence (GaoStageSet ξ γ)) :
    ∃ α : GaoIndex ξ, α.1 ≤ Ordinal.omega0 ^ ξ ∧
      leastCNFExponent α.1 ≤ γ ∧ z ≤ ordinalProjection ξ α := by
  classical
  rcases hz with ⟨hz0, B, hBstage, hBne, hBdir, hBlub⟩
  by_cases hzero : z = 0
  · let α : GaoIndex ξ := ⟨0, by simp⟩
    refine ⟨α, by simp [α], by simp [α, leastCNFExponent], ?_⟩
    rw [hzero]
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  have hbne : ∃ b ∈ B, b ≠ 0 := by
    by_contra h
    have hzeroUpper : (0 : C(GaoCompactSpace ξ, ℝ)) ∈ upperBounds B := by
      intro b hb
      have hb0 := (hBstage hb).2
      have hbzero : b = 0 := by
        by_contra hbne'
        exact h ⟨b, hb, hbne'⟩
      rw [hbzero]
    exact hzero (le_antisymm (hBlub.2 hzeroUpper) hz0)
  obtain ⟨b₀, hb₀B, hb₀ne⟩ := hbne
  have hb₀0 : 0 ≤ b₀ := (hBstage hb₀B).2
  let M := gaoMinimalDominators ξ γ b₀
  have hMfin : M.Finite := gaoMinimalDominators_finite ξ γ hb₀0 hb₀ne
  have hMne : M.Nonempty := by
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb₀0 (hBstage hb₀B).1
    obtain ⟨μ, hμ, _⟩ := gaoDominator_above_minimal ξ γ hζ
    exact ⟨μ, hμ⟩
  letI : Nonempty B := hBne.to_subtype
  letI : IsDirectedOrder B := hBdir.isDirectedOrder
  let b₀B : B := ⟨b₀, hb₀B⟩
  let D : M → Set B := fun μ ↦
    {b | b₀ ≤ b.1 ∧ ∃ ζ ∈ gaoDominators ξ γ b.1,
      cnfExtensionLE μ.1.1 ζ.1}
  have hcover : ∀ b : B, b₀ ≤ b.1 → ∃ μ : M, b ∈ D μ := by
    intro b hb₀b
    have hb0 : 0 ≤ b.1 := (hBstage b.2).2
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb0 (hBstage b.2).1
    have hζ₀ : ζ ∈ gaoDominators ξ γ b₀ := ⟨hζ.1, hb₀b.trans hζ.2⟩
    obtain ⟨μ, hμ, hμζ⟩ := gaoDominator_above_minimal ξ γ hζ₀
    exact ⟨⟨μ, hμ⟩, hb₀b, ζ, hζ, hμζ⟩
  have hcofinal : ∃ μ : M, ∀ b : B, ∃ c ∈ D μ, b ≤ c := by
    by_contra h
    have hbad : ∀ μ : M, ∃ b : B, ∀ c ∈ D μ, ¬ b ≤ c := by
      intro μ
      have hμ : ¬ ∀ b : B, ∃ c ∈ D μ, b ≤ c := fun hμ ↦ h ⟨μ, hμ⟩
      push Not at hμ
      exact hμ
    choose w hw using hbad
    letI : Fintype M := hMfin.fintype
    obtain ⟨d, hd⟩ := Finite.exists_le w
    obtain ⟨e, hde, hb₀e⟩ := exists_ge_ge d b₀B
    obtain ⟨μ, heD⟩ := hcover e hb₀e
    exact (hw μ e heD) ((hd μ).trans hde)
  obtain ⟨μ, hμcofinal⟩ := hcofinal
  have hDne : (D μ).Nonempty := by
    obtain ⟨c, hcD, _⟩ := hμcofinal b₀B
    exact ⟨c, hcD⟩
  let ζfun : D μ → GaoIndex ξ := fun b ↦ Classical.choose b.2.2
  have hζfun : ∀ b : D μ,
      ζfun b ∈ gaoDominators ξ γ b.1.1 ∧
        cnfExtensionLE μ.1.1 (ζfun b).1 := fun b ↦
    ⟨Classical.choose_spec b.2.2 |>.1,
      Classical.choose_spec b.2.2 |>.2⟩
  let Z : Set (GaoIndex ξ) := Set.range ζfun
  have hZne : Z.Nonempty := by
    obtain ⟨b, hb⟩ := hDne
    exact ⟨ζfun ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have hZchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1 := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    exact cnfExtensionLE_linear_above μ.1.1 (hζfun b).2 (hζfun c).2
  let a : Ordinal.{u} := sSup ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z)
  have hvalsne : ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z).Nonempty := hZne.image _
  have hvalsBdd : BddAbove ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) := by
    refine ⟨Ordinal.omega0 ^ ξ, ?_⟩
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  have haLUB : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) a :=
    isLUB_csSup hvalsne hvalsBdd
  have hale : a ≤ Ordinal.omega0 ^ ξ := by
    apply haLUB.2
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  let α : GaoIndex ξ := ⟨a, hale.trans le_self_add⟩
  have hprojLUB : IsLUB (ordinalProjection ξ '' Z)
      (ordinalProjection ξ α) :=
    ordinalProjection_chain_iSup ξ Z α hZne hZchain haLUB
  have hzα : z ≤ ordinalProjection ξ α := hBlub.2 (by
    intro b hbB
    obtain ⟨c, hcD, hbc⟩ := hμcofinal ⟨b, hbB⟩
    let cD : D μ := ⟨c, hcD⟩
    calc
      b ≤ c.1 := hbc
      _ ≤ ordinalProjection ξ (ζfun cD) := (hζfun cD).1.2
      _ ≤ ordinalProjection ξ α := hprojLUB.1 ⟨ζfun cD, ⟨cD, rfl⟩, rfl⟩)
  have hleast : leastCNFExponent α.1 ≤ γ := by
    apply leastCNFExponent_chain_lub_le ξ γ Z α hZne hZchain haLUB
    rintro _ ⟨b, rfl⟩
    exact (hζfun b).1.1.2
  exact ⟨α, hale, hleast, hzα⟩

private theorem orderAdherence_gaoStage_subset
    (ξ γ : Ordinal.{u}) :
    orderAdherence (GaoStageSet ξ γ) ⊆ GaoStageSet ξ (γ + 1) := by
  rw [orderAdherence_eq_solidOrderAdherence (isSolid_gaoStageSet ξ γ)]
  rintro f ⟨z, hz, hfz⟩
  obtain ⟨α, hαbound, hαleast, hzα⟩ :=
    directedPositive_gaoStage_dominated ξ γ hz
  refine ⟨α, ⟨hαbound, ?_⟩, hfz.trans ?_⟩
  · exact hαleast.trans_lt (lt_add_one γ)
  · simpa only [abs_of_nonneg hz.1] using hzα

private def singletonCNFBelow (γ : Ordinal.{u}) : Set (Ordinal.{u}) :=
  {q | ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧
    q < Ordinal.omega0 ^ γ}

private theorem singletonCNFBelow_isLUB (γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    IsLUB (singletonCNFBelow γ) (Ordinal.omega0 ^ γ) := by
  constructor
  · rintro q ⟨δ, d, hq, hqpow⟩
    exact hqpow.le
  · intro c hc
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ γ) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hγ
    apply hlim.isLUB_Iio.2
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      exact zero_le
    let δ := Ordinal.log Ordinal.omega0 r
    let d := r / Ordinal.omega0 ^ δ
    let q := Ordinal.omega0 ^ δ * (d + 1)
    have hdpos : 0 < d := Ordinal.div_opow_log_pos Ordinal.omega0 hr0
    have hdlt : d < Ordinal.omega0 :=
      Ordinal.div_opow_log_lt r Ordinal.one_lt_omega0
    have hdsuccpos : 0 < d + 1 := hdpos.trans_le le_self_add
    have hdsucclt : d + 1 < Ordinal.omega0 := by
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hdlt
      rw [hn, ← Nat.cast_one, ← Nat.cast_add]
      exact Ordinal.natCast_lt_omega0 (n + 1)
    have hδγ : δ < γ :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).mp hr
    have hqcnf : Ordinal.CNF Ordinal.omega0 q = [(δ, d + 1)] := by
      dsimp [q]
      simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
        (e := δ) (x := d + 1) (y := 0) Ordinal.one_lt_omega0
        hdsuccpos.ne' hdsucclt (Ordinal.opow_pos δ Ordinal.omega0_pos)
    have hqpow : q < Ordinal.omega0 ^ γ := by
      dsimp [q]
      simpa only [add_zero] using Ordinal.opow_mul_add_lt_opow hdsucclt
        (Ordinal.opow_pos δ Ordinal.omega0_pos) hδγ
    have hrq : r < q := by
      rw [← Ordinal.div_add_mod r (Ordinal.omega0 ^ δ)]
      dsimp [q, d]
      exact Ordinal.opow_mul_add_lt_opow_mul
        (Ordinal.mod_lt r (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero))
        (lt_add_one (r / Ordinal.omega0 ^ δ))
    exact hrq.le.trans (hc ⟨δ, d + 1, hqcnf, hqpow⟩)

private theorem singletonCNF_step_of_lt
    {q r δ d ε e : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(δ, d)])
    (hr : Ordinal.CNF Ordinal.omega0 r = [(ε, e)]) (hqr : q < r) :
    (ε = δ ∧ d < e) ∨ δ < ε := by
  obtain ⟨hqeq, _, _, hlogq⟩ := cnf_singleton_spec hq
  obtain ⟨hreq, _, _, hlogr⟩ := cnf_singleton_spec hr
  have hδε : δ ≤ ε := by
    have := Ordinal.log_mono_right Ordinal.omega0 hqr.le
    simpa only [hlogq, hlogr] using this
  rcases hδε.eq_or_lt with hδε | hδε
  · left
    refine ⟨hδε.symm, ?_⟩
    rw [← hδε] at hreq
    by_contra h
    have hed : e ≤ d := le_of_not_gt h
    have hmul : Ordinal.omega0 ^ δ * e ≤ Ordinal.omega0 ^ δ * d :=
      mul_le_mul_right hed _
    exact (not_le_of_gt (by rw [← hqeq, ← hreq]; exact hqr)) hmul
  · exact Or.inr hδε

private theorem gaoIndex_approximation
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) (ζ : GaoIndex ξ)
    (hζbound : ζ.1 ≤ Ordinal.omega0 ^ ξ)
    (hζleast : leastCNFExponent ζ.1 = γ) :
    ∃ Z : Set (GaoIndex ξ), Z.Nonempty ∧
      (∀ η ∈ Z, η ∈ GaoStageIndices ξ γ) ∧
      (∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
        cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1) ∧
      IsLUB ((fun η : GaoIndex ξ ↦ η.1) '' Z) ζ.1 := by
  classical
  have hζ0 : ζ.1 ≠ 0 := by
    intro hzero
    have : γ = 0 := by
      rw [← hζleast, hzero]
      simp [leastCNFExponent]
    exact hγ this
  let pre := (Ordinal.CNF Ordinal.omega0 ζ.1).dropLast
  have hcnfne : Ordinal.CNF Ordinal.omega0 ζ.1 ≠ [] := by
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 ζ.1
    rw [h] at hfold
    exact hζ0 hfold.symm
  let p := (Ordinal.CNF Ordinal.omega0 ζ.1).getLast hcnfne
  have hpcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [p] := by
    simpa only [pre, p] using (List.dropLast_append_getLast hcnfne).symm
  have hpγ : p.1 = γ := by
    have := hζleast
    rw [leastCNFExponent, hpcnf] at this
    have hlast : (pre ++ [p]).getLast? = some p := by simp
    rw [hlast] at this
    simpa using this
  let c := p.2
  have hpeq : p = (γ, c) := Prod.ext hpγ rfl
  have hζcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [(γ, c)] := by
    rw [hpcnf, hpeq]
  have hcpos : 0 < c := by
    apply Ordinal.CNF.snd_pos (x := (γ, c))
    rw [hζcnf]
    simp
  have hclt : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (x := (γ, c))
    rw [hζcnf]
    simp
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hclt
  have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let ρ : Ordinal.{u} := cnfValue pre
  let base : Ordinal.{u} := ρ + Ordinal.omega0 ^ γ * (n : Ordinal)
  have hζeq : ζ.1 = base + Ordinal.omega0 ^ γ := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ.1, hζcnf, hm]
    change cnfValue (pre ++ [(γ, ((n + 1 : ℕ) : Ordinal))]) =
      base + Ordinal.omega0 ^ γ
    rw [cnfValue_append]
    simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
    dsimp [base, ρ]
    change cnfValue pre + Ordinal.omega0 ^ γ * ((n + 1 : ℕ) : Ordinal) =
      cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + Ordinal.omega0 ^ γ
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
  let Q := singletonCNFBelow γ
  have hQne : Q.Nonempty := by
    have hγpos : 0 < γ := (pos_iff_ne_zero).2 hγ
    have honepow : (1 : Ordinal) < Ordinal.omega0 ^ γ := by
      have hp : Ordinal.omega0 ^ (1 : Ordinal) ≤ Ordinal.omega0 ^ γ :=
        (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).2
          (by simpa using (Order.succ_le_iff.2 hγpos : Order.succ 0 ≤ γ))
      exact Ordinal.one_lt_omega0.trans_le (by simpa using hp)
    refine ⟨1, 0, 1, ?_, honepow⟩
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := 0) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos 0 Ordinal.omega0_pos)
  let ηval : Q → Ordinal.{u} := fun q ↦ base + q.1
  have hηlt : ∀ q : Q, ηval q < ζ.1 := by
    intro q
    obtain ⟨δ, d, hqcnf, hqpow⟩ := q.2
    rw [hζeq]
    exact (add_lt_add_iff_left base).2 hqpow
  let η : Q → GaoIndex ξ := fun q ↦
    ⟨ηval q, (hηlt q).le.trans hζbound |>.trans le_self_add⟩
  have hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hpreAbove : ∀ x ∈ pre, γ < x.1 := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    intro x hx
    exact h.2.2 x.1 (by exact List.mem_map.mpr ⟨x, hx, rfl⟩)
      γ (by simp)
  have hprePos : ∀ x ∈ pre, 0 < x.2 := by
    intro x hx
    exact Ordinal.CNF.snd_pos (by rw [hζcnf]; exact List.mem_append_left _ hx)
  have hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0 := by
    intro x hx
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hζcnf]
      exact List.mem_append_left _ hx)
  have hηcnf : ∀ q : Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q.1 = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0 (η q).1 =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by
    intro q
    obtain ⟨δ, d, hqcnf, hqpow⟩ := q.2
    obtain ⟨hqeq, hdpos, hdlt, hlogq⟩ := cnf_singleton_spec hqcnf
    have hδγraw : Ordinal.log Ordinal.omega0 q.1 < γ :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
        rw [hqeq]
        exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
          hdpos.ne')).mp hqpow
    have hδγ : δ < γ := by simpa only [hlogq] using hδγraw
    refine ⟨δ, d, hqcnf, hδγ, ?_⟩
    by_cases hn : n = 0
    · subst n
      dsimp [η, ηval, base]
      simp only [Nat.cast_zero, mul_zero, add_zero]
      rw [hqeq, CNF_cnfValue_add_monomial pre hpreSorted hprePos hpreLt
        δ d hdpos hdlt, cnfAddMonomial_eq_append_of_lt_all pre δ d
          (fun x hx ↦ hδγ.trans (hpreAbove x hx))]
    · let l := pre ++ [(γ, (n : Ordinal))]
      have hnpos : 0 < (n : Ordinal) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hnlt : (n : Ordinal) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 n
      have hlsorted : (l.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
        dsimp [l]
        rw [List.map_append, List.pairwise_append]
        refine ⟨hpreSorted, by simp, ?_⟩
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        simp only [List.map_singleton, List.mem_singleton] at hb
        subst b
        exact hpreAbove x hx
      have hlpos : ∀ x ∈ l, 0 < x.2 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hprePos x hx
        · simp only [List.mem_singleton] at hx
          subst x
          exact hnpos
      have hllt : ∀ x ∈ l, x.2 < Ordinal.omega0 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hpreLt x hx
        · simp only [List.mem_singleton] at hx
          subst x
          exact hnlt
      have hδl : ∀ x ∈ l, δ < x.1 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hδγ.trans (hpreAbove x hx)
        · simp only [List.mem_singleton] at hx
          subst x
          exact hδγ
      rw [if_neg hn]
      dsimp [η, ηval, base]
      change Ordinal.CNF Ordinal.omega0
        ((ρ + Ordinal.omega0 ^ γ * (n : Ordinal)) + q.1) =
          pre ++ (γ, (n : Ordinal)) :: [(δ, d)]
      have hlvalue : cnfValue l = ρ + Ordinal.omega0 ^ γ * (n : Ordinal) := by
        dsimp [l, ρ]
        rw [cnfValue_append]
        simp [cnfValue]
      rw [← hlvalue, hqeq,
        CNF_cnfValue_add_monomial l hlsorted hlpos hllt δ d hdpos hdlt,
        cnfAddMonomial_eq_append_of_lt_all l δ d hδl]
      simp [l, List.append_assoc]
  have hηstage : ∀ q : Q, η q ∈ GaoStageIndices ξ γ := by
    intro q
    obtain ⟨δ, d, hqcnf, hδγ, hcnf⟩ := hηcnf q
    refine ⟨(hηlt q).le.trans hζbound, ?_⟩
    rw [leastCNFExponent, hcnf]
    split_ifs <;> simp_all
  have hηrel : ∀ q : Q, cnfExtensionLT (η q).1 ζ.1 := by
    intro q
    obtain ⟨δ, d, hqcnf, hδγ, hcnf⟩ := hηcnf q
    by_cases hn : n = 0
    · refine ⟨pre, [], δ, d, γ, ((n + 1 : ℕ) : Ordinal), ?_, ?_, ?_⟩
      · simpa [hn] using hcnf
      · simpa [hm] using hζcnf
      · exact Or.inr ⟨hδγ, by
          by_cases hp : pre = []
          · exact Or.inl hp
          · let last := pre.getLast hp
            have hlast : pre.getLast? = some last := by
              dsimp [last]
              exact List.getLast?_eq_getLast_of_ne_nil hp
            have hlastMem : last ∈ pre := by
              dsimp [last]
              exact List.getLast_mem hp
            exact Or.inr ⟨last.1, last.2, hlast, by
              exact hpreAbove last hlastMem⟩⟩
    · refine ⟨pre, [(δ, d)], γ, (n : Ordinal), γ,
        ((n + 1 : ℕ) : Ordinal), ?_, ?_, ?_⟩
      · simpa [hn] using hcnf
      · simpa [hm] using hζcnf
      · exact Or.inl ⟨rfl, by exact_mod_cast (Nat.lt_succ_self n)⟩
  let Z : Set (GaoIndex ξ) := Set.range η
  letI : Nonempty Q := hQne.to_subtype
  have hZne : Z.Nonempty := Set.range_nonempty η
  have hZstage : ∀ η' ∈ Z, η' ∈ GaoStageIndices ξ γ := by
    rintro _ ⟨q, rfl⟩
    exact hηstage q
  have hηchainLT : ∀ q r : Q, q.1 < r.1 →
      cnfExtensionLT (η q).1 (η r).1 := by
    intro q r hqr
    obtain ⟨δ, d, hqcnf, hδγ, hqηcnf⟩ := hηcnf q
    obtain ⟨ε, e, hrcnf, hεγ, hrηcnf⟩ := hηcnf r
    have hstep := singletonCNF_step_of_lt hqcnf hrcnf hqr
    by_cases hn : n = 0
    · refine ⟨pre, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn] using hqηcnf
      · simpa [hn] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, by
            by_cases hp : pre = []
            · exact Or.inl hp
            · let last := pre.getLast hp
              have hlast : pre.getLast? = some last := by
                dsimp [last]
                exact List.getLast?_eq_getLast_of_ne_nil hp
              have hlastMem : last ∈ pre := by
                dsimp [last]
                exact List.getLast_mem hp
              exact Or.inr ⟨last.1, last.2, hlast,
                hεγ.trans (hpreAbove last hlastMem)⟩⟩
    · let common := pre ++ [(γ, (n : Ordinal))]
      refine ⟨common, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn, common, List.append_assoc] using hqηcnf
      · simpa [hn, common, List.append_assoc] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, Or.inr ⟨γ, (n : Ordinal), by
            simp [common], hεγ⟩⟩
  have hZchain : ∀ ⦃η₁⦄, η₁ ∈ Z → ∀ ⦃η₂⦄, η₂ ∈ Z →
      cnfExtensionLE η₁.1 η₂.1 ∨ cnfExtensionLE η₂.1 η₁.1 := by
    rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩
    rcases lt_trichotomy q.1 r.1 with hlt | heq | hgt
    · exact Or.inl (Or.inr (hηchainLT q r hlt))
    · have hsub : q = r := Subtype.ext heq
      subst r
      exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr (hηchainLT r q hgt))
  have hvalLUB : IsLUB ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) ζ.1 := by
    have hmap := (Ordinal.isNormal_add_right base).map_isLUB
      (singletonCNFBelow_isLUB γ hγ) hQne
    rw [hζeq]
    have hsets : ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) =
        (fun q : Ordinal.{u} ↦ base + q) '' Q := by
      ext x
      constructor
      · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
        exact ⟨q.1, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨η ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    rw [hsets]
    exact hmap
  exact ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩

private theorem gaoStage_succ_subset_orderAdherence
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    GaoStageSet ξ (γ + 1) ⊆ orderAdherence (GaoStageSet ξ γ) := by
  classical
  intro f hf
  obtain ⟨ζ, hζstage, hfζ⟩ := hf
  by_cases hleast : leastCNFExponent ζ.1 < γ
  · exact subset_orderAdherence (GaoStageSet ξ γ)
      ⟨ζ, ⟨hζstage.1, hleast⟩, hfζ⟩
  have hleastLe : leastCNFExponent ζ.1 ≤ γ := by
    rw [← Order.succ_eq_add_one] at hζstage
    exact Order.lt_succ_iff.mp hζstage.2
  have hleastEq : leastCNFExponent ζ.1 = γ :=
    le_antisymm hleastLe (le_of_not_gt hleast)
  obtain ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩ :=
    gaoIndex_approximation ξ γ hγ ζ hζstage.1 hleastEq
  have hprojLUB := ordinalProjection_chain_iSup ξ Z ζ hZne hZchain hvalLUB
  letI : Nonempty Z := hZne.to_subtype
  let p : Z → C(GaoCompactSpace ξ, ℝ) := fun η ↦ ordinalProjection ξ η.1
  have hpmono : Monotone p := by
    intro η θ hηθ
    apply (ordinalProjection_le_iff ξ η.1 θ.1).2
    rcases hZchain η.2 θ.2 with h | h
    · exact h
    · have hOrd := cnfExtensionLE_partialOrder_and_subrelation.2 h
      exact Or.inl (le_antisymm hηθ hOrd)
  have hpLUB : IsLUB (Set.range p) (ordinalProjection ξ ζ) := by
    have hsets : Set.range p = ordinalProjection ξ '' Z := by
      ext g
      constructor
      · rintro ⟨η, rfl⟩
        exact ⟨η.1, η.2, rfl⟩
      · rintro ⟨η, hηZ, rfl⟩
        exact ⟨⟨η, hηZ⟩, rfl⟩
    rw [hsets]
    exact hprojLUB
  have hprojAdh : ordinalProjection ξ ζ ∈ orderAdherence (GaoStageSet ξ γ) := by
    refine ⟨Z, inferInstance, inferInstance, inferInstance, p, ?_,
      orderConvergesTo_of_monotone_isLUB hpmono hpLUB⟩
    intro η
    refine ⟨η.1, hZstage η.1 η.2, ?_⟩
    have hnonneg : 0 ≤ ordinalProjection ξ η.1 := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg]
  apply isSolid_orderAdherence (isSolid_gaoStageSet ξ γ) hprojAdh
  have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  simpa only [abs_of_nonneg hnonneg] using hfζ

private theorem orderAdherence_gaoStage
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    orderAdherence (GaoStageSet ξ γ) = GaoStageSet ξ (γ + 1) :=
  Set.Subset.antisymm (orderAdherence_gaoStage_subset ξ γ)
    (gaoStage_succ_subset_orderAdherence ξ γ hγ)

/-- Claim 3 in the proof of Theorem `thm:solid-iterations`. -/
theorem gao_orderAdherence_stage_formula
    (ξ : Ordinal.{u}) (T : OrderAdherenceTower (GaoStageSet ξ 1)) :
    ∀ β ≤ ξ, T.stage (Ordinal.lift.{u + 1, u} β) = GaoStageSet ξ (1 + β) := by
  intro β
  induction β using Ordinal.limitRecOn with
  | zero =>
      intro hzero
      simpa using T.stage_zero
  | add_one β ih =>
      intro hβ
      have hβξ : β ≤ ξ := le_self_add.trans hβ
      have hstage := ih hβξ
      have hnonzero : 1 + β ≠ 0 := by
        exact (zero_lt_one.trans_le (le_self_add : (1 : Ordinal) ≤ 1 + β)).ne'
      rw [show Ordinal.lift.{u + 1, u} (β + 1) =
          Order.succ (Ordinal.lift.{u + 1, u} β) by
            rw [← Order.succ_eq_add_one, Ordinal.lift_succ],
        T.stage_succ, hstage, orderAdherence_gaoStage ξ (1 + β) hnonzero,
        add_assoc]
  | limit β hβlim ih =>
      intro hβξ
      rw [T.stage_limit _ (Ordinal.isSuccLimit_lift.mpr hβlim)]
      ext f
      constructor
      · intro hf
        rcases Set.mem_iUnion.mp hf with ⟨η, hfη⟩
        obtain ⟨δ, hδη⟩ := Ordinal.mem_range_lift_of_le η.2.le
        have hδβ : δ < β := by
          have h := η.2
          rw [← hδη] at h
          exact Ordinal.lift_lt.mp h
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        have hfδ : f ∈ GaoStageSet ξ (1 + δ) := by
          rw [← ih δ hδβ hδξ]
          simpa only [hδη] using hfη
        obtain ⟨ζ, hζ, hfζ⟩ := hfδ
        exact ⟨ζ, ⟨hζ.1, hζ.2.trans_le (add_le_add_right hδβ.le 1)⟩, hfζ⟩
      · intro hf
        obtain ⟨ζ, hζ, hfζ⟩ := hf
        obtain ⟨δ, hδβ, hleastδ⟩ :=
          ((Ordinal.isNormal_add_right 1).lt_iff_exists_lt hβlim).mp hζ.2
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        apply Set.mem_iUnion.mpr
        let η : Set.Iio (Ordinal.lift.{u + 1, u} β) :=
          ⟨Ordinal.lift.{u + 1, u} δ, Ordinal.lift_lt.mpr hδβ⟩
        refine ⟨η, ?_⟩
        rw [ih δ hδβ hδξ]
        exact ⟨ζ, ⟨hζ.1, hleastδ⟩, hfζ⟩

/-- The strict witness separating consecutive stages in Claim 3. -/
theorem ordinalProjection_strict_stage
    (ξ γ : Ordinal.{u}) (hγ : γ ≤ ξ) :
    ∃ ζ : GaoIndex ξ,
      ordinalProjection ξ ζ ∈ GaoStageSet ξ (γ + 1) ∧
        ordinalProjection ξ ζ ∉ GaoStageSet ξ γ := by
  have hpow : Ordinal.omega0 ^ γ ≤ Ordinal.omega0 ^ ξ :=
    Ordinal.opow_le_opow_right Ordinal.omega0_pos hγ
  let ζ : GaoIndex ξ := ⟨Ordinal.omega0 ^ γ,
    hpow.trans le_self_add⟩
  have hcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = [(γ, 1)] := by
    dsimp [ζ]
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := γ) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos γ Ordinal.omega0_pos)
  have hleast : leastCNFExponent ζ.1 = γ := by
    simp [leastCNFExponent, hcnf]
  refine ⟨ζ, ?_, ?_⟩
  · refine ⟨ζ, ⟨hpow, ?_⟩, ?_⟩
    · rw [hleast]
      rw [Ordinal.lt_add_iff one_ne_zero]
      exact ⟨0, zero_lt_one, by simp⟩
    · have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
        intro x
        simp only [ordinalProjection]
        split_ifs <;> norm_num
      rw [abs_of_nonneg hnonneg]
  · rintro ⟨η, hη, hdom⟩
    have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg] at hdom
    have hrel := (ordinalProjection_le_iff ξ ζ η).mp hdom
    rcases hrel with heq | hrel
    · have : leastCNFExponent η.1 = γ := by
        rw [← heq]
        exact hleast
      exact (lt_irrefl γ) (by simpa only [this] using hη.2)
    · rcases hrel with ⟨pre, tail, β, c, δ, d, hζcnf, hηcnf, hstep⟩
      rw [hcnf] at hζcnf
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨hhead, rfl⟩
          have hβ : β = γ := congrArg Prod.fst hhead.symm
          have hc : c = 1 := congrArg Prod.snd hhead.symm
          subst β
          subst c
          have hγδ : γ ≤ δ := by
            rcases hstep with ⟨rfl, _⟩ | ⟨hγδ, _⟩
            · exact le_rfl
            · exact hγδ.le
          have hleastη : leastCNFExponent η.1 = δ := by
            simp [leastCNFExponent, hηcnf]
          exact (not_lt_of_ge (hleastη.symm ▸ hγδ)) hη.2
      | cons p pre =>
          simp only [List.cons_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨rfl, hfalse⟩
          simp at hfalse

/-- Paper Theorem `thm:solid-iterations`. Here `κ⁺` is represented by the
initial ordinal of the successor cardinal. -/
private noncomputable def canonicalOrderAdherenceTower
    {X : Type v} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] (A : Set X) : OrderAdherenceTower A where
  stage η := transfiniteIterate orderAdherence η A
  stage_zero := transfiniteIterate_bot _ _
  stage_succ η := transfiniteIterate_succ _ _ _ (by
    rw [not_isMax_iff]
    exact ⟨η + 1, lt_add_one η⟩)
  stage_limit η hη := by
    rw [transfiniteIterate_limit _ _ _ hη]
    ext x
    simp

private abbrev GaoSuccessorGenerator (β : Ordinal.{u}) :=
  {ζ : GaoIndex β // ζ ∈ GaoStageIndices β 1}

private abbrev GaoComponentIndex (κ : Cardinal.{u}) :=
  Set.Iio (Cardinal.ord (Order.succ κ))

private abbrev GaoComponent (β : Ordinal.{u}) :=
  C(GaoCompactSpace β, ℝ)

private abbrev GaoIterationProduct (κ : Cardinal.{u}) :=
  (∀ β : GaoComponentIndex κ, GaoComponent β.1) ×
    (ULift.{u + 1, u} (Cardinal.ord κ).ToType → ℝ)

private instance (κ : Cardinal.{u}) : IsOrderedAddMonoid (GaoIterationProduct κ) where
  add_le_add_left a b hab c := by
    constructor
    · intro β
      simpa [add_comm] using add_le_add_right (hab.1 β) (c.1 β)
    · intro i
      simpa [add_comm] using add_le_add_right (hab.2 i) (c.2 i)

private instance (κ : Cardinal.{u}) : PosSMulMono ℝ (GaoIterationProduct κ) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hbc := by
    constructor
    · intro β
      rw [ContinuousMap.le_def]
      intro y
      exact smul_le_smul_of_nonneg_left ((hbc.1 β) y) ha
    · intro i
      exact smul_le_smul_of_nonneg_left (hbc.2 i) ha

private noncomputable instance (κ : Cardinal.{u}) : VectorLattice (GaoIterationProduct κ) where

private theorem gaoIterationProduct_abs_fst
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ) (β : GaoComponentIndex κ) :
    |x|.1 β = |x.1 β| := rfl

private theorem gaoIterationProduct_abs_snd
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    |x|.2 a = |x.2 a| := rfl

private theorem mk_gaoSuccessorGenerator_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : Ordinal.{u}) (hβ : β < Cardinal.ord (Order.succ κ)) :
    Cardinal.mk (GaoSuccessorGenerator β) ≤ Cardinal.lift.{u + 1, u} κ := by
  let bound : Ordinal.{u} := (Ordinal.omega0 ^ β + 1) + 1
  let e : GaoIndex β ↪ Set.Iio bound :=
    ⟨fun ζ ↦ ⟨ζ.1, by
        change ζ.1 < (Ordinal.omega0 ^ β + 1) + 1
        rw [← Order.succ_eq_add_one, Order.lt_succ_iff]
        exact ζ.2⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : Set.Iio bound ↦ z.1) h)⟩
  have hβcard : β.card ≤ κ := Cardinal.card_le_iff.mpr hβ
  have hpowcard : (Ordinal.omega0 ^ β).card ≤ κ := by
    refine (Ordinal.card_opow_le Ordinal.omega0 β).trans ?_
    rw [Ordinal.card_omega0]
    exact max_le hκ (max_le hκ hβcard)
  have honeκ : (1 : Cardinal) ≤ κ := Cardinal.one_lt_aleph0.le.trans hκ
  have hboundcard : bound.card ≤ κ := by
    calc
      bound.card = (Ordinal.omega0 ^ β).card + 1 + 1 := by
        simp only [bound, Ordinal.card_add, Ordinal.card_one]
      _ ≤ κ + 1 + 1 := add_le_add (add_le_add hpowcard le_rfl) le_rfl
      _ = κ := by
        rw [Cardinal.add_eq_left hκ honeκ, Cardinal.add_eq_left hκ honeκ]
  calc
    Cardinal.mk (GaoSuccessorGenerator β) ≤ Cardinal.mk (GaoIndex β) :=
      Cardinal.mk_subtype_le _
    _ ≤ Cardinal.mk (Set.Iio bound) := Cardinal.mk_le_of_injective e.injective
    _ = Cardinal.lift.{u + 1, u} bound.card := Cardinal.mk_Iio_ordinal bound
    _ ≤ Cardinal.lift.{u + 1, u} κ := Cardinal.lift_le.mpr hboundcard

private noncomputable def gaoGeneratorEmbedding
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : Ordinal.{u}) (hβ : β < Cardinal.ord (Order.succ κ)) :
    GaoSuccessorGenerator β ↪ ULift.{u + 1, u} (Cardinal.ord κ).ToType := by
  apply Classical.choice
  rw [← Cardinal.le_def]
  change Cardinal.mk (GaoSuccessorGenerator β) ≤
    Cardinal.lift.{u + 1, u} (Cardinal.mk (Cardinal.ord κ).ToType)
  rw [Cardinal.mk_ord_toType]
  exact mk_gaoSuccessorGenerator_le κ hκ β hβ

private noncomputable def gaoComponentGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoComponent β.1 := by
  classical
  exact if h : ∃ ζ : GaoSuccessorGenerator β.1,
        gaoGeneratorEmbedding κ hκ β.1 β.2 ζ = a then
      ordinalProjection β.1 (Classical.choose h).1
    else 0

private theorem gaoComponentGenerator_embedding
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) (ζ : GaoSuccessorGenerator β.1) :
    gaoComponentGenerator κ hκ β
        (gaoGeneratorEmbedding κ hκ β.1 β.2 ζ) =
      ordinalProjection β.1 ζ.1 := by
  rw [gaoComponentGenerator, dif_pos ⟨ζ, rfl⟩]
  congr 1
  exact congrArg (fun η : GaoSuccessorGenerator β.1 ↦ η.1)
    ((gaoGeneratorEmbedding κ hκ β.1 β.2).injective
      (Classical.choose_spec
        (show ∃ η : GaoSuccessorGenerator β.1,
            gaoGeneratorEmbedding κ hκ β.1 β.2 η =
              gaoGeneratorEmbedding κ hκ β.1 β.2 ζ from ⟨ζ, rfl⟩)))

private noncomputable def gaoGlobalGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoIterationProduct κ :=
  (fun β ↦ gaoComponentGenerator κ hκ β a,
    fun b ↦ if b = a then (1 : ℝ) else 0)

private def gaoProductProjection (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoIterationProduct κ → GaoComponent β.1 := fun x ↦ x.1 β

private noncomputable def gaoProductInclusion
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoComponent β.1 → GaoIterationProduct κ := fun x ↦
  (Pi.single β x, 0)

private theorem orderConvergesTo_gaoProductProjection
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ)
    {i : Type v} [Preorder i] {f : i → GaoIterationProduct κ}
    {x : GaoIterationProduct κ} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductProjection κ β (f j))
      (gaoProductProjection κ β x) := by
  classical
  rcases hfx with ⟨τ, hτpre, hτdir, hτne, r, hranti, hrnonneg, hrglb, hbound⟩
  letI : Preorder τ := hτpre
  letI : IsDirected τ (· ≤ ·) := hτdir
  letI : Nonempty τ := hτne
  refine ⟨τ, inferInstance, inferInstance, inferInstance,
    fun k ↦ gaoProductProjection κ β (r k), ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact (hranti hkl).1 β
  · intro k
    exact (hrnonneg k).1 β
  · constructor
    · rintro _ ⟨k, rfl⟩
      exact (hrglb.1 ⟨k, rfl⟩).1 β
    · intro c hc
      let w : GaoIterationProduct κ := (Pi.single β c, 0)
      have hw : w ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        constructor
        · intro γ
          by_cases hγ : γ = β
          · subst γ
            simpa [w] using hc ⟨k, rfl⟩
          · simpa [w, hγ] using (hrnonneg k).1 γ
        · exact fun _ ↦ (hrnonneg k).2 _
      have hw0 := hrglb.2 hw
      simpa [w] using hw0.1 β
  · intro k
    exact (hbound k).mono fun j hj ↦ hj.1 β

private theorem orderConvergesTo_gaoProductInclusion
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ)
    {i : Type v} [Preorder i] {f : i → GaoComponent β.1}
    {x : GaoComponent β.1} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductInclusion κ β (f j))
      (gaoProductInclusion κ β x) := by
  classical
  rcases hfx with ⟨τ, hτpre, hτdir, hτne, r, hranti, hrnonneg, hrglb, hbound⟩
  letI : Preorder τ := hτpre
  letI : IsDirected τ (· ≤ ·) := hτdir
  letI : Nonempty τ := hτne
  refine ⟨τ, inferInstance, inferInstance, inferInstance,
    fun k ↦ gaoProductInclusion κ β (r k), ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    constructor
    · intro γ
      by_cases hγ : γ = β
      · subst γ
        simpa [gaoProductInclusion] using hranti hkl
      · simp [gaoProductInclusion, hγ]
    · exact le_rfl
  · intro k
    constructor
    · intro γ
      by_cases hγ : γ = β
      · subst γ
        simpa [gaoProductInclusion] using hrnonneg k
      · simp [gaoProductInclusion, hγ]
    · exact le_rfl
  · constructor
    · rintro _ ⟨k, rfl⟩
      constructor
      · intro γ
        by_cases hγ : γ = β
        · subst γ
          simpa [gaoProductInclusion] using hrglb.1 ⟨k, rfl⟩
        · simp [gaoProductInclusion, hγ]
      · exact le_rfl
    · intro w hw
      constructor
      · intro γ
        by_cases hγ : γ = β
        · subst γ
          apply hrglb.2
          rintro _ ⟨k, rfl⟩
          simpa [gaoProductInclusion] using (hw ⟨k, rfl⟩).1 β
        · obtain ⟨k⟩ := (inferInstance : Nonempty τ)
          simpa [gaoProductInclusion, hγ] using
            (hw ⟨k, rfl⟩).1 γ
      · intro a
        obtain ⟨k⟩ := (inferInstance : Nonempty τ)
        simpa [gaoProductInclusion] using (hw ⟨k, rfl⟩).2 a
  · intro k
    exact (hbound k).mono fun j hj ↦ by
      constructor
      · intro γ
        change |((Pi.single
            (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β (f j) -
          Pi.single (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β x) γ)| ≤
            (Pi.single (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1)
              β (r k)) γ
        by_cases hγ : γ = β
        · subst γ
          simpa only [Pi.sub_apply, Pi.single_eq_same] using hj
        · simp [hγ]
      · intro a
        change |((0 : ULift.{u + 1, u} (Cardinal.ord κ).ToType → ℝ) a - 0)| ≤ 0
        simp

private theorem gaoProductProjection_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoIterationProduct κ)) :
    gaoProductProjection κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductProjection κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductProjection κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductProjection κ β hfx⟩

private theorem gaoProductInclusion_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoComponent β.1)) :
    gaoProductInclusion κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductInclusion κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductInclusion κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductInclusion κ β hfx⟩

private noncomputable def gaoIterationSet
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) : Set (GaoIterationProduct κ) :=
  solidHull (Set.range (gaoGlobalGenerator κ hκ))

private theorem gaoComponentGenerator_mem
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    gaoComponentGenerator κ hκ β a ∈ GaoStageSet β.1 1 := by
  classical
  rw [gaoComponentGenerator]
  split
  next h =>
    let ζ := Classical.choose h
    have hζ := ζ.2
    refine ⟨ζ.1, hζ, ?_⟩
    have hnonneg : 0 ≤ ordinalProjection β.1 ζ.1 := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg]
  next h =>
    let ζ : GaoIndex β.1 := ⟨0, by simp⟩
    refine ⟨ζ, ⟨by simp [ζ], by simp [ζ, leastCNFExponent]⟩, ?_⟩
    have hnonneg : 0 ≤ ordinalProjection β.1 ζ := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    simpa using hnonneg

private theorem gaoProjection_initial
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductProjection κ β '' gaoIterationSet κ hκ ⊆ GaoStageSet β.1 1 := by
  rintro _ ⟨x, ⟨g, ⟨a, rfl⟩, hx⟩, rfl⟩
  apply isSolid_gaoStageSet β.1 1 (gaoComponentGenerator_mem κ hκ β a)
  simpa [gaoProductProjection, gaoGlobalGenerator] using hx.1 β

private theorem gaoInclusion_initial
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductInclusion κ β '' GaoStageSet β.1 1 ⊆ gaoIterationSet κ hκ := by
  classical
  rintro _ ⟨x, ⟨ζ, hζ, hx⟩, rfl⟩
  let ζ' : GaoSuccessorGenerator β.1 := ⟨ζ, hζ⟩
  let a := gaoGeneratorEmbedding κ hκ β.1 β.2 ζ'
  refine ⟨gaoGlobalGenerator κ hκ a, ⟨a, rfl⟩, ?_⟩
  constructor
  · intro γ
    rw [gaoIterationProduct_abs_fst, gaoIterationProduct_abs_fst]
    by_cases hγ : γ = β
    · subst γ
      simp only [gaoProductInclusion, gaoGlobalGenerator, Pi.single_eq_same]
      rw [gaoComponentGenerator_embedding]
      have hnonneg : 0 ≤ ordinalProjection β.1 ζ := by
        intro y
        simp only [ordinalProjection]
        split_ifs <;> norm_num
      dsimp only [ζ']
      rw [abs_of_nonneg hnonneg]
      exact hx
    · change |(Pi.single
          (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β x) γ| ≤
        |gaoComponentGenerator κ hκ γ a|
      rw [Pi.single_eq_of_ne hγ]
      simp
  · intro b
    rw [gaoIterationProduct_abs_snd, gaoIterationProduct_abs_snd]
    simp only [gaoProductInclusion, gaoGlobalGenerator, Pi.zero_apply]
    simp

private theorem gaoProjection_stage
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) : ∀ η : Ordinal.{u + 1},
    gaoProductProjection κ β ''
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η ⊆
      (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage η := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero =>
      simpa only [OrderAdherenceTower.stage_zero] using gaoProjection_initial κ hκ β
  | add_one η ih =>
      rintro _ ⟨x, hx, rfl⟩
      rw [← Order.succ_eq_add_one,
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_succ] at hx
      rw [← Order.succ_eq_add_one,
        (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage_succ]
      apply orderAdherence_mono ih
      exact gaoProductProjection_orderAdherence κ β _ ⟨x, hx, rfl⟩
  | limit η hη ih =>
      rintro _ ⟨x, hx, rfl⟩
      rw [(canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_limit η hη] at hx
      rw [(canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage_limit η hη]
      rcases Set.mem_iUnion.mp hx with ⟨δ, hxδ⟩
      apply Set.mem_iUnion.mpr
      exact ⟨δ, ih δ.1 δ.2 ⟨x, hxδ, rfl⟩⟩

private theorem gaoInclusion_stage
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) : ∀ η : Ordinal.{u + 1},
    gaoProductInclusion κ β ''
        (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage η ⊆
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero =>
      simpa only [OrderAdherenceTower.stage_zero] using gaoInclusion_initial κ hκ β
  | add_one η ih =>
      rintro _ ⟨x, hx, rfl⟩
      rw [← Order.succ_eq_add_one,
        (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage_succ] at hx
      rw [← Order.succ_eq_add_one,
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_succ]
      apply orderAdherence_mono ih
      exact gaoProductInclusion_orderAdherence κ β _ ⟨x, hx, rfl⟩
  | limit η hη ih =>
      rintro _ ⟨x, hx, rfl⟩
      rw [(canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage_limit η hη] at hx
      rw [(canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_limit η hη]
      rcases Set.mem_iUnion.mp hx with ⟨δ, hxδ⟩
      apply Set.mem_iUnion.mpr
      exact ⟨δ, ih δ.1 δ.2 ⟨x, hxδ, rfl⟩⟩

private theorem one_add_le_add_one_ordinal (δ : Ordinal.{u}) :
    1 + δ ≤ δ + 1 := by
  induction δ using Ordinal.limitRecOn with
  | zero => simp
  | add_one δ ih =>
      calc
        1 + (δ + 1) = (1 + δ) + 1 := (add_assoc 1 δ 1).symm
        _ ≤ (δ + 1) + 1 := by
          simpa only [Order.succ_eq_add_one] using Order.succ_le_succ ih
  | limit δ hδ ih =>
      rw [Ordinal.one_add_of_omega0_le (Ordinal.omega0_le_of_isSuccLimit hδ)]
      exact le_self_add

private theorem gaoIterationTower_strict
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∀ η < Ordinal.lift.{u + 1, u} (Cardinal.ord (Order.succ κ)),
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η ⊂
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage (Order.succ η) := by
  classical
  intro η hη
  obtain ⟨δ, hδ, hδη⟩ := Ordinal.lt_lift_iff.mp hη
  have hκsucc : Cardinal.aleph0 ≤ Order.succ κ := hκ.trans (Order.le_succ κ)
  have hlimit := Cardinal.isSuccLimit_ord hκsucc
  let β : GaoComponentIndex κ := ⟨Order.succ δ, hlimit.succ_lt hδ⟩
  let C := canonicalOrderAdherenceTower (GaoStageSet β.1 1)
  have hδβ : δ ≤ β.1 := by
    dsimp only [β]
    exact Order.le_succ δ
  have hδoneβ : δ + 1 ≤ β.1 := by
    dsimp only [β]
    rw [Order.succ_eq_add_one]
  have hgamma : 1 + δ ≤ β.1 :=
    (one_add_le_add_one_ordinal δ).trans hδoneβ
  obtain ⟨ζ, hζnext, hζprev⟩ := ordinalProjection_strict_stage β.1 (1 + δ) hgamma
  let p := ordinalProjection β.1 ζ
  have hCδ := gao_orderAdherence_stage_formula β.1 C δ hδβ
  have hCnext := gao_orderAdherence_stage_formula β.1 C (δ + 1) hδoneβ
  have hpCnext : p ∈ C.stage (Ordinal.lift.{u + 1, u} (δ + 1)) := by
    rw [hCnext]
    simpa only [p, add_assoc] using hζnext
  have hpCprev : p ∉ C.stage (Ordinal.lift.{u + 1, u} δ) := by
    rw [hCδ]
    exact hζprev
  have hliftnext : Ordinal.lift.{u + 1, u} (δ + 1) = Order.succ η := by
    rw [← Order.succ_eq_add_one, Ordinal.lift_succ, hδη]
  let q := gaoProductInclusion κ β p
  have hqnext : q ∈
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage (Order.succ η) := by
    rw [← hliftnext]
    exact gaoInclusion_stage κ hκ β _ ⟨p, hpCnext, rfl⟩
  have hqprev : q ∉
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η := by
    intro hq
    have hproj := gaoProjection_stage κ hκ β η ⟨q, hq, rfl⟩
    have hp : p ∈ C.stage η := by
      simpa [q, gaoProductProjection, gaoProductInclusion] using hproj
    rw [← hδη] at hp
    exact hpCprev hp
  rw [Set.ssubset_iff_exists]
  refine ⟨?_, q, hqnext, hqprev⟩
  intro x hx
  rw [(canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_succ]
  exact subset_orderAdherence _ hx

private theorem gaoGlobalGenerator_index_eq_of_abs_le
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {a b : ULift.{u + 1, u} (Cardinal.ord κ).ToType}
    (hab : |gaoGlobalGenerator κ hκ a| ≤ |gaoGlobalGenerator κ hκ b|) :
    a = b := by
  classical
  by_contra hne
  have h := hab.2 a
  rw [gaoIterationProduct_abs_snd, gaoIterationProduct_abs_snd] at h
  simp [gaoGlobalGenerator, hne] at h
  norm_num at h

private theorem gaoGlobalGenerator_injective
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Function.Injective (gaoGlobalGenerator κ hκ) := by
  intro a b hab
  apply gaoGlobalGenerator_index_eq_of_abs_le κ hκ
  rw [hab]

private theorem mk_gaoGlobalGenerator_range
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) =
      Cardinal.lift.{u + 1, u} κ := by
  calc
    Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) =
        Cardinal.mk (ULift.{u + 1, u} (Cardinal.ord κ).ToType) :=
      Cardinal.mk_range_eq _ (gaoGlobalGenerator_injective κ hκ)
    _ = Cardinal.lift.{u + 1, u} κ := by
      change Cardinal.lift.{u + 1, u}
        (Cardinal.mk (Cardinal.ord κ).ToType) = Cardinal.lift.{u + 1, u} κ
      rw [Cardinal.mk_ord_toType]

private theorem solidGeneratorNumber_gaoIterationSet
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    solidGeneratorNumber (gaoIterationSet κ hκ) = Cardinal.lift.{u + 1, u} κ := by
  classical
  apply le_antisymm
  · calc
      solidGeneratorNumber (gaoIterationSet κ hκ) ≤
          Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) := by
        apply csInf_le'
        exact ⟨Set.range (gaoGlobalGenerator κ hκ), rfl, rfl⟩
      _ = Cardinal.lift.{u + 1, u} κ := mk_gaoGlobalGenerator_range κ hκ
  · apply le_csInf
    · exact ⟨Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)),
        Set.range (gaoGlobalGenerator κ hκ), rfl, rfl⟩
    · intro c hc
      rcases hc with ⟨A, hAc, hAS⟩
      rw [← hAc]
      have hbelow : ∀ a : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
          ∃ x : A, |gaoGlobalGenerator κ hκ a| ≤ |x.1| := by
        intro a
        have hgenS : gaoGlobalGenerator κ hκ a ∈ solidHull A := by
          rw [hAS]
          exact ⟨gaoGlobalGenerator κ hκ a, ⟨a, rfl⟩, le_rfl⟩
        rcases hgenS with ⟨x, hxA, hax⟩
        exact ⟨⟨x, hxA⟩, hax⟩
      choose x hx using hbelow
      have habove : ∀ a : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
          ∃ b : ULift.{u + 1, u} (Cardinal.ord κ).ToType,
            |(x a).1| ≤ |gaoGlobalGenerator κ hκ b| := by
        intro a
        have hxS : (x a).1 ∈ gaoIterationSet κ hκ := by
          rw [← hAS]
          exact ⟨(x a).1, (x a).2, le_rfl⟩
        rcases hxS with ⟨g, ⟨b, rfl⟩, hxb⟩
        exact ⟨b, hxb⟩
      choose b hb using habove
      have hxinj : Function.Injective x := by
        intro a a' haa'
        have hab' : |gaoGlobalGenerator κ hκ a| ≤
            |gaoGlobalGenerator κ hκ (b a')| := by
          calc
            |gaoGlobalGenerator κ hκ a| ≤ |(x a).1| := hx a
            _ = |(x a').1| := by rw [haa']
            _ ≤ |gaoGlobalGenerator κ hκ (b a')| := hb a'
        have ha'b : a' = b a' :=
          gaoGlobalGenerator_index_eq_of_abs_le κ hκ ((hx a').trans (hb a'))
        exact (gaoGlobalGenerator_index_eq_of_abs_le κ hκ hab').trans ha'b.symm
      calc
        Cardinal.lift.{u + 1, u} κ =
            Cardinal.mk (ULift.{u + 1, u} (Cardinal.ord κ).ToType) := by
          change Cardinal.lift.{u + 1, u} κ = Cardinal.lift.{u + 1, u}
            (Cardinal.mk (Cardinal.ord κ).ToType)
          rw [Cardinal.mk_ord_toType]
        _ ≤ Cardinal.mk A := Cardinal.mk_le_of_injective hxinj

theorem solid_sets_require_arbitrarily_many_iterations
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (ξ : Ordinal.{u})
    (hξ : ξ ≤ Cardinal.ord (Order.succ κ)) :
    ∃ (X : Type (u + 1)) (_ : AddCommGroup X) (_ : Lattice X)
      (_ : IsOrderedAddMonoid X) (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.lift.{u + 1, u} κ ∧
          NeedsOrderAdherenceIterations S (Ordinal.lift.{u + 1, u} ξ) := by
  let S := gaoIterationSet κ hκ
  refine ⟨GaoIterationProduct κ, inferInstance, inferInstance, inferInstance,
    inferInstance, S, LatticeOrderedAddCommGroup.isSolid_solidClosure _,
    solidGeneratorNumber_gaoIterationSet κ hκ, ?_⟩
  refine ⟨canonicalOrderAdherenceTower S, ?_⟩
  intro η hη
  exact gaoIterationTower_strict κ hκ η
    (hη.trans_le (Ordinal.lift_le.mpr hξ))

private theorem orderConvergesTo_zero_of_abs_le_gao
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    {i : Type v} [Preorder i] {f g : i → X}
    (hg : OrderConvergesTo g 0) (hfg : ∀ j, |f j| ≤ |g j|) :
    OrderConvergesTo f 0 := by
  rcases hg with ⟨k, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, hbound⟩
  refine ⟨k, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, ?_⟩
  intro l
  exact (hbound l).mono fun j hj ↦ by
    simpa only [sub_zero] using (hfg j).trans (by simpa only [sub_zero] using hj)

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
  ext x
  constructor
  · rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    letI : Preorder ι := hpre
    letI : IsDirected ι (· ≤ ·) := hdir
    letI : Nonempty ι := hne
    rcases hfx with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
    letI : Preorder κ := hκpre
    letI : IsDirected κ (· ≤ ·) := hκdir
    letI : Nonempty κ := hκne
    let y : κ → X := fun k ↦ (|x| - r k)⁺
    have hy_mono : Monotone y := fun _ _ hkl ↦
      posPart_mono (sub_le_sub_left (hranti hkl) |x|)
    have hy_lub : IsLUB (Set.range y) |x| := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact show (|x| - r k) ⊔ 0 ≤ |x| from
          sup_le (sub_le_self _ (hrnonneg k)) (abs_nonneg _)
      · intro c hc
        have hlow : |x| - c ∈ lowerBounds (Set.range r) := by
          rintro _ ⟨k, rfl⟩
          have hraw : |x| - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
          exact sub_le_iff_le_add.mpr (by
            simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
        exact sub_nonpos.mp (hrglb.2 hlow)
    have hyG : ∀ k, ∃ a ∈ G, y k ≤ a := by
      intro k
      obtain ⟨i, hi⟩ := (hbound k).exists
      rcases hf i with ⟨a, haG, hfa⟩
      have hx_le : |x| ≤ |f i| + r k := by
        calc
          |x| = |(x - f i) + f i| := by congr 1; abel
          _ ≤ |x - f i| + |f i| := abs_add_le _ _
          _ = |f i| + |x - f i| := add_comm _ _
          _ ≤ |f i| + r k := add_le_add_right (by
            simpa [abs_sub_comm] using hi) _
      have hsub : |x| - r k ≤ |f i| := sub_le_iff_le_add.mpr hx_le
      have hyf : y k ≤ |f i| :=
        show (|x| - r k) ⊔ 0 ≤ |f i| from sup_le hsub (abs_nonneg _)
      exact ⟨a, haG, hyf.trans (by simpa [abs_of_nonneg (hG haG)] using hfa)⟩
    choose a haG hya using hyG
    let q : κ → X := fun k ↦ |x| ⊓ a k
    have hy_order : OrderConvergesTo y |x| :=
      orderConvergesTo_of_monotone_isLUB hy_mono hy_lub
    have hq_order : OrderConvergesTo q |x| := by
      have hzero : OrderConvergesTo (fun k ↦ q k - |x|) 0 := by
        have hbase : OrderConvergesTo (fun k ↦ y k - |x|) 0 := by
          simpa using hy_order.sub (orderConvergesTo_const |x|)
        apply orderConvergesTo_zero_of_abs_le_gao hbase
        intro k
        dsimp [q]
        have hyx : y k ≤ |x| := hy_lub.1 ⟨k, rfl⟩
        have hyq : y k ≤ |x| ⊓ a k := le_inf hyx (hya k)
        rw [abs_of_nonpos (sub_nonpos.mpr inf_le_left),
          abs_of_nonpos (sub_nonpos.mpr hyx)]
        exact neg_le_neg (sub_le_sub_right hyq |x|)
      have := hzero.add (orderConvergesTo_const (ι := κ) |x|)
      simpa [q] using this
    have hq_lub : IsLUB (Set.range q) |x| := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact inf_le_left
      · intro c hc
        apply hy_lub.2
        rintro _ ⟨k, rfl⟩
        exact (le_inf (hy_lub.1 ⟨k, rfl⟩) (hya k)).trans (hc ⟨k, rfl⟩)
    exact ⟨κ, inferInstance, inferInstance, inferInstance, a, haG, hq_order, hq_lub⟩
  · rintro ⟨ι, hpre, hdir, hne, a, haG, hq_order, _hq_lub⟩
    letI : Preorder ι := hpre
    letI : IsDirected ι (· ≤ ·) := hdir
    letI : Nonempty ι := hne
    let c : ι → X := fun i ↦ (x ⊓ a i) ⊔ (-a i)
    have hc_mem : ∀ i, c i ∈ solidHull G := by
      intro i
      refine ⟨a i, haG i, ?_⟩
      dsimp [c]
      have hai : 0 ≤ a i := hG (haG i)
      change |(x ⊓ a i) ⊔ -a i| ≤ |a i|
      llarith
    have hc_order : OrderConvergesTo c x := by
      have hzero : OrderConvergesTo (fun i ↦ c i - x) 0 := by
        have hbase : OrderConvergesTo (fun i ↦ (|x| ⊓ a i) - |x|) 0 := by
          simpa using hq_order.sub (orderConvergesTo_const |x|)
        apply orderConvergesTo_zero_of_abs_le_gao hbase
        intro i
        dsimp [c]
        have hai : 0 ≤ a i := hG (haG i)
        change |((x ⊓ a i) ⊔ (-a i)) - x| ≤ abs ((|x| ⊓ a i) - |x|)
        llarith
      have := hzero.add (orderConvergesTo_const (ι := ι) x)
      simpa [c] using this
    exact ⟨ι, inferInstance, inferInstance, inferInstance, c, hc_mem, hc_order⟩

end OrdinalConstruction

end OrderClosures
