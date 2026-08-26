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
    {A B : Set X} (_hA : LatticeOrderedAddCommGroup.IsSolid A)
    (_hB : LatticeOrderedAddCommGroup.IsSolid B) {c : ℝ} (hc : 0 < c) :
    (A ⊆ B → ∀ m, iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m) ∧
      (orderAdherence (scaleSet c A) = scaleSet c (orderAdherence A) ∧
        ∀ m, iteratedOrderAdherence (scaleSet c A) m =
          scaleSet c (iteratedOrderAdherence A m)) := by
  have hmono : A ⊆ B → ∀ m,
      iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m := by
    intro hAB m
    induction m with
    | zero => exact hAB
    | succ m ih => exact orderAdherence_mono ih
  have hscale : ∀ C : Set X,
      orderAdherence (scaleSet c C) = scaleSet c (orderAdherence C) := by
    intro C
    apply Set.Subset.antisymm
    · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
      letI : Preorder ι := hpre
      letI : IsDirected ι (· ≤ ·) := hdir
      letI : Nonempty ι := hne
      refine ⟨c⁻¹ • x, ?_, by simp [smul_smul, hc.ne']⟩
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c⁻¹ • f i, ?_, ?_⟩
      · intro i
        rcases hf i with ⟨a, ha, hfa⟩
        change c⁻¹ • f i ∈ C
        rw [← hfa]
        simpa [smul_smul, hc.ne'] using ha
      · exact hfx.smul c⁻¹
    · rintro x ⟨y, ⟨ι, hpre, hdir, hne, f, hf, hfy⟩, rfl⟩
      letI : Preorder ι := hpre
      letI : IsDirected ι (· ≤ ·) := hdir
      letI : Nonempty ι := hne
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c • f i, ?_, hfy.smul c⟩
      exact fun i ↦ ⟨f i, hf i, rfl⟩
  have hiter : ∀ m, iteratedOrderAdherence (scaleSet c A) m =
      scaleSet c (iteratedOrderAdherence A m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simpa only [iteratedOrderAdherence, ih] using
          hscale (iteratedOrderAdherence A m)
  exact ⟨hmono, hscale A, hiter⟩

/-- Paper Lemma `lem:fatou-order`, part (a). -/
theorem weakFatou_iterated_unitBall
    (p : PaperLatticeNorm X) {K : ℝ} (hK : HasWeakFatouProperty p K) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m ⊆
      scaleSet (K ^ m) (unitBallFor p) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK.1
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) ⊆ scaleSet K (unitBallFor p) := by
    rw [orderAdherence_eq_solidOrderAdherence hsolid]
    rintro x ⟨z, hz, hxz⟩
    rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
    letI : Nonempty B := hBne.to_subtype
    letI : IsDirectedOrder B := hBdir.isDirectedOrder
    let f : B → X := fun b ↦ b.1
    have hfmono : Monotone f := fun _ _ h ↦ h
    have hfrange : Set.range f = B := by
      ext y
      simp [f]
    have hpz : p z ≤ K := by
      have h := hK.2 f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub) 1
        (fun b ↦ hB b.2 |>.1)
      simpa using h
    have hpx : p x ≤ K := (p.solid hxz).trans hpz
    refine ⟨K⁻¹ • x, ?_, by simp [smul_smul, hKpos.ne']⟩
    change p (K⁻¹ • x) ≤ 1
    rw [p.smul, abs_of_pos (inv_pos.mpr hKpos)]
    calc
      K⁻¹ * p x ≤ K⁻¹ * K :=
        mul_le_mul_of_nonneg_left hpx (inv_nonneg.mpr hKpos.le)
      _ = 1 := inv_mul_cancel₀ hKpos.ne'
  intro m
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro _
      by_cases hm0 : m = 0
      · subst m
        simpa [iteratedOrderAdherence] using hstep
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hpowpos : 0 < K ^ m := pow_pos hKpos m
        have hscale :=
          (iteratedOrderAdherence_mono_and_scale hsolid hsolid hpowpos).2.1
        intro x hx
        change x ∈ orderAdherence (iteratedOrderAdherence (unitBallFor p) m) at hx
        have hxscaled : x ∈ orderAdherence (scaleSet (K ^ m) (unitBallFor p)) :=
          orderAdherence_mono (ih hm1) hx
        rw [hscale] at hxscaled
        rcases hxscaled with ⟨y, hy, hyx⟩
        rcases hstep hy with ⟨z, hz, hzy⟩
        refine ⟨z, hz, ?_⟩
        calc
          K ^ (m + 1) • z = K ^ m • (K • z) := by rw [pow_succ, mul_smul]
          _ = K ^ m • y := congrArg (fun w ↦ K ^ m • w) hzy
          _ = x := hyx

/-- Paper Lemma `lem:fatou-order`, part (b). -/
theorem fatou_iterated_unitBall
    (p : PaperLatticeNorm X) (hp : HasFatouProperty p) :
    ∀ m ≥ 1, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
  have hsolid : LatticeOrderedAddCommGroup.IsSolid (unitBallFor p) := by
    intro y hy x hxy
    exact (p.solid hxy).trans hy
  have hstep : orderAdherence (unitBallFor p) = unitBallFor p := by
    apply Set.Subset.antisymm
    · rw [orderAdherence_eq_solidOrderAdherence hsolid]
      rintro x ⟨z, hz, hxz⟩
      rcases hz with ⟨hz0, B, hB, hBne, hBdir, hBlub⟩
      letI : Nonempty B := hBne.to_subtype
      letI : IsDirectedOrder B := hBdir.isDirectedOrder
      let f : B → X := fun b ↦ b.1
      have hfmono : Monotone f := fun _ _ h ↦ h
      have hfrange : Set.range f = B := by
        ext y
        simp [f]
      have hpnorm := hp f z hfmono (fun b ↦ (hB b.2).2)
        (by simpa [hfrange] using hBlub)
      have hpz : p z ≤ 1 := hpnorm.2 (by
        rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
        exact (hB b.2).1)
      exact (p.solid hxz).trans hpz
    · exact subset_orderAdherence (unitBallFor p)
  have hall : ∀ m, iteratedOrderAdherence (unitBallFor p) m = unitBallFor p := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [iteratedOrderAdherence]
        rw [ih, hstep]
  exact fun m _ ↦ hall m

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

private theorem weakNakano_of_weakSequentialNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K := by
  refine ⟨hseq.1, ?_⟩
  intro A hApos hAdir hAbdd hAnorm ε hε
  classical
  by_cases hAempty : A = ∅
  · subst A
    refine ⟨0, le_rfl, ?_, ?_⟩
    · simp
    · norm_num
      linarith [hseq.1]
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  letI : Nonempty ↥A := ⟨⟨Classical.choose hAne, Classical.choose_spec hAne⟩⟩
  letI : TopologicalSpace.SeparableSpace ↥A := inferInstance
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq ↥A
  let join : ↥A → ↥A → ↥A := fun a b ↦
    ⟨Classical.choose (hAdir a.1 a.2 b.1 b.2),
      (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).1⟩
  have hjoin_left (a b : ↥A) : a.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.1
  have hjoin_right (a b : ↥A) : b.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.2
  let z : ℕ → ↥A := fun m ↦
    Nat.rec (d 0) (fun k a ↦ join a (d (k + 1))) m
  have hz_succ (m : ℕ) : z (m + 1) = join (z m) (d (m + 1)) := by
    simp [z]
  have hzmono : Monotone (fun m ↦ (z m).1) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [hz_succ]
    exact hjoin_left _ _
  have hd_le_z : ∀ m, (d m).1 ≤ (z m).1 := by
    intro m
    cases m with
    | zero => simp [z]
    | succ m =>
        rw [hz_succ]
        exact hjoin_right _ _
  have hzpos : ∀ m, 0 ≤ (z m).1 := fun m ↦ hApos (z m).2
  have hzbdd : BddAbove (Set.range fun m ↦ (z m).1) := by
    rcases hAbdd with ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨m, rfl⟩; exact hb (z m).2⟩
  have hznorm : ∀ m, ‖(z m).1‖ ≤ 1 := fun m ↦ hAnorm _ (z m).2
  obtain ⟨y, hypos, hyupper, hynorm⟩ :=
    hseq.2 (fun m ↦ (z m).1) hzmono hzpos hzbdd hznorm ε hε
  refine ⟨y, hypos, ?_, hynorm⟩
  have hd_upper : ∀ m, (d m).1 ≤ y :=
    fun m ↦ (hd_le_z m).trans (hyupper m)
  have hclosed : IsClosed {a : ↥A | a.1 ≤ y} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hclosure : closure (Set.range d) ⊆ {a : ↥A | a.1 ≤ y} := by
    apply closure_minimal
    · rintro _ ⟨m, rfl⟩
      exact hd_upper m
    · exact hclosed
  intro x hx
  let xA : ↥A := ⟨x, hx⟩
  exact hclosure (by rw [hdense.closure_eq]; exact Set.mem_univ xA)

private theorem weakFatou_of_weakNakano_norm
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) norm K) :
    HasWeakFatouProperty (norm : Y → ℝ) K := by
  refine ⟨hNak.1, ?_⟩
  intro ι _ _ _ f x hfmono hfpos hflub c hfc
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hc : 0 ≤ c := (norm_nonneg (f i₀)).trans (hfc i₀)
  by_cases hc0 : c = 0
  · subst c
    have hfzero : ∀ i, f i = 0 := by
      intro i
      exact norm_eq_zero.mp (le_antisymm (hfc i) (norm_nonneg _))
    have hxzero : x = 0 := by
      apply le_antisymm
      · apply hflub.2
        rintro _ ⟨i, rfl⟩
        simp [hfzero i]
      · simpa [hfzero i₀] using hflub.1 ⟨i₀, rfl⟩
    simp [hxzero]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let A : Set Y := Set.range fun i ↦ c⁻¹ • f i
  have hApos : A ⊆ Set.Ici 0 := by
    rintro _ ⟨i, rfl⟩
    exact smul_nonneg (inv_nonneg.mpr hc) (hfpos i)
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨c⁻¹ • f k, ⟨k, rfl⟩, ?_, ?_⟩
    · exact smul_le_smul_of_nonneg_left (hfmono hik) (inv_nonneg.mpr hc)
    · exact smul_le_smul_of_nonneg_left (hfmono hjk) (inv_nonneg.mpr hc)
  have hAbdd : BddAbove A := by
    refine ⟨c⁻¹ • x, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact smul_le_smul_of_nonneg_left (hflub.1 ⟨i, rfl⟩) (inv_nonneg.mpr hc)
  have hAnorm : ∀ z ∈ A, ‖z‖ ≤ 1 := by
    rintro _ ⟨i, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    have hi := hfc i
    rw [inv_mul_le_one₀ hcpos]
    exact hi
  obtain ⟨y, hypos, hyupper, hynorm⟩ :=
    hNak.2 A hApos hAdir hAbdd hAnorm (δ / c) (div_pos hδ hcpos)
  have hxy : x ≤ c • y := by
    apply hflub.2
    rintro _ ⟨i, rfl⟩
    have hi := hyupper (c⁻¹ • f i) ⟨i, rfl⟩
    have := smul_le_smul_of_nonneg_left hi hc
    simpa [smul_smul, hc0] using this
  have hxpos : 0 ≤ x := (hfpos i₀).trans (hflub.1 ⟨i₀, rfl⟩)
  have hcyp : 0 ≤ c • y := smul_nonneg hc hypos
  have hnormxy : ‖x‖ ≤ ‖c • y‖ := by
    apply norm_le_norm_of_abs_le_abs
    simpa [abs_of_nonneg hxpos, abs_of_nonneg hcyp] using hxy
  calc
    ‖x‖ ≤ ‖c • y‖ := hnormxy
    _ = c * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    _ ≤ c * (K + δ / c) := mul_le_mul_of_nonneg_left hynorm hc
    _ = K * c + δ := by field_simp

/-- Paper Proposition `prop:separable-reduction`. -/
theorem separable_weakSequentialNakano_implies_weakNakano
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    {K : ℝ} (_hK : 1 ≤ K)
    (hseq : IsWeakSequentialNakanoConstant (X := Y) norm K) :
    IsWeakNakanoConstant (X := Y) norm K ∧
      HasWeakFatouProperty (norm : Y → ℝ) K := by
  have hNak := weakNakano_of_weakSequentialNakano hseq
  exact ⟨hNak, weakFatou_of_weakNakano_norm hNak⟩

private theorem weakNakano_of_weakSequentialNakano_p
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] [TopologicalSpace.SeparableSpace Y]
    (p : PaperLatticeNorm Y) {K : ℝ}
    (hseq : IsWeakSequentialNakanoConstant (X := Y) p K) :
    IsWeakNakanoConstant (X := Y) p K := by
  refine ⟨hseq.1, ?_⟩
  intro A hApos hAdir hAbdd hAp ε hε
  classical
  by_cases hAempty : A = ∅
  · subst A
    refine ⟨0, le_rfl, by simp, ?_⟩
    rw [show p 0 = 0 from p.eq_zero_iff 0 |>.2 rfl]
    linarith [hseq.1]
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  letI : Nonempty ↥A := ⟨⟨Classical.choose hAne, Classical.choose_spec hAne⟩⟩
  letI : TopologicalSpace.SeparableSpace ↥A := inferInstance
  obtain ⟨d, hdense⟩ := TopologicalSpace.exists_dense_seq ↥A
  let join : ↥A → ↥A → ↥A := fun a b ↦
    ⟨Classical.choose (hAdir a.1 a.2 b.1 b.2),
      (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).1⟩
  have hjoin_left (a b : ↥A) : a.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.1
  have hjoin_right (a b : ↥A) : b.1 ≤ (join a b).1 :=
    (Classical.choose_spec (hAdir a.1 a.2 b.1 b.2)).2.2
  let z : ℕ → ↥A := fun m ↦
    Nat.rec (d 0) (fun k a ↦ join a (d (k + 1))) m
  have hz_succ (m : ℕ) : z (m + 1) = join (z m) (d (m + 1)) := by simp [z]
  have hzmono : Monotone (fun m ↦ (z m).1) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [hz_succ]
    exact hjoin_left _ _
  have hd_le_z : ∀ m, (d m).1 ≤ (z m).1 := by
    intro m
    cases m with
    | zero => simp [z]
    | succ m => rw [hz_succ]; exact hjoin_right _ _
  have hzpos : ∀ m, 0 ≤ (z m).1 := fun m ↦ hApos (z m).2
  have hzbdd : BddAbove (Set.range fun m ↦ (z m).1) := by
    rcases hAbdd with ⟨b, hb⟩
    exact ⟨b, by rintro _ ⟨m, rfl⟩; exact hb (z m).2⟩
  have hzp : ∀ m, p (z m).1 ≤ 1 := fun m ↦ hAp _ (z m).2
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hseq.2 (fun m ↦ (z m).1) hzmono hzpos hzbdd hzp ε hε
  refine ⟨y, hypos, ?_, hyp⟩
  have hd_upper : ∀ m, (d m).1 ≤ y := fun m ↦ (hd_le_z m).trans (hyupper m)
  have hclosed : IsClosed {a : ↥A | a.1 ≤ y} :=
    isClosed_Iic.preimage continuous_subtype_val
  have hclosure : closure (Set.range d) ⊆ {a : ↥A | a.1 ≤ y} := by
    apply closure_minimal
    · rintro _ ⟨m, rfl⟩
      exact hd_upper m
    · exact hclosed
  intro q hq
  exact hclosure (by rw [hdense.closure_eq]; exact Set.mem_univ ⟨q, hq⟩)

private theorem weakFatou_of_weakNakano_p
    {Y : Type u} [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (p : PaperLatticeNorm Y) {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) p K) :
    HasWeakFatouProperty p K := by
  refine ⟨hNak.1, ?_⟩
  intro ι _ _ _ f x hfmono hfpos hflub c hfc
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hc : 0 ≤ c := (p.nonneg (f i₀)).trans (hfc i₀)
  by_cases hc0 : c = 0
  · subst c
    have hfzero : ∀ i, f i = 0 := by
      intro i
      apply p.eq_zero_iff (f i) |>.1
      exact le_antisymm (hfc i) (p.nonneg _)
    have hxzero : x = 0 := by
      apply le_antisymm
      · apply hflub.2
        rintro _ ⟨i, rfl⟩
        simp [hfzero i]
      · simpa [hfzero i₀] using hflub.1 ⟨i₀, rfl⟩
    rw [hxzero]
    rw [p.eq_zero_iff 0 |>.2 rfl]
    simp
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let A : Set Y := Set.range fun i ↦ c⁻¹ • f i
  have hApos : A ⊆ Set.Ici 0 := by
    rintro _ ⟨i, rfl⟩
    exact smul_nonneg (inv_nonneg.mpr hc) (hfpos i)
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨c⁻¹ • f k, ⟨k, rfl⟩, ?_, ?_⟩
    · exact smul_le_smul_of_nonneg_left (hfmono hik) (inv_nonneg.mpr hc)
    · exact smul_le_smul_of_nonneg_left (hfmono hjk) (inv_nonneg.mpr hc)
  have hAbdd : BddAbove A := by
    refine ⟨c⁻¹ • x, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact smul_le_smul_of_nonneg_left (hflub.1 ⟨i, rfl⟩) (inv_nonneg.mpr hc)
  have hAp : ∀ z ∈ A, p z ≤ 1 := by
    rintro _ ⟨i, rfl⟩
    rw [p.smul, abs_of_pos (inv_pos.mpr hcpos), inv_mul_le_one₀ hcpos]
    exact hfc i
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hNak.2 A hApos hAdir hAbdd hAp (δ / c) (div_pos hδ hcpos)
  have hxy : x ≤ c • y := by
    apply hflub.2
    rintro _ ⟨i, rfl⟩
    have hi := hyupper (c⁻¹ • f i) ⟨i, rfl⟩
    have := smul_le_smul_of_nonneg_left hi hc
    simpa [smul_smul, hc0] using this
  have hxpos : 0 ≤ x := (hfpos i₀).trans (hflub.1 ⟨i₀, rfl⟩)
  have hcyp : 0 ≤ c • y := smul_nonneg hc hypos
  have hpxy : p x ≤ p (c • y) := by
    apply p.solid
    simpa [abs_of_nonneg hxpos, abs_of_nonneg hcyp] using hxy
  calc
    p x ≤ p (c • y) := hpxy
    _ = c * p y := by rw [p.smul, abs_of_pos hcpos]
    _ ≤ c * (K + δ / c) := mul_le_mul_of_nonneg_left hyp hc
    _ = K * c + δ := by field_simp

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
    simpa [level] using h⟩

/-- The parent map, fixing the root. -/
def parent {n : ℕ} (t : TreeNode n) : TreeNode n :=
  ⟨t.1.dropLast, by
    rw [List.length_dropLast]
    exact (Nat.sub_le _ _).trans t.2⟩

/-- Restriction `t|j`. -/
def restrict {n : ℕ} (t : TreeNode n) (j : ℕ) : TreeNode n :=
  ⟨t.1.take j, by
    rw [List.length_take]
    exact (min_le_right _ _).trans t.2⟩

end TreeNode

/-- Non-terminal nodes `H_n`. -/
def TreeNonterminal (n : ℕ) := {t : TreeNode n // TreeNode.level t < n}

/-- The product space `I_n = ℕ^{H_n}`. -/
abbrev TreeProduct (n : ℕ) := TreeNonterminal n → ℕ

/-- The strict prefix `t|j`, regarded as a non-terminal node. -/
def strictPrefix {n : ℕ} (t : TreeNode n) (j : Fin (TreeNode.level t)) :
    TreeNonterminal n :=
  ⟨TreeNode.restrict t j, by
    calc
      (TreeNode.restrict t j).level ≤ j := List.length_take_le _ _
      _ < TreeNode.level t := j.isLt
      _ ≤ n := t.2⟩

/-- The cylinder `E_t`. -/
def treeCylinder (n : ℕ) (t : TreeNode n) : Set (TreeProduct n) :=
  {α | ∀ j : Fin (TreeNode.level t), α (strictPrefix t j) ≤ t.1.get j}

private theorem mem_treeCylinder_child_iff
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) (m : ℕ)
    (α : TreeProduct n) :
    α ∈ treeCylinder n (TreeNode.child t ht m) ↔
      α ∈ treeCylinder n t ∧ α ⟨t, ht⟩ ≤ m := by
  constructor
  · intro h
    constructor
    · intro j
      let j' : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨j, by simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j' = strictPrefix t j := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length j.isLt.le
      have hget : (TreeNode.child t ht m).1.get j' = t.1.get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left j.isLt
      rw [hpref, hget] at hj
      exact hj
    · let j : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j
      have hpref : strictPrefix (TreeNode.child t ht m) j = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [j, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get j = m := by
        simp [j, TreeNode.level, TreeNode.child]
      rw [hpref, hget] at hj
      exact hj
  · rintro ⟨h, hlast⟩ j
    by_cases hj : (j : ℕ) < TreeNode.level t
    · let j' : Fin (TreeNode.level t) := ⟨j, hj⟩
      have hprefix := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j = strictPrefix t j' := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length hj.le
      have hget : (TreeNode.child t ht m).1.get j = t.1.get j' := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hj
      rw [hpref, hget]
      exact hprefix
    · have hjeq : (j : ℕ) = TreeNode.level t := by
        have hjlt : (j : ℕ) < TreeNode.level t + 1 := by
          simpa [TreeNode.level, TreeNode.child] using j.isLt
        omega
      let jlast : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hjlast : j = jlast := Fin.ext hjeq
      rw [hjlast]
      have hpref : strictPrefix (TreeNode.child t ht m) jlast = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [jlast, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get jlast = m := by
        simp [jlast, TreeNode.level, TreeNode.child]
      rw [hpref, hget]
      exact hlast

/-- Paper Lemma `lem:basic-tree`, part (a). -/
theorem treeCylinder_isClopen (n : ℕ) (t : TreeNode n) :
    IsClopen (treeCylinder n t) := by
  rw [show treeCylinder n t =
      ⋂ j : Fin (TreeNode.level t),
        {α | α (strictPrefix t j) ≤ t.1.get j} by
    ext α
    simp [treeCylinder]]
  apply isClopen_iInter_of_finite
  intro j
  exact (isClopen_discrete {m : ℕ | m ≤ t.1.get j}).preimage
    (continuous_apply (strictPrefix t j))

/-- The characteristic function `s_t = χ_{E_t}`. -/
noncomputable def treeFunction (n : ℕ) (t : TreeNode n) :
    BoundedContinuousFunction (TreeProduct n) ℝ :=
  BoundedContinuousFunction.indicator (treeCylinder n t) (treeCylinder_isClopen n t)

private theorem treeFunction_apply_of_mem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∈ treeCylinder n t) : treeFunction n t α = 1 := by
  classical
  simp [treeFunction, BoundedContinuousFunction.indicator, Set.indicator, hα]

private theorem treeFunction_apply_of_notMem (n : ℕ) (t : TreeNode n)
    {α : TreeProduct n} (hα : α ∉ treeCylinder n t) : treeFunction n t α = 0 := by
  classical
  simp [treeFunction, BoundedContinuousFunction.indicator, Set.indicator, hα]

/-- BanLat's vector-lattice structure is supplied here for real-valued bounded
continuous functions; all non-proof data comes from Mathlib's pointwise instances. -/
noncomputable instance boundedContinuousFunctionNormedVectorLattice
    (A : Type u) [TopologicalSpace A] :
    NormedVectorLattice (BoundedContinuousFunction A ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g h p
    exact mul_le_mul_of_nonneg_left (h p) ha

/-- Paper Lemma `lem:basic-tree`, parts (b) and (c). -/
theorem treeFunction_child_properties
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) :
    (∀ m, treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t ∧
      treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t) ∧
    Monotone (fun m ↦ treeFunction n (TreeNode.child t ht m)) ∧
      IsLUB (Set.range fun m ↦ treeFunction n (TreeNode.child t ht m))
        (treeFunction n t) := by
  have hnonneg : ∀ u : TreeNode n, 0 ≤ treeFunction n u := by
    intro u α
    change 0 ≤ treeFunction n u α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα]
      norm_num
    · rw [treeFunction_apply_of_notMem n u hα]
  have hindicator_mono : ∀ {u v : TreeNode n},
      treeCylinder n u ⊆ treeCylinder n v → treeFunction n u ≤ treeFunction n v := by
    intro u v huv α
    change treeFunction n u α ≤ treeFunction n v α
    by_cases hα : α ∈ treeCylinder n u
    · rw [treeFunction_apply_of_mem n u hα,
        treeFunction_apply_of_mem n v (huv hα)]
    · rw [treeFunction_apply_of_notMem n u hα]
      exact hnonneg v α
  have hsubset : ∀ m,
      treeCylinder n (TreeNode.child t ht m) ⊆ treeCylinder n t := by
    intro m α hα
    exact (mem_treeCylinder_child_iff n t ht m α).mp hα |>.1
  have hle : ∀ m, treeFunction n (TreeNode.child t ht m) ≤ treeFunction n t :=
    fun m ↦ hindicator_mono (hsubset m)
  refine ⟨fun m ↦ ⟨hsubset m, hle m⟩, ?_, ?_⟩
  · intro a b hab
    apply hindicator_mono
    intro α hα
    rcases (mem_treeCylinder_child_iff n t ht a α).mp hα with ⟨hαt, hlast⟩
    exact (mem_treeCylinder_child_iff n t ht b α).mpr ⟨hαt, hlast.trans hab⟩
  · constructor
    · rintro _ ⟨m, rfl⟩
      exact hle m
    · intro g hg α
      change treeFunction n t α ≤ g α
      by_cases hα : α ∈ treeCylinder n t
      · let m := α ⟨t, ht⟩
        have hchild : α ∈ treeCylinder n (TreeNode.child t ht m) :=
          (mem_treeCylinder_child_iff n t ht m α).mpr ⟨hα, le_rfl⟩
        calc
          treeFunction n t α = 1 := treeFunction_apply_of_mem n t hα
          _ = treeFunction n (TreeNode.child t ht m) α :=
            (treeFunction_apply_of_mem n _ hchild).symm
          _ ≤ g α := hg ⟨m, rfl⟩ α
      · rw [treeFunction_apply_of_notMem n t hα]
        exact (hnonneg (TreeNode.child t ht 0) α).trans (hg ⟨0, rfl⟩ α)

/-- Paper Lemma `lem:finite-cover`. -/
theorem treeCylinder_finite_cover
    (n : ℕ) (t : TreeNode n) (F : Finset (TreeNode n))
    (hcover : ∀ α ∈ treeCylinder n t, ∃ u ∈ F, α ∈ treeCylinder n u) :
    ∃ u ∈ F, treeCylinder n t ⊆ treeCylinder n u := by
  classical
  by_contra hconcl
  push Not at hconcl
  let witness : ↥F → TreeProduct n := fun u ↦
    Classical.choose (Set.not_subset.mp (hconcl u.1 u.2))
  have hwitness_mem (u : ↥F) : witness u ∈ treeCylinder n t :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).1
  have hwitness_notMem (u : ↥F) : witness u ∉ treeCylinder n u.1 :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).2
  let α : TreeProduct n := fun q ↦ Finset.univ.sup fun u : ↥F ↦ witness u q
  have hαt : α ∈ treeCylinder n t := by
    intro j
    apply Finset.sup_le
    intro u _
    exact hwitness_mem u j
  obtain ⟨u, huF, hαu⟩ := hcover α hαt
  let uF : ↥F := ⟨u, huF⟩
  have hnot := hwitness_notMem uF
  simp only [treeCylinder, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have hle : witness uF (strictPrefix u j) ≤ α (strictPrefix u j) := by
    exact Finset.le_sup (s := Finset.univ)
      (f := fun v : ↥F ↦ witness v (strictPrefix u j)) (Finset.mem_univ uF)
  exact (not_lt_of_ge (hαu j)) (hj.trans_le hle)

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
    apply isClopen_iUnion_of_finite
    exact fun t ↦ treeCylinder_isClopen n t.1)

private def treeLastLabel {n : ℕ} (t : TreeNode n) : ℕ :=
  if h : 0 < TreeNode.level t then
    t.1.get ⟨TreeNode.level t - 1, Nat.sub_lt h (by omega)⟩ else 0

private theorem strictPrefix_last_eq_parent {n : ℕ} (t : TreeNode n)
    (ht : 0 < TreeNode.level t) :
    let j : Fin (TreeNode.level t) :=
      ⟨TreeNode.level t - 1, Nat.sub_lt ht (by omega)⟩
    (strictPrefix t j).1 = TreeNode.parent t ∧ t.1.get j = treeLastLabel t := by
  dsimp
  constructor
  · apply Subtype.ext
    simp [strictPrefix, TreeNode.restrict, TreeNode.parent, TreeNode.level,
      List.dropLast_eq_take]
  · simp [treeLastLabel, ht]

private theorem finiteTreeSup_nonneg (n : ℕ) (F : Finset (TreeNode n)) :
    0 ≤ finiteTreeSup n F := by
  intro α
  classical
  by_cases hα : α ∈ finiteCylinderUnion n F <;>
    simp [finiteTreeSup, BoundedContinuousFunction.indicator, Set.indicator, hα]

private theorem finiteTreeSup_apply_of_notMem (n : ℕ) (F : Finset (TreeNode n))
    {α : TreeProduct n} (hα : α ∉ finiteCylinderUnion n F) :
    finiteTreeSup n F α = 0 := by
  classical
  simp [finiteTreeSup, BoundedContinuousFunction.indicator, Set.indicator, hα]

private theorem commonLower_le_zero_of_parentDisjoint_subseq
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n))
      (F j : Set (TreeNode n)))
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hroot : ∀ m, TreeNode.root n ∉ F (φ m))
    (g : ℕ → BoundedContinuousFunction (TreeProduct n) ℝ)
    (hgzero : ∀ m α, α ∉ finiteCylinderUnion n (F (φ m)) → g (φ m) α = 0)
    {z : BoundedContinuousFunction (TreeProduct n) ℝ}
    (hz : ∀ m, z ≤ g m) : z ≤ 0 := by
  classical
  intro α
  change z α ≤ 0
  let β : ℕ → TreeProduct n := fun m q ↦
    max (α q) ((F (φ m)).sup fun t ↦
      if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0)
  have hβoutside : ∀ m, β m ∉ finiteCylinderUnion n (F (φ m)) := by
    intro m hmem
    simp only [finiteCylinderUnion, Set.mem_iUnion] at hmem
    obtain ⟨t, ht⟩ := hmem
    have htF : t.1 ∈ F (φ m) := t.2
    have htroot : t.1 ≠ TreeNode.root n := fun h ↦ hroot m (h ▸ htF)
    have htpos : 0 < TreeNode.level t.1 := Nat.pos_of_ne_zero fun hzero ↦ by
      apply htroot
      apply Subtype.ext
      have hnil : t.1.1 = [] := List.length_eq_zero_iff.mp (by
        simpa [TreeNode.level] using hzero)
      simpa [TreeNode.root] using hnil
    let j : Fin (TreeNode.level t.1) :=
      ⟨TreeNode.level t.1 - 1, Nat.sub_lt htpos (by omega)⟩
    have hj := strictPrefix_last_eq_parent t.1 htpos
    have hsup : treeLastLabel t.1 + 1 ≤
        (F (φ m)).sup fun u ↦
          if TreeNode.parent u = (strictPrefix t.1 j).1 then treeLastLabel u + 1 else 0 := by
      have hle := Finset.le_sup (s := F (φ m))
        (f := fun u ↦ if TreeNode.parent u = (strictPrefix t.1 j).1 then
          treeLastLabel u + 1 else 0) htF
      have hjparent : TreeNode.parent t.1 = (strictPrefix t.1 j).1 := hj.1.symm
      change (if TreeNode.parent t.1 = (strictPrefix t.1 j).1 then
        treeLastLabel t.1 + 1 else 0) ≤ _ at hle
      rw [if_pos hjparent] at hle
      exact hle
    have hlarge : treeLastLabel t.1 + 1 ≤ β m (strictPrefix t.1 j) :=
      hsup.trans (le_max_right _ _)
    have hcyl := ht j
    rw [hj.2] at hcyl
    exact (not_lt_of_ge hcyl) (lt_of_lt_of_le (Nat.lt_succ_self _) hlarge)
  have hβtendsto : Tendsto β atTop (nhds α) := by
    rw [tendsto_pi_nhds]
    intro q
    let bad : Set ℕ := {m | ∃ t ∈ F (φ m), TreeNode.parent t = q.1}
    have hbadsub : bad.Subsingleton := by
      intro i hi j hj
      rcases hi with ⟨ti, hti, hpi⟩
      rcases hj with ⟨tj, htj, hpj⟩
      by_contra hij
      have hindices : φ i ≠ φ j := fun h ↦ hij (hφ h)
      have hdis := hF hindices
      have hqmem : q.1 ∈
          TreeNode.parent '' (F (φ i) : Set (TreeNode n)) ∩
            TreeNode.parent '' (F (φ j) : Set (TreeNode n)) := by
        constructor
        · exact ⟨ti, hti, hpi⟩
        · exact ⟨tj, htj, hpj⟩
      rw [hdis] at hqmem
      exact hqmem
    have hevent : ∀ᶠ m in atTop, m ∉ bad := by
      rw [← Nat.cofinite_eq_atTop]
      exact hbadsub.finite.eventually_cofinite_notMem
    have heq : (fun m ↦ β m q) =ᶠ[atTop] fun _ ↦ α q := by
      filter_upwards [hevent] with m hm
      have hsupzero : (F (φ m)).sup (fun t ↦
          if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0) = 0 := by
        apply le_antisymm
        · apply Finset.sup_le
          intro t ht
          rw [if_neg]
          intro hparent
          exact hm ⟨t, ht, hparent⟩
        · exact bot_le
      simp [β, hsupzero]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hzβ : ∀ m, z (β m) ≤ 0 := by
    intro m
    have hle := hz (φ m) (β m)
    change z (β m) ≤ g (φ m) (β m) at hle
    rw [hgzero m (β m) (hβoutside m)] at hle
    exact hle
  have hzlim : Tendsto (fun m ↦ z (β m)) atTop (nhds (z α)) :=
    Filter.Tendsto.comp z.continuous.continuousAt hβtendsto
  exact isClosed_Iic.mem_of_tendsto hzlim (Eventually.of_forall hzβ)

/-- Paper Lemma `lem:pi-disjoint`. -/
theorem parentDisjoint_treeFunctions_iInf
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n)) (F j : Set (TreeNode n))) :
    IsGLB (Set.range fun m ↦ finiteTreeSup n (F m)) 0 := by
  constructor
  · rintro _ ⟨m, rfl⟩
    exact finiteTreeSup_nonneg n (F m)
  · intro z hz
    have hzall : ∀ m, z ≤ finiteTreeSup n (F m) := fun m ↦ hz ⟨m, rfl⟩
    by_cases hrootExists : ∃ i, TreeNode.root n ∈ F i
    · obtain ⟨i, hi⟩ := hrootExists
      let φ : ℕ → ℕ := fun m ↦ i + m + 1
      have hφ : Function.Injective φ := by
        intro a b h
        dsimp [φ] at h
        omega
      have hroot : ∀ m, TreeNode.root n ∉ F (φ m) := by
        intro m hm
        have hne : i ≠ φ m := by
          dsimp [φ]
          omega
        have hdis := hF hne
        have hmem : TreeNode.root n ∈
            TreeNode.parent '' (F i : Set (TreeNode n)) ∩
              TreeNode.parent '' (F (φ m) : Set (TreeNode n)) := by
          constructor
          · exact ⟨TreeNode.root n, hi, by simp [TreeNode.parent, TreeNode.root]⟩
          · exact ⟨TreeNode.root n, hm, by simp [TreeNode.parent, TreeNode.root]⟩
        rw [hdis] at hmem
        exact hmem
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF φ hφ hroot
        (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall
    · push Not at hrootExists
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF id
        Function.injective_id hrootExists (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall

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

private theorem treeRho_nonneg (n : ℕ) (w : TreeCoefficients n) :
    0 ≤ treeRho n w := by
  classical
  exact Finsupp.sum_nonneg' fun t ↦
    mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

private theorem treeRho_neg (n : ℕ) (w : TreeCoefficients n) :
    treeRho n (-w) = treeRho n w := by
  classical
  rw [treeRho, treeRho, Finsupp.sum, Finsupp.sum, Finsupp.support_neg]
  simp

private theorem treeRho_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeRho n (a • w) = |a| * treeRho n w := by
  classical
  unfold treeRho
  rw [Finsupp.sum_of_support_subset (a • w) Finsupp.support_smul _ (by simp)]
  simp only [Finsupp.sum, Finsupp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem treeRho_add_le (n : ℕ) (u v : TreeCoefficients n) :
    treeRho n (u + v) ≤ treeRho n u + treeRho n v := by
  classical
  rw [treeRho, treeRho, treeRho]
  rw [Finsupp.sum_of_support_subset (u + v) Finsupp.support_add _ (by simp)]
  rw [Finsupp.sum_of_support_subset u
    (show u.support ⊆ u.support ∪ v.support from Finset.subset_union_left) _ (by simp)]
  rw [Finsupp.sum_of_support_subset v
    (show v.support ⊆ u.support ∪ v.support from Finset.subset_union_right) _ (by simp)]
  simp only [Finsupp.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  simpa [mul_add] using
    (mul_le_mul_of_nonneg_left (abs_add_le (u t) (v t))
      (zpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (-(TreeNode.level t : ℤ))))

private theorem treeRho_mono_of_nonneg (n : ℕ) {u v : TreeCoefficients n}
    (hu : 0 ≤ u) (huv : u ≤ v) : treeRho n u ≤ treeRho n v := by
  classical
  have hv : 0 ≤ v := hu.trans huv
  rw [treeRho, treeRho]
  rw [Finsupp.sum_of_support_subset u
    (show u.support ⊆ u.support ∪ v.support from Finset.subset_union_left) _ (by simp)]
  rw [Finsupp.sum_of_support_subset v
    (show v.support ⊆ u.support ∪ v.support from Finset.subset_union_right) _ (by simp)]
  apply Finset.sum_le_sum
  intro t _
  rw [abs_of_nonneg (hu t), abs_of_nonneg (hv t)]
  exact mul_le_mul_of_nonneg_left (huv t) (zpow_nonneg (by norm_num) _)

private theorem treeOperator_zero (n : ℕ) :
    treeOperator n (0 : TreeCoefficients n) = 0 := by
  simp [treeOperator]

private theorem treeOperator_add (n : ℕ) (u v : TreeCoefficients n) :
    treeOperator n (u + v) = treeOperator n u + treeOperator n v := by
  classical
  simp only [treeOperator]
  exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

private theorem treeOperator_smul (n : ℕ) (a : ℝ) (w : TreeCoefficients n) :
    treeOperator n (a • w) = a • treeOperator n w := by
  classical
  simp only [treeOperator]
  rw [Finsupp.sum_smul_index (by simp)]
  change (∑ t ∈ w.support, (a * w t) • treeFunction n t) =
    a • ∑ t ∈ w.support, w t • treeFunction n t
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [smul_smul]

private theorem treeOperator_nonneg (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    0 ≤ treeOperator n w := by
  classical
  change 0 ≤ w.sum fun t a ↦ a • treeFunction n t
  apply Finsupp.sum_nonneg'
  intro t α
  change 0 ≤ w t * treeFunction n t α
  exact mul_nonneg (hw t) (by
    by_cases h : α ∈ treeCylinder n t <;> simp [treeFunction,
      BoundedContinuousFunction.indicator, Set.indicator, h])

private theorem treeOperator_single (n : ℕ) (t : TreeNode n) (a : ℝ) :
    treeOperator n (Finsupp.single t a) = a • treeFunction n t := by
  simp [treeOperator]

private theorem treeOperator_apply (n : ℕ) (w : TreeCoefficients n)
    (α : TreeProduct n) :
    treeOperator n w α = w.sum (fun t a ↦ a * treeFunction n t α) := by
  classical
  rw [treeOperator, Finsupp.sum, Finsupp.sum]
  change (BoundedContinuousFunction.evalCLM ℝ α)
      (∑ t ∈ w.support, w t • treeFunction n t) =
    ∑ t ∈ w.support, w t * treeFunction n t α
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp

private theorem treeFunction_root (n : ℕ) :
    treeFunction n (TreeNode.root n) = 1 := by
  ext α
  simp [treeFunction, BoundedContinuousFunction.indicator, treeCylinder,
    TreeNode.root, TreeNode.level]

private theorem abs_le_norm_smul_root (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    |x| ≤ ‖x‖ • treeFunction n (TreeNode.root n) := by
  rw [treeFunction_root]
  intro α
  change |x α| ≤ ‖x‖ * 1
  simpa using x.norm_coe_le_norm α

private theorem treeAdmissible_nonempty (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r}.Nonempty := by
  let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
  refine ⟨treeRho n w, w, ?_, ?_, rfl⟩
  · exact Finsupp.single_nonneg.mpr (norm_nonneg x)
  · rw [treeOperator_single]
    exact abs_le_norm_smul_root n x

private theorem treeAdmissible_bddBelow (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    BddBelow {r : ℝ | ∃ w : TreeCoefficients n,
      0 ≤ w ∧ |x| ≤ treeOperator n w ∧ treeRho n w = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w

private theorem treeSeminorm_nonneg (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    0 ≤ treeSeminorm n x := by
  apply le_csInf (treeAdmissible_nonempty n x)
  rintro r ⟨w, _, _, rfl⟩
  exact treeRho_nonneg n w

private theorem treeSeminorm_le_of_majorant (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    treeSeminorm n x ≤ treeRho n w := by
  exact csInf_le (treeAdmissible_bddBelow n x) ⟨w, hw, hxw, rfl⟩

private theorem treeSeminorm_zero (n : ℕ) :
    treeSeminorm n (0 : BoundedContinuousFunction (TreeProduct n) ℝ) = 0 := by
  apply le_antisymm
  · simpa [treeRho] using
      (treeSeminorm_le_of_majorant n 0 0 (by simp)
        (by simp [treeOperator_zero]))
  · exact treeSeminorm_nonneg n 0

private theorem exists_treeMajorant_lt (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧ |x| ≤ treeOperator n w ∧
      treeRho n w < treeSeminorm n x + ε := by
  obtain ⟨r, ⟨w, hw, hxw, hwr⟩, hr⟩ :=
    exists_lt_of_csInf_lt (treeAdmissible_nonempty n x)
      (lt_add_of_pos_right (treeSeminorm n x) hε)
  exact ⟨w, hw, hxw, by simpa [hwr] using hr⟩

private theorem treeSeminorm_smul_le (n : ℕ) (a : ℝ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n (a • x) ≤ |a| * treeSeminorm n x := by
  by_cases ha : a = 0
  · subst a
    simpa using (treeSeminorm_zero n).le
  apply le_of_forall_pos_le_add
  intro ε hε
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨w, hw, hxw, hrho⟩ := exists_treeMajorant_lt n x (div_pos hε habs)
  have hmajor : |a • x| ≤ treeOperator n (|a| • w) := by
    rw [treeOperator_smul]
    intro α
    change |a * x α| ≤ |a| * treeOperator n w α
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hxw α) (abs_nonneg a)
  have hwscale : 0 ≤ |a| • w := by
    intro t
    change 0 ≤ |a| * w t
    exact mul_nonneg (abs_nonneg a) (hw t)
  calc
    treeSeminorm n (a • x) ≤ treeRho n (|a| • w) :=
      treeSeminorm_le_of_majorant n _ _ hwscale hmajor
    _ = |a| * treeRho n w := by rw [treeRho_smul, abs_of_nonneg (abs_nonneg a)]
    _ ≤ |a| * treeSeminorm n x + ε := by
      have := mul_lt_mul_of_pos_left hrho habs
      rw [mul_add, mul_div_cancel₀ _ habs.ne'] at this
      exact this.le

private theorem treeFunction_norm_le_one (n : ℕ) (t : TreeNode n) :
    ‖treeFunction n t‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le zero_le_one]
  intro α
  by_cases h : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t h]
    norm_num
  · rw [treeFunction_apply_of_notMem n t h]
    norm_num

private theorem treeOperator_norm_le_sum (n : ℕ) (w : TreeCoefficients n) :
    ‖treeOperator n w‖ ≤ ∑ t ∈ w.support, |w t| := by
  classical
  rw [treeOperator, Finsupp.sum]
  calc
    ‖∑ t ∈ w.support, w t • treeFunction n t‖ ≤
        ∑ t ∈ w.support, ‖w t • treeFunction n t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ w.support, |w t| := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (w t), treeFunction_norm_le_one n t]

private theorem treeRho_controls_sum (n : ℕ) (w : TreeCoefficients n) :
    (∑ t ∈ w.support, |w t|) ≤ (2 : ℝ) ^ n * treeRho n w := by
  classical
  rw [treeRho, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hc : (1 : ℝ) ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    apply one_le_zpow₀ (by norm_num)
    exact sub_nonneg.mpr (by exact_mod_cast t.2)
  nlinarith [abs_nonneg (w t)]

private theorem norm_le_pow_mul_treeRho (n : ℕ)
    (x : BoundedContinuousFunction (TreeProduct n) ℝ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) (hxw : |x| ≤ treeOperator n w) :
    ‖x‖ ≤ (2 : ℝ) ^ n * treeRho n w := by
  calc
    ‖x‖ ≤ ‖treeOperator n w‖ := by
      apply norm_le_norm_of_abs_le_abs
      simpa [abs_of_nonneg (treeOperator_nonneg n w hw)] using hxw
    _ ≤ ∑ t ∈ w.support, |w t| := treeOperator_norm_le_sum n w
    _ ≤ (2 : ℝ) ^ n * treeRho n w := treeRho_controls_sum n w

private theorem treeOperator_le_root_of_nonneg (n : ℕ) (w : TreeCoefficients n)
    (hw : 0 ≤ w) :
    treeOperator n w ≤
      ((2 : ℝ) ^ n * treeRho n w) • treeFunction n (TreeNode.root n) := by
  calc
    treeOperator n w = |treeOperator n w| :=
      (abs_of_nonneg (treeOperator_nonneg n w hw)).symm
    _ ≤ ‖treeOperator n w‖ • treeFunction n (TreeNode.root n) :=
      abs_le_norm_smul_root n (treeOperator n w)
    _ ≤ ((2 : ℝ) ^ n * treeRho n w) • treeFunction n (TreeNode.root n) := by
      intro α
      simpa [treeFunction_root] using
        (treeOperator_norm_le_sum n w).trans (treeRho_controls_sum n w)

/-- Paper Lemma `lem:pn-seminorm`, bundled using BanLat's `LatticeSeminorm`. -/
noncomputable def treeLatticeSeminorm (n : ℕ) :
    LatticeSeminorm (BoundedContinuousFunction (TreeProduct n) ℝ) where
  toFun := treeSeminorm n
  map_zero' := by
    exact treeSeminorm_zero n
  add_le' := by
    intro x y
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u, hu, hxu, hρu⟩ := exists_treeMajorant_lt n x (half_pos hε)
    obtain ⟨v, hv, hyv, hρv⟩ := exists_treeMajorant_lt n y (half_pos hε)
    have hmajor : |x + y| ≤ treeOperator n (u + v) := by
      rw [treeOperator_add]
      exact (abs_add_le x y).trans (add_le_add hxu hyv)
    calc
      treeSeminorm n (x + y) ≤ treeRho n (u + v) :=
        treeSeminorm_le_of_majorant n _ _ (add_nonneg hu hv) hmajor
      _ ≤ treeRho n u + treeRho n v := treeRho_add_le n u v
      _ ≤ treeSeminorm n x + treeSeminorm n y + ε := by linarith
  neg' := by
    intro x
    simp [treeSeminorm]
  smul' := by
    intro a x
    apply le_antisymm
    · exact treeSeminorm_smul_le n a x
    · by_cases ha : a = 0
      · subst a
        simp [treeSeminorm_zero]
      have hinv := treeSeminorm_smul_le n a⁻¹ (a • x)
      have habs : 0 < |a| := abs_pos.mpr ha
      calc
        |a| * treeSeminorm n x =
            |a| * treeSeminorm n (a⁻¹ • (a • x)) := by
              simp [smul_smul, ha]
        _ ≤ |a| * (|a⁻¹| * treeSeminorm n (a • x)) :=
          mul_le_mul_of_nonneg_left hinv habs.le
        _ = treeSeminorm n (a • x) := by
          rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]
  monotone_abs' := by
    intro x y hxy
    apply le_csInf (treeAdmissible_nonempty n y)
    rintro r ⟨w, hw, hyw, rfl⟩
    exact treeSeminorm_le_of_majorant n x w hw (hxy.trans hyw)

/-- Paper Lemma `lem:norm-comparison`. -/
theorem treeSeminorm_norm_comparison
    (n : ℕ) (x : BoundedContinuousFunction (TreeProduct n) ℝ) :
    treeSeminorm n x ≤ ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ n * treeSeminorm n x := by
  constructor
  · let w : TreeCoefficients n := Finsupp.single (TreeNode.root n) ‖x‖
    have hw : 0 ≤ w := Finsupp.single_nonneg.mpr (norm_nonneg x)
    have hxw : |x| ≤ treeOperator n w := by
      rw [treeOperator_single]
      exact abs_le_norm_smul_root n x
    calc
      treeSeminorm n x ≤ treeRho n w := treeSeminorm_le_of_majorant n x w hw hxw
      _ = ‖x‖ := by simp [w, treeRho, TreeNode.root, TreeNode.level]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    obtain ⟨w, hw, hxw, hrho⟩ :=
      exists_treeMajorant_lt n x (div_pos hε hpow)
    have hnorm := norm_le_pow_mul_treeRho n x w hw hxw
    have hscaled := mul_lt_mul_of_pos_left hrho hpow
    rw [mul_add, mul_div_cancel₀ _ hpow.ne'] at hscaled
    exact hnorm.trans hscaled.le

private theorem level_strictPrefix {n : ℕ} (t : TreeNode n)
    (j : Fin (TreeNode.level t)) :
    TreeNode.level (strictPrefix t j).1 = j := by
  simp [strictPrefix, TreeNode.restrict, TreeNode.level]

private theorem level_le_of_treeCylinder_subset {n : ℕ} {t u : TreeNode n}
    (hsub : treeCylinder n t ⊆ treeCylinder n u) :
    TreeNode.level u ≤ TreeNode.level t := by
  classical
  by_contra h
  have hlt : TreeNode.level t < TreeNode.level u := Nat.lt_of_not_ge h
  let j : Fin (TreeNode.level u) := ⟨TreeNode.level t, hlt⟩
  let q : TreeNonterminal n := strictPrefix u j
  let α : TreeProduct n := fun r ↦ if r = q then u.1.get j + 1 else 0
  have hαt : α ∈ treeCylinder n t := by
    intro k
    have hne : strictPrefix t k ≠ q := by
      intro heq
      have hlevel := congrArg (fun r : TreeNonterminal n ↦ TreeNode.level r.1) heq
      change TreeNode.level (strictPrefix t k).1 = TreeNode.level q.1 at hlevel
      rw [level_strictPrefix t k, show TreeNode.level q.1 = j by
        exact level_strictPrefix u j] at hlevel
      exact (Nat.ne_of_lt k.isLt) hlevel
    simp [α, hne]
  have hαu := hsub hαt j
  simp [α, q] at hαu

private theorem treeFunction_nonneg (n : ℕ) (t : TreeNode n) :
    0 ≤ treeFunction n t := by
  intro α
  change (0 : ℝ) ≤ treeFunction n t α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα]
    norm_num
  · rw [treeFunction_apply_of_notMem n t hα]

/-- Paper Lemma `lem:exact-basis`. -/
theorem treeSeminorm_exact_basis (n : ℕ) (t : TreeNode n) :
    (∀ w : TreeCoefficients n, 0 ≤ w → treeFunction n t ≤ treeOperator n w →
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) ≤ treeRho n w) ∧
    treeSeminorm n (treeFunction n t) =
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  classical
  let a : ℝ := (2 : ℝ) ^ (-(TreeNode.level t : ℤ))
  have ha : 0 < a := zpow_pos (by norm_num) _
  have hlower : ∀ w : TreeCoefficients n, 0 ≤ w →
      treeFunction n t ≤ treeOperator n w → a ≤ treeRho n w := by
    intro w hw hdom
    let C := w.support.filter fun u ↦ treeCylinder n t ⊆ treeCylinder n u
    let N := w.support.filter fun u ↦ ¬treeCylinder n t ⊆ treeCylinder n u
    have hnotcover : ¬(∀ α ∈ treeCylinder n t,
        ∃ u ∈ N, α ∈ treeCylinder n u) := by
      intro hcover
      obtain ⟨u, huN, hsub⟩ := treeCylinder_finite_cover n t N hcover
      exact (Finset.mem_filter.mp huN).2 hsub
    push Not at hnotcover
    obtain ⟨α, hαt, hαN⟩ := hnotcover
    have hoperator : treeOperator n w α = ∑ u ∈ C, w u := by
      rw [treeOperator_apply, Finsupp.sum]
      change (∑ u ∈ w.support, w u * treeFunction n u α) = ∑ u ∈ C, w u
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hsub : treeCylinder n t ⊆ treeCylinder n u
      · rw [if_pos hsub, treeFunction_apply_of_mem n u (hsub hαt), mul_one]
      · have huN : u ∈ N := Finset.mem_filter.mpr ⟨hu, hsub⟩
        rw [if_neg hsub, treeFunction_apply_of_notMem n u (hαN u huN), mul_zero]
    have hsum : 1 ≤ ∑ u ∈ C, w u := by
      have hdomα := hdom α
      change treeFunction n t α ≤ treeOperator n w α at hdomα
      rw [treeFunction_apply_of_mem n t hαt, hoperator] at hdomα
      exact hdomα
    calc
      a ≤ a * ∑ u ∈ C, w u := by nlinarith
      _ = ∑ u ∈ C, a * w u := by rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ C,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum
        intro u huC
        have hsub := (Finset.mem_filter.mp huC).2
        have hlevel := level_le_of_treeCylinder_subset hsub
        have hweight : a ≤ (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) := by
          apply zpow_le_zpow_right₀ (by norm_num)
          exact neg_le_neg (by exact_mod_cast hlevel)
        rw [abs_of_nonneg (hw u)]
        exact mul_le_mul_of_nonneg_right hweight (hw u)
      _ ≤ ∑ u ∈ w.support,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u _ _
        exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
      _ = treeRho n w := by rw [treeRho, Finsupp.sum]
  refine ⟨hlower, ?_⟩
  apply le_antisymm
  · let w : TreeCoefficients n := treeBasis t
    have hw : 0 ≤ w := by simp [w, treeBasis]
    have hmajor : |treeFunction n t| ≤ treeOperator n w := by
      rw [abs_of_nonneg (treeFunction_nonneg n t)]
      change treeFunction n t ≤ treeOperator n (treeBasis t)
      rw [treeBasis, treeOperator_single, one_smul]
    calc
      treeSeminorm n (treeFunction n t) ≤ treeRho n w :=
        treeSeminorm_le_of_majorant n _ w hw hmajor
      _ = a := by simp [w, treeBasis, treeRho, a]
  · apply le_csInf (treeAdmissible_nonempty n (treeFunction n t))
    rintro r ⟨w, hw, hmajor, rfl⟩
    apply hlower w hw
    simpa [abs_of_nonneg (treeFunction_nonneg n t)] using hmajor

/-- The closed vector sublattice generated by the tree functions. -/
noncomputable def treeSublattice (n : ℕ) :
    VectorSublattice (BoundedContinuousFunction (TreeProduct n) ℝ) :=
  (VectorSublattice.generated (Set.range (treeFunction n))).topologicalClosure

private theorem treeOperator_mem_treeSublattice (n : ℕ) (w : TreeCoefficients n) :
    treeOperator n w ∈ treeSublattice n := by
  classical
  apply subset_closure
  change treeOperator n w ∈
    VectorSublattice.generated (Set.range (treeFunction n))
  rw [treeOperator, Finsupp.sum]
  apply Submodule.sum_mem
  intro t ht
  exact (VectorSublattice.generated (Set.range (treeFunction n))).toSubmodule.smul_mem
    _ (VectorSublattice.subset_generated _ ⟨t, rfl⟩)

/-- The component space `X_n`, using the underlying submodule carrier. -/
abbrev TreeComponent (n : ℕ) := ↥(treeSublattice n).toSubmodule

/-- Pointwise lattice operations on the component subspace. -/
noncomputable instance treeComponentLattice (n : ℕ) : Lattice (TreeComponent n) where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, (treeSublattice n).sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, (treeSublattice n).inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz

/-- Compatibility of the inherited addition with the pointwise order. -/
instance treeComponentIsOrderedAddMonoid (n : ℕ) :
    IsOrderedAddMonoid (TreeComponent n) where
  add_le_add_left a b hab c := by
    intro p
    simpa [add_comm] using add_le_add_right (hab p) (c.1 p)

/-- The component subspace is a real vector lattice. -/
noncomputable instance treeComponentVectorLattice (n : ℕ) :
    VectorLattice (TreeComponent n) where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    exact smul_le_smul_of_nonneg_left hxy ha

/-- The norm `p_n` restricted to `X_n`. -/
noncomputable def componentLatticeNorm (n : ℕ) : PaperLatticeNorm (TreeComponent n) where
  toFun := fun x ↦ treeSeminorm n x.1
  nonneg := by
    intro x
    exact apply_nonneg (treeLatticeSeminorm n).toSeminorm x.1
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      apply norm_eq_zero.mp
      have hle := (treeSeminorm_norm_comparison n x.1).2
      rw [hx, mul_zero] at hle
      exact le_antisymm hle (norm_nonneg _)
    · rintro rfl
      exact map_zero (treeLatticeSeminorm n).toSeminorm
  add_le := by
    intro x y
    exact map_add_le_add (treeLatticeSeminorm n).toSeminorm x.1 y.1
  smul := by
    intro a x
    simpa [Real.norm_eq_abs] using
      map_smul_eq_mul (treeLatticeSeminorm n).toSeminorm a x.1
  solid := by
    intro x y hxy
    exact (treeLatticeSeminorm n).monotone_abs' hxy

/-- The constant function `1`, as an element of `X_n`. -/
noncomputable def componentRoot (n : ℕ) : TreeComponent n :=
  ⟨treeFunction n (TreeNode.root n), by
    change treeFunction n (TreeNode.root n) ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨TreeNode.root n, rfl⟩⟩

/-- Any tree function, viewed in the generated component. -/
noncomputable def componentTreeFunction (n : ℕ) (t : TreeNode n) : TreeComponent n :=
  ⟨treeFunction n t, by
    change treeFunction n t ∈
      closure (VectorSublattice.generated (Set.range (treeFunction n)) :
        Set (BoundedContinuousFunction (TreeProduct n) ℝ))
    apply subset_closure
    exact VectorSublattice.subset_generated _ ⟨t, rfl⟩⟩

/-- Paper Corollary `cor:Yn-basic`. -/
theorem component_basic (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      componentLatticeNorm n (componentRoot n) = 1 ∧
      (∀ t : TreeNode n, TreeNode.level t = n →
        componentLatticeNorm n (componentTreeFunction n t) =
          (2 : ℝ) ^ (-(n : ℤ))) := by
  have hseparable : TopologicalSpace.IsSeparable
      (Set.univ : Set (TreeComponent n)) := by
    letI : Countable (TreeNode n) := by
      unfold TreeNode
      infer_instance
    letI : TopologicalSpace.SeparableSpace (TreeComponent n) :=
      VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
        (Set.countable_range (treeFunction n))
    exact TopologicalSpace.isSeparable_univ_iff.mpr inferInstance
  have hcomplete : IsCompleteFor (componentLatticeNorm n) := by
    intro f hf
    have hnormCauchy : CauchySeq (fun m ↦ (f m).1) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
      obtain ⟨N, hN⟩ := hf (ε / (2 : ℝ) ^ n) (div_pos hε hpow)
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hp := hN m hm k hk
      have hnorm := (treeSeminorm_norm_comparison n ((f m).1 - (f k).1)).2
      rw [dist_eq_norm_sub]
      change treeSeminorm n ((f m).1 - (f k).1) < ε / (2 : ℝ) ^ n at hp
      have hscaled := mul_lt_mul_of_pos_left hp hpow
      rw [mul_div_cancel₀ _ hpow.ne'] at hscaled
      exact hnorm.trans_lt hscaled
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hnormCauchy
    have hymem : y ∈ treeSublattice n := by
      apply isClosed_closure.mem_of_tendsto hy
      exact Eventually.of_forall fun m ↦ (f m).2
    let z : TreeComponent n := ⟨y, hymem⟩
    refine ⟨z, ?_⟩
    rw [Metric.tendsto_atTop] at hy
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    have hp := (treeSeminorm_norm_comparison n ((f m).1 - y)).1
    have hdist := hN m hm
    rw [dist_eq_norm_sub] at hdist
    change treeSeminorm n ((f m).1 - y) < ε
    exact hp.trans_lt hdist
  refine ⟨hseparable, hcomplete, ?_, ?_⟩
  · change treeSeminorm n (treeFunction n (TreeNode.root n)) = 1
    simpa [TreeNode.root, TreeNode.level] using
      (treeSeminorm_exact_basis n (TreeNode.root n)).2
  · intro t ht
    change treeSeminorm n (treeFunction n t) = (2 : ℝ) ^ (-(n : ℤ))
    simpa [ht] using (treeSeminorm_exact_basis n t).2

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

private noncomputable def treeBandOfNode (n : ℕ) (t : TreeNode n) : TreeBandIndex n :=
  by
    classical
    exact if h : t = TreeNode.root n then none else
      some ⟨TreeNode.parent t, by
        have htpos : 0 < TreeNode.level t := Nat.pos_of_ne_zero fun hzero ↦ h (by
          apply Subtype.ext
          have hnil : t.1 = [] := List.length_eq_zero_iff.mp (by
            simpa [TreeNode.level] using hzero)
          simpa [TreeNode.root] using hnil)
        have hp : TreeNode.level (TreeNode.parent t) = TreeNode.level t - 1 := by
          simp [TreeNode.parent, TreeNode.level]
        have htn : TreeNode.level t ≤ n := t.2
        omega⟩

private theorem node_mem_its_treeBand (n : ℕ) (t : TreeNode n) :
    t ∈ treeBandSupport n (treeBandOfNode n t) := by
  classical
  by_cases h : t = TreeNode.root n
  · simp [treeBandOfNode, h, treeBandSupport]
  · simp [treeBandOfNode, h, treeBandSupport]

private theorem treeBandOfNode_eq_of_mem (n : ℕ) (t : TreeNode n)
    (B : TreeBandIndex n) (ht : t ∈ treeBandSupport n B) :
    treeBandOfNode n t = B := by
  classical
  cases B with
  | none =>
      have htroot : t = TreeNode.root n := by simpa [treeBandSupport] using ht
      simp [treeBandOfNode, htroot]
  | some u =>
      have ht' : TreeNode.parent t = u.1 ∧ t ≠ TreeNode.root n := by
        simpa [treeBandSupport] using ht
      simp [treeBandOfNode, ht'.2, ht'.1]

private theorem treeBandProjection_support_nonempty_iff (n : ℕ)
    (B : TreeBandIndex n) (w : TreeCoefficients n) :
    (treeBandProjection n B w).support.Nonempty ↔
      ∃ t ∈ w.support, treeBandOfNode n t = B := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have ht' : t ∈ w.support ∧ t ∈ treeBandSupport n B := by
      simpa [treeBandProjection] using ht
    exact ⟨t, ht'.1, treeBandOfNode_eq_of_mem n t B ht'.2⟩
  · rintro ⟨t, htw, htB⟩
    refine ⟨t, ?_⟩
    have htmem := node_mem_its_treeBand n t
    rw [htB] at htmem
    simp [treeBandProjection, htw, htmem]

private noncomputable def bandsAt (n : ℕ) (w : TreeCoefficients n) :
    Finset (TreeBandIndex n) := by
  classical
  exact w.support.image (treeBandOfNode n)

private theorem mem_bandsAt_iff (n : ℕ) (w : TreeCoefficients n)
    (B : TreeBandIndex n) :
    B ∈ bandsAt n w ↔ (treeBandProjection n B w).support.Nonempty := by
  classical
  rw [treeBandProjection_support_nonempty_iff]
  simp [bandsAt, eq_comm]

private theorem finiteBandProjection_apply (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) (t : TreeNode n) :
    (treeBandOfNode n t ∈ Λ → finiteBandProjection n Λ w t = w t) ∧
      (treeBandOfNode n t ∉ Λ → finiteBandProjection n Λ w t = 0) := by
  classical
  constructor
  · intro hB
    apply Finsupp.filter_apply_pos
    exact ⟨treeBandOfNode n t, hB, node_mem_its_treeBand n t⟩
  · intro hB
    apply Finsupp.filter_apply_neg
    rintro ⟨B, hBΛ, htB⟩
    exact hB (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)

private theorem treeRho_finiteBandProjection (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) =
      ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) := by
  classical
  have hfinite : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |finiteBandProjection n Λ w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [finiteBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  have hband (B : TreeBandIndex n) : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |treeBandProjection n B w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [treeBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  rw [hfinite]
  simp_rw [hband]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hΛ : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 hΛ]
    rw [Finset.sum_eq_single (treeBandOfNode n t)]
    · rw [treeBandProjection, Finsupp.filter_apply_pos]
      exact node_mem_its_treeBand n t
    · intro B hBΛ hBne
      have hnot : t ∉ treeBandSupport n B := by
        intro htB
        exact hBne (treeBandOfNode_eq_of_mem n t B htB).symm
      rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
      simp
    · intro hnot
      exact (hnot hΛ).elim
  · rw [(finiteBandProjection_apply n Λ w t).2 hΛ]
    simp only [abs_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro B hBΛ
    have hnot : t ∉ treeBandSupport n B := by
      intro htB
      exact hΛ (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)
    rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
    simp

private noncomputable def treeBandParent (n : ℕ) : TreeBandIndex n → TreeNode n
  | none => TreeNode.root n
  | some u => u.1

private theorem parent_eq_treeBandParent (n : ℕ) (t : TreeNode n) :
    TreeNode.parent t = treeBandParent n (treeBandOfNode n t) := by
  classical
  by_cases ht : t = TreeNode.root n
  · subst t
    simp [treeBandOfNode, treeBandParent, TreeNode.parent, TreeNode.root]
  · simp [treeBandOfNode, treeBandParent, ht]

/-- The upshift `S_n`, merging coefficients at their parents. -/
noncomputable def treeUpshift (n : ℕ) (w : TreeCoefficients n) : TreeCoefficients n :=
  w.mapDomain TreeNode.parent

private noncomputable def treeBandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) : Finset (TreeNode n) := by
  classical
  exact Λ.image (treeBandParent n)

private theorem treeUpshift_support_subset_bandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    (treeUpshift n (finiteBandProjection n Λ w)).support ⊆
      treeBandParents n Λ := by
  classical
  intro q hq
  rw [treeUpshift] at hq
  have hq' := Finsupp.mapDomain_support hq
  rcases Finset.mem_image.mp hq' with ⟨t, ht, rfl⟩
  rw [treeBandParents]
  apply Finset.mem_image.mpr
  refine ⟨treeBandOfNode n t, ?_, (parent_eq_treeBandParent n t).symm⟩
  have htfinite : t ∈ (finiteBandProjection n Λ w).support := ht
  by_contra hnot
  have hzero := (finiteBandProjection_apply n Λ w t).2 hnot
  exact Finsupp.mem_support_iff.mp htfinite hzero

private theorem treeParent_weight_le (n : ℕ) (t : TreeNode n) :
    (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) ≤
      2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  have hp : TreeNode.level (TreeNode.parent t) = TreeNode.level t - 1 := by
    simp [TreeNode.parent, TreeNode.level]
  by_cases ht : TreeNode.level t = 0
  · simp [hp, ht]
  · have hz : -(TreeNode.level (TreeNode.parent t) : ℤ) =
        -(TreeNode.level t : ℤ) + 1 := by omega
    rw [hz, zpow_add₀ (by norm_num)]
    simp [mul_comm]

private theorem treeCylinder_subset_parent (n : ℕ) (t : TreeNode n) :
    treeCylinder n t ⊆ treeCylinder n (TreeNode.parent t) := by
  intro α hα j
  let j' : Fin (TreeNode.level t) := ⟨j, by
    exact j.isLt.trans_le (by simp [TreeNode.parent, TreeNode.level])⟩
  have hj := hα j'
  have hpref : strictPrefix (TreeNode.parent t) j = strictPrefix t j' := by
    apply Subtype.ext
    apply Subtype.ext
    change t.1.dropLast.take j = t.1.take j'
    have htne : t.1 ≠ [] := by
      intro ht
      have hjlt := j.isLt
      simp [TreeNode.parent, TreeNode.level, ht] at hjlt
    nth_rewrite 2 [← List.dropLast_append_getLast htne]
    exact (List.take_append_of_le_length j.isLt.le).symm
  have hget : (TreeNode.parent t).1.get j = t.1.get j' := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp [TreeNode.parent]
    rfl
  rw [hpref, hget]
  exact hj

private theorem treeFunction_le_parent (n : ℕ) (t : TreeNode n) :
    treeFunction n t ≤ treeFunction n (TreeNode.parent t) := by
  intro α
  change treeFunction n t α ≤ treeFunction n (TreeNode.parent t) α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα,
      treeFunction_apply_of_mem n _ (treeCylinder_subset_parent n t hα)]
  · rw [treeFunction_apply_of_notMem n t hα]
    exact treeFunction_nonneg n _ α

/-- Paper Lemma `lem:upshift-basic`. -/
theorem treeUpshift_basic (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    treeRho n (treeUpshift n w) ≤ 2 * treeRho n w ∧
      treeOperator n w ≤ treeOperator n (treeUpshift n w) := by
  have hupnonneg : 0 ≤ treeUpshift n w :=
    Finsupp.mapDomain_nonneg hw
  constructor
  · classical
    have hrho_up : treeRho n (treeUpshift n w) =
        (treeUpshift n w).sum fun t a ↦
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * a := by
      rw [treeRho]
      apply Finsupp.sum_congr
      intro t _
      rw [abs_of_nonneg (hupnonneg t)]
    rw [hrho_up]
    rw [treeUpshift, Finsupp.sum_mapDomain_index (by simp) (by simp [mul_add])]
    rw [treeRho, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [abs_of_nonneg (hw t)]
    calc
      (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) * w t ≤
          (2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ))) * w t :=
        mul_le_mul_of_nonneg_right (treeParent_weight_le n t) (hw t)
      _ = 2 * ((2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * w t) := by ring
  · classical
    change (w.sum fun t a ↦ a • treeFunction n t) ≤
      (Finsupp.mapDomain TreeNode.parent w).sum fun t a ↦ a • treeFunction n t
    rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    apply Finsupp.sum_le_sum
    intro t _ α
    change w t * treeFunction n t α ≤ w t * treeFunction n (TreeNode.parent t) α
    exact mul_le_mul_of_nonneg_left (treeFunction_le_parent n t α) (hw t)

private theorem treeRho_bandProjection_le (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) :
    treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support.filter (fun t ↦ t ∈ treeBandSupport n B),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    rw [treeRho, treeBandProjection, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp ht).2]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

private theorem treeRho_finiteBandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support.filter (fun t ↦ treeBandOfNode n t ∈ Λ),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    have hp (t : TreeNode n) :
        (∃ B ∈ Λ, t ∈ treeBandSupport n B) ↔ treeBandOfNode n t ∈ Λ := by
      constructor
      · rintro ⟨B, hB, ht⟩
        exact treeBandOfNode_eq_of_mem n t B ht ▸ hB
      · intro ht
        exact ⟨treeBandOfNode n t, ht, node_mem_its_treeBand n t⟩
    rw [treeRho, finiteBandProjection, Finsupp.sum, Finsupp.support_filter]
    simp_rw [hp]
    apply Finset.sum_congr rfl
    intro t ht
    have happly : (w.filter fun x ↦ treeBandOfNode n x ∈ Λ) t = w t :=
      Finsupp.filter_apply_pos (fun x ↦ treeBandOfNode n x ∈ Λ) w
        (Finset.mem_filter.mp ht).2
    rw [happly]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)

private theorem sum_treeRho_bandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  rw [← treeRho_finiteBandProjection]
  exact treeRho_finiteBandProjection_le n Λ w

/-- Paper Lemma `lem:sharp-subsequence`. -/
theorem tree_sharp_subsequence
    (n : ℕ) (w : ℕ → TreeCoefficients n) (C : ℝ)
    (hw : ∀ m, treeRho n (w m) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : TreeBandIndex n,
      ∃ l : ℝ, Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w (φ m))))
        atTop (nhds l) := by
  classical
  letI : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  letI : Countable (TreeNonterminal n) := by
    unfold TreeNonterminal
    infer_instance
  let D := max C 0
  let y : ℕ → TreeBandIndex n → Set.Icc (0 : ℝ) D := fun m B ↦
    ⟨treeRho n (treeBandProjection n B (w m)),
      treeRho_nonneg n _,
      (treeRho_bandProjection_le n B (w m)).trans
        ((hw m).trans (le_max_left C 0))⟩
  letI : SeqCompactSpace (TreeBandIndex n → Set.Icc (0 : ℝ) D) := inferInstance
  obtain ⟨l, _, φ, hφ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ
      (X := TreeBandIndex n → Set.Icc (0 : ℝ) D)) (x := y) (fun _ ↦ Set.mem_univ _)
  refine ⟨φ, hφ, fun B ↦ ⟨(l B).1, ?_⟩⟩
  have hcoord := tendsto_pi_nhds.mp hlim B
  simpa [y, Function.comp_def] using tendsto_subtype_rng.mp hcoord

/-- The bands occurring in infinitely many supports of a sequence. -/
def recurrentBands (n : ℕ) (w : ℕ → TreeCoefficients n) : Set (TreeBandIndex n) :=
  {B | Set.Infinite {m | (treeBandProjection n B (w m)).support.Nonempty}}

private noncomputable def lastBandOccurrence (n : ℕ)
    (w : ℕ → TreeCoefficients n) (B : TreeBandIndex n) : ℕ := by
  classical
  let S : Set ℕ := {m | (treeBandProjection n B (w m)).support.Nonempty}
  exact if h : S.Finite then h.toFinset.sup id else 0

private theorem le_lastBandOccurrence (n : ℕ) (w : ℕ → TreeCoefficients n)
    (B : TreeBandIndex n)
    (hfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite)
    {m : ℕ} (hm : (treeBandProjection n B (w m)).support.Nonempty) :
    m ≤ lastBandOccurrence n w B := by
  classical
  rw [lastBandOccurrence, dif_pos hfinite]
  exact Finset.le_sup (s := hfinite.toFinset) (f := id) (by simpa using hm)

/-- Paper Lemma `lem:trim`. -/
theorem tree_trim
    (n : ℕ) (x : ℕ → TreeComponent n) (w : ℕ → TreeCoefficients n)
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ m, 0 ≤ w m)
    (hdom : ∀ m, (x m).1 ≤ treeOperator n (w m))
    (hrho : ∀ m, treeRho n (w m) < 1 + ε / 4)
    (hsharp : ∀ B : TreeBandIndex n, ∃ l : ℝ,
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds l)) :
    ∃ w' : ℕ → TreeCoefficients n,
      (∀ m, 0 ≤ w' m ∧ (x m).1 ≤ treeOperator n (w' m) ∧
        treeRho n (w' m) < 1 + ε / 2) ∧
      (recurrentBands n w').Finite := by
  classical
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let lam : TreeBandIndex n → ℝ := fun B ↦ Classical.choose (hsharp B)
  have hlamlim (B : TreeBandIndex n) :
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (lam B)) := Classical.choose_spec (hsharp B)
  have hlamnonneg (B : TreeBandIndex n) : 0 ≤ lam B := by
    apply ge_of_tendsto (hlamlim B)
    exact Filter.Eventually.of_forall fun m ↦ treeRho_nonneg n _
  have hlamfinite (S : Finset (TreeBandIndex n)) :
      ∑ B ∈ S, lam B ≤ 1 + ε / 4 := by
    have hlim : Tendsto
        (fun m ↦ ∑ B ∈ S, treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (∑ B ∈ S, lam B)) :=
      tendsto_finsetSum S fun B _ ↦ hlamlim B
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun m ↦
      (sum_treeRho_bandProjection_le n S (w m)).trans (hrho m).le
  have hlamsummable : Summable lam :=
    summable_of_sum_le (fun B ↦ hlamnonneg B) hlamfinite
  have hlamtsum_le : ∑' B, lam B ≤ 1 + ε / 4 :=
    Real.tsum_le_of_sum_le (fun B ↦ hlamnonneg B) hlamfinite
  let tailBudget : ℝ := ε / (8 * M)
  have htailBudget : 0 < tailBudget := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨Λ₀, hΛ₀⟩ :=
    (Metric.tendsto_atTop.mp hlamsummable.hasSum) tailBudget htailBudget
  let Λ : Finset (TreeBandIndex n) := insert none Λ₀
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hΛapprox : dist (∑ B ∈ Λ, lam B) (∑' B, lam B) < tailBudget :=
    hΛ₀ Λ (Finset.subset_insert none Λ₀)
  have hΛsum_le : ∑ B ∈ Λ, lam B ≤ ∑' B, lam B :=
    Summable.sum_le_tsum Λ (fun B _ ↦ hlamnonneg B) hlamsummable
  have htail (F : Finset (TreeBandIndex n))
      (hF : ∀ B ∈ F, B ∉ Λ) : ∑ B ∈ F, lam B < tailBudget := by
    have hdis : Disjoint Λ F := Finset.disjoint_left.mpr fun B hBΛ hBF ↦
      (hF B hBF) hBΛ
    have hunion : (∑ B ∈ Λ, lam B) + ∑ B ∈ F, lam B =
        ∑ B ∈ Λ ∪ F, lam B := by
      exact (Finset.sum_union hdis).symm
    have hle : ∑ B ∈ Λ ∪ F, lam B ≤ ∑' B, lam B :=
      Summable.sum_le_tsum (Λ ∪ F) (fun B _ ↦ hlamnonneg B) hlamsummable
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hΛsum_le)] at hΛapprox
    linarith
  letI : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  letI : Countable (TreeNonterminal n) := by
    unfold TreeNonterminal
    infer_instance
  letI : Encodable (TreeBandIndex n) := Encodable.ofCountable _
  let a : ℝ := ε / (16 * M)
  have ha : 0 < a := div_pos hε (mul_pos (by norm_num) hM)
  let δ : TreeBandIndex n → ℝ := fun B ↦ a * (1 / 2 : ℝ) ^ Encodable.encode B
  have hδpos (B : TreeBandIndex n) : 0 < δ B :=
    mul_pos ha (pow_pos (by norm_num) _)
  have hgeom : Summable (fun B : TreeBandIndex n ↦
      (1 / 2 : ℝ) ^ Encodable.encode B) := by
    simpa [Function.comp_def] using
      summable_geometric_two.comp_injective Encodable.encode_injective
  have hgeom_tsum_le :
      ∑' B : TreeBandIndex n, (1 / 2 : ℝ) ^ Encodable.encode B ≤ 2 := by
    calc
      ∑' B : TreeBandIndex n, (1 / 2 : ℝ) ^ Encodable.encode B ≤
          ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        hgeom.tsum_le_tsum_of_inj Encodable.encode Encodable.encode_injective
          (fun k _ ↦ by positivity) (fun _ ↦ le_rfl) summable_geometric_two
      _ = 2 := tsum_geometric_two
  have hδsummable : Summable δ := by
    exact hgeom.mul_left a
  have hδfinite (F : Finset (TreeBandIndex n)) :
      ∑ B ∈ F, δ B ≤ tailBudget := by
    calc
      ∑ B ∈ F, δ B ≤ ∑' B, δ B :=
        Summable.sum_le_tsum F (fun B _ ↦ (hδpos B).le) hδsummable
      _ = a * ∑' B : TreeBandIndex n, (1 / 2 : ℝ) ^ Encodable.encode B := by
        exact tsum_mul_left
      _ ≤ a * 2 := mul_le_mul_of_nonneg_left hgeom_tsum_le ha.le
      _ = tailBudget := by
        dsimp [a, tailBudget, M]
        field_simp
        ring
  have hcutoff (B : TreeBandIndex n) : ∃ N : ℕ, ∀ m ≥ N,
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp (hlamlim B)) (δ B) (hδpos B)
    refine ⟨N, fun m hm ↦ ?_⟩
    have habs := hN m hm
    rw [Real.dist_eq] at habs
    have hsub : treeRho n (treeBandProjection n B (w m)) - lam B < δ B :=
      (le_abs_self _).trans_lt habs
    linarith
  let N : TreeBandIndex n → ℕ := fun B ↦ Classical.choose (hcutoff B)
  have hN (B : TreeBandIndex n) (m : ℕ) (hm : N B ≤ m) :
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B :=
    Classical.choose_spec (hcutoff B) m hm
  let removedBands : ℕ → Finset (TreeBandIndex n) := fun m ↦
    (bandsAt n (w m)).filter fun B ↦ B ∉ Λ ∧ N B ≤ m
  let r : ℕ → TreeCoefficients n := fun m ↦
    finiteBandProjection n (removedBands m) (w m)
  let w' : ℕ → TreeCoefficients n := fun m ↦
    w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n)
  have hr_nonneg (m : ℕ) : 0 ≤ r m := by
    intro t
    by_cases ht : treeBandOfNode n t ∈ removedBands m
    · change 0 ≤ finiteBandProjection n (removedBands m) (w m) t
      rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1 ht]
      exact hw m t
    · change 0 ≤ finiteBandProjection n (removedBands m) (w m) t
      rw [(finiteBandProjection_apply n (removedBands m) (w m) t).2 ht]
  have hkeep_nonneg (m : ℕ) : 0 ≤ w m - r m := by
    intro t
    by_cases ht : treeBandOfNode n t ∈ removedBands m
    · change 0 ≤ w m t - finiteBandProjection n (removedBands m) (w m) t
      rw [
        (finiteBandProjection_apply n (removedBands m) (w m) t).1 ht]
      simp
    · change 0 ≤ w m t - finiteBandProjection n (removedBands m) (w m) t
      rw [
        (finiteBandProjection_apply n (removedBands m) (w m) t).2 ht]
      simpa using hw m t
  have hrho_r (m : ℕ) : treeRho n (r m) < ε / (4 * M) := by
    have hRB (B : TreeBandIndex n) (hB : B ∈ removedBands m) :
        treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
      exact hN B m (Finset.mem_filter.mp hB).2.2
    have houtside (B : TreeBandIndex n) (hB : B ∈ removedBands m) : B ∉ Λ :=
      (Finset.mem_filter.mp hB).2.1
    change treeRho n (finiteBandProjection n (removedBands m) (w m)) < _
    rw [treeRho_finiteBandProjection]
    calc
      ∑ B ∈ removedBands m, treeRho n (treeBandProjection n B (w m)) ≤
          ∑ B ∈ removedBands m, (lam B + δ B) := by
        apply Finset.sum_le_sum
        intro B hB
        exact (hRB B hB).le
      _ = (∑ B ∈ removedBands m, lam B) + ∑ B ∈ removedBands m, δ B := by
        rw [← Finset.sum_add_distrib]
      _ < tailBudget + tailBudget :=
        add_lt_add_of_lt_of_le (htail (removedBands m) houtside)
          (hδfinite (removedBands m))
      _ = ε / (4 * M) := by
        dsimp [tailBudget]
        field_simp
        ring
  refine ⟨w', ?_, ?_⟩
  · intro m
    have hroot_nonneg : 0 ≤
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n) := by
      intro t
      change 0 ≤ (M * treeRho n (r m)) * treeBasis (TreeNode.root n) t
      apply mul_nonneg (mul_nonneg hM.le (treeRho_nonneg n (r m)))
      by_cases ht : t = TreeNode.root n <;> simp [treeBasis, ht]
    refine ⟨add_nonneg (hkeep_nonneg m) hroot_nonneg, ?_, ?_⟩
    · calc
        (x m).1 ≤ treeOperator n (w m) := hdom m
        _ = treeOperator n (w m - r m) + treeOperator n (r m) := by
          rw [← treeOperator_add]
          congr 1
          abel
        _ ≤ treeOperator n (w m - r m) +
            (M * treeRho n (r m)) • treeFunction n (TreeNode.root n) := by
          exact add_le_add le_rfl
            (treeOperator_le_root_of_nonneg n (r m) (hr_nonneg m))
        _ = treeOperator n (w' m) := by
          change _ = treeOperator n
            (w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n))
          rw [treeOperator_add, treeOperator_smul, treeBasis,
            treeOperator_single, one_smul]
    · have hkeep_le : w m - r m ≤ w m := by
        exact sub_le_self _ (hr_nonneg m)
      calc
        treeRho n (w' m) ≤ treeRho n (w m - r m) +
            treeRho n ((M * treeRho n (r m)) • treeBasis (TreeNode.root n)) :=
          treeRho_add_le n _ _
        _ ≤ treeRho n (w m) + M * treeRho n (r m) := by
          apply add_le_add
          · exact treeRho_mono_of_nonneg n (hkeep_nonneg m) hkeep_le
          · rw [treeRho_smul, abs_of_nonneg
              (mul_nonneg hM.le (treeRho_nonneg n (r m)))]
            simp [treeBasis, treeRho, TreeNode.root, TreeNode.level]
        _ < 1 + ε / 2 := by
          have hMr : M * treeRho n (r m) < ε / 4 := by
            calc
              M * treeRho n (r m) < M * (ε / (4 * M)) :=
                mul_lt_mul_of_pos_left (hrho_r m) hM
              _ = ε / 4 := by field_simp
          linarith [hrho m]
  · apply Set.Finite.subset Λ.finite_toSet
    intro B hBrec
    by_contra hBΛ
    have hoccFinite :
        {m | (treeBandProjection n B (w' m)).support.Nonempty}.Finite := by
      apply (Finset.finite_toSet (Finset.range (N B))).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hmN
      have hNm : N B ≤ m := Nat.le_of_not_gt hmN
      rcases hm with ⟨t, ht⟩
      have htw' : t ∈ (w' m).support ∧ t ∈ treeBandSupport n B := by
        simpa [treeBandProjection] using ht
      have htBand : treeBandOfNode n t = B :=
        treeBandOfNode_eq_of_mem n t B htw'.2
      have htroot : t ≠ TreeNode.root n := by
        intro htr
        have : B = none := by
          rw [← htBand, htr]
          simp [treeBandOfNode]
        exact hBΛ (this ▸ hnoneΛ)
      have hwt_ne : w m t ≠ 0 := by
        intro hzero
        have hrzero : r m t = 0 := by
          by_cases htR : treeBandOfNode n t ∈ removedBands m
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1 htR,
              hzero]
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).2 htR]
        have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
          simp [treeBasis, htroot]
        have htne := Finsupp.mem_support_iff.mp htw'.1
        change (w m - r m +
          (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
        simp [Finsupp.add_apply, Finsupp.sub_apply, hzero, hrzero,
          Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
      have hBbands : B ∈ bandsAt n (w m) := by
        rw [mem_bandsAt_iff, treeBandProjection_support_nonempty_iff]
        exact ⟨t, Finsupp.mem_support_iff.mpr hwt_ne, htBand⟩
      have hBR : B ∈ removedBands m := by
        apply Finset.mem_filter.mpr
        exact ⟨hBbands, hBΛ, hNm⟩
      have hrval : r m t = w m t := by
        change finiteBandProjection n (removedBands m) (w m) t = w m t
        rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1]
        exact htBand ▸ hBR
      have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
        simp [treeBasis, htroot]
      have htne := Finsupp.mem_support_iff.mp htw'.1
      change (w m - r m +
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
      simp [Finsupp.add_apply, Finsupp.sub_apply, hrval,
        Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
    exact hBrec hoccFinite

/-- Paper Lemma `lem:thinning`. -/
theorem tree_thinning
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hΛ : recurrentBands n w ⊆ (Λ : Set (TreeBandIndex n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w (φ m))).support.Nonempty}.Subsingleton := by
  classical
  let φ : ℕ → ℕ := fun m ↦ Nat.rec 0 (fun _ r ↦
    max (r + 1) (((bandsAt n (w r)).filter fun B ↦ B ∉ Λ).sup fun B ↦
      lastBandOccurrence n w B + 1)) m
  have hφ_succ (m : ℕ) : φ (m + 1) =
      max (φ m + 1) (((bandsAt n (w (φ m))).filter fun B ↦ B ∉ Λ).sup fun B ↦
        lastBandOccurrence n w B + 1) := by simp [φ]
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro m
    rw [hφ_succ]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  refine ⟨φ, hφ, ?_⟩
  intro B hBΛ
  have hBfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite := by
    apply Set.not_infinite.mp
    intro hInf
    exact hBΛ (hΛ hInf)
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hBbands : B ∈ bandsAt n (w (φ i)) :=
      (mem_bandsAt_iff n _ B).mpr hi
    have hBfilter : B ∈ (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (i + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ i + 1)
        (((bandsAt n (w (φ i))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (i + 1) ≤ φ j := hφ.monotone (Nat.succ_le_iff.mpr hijlt)
    have hjlast := le_lastBandOccurrence n w B hBfinite hj
    omega
  · have hBbands : B ∈ bandsAt n (w (φ j)) :=
      (mem_bandsAt_iff n _ B).mpr hj
    have hBfilter : B ∈ (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ :=
      Finset.mem_filter.mpr ⟨hBbands, hBΛ⟩
    have hlast_lt_succ : lastBandOccurrence n w B < φ (j + 1) := by
      have hle := Finset.le_sup
        (s := (bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ)
        (f := fun B ↦ lastBandOccurrence n w B + 1) hBfilter
      change lastBandOccurrence n w B + 1 ≤ _ at hle
      have hle' := hle.trans (le_max_right (φ j + 1)
        (((bandsAt n (w (φ j))).filter fun B ↦ B ∉ Λ).sup fun B ↦
          lastBandOccurrence n w B + 1))
      rw [← hφ_succ] at hle'
      omega
    have hsucc_le : φ (j + 1) ≤ φ i := hφ.monotone (Nat.succ_le_iff.mpr hjilt)
    have hilast := le_lastBandOccurrence n w B hBfinite hi
    omega

private theorem treeOperator_apply_eq_zero_of_outside_support
    (n : ℕ) (w : TreeCoefficients n) {α : TreeProduct n}
    (hα : α ∉ finiteCylinderUnion n w.support) :
    treeOperator n w α = 0 := by
  classical
  rw [treeOperator_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hnot : α ∉ treeCylinder n t := by
    intro hmem
    apply hα
    simp only [finiteCylinderUnion, Set.mem_iUnion]
    exact ⟨⟨t, ht⟩, hmem⟩
  rw [treeFunction_apply_of_notMem n t hnot, mul_zero]

/-- Paper Lemma `lem:transient`. -/
theorem tree_transient
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hnone : none ∈ Λ)
    (hdis : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w m)).support.Nonempty}.Subsingleton) :
    let v := fun m ↦ w m - finiteBandProjection n Λ (w m)
    (Pairwise fun i j ↦ ParentDisjoint ((v i).support : Set (TreeNode n))
      ((v j).support : Set (TreeNode n))) ∧
    ∀ z : BoundedContinuousFunction (TreeProduct n) ℝ,
      0 ≤ z → (∀ m, z ≤ treeOperator n (v m)) → z = 0 := by
  classical
  dsimp
  let v : ℕ → TreeCoefficients n := fun m ↦
    w m - finiteBandProjection n Λ (w m)
  have hv_apply (m : ℕ) (t : TreeNode n) :
      v m t = if treeBandOfNode n t ∈ Λ then 0 else w m t := by
    change (w m - finiteBandProjection n Λ (w m)) t = _
    rw [Finsupp.sub_apply]
    by_cases hB : treeBandOfNode n t ∈ Λ
    · rw [(finiteBandProjection_apply n Λ (w m) t).1 hB]
      simp [hB]
    · rw [(finiteBandProjection_apply n Λ (w m) t).2 hB]
      simp [hB]
  have hv_band_notMem {m : ℕ} {t : TreeNode n} (ht : t ∈ (v m).support) :
      treeBandOfNode n t ∉ Λ := by
    intro hB
    have htne := Finsupp.mem_support_iff.mp ht
    rw [hv_apply, if_pos hB] at htne
    exact htne rfl
  have hv_root_notMem (m : ℕ) : TreeNode.root n ∉ (v m).support := by
    intro ht
    have hB := hv_band_notMem ht
    apply hB
    simpa [treeBandOfNode] using hnone
  have hpair : Pairwise fun i j ↦
      ParentDisjoint ((v i).support : Set (TreeNode n))
        ((v j).support : Set (TreeNode n)) := by
    intro i j hij
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq.1 with ⟨ti, hti, hpti⟩
    rcases hq.2 with ⟨tj, htj, hptj⟩
    have htiroot : ti ≠ TreeNode.root n := fun h ↦ hv_root_notMem i (h ▸ hti)
    have htjroot : tj ≠ TreeNode.root n := fun h ↦ hv_root_notMem j (h ▸ htj)
    let B := treeBandOfNode n ti
    have hBnot : B ∉ Λ := hv_band_notMem hti
    have hBsame : treeBandOfNode n tj = B := by
      change treeBandOfNode n tj = treeBandOfNode n ti
      rw [treeBandOfNode, dif_neg htjroot, treeBandOfNode, dif_neg htiroot]
      congr 2
      exact hptj.trans hpti.symm
    have hwti : ti ∈ (w i).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp hti
      rw [hv_apply, if_neg hBnot] at hvne
      exact hvne
    have hBt_i : (treeBandProjection n B (w i)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w i)).mpr
        ⟨ti, hwti, rfl⟩
    have hwjt : tj ∈ (w j).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp htj
      rw [hv_apply, if_neg (hBsame ▸ hBnot)] at hvne
      exact hvne
    have hBt_j : (treeBandProjection n B (w j)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w j)).mpr
        ⟨tj, hwjt, hBsame⟩
    exact hij ((hdis B hBnot) hBt_i hBt_j)
  refine ⟨hpair, ?_⟩
  intro z hzpos hzlower
  apply le_antisymm
  · exact commonLower_le_zero_of_parentDisjoint_subseq n
      (fun m ↦ (v m).support) hpair id Function.injective_id hv_root_notMem
      (fun m ↦ treeOperator n (v m))
      (fun m α hα ↦ treeOperator_apply_eq_zero_of_outside_support n (v m) hα)
      hzlower
  · exact hzpos

/-- Paper Proposition `prop:moderated`. -/
theorem component_moderated
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧
      (∀ m, (x m).1 ≤ treeOperator n w) ∧ treeRho n w ≤ 2 + ε := by
  classical
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  choose w hw hmajor hrho using fun m ↦
    exists_treeMajorant_lt n (x m).1 hquarter
  have hdom (m : ℕ) : (x m).1 ≤ treeOperator n (w m) := by
    have hxpos' : 0 ≤ (x m).1 := hxpos m
    simpa [abs_of_nonneg hxpos'] using hmajor m
  have hrho' (m : ℕ) : treeRho n (w m) < 1 + ε / 4 := by
    have hn := hxnorm m
    change treeSeminorm n (x m).1 ≤ 1 at hn
    linarith [hrho m]
  obtain ⟨φ, hφ, hsharp⟩ :=
    tree_sharp_subsequence n w (1 + ε / 4) (fun m ↦ (hrho' m).le)
  have hφid (m : ℕ) : m ≤ φ m := hφ.id_le m
  have hdomφ (m : ℕ) : (x m).1 ≤ treeOperator n (w (φ m)) := by
    have hxm := hxmono (hφid m)
    change (x m).1 ≤ (x (φ m)).1 at hxm
    exact hxm.trans (hdom (φ m))
  obtain ⟨wt, hwt, hrec⟩ := tree_trim n x (fun m ↦ w (φ m)) hε
    (fun m ↦ hw (φ m)) hdomφ (fun m ↦ hrho' (φ m)) hsharp
  let Λ : Finset (TreeBandIndex n) := insert none hrec.toFinset
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hrecΛ : recurrentBands n wt ⊆ (Λ : Set (TreeBandIndex n)) := by
    intro B hB
    simp only [Λ, Finset.mem_coe, Finset.mem_insert]
    exact Or.inr (hrec.mem_toFinset.mpr hB)
  obtain ⟨ψ, hψ, hthin⟩ := tree_thinning n wt Λ hrecΛ
  have hψid (m : ℕ) : m ≤ ψ m := hψ.id_le m
  let W : ℕ → TreeCoefficients n := fun m ↦ wt (ψ m)
  have hWpos (m : ℕ) : 0 ≤ W m := (hwt (ψ m)).1
  have hWdom (m : ℕ) : (x m).1 ≤ treeOperator n (W m) := by
    have hxm := hxmono (hψid m)
    change (x m).1 ≤ (x (ψ m)).1 at hxm
    exact hxm.trans (hwt (ψ m)).2.1
  have hWrho (m : ℕ) : treeRho n (W m) < 1 + ε / 2 :=
    (hwt (ψ m)).2.2
  have hthinW : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (W m)).support.Nonempty}.Subsingleton :=
    hthin
  let U₀ : ℕ → TreeCoefficients n := fun m ↦ finiteBandProjection n Λ (W m)
  let V : ℕ → TreeCoefficients n := fun m ↦ W m - U₀ m
  let U : ℕ → TreeCoefficients n := fun m ↦ treeUpshift n (U₀ m)
  have hU₀pos (m : ℕ) : 0 ≤ U₀ m := by
    intro t
    by_cases ht : treeBandOfNode n t ∈ Λ
    · change 0 ≤ finiteBandProjection n Λ (W m) t
      rw [(finiteBandProjection_apply n Λ (W m) t).1 ht]
      exact hWpos m t
    · change 0 ≤ finiteBandProjection n Λ (W m) t
      rw [(finiteBandProjection_apply n Λ (W m) t).2 ht]
  have hVpos (m : ℕ) : 0 ≤ V m := by
    intro t
    by_cases ht : treeBandOfNode n t ∈ Λ
    · change 0 ≤ W m t - finiteBandProjection n Λ (W m) t
      rw [(finiteBandProjection_apply n Λ (W m) t).1 ht]
      simp
    · change 0 ≤ W m t - finiteBandProjection n Λ (W m) t
      rw [(finiteBandProjection_apply n Λ (W m) t).2 ht]
      simpa using hWpos m t
  have hUpos (m : ℕ) : 0 ≤ U m :=
    Finsupp.mapDomain_nonneg (hU₀pos m)
  let P : Finset (TreeNode n) := treeBandParents n Λ
  have hUsupport (m : ℕ) : (U m).support ⊆ P :=
    treeUpshift_support_subset_bandParents n Λ (W m)
  have hUrho (m : ℕ) : treeRho n (U m) < 2 + ε := by
    calc
      treeRho n (U m) ≤ 2 * treeRho n (U₀ m) :=
        (treeUpshift_basic n (U₀ m) (hU₀pos m)).1
      _ ≤ 2 * treeRho n (W m) :=
        mul_le_mul_of_nonneg_left (treeRho_finiteBandProjection_le n Λ (W m))
          (by norm_num)
      _ < 2 * (1 + ε / 2) := mul_lt_mul_of_pos_left (hWrho m) (by norm_num)
      _ = 2 + ε := by ring
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let D : ℝ := M * (2 + ε)
  have htwoeps : 0 < 2 + ε := by linarith
  have hD : 0 < D := mul_pos hM htwoeps
  have hUcoord (m : ℕ) (t : TreeNode n) : |U m t| ≤ D := by
    have hone : |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := by
      by_cases ht : U m t = 0
      · rw [ht, abs_zero]
        exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      · exact Finset.single_le_sum (fun q _ ↦ abs_nonneg (U m q))
          (Finsupp.mem_support_iff.mpr ht)
    calc
      |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := hone
      _ ≤ M * treeRho n (U m) := treeRho_controls_sum n (U m)
      _ ≤ M * (2 + ε) := mul_le_mul_of_nonneg_left (hUrho m).le hM.le
      _ = D := rfl
  let y : ℕ → ↥P → Set.Icc (-D) D := fun m t ↦
    ⟨U m t.1, by
      have habs := hUcoord m t.1
      exact ⟨(neg_le_neg habs).trans (neg_abs_le _), (le_abs_self _).trans habs⟩⟩
  letI : SeqCompactSpace (↥P → Set.Icc (-D) D) := inferInstance
  obtain ⟨l, _, θ, hθ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ (X := ↥P → Set.Icc (-D) D))
      (x := y) (fun _ ↦ Set.mem_univ _)
  let coeff : TreeNode n → ℝ := fun t ↦
    if ht : t ∈ P then (l ⟨t, ht⟩).1 else 0
  let u : TreeCoefficients n := Finsupp.onFinset P coeff (by
    intro t ht
    by_contra htP
    simp [coeff, htP] at ht)
  have hcoordlim (t : TreeNode n) :
      Tendsto (fun m ↦ U (θ m) t) atTop (nhds (u t)) := by
    by_cases ht : t ∈ P
    · have htend := tendsto_pi_nhds.mp hlim ⟨t, ht⟩
      have htend' := tendsto_subtype_rng.mp htend
      simpa [y, u, coeff, ht, Function.comp_def] using htend'
    · have hzero (m : ℕ) : U (θ m) t = 0 := by
        by_contra hne
        exact ht (hUsupport (θ m) (Finsupp.mem_support_iff.mpr hne))
      have huzero : u t = 0 := by simp [u, coeff, ht]
      simp only [hzero, huzero]
      exact tendsto_const_nhds
  have hupos : 0 ≤ u := by
    intro t
    apply ge_of_tendsto (hcoordlim t)
    exact Filter.Eventually.of_forall fun m ↦ hUpos (θ m) t
  have huSupport : u.support ⊆ P := Finsupp.support_onFinset_subset
  have hTop_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeOperator n q = ∑ t ∈ P, q t • treeFunction n t := by
    rw [treeOperator]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hRho_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeRho n q = ∑ t ∈ P,
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |q t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hToplim : Tendsto (fun m ↦ treeOperator n (U (θ m))) atTop
      (nhds (treeOperator n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P, U (θ m) t • treeFunction n t) atTop
        (nhds (∑ t ∈ P, u t • treeFunction n t)) :=
      tendsto_finsetSum P fun t _ ↦ (hcoordlim t).smul_const (treeFunction n t)
    rw [hTop_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hTop_repr (U (θ m)) (hUsupport (θ m))
  have hRholim : Tendsto (fun m ↦ treeRho n (U (θ m))) atTop
      (nhds (treeRho n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |U (θ m) t|) atTop
        (nhds (∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |u t|)) :=
      tendsto_finsetSum P fun t _ ↦ tendsto_const_nhds.mul (hcoordlim t).abs
    rw [hRho_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hRho_repr (U (θ m)) (hUsupport (θ m))
  have hurho : treeRho n u ≤ 2 + ε := by
    apply le_of_tendsto hRholim
    exact Filter.Eventually.of_forall fun m ↦ (hUrho (θ m)).le
  have htransient_subseq (χ : ℕ → ℕ) (hχ : Function.Injective χ)
      (z : BoundedContinuousFunction (TreeProduct n) ℝ) (hz : 0 ≤ z)
      (hzlower : ∀ k, z ≤ treeOperator n (V (χ k))) : z = 0 := by
    have hsub : ∀ B ∉ Λ,
        {k | (treeBandProjection n B (W (χ k))).support.Nonempty}.Subsingleton := by
      intro B hB i hi j hj
      exact hχ (hthinW B hB hi hj)
    have htr := (tree_transient n (fun k ↦ W (χ k)) Λ hnoneΛ hsub).2
    apply htr z hz
    intro k
    change z ≤ treeOperator n
      (W (χ k) - finiteBandProjection n Λ (W (χ k)))
    exact hzlower k
  refine ⟨u, hupos, ?_, hurho⟩
  intro j α
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp hToplim) η hη
  let K : ℕ := max j m₀
  let χ : ℕ → ℕ := fun k ↦ θ (k + K)
  have hχ : Function.Injective χ := hθ.injective.comp fun a b hab ↦ by
    omega
  have hclose (k : ℕ) :
      ‖treeOperator n (U (χ k)) - treeOperator n u‖ < η := by
    have hk : m₀ ≤ k + K := le_trans (le_max_right j m₀) (Nat.le_add_left K k)
    have := hm₀ (k + K) hk
    rw [dist_eq_norm_sub] at this
    exact this
  have happrox (k : ℕ) :
      treeOperator n (U (χ k)) ≤ treeOperator n u +
        η • treeFunction n (TreeNode.root n) := by
    let d := treeOperator n (U (χ k)) - treeOperator n u
    have habs : |d| ≤ η • treeFunction n (TreeNode.root n) := by
      calc
        |d| ≤ ‖d‖ • treeFunction n (TreeNode.root n) :=
          abs_le_norm_smul_root n d
        _ ≤ η • treeFunction n (TreeNode.root n) := by
          intro β
          simpa [treeFunction_root] using (hclose k).le
    calc
      treeOperator n (U (χ k)) = d + treeOperator n u := by
        dsimp [d]
        abel
      _ ≤ |d| + treeOperator n u := add_le_add (le_abs_self d) le_rfl
      _ ≤ η • treeFunction n (TreeNode.root n) + treeOperator n u :=
        add_le_add habs le_rfl
      _ = treeOperator n u + η • treeFunction n (TreeNode.root n) := add_comm _ _
  let b : BoundedContinuousFunction (TreeProduct n) ℝ :=
    treeOperator n u + η • treeFunction n (TreeNode.root n)
  let z : BoundedContinuousFunction (TreeProduct n) ℝ := ((x j).1 - b)⁺
  have hzpos : 0 ≤ z := posPart_nonneg _
  have hzlower (k : ℕ) : z ≤ treeOperator n (V (χ k)) := by
    have hjχ : j ≤ χ k := by
      have hK : j ≤ k + K := le_trans (le_max_left j m₀) (Nat.le_add_left K k)
      exact hK.trans (hθ.id_le (k + K))
    have hxjχ := hxmono hjχ
    change (x j).1 ≤ (x (χ k)).1 at hxjχ
    have hxW : (x j).1 ≤ treeOperator n (W (χ k)) :=
      hxjχ.trans (hWdom (χ k))
    have hdecomp : treeOperator n (W (χ k)) =
        treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := by
      rw [← treeOperator_add]
      congr 1
      dsimp [V]
      abel
    have hup := (treeUpshift_basic n (U₀ (χ k)) (hU₀pos (χ k))).2
    have hmain : (x j).1 ≤ b + treeOperator n (V (χ k)) := by
      calc
        (x j).1 ≤ treeOperator n (W (χ k)) := hxW
        _ = treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := hdecomp
        _ ≤ treeOperator n (U (χ k)) + treeOperator n (V (χ k)) :=
          add_le_add hup le_rfl
        _ ≤ b + treeOperator n (V (χ k)) :=
          add_le_add (happrox k) le_rfl
    have hdiff : (x j).1 - b ≤ treeOperator n (V (χ k)) := by
      rw [sub_le_iff_le_add]
      simpa [add_comm] using hmain
    change ((x j).1 - b) ⊔ 0 ≤ treeOperator n (V (χ k))
    exact sup_le hdiff (treeOperator_nonneg n (V (χ k)) (hVpos (χ k)))
  have hz0 := htransient_subseq χ hχ z hzpos hzlower
  have hxb : (x j).1 ≤ b := by
    rw [← sub_nonpos]
    exact (le_posPart ((x j).1 - b)).trans_eq hz0
  have hpoint := hxb α
  simpa [b, treeFunction_root] using hpoint

/-- Paper Corollary `cor:weak-fatou`. -/
theorem component_weakFatou (n : ℕ) :
    IsWeakNakanoConstant (componentLatticeNorm n) 2 ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 := by
  have hseq : IsWeakSequentialNakanoConstant (componentLatticeNorm n) 2 := by
    refine ⟨by norm_num, ?_⟩
    intro x hxmono hxpos _ hxnorm ε hε
    obtain ⟨w, hw, hwupper, hwrho⟩ :=
      component_moderated n x hxmono hxpos hxnorm hε
    let y : TreeComponent n := ⟨treeOperator n w, treeOperator_mem_treeSublattice n w⟩
    refine ⟨y, ?_, ?_, ?_⟩
    · exact treeOperator_nonneg n w hw
    · exact hwupper
    · change treeSeminorm n (treeOperator n w) ≤ 2 + ε
      apply (treeSeminorm_le_of_majorant n (treeOperator n w) w hw ?_).trans hwrho
      rw [abs_of_nonneg (treeOperator_nonneg n w hw)]
  letI : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  letI : TopologicalSpace.SeparableSpace (TreeComponent n) :=
    VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
      (Set.countable_range (treeFunction n))
  have hNak : IsWeakNakanoConstant (componentLatticeNorm n) 2 :=
    weakNakano_of_weakSequentialNakano_p (Y := TreeComponent n) (K := 2)
      (componentLatticeNorm n) hseq
  exact ⟨hNak, weakFatou_of_weakNakano_p (componentLatticeNorm n) hNak⟩

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
  have hiter : ∀ k : ℕ, ∀ t : TreeNode n, TreeNode.level t + k = n →
      ((2 : ℝ) ^ n • componentTreeFunction n t) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
    intro k
    induction k with
    | zero =>
        intro t ht
        have hlevel : TreeNode.level t = n := by omega
        change componentLatticeNorm n ((2 : ℝ) ^ n • componentTreeFunction n t) ≤ 1
        rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
          (component_basic n).2.2.2 t hlevel]
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
        norm_num
    | succ k ih =>
        intro t ht
        have ht_nonterminal : TreeNode.level t < n := by omega
        let f : ℕ → TreeComponent n := fun m ↦
          (2 : ℝ) ^ n • componentTreeFunction n (TreeNode.child t ht_nonterminal m)
        have hf : ∀ m, f m ∈
            iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
          intro m
          apply ih
          have hlevelchild : TreeNode.level (TreeNode.child t ht_nonterminal m) =
              TreeNode.level t + 1 := by simp [TreeNode.child, TreeNode.level]
          rw [hlevelchild]
          omega
        have hchild := treeFunction_child_properties n t ht_nonterminal
        have hmono : Monotone
            (fun m ↦ componentTreeFunction n (TreeNode.child t ht_nonterminal m)) := by
          intro a b hab
          exact hchild.2.1 hab
        have hlub : IsLUB
            (Set.range fun m ↦ componentTreeFunction n
              (TreeNode.child t ht_nonterminal m)) (componentTreeFunction n t) := by
          constructor
          · rintro _ ⟨m, rfl⟩
            exact hchild.1 m |>.2
          · intro z hz
            change treeFunction n t ≤ z.1
            apply hchild.2.2.2
            rintro _ ⟨m, rfl⟩
            exact hz ⟨m, rfl⟩
        change ((2 : ℝ) ^ n • componentTreeFunction n t) ∈ orderAdherence
          (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k)
        refine ⟨ℕ, inferInstance, inferInstance, inferInstance, f, hf, ?_⟩
        simpa [f] using
          (orderConvergesTo_of_monotone_isLUB hmono hlub).smul ((2 : ℝ) ^ n)
  have hroot : componentTreeFunction n (TreeNode.root n) = componentRoot n := rfl
  have hmembership : ((2 : ℝ) ^ n • componentRoot n) ∈
      iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n := by
    rw [← hroot]
    apply hiter n (TreeNode.root n)
    simp [TreeNode.root, TreeNode.level]
  have hnorm : componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) =
      (2 : ℝ) ^ n := by
    rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
      (component_basic n).2.2.1, mul_one]
  exact ⟨(component_basic n).1, (component_basic n).2.1,
    (component_weakFatou n).2, hmembership, hnorm⟩

/-- The ambient product of all component spaces. -/
abbrev ComponentProduct := ∀ n : ℕ, TreeComponent n

/-- The usual `c₀` condition for the component norms. -/
def componentVanishes (x : ComponentProduct) : Prop :=
  Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0)

/-- The concrete `c₀`-sum as a vector sublattice of the component product. -/
noncomputable def componentC0Sublattice : VectorSublattice ComponentProduct where
  carrier := {x | componentVanishes x}
  zero_mem' := by
    change Tendsto (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) atTop (nhds 0)
    have hzero : (fun n ↦ componentLatticeNorm n (0 : TreeComponent n)) =
        fun _ ↦ 0 := by
      funext n
      exact (componentLatticeNorm n).eq_zero_iff 0 |>.2 rfl
    rw [hzero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n + y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · exact fun n ↦ (componentLatticeNorm n).add_le _ _
    · simpa using hx.add hy
  smul_mem' := by
    intro a x hx
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (a • x n)) atTop (nhds 0)
    have heq : (fun n ↦ componentLatticeNorm n (a • x n)) =
        fun n ↦ |a| * componentLatticeNorm n (x n) := by
      funext n
      exact (componentLatticeNorm n).smul a (x n)
    rw [heq]
    simpa using hx.const_mul |a|
  sup_mem' := by
    intro x y hx hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n)) atTop (nhds 0) at hx
    change Tendsto (fun n ↦ componentLatticeNorm n (y n)) atTop (nhds 0) at hy
    change Tendsto (fun n ↦ componentLatticeNorm n (x n ⊔ y n)) atTop (nhds 0)
    apply squeeze_zero
    · exact fun n ↦ (componentLatticeNorm n).nonneg _
    · intro n
      have habsx : componentLatticeNorm n |x n| = componentLatticeNorm n (x n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      have habsy : componentLatticeNorm n |y n| = componentLatticeNorm n (y n) := by
        apply le_antisymm
        · exact (componentLatticeNorm n).solid (by simp)
        · exact (componentLatticeNorm n).solid (by simp)
      calc
        componentLatticeNorm n (x n ⊔ y n) ≤
            componentLatticeNorm n (|x n| + |y n|) :=
          (componentLatticeNorm n).solid (by
            have hsum0 : (0 : TreeComponent n) ≤ |x n| + |y n| :=
              add_nonneg (abs_nonneg _) (abs_nonneg _)
            rw [abs_of_nonneg hsum0]
            exact FVLv.abs_sup_le_add_abs (x n) (y n))
        _ ≤ componentLatticeNorm n |x n| + componentLatticeNorm n |y n| :=
          (componentLatticeNorm n).add_le _ _
        _ = componentLatticeNorm n (x n) + componentLatticeNorm n (y n) := by
          rw [habsx, habsy]
    · simpa using hx.add hy

/-- The final space `X = c₀(X_n)`, using the underlying submodule carrier. -/
abbrev FinalSpace := ↥componentC0Sublattice.toSubmodule

/-- Inclusion of one component as a coordinate band of the final `c₀`-sum. -/
noncomputable def finalCoordinateEmbedding (n : ℕ) (z : TreeComponent n) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ z else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m (if h : m = n then h.symm ▸ z else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ z else 0)) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dif_neg hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩

@[simp] private theorem finalCoordinateEmbedding_same (n : ℕ) (z : TreeComponent n) :
    (finalCoordinateEmbedding n z).1 n = z := by
  simp [finalCoordinateEmbedding]

private theorem finalCoordinateEmbedding_ne (n m : ℕ) (h : m ≠ n)
    (z : TreeComponent n) : (finalCoordinateEmbedding n z).1 m = 0 := by
  simp [finalCoordinateEmbedding, h]

/-- Pointwise lattice operations on the final `c₀`-sum. -/
noncomputable instance finalSpaceLattice : Lattice FinalSpace where
  le := fun x y ↦ x.1 ≤ y.1
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ hxy hyz ↦ hxy.trans hyz
  le_antisymm := fun x y hxy hyx ↦ Subtype.ext (le_antisymm hxy hyx)
  sup := fun x y ↦ ⟨x.1 ⊔ y.1, componentC0Sublattice.sup_mem x.2 y.2⟩
  le_sup_left := fun _ _ ↦ le_sup_left
  le_sup_right := fun _ _ ↦ le_sup_right
  sup_le := fun _ _ _ hx hz ↦ sup_le hx hz
  inf := fun x y ↦ ⟨x.1 ⊓ y.1, componentC0Sublattice.inf_mem x.2 y.2⟩
  inf_le_left := fun _ _ ↦ inf_le_left
  inf_le_right := fun _ _ ↦ inf_le_right
  le_inf := fun _ _ _ hx hz ↦ le_inf hx hz

/-- Compatibility of addition and order on the final space. -/
instance finalSpaceIsOrderedAddMonoid : IsOrderedAddMonoid FinalSpace where
  add_le_add_left a b hab c := by
    intro n
    simpa [add_comm] using add_le_add_right (hab n) (c.1 n)

/-- The final `c₀`-sum is a real vector lattice. -/
noncomputable instance finalSpaceVectorLattice : VectorLattice FinalSpace where
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy n
    exact smul_le_smul_of_nonneg_left (hxy n) ha

/-- The supremum norm on the final `c₀`-sum. -/
noncomputable def finalNormValue (x : FinalSpace) : ℝ :=
  sSup (Set.range fun n ↦ componentLatticeNorm n (x.1 n))

private theorem finalNormValue_bddAbove (x : FinalSpace) :
    BddAbove (Set.range fun n ↦ componentLatticeNorm n (x.1 n)) :=
  x.2.bddAbove_range

private theorem componentNorm_le_finalNormValue (x : FinalSpace) (n : ℕ) :
    componentLatticeNorm n (x.1 n) ≤ finalNormValue x := by
  exact le_csSup (finalNormValue_bddAbove x) ⟨n, rfl⟩

/-- The final lattice norm, with all its laws exposed as proof obligations. -/
noncomputable def finalLatticeNorm : PaperLatticeNorm FinalSpace where
  toFun := finalNormValue
  nonneg := by
    intro x
    exact ((componentLatticeNorm 0).nonneg _).trans
      (componentNorm_le_finalNormValue x 0)
  eq_zero_iff := by
    intro x
    constructor
    · intro hx
      apply Subtype.ext
      funext n
      apply (componentLatticeNorm n).eq_zero_iff (x.1 n) |>.1
      apply le_antisymm
      · simpa [hx] using componentNorm_le_finalNormValue x n
      · exact (componentLatticeNorm n).nonneg _
    · rintro rfl
      unfold finalNormValue
      have hzero : (fun n ↦ componentLatticeNorm n ((0 : FinalSpace).1 n)) =
          fun _ ↦ 0 := by
        funext n
        apply (componentLatticeNorm n).eq_zero_iff _ |>.2
        rfl
      rw [hzero]
      simp
  add_le := by
    intro x y
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    calc
      componentLatticeNorm n ((x + y).1 n) ≤
          componentLatticeNorm n (x.1 n) + componentLatticeNorm n (y.1 n) := by
        simpa using (componentLatticeNorm n).add_le (x.1 n) (y.1 n)
      _ ≤ finalNormValue x + finalNormValue y :=
        add_le_add (componentNorm_le_finalNormValue x n)
          (componentNorm_le_finalNormValue y n)
  smul := by
    intro a x
    unfold finalNormValue
    simp_rw [show ∀ n, componentLatticeNorm n ((a • x).1 n) =
        |a| * componentLatticeNorm n (x.1 n) by
      intro n
      simpa using (componentLatticeNorm n).smul a (x.1 n)]
    simpa [smul_eq_mul] using
      (Real.smul_iSup_of_nonneg (abs_nonneg a)
        (fun n ↦ componentLatticeNorm n (x.1 n))).symm
  solid := by
    intro x y hxy
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    exact ((componentLatticeNorm n).solid (hxy n)).trans
      (componentNorm_le_finalNormValue y n)

/-- Paper Lemma `lem:c0-weak-fatou`. -/
theorem finalSpace_weakFatou :
    IsCompleteFor finalLatticeNorm ∧ HasWeakFatouProperty finalLatticeNorm 2 := by
  have hcomplete : IsCompleteFor finalLatticeNorm := by
    intro f hf
    have hcoordCauchy (k : ℕ) :
        ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ q ≥ N,
          componentLatticeNorm k ((f m).1 k - (f q).1 k) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hf ε hε
      refine ⟨N, fun m hm q hq ↦ ?_⟩
      exact (componentNorm_le_finalNormValue (f m - f q) k).trans_lt
        (hN m hm q hq)
    choose x hx using fun k ↦ (component_basic k).2.1 (fun m ↦ (f m).1 k) (hcoordCauchy k)
    have hxVanishes : componentVanishes x := by
      change Tendsto (fun k ↦ componentLatticeNorm k (x k)) atTop (nhds 0)
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
      obtain ⟨N, hN⟩ := hf (ε / 3) hthird
      have hfN : Tendsto (fun k ↦ componentLatticeNorm k ((f N).1 k))
          atTop (nhds 0) := (f N).2
      rw [Metric.tendsto_atTop] at hfN
      obtain ⟨K, hK⟩ := hfN (ε / 3) hthird
      refine ⟨K, fun k hk ↦ ?_⟩
      obtain ⟨L, hL⟩ := hx k (ε / 3) hthird
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      have hmx : componentLatticeNorm k ((f m).1 k - x k) < ε / 3 := hL m hmL
      have hfmN : componentLatticeNorm k ((f m).1 k - (f N).1 k) < ε / 3 := by
        exact (componentNorm_le_finalNormValue (f m - f N) k).trans_lt (hN m hmN N le_rfl)
      have hfNk : componentLatticeNorm k ((f N).1 k) < ε / 3 := by
        have := hK k hk
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)] at this
        exact this
      have hneg : componentLatticeNorm k (x k - (f m).1 k) =
          componentLatticeNorm k ((f m).1 k - x k) := by
        rw [show x k - (f m).1 k = -((f m).1 k - x k) by abel,
          show -((f m).1 k - x k) = (-1 : ℝ) • ((f m).1 k - x k) by simp,
          (componentLatticeNorm k).smul]
        norm_num
      have hxbound : componentLatticeNorm k (x k) < ε := by
        calc
          componentLatticeNorm k (x k) =
              componentLatticeNorm k ((x k - (f m).1 k) +
                (((f m).1 k - (f N).1 k) + (f N).1 k)) := by
            congr 1
            abel
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              componentLatticeNorm k (((f m).1 k - (f N).1 k) + (f N).1 k) :=
            (componentLatticeNorm k).add_le _ _
          _ ≤ componentLatticeNorm k (x k - (f m).1 k) +
              (componentLatticeNorm k ((f m).1 k - (f N).1 k) +
                componentLatticeNorm k ((f N).1 k)) :=
            add_le_add le_rfl ((componentLatticeNorm k).add_le _ _)
          _ < ε := by rw [hneg]; linarith
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((componentLatticeNorm k).nonneg _)]
      exact hxbound
    let x₀ : FinalSpace := ⟨x, hxVanishes⟩
    refine ⟨x₀, ?_⟩
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := hf (ε / 2) hhalf
    refine ⟨N, fun q hq ↦ ?_⟩
    have hcoord (k : ℕ) :
        componentLatticeNorm k ((f q).1 k - x k) ≤ ε / 2 := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      obtain ⟨L, hL⟩ := hx k δ hδ
      let m := max N L
      have hmN : N ≤ m := le_max_left _ _
      have hmL : L ≤ m := le_max_right _ _
      calc
        componentLatticeNorm k ((f q).1 k - x k) =
            componentLatticeNorm k (((f q).1 k - (f m).1 k) +
              ((f m).1 k - x k)) := by
          congr 1
          abel
        _ ≤ componentLatticeNorm k ((f q).1 k - (f m).1 k) +
            componentLatticeNorm k ((f m).1 k - x k) :=
          (componentLatticeNorm k).add_le _ _
        _ ≤ ε / 2 + δ :=
          (add_lt_add (componentNorm_le_finalNormValue (f q - f m) k |>.trans_lt
            (hN q hq m hmN)) (hL m hmL)).le
    have hfinal : finalLatticeNorm (f q - x₀) ≤ ε / 2 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact hcoord k
    exact hfinal.trans_lt (by linarith)
  have hweak : HasWeakFatouProperty finalLatticeNorm 2 := by
    refine ⟨by norm_num, ?_⟩
    intro ι _ _ _ f x hfmono hfpos hflub c hfc
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    have hcoordLUB : IsLUB (Set.range fun i ↦ (f i).1 k) (x.1 k) := by
      constructor
      · rintro _ ⟨i, rfl⟩
        exact hflub.1 ⟨i, rfl⟩ k
      · intro z hz
        let y : FinalSpace := x + finalCoordinateEmbedding k (z - x.1 k)
        have hyupper : y ∈ upperBounds (Set.range f) := by
          rintro _ ⟨i, rfl⟩ m
          by_cases hmk : m = k
          · subst m
            simpa [y] using hz ⟨i, rfl⟩
          · have hix := hflub.1 ⟨i, rfl⟩ m
            simpa [y, finalCoordinateEmbedding_ne k m hmk] using hix
        have hxy := hflub.2 hyupper k
        simpa [y] using hxy
    exact (component_weakFatou k).2.2 (fun i ↦ (f i).1 k) (x.1 k)
      (fun _ _ hij ↦ hfmono hij k) (fun i ↦ hfpos i k) hcoordLUB c
      (fun i ↦ (componentNorm_le_finalNormValue (f i) k).trans (hfc i))
  exact ⟨hcomplete, hweak⟩

private theorem finalLatticeNorm_coordinateEmbedding (n : ℕ) (z : TreeComponent n) :
    finalLatticeNorm (finalCoordinateEmbedding n z) = componentLatticeNorm n z := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨m, rfl⟩
    by_cases hmn : m = n
    · subst m
      simp
    · change componentLatticeNorm m ((finalCoordinateEmbedding n z).1 m) ≤ _
      rw [finalCoordinateEmbedding_ne n m hmn]
      rw [(componentLatticeNorm m).eq_zero_iff 0 |>.2 rfl]
      exact (componentLatticeNorm n).nonneg z
  · simpa using componentNorm_le_finalNormValue (finalCoordinateEmbedding n z) n

private theorem finalCoordinateEmbedding_orderConverges
    {n : ℕ} {ι : Type} [Preorder ι] {f : ι → TreeComponent n} {z : TreeComponent n}
    (hf : OrderConvergesTo f z) :
    OrderConvergesTo (fun i ↦ finalCoordinateEmbedding n (f i))
      (finalCoordinateEmbedding n z) := by
  classical
  rcases hf with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrpos, hrglb, hcontrol⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκne
  refine ⟨κ, inferInstance, inferInstance, inferInstance,
    fun k ↦ finalCoordinateEmbedding n (r k), ?_, ?_, ?_, ?_⟩
  · intro a b hab m
    by_cases hmn : m = n
    · subst m
      simpa using hranti hab
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · intro k m
    by_cases hmn : m = n
    · subst m
      simpa using hrpos k
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · constructor
    · rintro _ ⟨k, rfl⟩
      intro m
      by_cases hmn : m = n
      · subst m
        simpa using hrpos k
      · simp [finalCoordinateEmbedding_ne n m hmn]
    · intro y hy m
      by_cases hmn : m = n
      · subst m
        apply hrglb.2
        rintro _ ⟨k, rfl⟩
        simpa using hy ⟨k, rfl⟩ n
      · let k₀ : κ := Classical.choice inferInstance
        have := hy ⟨k₀, rfl⟩ m
        simpa [finalCoordinateEmbedding_ne n m hmn] using this
  · intro k
    filter_upwards [hcontrol k] with i hi
    intro m
    by_cases hmn : m = n
    · subst m
      change |(finalCoordinateEmbedding n (f i)).1 n -
          (finalCoordinateEmbedding n z).1 n| ≤
        (finalCoordinateEmbedding n (r k)).1 n
      simpa using hi
    · change |(finalCoordinateEmbedding n (f i)).1 m -
          (finalCoordinateEmbedding n z).1 m| ≤
        (finalCoordinateEmbedding n (r k)).1 m
      rw [finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn]
      simp

private theorem finalCoordinateEmbedding_iteratedOrderAdherence (n k : ℕ)
    {z : TreeComponent n}
    (hz : z ∈ iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) :
    finalCoordinateEmbedding n z ∈
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k := by
  induction k generalizing z with
  | zero =>
      change componentLatticeNorm n z ≤ 1 at hz
      change finalLatticeNorm (finalCoordinateEmbedding n z) ≤ 1
      simpa [finalLatticeNorm_coordinateEmbedding] using hz
  | succ k ih =>
      change z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) at hz
      rcases hz with ⟨ι, hpre, hdir, hne, f, hfmem, hfz⟩
      letI : Preorder ι := hpre
      letI : IsDirected ι (· ≤ ·) := hdir
      letI : Nonempty ι := hne
      change finalCoordinateEmbedding n z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor finalLatticeNorm) k)
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ finalCoordinateEmbedding n (f i), fun i ↦ ih (hfmem i), ?_⟩
      exact finalCoordinateEmbedding_orderConverges hfz

/-- The vector `z_n`, supported in coordinate `n`. -/
noncomputable def finalLargeVector (n : ℕ) : FinalSpace :=
  ⟨fun m ↦ if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0, by
    change Tendsto
      (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0))
      atTop (nhds 0)
    have heq : (fun m ↦ componentLatticeNorm m
        (if h : m = n then h.symm ▸ ((2 : ℝ) ^ n • componentRoot n) else 0)) =ᶠ[atTop]
        fun _ ↦ 0 := by
      filter_upwards [eventually_gt_atTop n] with m hm
      rw [dif_neg hm.ne']
      exact (componentLatticeNorm m).eq_zero_iff _ |>.2 rfl
    exact (tendsto_congr' heq).2 tendsto_const_nhds⟩

/-- Paper Proposition `prop:zn`. -/
theorem finalLargeVector_properties (n : ℕ) :
    finalLargeVector n ∈ iteratedOrderAdherence (unitBallFor finalLatticeNorm) n ∧
      finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n := by
  have heq : finalLargeVector n =
      finalCoordinateEmbedding n ((2 : ℝ) ^ n • componentRoot n) := by
    apply Subtype.ext
    funext m
    simp [finalLargeVector, finalCoordinateEmbedding]
  rw [heq]
  exact ⟨finalCoordinateEmbedding_iteratedOrderAdherence n n
      (component_large_iterated_adherence n).2.2.2.1,
    (finalLatticeNorm_coordinateEmbedding n _).trans
      (component_large_iterated_adherence n).2.2.2.2⟩

/-- The constructed `c₀`-sum admits no equivalent Fatou lattice norm. -/
theorem finalSpace_not_equivalent_fatou :
    ∀ q : PaperLatticeNorm FinalSpace,
      HasFatouProperty q → ¬ EquivalentNorms finalLatticeNorm q := by
  intro q hq hequiv
  rcases hequiv with ⟨c, C, hc, hC, hcompare⟩
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (C / c : ℝ) (by norm_num : (1 : ℝ) < 2)
  let n := n₀ + 1
  have hn : 1 ≤ n := by simp [n]
  have hlarge : C < c * (2 : ℝ) ^ n := by
    have hpow : (2 : ℝ) ^ n₀ < (2 : ℝ) ^ n := by
      change (2 : ℝ) ^ n₀ < (2 : ℝ) ^ (n₀ + 1)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n₀]
    have hcdiv : C < c * (2 : ℝ) ^ n₀ := by
      rw [div_lt_iff₀ hc] at hn₀
      simpa [mul_comm] using hn₀
    exact hcdiv.trans (mul_lt_mul_of_pos_left hpow hc)
  have hball : unitBallFor finalLatticeNorm ⊆ scaleSet C (unitBallFor q) := by
    intro z hz
    refine ⟨C⁻¹ • z, ?_, ?_⟩
    · change q (C⁻¹ • z) ≤ 1
      rw [q.smul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_one₀ hC]
      exact (hcompare z).2.trans (by
        simpa using mul_le_mul_of_nonneg_left hz hC.le)
    · simp [smul_smul, hC.ne']
  have hitermono : ∀ k,
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k ⊆
        iteratedOrderAdherence (scaleSet C (unitBallFor q)) k := by
    intro k
    induction k with
    | zero => exact hball
    | succ k ih => exact orderAdherence_mono ih
  have hsolidq : LatticeOrderedAddCommGroup.IsSolid (unitBallFor q) := by
    intro y hy z hzy
    exact (q.solid hzy).trans hy
  have hscale :=
    (iteratedOrderAdherence_mono_and_scale hsolidq hsolidq hC).2.2 n
  have hz := hitermono n (finalLargeVector_properties n).1
  rw [hscale, fatou_iterated_unitBall q hq n hn] at hz
  rcases hz with ⟨y, hy, hyz⟩
  have hqz : q (finalLargeVector n) ≤ C := by
    rw [← hyz, q.smul, abs_of_pos hC]
    simpa using mul_le_mul_of_nonneg_left hy hC.le
  have hpz : finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n :=
    (finalLargeVector_properties n).2
  have hlower := (hcompare (finalLargeVector n)).1
  rw [hpz] at hlower
  exact (not_lt_of_ge (hlower.trans hqz)) hlarge

/-- Paper Theorem `thm:fremlin-main`. -/
theorem exists_weaklyFatou_not_equivalent_fatou :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ p : PaperLatticeNorm X, IsCompleteFor p ∧ HasWeakFatouProperty p 2 ∧
        ∀ q : PaperLatticeNorm X, HasFatouProperty q → ¬ EquivalentNorms p q := by
  refine ⟨FinalSpace, inferInstance, inferInstance, inferInstance, inferInstance,
    finalLatticeNorm, (finalSpace_weakFatou).1, (finalSpace_weakFatou).2,
    finalSpace_not_equivalent_fatou⟩

end OrderClosures
