import OrderClosures.GaoLeungProblem.StageFormula

/-!
# Arbitrarily long order-adherence iterations
-/

namespace OrderClosures

open Set

universe u v

section OrdinalConstruction

/-- Paper Theorem `thm:solid-iterations`. Here `κ⁺` is represented by the
initial ordinal of the successor cardinal. -/
noncomputable def canonicalOrderAdherenceTower
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

abbrev GaoSuccessorGenerator (β : Ordinal.{u}) :=
  {ζ : GaoIndex β // ζ ∈ GaoStageIndices β 1}

abbrev GaoComponentIndex (κ : Cardinal.{u}) :=
  Set.Iio (Cardinal.ord (Order.succ κ))

abbrev GaoComponent (β : Ordinal.{u}) :=
  C(GaoCompactSpace β, ℝ)

abbrev GaoIterationProduct (κ : Cardinal.{u}) :=
  (∀ β : GaoComponentIndex κ, GaoComponent β.1) ×
    (ULift.{u + 1, u} (Cardinal.ord κ).ToType → ℝ)

instance (κ : Cardinal.{u}) : IsOrderedAddMonoid (GaoIterationProduct κ) where
  add_le_add_left a b hab c := by
    constructor
    · intro β
      simpa [add_comm] using add_le_add_right (hab.1 β) (c.1 β)
    · intro i
      simpa [add_comm] using add_le_add_right (hab.2 i) (c.2 i)

instance (κ : Cardinal.{u}) : PosSMulMono ℝ (GaoIterationProduct κ) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hbc := by
    constructor
    · intro β
      rw [ContinuousMap.le_def]
      intro y
      exact smul_le_smul_of_nonneg_left ((hbc.1 β) y) ha
    · intro i
      exact smul_le_smul_of_nonneg_left (hbc.2 i) ha

noncomputable instance (κ : Cardinal.{u}) : VectorLattice (GaoIterationProduct κ) where

theorem gaoIterationProduct_abs_fst
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ) (β : GaoComponentIndex κ) :
    |x|.1 β = |x.1 β| := rfl

theorem gaoIterationProduct_abs_snd
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    |x|.2 a = |x.2 a| := rfl

theorem mk_gaoSuccessorGenerator_le
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

noncomputable def gaoGeneratorEmbedding
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : Ordinal.{u}) (hβ : β < Cardinal.ord (Order.succ κ)) :
    GaoSuccessorGenerator β ↪ ULift.{u + 1, u} (Cardinal.ord κ).ToType := by
  apply Classical.choice
  rw [← Cardinal.le_def]
  change Cardinal.mk (GaoSuccessorGenerator β) ≤
    Cardinal.lift.{u + 1, u} (Cardinal.mk (Cardinal.ord κ).ToType)
  rw [Cardinal.mk_ord_toType]
  exact mk_gaoSuccessorGenerator_le κ hκ β hβ

noncomputable def gaoComponentGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoComponent β.1 := by
  classical
  exact if h : ∃ ζ : GaoSuccessorGenerator β.1,
        gaoGeneratorEmbedding κ hκ β.1 β.2 ζ = a then
      ordinalProjection β.1 (Classical.choose h).1
    else 0

theorem gaoComponentGenerator_embedding
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

noncomputable def gaoGlobalGenerator
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) : GaoIterationProduct κ :=
  (fun β ↦ gaoComponentGenerator κ hκ β a,
    fun b ↦ if b = a then (1 : ℝ) else 0)

def gaoProductProjection (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoIterationProduct κ → GaoComponent β.1 := fun x ↦ x.1 β

noncomputable def gaoProductInclusion
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) :
    GaoComponent β.1 → GaoIterationProduct κ := fun x ↦
  (Pi.single β x, 0)

theorem orderConvergesTo_gaoProductProjection
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

theorem orderConvergesTo_gaoProductInclusion
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

theorem gaoProductProjection_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoIterationProduct κ)) :
    gaoProductProjection κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductProjection κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductProjection κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductProjection κ β hfx⟩

theorem gaoProductInclusion_orderAdherence
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoComponent β.1)) :
    gaoProductInclusion κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductInclusion κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductInclusion κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductInclusion κ β hfx⟩

noncomputable def gaoIterationSet
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) : Set (GaoIterationProduct κ) :=
  solidHull (Set.range (gaoGlobalGenerator κ hκ))

theorem gaoComponentGenerator_mem
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

theorem gaoProjection_initial
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductProjection κ β '' gaoIterationSet κ hκ ⊆ GaoStageSet β.1 1 := by
  rintro _ ⟨x, ⟨g, ⟨a, rfl⟩, hx⟩, rfl⟩
  apply isSolid_gaoStageSet β.1 1 (gaoComponentGenerator_mem κ hκ β a)
  simpa [gaoProductProjection, gaoGlobalGenerator] using hx.1 β

theorem gaoInclusion_initial
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

theorem gaoProjection_stage
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

theorem gaoInclusion_stage
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

theorem one_add_le_add_one_ordinal (δ : Ordinal.{u}) :
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

theorem gaoIterationTower_strict
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

theorem gaoGlobalGenerator_index_eq_of_abs_le
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

theorem gaoGlobalGenerator_injective
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Function.Injective (gaoGlobalGenerator κ hκ) := by
  intro a b hab
  apply gaoGlobalGenerator_index_eq_of_abs_le κ hκ
  rw [hab]

theorem mk_gaoGlobalGenerator_range
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

theorem solidGeneratorNumber_gaoIterationSet
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

theorem orderConvergesTo_zero_of_abs_le_gao
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
