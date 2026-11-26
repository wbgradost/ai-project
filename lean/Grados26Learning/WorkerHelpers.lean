module

public import Grados26Learning.WorkerModel
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! # Existence and order of the greatest total-input optimizer -/

open Set Filter

noncomputable section
namespace Grados26Learning

/-- Concavity bounds the production/input ratio on the positive tail. -/
theorem production_ratio_eventually_bounded (W : WorkerModel) :
    IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => W.p x / x) := by
  refine ⟨W.p 1 - W.p 0 + |W.p 0|, ?_⟩
  change ∀ᶠ x : ℝ in atTop, W.p x / x ≤ W.p 1 - W.p 0 + |W.p 0|
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hs := W.p_concave.slope_anti_adjacent
    (x := 0) (y := 1) (z := x) (by simp) hx0.le (by norm_num) hx
  simp only [sub_zero, div_one] at hs
  have hp : W.p x ≤ W.p 0 + x * (W.p 1 - W.p 0) := by
    have h := (div_le_iff₀ (sub_pos.mpr hx)).mp hs
    nlinarith only [h]
  apply (div_le_iff₀ hx0).mpr
  have hbase := le_abs_self (W.p 0)
  have habs : 0 ≤ |W.p 0| := abs_nonneg _
  have habsprod : 0 ≤ |W.p 0| * (x - 1) :=
    mul_nonneg habs (sub_nonneg.mpr hx.le)
  nlinarith only [hp, hbase, habsprod]

/-- The literal limsup assumption implies a strict linear upper tail with
slope below the effort cost; no coercivity premise is added to the model. -/
theorem exists_production_linear_tail (W : WorkerModel) :
    ∃ c : ℝ, c < W.gamma ∧ ∀ᶠ x : ℝ in atTop, W.p x < c * x := by
  obtain ⟨c, hc1, hc2⟩ := exists_between W.growth
  refine ⟨c, hc2, ?_⟩
  have hratio := eventually_lt_of_limsup_lt hc1
    (production_ratio_eventually_bounded W)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact (div_lt_iff₀ hx0).mp hx

/-- The growth hypothesis supplies a bounded interval containing every
optimizer; all points in the tail are strictly worse than input zero. -/
theorem exists_input_tail_cutoff (W : WorkerModel) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x → inputObjective W x < inputObjective W 0 := by
  obtain ⟨c, hc, htail⟩ := exists_production_linear_tail W
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let d := W.gamma - c
  have hd : 0 < d := sub_pos.mpr hc
  let R := max N (max 1 ((-inputObjective W 0 + 1) / d))
  refine ⟨R, lt_of_lt_of_le zero_lt_one ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · intro x hx
    have hxN : N ≤ x := (le_max_left _ _).trans hx
    have hxb : (-inputObjective W 0 + 1) / d ≤ x :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hx)
    have hprod : -inputObjective W 0 + 1 ≤ x * d :=
      (div_le_iff₀ hd).mp hxb
    have hpx := hN x hxN
    change W.p x - W.gamma * x < inputObjective W 0
    dsimp [d] at hprod
    nlinarith only [hpx, hprod]

/-- Continuity used for the compact-domain existence argument. -/
theorem continuousOn_inputObjective (W : WorkerModel) :
    ContinuousOn (inputObjective W) (Ici 0) := by
  exact W.p_contDiff.continuousOn.sub (continuousOn_const.mul continuousOn_id)

/-- A compact nonempty optimizer set follows from the source growth condition. -/
theorem inputMaximizers_compact_nonempty (W : WorkerModel) :
    IsCompact (inputMaximizers W) ∧ (inputMaximizers W).Nonempty := by
  obtain ⟨R, hR, htail⟩ := exists_input_tail_cutoff W
  have hcont := continuousOn_inputObjective W
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Icc (0 : ℝ) R) ⟨0, le_rfl, hR.le⟩
    (hcont.mono (fun x hx => hx.1))
  have hglobal : IsMaxOn (inputObjective W) (Ici 0) m := by
    intro x hx
    by_cases hxR : x ≤ R
    · exact hmax ⟨hx, hxR⟩
    · exact (htail x (le_of_lt (lt_of_not_ge hxR))).le.trans
        (hmax ⟨le_rfl, hR.le⟩)
  have hne : (inputMaximizers W).Nonempty := ⟨m, hm.1, hglobal⟩
  have hclamp : Continuous (fun x : ℝ => inputObjective W (max x 0)) :=
    hcont.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)
  have hclosed : IsClosed (inputMaximizers W) := by
    have hset : inputMaximizers W =
        Ici 0 ∩ {x | inputObjective W (max x 0) = inputObjective W m} := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        change inputObjective W (max x 0) = inputObjective W m
        rw [max_eq_left hx.1]
        exact le_antisymm (hglobal hx.1) (hx.2 hm.1)
      · rintro ⟨hx, hval⟩
        have hx0 : 0 ≤ x := mem_Ici.mp hx
        change inputObjective W (max x 0) = inputObjective W m at hval
        rw [max_eq_left hx0] at hval
        refine ⟨hx0, ?_⟩
        intro y hy
        exact (hglobal hy).trans hval.ge
    rw [hset]
    exact isClosed_Ici.inter (isClosed_eq hclamp continuous_const)
  have hsubset : inputMaximizers W ⊆ Icc 0 R := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra h
    have hlt := htail x (le_of_lt (lt_of_not_ge h))
    have hge := hx.2 (show (0 : ℝ) ∈ Ici 0 by simp)
    exact (not_lt_of_ge hge) hlt
  exact ⟨isCompact_Icc.of_isClosed_subset hclosed hsubset, hne⟩

/-- The reference input exists and is the greatest member of the entire
unrestricted optimizer set, including all ties. -/
theorem isGreatest_referenceInput (W : WorkerModel) :
    IsGreatest (inputMaximizers W) (referenceInput W) := by
  obtain ⟨hcompact, hne⟩ := inputMaximizers_compact_nonempty W
  exact hcompact.isGreatest_sSup hne

/-- Feasibility of the reference input is derived, not assumed. -/
theorem referenceInput_nonneg (W : WorkerModel) : 0 ≤ referenceInput W :=
  (isGreatest_referenceInput W).1.1

/-- Global optimality of the selected reference input. -/
theorem referenceInput_isMaxOn (W : WorkerModel) :
    IsMaxOn (inputObjective W) (Ici 0) (referenceInput W) :=
  (isGreatest_referenceInput W).1.2

/-- Subtracting the linear effort cost preserves weak concavity. -/
theorem concaveOn_inputObjective (W : WorkerModel) :
    ConcaveOn ℝ (Ici 0) (inputObjective W) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy u v hu hv huv
  have hp := W.p_concave.2 hx hy hu hv huv
  simp only [smul_eq_mul] at hp ⊢
  dsimp only [inputObjective]
  have hlin : u * (W.p x - W.gamma * x) + v * (W.p y - W.gamma * y) =
      u * W.p x + v * W.p y - W.gamma * (u * x + v * y) := by ring
  rw [hlin]
  exact sub_le_sub_right hp (W.gamma * (u * x + v * y))

/-- Every input beyond the greatest optimizer has a strictly lower value. -/
theorem inputObjective_lt_reference_of_lt (W : WorkerModel) {x : ℝ}
    (hx : referenceInput W < x) :
    inputObjective W x < inputObjective W (referenceInput W) := by
  have hx0 : 0 ≤ x := (referenceInput_nonneg W).trans hx.le
  by_contra h
  have hrev : inputObjective W (referenceInput W) ≤ inputObjective W x :=
    le_of_not_gt h
  have hxmax : IsMaxOn (inputObjective W) (Ici 0) x := by
    intro y hy
    exact (referenceInput_isMaxOn W hy).trans hrev
  have hxle := (isGreatest_referenceInput W).2 (show x ∈ inputMaximizers W from ⟨hx0, hxmax⟩)
  exact (not_le_of_gt hx) hxle

/-- Concavity makes the objective strictly decreasing after its greatest
optimizer, even though it may be flat at the optimizer set itself. -/
theorem inputObjective_strict_tail (W : WorkerModel) {x y : ℝ}
    (hx : referenceInput W < x) (hxy : x < y) :
    inputObjective W y < inputObjective W x := by
  have hy0 : 0 ≤ y := ((referenceInput_nonneg W).trans hx.le).trans hxy.le
  have hs := (concaveOn_inputObjective W).slope_anti_adjacent
    (x := referenceInput W) (y := x) (z := y)
    (referenceInput_nonneg W) hy0 hx hxy
  have hright :
      (inputObjective W x - inputObjective W (referenceInput W)) /
        (x - referenceInput W) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr (inputObjective_lt_reference_of_lt W hx))
      (sub_pos.mpr hx)
  have hleft := hs.trans_lt hright
  have hdiff := (div_lt_iff₀ (sub_pos.mpr hxy)).mp hleft
  linarith only [hdiff]


end Grados26Learning
end
