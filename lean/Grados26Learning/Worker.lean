module

public import Grados26Learning.WorkerHelpers
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! # Lemma 1: the original greatest-effort choice and its active regime -/

open Set Filter

set_option maxHeartbeats 200000

noncomputable section
namespace Grados26Learning
/-- Changing the decision variable from effort to total input only adds a
constant to utility, so it preserves the entire optimizer set. -/
theorem workerUtility_eq_inputObjective (W : WorkerModel) (s a e : ℝ) :
    workerUtility W s a e = inputObjective W (s + e + a) + W.gamma * (s + a) := by
  unfold workerUtility inputObjective
  ring

/-- Above the reference input, any positive effort is strictly worse than
zero effort. This is derived from weak concavity and the greatest tie rule. -/
theorem workerUtility_lt_zero_effort (W : WorkerModel) {s a e : ℝ}
    (hz : referenceInput W < s + a) (he : 0 < e) :
    workerUtility W s a e < workerUtility W s a 0 := by
  have hdrop := inputObjective_strict_tail W hz
    (show s + a < s + e + a by linarith only [he])
  rw [workerUtility_eq_inputObjective, workerUtility_eq_inputObjective]
  simp only [add_zero]
  linarith only [hdrop]

/-- The source candidate is the greatest feasible effort maximizer. This
proves both attainment and the tie convention from the worker primitives. -/
theorem effort_candidate_isGreatest (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) :
    IsGreatest (effortMaximizers W s a) (max (referenceInput W - s - a) 0) := by
  by_cases hz : s + a ≤ referenceInput W
  · have hgap : 0 ≤ referenceInput W - s - a := by linarith only [hz]
    rw [max_eq_left hgap]
    have htotal : s + (referenceInput W - s - a) + a = referenceInput W := by ring
    have hbest : IsMaxOn (workerUtility W s a) (Ici 0)
        (referenceInput W - s - a) := by
      intro e he
      change workerUtility W s a e ≤ workerUtility W s a (referenceInput W - s - a)
      rw [workerUtility_eq_inputObjective, workerUtility_eq_inputObjective, htotal]
      have hfeasible : s + e + a ∈ Ici 0 := add_nonneg (add_nonneg hs he) ha
      have hglobal : inputObjective W (s + e + a) ≤ inputObjective W (referenceInput W) :=
        referenceInput_isMaxOn W hfeasible
      exact add_le_add_left hglobal _
    refine ⟨⟨hgap, hbest⟩, ?_⟩
    intro e he
    have hvalue : workerUtility W s a (referenceInput W - s - a) ≤ workerUtility W s a e :=
      he.2 hgap
    rw [workerUtility_eq_inputObjective, workerUtility_eq_inputObjective, htotal] at hvalue
    have he0 : 0 ≤ s + e + a := add_nonneg (add_nonneg hs he.1) ha
    have hinput : IsMaxOn (inputObjective W) (Ici 0) (s + e + a) := by
      intro x hx
      change inputObjective W x ≤ inputObjective W (s + e + a)
      have hglobal : inputObjective W x ≤ inputObjective W (referenceInput W) :=
        referenceInput_isMaxOn W hx
      linarith only [hglobal, hvalue]
    have hbound := (isGreatest_referenceInput W).2
      (show s + e + a ∈ inputMaximizers W from ⟨he0, hinput⟩)
    linarith only [hbound]
  · have hz' : referenceInput W < s + a := lt_of_not_ge hz
    have hgap : referenceInput W - s - a ≤ 0 := by linarith only [hz']
    rw [max_eq_right hgap]
    have hbest : IsMaxOn (workerUtility W s a) (Ici 0) 0 := by
      intro e he
      change workerUtility W s a e ≤ workerUtility W s a 0
      by_cases he0 : e = 0
      · subst e
        exact le_rfl
      · exact (workerUtility_lt_zero_effort W hz' (lt_of_le_of_ne he (Ne.symm he0))).le
    refine ⟨⟨le_rfl, hbest⟩, ?_⟩
    intro e he
    by_contra hnot
    have hepos : 0 < e := lt_of_not_ge hnot
    have hdrop := workerUtility_lt_zero_effort W hz' hepos
    exact (not_lt_of_ge (he.2 (show (0 : ℝ) ∈ Ici 0 by simp))) hdrop

/-- Lemma 1's effort formula for the actual greatest-maximizer selection. -/
theorem selectedEffort_eq (W : WorkerModel) {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    selectedEffort W s a = max (referenceInput W - s - a) 0 := by
  have hgreat := effort_candidate_isGreatest W hs ha
  unfold selectedEffort
  apply le_antisymm
  · exact csSup_le ⟨_, hgreat.1⟩ hgreat.2
  · exact le_csSup ⟨_, hgreat.2⟩ hgreat.1

/-- The selected effort is a greatest optimizer; its existence is proved. -/
theorem selectedEffort_isGreatest (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) :
    IsGreatest (effortMaximizers W s a) (selectedEffort W s a) := by
  rw [selectedEffort_eq W hs ha]
  exact effort_candidate_isGreatest W hs ha

/-- Effort is affine and positive strictly below its state-specific cutoff. -/
theorem selectedEffort_eq_sub_of_lt (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hint : a < referenceInput W - s) :
    selectedEffort W s a = referenceInput W - s - a := by
  have hgap : 0 ≤ referenceInput W - s - a := by linarith only [hint]
  rw [selectedEffort_eq W hs ha, max_eq_left hgap]

/-- Active effort is strictly positive, as required by the interior regime. -/
theorem selectedEffort_pos_of_lt (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hint : a < referenceInput W - s) :
    0 < selectedEffort W s a := by
  rw [selectedEffort_eq_sub_of_lt W hs ha hint]
  linarith only [hint]

/-- Effort vanishes at the cutoff and at every larger assistance level. -/
theorem selectedEffort_eq_zero_of_le (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hcut : referenceInput W - s ≤ a) :
    selectedEffort W s a = 0 := by
  have hgap : referenceInput W - s - a ≤ 0 := sub_nonpos.mpr hcut
  rw [selectedEffort_eq W hs ha, max_eq_right hgap]

/-- The one-for-one crowd-out derivative on the source's active interval. -/
theorem hasDerivAt_selectedEffort_of_lt (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 < a) (hint : a < referenceInput W - s) :
    HasDerivAt (fun t : ℝ => selectedEffort W s t) (-1) a := by
  have hder : HasDerivAt (fun t : ℝ => referenceInput W - s - t) (-1) a := by
    simpa only [zero_sub] using (hasDerivAt_const a (referenceInput W - s)).sub (hasDerivAt_id a)
  apply HasDerivAt.congr_of_eventuallyEq
    (f₁ := fun t : ℝ => selectedEffort W s t) hder
  filter_upwards [Ioo_mem_nhds ha hint] with t ht
  exact selectedEffort_eq_sub_of_lt W hs ht.1.le ht.2

/-- The derivative of net output on the production domain. -/
private theorem hasDerivWithinAt_inputObjective (W : WorkerModel) {x : ℝ}
    (hx : 0 ≤ x) :
    HasDerivWithinAt (inputObjective W)
      (derivWithin W.p (Ici 0) x - W.gamma) (Ici 0) x := by
  have hprod := (W.p_contDiff.differentiableOn_one x hx).hasDerivWithinAt
  have hcost : HasDerivAt (fun t : ℝ => W.gamma * t) W.gamma x := by
    simpa using (hasDerivAt_id x).const_mul W.gamma
  exact hprod.sub hcost.hasDerivWithinAt

/-- At a positive reference input, the ordinary marginal product equals
the marginal effort cost. An interior effort choice always has such an input. -/
theorem deriv_production_referenceInput (W : WorkerModel) (h : 0 < referenceInput W) :
    deriv W.p (referenceInput W) = W.gamma := by
  have hmem := Ici_mem_nhds h
  have hmax : IsLocalMax (inputObjective W) (referenceInput W) := by
    filter_upwards [hmem] with x hx
    exact referenceInput_isMaxOn W hx
  have hnet := (hasDerivWithinAt_inputObjective W h.le).hasDerivAt hmem
  have hp := ((W.p_contDiff.differentiableOn_one _ h.le).hasDerivWithinAt).hasDerivAt hmem
  have hzero := hmax.deriv_eq_zero
  rw [hnet.deriv, ← hp.deriv] at hzero
  exact sub_eq_zero.mp hzero

/-- At the zero-effort corner, the (right at zero) marginal product is at
most the effort cost. Beyond the reference input the inequality is strict. -/
theorem production_derivWithin_corner (W : WorkerModel) {z : ℝ}
    (hz : referenceInput W ≤ z) :
    derivWithin W.p (Ici 0) z ≤ W.gamma ∧
      (referenceInput W < z → derivWithin W.p (Ici 0) z < W.gamma) := by
  have hz0 : 0 ≤ z := (referenceInput_nonneg W).trans hz
  have hstrict (h : referenceInput W < z) :
      derivWithin W.p (Ici 0) z < W.gamma := by
    have hsec := (concaveOn_inputObjective W).le_slope_of_hasDerivWithinAt
      (referenceInput_nonneg W) hz0 h (hasDerivWithinAt_inputObjective W hz0)
    have hnegative : slope (inputObjective W) (referenceInput W) z < 0 := by
      rw [slope_def_field]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (inputObjective_lt_reference_of_lt W h))
        (sub_pos.mpr h)
    exact sub_neg.mp (hsec.trans_lt hnegative)
  refine ⟨?_, hstrict⟩
  rcases eq_or_lt_of_le hz with rfl | h
  · have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) (referenceInput W) := by
      apply mem_posTangentConeAt_of_segment_subset
      rw [segment_eq_Icc (by linarith)]
      exact fun _ ht => (referenceInput_nonneg W).trans ht.1
    have hsign := ((referenceInput_isMaxOn W).localize).hasFDerivWithinAt_nonpos
      (hasDerivWithinAt_inputObjective W hz0).hasFDerivWithinAt htangent
    exact sub_nonpos.mp (by simpa using hsign)
  · exact (hstrict h).le

/-- The interior first-order condition applies to the actual selected effort. -/
theorem deriv_production_of_selectedEffort_pos (W : WorkerModel) {s a : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (he : 0 < selectedEffort W s a) :
    deriv W.p (referenceInput W) = W.gamma := by
  apply deriv_production_referenceInput W
  by_contra! hn
  rw [selectedEffort_eq W hs ha,
    max_eq_right (show referenceInput W - s - a ≤ 0 by linarith only [hn, hs, ha])] at he
  exact (lt_irrefl 0) he

end Grados26Learning

end
