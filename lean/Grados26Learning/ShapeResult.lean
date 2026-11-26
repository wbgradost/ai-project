module

public import Grados26Learning.DeterministicInterface
public import Grados26Learning.Shape
public import Grados26Learning.Calculus
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

namespace Grados26Learning

open Set

noncomputable section

private theorem gain_eq_return (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 < a) :
    stationaryShare p a = stationaryShare p 0 ↔ a = returnPoint p := by
  constructor
  · intro heq
    rcases lt_trichotomy a (returnPoint p) with hlt | hr | hgt
    · have hgain := (strong_gain_iff p h ha.le).2 ⟨ha, hlt⟩
      exact False.elim ((ne_of_gt hgain) heq)
    · exact hr
    · exact False.elim ((ne_of_lt (strong_loss_after_return p h hgt)) heq)
  · rintro rfl
    exact return_to_noAI p h

private theorem loss_iff_after_return (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 < a) :
    stationaryShare p a < stationaryShare p 0 ↔ returnPoint p < a := by
  constructor
  · intro hloss
    rcases lt_trichotomy a (returnPoint p) with hlt | heq | hgt
    · exact False.elim
        ((lt_asymm hloss) ((strong_gain_iff p h ha.le).2 ⟨ha, hlt⟩))
    · exact False.elim ((ne_of_lt hloss) ((gain_eq_return p h ha).2 heq))
    · exact hgt
  · exact strong_loss_after_return p h

private theorem not_concave_stationaryShare (p : Parameters) :
    ¬ ConcaveOn ℝ (Ici 0) (stationaryShare p) := by
  intro hc
  have hu : (0 : ℝ) ∈ Ici 0 := mem_Ici.mpr le_rfl
  have hv : 2 * p.b ∈ Ici 0 := mul_nonneg (by norm_num) p.b_pos.le
  have hab : p.b ≤ 2 * p.b := by linarith [p.b_pos]
  have htail : stationaryShare p (2 * p.b) = stationaryShare p p.b :=
    plateau_pair_equal p le_rfl hab
  have hweight : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hmid := hc.2 hu hv hweight hweight hsum
  simp only [smul_eq_mul] at hmid
  have hm : (1 / 2 : ℝ) * 0 + 1 / 2 * (2 * p.b) = p.b := by ring
  rw [hm, htail] at hmid
  have hlt := mixed_pair_decrease p (show (0 : ℝ) ≤ 0 from le_rfl) p.b_pos le_rfl
  linarith

private theorem stationaryShare_not_differentiable_cutoff (p : Parameters) :
    ¬ DifferentiableAt ℝ (stationaryShare p) p.b := by
  intro h
  have hl := left_derivative_cutoff p
  have hr := right_derivative_cutoff p
  have hIic := uniqueDiffOn_Iic p.b p.b self_mem_Iic
  have hIci := uniqueDiffOn_Ici p.b p.b self_mem_Ici
  have hleft := (hl.derivWithin hIic).symm.trans
    (h.hasDerivAt.hasDerivWithinAt.derivWithin hIic)
  have hright := (hr.derivWithin hIci).symm.trans
    (h.hasDerivAt.hasDerivWithinAt.derivWithin hIci)
  have hden := add_pos p.lambda0_pos p.mu_pos
  have hcomp : 0 < 1 + p.eta * p.b := by
    linarith [mul_nonneg p.eta_nonneg p.b_pos.le]
  have hneg : -p.mu * p.kappa * (1 + p.eta * p.b) / (p.lambda0 + p.mu)^2 < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos p.mu_pos)
        p.kappa_pos) hcomp) (pow_pos hden 2)
  rw [hleft, ← hright] at hneg
  exact (lt_irrefl 0) hneg

/-- Proposition 1 from the source-pinned paper. -/
theorem proposition1 : proposition1Spec := by
  intro E
  let p := E.parameters
  refine ⟨continuousOn_stationaryShare p, ?_, right_derivative_zero p, ?_, ?_,
    ?_, ?_, left_derivative_cutoff p, right_derivative_cutoff p, ?_, ?_,
    not_concave_stationaryShare p, stationaryShare_not_differentiable_cutoff p⟩
  · intro a ha
    exact hasDerivAt_stationaryShare p ha.1.le ha.2
  · intro h
    exact ⟨weak_strictAntiOn p h, weak_global_max p h, fun _ => weak_max_unique p h,
      fun _ => weak_loss p h⟩
  · intro h
    refine ⟨critical_right_derivative_zero p h, ?_⟩
    intro a ha
    rw [(hasDerivAt_stationaryShare p ha.1.le ha.2).deriv]
    have hη : 0 < p.eta := by
      rcases eq_or_lt_of_le p.eta_nonneg with hz | hpos
      · change p.eta * p.b = 1 at h
        norm_num [← hz] at h
      · exact hpos
    have hn : marginalNumerator p a < 0 := by
      unfold marginalNumerator
      nlinarith [mul_pos hη ha.1]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos p.mu_pos p.kappa_pos) hn)
      (pow_pos (denominator_pos p ha.1.le) 2)
  · intro h
    obtain ⟨hp, hpr, hrb, hhalf⟩ := strong_thresholds p h
    exact ⟨hp, hpr, hrb, hhalf, return_twice_peak p, strong_strictMonoOn p h,
      strong_strictAntiOn p h, strong_global_max p h, fun _ => strong_max_unique p h,
      fun _ => strong_gain_iff p h, fun _ => gain_eq_return p h,
      fun _ => loss_iff_after_return p h⟩
  · intro a ha
    exact ⟨effort_saturated p ha, learningRate_saturated p ha, share_saturated p ha,
      mixed_pair_decrease p le_rfl p.b_pos ha⟩
  · intro a ha
    exact second_derivative_neg p ha.1 ha.2
  · apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    · exact (continuousOn_stationaryShare p).mono (fun _ h => h.1)
    · intro a ha
      rw [interior_Icc] at ha
      exact second_derivative_neg p ha.1 ha.2

end

end Grados26Learning
