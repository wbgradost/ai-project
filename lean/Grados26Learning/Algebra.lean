import Grados26Learning.Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Grados26Learning

noncomputable section

theorem effort_nonneg (p : Parameters) (a : ℝ) : 0 ≤ effort p a :=
  le_max_right _ _

theorem effort_active (p : Parameters) {a : ℝ} (ha : a ≤ p.b) :
    effort p a = p.b - a := by
  exact max_eq_left (sub_nonneg.mpr ha)

theorem effort_saturated (p : Parameters) {a : ℝ} (ha : p.b ≤ a) :
    effort p a = 0 := by
  exact max_eq_right (sub_nonpos.mpr ha)

theorem effectiveEffort_nonneg (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ effectiveEffort p a := by
  unfold effectiveEffort
  exact mul_nonneg (effort_nonneg p a)
    (by nlinarith [mul_nonneg p.eta_nonneg ha])

theorem effectiveEffort_pos (p : Parameters) {a : ℝ} (ha : 0 ≤ a) (hab : a < p.b) :
    0 < effectiveEffort p a := by
  rw [effectiveEffort, effort_active p hab.le]
  exact mul_pos (sub_pos.mpr hab) (by nlinarith [mul_nonneg p.eta_nonneg ha])

theorem learningRate_pos (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    0 < learningRate p a := by
  unfold learningRate
  exact add_pos_of_pos_of_nonneg p.lambda0_pos
    (mul_nonneg p.kappa_pos.le (effectiveEffort_nonneg p ha))

theorem denominator_pos (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    0 < learningRate p a + p.mu :=
  add_pos (learningRate_pos p ha) p.mu_pos

theorem share_pos (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    0 < stationaryShare p a :=
  div_pos (learningRate_pos p ha) (denominator_pos p ha)

theorem share_lt_one (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    stationaryShare p a < 1 := by
  unfold stationaryShare
  exact (div_lt_one (denominator_pos p ha)).2 (by linarith [p.mu_pos])

theorem learningRate_active (p : Parameters) {a : ℝ} (ha : a ≤ p.b) :
    learningRate p a = activeRate p a := by
  simp only [learningRate, effectiveEffort, effort_active p ha, activeRate]

theorem share_active (p : Parameters) {a : ℝ} (ha : a ≤ p.b) :
    stationaryShare p a = activeShare p a := by
  simp only [stationaryShare, activeShare, learningRate_active p ha]

theorem effectiveEffort_saturated (p : Parameters) {a : ℝ} (ha : p.b ≤ a) :
    effectiveEffort p a = 0 := by
  simp only [effectiveEffort, effort_saturated p ha, zero_mul]

theorem learningRate_saturated (p : Parameters) {a : ℝ} (ha : p.b ≤ a) :
    learningRate p a = p.lambda0 := by
  simp only [learningRate, effectiveEffort_saturated p ha, mul_zero, add_zero]

theorem share_saturated (p : Parameters) {a : ℝ} (ha : p.b ≤ a) :
    stationaryShare p a = p.lambda0 / (p.lambda0 + p.mu) := by
  simp only [stationaryShare, learningRate_saturated p ha]

theorem effectiveEffort_zero (p : Parameters) : effectiveEffort p 0 = p.b := by
  simp [effectiveEffort, effort_active p p.b_pos.le]

theorem share_difference (p : Parameters) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    stationaryShare p v - stationaryShare p u =
      p.mu * p.kappa * (effectiveEffort p v - effectiveEffort p u) /
        ((learningRate p v + p.mu) * (learningRate p u + p.mu)) := by
  have hdu := ne_of_gt (denominator_pos p hu)
  have hdv := ne_of_gt (denominator_pos p hv)
  unfold stationaryShare
  field_simp
  unfold learningRate
  ring

theorem effectiveEffort_active_difference (p : Parameters) {u v : ℝ}
    (hu : u ≤ p.b) (hv : v ≤ p.b) :
    effectiveEffort p v - effectiveEffort p u =
      (v - u) * (p.eta * (p.b - u - v) - 1) := by
  rw [effectiveEffort, effectiveEffort, effort_active p hu, effort_active p hv]
  ring

theorem share_active_difference (p : Parameters) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ p.b) :
    stationaryShare p v - stationaryShare p u =
      p.mu * p.kappa * (v - u) * (p.eta * (p.b - u - v) - 1) /
        ((learningRate p v + p.mu) * (learningRate p u + p.mu)) := by
  rw [share_difference p hu (le_trans hu huv.le),
    effectiveEffort_active_difference p (le_trans huv.le hv) hv]
  ring

theorem share_order_iff (p : Parameters) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    stationaryShare p u < stationaryShare p v ↔
      effectiveEffort p u < effectiveEffort p v := by
  have hd := mul_pos (denominator_pos p hv) (denominator_pos p hu)
  have hk := mul_pos p.mu_pos p.kappa_pos
  rw [← sub_pos, share_difference p hu hv, div_pos_iff_of_pos_right hd,
    mul_pos_iff_of_pos_left hk, sub_pos]

theorem active_pair_increase_iff (p : Parameters) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ p.b) :
    stationaryShare p u < stationaryShare p v ↔ p.eta * (p.b - u - v) > 1 := by
  rw [share_order_iff p hu (le_trans hu huv.le), ← sub_pos,
    effectiveEffort_active_difference p (le_trans huv.le hv) hv,
    mul_pos_iff_of_pos_left (sub_pos.mpr huv), sub_pos]

theorem active_pair_equal_iff (p : Parameters) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ p.b) :
    stationaryShare p v = stationaryShare p u ↔ p.eta * (p.b - u - v) = 1 := by
  have hd := ne_of_gt (mul_pos (denominator_pos p (le_trans hu huv.le))
    (denominator_pos p hu))
  have hk := ne_of_gt (mul_pos (mul_pos p.mu_pos p.kappa_pos) (sub_pos.mpr huv))
  rw [← sub_eq_zero, share_active_difference p hu huv hv, div_eq_zero_iff, mul_eq_zero]
  simp only [hd, hk, false_or, or_false, sub_eq_zero]

theorem active_pair_decrease_iff (p : Parameters) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ p.b) :
    stationaryShare p v < stationaryShare p u ↔ p.eta * (p.b - u - v) < 1 := by
  have hd := mul_pos (denominator_pos p (le_trans hu huv.le)) (denominator_pos p hu)
  have hk := mul_pos (mul_pos p.mu_pos p.kappa_pos) (sub_pos.mpr huv)
  rw [← sub_neg, share_active_difference p hu huv hv, div_lt_iff₀ hd]
  simp only [zero_mul]
  constructor
  · intro hn
    by_contra hnot
    have hnonneg := mul_nonneg hk.le (sub_nonneg.mpr (le_of_not_gt hnot))
    linarith
  · intro hn
    exact mul_neg_of_pos_of_neg hk (sub_neg.mpr hn)

theorem mixed_pair_decrease (p : Parameters) {u v : ℝ}
    (hu : 0 ≤ u) (hub : u < p.b) (hbv : p.b ≤ v) :
    stationaryShare p v < stationaryShare p u := by
  rw [share_order_iff p (le_trans p.b_pos.le hbv) hu,
    effectiveEffort_saturated p hbv]
  exact effectiveEffort_pos p hu hub

theorem plateau_pair_equal (p : Parameters) {u v : ℝ}
    (hu : p.b ≤ u) (hv : p.b ≤ v) :
    stationaryShare p v = stationaryShare p u := by
  rw [share_saturated p hu, share_saturated p hv]

theorem skillFOSD_iff (qHigh qLow sL sH : ℝ) (hs : sL < sH) :
    skillFOSD qHigh qLow sL sH ↔ qLow ≤ qHigh := by
  constructor
  · intro h
    have hh := h sL
    simp only [skillCDF, lt_self_iff_false, if_false, hs, if_true] at hh
    linarith
  · intro h x
    unfold skillCDF
    split_ifs <;> linarith

theorem meanSkill_order_iff (qHigh qLow sL sH : ℝ) (hs : sL < sH) :
    meanSkill qLow sL sH ≤ meanSkill qHigh sL sH ↔ qLow ≤ qHigh := by
  have hdiff : meanSkill qHigh sL sH - meanSkill qLow sL sH =
      (sH - sL) * (qHigh - qLow) := by unfold meanSkill; ring
  rw [← sub_nonneg, hdiff, mul_nonneg_iff_of_pos_left (sub_pos.mpr hs), sub_nonneg]

end

end Grados26Learning
