module

public import Grados26Learning.SensitivityBoundary
public import Mathlib.Data.Real.Sqrt

@[expose] public section

namespace Grados26Learning

open Filter Set
open scoped Topology

noncomputable section

theorem effectiveEffort_peak_excess (p : Parameters) (h : 1 < p.eta * p.b) :
    effectiveEffort p (peak p) - p.b = (p.eta * p.b - 1)^2 / (4 * p.eta) := by
  have hη := sensitivity_eta_pos p h
  have hh : 0 < 1 / p.eta := one_div_pos.mpr hη
  have hmax : 0 ≤ p.b - peak p := by
    unfold peak
    linarith [p.b_pos]
  rw [effectiveEffort, effort, max_eq_left hmax]
  unfold peak
  field_simp [ne_of_gt hη] <;> ring

theorem learningRate_peak_gain (p : Parameters) (h : 1 < p.eta * p.b) :
    learningRate p (peak p) - learningRate p 0 =
      p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta) := by
  calc
    _ = p.kappa * (effectiveEffort p (peak p) - p.b) := by
      rw [learningRate, learningRate, effectiveEffort_zero]
      ring
    _ = _ := by rw [effectiveEffort_peak_excess p h]; ring

theorem normalizedPeakGain_eq (p : Parameters) (h : 1 < p.eta * p.b) :
    let D := p.lambda0 + p.kappa * p.b + p.mu
    (stationaryShare p (peak p) - stationaryShare p 0) / (p.eta * p.b - 1)^2 =
      p.mu * p.kappa /
        (4 * p.eta * D * (D + p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta))) := by
  have hη := sensitivity_eta_pos p h
  have hh := (div_lt_iff₀ hη).mpr (by simpa [mul_comm] using h)
  have hp : 0 < peak p := by unfold peak; linarith
  have hn : p.eta * p.b - 1 ≠ 0 := ne_of_gt (sub_pos.mpr h)
  have hup := learningRate_peak_gain p h
  have h0 : learningRate p 0 = p.lambda0 + p.kappa * p.b := by
    rw [learningRate, effectiveEffort_zero]
  have hden := ne_of_gt (denominator_pos p hp.le)
  have hzero := ne_of_gt (denominator_pos p (a := 0) le_rfl)
  dsimp only
  have hgain : learningRate p (peak p) =
      p.lambda0 + p.kappa * p.b + p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta) := by
    linarith
  have hpos : 0 < p.lambda0 + p.kappa * p.b + p.mu := by
    rw [← h0]
    exact denominator_pos p (a := 0) le_rfl
  have hpos' : 0 < p.lambda0 + p.kappa * p.b + p.mu +
      p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta) := by
    exact add_pos_of_pos_of_nonneg hpos (div_nonneg
      (mul_nonneg p.kappa_pos.le (sq_nonneg _)) (by positivity))
  rw [share_difference p le_rfl hp.le, effectiveEffort_zero,
    effectiveEffort_peak_excess p h, h0, hgain]
  have hsum : p.lambda0 + p.kappa * p.b +
      p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta) + p.mu =
      p.lambda0 + p.kappa * p.b + p.mu +
        p.kappa * (p.eta * p.b - 1)^2 / (4 * p.eta) := by ring
  rw [hsum]
  field_simp [ne_of_gt hη, hn, ne_of_gt hpos, ne_of_gt hpos']

theorem peakGain_second_order (p : Parameters) :
    let D := p.lambda0 + p.kappa * p.b + p.mu
    Tendsto (fun η : ℝ =>
      (rawShare p.b p.lambda0 p.kappa p.mu η ((p.b - 1 / η) / 2) -
        rawShare p.b p.lambda0 p.kappa p.mu η 0) / (η * p.b - 1)^2)
      (𝓝[>] (1 / p.b)) (𝓝 (p.mu * p.kappa * p.b / (4 * D^2))) ∧
    0 < p.mu * p.kappa * p.b / (4 * D^2) := by
  dsimp only
  let D := p.lambda0 + p.kappa * p.b + p.mu
  let c := 1 / p.b
  have hd : 0 < D := add_pos (add_pos p.lambda0_pos (mul_pos p.kappa_pos p.b_pos)) p.mu_pos
  have hc : 0 < c := one_div_pos.mpr p.b_pos
  have hcprod : c * p.b = 1 := one_div_mul_cancel (ne_of_gt p.b_pos)
  let den := fun η : ℝ =>
    4 * η * D * (D + p.kappa * (η * p.b - 1)^2 / (4 * η))
  have hden : den c = 4 * c * D^2 := by simp [den, hcprod, pow_two, mul_assoc]
  have hcont : ContinuousAt (fun η : ℝ => p.mu * p.kappa / den η) c := by
    have hl : ContinuousAt (fun η : ℝ => p.kappa * (η * p.b - 1)^2) c := by fun_prop
    have hr : ContinuousAt (fun η : ℝ => 4 * η) c := by fun_prop
    have hq := hl.div hr (show (4 : ℝ) * c ≠ 0 by positivity)
    have ht : ContinuousAt (fun η : ℝ => 4 * η * D) c := by fun_prop
    have hD : ContinuousAt (fun _ : ℝ => D) c := continuousAt_const
    have hprod := ht.mul (hD.add hq)
    exact continuousAt_const.div hprod (by
      change den c ≠ 0
      rw [hden]
      exact ne_of_gt (mul_pos (mul_pos (by norm_num) hc) (pow_pos hd 2)))
  have hvalue : p.mu * p.kappa / den c = p.mu * p.kappa * p.b / (4 * D^2) := by
    rw [hden]
    dsimp [c]
    field_simp [ne_of_gt p.b_pos, ne_of_gt hd]
  have hlim := (tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto :
    Tendsto (fun η : ℝ => p.mu * p.kappa / den η) (𝓝[>] c) _)
  rw [hvalue] at hlim
  refine ⟨?_, div_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) p.b_pos)
    (mul_pos (by norm_num) (pow_pos hd 2))⟩
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hηc : c < η := hη
  have hp : 0 < η := lt_trans hc hηc
  let q : Parameters := { p with eta := η, eta_nonneg := hp.le }
  have hq : 1 < q.eta * q.b := (critical_complementarity_iff q).mpr hηc
  exact (normalizedPeakGain_eq q hq).symm

private theorem ratio_lt_at_root {A B x y z r : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hr : 0 < r) (hne : z ≠ r) (hr2 : A * B = x * y * r^2) :
    z / ((A + x * z) * (B + y * z)) < r / ((A + x * r) * (B + y * r)) := by
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have heq : r * ((A + x * z) * (B + y * z)) -
      z * ((A + x * r) * (B + y * r)) = r * x * y * (z - r)^2 := by
    calc
      _ = (r - z) * (A * B) + x * y * (r * z^2 - z * r^2) := by ring
      _ = _ := by rw [hr2]; ring
  linarith only [heq, mul_pos (mul_pos (mul_pos hr hx) hy)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))]

private theorem gain_identity {l k m x y : ℝ}
    (h₁ : l + k * x + m ≠ 0) (h₀ : l + k * y + m ≠ 0) :
    (l + k * x) / (l + k * x + m) - (l + k * y) / (l + k * y + m) =
      m * k * (x - y) / ((l + k * x + m) * (l + k * y + m)) := by
  field_simp [h₁, h₀] <;> ring

theorem gain_depreciation_strict_max (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 < a) (har : a < returnPoint p) :
    let f := fun m : ℝ => rawShare p.b p.lambda0 p.kappa m p.eta a -
      rawShare p.b p.lambda0 p.kappa m p.eta 0
    let r := Real.sqrt (learningRate p a * learningRate p 0)
    0 < r ∧ ∀ m > 0, m ≠ r → f m < f r := by
  dsimp only
  let x := effectiveEffort p a
  let A := p.lambda0 + p.kappa * x
  let B := p.lambda0 + p.kappa * p.b
  have hx := (gain_region p h ha har).2
  have hA : 0 < A := learningRate_pos p ha.le
  have hB : 0 < B := add_pos p.lambda0_pos (mul_pos p.kappa_pos p.b_pos)
  have hzero : learningRate p 0 = B := by rw [learningRate, effectiveEffort_zero]
  rw [hzero]
  change 0 < Real.sqrt (A * B) ∧ _
  let r := Real.sqrt (A * B)
  have hr : 0 < r := Real.sqrt_pos.2 (mul_pos hA hB)
  refine ⟨hr, ?_⟩
  intro m hm hmr
  have heq (z : ℝ) (hz : 0 < z) :
      rawShare p.b p.lambda0 p.kappa z p.eta a - rawShare p.b p.lambda0 p.kappa z p.eta 0 =
        p.kappa * (x - p.b) * (z / ((A + z) * (B + z))) := by
    have h1 : p.lambda0 + p.kappa * x + z ≠ 0 := ne_of_gt (add_pos hA hz)
    have h0 : p.lambda0 + p.kappa * p.b + z ≠ 0 := ne_of_gt (add_pos hB hz)
    unfold rawShare
    simp only [sub_zero, max_eq_left p.b_pos.le, mul_zero, add_zero, mul_one]
    change (p.lambda0 + p.kappa * x) / (p.lambda0 + p.kappa * x + z) -
      (p.lambda0 + p.kappa * p.b) / (p.lambda0 + p.kappa * p.b + z) = _
    rw [gain_identity h1 h0]
    simp only [A, B, ← mul_div_assoc]
    congr 1
    ring
  change m ≠ r at hmr
  change rawShare p.b p.lambda0 p.kappa m p.eta a - rawShare p.b p.lambda0 p.kappa m p.eta 0 <
    rawShare p.b p.lambda0 p.kappa r p.eta a - rawShare p.b p.lambda0 p.kappa r p.eta 0
  rw [heq m hm, heq r hr]
  apply mul_lt_mul_of_pos_left _ (mul_pos p.kappa_pos hx)
  simpa only [one_mul] using ratio_lt_at_root hA hB (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1) hm hr hmr
    (by simpa only [one_mul] using (Real.sq_sqrt (mul_nonneg hA.le hB.le)).symm)

theorem gain_effortSensitivity_strict_max (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 < a) (har : a < returnPoint p) :
    let f := fun k : ℝ => rawShare p.b p.lambda0 k p.mu p.eta a -
      rawShare p.b p.lambda0 k p.mu p.eta 0
    let r := (p.lambda0 + p.mu) / Real.sqrt (effectiveEffort p a * p.b)
    0 < r ∧ ∀ k > 0, k ≠ r → f k < f r := by
  dsimp only
  let x := effectiveEffort p a
  let B := p.lambda0 + p.mu
  let s := Real.sqrt (x * p.b)
  let r := B / s
  have hΔ := (gain_region p h ha har).2
  have hx : 0 < x := by dsimp [x]; linarith [p.b_pos]
  have hB : 0 < B := add_pos p.lambda0_pos p.mu_pos
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos hx p.b_pos)
  have hr : 0 < r := div_pos hB hs
  refine ⟨hr, ?_⟩
  intro k hk hkr
  have heq (z : ℝ) (hz : 0 < z) :
      rawShare p.b p.lambda0 z p.mu p.eta a - rawShare p.b p.lambda0 z p.mu p.eta 0 =
        p.mu * (x - p.b) * (z / ((B + x * z) * (B + p.b * z))) := by
    have h1 := ne_of_gt (add_pos (add_pos p.lambda0_pos (mul_pos hz hx)) p.mu_pos)
    have h0 := ne_of_gt (add_pos (add_pos p.lambda0_pos (mul_pos hz p.b_pos)) p.mu_pos)
    unfold rawShare
    simp only [sub_zero, max_eq_left p.b_pos.le, mul_zero, add_zero, mul_one]
    change (p.lambda0 + z * x) / (p.lambda0 + z * x + p.mu) -
      (p.lambda0 + z * p.b) / (p.lambda0 + z * p.b + p.mu) = _
    rw [gain_identity h1 h0]
    simp only [B, ← mul_div_assoc]
    congr 1 <;> ring
  have hs2 : s^2 = x * p.b := Real.sq_sqrt (mul_nonneg hx.le p.b_pos.le)
  have hr2 : B * B = x * p.b * r^2 := by
    rw [← hs2]
    dsimp [r]
    field_simp [ne_of_gt hs] <;> ring
  rw [heq k hk, heq r hr]
  exact mul_lt_mul_of_pos_left (ratio_lt_at_root hB hB hx p.b_pos hk hr hkr hr2)
    (mul_pos p.mu_pos hΔ)

end
end Grados26Learning
