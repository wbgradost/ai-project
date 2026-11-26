module

public import Grados26Learning.Sensitivity

@[expose] public section

namespace Grados26Learning

open Filter Set
open scoped Topology

noncomputable section

theorem ratePartial_zero_iff (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    p.mu * effectiveEffort p a / (learningRate p a + p.mu)^2 = 0 ↔ p.b ≤ a := by
  constructor
  · intro hz
    by_contra h
    have hp := effectiveEffort_pos p ha (lt_of_not_ge h)
    exact (ne_of_gt (div_pos (mul_pos p.mu_pos hp) (pow_pos (denominator_pos p ha) 2))) hz
  · intro h
    simp [effectiveEffort_saturated p h]

theorem complementarityPartial_zero_iff (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    p.mu * p.kappa * a * max (p.b - a) 0 / (learningRate p a + p.mu)^2 = 0 ↔
      a = 0 ∨ p.b ≤ a := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h.1)
    have hmax : 0 < max (p.b - a) 0 :=
      lt_of_lt_of_le (sub_pos.mpr h.2) (le_max_left _ _)
    exact (ne_of_gt (div_pos (mul_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) hap) hmax)
      (pow_pos (denominator_pos p ha) 2))) hz
  · rintro (rfl | hab)
    · simp
    · simp [max_eq_right (sub_nonpos.mpr hab)]

theorem hasDerivAt_rawShare_b_saturated (p : Parameters) {a : ℝ} (h : p.b < a) :
    HasDerivAt (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a) 0 p.b := by
  have heq : (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a) =ᶠ[𝓝 p.b]
      (fun _ : ℝ => p.lambda0 / (p.lambda0 + p.mu)) := by
    filter_upwards [Iio_mem_nhds h] with b hb
    have hba : b < a := hb
    simp [rawShare, max_eq_right (sub_nonpos.mpr hba.le)]
  exact (hasDerivAt_const p.b _).congr_of_eventuallyEq heq

theorem hasDerivWithinAt_rawShare_b_boundary (p : Parameters) :
    let f := fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta p.b
    let rightSlope := p.mu * p.kappa * (1 + p.eta * p.b) / (p.lambda0 + p.mu)^2
    HasDerivWithinAt f 0 (Iic p.b) p.b ∧
      HasDerivWithinAt f rightSlope (Ici p.b) p.b ∧ 0 < rightSlope := by
  dsimp only
  have hden := ne_of_gt (add_pos p.lambda0_pos p.mu_pos)
  have hfactor : 0 < 1 + p.eta * p.b := by
    linarith [mul_nonneg p.eta_nonneg p.b_pos.le]
  constructor
  · apply (hasDerivWithinAt_const p.b (Iic p.b) (p.lambda0 / (p.lambda0 + p.mu))).congr_of_mem
    · intro b hb
      change b ≤ p.b at hb
      simp [rawShare, max_eq_right (sub_nonpos.mpr hb)]
    · change p.b ≤ p.b
      exact le_rfl
  · refine ⟨?_, div_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) hfactor)
      (pow_pos (add_pos p.lambda0_pos p.mu_pos) 2)⟩
    let numer := fun b : ℝ => p.lambda0 + p.kappa * ((b - p.b) * (1 + p.eta * p.b))
    have hnum : HasDerivAt numer (p.kappa * (1 + p.eta * p.b)) p.b := by
      simpa only [numer, id_eq, sub_zero, one_mul, zero_add] using
        HasDerivAt.fun_add (hasDerivAt_const p.b p.lambda0)
          (HasDerivAt.const_mul p.kappa (HasDerivAt.mul_const
            (HasDerivAt.fun_sub (hasDerivAt_id p.b) (hasDerivAt_const p.b p.b))
            (1 + p.eta * p.b)))
    have hn : numer p.b + p.mu ≠ 0 := by simpa [numer] using hden
    have hdiv := HasDerivAt.fun_div hnum
      (HasDerivAt.fun_add hnum (hasDerivAt_const p.b p.mu)) hn
    have hd : HasDerivAt (fun b : ℝ => numer b / (numer b + p.mu))
        (p.mu * p.kappa * (1 + p.eta * p.b) / (p.lambda0 + p.mu)^2) p.b := by
      convert hdiv using 1
      simp only [numer, sub_self, zero_mul, mul_zero, add_zero]
      congr 1
      ring
    apply (hd.hasDerivWithinAt (s := Ici p.b)).congr_of_mem
    · intro b hb
      change p.b ≤ b at hb
      simp [rawShare, numer, max_eq_left (sub_nonneg.mpr hb)]
    · change p.b ≤ p.b
      exact le_rfl

theorem criticalEta_derivative {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => 1 / x) (-1 / b^2) b := by
  simpa [one_div] using (hasDerivAt_id b).inv (ne_of_gt hb)

theorem threshold_limits {b : ℝ} (hb : 0 < b) :
    Tendsto (fun η : ℝ => (b - 1 / η) / 2) (𝓝[>] (1 / b)) (𝓝 0) ∧
    Tendsto (fun η : ℝ => b - 1 / η) (𝓝[>] (1 / b)) (𝓝 0) ∧
    Tendsto (fun η : ℝ => (b - 1 / η) / 2) atTop (𝓝 (b / 2)) ∧
    Tendsto (fun η : ℝ => b - 1 / η) atTop (𝓝 b) := by
  have hn : (1 / b : ℝ) ≠ 0 := ne_of_gt (one_div_pos.mpr hb)
  have hcrit : Tendsto (fun η : ℝ => b - 1 / η) (𝓝[>] (1 / b)) (𝓝 0) := by
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] (1 / b)) (𝓝 (1 / b)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hinv : Tendsto (fun η : ℝ => 1 / η) (𝓝[>] (1 / b)) (𝓝 (1 / (1 / b))) :=
      tendsto_const_nhds.div hid hn
    have h : Tendsto (fun η : ℝ => b - 1 / η) (𝓝[>] (1 / b)) (𝓝 (b - 1 / (1 / b))) :=
      tendsto_const_nhds.sub hinv
    simpa only [one_div_one_div, sub_self] using h
  have hinv : Tendsto (fun η : ℝ => 1 / η) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have htop : Tendsto (fun η : ℝ => b - 1 / η) atTop (𝓝 b) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := b)).sub hinv
  exact ⟨by simpa using hcrit.div_const (2 : ℝ), hcrit, htop.div_const 2, htop⟩

theorem stationary_gain_strictAntiOn_lambda0 (p : Parameters)
    (h : 1 < p.eta * p.b) {a : ℝ} (ha : 0 < a) (har : a < returnPoint p) :
    StrictAntiOn (fun l : ℝ =>
      rawShare p.b l p.kappa p.mu p.eta a - rawShare p.b l p.kappa p.mu p.eta 0)
      (Ioi (0 : ℝ)) := by
  let x := effectiveEffort p a
  let numerator := p.mu * p.kappa * (x - p.b)
  let D := fun l f : ℝ => l + p.kappa * f + p.mu
  have hΔ : 0 < x - p.b := (gain_region p h ha har).2
  have hx : 0 < x := lt_trans p.b_pos (sub_pos.mp hΔ)
  have hn : 0 < numerator := mul_pos (mul_pos p.mu_pos p.kappa_pos) hΔ
  have identity (l : ℝ) (hl : 0 < l) :
      rawShare p.b l p.kappa p.mu p.eta a - rawShare p.b l p.kappa p.mu p.eta 0 =
        numerator / (D l x * D l p.b) := by
    let q : Parameters := { p with lambda0 := l, lambda0_pos := hl }
    simpa only [learningRate, effectiveEffort_zero] using
      (share_difference q (u := 0) (v := a) le_rfl ha.le)
  have pos (l f : ℝ) (hl : 0 < l) (hf : 0 < f) : 0 < D l f :=
    add_pos (add_pos hl (mul_pos p.kappa_pos hf)) p.mu_pos
  intro l hl r hr hlr
  change 0 < l at hl
  change 0 < r at hr
  change rawShare p.b r p.kappa p.mu p.eta a - rawShare p.b r p.kappa p.mu p.eta 0 <
    rawShare p.b l p.kappa p.mu p.eta a - rawShare p.b l p.kappa p.mu p.eta 0
  rw [identity l hl, identity r hr]
  have hDx : D l x < D r x := by dsimp only [D]; linarith only [hlr]
  have hDb : D l p.b < D r p.b := by dsimp only [D]; linarith only [hlr]
  have hprod : D l x * D l p.b < D r x * D r p.b :=
    (mul_lt_mul_of_pos_right hDx (pos l p.b hl p.b_pos)).trans
      (mul_lt_mul_of_pos_left hDb (pos r x hr hx))
  exact (div_lt_div_iff₀ (mul_pos (pos r x hr hx) (pos r p.b hr p.b_pos))
    (mul_pos (pos l x hl hx) (pos l p.b hl p.b_pos))).mpr
      (mul_lt_mul_of_pos_left hprod hn)

end
end Grados26Learning
