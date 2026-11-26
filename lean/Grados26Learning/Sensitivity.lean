module

public import Grados26Learning.Algebra
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Grados26Learning

open Set Filter
open scoped Topology

noncomputable section

theorem critical_complementarity_iff (p : Parameters) :
    1 < p.eta*p.b ↔ 1/p.b < p.eta := by
  rw [div_lt_iff₀ p.b_pos]

theorem thresholds_independent_of_rates (p q : Parameters)
    (hb : q.b = p.b) (hη : q.eta = p.eta) :
    peak q = peak p ∧ returnPoint q = returnPoint p := by
  simp only [peak, returnPoint, hb, hη, and_self]

theorem sensitivity_eta_pos (p : Parameters) (h : 1 < p.eta*p.b) : 0 < p.eta := by
  have hn : p.eta ≠ 0 := by
    intro hz
    norm_num [hz] at h
  exact lt_of_le_of_ne p.eta_nonneg (Ne.symm hn)

theorem threshold_partial_derivatives (p : Parameters) (h : 1 < p.eta*p.b) :
    HasDerivAt (fun η : ℝ => (p.b-1/η)/2) (1/(2*p.eta^2)) p.eta ∧
    HasDerivAt (fun η : ℝ => p.b-1/η) (1/p.eta^2) p.eta ∧
    HasDerivAt (fun b : ℝ => (b-1/p.eta)/2) (1/2) p.b ∧
    HasDerivAt (fun b : ℝ => b-1/p.eta) 1 p.b := by
  have hn := ne_of_gt (sensitivity_eta_pos p h)
  have hi := (hasDerivAt_id p.eta).inv hn
  have hr := HasDerivAt.fun_sub (hasDerivAt_const p.eta p.b) hi
  have hp := HasDerivAt.div_const hr 2
  have hb := HasDerivAt.fun_sub (hasDerivAt_id p.b) (hasDerivAt_const p.b (1 / p.eta))
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hp using 1 <;> simp only [one_div, id_eq, Pi.inv_apply] <;> ring
  · convert hr using 1 <;> simp only [one_div, id_eq, Pi.inv_apply] <;> ring
  · convert HasDerivAt.div_const hb 2 using 1 <;> norm_num
  · simpa only [sub_zero] using hb

private theorem quotient_partial_l (l k m f : ℝ) (hD : l+k*f+m ≠ 0) :
    HasDerivAt (fun x : ℝ => (x+k*f)/(x+k*f+m))
      (m/(l+k*f+m)^2) l := by
  have hn := HasDerivAt.fun_add (hasDerivAt_id l) (hasDerivAt_const l (k * f))
  have hd := HasDerivAt.fun_div hn (HasDerivAt.fun_add hn (hasDerivAt_const l m)) hD
  convert hd using 1 <;> simp only [id_eq] <;> ring

private theorem quotient_partial_k (l k m f : ℝ) (hD : l+k*f+m ≠ 0) :
    HasDerivAt (fun x : ℝ => (l+x*f)/(l+x*f+m))
      (m*f/(l+k*f+m)^2) k := by
  have hn := HasDerivAt.fun_add (hasDerivAt_const k l) (HasDerivAt.mul_const (hasDerivAt_id k) f)
  have hd := HasDerivAt.fun_div hn (HasDerivAt.fun_add hn (hasDerivAt_const k m)) hD
  convert hd using 1 <;> simp only [id_eq] <;> ring

private theorem quotient_partial_m (l k m f : ℝ) (hD : l+k*f+m ≠ 0) :
    HasDerivAt (fun x : ℝ => (l+k*f)/(l+k*f+x))
      (-(l+k*f)/(l+k*f+m)^2) m := by
  have hn := hasDerivAt_const m (l+k*f)
  have hd := HasDerivAt.fun_div hn (HasDerivAt.fun_add hn (hasDerivAt_id m)) hD
  convert hd using 1 <;> simp only [id_eq] <;> ring

theorem hasDerivAt_rawShare_l (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun l : ℝ => rawShare p.b l p.kappa p.mu p.eta a)
      (p.mu/(learningRate p a+p.mu)^2) p.lambda0 := by
  have hD : p.lambda0+p.kappa*effectiveEffort p a+p.mu ≠ 0 :=
    ne_of_gt (denominator_pos p ha)
  simpa only [rawShare, learningRate, effectiveEffort, effort] using
    quotient_partial_l p.lambda0 p.kappa p.mu (effectiveEffort p a) hD

theorem hasDerivAt_rawShare_k (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun k : ℝ => rawShare p.b p.lambda0 k p.mu p.eta a)
      (p.mu*effectiveEffort p a/(learningRate p a+p.mu)^2) p.kappa := by
  have hD : p.lambda0+p.kappa*effectiveEffort p a+p.mu ≠ 0 :=
    ne_of_gt (denominator_pos p ha)
  simpa only [rawShare, learningRate, effectiveEffort, effort] using
    quotient_partial_k p.lambda0 p.kappa p.mu (effectiveEffort p a) hD

theorem hasDerivAt_rawShare_m (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun m : ℝ => rawShare p.b p.lambda0 p.kappa m p.eta a)
      (-learningRate p a/(learningRate p a+p.mu)^2) p.mu := by
  have hD : p.lambda0+p.kappa*effectiveEffort p a+p.mu ≠ 0 :=
    ne_of_gt (denominator_pos p ha)
  simpa only [rawShare, learningRate, effectiveEffort, effort] using
    quotient_partial_m p.lambda0 p.kappa p.mu (effectiveEffort p a) hD

theorem hasDerivAt_rawShare_eta (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun η : ℝ => rawShare p.b p.lambda0 p.kappa p.mu η a)
      (p.mu*p.kappa*a*max (p.b - a) 0/(learningRate p a+p.mu)^2) p.eta := by
  have hD := ne_of_gt (denominator_pos p ha)
  have hf := HasDerivAt.const_mul (max (p.b - a) 0)
    (HasDerivAt.fun_add (hasDerivAt_const p.eta 1) (HasDerivAt.mul_const (hasDerivAt_id p.eta) a))
  have hn := HasDerivAt.fun_add (hasDerivAt_const p.eta p.lambda0)
    (HasDerivAt.const_mul p.kappa hf)
  have hd := HasDerivAt.fun_div hn (HasDerivAt.fun_add hn (hasDerivAt_const p.eta p.mu)) hD
  convert hd using 1 <;> dsimp only [rawShare, learningRate, effectiveEffort, effort, id_eq] <;> ring

theorem hasDerivAt_rawShare_b (p : Parameters) {a : ℝ} (ha : 0 ≤ a) (hab : a < p.b) :
    HasDerivAt (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a)
      (p.mu*p.kappa*(1+p.eta*a)/(learningRate p a+p.mu)^2) p.b := by
  have hm : max (p.b-a) 0 = p.b-a := max_eq_left (sub_nonneg.mpr hab.le)
  have hD : p.lambda0+p.kappa*((p.b-a)*(1+p.eta*a))+p.mu ≠ 0 := by
    simpa only [learningRate, effectiveEffort, effort, hm] using ne_of_gt (denominator_pos p ha)
  have hf := HasDerivAt.mul_const
    (HasDerivAt.fun_sub (hasDerivAt_id p.b) (hasDerivAt_const p.b a)) (1 + p.eta * a)
  have hn := HasDerivAt.fun_add (hasDerivAt_const p.b p.lambda0)
    (HasDerivAt.const_mul p.kappa hf)
  have hd := HasDerivAt.fun_div hn (HasDerivAt.fun_add hn (hasDerivAt_const p.b p.mu)) hD
  have heq : (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a) =ᶠ[𝓝 p.b]
      (fun b : ℝ => (p.lambda0+p.kappa*((b-a)*(1+p.eta*a))) /
        (p.lambda0+p.kappa*((b-a)*(1+p.eta*a))+p.mu)) := by
    filter_upwards [Ioi_mem_nhds hab] with b hb
    have habx : a < b := hb
    simp only [rawShare, max_eq_left (sub_nonneg.mpr habx.le)]
  have hd' := hd.congr_of_eventuallyEq heq
  convert hd' using 1 <;> dsimp only [learningRate, effectiveEffort, effort] <;> rw [hm] <;> simp only [id_eq] <;> ring

theorem stationary_level_partials (p : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    let D := learningRate p a+p.mu
    HasDerivAt (fun l : ℝ => rawShare p.b l p.kappa p.mu p.eta a) (p.mu/D^2) p.lambda0 ∧
    0 < p.mu/D^2 ∧
    HasDerivAt (fun k : ℝ => rawShare p.b p.lambda0 k p.mu p.eta a)
      (p.mu*effectiveEffort p a/D^2) p.kappa ∧
    0 ≤ p.mu*effectiveEffort p a/D^2 ∧
    HasDerivAt (fun m : ℝ => rawShare p.b p.lambda0 p.kappa m p.eta a)
      (-learningRate p a/D^2) p.mu ∧
    -learningRate p a/D^2 < 0 ∧
    HasDerivWithinAt (fun η : ℝ => rawShare p.b p.lambda0 p.kappa p.mu η a)
      (p.mu*p.kappa*a*max (p.b - a) 0/D^2) (Ici 0) p.eta ∧
    0 ≤ p.mu*p.kappa*a*max (p.b - a) 0/D^2 ∧
    (a < p.b →
      HasDerivAt (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a)
        (p.mu*p.kappa*(1+p.eta*a)/D^2) p.b ∧
      0 < p.mu*p.kappa*(1+p.eta*a)/D^2) := by
  dsimp only
  have hD := pow_pos (denominator_pos p ha) 2
  refine ⟨hasDerivAt_rawShare_l p ha, div_pos p.mu_pos hD,
    hasDerivAt_rawShare_k p ha,
    div_nonneg (mul_nonneg p.mu_pos.le (effectiveEffort_nonneg p ha)) hD.le,
    hasDerivAt_rawShare_m p ha, ?_,
    (hasDerivAt_rawShare_eta p ha).hasDerivWithinAt, ?_, ?_⟩
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos (learningRate_pos p ha)) hD
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg p.mu_pos.le p.kappa_pos.le) ha) (le_max_right _ _)) hD.le
  · intro hab
    refine ⟨hasDerivAt_rawShare_b p ha hab, ?_⟩
    have hp : 0 < 1+p.eta*a := by nlinarith [mul_nonneg p.eta_nonneg ha]
    exact div_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) hp) hD

theorem common_rate_scaling (p : Parameters) {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    rawShare p.b (c*p.lambda0) (c*p.kappa) (c*p.mu) p.eta a = stationaryShare p a ∧
    ((c*p.lambda0)+(c*p.kappa)*effectiveEffort p a+c*p.mu) = c*(learningRate p a+p.mu) := by
  have hc0 := ne_of_gt hc
  have hD0 := ne_of_gt (denominator_pos p ha)
  constructor
  · unfold rawShare stationaryShare learningRate effectiveEffort effort
    have hn : c*p.lambda0+c*p.kappa*(max (p.b - a) 0*(1+p.eta*a)) =
        c*(p.lambda0+p.kappa*(max (p.b - a) 0*(1+p.eta*a))) := by ring
    have hd : c*p.lambda0+c*p.kappa*(max (p.b - a) 0*(1+p.eta*a))+c*p.mu =
        c*(p.lambda0+p.kappa*(max (p.b - a) 0*(1+p.eta*a))+p.mu) := by ring
    rw [hd, hn]
    exact mul_div_mul_left _ _ hc0
  · unfold learningRate
    ring

private theorem gain_l_slope_identity (l k m x y : ℝ)
    (h1 : l+k*x+m ≠ 0) (h0 : l+k*y+m ≠ 0) :
    m/(l+k*x+m)^2-m/(l+k*y+m)^2 =
      -(m*k*(x-y)*((l+k*x+m)+(l+k*y+m))) /
        ((l+k*x+m)^2*(l+k*y+m)^2) := by
  rw [div_sub_div _ _ (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  congr 1
  ring

private theorem gain_m_slope_identity (l k m x y : ℝ)
    (h1 : l+k*x+m ≠ 0) (h0 : l+k*y+m ≠ 0) :
    -(l+k*x)/(l+k*x+m)^2-(-(l+k*y)/(l+k*y+m)^2) =
      k*(x-y)*((l+k*x)*(l+k*y)-m^2) /
        ((l+k*x+m)^2*(l+k*y+m)^2) := by
  rw [div_sub_div _ _ (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  congr 1
  ring

private theorem gain_k_slope_identity (l k m x y : ℝ)
    (h1 : l+k*x+m ≠ 0) (h0 : l+k*y+m ≠ 0) :
    m*x/(l+k*x+m)^2-m*y/(l+k*y+m)^2 =
      m*(x-y)*((l+m)^2-k^2*x*y) /
        ((l+k*x+m)^2*(l+k*y+m)^2) := by
  rw [div_sub_div _ _ (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  congr 1
  ring

private theorem positive_factor_sign (C t D : ℝ) (hC : 0 < C) (hD : 0 < D) :
    (0 < C*t/D ↔ 0 < t) ∧ (C*t/D = 0 ↔ t = 0) ∧ (C*t/D < 0 ↔ t < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hD, zero_mul, mul_pos_iff_of_pos_left hC]
  · rw [div_eq_zero_iff, mul_eq_zero]
    simp only [ne_of_gt hC, ne_of_gt hD, false_or, or_false]
  · rw [div_lt_iff₀ hD, zero_mul]
    constructor
    · intro h
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg hC.le (le_of_not_gt hn))) h
    · intro h
      exact mul_neg_of_pos_of_neg hC h

theorem gain_region (p : Parameters) (h : 1 < p.eta*p.b)
    {a : ℝ} (ha : 0 < a) (har : a < returnPoint p) :
    a < p.b ∧ 0 < effectiveEffort p a-p.b := by
  have hη := sensitivity_eta_pos p h
  have hid : p.eta*returnPoint p = p.eta*p.b-1 := by
    unfold returnPoint
    field_simp [ne_of_gt hη]
  have hrb : returnPoint p < p.b := by
    unfold returnPoint
    exact sub_lt_self _ (one_div_pos.mpr hη)
  have hab := lt_trans har hrb
  have hbr : 0 < p.eta*(p.b-a)-1 := by
    nlinarith [mul_lt_mul_of_pos_left har hη]
  have hdiff := effectiveEffort_active_difference p p.b_pos.le hab.le
  refine ⟨hab, ?_⟩
  rw [effectiveEffort_zero, sub_zero, sub_zero] at hdiff
  rw [hdiff]
  exact mul_pos ha hbr

theorem stationary_gain_partials (p : Parameters) (h : 1 < p.eta*p.b)
    {a : ℝ} (ha : 0 < a) (har : a < returnPoint p) :
    let G := stationaryShare p a-stationaryShare p 0
    let Δ := effectiveEffort p a-p.b
    let gL := fun l : ℝ =>
      rawShare p.b l p.kappa p.mu p.eta a-rawShare p.b l p.kappa p.mu p.eta 0
    let gM := fun m : ℝ =>
      rawShare p.b p.lambda0 p.kappa m p.eta a-rawShare p.b p.lambda0 p.kappa m p.eta 0
    let gK := fun k : ℝ =>
      rawShare p.b p.lambda0 k p.mu p.eta a-rawShare p.b p.lambda0 k p.mu p.eta 0
    0 < Δ ∧ 0 < G ∧
    G = p.mu*p.kappa*Δ /
      ((p.lambda0+p.kappa*effectiveEffort p a+p.mu)*(p.lambda0+p.kappa*p.b+p.mu)) ∧
    DifferentiableAt ℝ gL p.lambda0 ∧ deriv gL p.lambda0 < 0 ∧
    DifferentiableAt ℝ gM p.mu ∧
    ((0 < deriv gM p.mu ↔
        0 < (p.lambda0+p.kappa*effectiveEffort p a)*(p.lambda0+p.kappa*p.b)-p.mu^2) ∧
      (deriv gM p.mu = 0 ↔
        (p.lambda0+p.kappa*effectiveEffort p a)*(p.lambda0+p.kappa*p.b)-p.mu^2 = 0) ∧
      (deriv gM p.mu < 0 ↔
        (p.lambda0+p.kappa*effectiveEffort p a)*(p.lambda0+p.kappa*p.b)-p.mu^2 < 0)) ∧
    DifferentiableAt ℝ gK p.kappa ∧
    ((0 < deriv gK p.kappa ↔ 0 < (p.lambda0+p.mu)^2-p.kappa^2*effectiveEffort p a*p.b) ∧
      (deriv gK p.kappa = 0 ↔ (p.lambda0+p.mu)^2-p.kappa^2*effectiveEffort p a*p.b = 0) ∧
      (deriv gK p.kappa < 0 ↔ (p.lambda0+p.mu)^2-p.kappa^2*effectiveEffort p a*p.b < 0)) := by
  dsimp only
  have hΔ := (gain_region p h ha har).2
  have hD1 := denominator_pos p ha.le
  have hD0 := denominator_pos p (a := 0) le_rfl
  have hD00 : 0 < p.lambda0+p.kappa*p.b+p.mu := by
    simpa only [learningRate, effectiveEffort_zero] using hD0
  have hM := mul_pos (pow_pos hD1 2) (pow_pos hD00 2)
  have hL := HasDerivAt.fun_sub (hasDerivAt_rawShare_l p ha.le) (hasDerivAt_rawShare_l p (a := 0) le_rfl)
  have hMu := HasDerivAt.fun_sub (hasDerivAt_rawShare_m p ha.le) (hasDerivAt_rawShare_m p (a := 0) le_rfl)
  have hK := HasDerivAt.fun_sub (hasDerivAt_rawShare_k p ha.le) (hasDerivAt_rawShare_k p (a := 0) le_rfl)
  have hform := share_difference p (u := 0) (v := a) le_rfl ha.le
  rw [effectiveEffort_zero] at hform
  have hG : 0 < stationaryShare p a-stationaryShare p 0 := by
    rw [hform]
    exact div_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) hΔ) (mul_pos hD1 hD0)
  refine ⟨hΔ, hG, ?_, hL.differentiableAt, ?_, hMu.differentiableAt, ?_, hK.differentiableAt, ?_⟩
  · simpa only [learningRate, effectiveEffort_zero] using hform
  · rw [hL.deriv]
    simp only [learningRate, effectiveEffort_zero]
    rw [gain_l_slope_identity p.lambda0 p.kappa p.mu (effectiveEffort p a) p.b
      (ne_of_gt hD1) (ne_of_gt hD00)]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos (mul_pos (mul_pos (mul_pos p.mu_pos p.kappa_pos) hΔ)
        (add_pos hD1 hD00))) hM
  · simp only [hMu.deriv, learningRate, effectiveEffort_zero]
    simp only [gain_m_slope_identity p.lambda0 p.kappa p.mu (effectiveEffort p a) p.b
      (ne_of_gt hD1) (ne_of_gt hD00)]
    exact positive_factor_sign _ _ _ (mul_pos p.kappa_pos hΔ) hM
  · simp only [hK.deriv, learningRate, effectiveEffort_zero]
    simp only [gain_k_slope_identity p.lambda0 p.kappa p.mu (effectiveEffort p a) p.b
      (ne_of_gt hD1) (ne_of_gt hD00)]
    exact positive_factor_sign _ _ _ (mul_pos p.mu_pos hΔ) hM

end
end Grados26Learning
