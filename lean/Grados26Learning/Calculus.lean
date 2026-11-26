module

public import Grados26Learning.Algebra
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Grados26Learning

open Set Filter
open scoped Topology

noncomputable section

theorem continuous_learningRate (p : Parameters) : Continuous (learningRate p) := by
  unfold learningRate effectiveEffort effort
  fun_prop

theorem continuousOn_stationaryShare (p : Parameters) :
    ContinuousOn (stationaryShare p) (Ici 0) := by
  intro a ha
  exact (continuous_learningRate p).continuousWithinAt.div
    ((continuous_learningRate p).add continuous_const).continuousWithinAt
    (ne_of_gt (denominator_pos p ha))

theorem hasDerivAt_activeRate (p : Parameters) (a : ℝ) :
    HasDerivAt (activeRate p) (p.kappa * marginalNumerator p a) a := by
  have hprod := (HasDerivAt.sub (hasDerivAt_const a p.b) (hasDerivAt_id a)).mul
    (HasDerivAt.add (hasDerivAt_const a 1) ((hasDerivAt_id a).const_mul p.eta))
  have hd := HasDerivAt.add (hasDerivAt_const a p.lambda0) (hprod.const_mul p.kappa)
  convert hd using 1 <;> simp only [marginalNumerator, Pi.sub_apply, Pi.add_apply, id_eq] <;> ring

def activeSlope (p : Parameters) (a : ℝ) : ℝ :=
  p.mu * p.kappa * marginalNumerator p a / (activeRate p a + p.mu) ^ 2

theorem hasDerivAt_activeShare (p : Parameters) {a : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ p.b) :
    HasDerivAt (activeShare p) (activeSlope p a) a := by
  have hden : activeRate p a + p.mu ≠ 0 := by
    rw [← learningRate_active p hab]
    exact ne_of_gt (denominator_pos p ha)
  have hr := hasDerivAt_activeRate p a
  have hd := hr.div (HasDerivAt.add hr (hasDerivAt_const a p.mu)) hden
  convert hd using 1
  simp only [activeSlope, Pi.add_apply, add_zero]
  field_simp [hden]
  ring

theorem hasDerivAt_stationaryShare (p : Parameters) {a : ℝ}
    (ha : 0 ≤ a) (hab : a < p.b) :
    HasDerivAt (stationaryShare p)
      (p.mu * p.kappa * marginalNumerator p a / (learningRate p a + p.mu)^2) a := by
  have heq : stationaryShare p =ᶠ[𝓝 a] activeShare p := by
    filter_upwards [Iio_mem_nhds hab] with x hx
    exact share_active p (le_of_lt hx)
  have hd := (hasDerivAt_activeShare p ha hab.le).congr_of_eventuallyEq heq
  simpa only [activeSlope, ← learningRate_active p hab.le] using hd

theorem right_derivative_zero (p : Parameters) :
    HasDerivWithinAt (stationaryShare p)
      (p.mu * p.kappa * (p.eta*p.b-1) / (learningRate p 0 + p.mu)^2) (Ici 0) 0 := by
  simpa [marginalNumerator] using
    (hasDerivAt_stationaryShare p (a := 0) le_rfl p.b_pos).hasDerivWithinAt (s := Ici 0)

theorem critical_right_derivative_zero (p : Parameters) (h : p.eta*p.b = 1) :
    HasDerivWithinAt (stationaryShare p) 0 (Ici 0) 0 := by
  simpa [h] using right_derivative_zero p

theorem left_derivative_cutoff (p : Parameters) :
    HasDerivWithinAt (stationaryShare p)
      (-p.mu*p.kappa*(1+p.eta*p.b)/(p.lambda0+p.mu)^2) (Iic p.b) p.b := by
  have hd := (hasDerivAt_activeShare p p.b_pos.le le_rfl).hasDerivWithinAt (s := Iic p.b)
  have heq : ∀ x ∈ Iic p.b, stationaryShare p x = activeShare p x :=
    fun x hx => share_active p hx
  have ht := hd.congr_of_mem heq (Set.mem_Iic.mpr le_rfl)
  convert ht using 1
  unfold activeSlope marginalNumerator
  rw [← learningRate_active p (a := p.b) le_rfl, learningRate_saturated p le_rfl]
  ring

theorem right_derivative_cutoff (p : Parameters) :
    HasDerivWithinAt (stationaryShare p) 0 (Ici p.b) p.b := by
  exact (hasDerivWithinAt_const p.b (Ici p.b) (p.lambda0/(p.lambda0+p.mu))).congr_of_mem
    (fun x hx => share_saturated p hx) (Set.mem_Ici.mpr le_rfl)

def activeCurvature (p : Parameters) (a : ℝ) : ℝ :=
  -2*p.mu*p.kappa*
    (p.eta*(activeRate p a+p.mu)+p.kappa*(marginalNumerator p a)^2) /
      (activeRate p a+p.mu)^3

theorem hasDerivAt_activeSlope (p : Parameters) {a : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ p.b) :
    HasDerivAt (activeSlope p) (activeCurvature p a) a := by
  have hden : activeRate p a + p.mu ≠ 0 := by
    rw [← learningRate_active p hab]
    exact ne_of_gt (denominator_pos p ha)
  have hn : HasDerivAt (marginalNumerator p) (-2*p.eta) a := by
    have hlinear := HasDerivAt.sub (hasDerivAt_const a p.b) ((hasDerivAt_id a).const_mul 2)
    have hd := HasDerivAt.sub (hlinear.const_mul p.eta) (hasDerivAt_const a 1)
    convert hd using 1 <;> try simp only [marginalNumerator, Pi.sub_apply, id_eq]
    all_goals ring
  have hr := HasDerivAt.add (hasDerivAt_activeRate p a) (hasDerivAt_const a p.mu)
  have hd := (hn.const_mul (p.mu*p.kappa)).div (hr.pow 2) (pow_ne_zero 2 hden)
  convert hd using 1
  simp only [activeCurvature, Pi.pow_apply, Pi.add_apply, add_zero]
  norm_num
  field_simp [hden]
  ring

theorem second_derivative_formula (p : Parameters) {a : ℝ}
    (ha : 0 < a) (hab : a < p.b) :
    deriv (deriv (stationaryShare p)) a = activeCurvature p a := by
  have heq : deriv (stationaryShare p) =ᶠ[𝓝 a] activeSlope p := by
    filter_upwards [Ioo_mem_nhds ha hab] with x hx
    rw [(hasDerivAt_stationaryShare p hx.1.le hx.2).deriv]
    simp only [activeSlope, ← learningRate_active p hx.2.le]
  exact ((hasDerivAt_activeSlope p ha.le hab.le).congr_of_eventuallyEq heq).deriv

theorem activeCurvature_neg (p : Parameters) {a : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ p.b) : activeCurvature p a < 0 := by
  have hD : 0 < activeRate p a + p.mu := by
    rw [← learningRate_active p hab]
    exact denominator_pos p ha
  have hinner :
      0 < p.eta*(activeRate p a+p.mu)+p.kappa*(marginalNumerator p a)^2 := by
    by_cases hz : p.eta = 0
    · simpa [marginalNumerator, hz] using p.kappa_pos
    · have hη : 0 < p.eta := lt_of_le_of_ne p.eta_nonneg (Ne.symm hz)
      exact add_pos_of_pos_of_nonneg (mul_pos hη hD)
        (mul_nonneg p.kappa_pos.le (sq_nonneg _))
  unfold activeCurvature
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num : (-2 : ℝ) < 0) p.mu_pos) p.kappa_pos)
      hinner)
    (pow_pos hD 3)

theorem second_derivative_neg (p : Parameters) {a : ℝ}
    (ha : 0 < a) (hab : a < p.b) :
    deriv (deriv (stationaryShare p)) a < 0 := by
  rw [second_derivative_formula p ha hab]
  exact activeCurvature_neg p ha.le hab.le

end
end Grados26Learning
