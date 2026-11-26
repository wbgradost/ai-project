module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace Grados26Learning

open MeasureTheory Set

noncomputable section

private theorem decay_hasDerivAt (q s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-q * t)) (-q * Real.exp (-q * s)) s := by
  have harg : HasDerivAt (fun t : ℝ => -q * t) (-q) s := by
    simpa using (hasDerivAt_id s).const_mul (-q)
  convert harg.exp using 1
  ring

private theorem reverse_decay_hasDerivAt (q T s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-q * (T - t))) (q * Real.exp (-q * (T - s))) s := by
  have harg : HasDerivAt (fun t : ℝ => -q * (T - t)) q s := by
    simpa using (((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul (-q))
  convert harg.exp using 1
  ring

/-- The first scalar integral in the occupation second moment. -/
theorem occupation_second_moment_integral₁ (q T : ℝ) (hq : q ≠ 0) :
    (∫ s in (0 : ℝ)..T, (1 - Real.exp (-q * s)) * (T - s)) =
      T ^ 2 / 2 - T / q + (1 - Real.exp (-q * T)) / q ^ 2 := by
  let F : ℝ → ℝ := fun s => T * s - s ^ 2 / 2 + ((T - s) / q - 1 / q ^ 2) * Real.exp (-q * s)
  have hF (s : ℝ) : HasDerivAt F ((1 - Real.exp (-q * s)) * (T - s)) s := by
    have hquad : HasDerivAt (fun y : ℝ => y ^ 2) (2 * s) s := by
      have hm := (hasDerivAt_id s).mul (hasDerivAt_id s)
      change HasDerivAt (fun y : ℝ => y * y) (1 * s + s * 1) s at hm
      convert hm using 1
      · funext y
        ring
      · ring
    have hpoly : HasDerivAt (fun y : ℝ => T * y - y ^ 2 / 2) (T - s) s := by
      convert ((hasDerivAt_id s).const_mul T).sub (hquad.div_const 2) using 1 <;> ring
    have hline : HasDerivAt (fun y : ℝ => (T - y) / q - 1 / q ^ 2) (-1 / q) s := by
      convert ((((hasDerivAt_const s T).sub (hasDerivAt_id s)).div_const q).sub_const
        (1 / q ^ 2)) using 1 <;> ring
    convert hpoly.add (hline.mul (decay_hasDerivAt q s)) using 1
    field_simp [hq]
    ring
  have hi : IntervalIntegrable (fun s : ℝ => (1 - Real.exp (-q * s)) * (T - s)) volume 0 T :=
    Continuous.intervalIntegrable
      (show Continuous (fun s : ℝ => (1 - Real.exp (-q * s)) * (T - s)) by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) hi]
  simp [F]
  ring

/-- The second scalar integral in the occupation second moment. -/
theorem occupation_second_moment_integral₂ (q T : ℝ) (hq : q ≠ 0) :
    (∫ s in (0 : ℝ)..T, (1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s)))) =
      T * (1 + Real.exp (-q * T)) - (2 * (1 - Real.exp (-q * T))) / q := by
  let F : ℝ → ℝ := fun s => (1 + Real.exp (-q * T)) * s + Real.exp (-q * s) / q -
    Real.exp (-q * (T - s)) / q
  have hF (s : ℝ) : HasDerivAt F
      ((1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s)))) s := by
    have hlin := (hasDerivAt_id s).const_mul (1 + Real.exp (-q * T))
    have h := (hlin.add ((decay_hasDerivAt q s).div_const q)).sub
      ((reverse_decay_hasDerivAt q T s).div_const q)
    have hexp : Real.exp (-q * s) * Real.exp (-q * (T - s)) = Real.exp (-q * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    convert h using 1
    rw [show (1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s))) =
        1 - Real.exp (-q * s) - Real.exp (-q * (T - s)) + Real.exp (-q * T) by
      rw [← hexp]
      ring]
    field_simp [hq]
    ring
  have hi : IntervalIntegrable
      (fun s : ℝ => (1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s)))) volume 0 T :=
    Continuous.intervalIntegrable (show Continuous
      (fun s : ℝ => (1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s)))) by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) hi]
  simp [F]
  ring

private theorem shifted_decay_integral (q s T : ℝ) (hq : q ≠ 0) :
    (∫ t in s..T, Real.exp (-q * (t - s))) = (1 - Real.exp (-q * (T - s))) / q := by
  let F : ℝ → ℝ := fun t => -Real.exp (-q * (t - s)) / q
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-q * (t - s))) t := by
    have hshift : HasDerivAt (fun x : ℝ => x - s) 1 t := (hasDerivAt_id t).sub_const s
    have hd := (((decay_hasDerivAt q (t - s)).comp t hshift).neg).div_const q
    convert hd using 1
    field_simp [hq]
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-q * (t - s))) volume s T :=
    Continuous.intervalIntegrable
      (show Continuous (fun t : ℝ => Real.exp (-q * (t - s))) by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hi]
  simp [F] <;> ring

/-- Integrate the low-start two-time kernel over the ordered time pairs. -/
theorem occupation_second_moment_kernel_integral (p q T : ℝ) (hq : q ≠ 0) :
    (∫ s in (0 : ℝ)..T, ∫ t in s..T,
      (p * (1 - Real.exp (-q * s))) * (p + (1 - p) * Real.exp (-q * (t - s)))) =
      p * (p * (T ^ 2 / 2 - T / q + (1 - Real.exp (-q * T)) / q ^ 2) +
        (1 - p) / q * (T * (1 + Real.exp (-q * T)) - (2 * (1 - Real.exp (-q * T))) / q)) := by
  have hinner (s : ℝ) :
      (∫ t in s..T, (p * (1 - Real.exp (-q * s))) *
        (p + (1 - p) * Real.exp (-q * (t - s)))) =
      (p * p) * ((1 - Real.exp (-q * s)) * (T - s)) +
        (p * ((1 - p) / q)) * ((1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s)))) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable
        (show Continuous (fun t : ℝ => (1 - p) * Real.exp (-q * (t - s))) by fun_prop) s T)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      shifted_decay_integral q s T hq]
    simp only [smul_eq_mul]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable
      (show Continuous (fun s : ℝ => (p * p) * ((1 - Real.exp (-q * s)) * (T - s))) by fun_prop) 0 T)
    (Continuous.intervalIntegrable
      (show Continuous (fun s : ℝ => (p * ((1 - p) / q)) *
        ((1 - Real.exp (-q * s)) * (1 - Real.exp (-q * (T - s))))) by fun_prop) 0 T)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    occupation_second_moment_integral₁ q T hq, occupation_second_moment_integral₂ q T hq]
  ring

end
end Grados26Learning
