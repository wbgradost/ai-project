module

public import Grados26Learning.CTMC
public import Grados26Learning.OccupationSecondMoment
public import Grados26Learning.OccupationMomentIntegrals

@[expose] public section

/-! # Appendix A.2: the evaluated occupation second moment -/

namespace Grados26Learning

open MeasureTheory Set

noncomputable section

/-- The joint high-state probability after starting in the low state. -/
theorem process_jointHigh_startLow_formula
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (hq : up + down ≠ 0)
    (hstart : processHigh X 0 = 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    let q := up + down
    let p := up / q
    ν.real {ω | X.state s.toNNReal ω = 1 ∧ X.state t.toNNReal ω = 1} =
      (p * (1 - Real.exp (-q * s))) * (p + (1 - p) * Real.exp (-q * (t - s))) := by
  have hnn : s.toNNReal ≤ t.toNNReal := Real.toNNReal_monotone hst
  have hshift : ((t.toNNReal - s.toNNReal : NNReal) : ℝ) = t - s := by
    rw [NNReal.coe_sub hnn, Real.coe_toNNReal t (hs.trans hst), Real.coe_toNNReal s hs]
  have hhigh := (transition_matrix_entries S hq
    (t.toNNReal - s.toNNReal : NNReal) (t.toNNReal - s.toNNReal).coe_nonneg).2.2.2
  have hlow : down / (up + down) = 1 - up / (up + down) := by
    field_simp [hq]
    ring
  dsimp only
  rw [process_jointHigh_eq X hnn, processHigh_eq_transient X hq, hstart, hhigh, hshift, hlow]
  simp only [transientHigh, Real.coe_toNNReal s hs]
  ring

/-- Equation (A.5), obtained by integrating the actual Markov two-time law. -/
theorem expected_occupation_sq_startLow_eq_formula
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (hup : 0 < up) (hdown : 0 < down)
    (hstart : processHigh X 0 = 0) (T : ℝ) (hT : 0 < T) :
    let q := up + down
    let p := up / q
    let d := 1 - Real.exp (-q * T)
    (∫ ω, (occupation X T ω) ^ 2 ∂ν) =
      (2 * p / T ^ 2) *
        (p * (T ^ 2 / 2 - T / q + d / q ^ 2) +
          (1 - p) / q * (T * (1 + Real.exp (-q * T)) - 2 * d / q)) := by
  let q := up + down
  let p := up / q
  have hq : q ≠ 0 := ne_of_gt (add_pos hup hdown)
  have htri : (∫ s in (0 : ℝ)..T, ∫ t in s..T,
      ν.real {ω | X.state s.toNNReal ω = 1 ∧ X.state t.toNNReal ω = 1}) =
      ∫ s in (0 : ℝ)..T, ∫ t in s..T,
        (p * (1 - Real.exp (-q * s))) * (p + (1 - p) * Real.exp (-q * (t - s))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T := uIcc_of_le hT.le ▸ hs
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc s T := uIcc_of_le hs'.2 ▸ ht
    exact process_jointHigh_startLow_formula X hq hstart hs'.1 ht'.1
  dsimp only
  rw [expected_occupation_sq_eq_twice_triangle X T hT, htri,
    occupation_second_moment_kernel_integral p q T hq]
  change (2 / T ^ 2) * (p * _) = (2 * p / T ^ 2) * _
  ring

end
end Grados26Learning
