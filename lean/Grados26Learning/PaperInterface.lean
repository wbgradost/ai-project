module

public import Grados26Learning.DeterministicInterface
public import Grados26Learning.CTMCModel

@[expose] public section

/-! Canonical source statements for the five numbered results. The deterministic
statements live in DeterministicInterface so their proofs can build without
loading the stochastic-process environment. -/
namespace Grados26Learning

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
universe u

/-- Lemma 2: an actual transition semigroup and given stochastic process. -/
def lemma2Spec : Prop :=
  ∀ E : Economy, ∀ a : ℝ, 0 ≤ a →
    0 < workerLearningRate E a ∧ 0 < E.mu ∧
    Nonempty (TwoStateSemigroup (workerLearningRate E a) E.mu) ∧
    ∀ S : TwoStateSemigroup (workerLearningRate E a) E.mu,
      (∀ low high : ℝ, (low + high = 1 ∧ IsStationaryHigh S high) ↔
        low = E.mu / (learningRate E.parameters a + E.mu) ∧
          high = stationaryShare E.parameters a) ∧
      (∀ low high : ℝ, low + high = 1 →
        (IsStationaryHigh S high ↔ low * workerLearningRate E a = high * E.mu)) ∧
      (∀ h0 ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
        semigroupHigh S h0 t =
          stationaryShare E.parameters a +
            (h0 - stationaryShare E.parameters a) *
              Real.exp (-(learningRate E.parameters a + E.mu)*t)) ∧
      (∀ t : ℝ, 0 ≤ t →
        let high := stationaryShare E.parameters a
        let low := E.mu / (learningRate E.parameters a + E.mu)
        let decay := Real.exp (-(learningRate E.parameters a + E.mu) * t)
        S.transition t 0 0 = low + high * decay ∧ S.transition t 0 1 = high * (1 - decay) ∧
          S.transition t 1 0 = low * (1 - decay) ∧ S.transition t 1 1 = high + low * decay) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (X : TwoStateProcess S Ω ν),
        processHigh X 0 ∈ Icc (0 : ℝ) 1 ∧
        (∀ t : NNReal, processHigh X t =
          stationaryShare E.parameters a +
            (processHigh X 0 - stationaryShare E.parameters a) *
              Real.exp (-(learningRate E.parameters a + E.mu)*(t : ℝ))) ∧
        (∀ T : ℝ, 0 < T →
          (∫ ω, occupation X T ω ∂ν) =
            stationaryShare E.parameters a +
              (processHigh X 0 - stationaryShare E.parameters a) *
                (1 - Real.exp (-(learningRate E.parameters a + E.mu)*T)) /
                  ((learningRate E.parameters a + E.mu)*T)) ∧
        (processHigh X 0 = 0 → ∀ T : ℝ, 0 < T →
          stationaryShare E.parameters a - (∫ ω, occupation X T ω ∂ν) =
            stationaryShare E.parameters a *
              (1 - Real.exp (-(learningRate E.parameters a + E.mu)*T)) /
                ((learningRate E.parameters a + E.mu)*T) ∧
          (∫ ω, occupation X T ω ∂ν) < stationaryShare E.parameters a))

end

end Grados26Learning
