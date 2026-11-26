module

public import Grados26Learning.DeterministicInterface
public import Grados26Learning.Worker

@[expose] public section

/-!
# Lemma 1 of the pinned manuscript

The optimizer and derivative proofs live in the worker modules. The bridge to
the two-state model substitutes actual selected effort into the learning rate.
-/

namespace Grados26Learning

open Set

/-- Evaluating learning at the myopic worker's actual selection yields the
effective-effort rate in Definition 1. -/
theorem workerLearningRate_eq (E : Economy) (a : ℝ) (ha : 0 ≤ a) :
    workerLearningRate E a = learningRate E.parameters a := by
  change E.lambda0 + E.kappa * selectedEffort E.worker E.sL a * (1 + E.eta * a) =
    E.lambda0 + E.kappa * (max (referenceInput E.worker - E.sL - a) 0 * (1 + E.eta * a))
  rw [selectedEffort_eq E.worker E.sL_nonneg ha]
  ring

/-- Lemma 1, with existence, greatest-maximizer selection and marginal
conditions derived from the worker primitives. -/
theorem lemma1 : lemma1Spec := by
  unfold lemma1Spec
  refine ⟨?_, ?_, ?_, workerLearningRate_eq⟩
  · intro W
    refine ⟨(inputMaximizers_compact_nonempty W).1, isGreatest_referenceInput W, ?_⟩
    intro s hs a ha
    refine ⟨selectedEffort_isGreatest W hs ha, selectedEffort_eq W hs ha,
      deriv_production_of_selectedEffort_pos W hs ha, ?_⟩
    intro hz
    have hcut : referenceInput W - s ≤ a := by linarith only [hz]
    exact ⟨selectedEffort_eq_zero_of_le W hs ha hcut, production_derivWithin_corner W hz⟩
  · intro E a ha
    constructor
    · intro hactive
      exact ⟨selectedEffort_eq_sub_of_lt E.worker E.sL_nonneg ha hactive,
        selectedEffort_pos_of_lt E.worker E.sL_nonneg ha hactive⟩
    · intro hcut
      exact selectedEffort_eq_zero_of_le E.worker E.sL_nonneg ha hcut
  · intro E a ha
    exact hasDerivAt_selectedEffort_of_lt E.worker E.sL_nonneg ha.1 ha.2

end Grados26Learning
