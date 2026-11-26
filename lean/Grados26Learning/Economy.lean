module

public import Grados26Learning.Model
public import Grados26Learning.WorkerModel

@[expose] public section

namespace Grados26Learning
noncomputable section

/-- Assumption 2 with b defined from the actual worker's optimizer. -/
structure Economy where
  worker : WorkerModel
  sL : ℝ
  sH : ℝ
  sL_nonneg : 0 ≤ sL
  skill_order : sL < sH
  lambda0 : ℝ
  kappa : ℝ
  mu : ℝ
  eta : ℝ
  lambda0_pos : 0 < lambda0
  kappa_pos : 0 < kappa
  mu_pos : 0 < mu
  eta_nonneg : 0 ≤ eta
  b_pos : 0 < referenceInput worker - sL

def Economy.parameters (E : Economy) : Parameters where
  b := referenceInput E.worker - E.sL
  lambda0 := E.lambda0
  kappa := E.kappa
  mu := E.mu
  eta := E.eta
  b_pos := E.b_pos
  lambda0_pos := E.lambda0_pos
  kappa_pos := E.kappa_pos
  mu_pos := E.mu_pos
  eta_nonneg := E.eta_nonneg

/-- The learning technology evaluated at the selected myopic effort. -/
def workerLearningRate (E : Economy) (a : ℝ) : ℝ :=
  E.lambda0 + E.kappa * selectedEffort E.worker E.sL a * (1 + E.eta*a)

end
end Grados26Learning
