import Mathlib.Data.Real.Basic

/-!
# Grados (2026): primitives and the two-state learning extension

Source: the author's unpublished manuscript pinned at ai-project commit
7cc3a7406e09ba1544ff6997d5d742430c6c771c, Assumption 2 and Definition 1.
Parameters is the reduced view of the source primitives, with b>0.
The worker-to-b bridge is supplied separately from the actual optimizer.
-/
namespace Grados26Learning

noncomputable section

/-- The positive primitives of Assumption 2, after setting b=x*-s_L. -/
structure Parameters where
  b : ℝ
  lambda0 : ℝ
  kappa : ℝ
  mu : ℝ
  eta : ℝ
  b_pos : 0 < b
  lambda0_pos : 0 < lambda0
  kappa_pos : 0 < kappa
  mu_pos : 0 < mu
  eta_nonneg : 0 ≤ eta

/-- Low-state human effort as a function of fixed assistance. -/
def effort (p : Parameters) (a : ℝ) : ℝ := max (p.b - a) 0

/-- Definition 1: learning-effective human effort. -/
def effectiveEffort (p : Parameters) (a : ℝ) : ℝ :=
  effort p a * (1 + p.eta * a)

/-- Upward intensity; the downward intensity is p.mu. -/
def learningRate (p : Parameters) (a : ℝ) : ℝ :=
  p.lambda0 + p.kappa * effectiveEffort p a

/-- The rational stationary candidate, identified with the invariant law in Lemma 2. -/
def stationaryShare (p : Parameters) (a : ℝ) : ℝ :=
  learningRate p a / (learningRate p a + p.mu)

/-- Analytic active-effort branch, including its endpoint a=b. -/
def activeRate (p : Parameters) (a : ℝ) : ℝ :=
  p.lambda0 + p.kappa * ((p.b - a) * (1 + p.eta * a))

def activeShare (p : Parameters) (a : ℝ) : ℝ :=
  activeRate p a / (activeRate p a + p.mu)

/-- Positive economic peak only under eta*b>1. -/
def peak (p : Parameters) : ℝ := (p.b - 1 / p.eta) / 2

/-- Positive no-AI return only under eta*b>1. -/
def returnPoint (p : Parameters) : ℝ := p.b - 1 / p.eta

/-- The numerator determining the active marginal sign. -/
def marginalNumerator (p : Parameters) (a : ℝ) : ℝ :=
  p.eta * (p.b - 2 * a) - 1

/-- A literal two-atom skill law. -/
def skillCDF (q sL sH x : ℝ) : ℝ :=
  if x < sL then 0 else if x < sH then 1 - q else 1

/-- First-order stochastic dominance, in the CDF convention. -/
def skillFOSD (qHigh qLow sL sH : ℝ) : Prop :=
  ∀ x : ℝ, skillCDF qHigh sL sH x ≤ skillCDF qLow sL sH x

/-- Mean skill of the same two-atom law. -/
def meanSkill (q sL sH : ℝ) : ℝ := (1 - q) * sL + q * sH

/-- The unbundled formula is used to state genuine partial derivatives. -/
def rawShare (b lambda0 kappa mu eta a : ℝ) : ℝ :=
  (lambda0 + kappa * (max (b - a) 0 * (1 + eta * a))) /
    (lambda0 + kappa * (max (b - a) 0 * (1 + eta * a)) + mu)

end

end Grados26Learning
