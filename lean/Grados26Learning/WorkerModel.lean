module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Source worker primitives and greatest-maximizer definitions

The primitives are Assumption 1 of the commit-pinned manuscript. Optimization
is over the nonnegative half-line; weak concavity and the original greatest
maximizer rule are retained. Neither optimizer existence nor its claimed
closed form is included as a model field.
-/

open Set Filter

noncomputable section

namespace Grados26Learning

/-- The worker primitives in Assumption 1; all regularity is restricted to
the source domain of nonnegative total inputs. -/
structure WorkerModel where
  p : ℝ → ℝ
  gamma : ℝ
  gamma_pos : 0 < gamma
  p_contDiff : ContDiffOn ℝ 1 p (Ici 0)
  p_mono : MonotoneOn p (Ici 0)
  p_concave : ConcaveOn ℝ (Ici 0) p
  growth : Filter.limsup (fun x : ℝ => p x / x) atTop < gamma

/-- Utility as a function of unrestricted nonnegative total input. -/
def inputObjective (W : WorkerModel) (x : ℝ) : ℝ :=
  W.p x - W.gamma * x

/-- The complete optimizer set for total input, including feasibility. -/
def inputMaximizers (W : WorkerModel) : Set ℝ :=
  {x | 0 ≤ x ∧ IsMaxOn (inputObjective W) (Ici 0) x}

/-- The greatest optimizer of total-input utility, as selected in the paper. -/
noncomputable def referenceInput (W : WorkerModel) : ℝ :=
  sSup (inputMaximizers W)

/-- The original myopic objective; learning does not enter the decision. -/
def workerUtility (W : WorkerModel) (s a e : ℝ) : ℝ :=
  W.p (s + e + a) - W.gamma * e

/-- All feasible effort maximizers before applying the tie convention. -/
def effortMaximizers (W : WorkerModel) (s a : ℝ) : Set ℝ :=
  {e | 0 ≤ e ∧ IsMaxOn (workerUtility W s a) (Ici 0) e}

/-- The actual greatest-effort choice, defined through the optimizer set. -/
noncomputable def selectedEffort (W : WorkerModel) (s a : ℝ) : ℝ :=
  sSup (effortMaximizers W s a)

end Grados26Learning

end
