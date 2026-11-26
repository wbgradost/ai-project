module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Lemma 2: finite-state CTMC semantics and occupation

The model below is a continuous stochastic transition semigroup with its
infinitesimal generator, together with a measurable process satisfying the
finite-history homogeneous Markov law.  No forward equation, closed-form
transition probability, stationary distribution, or occupation identity is
assumed.  They are the conclusions of the subsequent theorems.

Times of the random process are nonnegative.  This avoids assumptions about
behavior outside the source time domain.  Joint measurability is the standard
well-formedness property of the finite-state CTMC in Assumption 2.
-/

namespace Grados26Learning

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

/-- Generator in the order (L,H). -/
def twoStateGenerator (up down : ℝ) (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then -up else up)
  else (if j = 0 then down else -down)

/-- Standard finite-state CTMC transition-semigroup data.  The generator is
specified only at zero; the forward equation at positive times is derived. -/
structure TwoStateSemigroup (up down : ℝ) where
  transition : ℝ → Fin 2 → Fin 2 → ℝ
  nonneg : ∀ t, 0 ≤ t → ∀ i j, 0 ≤ transition t i j
  row_sum : ∀ t, 0 ≤ t → ∀ i, transition t i 0 + transition t i 1 = 1
  zero : ∀ i j, transition 0 i j = if i = j then 1 else 0
  composition : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ i j,
    transition (s + t) i j =
      transition s i 0 * transition t 0 j +
      transition s i 1 * transition t 1 j
  continuous : ∀ i j, ContinuousOn (fun t => transition t i j) (Ici 0)
  generator : ∀ i j, HasDerivWithinAt (fun t => transition t i j)
    (twoStateGenerator up down i j) (Ici 0) 0

/-- A homogeneous Markov process governed by the given semigroup.  The
finite-history condition is the usual finite-dimensional Markov law; its
history can be empty. -/
structure TwoStateProcess {up down : ℝ} (S : TwoStateSemigroup up down)
    (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω) where
  state : NNReal → Ω → Fin 2
  measurable : Measurable (fun z : NNReal × Ω => state z.1 z.2)
  markov : ∀ (s t : NNReal) (i j : Fin 2) (history : List (NNReal × Fin 2)),
    (∀ entry ∈ history, entry.1 ≤ s) →
    ν.real {ω | (∀ entry ∈ history, state entry.1 ω = entry.2) ∧
      state s ω = i ∧ state (s + t) ω = j} =
    ν.real {ω | (∀ entry ∈ history, state entry.1 ω = entry.2) ∧
      state s ω = i} * S.transition t i j

def semigroupHigh {up down : ℝ} (S : TwoStateSemigroup up down)
    (initialHigh t : ℝ) : ℝ :=
  (1 - initialHigh) * S.transition t 0 1 +
    initialHigh * S.transition t 1 1

def transientHigh (up down initialHigh t : ℝ) : ℝ :=
  up / (up + down) +
    (initialHigh - up / (up + down)) * Real.exp (-(up + down) * t)

def IsStationaryHigh {up down : ℝ} (S : TwoStateSemigroup up down)
    (q : ℝ) : Prop :=
  q ∈ Icc (0 : ℝ) 1 ∧ ∀ t, 0 ≤ t → semigroupHigh S q t = q

def processHigh {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : TwoStateProcess S Ω ν) (t : NNReal) : ℝ :=
  ν.real {ω | X.state t ω = 1}

def occupation {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : TwoStateProcess S Ω ν) (T : ℝ) (ω : Ω) : ℝ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, if X.state t.toNNReal ω = 1 then (1 : ℝ) else 0

end
end Grados26Learning
