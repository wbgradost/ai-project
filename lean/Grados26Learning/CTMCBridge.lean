module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Two-state Markov semigroup support

Selected definitions and proofs from AppliedModelingLib's
`AppliedModelingLib/Foundations/Probability/CTMC.lean` at commit
`194edcc95df74806a39b961d10dedddc6e730cce`.
Source: <https://github.com/nikhgarg/AppliedModelingLib>.
SPDX-License-Identifier: Apache-2.0. See `CTMCBridge.LICENSE`.

This adaptation keeps the proofs used by Lemma 2 and changes their
namespace and imports so the paper can use Lean's module system.
-/

namespace Grados26Learning.CTMCBridge

open scoped Topology
open Filter

/--
Closed-form probability that a two-state CTMC currently in state `i` is in the
opposite state `j` after elapsed time `t`.

The rates are `lambdaIJ` for transitions from `i` to `j` and `lambdaJI` for
transitions from `j` back to `i`.
-/
noncomputable def twoStateCtmcSwitchProb (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  lambdaIJ / (lambdaIJ + lambdaJI) *
    (1 - Real.exp (-(lambdaIJ + lambdaJI) * t))

@[simp] theorem twoStateCtmcSwitchProb_zero
    (lambdaIJ lambdaJI : ℝ) :
    twoStateCtmcSwitchProb lambdaIJ lambdaJI 0 = 0 := by
  simp [twoStateCtmcSwitchProb]

/-- Closed-form probability of remaining in the starting state after elapsed time `t`. -/
noncomputable def twoStateCtmcStayProb (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  1 - twoStateCtmcSwitchProb lambdaIJ lambdaJI t

@[simp] theorem twoStateCtmcStayProb_zero
    (lambdaIJ lambdaJI : ℝ) :
    twoStateCtmcStayProb lambdaIJ lambdaJI 0 = 1 := by
  simp [twoStateCtmcStayProb]

/-- The two outgoing probabilities from a starting state sum to one. -/
theorem twoStateCtmcStayProb_add_switchProb
    (lambdaIJ lambdaJI t : ℝ) :
    twoStateCtmcStayProb lambdaIJ lambdaJI t +
        twoStateCtmcSwitchProb lambdaIJ lambdaJI t = 1 := by
  unfold twoStateCtmcStayProb
  ring

/--
Two-state CTMC transition probabilities on states `0` and `1`, with transition
rate `lambda01` from state `0` to state `1` and `lambda10` from state `1` to
state `0`.
-/
noncomputable def twoStateCtmcTransitionProb
    (lambda01 lambda10 t : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then
    if i = 0 then
      twoStateCtmcStayProb lambda01 lambda10 t
    else
      twoStateCtmcStayProb lambda10 lambda01 t
  else
    if i = 0 then
      twoStateCtmcSwitchProb lambda01 lambda10 t
    else
      twoStateCtmcSwitchProb lambda10 lambda01 t

@[simp] theorem twoStateCtmcTransitionProb_zero_zero
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 0 0 =
      twoStateCtmcStayProb lambda01 lambda10 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_zero_one
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 0 1 =
      twoStateCtmcSwitchProb lambda01 lambda10 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_one_zero
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 1 0 =
      twoStateCtmcSwitchProb lambda10 lambda01 t := by
  simp [twoStateCtmcTransitionProb]

@[simp] theorem twoStateCtmcTransitionProb_one_one
    (lambda01 lambda10 t : ℝ) :
    twoStateCtmcTransitionProb lambda01 lambda10 t 1 1 =
      twoStateCtmcStayProb lambda10 lambda01 t := by
  simp [twoStateCtmcTransitionProb]

/-- At elapsed time zero, the two-state transition kernel is the identity. -/
theorem twoStateCtmcTransitionProb_zero_time
    (lambda01 lambda10 : ℝ) (i j : Fin 2) :
    twoStateCtmcTransitionProb lambda01 lambda10 0 i j =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp

/-- Each row of the two-state transition kernel sums to one. -/
theorem twoStateCtmcTransitionProb_row_sum
    (lambda01 lambda10 t : ℝ) (i : Fin 2) :
    twoStateCtmcTransitionProb lambda01 lambda10 t i 0 +
        twoStateCtmcTransitionProb lambda01 lambda10 t i 1 = 1 := by
  fin_cases i
  · exact twoStateCtmcStayProb_add_switchProb lambda01 lambda10 t
  · simpa [add_comm] using
      twoStateCtmcStayProb_add_switchProb lambda10 lambda01 t

/-- Derivative of the two-state CTMC switch-probability closed form. -/
theorem twoStateCtmcSwitchProb_hasDerivAt
    (lambdaIJ lambdaJI t : ℝ) :
    HasDerivAt (fun s => twoStateCtmcSwitchProb lambdaIJ lambdaJI s)
      (lambdaIJ / (lambdaIJ + lambdaJI) *
        ((lambdaIJ + lambdaJI) *
          Real.exp (-(lambdaIJ + lambdaJI) * t))) t := by
  unfold twoStateCtmcSwitchProb
  have hlin :
      HasDerivAt (fun s : ℝ => -(lambdaIJ + lambdaJI) * s)
        (-(lambdaIJ + lambdaJI)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(lambdaIJ + lambdaJI)))
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (-(lambdaIJ + lambdaJI) * s))
        (Real.exp (-(lambdaIJ + lambdaJI) * t) *
          (-(lambdaIJ + lambdaJI))) t := by
    exact hlin.exp
  have hsub :
      HasDerivAt (fun s : ℝ => 1 - Real.exp (-(lambdaIJ + lambdaJI) * s))
        ((lambdaIJ + lambdaJI) *
          Real.exp (-(lambdaIJ + lambdaJI) * t)) t := by
    convert (hexp.const_sub 1) using 1
    ring
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hsub.const_mul (lambdaIJ / (lambdaIJ + lambdaJI))

/-- A homogeneous scalar ODE with a zero initial value has the zero solution
on the nonnegative half-line when its derivative is available from the right
at the boundary.  This is the half-line Grönwall form needed for literal
clock paths, whose extension to negative calendar times need not be
two-sided differentiable at zero. -/
theorem eq_zero_of_continuousOn_Ici_of_hasDerivWithinAt_linear
    (c : ℝ) (f : ℝ → ℝ) (hzero : f 0 = 0)
    (hcontinuous : ContinuousOn f (Set.Ici 0))
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (c * f t) (Set.Ici t) t) :
    ∀ ⦃t : ℝ⦄, 0 ≤ t → f t = 0 := by
  intro t ht
  have hzeroOn := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := f) (f' := fun x => c * f x) (K := ‖c‖)
    (a := (0 : ℝ)) (b := t)
    (hcontinuous.mono Set.Icc_subset_Ici_self)
    (fun x hx => hderiv x hx.1)
    hzero
    (fun x _ => by rw [norm_mul])
  exact hzeroOn t ⟨ht, le_rfl⟩

/-- The two-state switch-probability closed form is nonnegative in the usual parameter range. -/
theorem twoStateCtmcSwitchProb_nonneg
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    0 ≤ twoStateCtmcSwitchProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcSwitchProb
  apply mul_nonneg
  · exact div_nonneg hlambdaIJ (le_of_lt hsum)
  · have harg : -(lambdaIJ + lambdaJI) * t ≤ 0 := by nlinarith
    have hexp : Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
      have := (Real.exp_le_exp).2 harg
      simpa using this
    linarith

/-- The two-state switch-probability closed form is at most one in the usual parameter range. -/
theorem twoStateCtmcSwitchProb_le_one
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ) (hlambdaJI : 0 ≤ lambdaJI)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    twoStateCtmcSwitchProb lambdaIJ lambdaJI t ≤ 1 := by
  unfold twoStateCtmcSwitchProb
  have hfactor_le_one : lambdaIJ / (lambdaIJ + lambdaJI) ≤ 1 := by
    rw [div_le_one hsum]
    linarith
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-(lambdaIJ + lambdaJI) * t) := by
    have harg : -(lambdaIJ + lambdaJI) * t ≤ 0 := by nlinarith
    have hexp : Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
      have := (Real.exp_le_exp).2 harg
      simpa using this
    linarith
  have hterm_le_one : 1 - Real.exp (-(lambdaIJ + lambdaJI) * t) ≤ 1 := by
    have hnonneg := Real.exp_nonneg (-(lambdaIJ + lambdaJI) * t)
    linarith
  have hmul :
      lambdaIJ / (lambdaIJ + lambdaJI) *
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * t)) ≤ 1 * 1 := by
    exact mul_le_mul hfactor_le_one hterm_le_one hterm_nonneg zero_le_one
  simpa using hmul

/-- The paired stay probability is nonnegative in the usual parameter range. -/
theorem twoStateCtmcStayProb_nonneg
    (lambdaIJ lambdaJI t : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ) (hlambdaJI : 0 ≤ lambdaJI)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (ht : 0 ≤ t) :
    0 ≤ twoStateCtmcStayProb lambdaIJ lambdaJI t := by
  unfold twoStateCtmcStayProb
  have hswitch_le_one :=
    twoStateCtmcSwitchProb_le_one lambdaIJ lambdaJI t
      hlambdaIJ hlambdaJI hsum ht
  linarith

end Grados26Learning.CTMCBridge
