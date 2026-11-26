module

public import Grados26Learning.CTMCModel
public import Grados26Learning.CTMCBridge
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Grados26Learning

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

private theorem fin2_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- Differentiate the semigroup identity in its second time argument. -/
theorem semigroup_forward_right {up down : ℝ} (S : TwoStateSemigroup up down)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 2) :
    HasDerivWithinAt (fun u => S.transition u i 1)
      (up - (up + down) * S.transition t i 1) (Ici t) t := by
  have hshift : HasDerivWithinAt (fun u : ℝ => u - t) 1 (Ici t) t := by
    simpa using ((hasDerivAt_id t).sub_const t).hasDerivWithinAt (s := Ici t)
  have hmaps : MapsTo (fun u : ℝ => u - t) (Ici t) (Ici 0) := by
    intro u hu
    exact sub_nonneg.mpr (mem_Ici.mp hu)
  have h0 := (S.generator 0 1).comp_of_eq t hshift hmaps (by simp)
  have h1 := (S.generator 1 1).comp_of_eq t hshift hmaps (by simp)
  have hsum := (h0.const_mul (S.transition t i 0)).add
    (h1.const_mul (S.transition t i 1))
  simp only [mul_one] at hsum
  have hcongr :
      HasDerivWithinAt (fun u => S.transition u i 1)
        (S.transition t i 0 * twoStateGenerator up down 0 1 +
          S.transition t i 1 * twoStateGenerator up down 1 1) (Ici t) t := by
    apply hsum.congr_of_mem
    · intro u hu
      have htime : t + (u - t) = u := by ring
      simpa only [Function.comp_apply, htime] using
        S.composition t (u - t) ht (sub_nonneg.mpr (mem_Ici.mp hu)) i 1
    · exact mem_Ici.mpr (le_refl t)
  have hrow : S.transition t i 0 = 1 - S.transition t i 1 := by
    linarith [S.row_sum t ht i]
  convert hcongr using 1
  simp [twoStateGenerator, hrow]
  ring

theorem semigroupHigh_forward_right {up down : ℝ} (S : TwoStateSemigroup up down)
    (h0 t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (semigroupHigh S h0)
      (up - (up + down) * semigroupHigh S h0 t) (Ici t) t := by
  have hd := ((semigroup_forward_right S t ht 0).const_mul (1-h0)).add
    ((semigroup_forward_right S t ht 1).const_mul h0)
  convert hd using 1
  simp only [semigroupHigh]
  ring

theorem semigroupHigh_zero {up down : ℝ} (S : TwoStateSemigroup up down) (h0 : ℝ) :
    semigroupHigh S h0 0 = h0 := by
  simp [semigroupHigh, S.zero]

theorem transientHigh_hasDerivAt (up down h0 t : ℝ) (hr : up + down ≠ 0) :
    HasDerivAt (transientHigh up down h0)
      (up - (up + down) * transientHigh up down h0 t) t := by
  have hd := (((hasDerivAt_id t).const_mul (-(up + down))).exp.const_mul
    (h0 - up / (up + down))).const_add (up / (up + down))
  simp only [id_eq, mul_one] at hd
  convert hd using 1
  unfold transientHigh
  field_simp [hr]
  ring

/-- A common clock-rate multiplier is equivalent to rescaling elapsed
time in the transient state probability. -/
theorem transientHigh_scale_rates (up down h0 t c : ℝ)
    (hc : c ≠ 0) (hr : up + down ≠ 0) :
    transientHigh (c * up) (c * down) h0 t = transientHigh up down h0 (c * t) := by
  have hshare : c * up / (c * (up + down)) = up / (up + down) := by
    field_simp [hc, hr]
  unfold transientHigh
  rw [show c * up + c * down = c * (up + down) by ring, hshare,
    show -(c * (up + down)) * t = -(up + down) * (c * t) by ring]

/-- The generator and semigroup, rather than a guessed ODE hypothesis,
determine the transient law. -/
theorem semigroupHigh_eq_transient {up down : ℝ} (S : TwoStateSemigroup up down)
    (hr : up + down ≠ 0) (h0 : ℝ) :
    ∀ t, 0 ≤ t → semigroupHigh S h0 t = transientHigh up down h0 t := by
  let d : ℝ → ℝ := fun t => semigroupHigh S h0 t - transientHigh up down h0 t
  have hzero : d 0 = 0 := by simp [d, semigroupHigh_zero, transientHigh]
  have hc : ContinuousOn d (Ici 0) := by
    apply ContinuousOn.sub
    · exact ((S.continuous 0 1).const_mul (1-h0)).add
        ((S.continuous 1 1).const_mul h0)
    · exact (by
        unfold transientHigh
        fun_prop : Continuous (transientHigh up down h0)).continuousOn
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt d (-(up + down) * d t) (Ici t) t := by
    intro t ht
    have hdiff := (semigroupHigh_forward_right S h0 t ht).sub
      (transientHigh_hasDerivAt up down h0 t hr).hasDerivWithinAt
    convert hdiff using 1
    dsimp [d]
    ring
  intro t ht
  exact sub_eq_zero.mp
    (CTMCBridge.eq_zero_of_continuousOn_Ici_of_hasDerivWithinAt_linear
      (-(up + down)) d hzero hc hd ht)

/-- The ordinary forward equation on the positive-time interior of the
semigroup domain. The boundary at zero uses the right derivative. -/
theorem semigroupHigh_forward {up down : ℝ} (S : TwoStateSemigroup up down)
    (hr : up + down ≠ 0) (h0 t : ℝ) (ht : 0 < t) :
    HasDerivAt (semigroupHigh S h0)
      (up - (up + down) * semigroupHigh S h0 t) t := by
  rw [semigroupHigh_eq_transient S hr h0 t ht.le]
  apply (transientHigh_hasDerivAt up down h0 t hr).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact semigroupHigh_eq_transient S hr h0 s (le_of_lt hs)

/-- All four entries of the transition matrix in Appendix A.2, derived
for any semigroup with the prescribed generator. -/
theorem transition_matrix_entries {up down : ℝ} (S : TwoStateSemigroup up down)
    (hr : up + down ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    let high := up / (up + down)
    let low := down / (up + down)
    let decay := Real.exp (-(up + down) * t)
    S.transition t 0 0 = low + high * decay ∧
    S.transition t 0 1 = high * (1 - decay) ∧
    S.transition t 1 0 = low * (1 - decay) ∧
    S.transition t 1 1 = high + low * decay := by
  dsimp only
  have hH := semigroupHigh_eq_transient S hr 1 t ht
  have hL := semigroupHigh_eq_transient S hr 0 t ht
  simp only [semigroupHigh, sub_self, zero_mul, one_mul, zero_add] at hH
  simp only [semigroupHigh, sub_zero, one_mul, zero_mul, add_zero] at hL
  have hnorm : down / (up + down) = 1 - up / (up + down) := by
    field_simp [hr]
    ring
  rw [hnorm]
  unfold transientHigh at hH hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show S.transition t 0 0 = 1 - S.transition t 0 1 by
          linarith [S.row_sum t ht 0], hL]
    ring
  · rw [hL]
    ring
  · rw [show S.transition t 1 0 = 1 - S.transition t 1 1 by
          linarith [S.row_sum t ht 1], hH]
    ring
  · exact hH

/-- The explicit transition kernel is a genuine stochastic semigroup with
the prescribed infinitesimal generator, not only a solution of an ODE. -/
def canonicalSemigroup (up down : ℝ) (hup : 0 < up) (hdown : 0 < down) :
    TwoStateSemigroup up down where
  transition := CTMCBridge.twoStateCtmcTransitionProb up down
  nonneg := by
    intro t ht i j
    fin_cases i <;> fin_cases j <;>
      simp only [CTMCBridge.twoStateCtmcTransitionProb, ↓reduceIte]
    · exact CTMCBridge.twoStateCtmcStayProb_nonneg up down t
        hup.le hdown.le (add_pos hup hdown) ht
    · exact CTMCBridge.twoStateCtmcSwitchProb_nonneg up down t
        hup.le (add_pos hup hdown) ht
    · exact CTMCBridge.twoStateCtmcSwitchProb_nonneg down up t
        hdown.le (add_pos hdown hup) ht
    · exact CTMCBridge.twoStateCtmcStayProb_nonneg down up t
        hdown.le hup.le (add_pos hdown hup) ht
  row_sum := by
    intro t _ i
    exact CTMCBridge.twoStateCtmcTransitionProb_row_sum up down t i
  zero := CTMCBridge.twoStateCtmcTransitionProb_zero_time up down
  composition := by
    intro s t _ _ i j
    have hr : up + down ≠ 0 := ne_of_gt (add_pos hup hdown)
    have he : Real.exp (-(up + down) * (s+t)) =
        Real.exp (-(up + down) * s) * Real.exp (-(up + down) * t) := by
      rw [mul_add, Real.exp_add]
    obtain rfl | rfl := fin2_zero_or_one i <;>
      obtain rfl | rfl := fin2_zero_or_one j <;>
      simp only [CTMCBridge.twoStateCtmcTransitionProb_zero_zero,
        CTMCBridge.twoStateCtmcTransitionProb_zero_one,
        CTMCBridge.twoStateCtmcTransitionProb_one_zero,
        CTMCBridge.twoStateCtmcTransitionProb_one_one,
        CTMCBridge.twoStateCtmcStayProb, CTMCBridge.twoStateCtmcSwitchProb] <;>
      simp only [add_comm down up] <;> rw [he] <;>
      field_simp [hr] <;> ring
  continuous := by
    intro i j
    obtain rfl | rfl := fin2_zero_or_one i <;>
      obtain rfl | rfl := fin2_zero_or_one j <;>
      simp only [CTMCBridge.twoStateCtmcTransitionProb_zero_zero,
        CTMCBridge.twoStateCtmcTransitionProb_zero_one,
        CTMCBridge.twoStateCtmcTransitionProb_one_zero,
        CTMCBridge.twoStateCtmcTransitionProb_one_one,
        CTMCBridge.twoStateCtmcStayProb, CTMCBridge.twoStateCtmcSwitchProb] <;>
      fun_prop
  generator := by
    intro i j
    have hr : up + down ≠ 0 := ne_of_gt (add_pos hup hdown)
    have hrd : down + up ≠ 0 := ne_of_gt (add_pos hdown hup)
    have hu : HasDerivAt
        (fun t => CTMCBridge.twoStateCtmcSwitchProb up down t) up 0 := by
      convert CTMCBridge.twoStateCtmcSwitchProb_hasDerivAt up down 0 using 1
      simp [hr]
    have hd : HasDerivAt
        (fun t => CTMCBridge.twoStateCtmcSwitchProb down up t) down 0 := by
      convert CTMCBridge.twoStateCtmcSwitchProb_hasDerivAt down up 0 using 1
      simp [hrd]
    fin_cases i <;> fin_cases j
    · simpa [CTMCBridge.twoStateCtmcTransitionProb,
        CTMCBridge.twoStateCtmcStayProb, twoStateGenerator] using
        (hu.const_sub 1).hasDerivWithinAt (s := Ici 0)
    · simpa [CTMCBridge.twoStateCtmcTransitionProb, twoStateGenerator] using
        hu.hasDerivWithinAt (s := Ici 0)
    · simpa [CTMCBridge.twoStateCtmcTransitionProb, twoStateGenerator] using
        hd.hasDerivWithinAt (s := Ici 0)
    · simpa [CTMCBridge.twoStateCtmcTransitionProb,
        CTMCBridge.twoStateCtmcStayProb, twoStateGenerator] using
        (hd.const_sub 1).hasDerivWithinAt (s := Ici 0)

/-- Invariance under the actual transition semigroup, with uniqueness. -/
theorem stationaryHigh_iff {up down : ℝ} (S : TwoStateSemigroup up down)
    (hup : 0 < up) (hdown : 0 < down) (q : ℝ) :
    IsStationaryHigh S q ↔ q = up / (up + down) := by
  have hr : 0 < up + down := add_pos hup hdown
  have hrn : up + down ≠ 0 := ne_of_gt hr
  constructor
  · intro hq
    have he : Real.exp (-(up + down) * 1) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have heq := hq.2 1 zero_le_one
    rw [semigroupHigh_eq_transient S hrn q 1 zero_le_one] at heq
    unfold transientHigh at heq
    have hprod : (q - up / (up + down)) *
        (1 - Real.exp (-(up + down) * 1)) = 0 := by
      nlinarith [heq]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · linarith
  · rintro rfl
    refine ⟨⟨(div_pos hup hr).le, ?_⟩, ?_⟩
    · rw [div_le_one hr]
      linarith
    · intro t ht
      rw [semigroupHigh_eq_transient S hrn _ t ht]
      simp [transientHigh]

/-- The normalized stationary law is unique, including its low-state mass. -/
theorem stationaryLaw_iff {up down : ℝ} (S : TwoStateSemigroup up down)
    (hup : 0 < up) (hdown : 0 < down) (low high : ℝ) :
    (low + high = 1 ∧ IsStationaryHigh S high) ↔
      low = down / (up + down) ∧ high = up / (up + down) := by
  rw [stationaryHigh_iff S hup hdown]
  have hnorm : down / (up + down) + up / (up + down) = 1 := by
    rw [← add_div, add_comm down up, div_self (ne_of_gt (add_pos hup hdown))]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨by linarith, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hnorm, rfl⟩

/-- Existence and uniqueness of the stationary probability vector. -/
theorem stationaryLaw_existsUnique {up down : ℝ} (S : TwoStateSemigroup up down)
    (hup : 0 < up) (hdown : 0 < down) :
    ∃! law : ℝ × ℝ, law.1 + law.2 = 1 ∧ IsStationaryHigh S law.2 := by
  refine ⟨(down / (up + down), up / (up + down)), ?_, ?_⟩
  · exact (stationaryLaw_iff S hup hdown _ _).mpr ⟨rfl, rfl⟩
  · intro law hlaw
    obtain ⟨hlow, hhigh⟩ := (stationaryLaw_iff S hup hdown _ _).mp hlaw
    exact Prod.ext hlow hhigh

/-- The invariant law is equivalently determined by normalization and
balance of the two transition flows. -/
theorem stationaryHigh_iff_detailedBalance {up down : ℝ}
    (S : TwoStateSemigroup up down) (hup : 0 < up) (hdown : 0 < down)
    (low high : ℝ) (h : low + high = 1) :
    IsStationaryHigh S high ↔ low * up = high * down := by
  rw [stationaryHigh_iff S hup hdown, eq_div_iff (ne_of_gt (add_pos hup hdown))]
  have hnorm := congrArg (fun x : ℝ => x * up) h
  constructor <;> intro hb <;> nlinarith

/-- Deterministic evaluation needed only after the stochastic Fubini bridge. -/
theorem transientHigh_integral (up down h0 T : ℝ) (hr : up + down ≠ 0) :
    (∫ t in (0 : ℝ)..T, transientHigh up down h0 t) =
      up / (up + down) * T +
      (h0 - up / (up + down)) * (1 - Real.exp (-(up + down) * T)) / (up + down) := by
  let F : ℝ → ℝ := fun t =>
    up / (up + down) * t -
      (h0 - up / (up + down)) / (up + down) * Real.exp (-(up + down) * t)
  have hF : ∀ t, HasDerivAt F (transientHigh up down h0 t) t := by
    intro t
    have hd := ((hasDerivAt_id t).const_mul (up / (up + down))).sub
      ((((hasDerivAt_id t).const_mul (-(up + down))).exp).const_mul
        ((h0 - up / (up + down)) / (up + down)))
    simp only [id_eq, mul_one] at hd
    convert hd using 1
    unfold transientHigh
    field_simp [hr]
    ring
  have hi : IntervalIntegrable (transientHigh up down h0) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold transientHigh
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hi]
  simp only [F, mul_zero, Real.exp_zero]
  ring

/-- Coordinate measurability follows from the process's joint measurability. -/
theorem process_state_measurable {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : TwoStateProcess S Ω ν) (t : NNReal) :
    Measurable (X.state t) :=
  X.measurable.comp (measurable_const.prodMk measurable_id)

theorem process_state_event_measurable {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : TwoStateProcess S Ω ν) (t : NNReal) (i : Fin 2) :
    MeasurableSet {ω | X.state t ω = i} :=
  (process_state_measurable X t) (measurableSet_singleton i)

theorem processHigh_mem_Icc {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (t : NNReal) :
    processHigh X t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact measureReal_nonneg
  · exact measureReal_le_one

theorem process_low_mass {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (t : NNReal) :
    ν.real {ω | X.state t ω = 0} = 1 - processHigh X t := by
  have he : {ω | X.state t ω = 0} = {ω | X.state t ω = 1}ᶜ := by
    ext ω
    rcases fin2_zero_or_one (X.state t ω) with h | h <;> simp [h]
  rw [he, measureReal_compl (process_state_event_measurable X t 1)]
  simp [processHigh]

/-- The Markov law, not an assumed transient formula, supplies the marginal
probability from the initial distribution and transition semigroup. -/
theorem processHigh_eq_semigroupHigh {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (t : NNReal) :
    processHigh X t = semigroupHigh S (processHigh X 0) t := by
  let A : Set Ω := {ω | X.state 0 ω = 0 ∧ X.state t ω = 1}
  let B : Set Ω := {ω | X.state 0 ω = 1 ∧ X.state t ω = 1}
  have hsplit : {ω | X.state t ω = 1} = A ∪ B := by
    ext ω
    rcases fin2_zero_or_one (X.state 0 ω) with h | h <;> simp [A, B, h]
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro ω hA hB
    have he : (0 : Fin 2) = 1 := hA.1.symm.trans hB.1
    norm_num at he
  have hBmeas : MeasurableSet B :=
    (process_state_event_measurable X 0 1).inter
      (process_state_event_measurable X t 1)
  have hA : ν.real A = ν.real {ω | X.state 0 ω = 0} * S.transition t 0 1 := by
    simpa [A] using X.markov 0 t 0 1 [] (by simp)
  have hB : ν.real B = ν.real {ω | X.state 0 ω = 1} * S.transition t 1 1 := by
    simpa [B] using X.markov 0 t 1 1 [] (by simp)
  unfold processHigh semigroupHigh
  rw [hsplit, measureReal_union hdisj hBmeas, hA, hB, process_low_mass X 0]
  rfl

theorem processHigh_eq_transient {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (hr : up + down ≠ 0) (t : NNReal) :
    processHigh X t = transientHigh up down (processHigh X 0) t := by
  rw [processHigh_eq_semigroupHigh X t]
  exact semigroupHigh_eq_transient S hr _ t t.coe_nonneg

/-- The two-time high-state event used in the Appendix A.2 occupation
calculation follows from the finite-history Markov law. -/
theorem process_jointHigh_eq {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (X : TwoStateProcess S Ω ν) {s t : NNReal} (hst : s ≤ t) :
    ν.real {ω | X.state s ω = 1 ∧ X.state t ω = 1} =
      processHigh X s * S.transition (t - s : NNReal) 1 1 := by
  have hsum : s + (t - s) = t := by
    rw [add_comm, tsub_add_cancel_of_le hst]
  simpa [processHigh, hsum] using X.markov s (t - s) 1 1 [] (by simp)

/-- Fubini for the actual random occupation integral.  Its integrability is
derived from joint measurability and the bounded finite-state indicator. -/
theorem expected_occupation_eq_formula {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (hr : up + down ≠ 0) (T : ℝ) (hT : 0 < T) :
    (∫ ω, occupation X T ω ∂ν) =
      up / (up + down) + (processHigh X 0 - up / (up + down)) *
        (1 - Real.exp (-(up + down) * T)) / ((up + down) * T) := by
  let f : ℝ → Ω → ℝ :=
    fun t ω => if X.state t.toNNReal ω = 1 then 1 else 0
  have hX : Measurable (fun z : ℝ × Ω => X.state z.1.toNNReal z.2) := by
    have hmap : Measurable (fun z : ℝ × Ω => (z.1.toNNReal, z.2)) :=
      (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
    exact X.measurable.comp hmap
  have hf : Measurable (Function.uncurry f) := by
    apply Measurable.ite
    · exact hX (measurableSet_singleton 1)
    · exact measurable_const
    · exact measurable_const
  have hbounded : ∀ z : ℝ × Ω, ‖Function.uncurry f z‖ ≤ 1 := by
    intro z
    dsimp [f, Function.uncurry]
    split_ifs <;> norm_num
  letI : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T)) := by
    rw [isFiniteMeasure_restrict, Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc 0 T)).prod ν) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hbounded)
  have hinner (t : ℝ) :
      (∫ ω, f t ω ∂ν) = processHigh X t.toNNReal := by
    simpa [f, processHigh, Set.indicator] using
      (integral_indicator_one (μ := ν)
        (process_state_event_measurable X t.toNNReal 1))
  have hformula :
      (∫ t in (0 : ℝ)..T, ∫ ω, f t ω ∂ν) =
        ∫ t in (0 : ℝ)..T, transientHigh up down (processHigh X 0) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (Set.uIcc_of_le hT.le ▸ ht).1
    change (∫ ω, f t ω ∂ν) = _
    rw [hinner, processHigh_eq_transient X hr]
    simp [Real.coe_toNNReal t ht0]
  calc
    (∫ ω, occupation X T ω ∂ν) =
        T⁻¹ * ∫ t in (0 : ℝ)..T, ∫ ω, f t ω ∂ν := by
      unfold occupation
      rw [integral_const_mul]
      simp only [intervalIntegral.integral_of_le hT.le]
      rw [uIoc_of_le hT.le] at hint
      exact congrArg (fun value : ℝ => T⁻¹ * value) (integral_integral_swap hint).symm
    _ = T⁻¹ * ∫ t in (0 : ℝ)..T,
        transientHigh up down (processHigh X 0) t := by rw [hformula]
    _ = _ := by
      rw [transientHigh_integral up down (processHigh X 0) T hr]
      field_simp [hr, ne_of_gt hT]

theorem expected_occupation_startLow_bias
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (hup : 0 < up) (hdown : 0 < down)
    (hstart : processHigh X 0 = 0) (T : ℝ) (hT : 0 < T) :
    (∫ ω, occupation X T ω ∂ν) =
      up / (up + down) -
        (up / (up + down)) * (1 - Real.exp (-(up + down) * T)) /
          ((up + down) * T) ∧
    0 < (up / (up + down)) * (1 - Real.exp (-(up + down) * T)) /
          ((up + down) * T) := by
  have hr : 0 < up + down := add_pos hup hdown
  constructor
  · rw [expected_occupation_eq_formula X (ne_of_gt hr) T hT, hstart]
    ring
  · have he : Real.exp (-(up + down) * T) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    exact div_pos (mul_pos (div_pos hup hr) (sub_pos.mpr he)) (mul_pos hr hT)

end
end Grados26Learning
