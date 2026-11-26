module

public import Grados26Learning.CTMCModel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # The product-integral formula for the occupation second moment -/

namespace Grados26Learning

open MeasureTheory Set

noncomputable section

private theorem occupation_joint_integral_bridge
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (T : ℝ) (hT : 0 < T) :
    let J := fun p : ℝ × ℝ =>
      ν.real {ω | X.state p.1.toNNReal ω = 1 ∧ X.state p.2.toNNReal ω = 1}
    let τ : Measure ℝ := volume.restrict (Ioc 0 T)
    (∫ ω, (occupation X T ω) ^ 2 ∂ν) =
      T⁻¹ ^ 2 * (∫ p, J p ∂(τ.prod τ)) ∧ Integrable J (τ.prod τ) := by
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  let f : ℝ → Ω → ℝ := fun t ω => if X.state t.toNNReal ω = 1 then 1 else 0
  let g : (ℝ × ℝ) → Ω → ℝ := fun p ω => f p.1 ω * f p.2 ω
  have hstate₁ : Measurable (fun z : (ℝ × ℝ) × Ω => X.state z.1.1.toNNReal z.2) := by
    exact X.measurable.comp (show Measurable (fun z : (ℝ × ℝ) × Ω =>
      (z.1.1.toNNReal, z.2)) by fun_prop)
  have hstate₂ : Measurable (fun z : (ℝ × ℝ) × Ω => X.state z.1.2.toNNReal z.2) := by
    exact X.measurable.comp (show Measurable (fun z : (ℝ × ℝ) × Ω =>
      (z.1.2.toNNReal, z.2)) by fun_prop)
  have hm₁ : Measurable (fun z : (ℝ × ℝ) × Ω => f z.1.1 z.2) :=
    Measurable.ite (hstate₁ (measurableSet_singleton 1)) measurable_const measurable_const
  have hm₂ : Measurable (fun z : (ℝ × ℝ) × Ω => f z.1.2 z.2) :=
    Measurable.ite (hstate₂ (measurableSet_singleton 1)) measurable_const measurable_const
  have hmeas : Measurable (Function.uncurry g) := hm₁.mul hm₂
  have hbounded : ∀ z : (ℝ × ℝ) × Ω, ‖Function.uncurry g z‖ ≤ 1 := by
    intro z
    dsimp [g, f, Function.uncurry]
    split_ifs <;> norm_num
  have hint : Integrable (Function.uncurry g) ((τ.prod τ).prod ν) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbounded)
  have hpoint (ω : Ω) :
      (occupation X T ω) ^ 2 = T⁻¹ ^ 2 * (∫ p, g p ω ∂(τ.prod τ)) := by
    calc
      (occupation X T ω) ^ 2 =
          T⁻¹ ^ 2 * ((∫ s, f s ω ∂τ) * (∫ t, f t ω ∂τ)) := by
        simp only [occupation, intervalIntegral.integral_of_le hT.le, f, τ, pow_two]
        ring
      _ = _ := by
        exact congrArg (fun u : ℝ => T⁻¹ ^ 2 * u)
          (integral_prod_mul (μ := τ) (ν := τ) (fun s => f s ω) (fun t => f t ω)).symm
  have hstate (t : ℝ) : Measurable (X.state t.toNNReal) :=
    X.measurable.comp (measurable_const.prodMk measurable_id)
  have hinner (p : ℝ × ℝ) :
      (∫ ω, g p ω ∂ν) =
        ν.real {ω | X.state p.1.toNNReal ω = 1 ∧ X.state p.2.toNNReal ω = 1} := by
    let A := {ω | X.state p.1.toNNReal ω = 1 ∧ X.state p.2.toNNReal ω = 1}
    have hA : MeasurableSet A :=
      (hstate p.1 (measurableSet_singleton 1)).inter (hstate p.2 (measurableSet_singleton 1))
    have heq : g p = A.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hs : X.state p.1.toNNReal ω = 1 <;>
        by_cases ht : X.state p.2.toNNReal ω = 1 <;>
        simp [g, f, A, Set.indicator, hs, ht]
    rw [heq]
    exact integral_indicator_one (μ := ν) hA
  refine ⟨?_, hint.integral_prod_left.congr (Filter.Eventually.of_forall hinner)⟩
  calc
    (∫ ω, (occupation X T ω) ^ 2 ∂ν) =
        T⁻¹ ^ 2 * (∫ ω, ∫ p, g p ω ∂(τ.prod τ) ∂ν) := by
      simp only [hpoint, integral_const_mul]
    _ = T⁻¹ ^ 2 * (∫ p, ∫ ω, g p ω ∂ν ∂(τ.prod τ)) :=
      congrArg (fun u : ℝ => T⁻¹ ^ 2 * u) (integral_integral_swap hint).symm
    _ = _ := by simp only [hinner, τ]

/-- Applying Fubini to the squared occupation integral gives the integral
of the two-time high-state probability over the full time square. -/
theorem expected_occupation_sq_eq_joint_integral
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (T : ℝ) (hT : 0 < T) :
    (∫ ω, (occupation X T ω) ^ 2 ∂ν) =
      T⁻¹ ^ 2 * ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T,
        ν.real {ω | X.state s.toNNReal ω = 1 ∧ X.state t.toNNReal ω = 1} := by
  obtain ⟨heq, hint⟩ := occupation_joint_integral_bridge X T hT
  rw [heq, integral_prod _ hint]
  simp only [intervalIntegral.integral_of_le hT.le]

private theorem integral_prod_eq_twice_upper_triangle (T : ℝ)
    {J : ℝ × ℝ → ℝ} (hsym : ∀ z, J z.swap = J z)
    (hint : Integrable J ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))) :
    (∫ z, J z ∂((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))) =
      2 * ∫ s in Ioc (0 : ℝ) T, ∫ t in s..T, J (s, t) := by
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  let A : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let B : Set (ℝ × ℝ) := {z | z.2 < z.1}
  let D : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hA : MeasurableSet A := measurableSet_lt measurable_fst measurable_snd
  have hB : MeasurableSet B := measurableSet_lt measurable_snd measurable_fst
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have hdiag : (τ.prod τ) D = 0 := by
    rw [Measure.prod_apply hD]
    have hslice (s : ℝ) : Prod.mk s ⁻¹' D = {s} := by
      ext t
      simp [D, eq_comm]
    simp only [hslice, measure_singleton, lintegral_zero]
  have hneq : ∀ᵐ z ∂(τ.prod τ), z.1 ≠ z.2 := by
    rw [ae_iff]
    simpa [D] using hdiag
  have hsplit : J =ᵐ[τ.prod τ] fun z => A.indicator J z + B.indicator J z := by
    filter_upwards [hneq] with z h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · simp [A, B, Set.indicator, hlt, not_lt_of_ge hlt.le]
    · simp [A, B, Set.indicator, hgt, not_lt_of_ge hgt.le]
  have hswap_fun : (fun z => A.indicator J z.swap) = B.indicator J := by
    funext z
    by_cases h : z.2 < z.1 <;> simp [A, B, Set.indicator, hsym, h]
  have hswap := integral_prod_swap (μ := τ) (ν := τ) (A.indicator J)
  rw [hswap_fun] at hswap
  have htria : (∫ z, A.indicator J z ∂(τ.prod τ)) =
      ∫ s in Ioc (0 : ℝ) T, ∫ t in s..T, J (s, t) := by
    rw [integral_prod _ (hint.indicator hA)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc 0 T))]
      with s hs
    have hslice : (fun t => A.indicator J (s, t)) = (Ioi s).indicator (fun t => J (s, t)) := by
      funext t
      simp [A, Set.indicator]
    have hcap : Ioi s ∩ Ioc 0 T = Ioc s T := by
      ext t
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.1.trans h.1, h.2⟩⟩
    rw [hslice, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hcap, intervalIntegral.integral_of_le hs.2]
  calc
    (∫ z, J z ∂(τ.prod τ)) = ∫ z, A.indicator J z + B.indicator J z ∂(τ.prod τ) :=
      integral_congr_ae hsplit
    _ = (∫ z, A.indicator J z ∂(τ.prod τ)) + (∫ z, B.indicator J z ∂(τ.prod τ)) :=
      integral_add (hint.indicator hA) (hint.indicator hB)
    _ = _ := by rw [hswap, htria, two_mul]

/-- The Fubini and symmetry identity used in the first line of the
occupation second-moment calculation. The diagonal has zero time measure. -/
theorem expected_occupation_sq_eq_twice_triangle
    {up down : ℝ} {S : TwoStateSemigroup up down}
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (X : TwoStateProcess S Ω ν) (T : ℝ) (hT : 0 < T) :
    (∫ ω, (occupation X T ω) ^ 2 ∂ν) =
      (2 / T ^ 2) * ∫ s in (0 : ℝ)..T, ∫ t in s..T,
        ν.real {ω | X.state s.toNNReal ω = 1 ∧ X.state t.toNNReal ω = 1} := by
  obtain ⟨heq, hint⟩ := occupation_joint_integral_bridge X T hT
  have hsym : ∀ z : ℝ × ℝ,
      ν.real {ω | X.state z.2.toNNReal ω = 1 ∧ X.state z.1.toNNReal ω = 1} =
        ν.real {ω | X.state z.1.toNNReal ω = 1 ∧ X.state z.2.toNNReal ω = 1} := by
    intro z
    simp only [and_comm]
  rw [heq, integral_prod_eq_twice_upper_triangle T hsym hint,
    intervalIntegral.integral_of_le hT.le]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end
end Grados26Learning
