module

public import Grados26Learning.DeterministicInterface
public import Grados26Learning.SensitivityBoundary

@[expose] public section

namespace Grados26Learning

open Set Filter
open scoped Topology

/-- Corollary 1 with the cutoff parameter treated independently from assistance. -/
theorem corollary1 : corollary1Spec := by
  intro E
  dsimp only
  generalize hp : E.parameters = p
  refine ⟨critical_complementarity_iff p, ?_, threshold_partial_derivatives p, ?_,
    hasDerivWithinAt_rawShare_b_boundary p, ?_, ?_⟩
  · intro _ q hb hη
    exact thresholds_independent_of_rates p q hb hη
  · intro a ha
    rcases stationary_level_partials p ha with ⟨hl, hlp, hk, hkp, hm, hmn, hη, hηp, hb⟩
    exact ⟨hl, hlp, hk, hkp, ratePartial_zero_iff p ha, hm, hmn, hη, hηp,
      complementarityPartial_zero_iff p ha, hb, hasDerivAt_rawShare_b_saturated p⟩
  · intro c hc a ha
    exact common_rate_scaling p hc ha
  · intro h a ha har
    obtain ⟨hΔ, hG, hformula, hLdiff, hLneg, hMdiff, hMsign, hKdiff, hKsign⟩ :=
      stationary_gain_partials p h ha har
    exact ⟨hΔ, hG, hformula, hLdiff, hLneg, stationary_gain_strictAntiOn_lambda0 p h ha har,
      hMdiff, hMsign, hKdiff, hKsign⟩

end Grados26Learning
