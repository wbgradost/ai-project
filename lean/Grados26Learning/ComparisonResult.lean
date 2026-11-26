module

public import Grados26Learning.DeterministicInterface
public import Grados26Learning.Algebra

@[expose] public section

namespace Grados26Learning
open Set
noncomputable section

private theorem strictSkillFOSD_iff (qHigh qLow sL sH : ℝ) (hs : sL < sH) :
    (skillFOSD qHigh qLow sL sH ∧
      ∃ x, skillCDF qHigh sL sH x < skillCDF qLow sL sH x) ↔ qLow < qHigh := by
  constructor
  · rintro ⟨_, x, hx⟩
    by_contra h
    have hb := (skillFOSD_iff qLow qHigh sL sH hs).2 (le_of_not_gt h) x
    exact (not_lt_of_ge hb) hx
  · intro h
    refine ⟨(skillFOSD_iff qHigh qLow sL sH hs).2 h.le, sL, ?_⟩
    simpa only [skillCDF, lt_self_iff_false, if_false, hs, if_true, sub_lt_sub_iff_left] using h

/-- Proposition 2, including active comparisons, saturation, FOSD and mean skill. -/
theorem proposition2 : proposition2Spec := by
  unfold proposition2Spec
  intro E
  dsimp only
  intro u v hu huv
  refine ⟨share_difference E.parameters hu (le_trans hu huv.le), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hv
    exact ⟨share_active_difference E.parameters hu huv hv,
      active_pair_increase_iff E.parameters hu huv hv,
      active_pair_equal_iff E.parameters hu huv hv,
      active_pair_decrease_iff E.parameters hu huv hv⟩
  · intro hub hbv
    exact mixed_pair_decrease E.parameters hu hub hbv
  · intro hbu
    exact plateau_pair_equal E.parameters hbu (le_trans hbu huv.le)
  · exact skillFOSD_iff _ _ E.sL E.sH E.skill_order
  · exact meanSkill_order_iff _ _ E.sL E.sH E.skill_order
  · exact strictSkillFOSD_iff _ _ E.sL E.sH E.skill_order
  · simp only [lt_iff_not_ge, meanSkill_order_iff _ _ E.sL E.sH E.skill_order]

end
end Grados26Learning
