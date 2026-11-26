module

public import Grados26Learning.PaperInterface
public import Grados26Learning.CTMC
public import Grados26Learning.WorkerResult
public import Grados26Learning.Algebra

@[expose] public section

namespace Grados26Learning

open Set MeasureTheory

noncomputable section
universe u

/-- Lemma 2 of the pinned manuscript. The Markov and generator properties
are assumptions on the process, while its transition and occupation
formulas are conclusions. -/
theorem lemma2 : lemma2Spec.{u} := by
  unfold lemma2Spec
  intro E a ha
  have hrate := workerLearningRate_eq E a ha
  have hup : 0 < workerLearningRate E a := by
    rw [hrate]
    exact learningRate_pos E.parameters ha
  have hr : workerLearningRate E a + E.mu ≠ 0 := ne_of_gt (add_pos hup E.mu_pos)
  have hq : workerLearningRate E a + E.mu = learningRate E.parameters a + E.mu :=
    congrArg (fun l : ℝ => l + E.mu) hrate
  have hshare : workerLearningRate E a / (workerLearningRate E a + E.mu) =
      stationaryShare E.parameters a := by
    rw [hrate]
    rfl
  refine ⟨hup, E.mu_pos, ⟨canonicalSemigroup _ _ hup E.mu_pos⟩, ?_⟩
  intro S
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro low high
    have h := stationaryLaw_iff S hup E.mu_pos low high
    rwa [hshare, hq] at h
  · intro low high hnorm
    exact stationaryHigh_iff_detailedBalance S hup E.mu_pos low high hnorm
  · intro h0 _ t ht
    have h := semigroupHigh_eq_transient S hr h0 t ht
    unfold transientHigh at h
    rwa [hshare, hq] at h
  · intro t ht
    have h := transition_matrix_entries S hr t ht
    dsimp only at h ⊢
    rwa [hshare, hq] at h
  · intro Ω _ ν _ X
    refine ⟨processHigh_mem_Icc X 0, ?_, ?_, ?_⟩
    · intro t
      have h := processHigh_eq_transient X hr t
      unfold transientHigh at h
      rwa [hshare, hq] at h
    · intro T hT
      have h := expected_occupation_eq_formula X hr T hT
      rwa [hshare, hq] at h
    · intro hstart T hT
      have h := expected_occupation_startLow_bias X hup E.mu_pos hstart T hT
      rw [hshare, hq] at h
      constructor
      · rw [h.1]
        ring
      · rw [h.1]
        exact sub_lt_self _ h.2

end
end Grados26Learning
