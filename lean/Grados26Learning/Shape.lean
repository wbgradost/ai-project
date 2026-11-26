module

public import Grados26Learning.Algebra
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace Grados26Learning

open Set

noncomputable section

theorem eta_pos_of_strong (p : Parameters) (h : 1 < p.eta * p.b) : 0 < p.eta := by
  by_contra hn
  have hz : p.eta = 0 := le_antisymm (le_of_not_gt hn) p.eta_nonneg
  norm_num [hz] at h

theorem return_twice_peak (p : Parameters) : returnPoint p = 2 * peak p := by
  unfold returnPoint peak
  ring

theorem eta_return_identity (p : Parameters) (hη : 0 < p.eta) :
    p.eta * returnPoint p = p.eta * p.b - 1 := by
  unfold returnPoint
  field_simp [ne_of_gt hη] <;> ring

theorem eta_peak_identity (p : Parameters) (hη : 0 < p.eta) :
    p.eta * (p.b - 2 * peak p) = 1 := by
  unfold peak
  field_simp [ne_of_gt hη] <;> ring

theorem strong_thresholds (p : Parameters) (h : 1 < p.eta * p.b) :
    0 < peak p ∧ peak p < returnPoint p ∧ returnPoint p < p.b ∧ peak p < p.b / 2 := by
  have hη := eta_pos_of_strong p h
  have hid := eta_return_identity p hη
  have hr : 0 < returnPoint p := by nlinarith
  have hib : returnPoint p < p.b := by
    unfold returnPoint
    exact sub_lt_self _ (one_div_pos.mpr hη)
  have heq := return_twice_peak p
  constructor
  · nlinarith
  constructor
  · nlinarith
  exact ⟨hib, by nlinarith⟩

theorem weak_strictAntiOn (p : Parameters) (h : p.eta * p.b ≤ 1) :
    StrictAntiOn (stationaryShare p) (Icc 0 p.b) := by
  intro u hu v hv huv
  apply (active_pair_decrease_iff p hu.1 huv hv.2).2
  rcases eq_or_lt_of_le p.eta_nonneg with hzero | hpos
  · simp [← hzero]
  · have huvpos : 0 < u + v := by linarith [hu.1]
    nlinarith [mul_pos hpos huvpos]

theorem weak_loss (p : Parameters) (h : p.eta * p.b ≤ 1) {a : ℝ} (ha : 0 < a) :
    stationaryShare p a < stationaryShare p 0 := by
  by_cases hab : a ≤ p.b
  · exact weak_strictAntiOn p h ⟨le_rfl, p.b_pos.le⟩ ⟨ha.le, hab⟩ ha
  · exact mixed_pair_decrease p le_rfl p.b_pos (le_of_not_ge hab)

theorem strong_strictMonoOn (p : Parameters) (h : 1 < p.eta * p.b) :
    StrictMonoOn (stationaryShare p) (Icc 0 (peak p)) := by
  intro u hu v hv huv
  have ht := strong_thresholds p h
  have hp_b : peak p < p.b := lt_trans ht.2.1 ht.2.2.1
  apply (active_pair_increase_iff p hu.1 huv (le_trans hv.2 hp_b.le)).2
  have hη := eta_pos_of_strong p h
  have hid := eta_peak_identity p hη
  have hgap : 0 < 2 * peak p - u - v := by linarith [hu.2, hv.2]
  nlinarith [mul_pos hη hgap]

theorem strong_strictAntiOn (p : Parameters) (h : 1 < p.eta * p.b) :
    StrictAntiOn (stationaryShare p) (Icc (peak p) p.b) := by
  intro u hu v hv huv
  have ht := strong_thresholds p h
  apply (active_pair_decrease_iff p (le_trans ht.1.le hu.1) huv hv.2).2
  have hη := eta_pos_of_strong p h
  have hid := eta_peak_identity p hη
  have hgap : 0 < u + v - 2 * peak p := by linarith [hu.1, hv.1]
  nlinarith [mul_pos hη hgap]

theorem strong_peak_strict_max (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 ≤ a) (hne : a ≠ peak p) :
    stationaryShare p a < stationaryShare p (peak p) := by
  have ht := strong_thresholds p h
  have hp_b : peak p < p.b := lt_trans ht.2.1 ht.2.2.1
  rcases lt_trichotomy a (peak p) with hlt | heq | hgt
  · exact strong_strictMonoOn p h ⟨ha, hlt.le⟩ ⟨ht.1.le, le_rfl⟩ hlt
  · exact False.elim (hne heq)
  · by_cases hab : a ≤ p.b
    · exact strong_strictAntiOn p h ⟨le_rfl, hp_b.le⟩ ⟨hgt.le, hab⟩ hgt
    · exact mixed_pair_decrease p ht.1.le hp_b (le_of_not_ge hab)

theorem strong_global_max (p : Parameters) (h : 1 < p.eta * p.b) :
    IsMaxOn (stationaryShare p) (Ici 0) (peak p) := by
  intro a ha
  by_cases heq : a = peak p
  · simp [heq]
  · exact (strong_peak_strict_max p h ha heq).le

theorem strong_max_unique (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 ≤ a) (hmax : IsMaxOn (stationaryShare p) (Ici 0) a) :
    a = peak p := by
  by_contra hne
  have hstrict := strong_peak_strict_max p h ha hne
  have hle : stationaryShare p (peak p) ≤ stationaryShare p a :=
    hmax (show peak p ∈ Ici 0 from mem_Ici.mpr (strong_thresholds p h).1.le)
  exact (not_le_of_gt hstrict) hle

theorem weak_global_max (p : Parameters) (h : p.eta * p.b ≤ 1) :
    IsMaxOn (stationaryShare p) (Ici 0) 0 := by
  intro a ha
  change 0 ≤ a at ha
  rcases eq_or_lt_of_le ha with hz | hpos
  · simp [← hz]
  · exact (weak_loss p h hpos).le

theorem weak_max_unique (p : Parameters) (h : p.eta * p.b ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (hmax : IsMaxOn (stationaryShare p) (Ici 0) a) :
    a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  have hstrict := weak_loss p h hpos
  have hle : stationaryShare p 0 ≤ stationaryShare p a :=
    hmax (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
  exact (not_le_of_gt hstrict) hle

theorem strong_gain_iff (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : 0 ≤ a) :
    stationaryShare p 0 < stationaryShare p a ↔ 0 < a ∧ a < returnPoint p := by
  have ht := strong_thresholds p h
  have hη := eta_pos_of_strong p h
  have hid := eta_return_identity p hη
  by_cases hzero : a = 0
  · simp [hzero]
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
  by_cases hab : a ≤ p.b
  · rw [active_pair_increase_iff p le_rfl hapos hab]
    constructor
    · intro hh
      exact ⟨hapos, by nlinarith⟩
    · intro hh
      nlinarith [mul_pos hη (sub_pos.mpr hh.2)]
  · have hba := le_of_not_ge hab
    have hloss := mixed_pair_decrease p (show (0 : ℝ) ≤ 0 from le_rfl) p.b_pos hba
    have hnot : ¬ (0 < a ∧ a < returnPoint p) := by
      intro hh
      linarith [ht.2.2.1, hh.2]
    exact iff_of_false (not_lt.mpr hloss.le) hnot

theorem return_to_noAI (p : Parameters) (h : 1 < p.eta * p.b) :
    stationaryShare p (returnPoint p) = stationaryShare p 0 := by
  have ht := strong_thresholds p h
  have hrpos : 0 < returnPoint p := lt_trans ht.1 ht.2.1
  apply (active_pair_equal_iff p le_rfl hrpos ht.2.2.1.le).2
  have hid := eta_return_identity p (eta_pos_of_strong p h)
  nlinarith

theorem strong_loss_after_return (p : Parameters) (h : 1 < p.eta * p.b)
    {a : ℝ} (ha : returnPoint p < a) :
    stationaryShare p a < stationaryShare p 0 := by
  have ht := strong_thresholds p h
  have hapos : 0 < a := lt_trans (lt_trans ht.1 ht.2.1) ha
  by_cases hab : a ≤ p.b
  · apply (active_pair_decrease_iff p le_rfl hapos hab).2
    have hid := eta_return_identity p (eta_pos_of_strong p h)
    nlinarith [mul_pos (eta_pos_of_strong p h) (sub_pos.mpr ha)]
  · exact mixed_pair_decrease p le_rfl p.b_pos (le_of_not_ge hab)

end

end Grados26Learning
