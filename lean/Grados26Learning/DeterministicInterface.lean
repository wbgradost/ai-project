module

public import Grados26Learning.Economy
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Source-facing specifications for the pinned Grados manuscript

Exact source: ai-project commit 3f8749bfbb5ee2c3d1eefa646724fb6c043018cf.
These four transparent propositions are the non-stochastic source statements.
Their separate theorem endpoints are supplied only when Lean checks them.
Assumptions 1 and 2 and Definition 1 govern all five results.
-/
namespace Grados26Learning

open Set Filter
open scoped Topology

noncomputable section

/-- Lemma 1, including the existence required by greatest-maximizer selection. -/
def lemma1Spec : Prop :=
  (∀ W : WorkerModel,
    IsCompact (inputMaximizers W) ∧ IsGreatest (inputMaximizers W) (referenceInput W) ∧
    ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ, 0 ≤ a →
      IsGreatest (effortMaximizers W s a) (selectedEffort W s a) ∧
      selectedEffort W s a = max (referenceInput W - s - a) 0 ∧
      (0 < selectedEffort W s a → deriv W.p (referenceInput W) = W.gamma) ∧
      (referenceInput W ≤ s + a →
        selectedEffort W s a = 0 ∧ derivWithin W.p (Ici 0) (s + a) ≤ W.gamma ∧
        (referenceInput W < s + a → derivWithin W.p (Ici 0) (s + a) < W.gamma))) ∧
  (∀ E : Economy, ∀ a : ℝ, 0 ≤ a →
    (a < E.parameters.b → selectedEffort E.worker E.sL a = E.parameters.b - a ∧
      0 < selectedEffort E.worker E.sL a) ∧
    (E.parameters.b ≤ a → selectedEffort E.worker E.sL a = 0)) ∧
  (∀ E : Economy, ∀ a ∈ Ioo (0 : ℝ) E.parameters.b,
    HasDerivAt (selectedEffort E.worker E.sL) (-1) a) ∧
  (∀ E : Economy, ∀ a : ℝ, 0 ≤ a →
    workerLearningRate E a = learningRate E.parameters a)

/-- Proposition 1: all regimes, the unique global maximum and both boundaries. -/
def proposition1Spec : Prop :=
  ∀ E : Economy, let p := E.parameters
    ContinuousOn (stationaryShare p) (Ici 0) ∧
    (∀ a ∈ Ioo (0 : ℝ) p.b,
      HasDerivAt (stationaryShare p)
        (p.mu*p.kappa*(p.eta*(p.b-2*a)-1)/(learningRate p a+p.mu)^2) a) ∧
    HasDerivWithinAt (stationaryShare p)
      (p.mu*p.kappa*(p.eta*p.b-1)/(learningRate p 0+p.mu)^2) (Ici 0) 0 ∧
    (p.eta*p.b ≤ 1 →
      StrictAntiOn (stationaryShare p) (Icc 0 p.b) ∧
      IsMaxOn (stationaryShare p) (Ici 0) 0 ∧
      (∀ x : ℝ, 0 ≤ x → IsMaxOn (stationaryShare p) (Ici 0) x → x = 0) ∧
      (∀ a : ℝ, 0 < a → stationaryShare p a < stationaryShare p 0)) ∧
    (p.eta*p.b = 1 → HasDerivWithinAt (stationaryShare p) 0 (Ici 0) 0 ∧
      ∀ a ∈ Ioo (0 : ℝ) p.b, deriv (stationaryShare p) a < 0) ∧
    (1 < p.eta*p.b →
      0 < peak p ∧ peak p < returnPoint p ∧ returnPoint p < p.b ∧
      peak p < p.b/2 ∧ returnPoint p = 2*peak p ∧
      StrictMonoOn (stationaryShare p) (Icc 0 (peak p)) ∧
      StrictAntiOn (stationaryShare p) (Icc (peak p) p.b) ∧
      IsMaxOn (stationaryShare p) (Ici 0) (peak p) ∧
      (∀ x : ℝ, 0 ≤ x → IsMaxOn (stationaryShare p) (Ici 0) x → x = peak p) ∧
      (∀ a : ℝ, 0 ≤ a →
        (stationaryShare p 0 < stationaryShare p a ↔ 0 < a ∧ a < returnPoint p)) ∧
      (∀ a : ℝ, 0 < a → (stationaryShare p a = stationaryShare p 0 ↔ a = returnPoint p)) ∧
      (∀ a : ℝ, 0 < a → (stationaryShare p a < stationaryShare p 0 ↔ returnPoint p < a))) ∧
    (∀ a : ℝ, p.b ≤ a →
      effort p a = 0 ∧ learningRate p a = p.lambda0 ∧
      stationaryShare p a = p.lambda0/(p.lambda0+p.mu) ∧
      stationaryShare p a < stationaryShare p 0) ∧
    HasDerivWithinAt (stationaryShare p)
      (-p.mu*p.kappa*(1+p.eta*p.b)/(p.lambda0+p.mu)^2) (Iic p.b) p.b ∧
    HasDerivWithinAt (stationaryShare p) 0 (Ici p.b) p.b ∧
    (∀ a ∈ Ioo (0 : ℝ) p.b, deriv (deriv (stationaryShare p)) a < 0) ∧
    StrictConcaveOn ℝ (Icc 0 p.b) (stationaryShare p) ∧
    ¬ ConcaveOn ℝ (Ici 0) (stationaryShare p) ∧
    ¬ DifferentiableAt ℝ (stationaryShare p) p.b

/-- Proposition 2: active comparisons are scoped to v<=b; the tail is separate. -/
def proposition2Spec : Prop :=
  ∀ E : Economy, let p := E.parameters
    ∀ u v : ℝ, 0 ≤ u → u < v →
      stationaryShare p v - stationaryShare p u =
        p.mu*p.kappa*(effectiveEffort p v-effectiveEffort p u) /
          ((learningRate p v+p.mu)*(learningRate p u+p.mu)) ∧
      (v ≤ p.b →
        stationaryShare p v-stationaryShare p u =
          p.mu*p.kappa*(v-u)*(p.eta*(p.b-u-v)-1) /
            ((learningRate p v+p.mu)*(learningRate p u+p.mu)) ∧
        (stationaryShare p u < stationaryShare p v ↔ p.eta*(p.b-u-v)>1) ∧
        (stationaryShare p v = stationaryShare p u ↔ p.eta*(p.b-u-v)=1) ∧
        (stationaryShare p v < stationaryShare p u ↔ p.eta*(p.b-u-v)<1)) ∧
      (u < p.b → p.b ≤ v → stationaryShare p v < stationaryShare p u) ∧
      (p.b ≤ u → stationaryShare p v = stationaryShare p u) ∧
      (skillFOSD (stationaryShare p v) (stationaryShare p u) E.sL E.sH ↔
        stationaryShare p u ≤ stationaryShare p v) ∧
      (meanSkill (stationaryShare p u) E.sL E.sH ≤
        meanSkill (stationaryShare p v) E.sL E.sH ↔
          stationaryShare p u ≤ stationaryShare p v) ∧
      (skillFOSD (stationaryShare p v) (stationaryShare p u) E.sL E.sH ∧
        (∃ x, skillCDF (stationaryShare p v) E.sL E.sH x <
          skillCDF (stationaryShare p u) E.sL E.sH x) ↔
        stationaryShare p u < stationaryShare p v) ∧
      (meanSkill (stationaryShare p u) E.sL E.sH <
        meanSkill (stationaryShare p v) E.sL E.sH ↔
          stationaryShare p u < stationaryShare p v)

/-- A transparent spelling of the source phrase "has the sign of". -/
def sameSign (x y : ℝ) : Prop :=
  (0 < x ↔ 0 < y) ∧ (x = 0 ↔ y = 0) ∧ (x < 0 ↔ y < 0)

/-- Corollary 1, with genuine partial derivatives of the unbundled formula. -/
def corollary1Spec : Prop :=
  ∀ E : Economy, let p := E.parameters
    (1 < p.eta*p.b ↔ 1/p.b < p.eta) ∧
    (1 < p.eta*p.b → ∀ q : Parameters, q.b = p.b → q.eta = p.eta →
      peak q = peak p ∧ returnPoint q = returnPoint p) ∧
    (1 < p.eta*p.b →
      HasDerivAt (fun η : ℝ => (p.b-1/η)/2) (1/(2*p.eta^2)) p.eta ∧
      HasDerivAt (fun η : ℝ => p.b-1/η) (1/p.eta^2) p.eta ∧
      HasDerivAt (fun b : ℝ => (b-1/p.eta)/2) (1/2) p.b ∧
      HasDerivAt (fun b : ℝ => b-1/p.eta) 1 p.b) ∧
    (∀ a : ℝ, 0 ≤ a →
      let D := learningRate p a+p.mu
      HasDerivAt (fun l : ℝ => rawShare p.b l p.kappa p.mu p.eta a) (p.mu/D^2) p.lambda0 ∧
      0 < p.mu/D^2 ∧
      HasDerivAt (fun k : ℝ => rawShare p.b p.lambda0 k p.mu p.eta a)
        (p.mu*effectiveEffort p a/D^2) p.kappa ∧
      0 ≤ p.mu*effectiveEffort p a/D^2 ∧
      (p.mu*effectiveEffort p a/D^2 = 0 ↔ p.b ≤ a) ∧
      HasDerivAt (fun m : ℝ => rawShare p.b p.lambda0 p.kappa m p.eta a)
        (-learningRate p a/D^2) p.mu ∧
      -learningRate p a/D^2 < 0 ∧
      HasDerivWithinAt (fun η : ℝ => rawShare p.b p.lambda0 p.kappa p.mu η a)
        (p.mu*p.kappa*a*max (p.b - a) 0/D^2) (Ici 0) p.eta ∧
      0 ≤ p.mu*p.kappa*a*max (p.b - a) 0/D^2 ∧
      (p.mu*p.kappa*a*max (p.b - a) 0/D^2 = 0 ↔ a = 0 ∨ p.b ≤ a) ∧
      (a < p.b →
        HasDerivAt (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a)
          (p.mu*p.kappa*(1+p.eta*a)/D^2) p.b ∧
        0 < p.mu*p.kappa*(1+p.eta*a)/D^2) ∧
      (p.b < a → HasDerivAt (fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta a) 0 p.b)) ∧
    (let f := fun b : ℝ => rawShare b p.lambda0 p.kappa p.mu p.eta p.b
     let rightSlope := p.mu * p.kappa * (1 + p.eta * p.b) / (p.lambda0 + p.mu)^2
     HasDerivWithinAt f 0 (Iic p.b) p.b ∧
       HasDerivWithinAt f rightSlope (Ici p.b) p.b ∧ 0 < rightSlope) ∧
    (∀ c : ℝ, 0 < c → ∀ a : ℝ, 0 ≤ a →
      rawShare p.b (c*p.lambda0) (c*p.kappa) (c*p.mu) p.eta a = stationaryShare p a ∧
      ((c*p.lambda0)+(c*p.kappa)*effectiveEffort p a+c*p.mu) =
        c*(learningRate p a+p.mu)) ∧
    (1 < p.eta*p.b → ∀ a : ℝ, 0 < a → a < returnPoint p →
      let G := stationaryShare p a-stationaryShare p 0
      let Δ := effectiveEffort p a-p.b
      let gL := fun l : ℝ =>
        rawShare p.b l p.kappa p.mu p.eta a-rawShare p.b l p.kappa p.mu p.eta 0
      let gM := fun m : ℝ =>
        rawShare p.b p.lambda0 p.kappa m p.eta a-rawShare p.b p.lambda0 p.kappa m p.eta 0
      let gK := fun k : ℝ =>
        rawShare p.b p.lambda0 k p.mu p.eta a-rawShare p.b p.lambda0 k p.mu p.eta 0
      0 < Δ ∧ 0 < G ∧
      G = p.mu*p.kappa*Δ /
        ((p.lambda0+p.kappa*effectiveEffort p a+p.mu)*(p.lambda0+p.kappa*p.b+p.mu)) ∧
      DifferentiableAt ℝ gL p.lambda0 ∧ deriv gL p.lambda0 < 0 ∧
      StrictAntiOn gL (Ioi (0 : ℝ)) ∧
      DifferentiableAt ℝ gM p.mu ∧
      sameSign (deriv gM p.mu)
        ((p.lambda0+p.kappa*effectiveEffort p a)*(p.lambda0+p.kappa*p.b)-p.mu^2) ∧
      DifferentiableAt ℝ gK p.kappa ∧
      sameSign (deriv gK p.kappa)
        ((p.lambda0+p.mu)^2-p.kappa^2*effectiveEffort p a*p.b))

end
end Grados26Learning
