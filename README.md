# AI-Assisted Learning and the Reversal of Long-Run Skill Degradation

**William Grados · Artificial Intelligence and Economic Modeling · UP 2026-II**

Can AI assistance improve stationary skill while displacing human effort?
This Track A paper extends Proposition 3.5 of Aouad, Lykouris, and Zhong's
[May 2026 working paper](https://arxiv.org/html/2605.11350v1#S3.SS3).

The worker maximizes current utility `p(s + e + a) − γe` over `e ≥ 0`,
with `γ > 0`, nondecreasing continuously differentiable concave production,
and `limsup p(x)/x < γ`. The largest-maximizer rule yields
`e*(s,a) = max(x* − s − a, 0)`. At fixed `a ≥ 0` and in two states
`0 ≤ s_L < s_H`, define `b = x* − s_L > 0`. Learning from `L` is
`λ_L(a) = λ₀ + κ e*(s_L,a)(1 + ηa)`, with `λ₀, κ, μ > 0` and
`η ≥ 0`; depreciation from `H` occurs at rate `μ`. The unique stationary
high-skill share is `π_H(a) = λ_L(a)/(λ_L(a) + μ)`.

- If `ηb ≤ 1`, the share strictly decreases to the cutoff `b` and stays
  constant thereafter. The unique maximum is at zero assistance.
- If `ηb > 1`, the share rises to its unique maximum `a* = (b − 1/η)/2`,
  declines to `b`, and stays constant thereafter. It exceeds the no-AI
  share exactly on `0 < a < a_R = 2a*`.
- For `0 ≤ u < v ≤ b`, the stationary comparison has the sign of
  `η(b − u − v) − 1`. A mixed active/saturated pair strictly loses skill.
  Two saturated levels give equal shares.
- Rate changes affect levels and gains. Common positive rescaling preserves
  the stationary curve and rescales convergence speed.

Run the single verification entry point from the repository root:

```bash
python -m pip install -r code/requirements.txt
python code/verify.py
```

[Verification methods and outputs](code/README.md) cover all five results,
regenerate the figures and document inputs, and compare simulated
continuous-time occupation to exact finite-horizon expectations.

| Component | Status |
|---|---|
| [Mathematical manuscript](paper/paper.pdf) | Five analytic proofs and computational checks. Use a commit-pinned copy of this PDF for the next Lean run. |
| [Proposal](proposal/proposal.pdf) and [topic slides](slides/topic.pdf) | Preserved from the topic stage. |
| [Final slides](slides/final.pdf) | Preserved Spanish presentation with Lean and handwritten evidence. |
| [Lean](lean/README.md) | Compiled stationary-comparison evidence for the [previous pin](https://github.com/wbgradost/ai-project/blob/7cc3a7406e09ba1544ff6997d5d742430c6c771c/paper/paper.pdf). The complete paper-scoped check is open. |
| [Handwritten check](hand/derivacion_manuscrita.jpeg) | Original author derivation and counterexample. The full handwritten appendix is pending. |
| [Collaboration log](prompts.md) | Original exchanges, checks, verdicts and corrections. |

[Assignment requirements](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7)
