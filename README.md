# AI-Assisted Learning and the Reversal of Long-Run Skill Degradation

**William Grados · Artificial Intelligence and Economic Modeling · UP 2026-II**

Track A extension of Aouad, Lykouris, and Zhong (2026), Proposition 3.5,
reviewed [arXiv version 1](https://arxiv.org/html/2605.11350v1).

**Question.** Can assistance improve stationary skill while displacing human
effort? Keep the original myopic problem `max p(s+e+a) − gamma*e`, with
nonnegative effort, concave differentiable production, sublinear growth
relative to the effort cost, and the original largest-maximizer selection.
Then `e*(s,a) = max(x*−s−a,0)`. Only learning changes:
`lambda(e,a) = lambda0 + kappa*e*(1+eta*a)`.

**Result and conditions.** In two states `0 <= s_L < s_H`, assume
`b = x*−s_L > 0`, fixed assistance `a >= 0`, and
`lambda0, kappa, mu > 0`, `eta >= 0`. The unique stationary high-skill
share is `pi_H(a) = lambda_L(a)/(lambda_L(a)+mu)`.

- If `eta*b <= 1`, the share strictly decreases until `a=b`, then is constant.
- If `eta*b > 1`, it strictly increases until the unique maximum
  `a_peak = (b−1/eta)/2`, then decreases until `b`.
- It exceeds the no-AI share exactly for `0 < a < a_return = b−1/eta`;
  `a_return = 2*a_peak`. Effort vanishes at `b`; this is a kink.
- For `0 <= a_low < a_high < b`, higher assistance improves skill exactly
  when `eta*(b−a_low−a_high) > 1`. A local reversal does not rank every pair.

Threshold locations depend on `eta,b`, not on `lambda0,kappa,mu`.
Common scaling of all three rates leaves stationary shares unchanged and
speeds convergence. No welfare, productivity, empirical, or general
N-state conclusion is asserted. Learning complementarity itself is not
claimed as novel; the topic proposal preserves the comparison with Davies.

**Computational evidence.** Illustrative values `b=2`, `lambda0=.1`,
`kappa=.4`, `mu=.3`, with `eta=0,.25,1`, expose three regimes.
The strong case peaks at `a=.5`: skill rises from 75% to 76.9231%,
returns at `a=1`, and reaches the 25% zero-effort plateau at `a=2`.
Formula evaluations and CTMC simulations are reported separately.
The latter use 384 independent paths per scenario/assistance cell,
seed `20261104`, and horizons 25, 100, 400. At 400, the largest gap from
stationarity is 0.5223 percentage points; finite-horizon bias is measured
separately. These are model checks, not parameter estimates.

Run all checks and regenerate data, figures, and document numbers with:

```bash
python -m pip install -r code/requirements.txt
python code/verify.py
```

See [code/README.md](code/README.md) for units, error formulas, checks, and
output provenance. Generated figure PDFs and LaTeX tables are committed
because the unchanged official workflow compiles documents in a separate job.

| Component | Current state |
|---|---|
| Topic proposal and slides | Preserved from the merged topic stage |
| Mathematical manuscript | Five numbered results with analytic proofs; pinned at 7cc3a7406e09ba1544ff6997d5d742430c6c771c |
| Simulations and verification | Symbolic, numerical, and independent CTMC checks implemented |
| Final slides | [22 Spanish frames](slides/final.pdf), about 30 minutes; five simulation slides, authentic Lean proof and handwritten check |
| Lean | [Verified stationary-comparison module](lean/README.md); the five complete numbered results are not all certified |
| Handwritten appendix | [Original photograph](hand/derivacion_manuscrita.jpeg): baseline comparison, distinct thresholds and a counterexample |
| Collaboration log | Actual current prompt, responses, corrections, and decisions in prompts.md |

**Formalization target.** The manuscript remains fixed at
[7cc3a7406e09ba1544ff6997d5d742430c6c771c](https://github.com/wbgradost/ai-project/blob/7cc3a7406e09ba1544ff6997d5d742430c6c771c/paper/paper.pdf).
The presentation displays the authentic verified pairwise comparison; it does
not claim completion of all five results or a successful full paper-scoped check.
Changing a numbered claim after this pin requires repeating the formalization.

The [official schedule](https://github.com/alexanderquispe/AI-Econ-Modeling/blob/main/PRESENTATIONS.md)
assigns Friday November 6, 07:30–08:15 (Lima); the
[Issue #7](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7)
slide deadline is November 5, 22:00. PR #2 is the approved manuscript baseline
for the official formalization. The final paper is due November 26, 22:00.
