# Reproduce and check the two-state results

Use Python 3.12 and the three versioned dependencies in `requirements.txt`.
From the repository root:

```text
python -m pip install -r code/requirements.txt
python code/verify.py
```

The second command is the single execution point and works from any current
directory when called with the script's path. No downloads, estimated data,
or external services are used by the script. The official workflow is unchanged.

## Illustrative parameters

The worker's payoff is `A log(1+s+e+a) - gamma e`, with `A=4`, `gamma=1`,
`s_L=1`, and `s_H=3`. Thus `x*=3` and initial low-state effort `b=2`.
Rates per model-time unit are `lambda0=0.1`, `kappa=0.4`, and `mu=0.3`.
Complementarity `eta` is 0, 0.25, or 1; the corresponding `eta*b` values
are 0, 0.5, and 2. These values deliberately separate qualitative regimes.
Skill, effort and assistance use the same units; `eta` has inverse-assistance
units, and `kappa` has rate-per-effort units. There is no calibration claim.

## Checks that fail on a discrepancy

- SymPy checks effort's first-order condition, stationary flow, the forward
  equation, derivative/curvature identities, the baseline and pairwise
  comparisons, threshold derivatives, rate effects on levels and gains,
  and the exact occupation mean and second moment.
- An independent grid maximization checks the worker's effort at interior
  and corner choices. Three hundred seeded random parameter cases check
  stationary balance, finite-difference derivatives, global maxima,
  comparisons, thresholds and invariance to the three rate parameters.
- Explicit boundary checks cover `eta=0`, `eta*b=1`, `a=b`, and `a>b`.
  Common scaling of all rates preserves the full stationary curve and
  multiplies the speed of convergence. The critical pair `a=0.4,0.8`
  verifies that both levels can exceed no AI even while increasing AI lowers
  skill. This is a computational check, not a handwritten derivation.
- Exact CTMC occupation means are checked against the finite-horizon
  analytic mean using six *exact* Monte Carlo standard errors. This is a
  conservative stochastic diagnostic, not a mathematical guarantee or a
  proof of the economic proposition. There is no requirement that every
  nominal 95% interval contain its target.

## Stochastic design and error

Assistance remains fixed along each trajectory. Every trajectory starts in
state L; there is no burn-in. At each jump, holding time is drawn from an
exponential distribution with the current state's exit rate. Time in H is
integrated over the complete path, including its terminal partial holding
time. Counting visits at jump times would instead produce the alternating
chain's high-state frequency of one half and is inappropriate here.

There are 21 parameter cells: the three complementarity regimes at
`a=0,0.25,0.5,1,1.5,2,2.5`. Each has 384 independent trajectories.
NumPy `SeedSequence(20261104)` spawns one child per cell and then one child
per replication; independent PCG64 streams generate trajectories. The same
trajectory is observed at `T=25,100,400`, so observations across horizons
are dependent. They are never treated as independent replications.

At fixed assistance let `r=lambda_L+mu` and `pi=lambda_L/r`. The exact expected
occupation share starting L is `pi*[1-(1-exp(-r*T))/(r*T)]`, below stationarity
by `pi*(1-exp(-r*T))/(r*T)`. Thus the initial bias declines as `1/T`; the
state probability itself converges exponentially. The code derives and checks
the exact occupation variance by integrating the Markov joint probability.
Independent-replication SEM is sample standard deviation divided by
`sqrt(384)`. Error bars are approximate normal 95% intervals (`1.96*SEM`)
for the finite-horizon expectation, not confidence intervals for estimated
economic parameters. The validation gate uses `sqrt(exact variance/384)`.

## Outputs

All five PDF figure files and their numerical inputs are reproducible:

| Figure | Purpose | Data |
|---|---|---|
| `figures/mechanism.pdf` | Same effort displacement, three learning regimes | `output/comparative_statics.csv` |
| `figures/thresholds.pdf` | Local increase versus improvement over no AI | `output/scenarios.csv`, closed-form thresholds |
| `figures/sensitivity.pdf` | Rate magnitudes versus initial-effort thresholds | `output/sensitivity.csv` |
| `figures/rate_sensitivity.pdf` | Wide slide rendering of the same three rate panels | `output/sensitivity.csv` |
| `figures/ctmc.pdf` | Stationary predictions, sampling error and finite-horizon bias | `output/ctmc_summary.csv` |

`output/critical_pair.csv` records the hand-critical example.
`output/effort_check.csv` records the independent maximization checks.
`output/summary.json` records runtime versions, parameters, gates and aggregate results.
`output/results.tex` and the two table bodies are generated inputs for the
manuscript/slides. Generated PDFs and LaTeX numbers are committed because
the official PDF and Python jobs run independently.

These experiments test mathematical and implementation consistency. They
do not estimate complementarity, establish causality, prove the proposition,
identify welfare-optimal assistance, or justify a claim for N skill states.
