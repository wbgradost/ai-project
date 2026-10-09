# AI-Assisted Learning and the Reversal of Long-Run Skill Degradation

**Artificial Intelligence and Economic Modeling · Universidad del Pacífico · 2026-II**

**Track A:** extension of Aouad, Lykouris, and Zhong (2026), *Human-AI
Productivity Paradoxes: Modeling the Interplay of Skill, Effort, and AI
Assistance*.

## Question

Can AI assistance raise the long-run share of high-skill workers when it not
only substitutes for current effort, as in the baseline model, but also makes
the remaining effort more effective at producing skill?

## Model

A myopic worker with skill `s`, effort `e ≥ 0`, and AI assistance `a ≥ 0`
solves

```text
max_{e ≥ 0} p(s + e + a) − γe,
```

where `p` is increasing and concave and `γ > 0`. Let `x*` be the largest
maximizer of `p(x) − γx`. The worker's effort remains

```text
e*(s,a) = max{x* − s − a, 0}.
```

There are two skill states, `s_L < s_H`. The downward transition rate is
`μ > 0`; the proposed upward learning technology is

```text
λ(e,a) = λ_0 + κe(1 + ηa),
```

with `λ_0 > 0`, `κ > 0`, and `η ≥ 0`. Thus AI and effort are substitutes in
current production but complements in skill acquisition when `η > 0`.

## Candidate result, with conditions

Let `b = x* − s_L > 0`. The stationary high-skill share is

```text
π_H(a) = λ_L(a) / [λ_L(a) + μ],
λ_L(a) = λ_0 + κ(b − a)^+(1 + ηa).
```

For `0 ≤ a < b`,

```text
sign(dπ_H/da) = sign(η(b − 2a) − 1).
```

Hence the baseline skill-degradation result survives when `ηb ≤ 1`. If
`ηb > 1`, assistance initially raises the high-skill share until

```text
a† = (ηb − 1)/(2η),
```

then lowers it for `a† < a < b`; once `a ≥ b`, effort is zero and the share is
constant at `λ_0/(λ_0 + μ)`. For two active-effort levels
`0 ≤ a_l < a_h < b`, the exact reversal condition is

```text
π_H(a_h) > π_H(a_l)  iff  η(b − a_h − a_l) > 1.
```

This is a local, conditional reversal of Proposition 3.5, not a universal
claim that more AI always improves skill.

## Status

| Component | State |
|---|---|
| Topic document and slides | Drafted and locally compiled; pending instructor/student review |
| Final slides | Template placeholder; not yet developed |
| Paper | Template placeholder; not yet developed |
| Simulations (`python code/verify.py`) | Template check only; extension checks are planned |
| Lean | Not started; planned after the paper's proposition is fixed |
| Handwritten appendix | Not started; required for the final paper |

Repository: <https://github.com/wbgradost/ai-project>
