# AI-Assisted Learning and the Reversal of Long-Run Skill Degradation

**William Grados · Universidad del Pacífico · Artificial Intelligence and Economic Modeling · Track A**

**Question.** When can AI assistance raise long-run skill while displacing
human effort? The [paper](paper/paper.pdf) extends the stationary skill
ordering in Proposition 3.5 of [Aouad, Lykouris, and Zhong, arXiv v1, p. 8](https://arxiv.org/pdf/2605.11350v1), renumbered Proposition 3.3 in the October revision.

**Model.** A myopic worker chooses $e\ge0$ to maximize $p(s+e+a)-\gamma e$.
Under concavity, the growth condition and the greatest-maximizer rule,
effort is $e^*(s,a)=(x^*-s-a)^+$. At a fixed assistance level $a\ge0$,
skill moves between $0\le s_L<s_H$. The upward rate is
$\lambda_L(a)=\lambda_0+\kappa(b-a)^+(1+\eta a)$, where $b=x^*-s_L>0$,
$\lambda_0,\kappa,\mu>0$, and $\eta\ge0$. The downward rate is $\mu$.

**Result.** The unique stationary high-skill share is
$\pi_H(a)=\lambda_L(a)/(\lambda_L(a)+\mu)$.
If $\eta b\le1$, the share strictly decreases through $a=b$.
If $\eta b>1$, it rises to its unique maximum at $a^*=(b-1/\eta)/2$
and then decreases through $b$. It exceeds the no-AI share exactly on
$0<a<a_R=b-1/\eta$, with $a_R=2a^*$.
In both regimes it is constant at $\lambda_0/(\lambda_0+\mu)$ for $a\ge b$.
For $0\le u<v\le b$, the sign of the stationary difference is the sign
of $\eta(b-u-v)-1$. With two skill states, the high-skill share determines
the entire stochastic ordering. A move from active effort to saturation
strictly lowers the share. Common positive scaling of the three rate
parameters preserves the stationary curve and scales convergence speed.

**Reproduction.** Run from the repository root.

~~~bash
python -m pip install -r code/requirements.txt
python code/verify.py
~~~

The script checks all five numbered results and regenerates the paper's
figures and numerical inputs. [Computational details](code/README.md)

| Component | Status |
|---|---|
| Manuscript | [Source](paper/paper.tex), [PDF](paper/paper.pdf), [bibliography](paper/references.bib). Five complete proofs. The [Lean target](https://github.com/wbgradost/ai-project/blob/3f8749bfbb5ee2c3d1eefa646724fb6c043018cf/paper/paper.pdf) is pinned at `3f8749b`. |
| Proposal and presentations | [Proposal](proposal/proposal.pdf), [topic slides](slides/topic.pdf), [final slides](slides/final.pdf). |
| Lean | All five numbered results compile. The paper-scoped check returned 0 with a local reader import adjustment. The upstream run timed out in the dependency reader. See [Lean verification](lean/README.md). |
| Handwritten work | [Six author photographs and original counterexample](hand/README.md). Includes coverage and two review notes. |
| Collaboration log | [Prompts, answers, and verification record](prompts.md). |

[Course requirements in Issue #7](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7)
