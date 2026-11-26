# Formalization plan: Grados26Learning

This is the active source-first proof plan, not a validation certificate.

The selected source is William Grados's own unpublished manuscript, with no
arXiv record, pinned to ai-project commit
`7cc3a7406e09ba1544ff6997d5d742430c6c771c`. The controlling artifact is the
12-page `paper/paper.pdf` at that commit. Its SHA-256 is
`906bd22a86a5be8a5ed292ab0a01192eed5b0123b517f58af98d6db94b090a02`.
The existing Poppler layout extraction is reused. Ignored source companions
are byte-pinned in `paper_statement_map.json`; no new extraction or numerical
experiment is needed for the proof campaign.

## Selected mathematical surface

| Source presentation | PDF page | Role |
|---|---:|---|
| Assumption 1: worker problem and selection | 2 | Governing model/assumption |
| Assumption 2: states, learning, depreciation | 3 | Governing model/assumption |
| Definition 1: effective effort | 3 | Semantic prerequisite |
| Lemma 1 | 3 | Complete selected-effort result |
| Lemma 2 | 3 | Complete stationary/transient/occupation result |
| Proposition 1 | 4 | Complete global shape and threshold result |
| Proposition 2 | 5 | Complete arbitrary-pair and two-state order result |
| Corollary 1 | 6 | Complete sensitivity and rate-scaling result |

The five asserted results form the result denominator. The three governing
presentations are reviewed semantic prerequisites, not reflexive theorem rows.
All numbered statements retain every conclusion clause. Exogenous assistance,
production technology, skill states, and transition primitives remain fixed
when their source comparisons require them to be fixed.

## Current intake boundary

- [x] Exact PDF identity checked; cached canonical source text retained.
- [x] Full source-only reading identifies eight named presentations and nine
  support/deep-only candidates; the latter do not inflate the five-result scope.
- [x] Official `paper_contribution.py new` created the paper and Lake target.
  The documented empty-interface lane avoids generating proof placeholders.
- [ ] Reconcile the mechanical source floor with the PDF: the embedded-font
  ligature in Definition 1 is not recognized as a heading; a wrapped reference
  to the baseline Proposition 3.5 and the appendix target table are detected
  as apparent theorem presentations. These are source-grammar/intake issues,
  not permission to invent extra paper results or omit the actual definition.
- [ ] Bind complete source-only region/candidate/prose classifications through
  the official preparer.
- [ ] Complete source-facing Specs and actual consumed semantic prerequisites.
- [ ] Obtain the non-certifying architecture review, then the independent
  source-to-expanded-Spec judgments under the current v11 protocol.
- [ ] Freeze the exact source/statement surface before claiming closeout.

## Dependency-ordered proof obligations

| Order | Source result | Required complete content | Owner / implementation |
|---:|---|---|---|
| 1 | Lemma 1 | Existence and greatest maximizer; constrained largest selection; effort regimes and derivative | Worker agent, `Worker.lean` |
| 2 | Lemma 2 | Actual CTMC generator-to-transition law; unique invariant law; arbitrary initial probability; stochastic occupation expectation | Coordinator's stochastic proof module |
| 3 | Proposition 2 | General difference, all sign/equality regimes including v=b and the plateau; actual binary FOSD and mean skill | Coordinator's algebra/comparative-statistics modules |
| 4 | Proposition 1 | Continuity, right derivative at zero, both regimes, global unique maximum, no-AI comparison, tail, kink and curvature | Coordinator's global comparative-statistics modules |
| 5 | Corollary 1 | All threshold/level/gain derivatives with correct domains and signs; common rate scaling and speed | Coordinator's sensitivity module |

`Model.lean` owns the transparent reduced-form primitives. The selected worker
optimizer and the invariant skill law must be connected to those primitives
by proved bridges; a ratio definition alone does not establish its economic
stationary interpretation.

Reserved paper contracts are `lemma1Spec`, `lemma2Spec`, `proposition1Spec`,
`proposition2Spec`, and `corollary1Spec` in `PaperInterface.lean`. Their distinct
proof endpoints are respectively `lemma1`, `lemma2`, `proposition1`,
`proposition2`, and `corollary1`. All are in namespace `Grados26Learning`.

## Fidelity risks requiring actual proofs

1. Weak concavity does not imply optimizer uniqueness. Prove the original
   greatest-maximizer selection and its existence from the source growth bound.
2. Verifying a proposed ODE solution or deterministic integral is not the full
   Markov-chain lemma. Prove the stochastic transition and occupation bridges.
3. Derive eta positivity from eta*b>1 before using reciprocal eta; retain eta=0
   and eta*b=1 in the weak regime and right derivatives where required.
4. Distinguish the peak (b-1/eta)/2, no-AI return b-1/eta, and effort cutoff b.
5. The active pairwise factor-sign equivalences require v<=b; mixed and
   plateau cases have separate conclusions. Do not globalize the equality iff.
6. Gain derivatives compare two share levels. A larger level need not mean a
   larger gain. Kappa's share derivative is nonnegative, not globally strict.

No additional economic hypothesis is authorized. Any unresolved bridge or
necessary added premise must remain explicitly open and must not be counted
as complete formalization of the original numbered result.

## Verification and closeout

Run one focused Lean module check per coherent proof seam, with one Lake
build at a time and `LEAN_NUM_THREADS=1`. Retain successful source seams in
the persistent named worktree. Do not rerun complete simulations.

Once the source/model/Spec/proof surface is stable, follow the current
closeout planner and its required independent reviews. Run and retain the
authentic output of the user-required command from the AppliedModelingLib root:

```bash
python3 scripts/paper_contribution.py check Grados26Learning --fast
```

The paper-scoped check, the kernel-checked proof closure, and semantic source
fidelity are distinct evidence. Report their actual results separately. The
complete generated paper folder is to be copied to ai-project/lean under its
generated ignore rules, without forced staging. The pinned manuscript's
numbered results must not be changed; any such change requires a new source
commit and a repeated formalization.
