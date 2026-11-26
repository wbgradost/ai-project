# Grados26Learning

Source manuscript [pinned at 3f8749bfbb5ee2c3d1eefa646724fb6c043018cf](https://github.com/wbgradost/ai-project/blob/3f8749bfbb5ee2c3d1eefa646724fb6c043018cf/paper/paper.pdf).

| Manuscript result | Lean declaration | File |
|---|---|---|
| Lemma 1 | `Grados26Learning.lemma1` | [WorkerResult.lean](WorkerResult.lean) |
| Lemma 2 | `Grados26Learning.lemma2` | [CTMCResult.lean](CTMCResult.lean) |
| Proposition 1 | `Grados26Learning.proposition1` | [ShapeResult.lean](ShapeResult.lean) |
| Proposition 2 | `Grados26Learning.proposition2` | [ComparisonResult.lean](ComparisonResult.lean) |
| Corollary 1 | `Grados26Learning.corollary1` | [SensitivityResult.lean](SensitivityResult.lean) |

The numbered declarations are exported by `ProofInterface.lean`.
`DeterministicInterface.lean` contains the four deterministic statements.
`PaperInterface.lean` adds the statement of the Markov result and exports all five.

[Course paper-scoped check](paper-scoped-check.txt) exited with status 0.
The [declaration and axiom audit](proof-kernel-check.txt) exited with status 0.
The check transcript records the local Lean driver compatibility adjustment.
The [upstream run](paper-scoped-check-upstream.txt) built the paper interface and timed out in the dependency reader.
The `docs/` and `audit/` directories include records from the earlier intake campaign.
