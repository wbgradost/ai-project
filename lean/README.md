# Official formalization: not started

No Lean statement, proof fragment, or paper-scoped check has been executed for
this manuscript. The mathematical proofs in `paper/paper.tex` are ordinary
proofs; symbolic and numerical checks in `code/` are not Lean certificates.

The manuscript appendix lists every numbered result and its current status.
The principal targets are the global shape and baseline comparison
(Proposition 1), and the exact ordering of two assistance levels
(Proposition 2). Effort, stationarity, transient behavior, and sensitivity
results must also be covered. Definitions of the positive part, generator,
stationary law, and the selected optimizer must be faithful to the paper.

## Sequence required by Issue #7

1. Review this PR and the compiled manuscript. Decide which version to
   formalize. Merge that version into `main` **only after the author's approval**
   and record its full commit hash. The present branch has not been merged.
2. From the existing AppliedModelingLib clone, run `git pull`. Use its
   **paper-formalization skill**, instructions, and the configuration specified
   in Issue #7: `gpt-5.6-sol`, reasoning effort `xhigh`. Do not replace this
   process with a standalone Lean file in this repository.
3. Supply the actual pinned URL and commit, with this task:

   ```text
   Please formalize my own paper, an unpublished manuscript with no arXiv
   record: https://github.com/wbgradost/ai-project/blob/<commit>/paper/paper.pdf
   (pinned at commit <commit>), using the paper-formalization skill and
   workflow in this repository.
   Use Grados26AIAssistedLearning as the paper folder.
   ```

4. From the AppliedModelingLib root, run and retain the complete output of:

   ```bash
   python3 scripts/paper_contribution.py check Grados26AIAssistedLearning --fast
   ```

5. Copy the **entire** generated
   `papers/Grados26AIAssistedLearning/` folder, exactly as generated, to this
   repository's `lean/` directory. Replace this preparatory README at that
   point. Respect the generated `.gitignore`; use `git add lean/`, never
   `git add -f`.
6. Complete the paper's formalization table with real declaration names,
   files, the pinned paper commit, check output, and the verdict for **each**
   numbered result: proved exactly; proved under an explicitly stated added
   hypothesis; or open with the exact blocker. Check that no hypothesis
   assumes the conclusion and that there are no `sorry` gaps.
7. Put a real declaration and the relevant executed proof fragment on the
   Lean slide. `slides/final.tex` can include `slides/lean-evidence.tex` once
   that file contains authenticated evidence from this run. Include an
   explanation of the mapping and any extra hypothesis. Recompile and review.
8. If a numbered claim changes after formalization, rerun the official
   process for the new paper version. Carry changes through a PR.

The commit placeholder above is an instruction for the future run, not an
identified or already formalized version. The preparatory paper appendix
contains no invented Lean declarations.

Source: [Issue #7, section 6](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7).
