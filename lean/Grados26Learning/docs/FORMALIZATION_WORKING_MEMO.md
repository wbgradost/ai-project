# Working memo: source clarifications and proof boundaries

This is a lead log for proof construction and closeout, not semantic evidence.

## Source authority

The controlling source is the author's PDF at ai-project commit
`7cc3a7406e09ba1544ff6997d5d742430c6c771c`, SHA-256
`906bd22a86a5be8a5ed292ab0a01192eed5b0123b517f58af98d6db94b090a02`.
The user explicitly selects the folder name `Grados26Learning`, replacing the
older operational folder suggestion in the manuscript appendix. This changes
no mathematical statement.

## Clarifications retained from the printed source

- Proposition 2, page 5: the factor-sign equality and strict-reverse
  equivalences follow the clause v<=b. The subsequent mixed and plateau cases
  cover the remaining domain. State this scope explicitly in Lean.
- Lemma 1, page 3: preserve the greatest-effort selection under weak concavity;
  proving uniqueness through an added strict-concavity assumption is not faithful.
- Lemma 2, pages 3-4: generator, transition probability and random occupation
  must be connected. The appendix explicitly warns against reporting only
  an ODE/integral check as the full Markov-chain theorem.
- Proposition 1, pages 4-5: the three assistance thresholds are distinct and
  the cutoff is a kink. Active-branch strict concavity is not global concavity.

No mathematical source error has been identified by the source-only audit.
No additional economic assumption has been approved.

## Intake/tooling observations

- The exact Poppler layout text has embedded-font ligature controls. Definition
  1 is visibly present in the PDF but its extracted heading is not recognized
  by the mechanical named-result floor. Keep the definition in scope.
- The mechanical floor detects a wrapped baseline Proposition 3.5 citation
  and the appendix's five operational target-table rows as apparent theorem
  headings. Reconcile these source-grammar observations honestly; they are not
  new mathematical assertions in the author's five-result manuscript.
- The official new facade initially required PYTHONPATH set to the repository
  root. A cold Lean scaffold validation timed out; the same official command
  completed after bounded startup diagnosis, with LEAN_NUM_THREADS=1. The
  library scripts were not bypassed or patched and the source was not changed.

The complete authentic setup logs remain in the external source/intake cache.
These observations grant no source-to-Lean match or proof status. At closeout,
verify all surviving mathematical notes against the source and actual checked
Lean declarations before using them in the validation report.
