# Final presentation: 30-minute speaking plan

The deck has 24 frames, including the cover. Allow approximately 30 minutes
of speaking and retain 15 minutes for discussion in the 45-minute slot.
The assigned session is Friday November 6, 07:30-08:15, Lima time.
Slides must be merged by Thursday November 5, 22:00 under Issue #7;
the present review PR intentionally remains unmerged.

| Frames | Minutes | Emphasis |
|---|---:|---|
| 1-3 | 3 | Question, exact conditional answer, departure from Proposition 3.5 |
| 4-6 | 4 | Original myopic choice, two-state generator, competing learning effects |
| 7-10 | 6 | Conditions, three comparisons, sign proof, pairwise factorization |
| 11-15 | 7 | Illustrative regimes, mechanism, bounded gain, threshold and rate sensitivity |
| 16-19 | 5 | Exact CTMC experiment, occupation error decomposition, results and limits |
| 20-23 | 3 | Proof status, authentic Lean evidence status, author's hand verification |
| 24 | 2 | Three concrete critique questions |

The main simulation distinction is between closed-form evaluations (frames
11-15) and simulated paths (frames 16-18). Show how identical effort
displacement produces different learning regimes. At the strong-regime peak,
skill rises by 1.923 percentage points while effort falls 25 percent.
The number is illustrative, not an empirical estimate or welfare optimum.

On the stochastic slide explain that intervals measure Monte Carlo error
across independent paths, and that starting in L creates finite-horizon bias.
Longer horizons reduce the theoretical bias and variance; an individual
realization's absolute error need not decrease monotonically.

## Evidence required before claiming the presentation is complete

- The official AppliedModelingLib run has not happened. After the author
  selects and merges a paper version, replace the evidence-status frame via
  `slides/lean-evidence.tex` with a real declaration, executed proof fragment,
  precise mapping to the numbered claim, pinned commit, and check result.
  The file should contain one complete Beamer frame; retain the existing
  Unicode mappings and add any symbols actually needed.
- The author must independently write, scan, and adjudicate the derivation
  in `hand/README.md`. The deck detects `hand/critical-check.pdf`; adjust its
  page and crop to make the actual factorization legible, then replace the
  instruction to explain the verdict with the author's real conclusion.
- The general claim chosen for challenge is a deliberately questioned
  overgeneralization. It is not represented as a quotation from a historical
  AI answer. The actual correction from this session is recorded in
  `prompts.md` separately.
- Recompile and visually inspect the changed slides after inserting either
  piece of authentic evidence. Do not present a status frame as completion
  of Issue #7's Lean or handwritten-evidence requirement.
