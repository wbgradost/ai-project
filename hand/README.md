# Handwritten verification: pending author work

There is no handwritten evidence in this directory yet. No AI-generated
image, typed derivation, or symbolic check should be represented as the
author's handwritten verification.

## Priority derivation for the final presentation

Independently verify **Proposition 2**, then specialize to Proposition 1's
comparison with no AI. The claim to question is whether `eta*b > 1` alone
implies that every increase in positive assistance improves stationary skill.
It does not; this condition only creates an increasing region.

Use your own handwriting and check each step without copying the proof:

1. State `b > 0`, `lambda0 > 0`, `kappa > 0`, `mu > 0`, `eta >= 0`,
   and initially `0 <= a_low < a_high < b`. Define the two upward rates.
2. Subtract `lambda_high/(lambda_high+mu)` and
   `lambda_low/(lambda_low+mu)`. Show the denominator is positive before
   inferring a sign. Name the common-denominator rule.
3. Expand and factor the difference in learning terms. Obtain
   `(a_high-a_low) * [eta*(b-a_high-a_low)-1]` and identify every positive
   factor. This is the exact condition for the two-level comparison.
4. Set `a_low=0`, factor the difference against no AI, and derive the
   return threshold `a_return=b-1/eta` when `eta*b>1`. Handle `eta=0`
   separately rather than dividing by zero.
5. Independently differentiate the stationary ratio using the quotient and
   chain rules. Derive `a_peak=(b-1/eta)/2`, hence `a_return=2*a_peak`.
6. Check the zero-derivative case `eta*b=1`, the kink at `a=b`, and
   comparisons with one or both assistance levels at or above `b`.
7. Give a counterexample with `b=2`, `eta=1`, `a_low=0.4`,
   `a_high=0.8`: learning factors are `2.24` and `2.16`, both above
   the no-AI factor `2`, yet the higher assistance level reduces skill.
8. Write your verdict in your own words and date the pages. Explain the
   distinction between a local increase, a gain over no AI, and a gain
   between two positive assistance levels.

Save a legible scan or photo sequence here. A single PDF named
`critical-check.pdf` is included automatically on the designated slide;
select a legible page containing the essential factorization and verdict,
and keep the full derivation in this directory. If necessary, adjust the
slide's page selection and layout to display the actual evidence clearly.
The slide must still explain the verdict orally; inserting a scan is not
enough. Do not claim completion until the author actually supplies it.

For the final paper, the official handwritten appendix must additionally
cover **every** derivation, step by step, with conditions and rules checked
where they are used. The list above prioritizes the presentation and does
not waive that broader requirement.
