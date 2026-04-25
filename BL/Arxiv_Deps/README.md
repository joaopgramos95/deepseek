# Arxiv dependency audit

This folder mirrors the mathematical structure of `Arxiv_Split` and lists
external results needed for an end-to-end Lean formalization.

The source chunk `sections/01_statement_and_spectral.tex` is intentionally
split into two audit files:

- `sections/01_statement_and_spectral_proof_relevant.md`
- `sections/01_statement_and_spectral_contextual.md`

This implements the requested split between statements used for the proof and
statements included for historical, explanatory, or completeness reasons.

Each audit file separates:

- **Common mathematics**: standard facts that may or may not already exist in
  Lean/mathlib in the exact required form.
- **Quoted results from other places**: claims imported from cited literature,
  with a reference and the precise form needed by this paper.

