# Plan 1: Quantify the existing BDV proof

Goal: make the Brasco--De Philippis--Velichkov selection-principle proof of
sharp quantitative Faber--Krahn/Saint-Venant stability more explicit and
quantitative.

Main files:

- `plan1.md`: original route sketch.
- `1306.0392v1.pdf`: BDV paper.
- `quantitative-selection-principle.md/.tex/.pdf`: current single-set
  quantitative selection-principle formulation.
- `graph-entry-closure.md/.tex/.pdf`: deterministic graph-entry threshold and
  final selected-counterexample contradiction using the BDV nearly spherical
  theorem.
- `bernoulli-spectral-closure.md/.tex/.pdf`: hard analysis of the remaining
  boundary-deficit gap; shows the naive boundary-deficit propagation is too
  strong and replaces it by a spectral closure using the selected Bernoulli
  law.
- `bernoulli-expansion-proofs.md/.tex/.pdf`: full proofs of the
  Schauder/quadratic-remainder lemmas (Lemmas 5.1 and 5.2 of
  `bernoulli-spectral-closure.md`), the volume-normalization passage, the
  quantitative spectral closure theorem, the conditional sharp Saint--Venant
  stability theorem, and the *selected-class* boundary-deficit propagation
  theorem that resolves the Plan 2 paradox.
- `implementation-summary.md/.tex/.pdf`: earlier cross-route summary; retained
  here because the main BDV source paper is in this folder.
- `PLAN1_AGENT_REPORT.md`: current Plan 1 work report and next theorem target.

Current focus:

1. Preserve the deficit-to-\(\alpha\) ratio under a single-set penalized
   selection map.
2. Use the graph-entry threshold to enter the global near-spherical regime.
3. Close by the direct Bernoulli spectral closure (now proved in
   `bernoulli-expansion-proofs.md`); the BDV nearly spherical second variation
   is no longer needed.

The full chain
selection \(\to\) graph entry \(\to\) Bernoulli spectral closure
is now end-to-end and gives sharp Saint--Venant/Faber--Krahn stability for
small \(Q_\alpha\), as stated in `bernoulli-expansion-proofs.md`,
Theorem 8.1.

Cross-reference:

- Plan 2 may still use the BDV selection step as a regularization device.
