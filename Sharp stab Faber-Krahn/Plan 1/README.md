# Plan 1: Quantify the existing BDV proof

Goal: make the Brasco--De Philippis--Velichkov selection-principle proof of
sharp quantitative Faber--Krahn/Saint-Venant stability more explicit and
quantitative.

Main files:

- `plan1.md`: original route sketch.
- `1306.0392v1.pdf`: BDV paper.
- `quantitative-selection-principle.md/.tex/.pdf`: current single-set
  quantitative selection-principle formulation.
- `implementation-summary.md/.tex/.pdf`: earlier cross-route summary; retained
  here because the main BDV source paper is in this folder.
- `PLAN1_AGENT_REPORT.md`: current Plan 1 work report and next theorem target.

Current focus:

1. Preserve the deficit-to-\(\alpha\) ratio under a single-set penalized
   selection map.
2. Quantify the compactness/regularity step that turns a selected minimizer
   into a global near-spherical graph.
3. Track enough constants/dependencies to replace "for \(j\) large" by an
   explicit smallness condition.

Cross-reference:

- Plan 2 may still use the BDV selection step as a regularization device.
