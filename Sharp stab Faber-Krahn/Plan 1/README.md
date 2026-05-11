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
  strong and isolates a conditional spectral closure using the selected
  Bernoulli law.
- `bernoulli-expansion-proofs.md/.tex/.pdf`: corrected status note for the
  Bernoulli spectral route. It records why the previous exterior-harmonic
  Schauder proof was invalid, gives the correct fixed-domain formulation, and
  states the conditional spectral closure that would follow from the missing
  tame \(C^{2,\gamma}\times L^2\) boundary-gradient remainder.
- `faber-krahn-transfer.md/.tex/.pdf`: applies the Kohler--Jobin inequality
  to convert the sharp Saint--Venant stability into sharp Faber--Krahn
  stability \(\lambda_1(\Omega)-\lambda_1(B^*)\ge c_{\rm FK}(N,R)\mathcal A(\Omega)^2\),
  matching BDV's Theorem 1.1. Tracks the dependence of \(c_{\rm FK}\) on the
  selection, graph-entry, and spectral-closure constants.
- `fixed-domain-bernoulli-expansion.md/.tex/.pdf`: closes the gap. Proves the
  Bernoulli expansion entirely on \(B_1\) by applying the implicit function
  theorem to the pulled-back torsion equation. The first variation
  \(\widetilde u'(g)(x)=u_1(x)-\chi(r)rg(\theta)/N\) is constructed on
  \(\overline{B_1}\) (no exterior harmonic continuation needed). The IFT
  gives the \(C^{2,\gamma}\)-quadratic Schauder remainder, and a bilinear
  analysis gives the \(C^{2,\gamma}\times H^1\to L^2\) tame remainder. The
  \(L^2\)-tame form is not required because \(\mathcal L=k-1\) on
  \(\{k\ge2\}\) gains a full derivative
  \(\norm{\mathcal Lh}_{L^2}\gtrsim\norm{h}_{H^1}\). This makes the
  conditional closure unconditional in the smallness regime.
- `implementation-summary.md/.tex/.pdf`: earlier cross-route summary; retained
  here because the main BDV source paper is in this folder.
- `PLAN1_AGENT_REPORT.md`: current Plan 1 work report and next theorem target.

Current focus:

1. Preserve the deficit-to-\(\alpha\) ratio under a single-set penalized
   selection map.
2. Use the graph-entry threshold to enter the global near-spherical regime.
3. Close by the Bernoulli spectral closure, now proved unconditionally in
   `fixed-domain-bernoulli-expansion.md`. BDV's nearly spherical second
   variation remains available as a backup but is no longer required.

The full chain
selection \(\to\) graph entry \(\to\) Bernoulli spectral closure
is now end-to-end and rigorous. Open items are bookkeeping:
\(\sigma_*,\delta_*,q_*\) constant tracking and the explicit Schauder
bootstrap in graph entry.

Cross-reference:

- Plan 2 may still use the BDV selection step as a regularization device.
