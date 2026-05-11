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
- `fixed-domain-bernoulli-expansion.md/.tex/.pdf`: proposed closure of the
  spectral route, working entirely on \(B_1\) via the implicit function
  theorem applied to the pulled-back torsion equation. The first variation
  \(\widetilde u'(g)(x)=u_1(x)-\chi(r)rg(\theta)/N\) is constructed on
  \(\overline{B_1}\) (no exterior harmonic continuation needed). The IFT
  gives a \(C^{2,\gamma}\)-quadratic Schauder remainder, and a bilinear
  analysis gives a \(C^{2,\gamma}\times H^1\to L^2\) remainder. This is
  enough for the spectral closure because \(\mathcal L=k-1\) on
  \(\{k\ge2\}\) gains a full derivative
  \(\norm{\mathcal Lh}_{L^2}\gtrsim\norm{h}_{H^1}\). **Conditional**: the
  bilinear source enumeration is partial (see `corrections-response.md`).
- `corrections-needed.md`: audit of overclaims in the above notes.
- `corrections-response.md/.tex/.pdf`: point-by-point response to the
  audit. Writes out the volume-normalized Bernoulli law, the
  \(C^{1,\gamma}\to C^{2,\gamma}\) Schauder bootstrap, and the
  second-variation source enumeration for $S_1, S_2$. Acknowledges the
  remaining gap (explicit constants).
- `implementation-summary.md/.tex/.pdf`: earlier cross-route summary; retained
  here because the main BDV source paper is in this folder.
- `PLAN1_AGENT_REPORT.md`: current Plan 1 work report and next theorem target.

Current status:

1. **Selection principle (rigorous):** preserves the deficit-to-\(\alpha\)
   ratio under a single-set penalized selection map.
2. **Graph entry (rigorous):** below an explicit asymmetry threshold the
   selected minimizer is a \(C^{1,\gamma}\) graph; the bootstrap to
   \(C^{2,\gamma}\) is now written out in `corrections-response.md`.
3. **Final closure:** two routes available.
   - **Route A (unconditional):** BDV's nearly spherical second variation.
   - **Route B (conditional):** Bernoulli spectral closure, conditional on
     the explicit constants in the bilinear source enumeration of
     `corrections-response.md`, §3.
4. **Kohler--Jobin transfer (rigorous):** converts Saint--Venant stability
   into sharp Faber--Krahn stability; works equally well for either
   Route A or Route B.

The reliable end-to-end route is selection \(\to\) graph entry \(\to\)
BDV nearly spherical second variation \(\to\) Kohler--Jobin. The Bernoulli
spectral closure is a promising alternative that avoids the second variation
but requires finishing the source-term constants.

Cross-reference:

- Plan 2 may still use the BDV selection step as a regularization device.
