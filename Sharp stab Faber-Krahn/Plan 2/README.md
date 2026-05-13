# Plan 2: Quantify the Nicola--Tilli inspired proof

Goal: use the Nicola--Tilli level-set/convexity proof, together with the new
STFT stability paper, to seek a genuinely quantitative route to sharp
Faber--Krahn/Saint-Venant stability.

Main files:

- `plan2.md`: original route sketch, now updated with the STFT stability input.
- `faber-krahn-1.pdf`: short torsion/Faber--Krahn note using the
  Nicola--Tilli style convexity proof.
- `s00222-024-01248-2-3.pdf`: Gómez--Guerra--Ramos--Tilli stability paper for
  the STFT Faber--Krahn theorem.
- `level-set-deficit-identity.md/.tex/.pdf`: exact weighted level-set deficit
  identity and profile-gap lemma.
- `nicola-tilli-stability-import.md/.tex/.pdf`: translation of STFT stability
  ideas into the torsion setting.
- `analytic-native-route.md/.tex/.pdf`: harmonic/holomorphic native-space route.
- `global-foliation-trace.md/.tex`: sharp Plan 2 branch using the whole outer
  level-set foliation. It replaces the one-level boundary slab by a fixed
  annular trace estimate in which \(D_H\) supplies radial kinetic energy and
  \(D_I\) supplies angular coercivity.
- `fvht-center-gluing-import.md`: import from Figalli--van Hintum--Tiba
  `2501.04656v1.pdf`; records the overlap/gluing mechanism that prevents
  level-wise centers from drifting and reformulates the outer foliation entry
  lemma in a metric center-quotient form.
- `outer-foliation-entry-proof-attempt.md`: current attempt at the full sharp
  Plan 2 theorem. It introduces the sharp cutoff
  \(\rho_\delta=1-\kappa\sqrt{\delta_T}\), proves the smooth coherent-foliation
  theorem, imports FvHT center gluing, and isolates the remaining
  finite-perimeter velocity-to-metric-derivative lemma.
- `metric-finite-perimeter-closure.md`: no-graph version of the closure. It
  works directly with the metric quotient of finite-perimeter level sets by
  translations, derives the \(D_H\) velocity estimate intrinsically, uses a
  strong isoperimetric oscillation-index input for the homothetic velocity
  defect, and proves sharp Saint--Venant stability in the bounded class modulo
  those standard GMT inputs.
- `gmt-inputs-for-metric-closure.md`: expands the two GMT inputs in the metric
  closure: homothetic velocity defect from strong isoperimetry and the
  finite-perimeter \(L^1\)-metric first variation estimate.
- `claude-agent-deployment.md`: task brief for deploying external agents on
  the remaining Plan 2 checks, with separate assignments for the level-set
  identity, strong isoperimetry input, metric first variation, weighted trace,
  bounded assembly, and adversarial audit.
- `concrete-next-steps.md/.tex/.pdf`: current action list.
- `selected-boundary-layer-theorem.md/.tex/.pdf`: hybrid Plan 1/Plan 2
  implementation of the selected-minimizer boundary-layer strategy; proves the
  near-boundary good-level and transfer estimates and isolates the remaining
  weighted Serrin input.
- `weighted-serrin-collar-reduction.md/.tex/.pdf`: reduces the weighted
  Serrin input in selected collars to a conditional Bernoulli/tame-expansion
  step and identifies boundary deficit propagation as the tempting but
  too-strong target; the currently justified closure still goes through BDV's
  nearly spherical expansion.
- `PLAN2_AGENT_REPORT.md`: local report of the latest Plan 2 worker pass.

Current focus:

1. Prove the global foliation coercivity estimates in
   `global-foliation-trace.md`: \(D_I\) controls the angular non-neutral modes,
   \(D_H\) controls the radial derivative of those modes, and the fixed-annulus
   trace recovers \(\mathcal A(\Omega)^2\) without the \(\eta\)-loss.
2. Prove the outer foliation entry lemma using the FvHT center-gluing mechanism:
   first glue block centers by overlap, then use the \(D_H\) velocity defect to
   control the metric derivative of the level-set curve modulo translations.
3. Prove the finite-perimeter velocity-to-metric-derivative lemma in
   `outer-foliation-entry-proof-attempt.md`, using the strong
   Fusco--Maggi--Pratelli/Fusco--Julin oscillation-index form of quantitative
   isoperimetry for \(D_I\) and the Cauchy velocity identity for \(D_H\). This
   is now the narrow replacement for the selection principle.
4. Turn `gmt-inputs-for-metric-closure.md` into a citation-ready theorem by
   pinning down the exact FMP/Fusco--Julin oscillation-index statement and the
   BV/coarea approximation reference.
5. Prove the finite-perimeter form of the level-set deficit identity.
6. Keep the selected-minimizer boundary-layer and analytic/native-space routes
   as backups or local models for the quadratic expansions.

Cross-reference:

- The BDV paper is stored in `../Plan 1/1306.0392v1.pdf`.
- Plan 1's selection map may be needed as a regularization step for this route.
