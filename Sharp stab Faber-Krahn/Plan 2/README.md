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
- `concrete-next-steps.md/.tex/.pdf`: current action list.
- `selected-boundary-layer-theorem.md/.tex/.pdf`: hybrid Plan 1/Plan 2
  implementation of the selected-minimizer boundary-layer strategy; proves the
  near-boundary good-level and transfer estimates and isolates the remaining
  weighted Serrin input.
- `weighted-serrin-collar-reduction.md/.tex/.pdf`: resolves the weighted
  Serrin input in selected collars and identifies boundary deficit propagation
  as the true sharpness bottleneck.
- `PLAN2_AGENT_REPORT.md`: local report of the latest Plan 2 worker pass.

Current focus:

1. ~~Prove boundary deficit propagation for selected minimizers in the graph
   regime: \(D_I(0)+D_H(0)\lesssim E(U)-E(B)\).~~  Resolved (in the smallness
   regime) by `../Plan 1/bernoulli-expansion-proofs.md`, Theorem 9.1: the
   selected Bernoulli law filters out high-frequency modes that block the
   inequality on the full nearly-spherical class.
2. Use the profile-gap lemma to choose near-boundary superlevel sets.
3. Prove the finite-perimeter form of the level-set deficit identity.
4. Test whether a GGRT-style second variation can be computed in a harmonic or
   holomorphic native space after BDV selection.

Cross-reference:

- The BDV paper is stored in `../Plan 1/1306.0392v1.pdf`.
- Plan 1's selection map may be needed as a regularization step for this route.
