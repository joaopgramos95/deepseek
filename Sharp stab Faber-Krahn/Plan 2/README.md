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
- `weighted-serrin-collar-reduction.md/.tex/.pdf`: reduces the weighted
  Serrin input in selected collars to a conditional Bernoulli/tame-expansion
  step and identifies boundary deficit propagation as the tempting but
  too-strong target; the currently justified closure still goes through BDV's
  nearly spherical expansion.
- `PLAN2_AGENT_REPORT.md`: local report of the latest Plan 2 worker pass.

Current focus:

1. Prove a valid boundary-gradient/tame expansion for the conditional Bernoulli
   spectral route, or use BDV's nearly spherical second variation for closure.
   The earlier boundary-deficit propagation target
   \(D_I(0)+D_H(0)\lesssim E(U)-E(B)\) is too strong on the full nearly
   spherical class and is not currently proved on the selected class.
2. Use the profile-gap lemma to choose near-boundary superlevel sets.
3. Prove the finite-perimeter form of the level-set deficit identity.
4. Test whether a GGRT-style second variation can be computed in a harmonic or
   holomorphic native space after BDV selection.

Cross-reference:

- The BDV paper is stored in `../Plan 1/1306.0392v1.pdf`.
- Plan 1's selection map may be needed as a regularization step for this route.
