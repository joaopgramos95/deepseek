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
- `PLAN2_AGENT_REPORT.md`: local report of the latest Plan 2 worker pass.

Current focus:

1. Prove the finite-perimeter form of the level-set deficit identity.
2. Use the profile-gap lemma to choose near-boundary superlevel sets.
3. Import the STFT paper's "matched superlevel set then transfer back" strategy.
4. Test whether a GGRT-style second variation can be computed in a harmonic or
   holomorphic native space after BDV selection.

Cross-reference:

- The BDV paper is stored in `../Plan 1/1306.0392v1.pdf`.
- Plan 1's selection map may be needed as a regularization step for this route.
