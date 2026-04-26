# Promotion notes (orchestrator)

## State

| File                    | Axioms |
|-------------------------|-------:|
| Basic.lean              |      0 |
| Bump.lean               |      0 |
| Potential.lean          |      0 |
| Normalization.lean      |      8 |
| TestFunction.lean       |     11 |
| OneDimensional.lean     |      6 |
| HigherDimensional.lean  |      6 |
| **Total**               | **31** |

`lake build L2Counterexample` succeeds. Zero `sorry` remaining.

## Cumulative axiom history

```
61  → initial
35  → previous round (measurability, rho_S as withDensity, MemLp.mul',
                       Z_S_pos, integrals via Gamma, q_S_abs_le_two,
                       HigherDim aliasing, etc.)
31  → this round (t_S_asymp, q_S_asymp, one_div_tildeS_asymp,
                   exp_neg_phi_boundary_asymp)
```

## Axioms discharged in this round

* `Normalization.t_S_asymp` proved by:
  - bounding `∫_{T_S} exp(−φ_S) ≤ vol(T_S) ≤ 4·ε_S = 4·S^{−3}` (via
    `norm_setIntegral_le_of_norm_le_const` plus `measureReal_union_le`
    on the two `Icc` pieces);
  - using `Z_S ≥ 1` eventually (`exists_S_Z_S_ge_one`).
* `Normalization.q_S_asymp` proved by the algebraic identity
  `q_S − (1/S − 1/S²) = −((1/S − 1/S²)·Z_S − 2·tailInt_S) / Z_S`
  combined with the BigOInv bounds on `Z_S − (2 + 2/S)` and
  `tailInt_S − 1/S`.
* `Normalization.one_div_tildeS_asymp` proved by
  `|1/tildeS − 1/S| = (tildeS − S)/(S·tildeS) ≤ (2·η_S)/S² = 2·S^{−6}`.
* `Normalization.exp_neg_phi_boundary_asymp` proved by
  `|exp(−φ_S(1+ε_S)) − 1| = 1 − exp(−φ_S(1+ε_S)) ≤ φ_S(1+ε_S) ≤ C·S^{−2}`.

To preserve the topological order required by Lean (definitions before
uses), `q_S_asymp` and `t_S_asymp` are placed at the end of
`Normalization.lean` (after `exists_S_Z_S_ge_one`), and
`exists_S_q_S_lt_one` is moved after `q_S_asymp`.

## What remains as axioms (31)

The remaining 31 axioms encode genuinely deep analytic facts. In rough
order of difficulty:

### Tractable in further rounds (with ~50–150 lines each)

* `tail_gaussian_bound` — sketched in comments; uses the proven
  `integral_exp_neg_Ici`, `integral_sq_exp_neg_Ici`,
  `one_sub_exp_neg_le`, plus integration monotonicity.
* `Var_phi_g_S_expansion` — derivable from `Var_phi_g_S_isBigO` and
  `q_S_isBigO` via algebraic expansion of `q(1−q)`. Three attempts
  in this round failed at the level of Lean's `Asymptotics.IsBigO`
  bookkeeping; the math is correct but the proof is extremely
  tedious without dedicated tactics.
* `g_S_continuous` — piecewise gluing argument; uses
  `Continuous.piecewise` from Mathlib.

### Less tractable

* The remaining `Normalization` axioms (`tailInt_S_tail_eq`,
  `tailInt_S_asymp`, `Z_S_asymp`, `phi_S_tail`, `phi_S_boundary_small`,
  `phi_S_layer_small`, `exp_negPhiS_integrable`) — encode the change-
  of-variables and asymptotic bookkeeping of section 3 of the paper.
  Each requires substantive measure-theory / real-analysis Lean code.
* `TestFunction` axioms `A_S_symm, A_S_asymp, hasDerivAt_g_S_layer_*,
  layerLebesgueEnergyPos/Neg_eq, E_phi_g_S_eq,
  integral_g_S_eq_q_plus_error, integral_g_S_sq_eq_q_plus_error` —
  encode the test-function calculations of section 4.
* `OneDimensional.{rho_S_isProb, rho_S_reflection_invariant,
  phiDer_S_memL2, g_S_memL2, EE_phi_S_asymp, Var_f_S_asymp}` —
  measure-theoretic and L²-membership facts (the first two have
  proofs sketched in this file's comments).
* `HigherDimensional.{stdGaussian, stdGaussian_isProb,
  stdGaussian_first_moment, integral_prod_first_coord,
  integral_prod_separable, prodSpace_iso_euclidean}` — Mathlib has
  the underlying tools (`gaussianReal`, `Measure.pi`,
  `MeasureTheory.integral_prod`) but lifting them to this file's
  forms requires careful integrability hypotheses.

## Naming canon

(Unchanged; reproduced for completeness.)

| Concept                        | Canonical name      | Defined in           |
|--------------------------------|---------------------|----------------------|
| Smooth bump                    | `kappa`             | `Bump.lean`          |
| ε, η parameters                | `eps_S, eta_S`      | `Potential.lean`     |
| Potential, derivatives         | `phi_S, phiDer_S, phiDer2_S` | `Potential.lean` |
| Evenness / oddness             | `phi_S_even, phiDer_S_odd, phiDer2_S_even` | `Potential.lean` |
| Quadratic lower bound          | `phi_S_quadratic_lower` | `Potential.lean` |
| Core formula                   | `phi_S_core`        | `Potential.lean`     |
| Partition function             | `Z_S`               | `Normalization.lean` |
| Right-tail integral            | `tailInt_S`         | `Normalization.lean` |
| Layer normalizer (blueprint A) | `A_S`               | `TestFunction.lean`  |
| Tail / layer masses            | `q_S, t_S`          | `Normalization.lean` |
| Probability measure            | `rho_S`             | `TestFunction.lean`  |
| Test function stack            | `g_S, ff_S, cc_S`   | TF / OneDim          |
| Functionals                    | `EE_phi_S, Var_f_S, delta_phi_S` | `OneDimensional.lean` |

## WIP files

Each `WIP_*.lean` is identical to its canonical counterpart. Future
agents edit the WIP files; the orchestrator promotes by `cp` and
re-runs `lake build`.
