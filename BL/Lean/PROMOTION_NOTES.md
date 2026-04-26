# Promotion notes (orchestrator)

## State

| File                    | Axioms |
|-------------------------|-------:|
| Basic.lean              |      0 |
| Bump.lean               |      0 |
| Potential.lean          |      0 |
| Normalization.lean      |      1 |
| TestFunction.lean       |      0 |
| OneDimensional.lean     |      4 |
| HigherDimensional.lean  |      0 |
| **Total**               | **5**  |

(Earlier counts in this file undercounted HigherDimensional by 1: the
`@[instance] axiom stdGaussian_isProb` doesn't start with `axiom`, so
the simple grep pattern `^axiom` missed it.)

Remaining 5 axioms by category:
* **Normalization (1)**: `Z_S_asymp` — `Z_S = 2 + 2/S + O(S^{-3})`.
  Requires partitioning `∫ exp(-φ_S)` over core/layer/tail and bounding
  each piece via `phi_S_quadratic_lower`, `phi_S_layer_small`,
  `phi_S_le_of_le`, plus the proven `tailInt_S_asymp`.
* **OneDimensional (4)**: `rho_S_isProb`, `rho_S_reflection_invariant`,
  `phiDer_S_memL2`, `g_S_memL2` — unconditional forms; the conditional
  `0 < S` versions are derivable, but call sites use these as instances
  without `0 < S` available. (Note: `rho_S_isProb` is technically false
  at `S = 0` since `rho_S 0` is the zero measure.)

`lake build L2Counterexample` succeeds. Zero `sorry` remaining.

## Cumulative axiom history

```
61  → initial
35  → previous round (measurability, rho_S as withDensity, MemLp.mul',
                       Z_S_pos, integrals via Gamma, q_S_abs_le_two,
                       HigherDim aliasing, etc.)
31  → previous round (t_S_asymp, q_S_asymp, one_div_tildeS_asymp,
                       exp_neg_phi_boundary_asymp)
30  → g_S_continuous (FTC for primitives + Continuous.if_le)
23  → previous round (hasDerivAt_g_S_layer_pos, hasDerivAt_g_S_layer_neg,
                       A_S_symm, layerLebesgueEnergyPos_eq,
                       layerLebesgueEnergyNeg_eq, E_phi_g_S_eq)
21  → integral_g_S_eq_q_plus_error, integral_g_S_sq_eq_q_plus_error
       (rho_S/volume conversion + partition of ℝ + tail symmetry)
20  → Var_phi_g_S_expansion (algebraic q(1−q) expansion + IsBigO algebra)
19  → Var_f_S_asymp (Var_f_S = Var_phi g_S via probability-measure
       linearity; bridge IsBigO → BigOInv1D)
18  → tail_gaussian_bound (1 - exp(-v) ≤ v with v = η u²/2;
       integrate ∫ exp(-S̃u) · η u²/2 = η/S̃³ via Gamma-function helper)
17  → tailInt_S_asymp (decompose tailInt_S = A · I, then bound
       (A−1)·I, I − 1/S̃, 1/S̃ − 1/S each by const/S³ for S ≥ 1)
16  → EE_phi_S_asymp (via E_phi_g_S_eq + Z_S_asymp + A_S_asymp
       + S²·Z_S·A_S ≥ S³/2 from `exists_S_Z_S_ge_one` and
       √(2·C_A) bound on A_S ≥ S/2)
15  → A_S_asymp (TestFunction now axiom-free): split A_S =
       (S + 2·η·ε) + R via integral_phiDer2_S_layer; bound R
       using phi_S_layer_small + exp/inv conversion
14  → phi_S_layer_small (from phi_S_boundary_small + monotonicity
       of phi_S on [0,∞))
13  → exp_negPhiS_integrable (Gaussian domination via
       phi_S_quadratic_lower + integrable_exp_neg_mul_sq)
13  → tailInt_S_tail_eq (change of variables u = x - (1+ε) plus
       `phi_S_tail` and pull constant out)
10  → stdGaussian + stdGaussian_isProb + stdGaussian_first_moment via
       Mathlib's `Measure.pi (gaussianReal 0 1)` plus
       `measurePreserving_eval` and `integral_id_gaussianReal`
9   → prodSpace_iso_euclidean removed (was unused; false for d ≥ 2
       because Prod uses sup-norm and EuclideanSpace uses ℓ² norm)
7   → integral_prod_first_coord + integral_prod_separable via
       `MeasureTheory.integral_prod_mul` (unconditional in Mathlib);
       the first-coord version uses `g(p.1) = g(p.1) * 1` plus
       `stdGaussian_integral_one = 1`
6   → phi_S_tail (FTC twice + new helpers `phiDer_S_at_one_plus_eps`
       and `phiDer_S_tail` in Potential.lean; the layer integral
       lemma was moved from TestFunction to Potential)
5   → phi_S_boundary_small (IBP `phi_S(b) = ∫_0^b (b-t)·φ''_S(t) dt`
       plus split at t=1-ε with `phiDer2_S_core` and
       `integral_phiDer2_S_layer`)
```

## Axioms discharged in this round

* `TestFunction.hasDerivAt_g_S_layer_pos` proved via FTC for primitives
  (`intervalIntegral.integral_hasDerivAt_right`) and chain rule with
  `|·|` (which equals `id` near `x > 0`), then `congr_of_eventuallyEq`
  to transport from `N_S(|·|)/A_S` to `g_S` on `layerPos`.
* `TestFunction.hasDerivAt_g_S_layer_neg` proved analogously using
  `|·| = -·` near `x < 0` (gives sign flip), `phi_S_even` and
  `phiDer2_S_even` to express the derivative at `-x` in terms of `x`.
* `TestFunction.A_S_symm` proved by:
  `∫_{Ioo(-1-ε,-1+ε)} φ''·exp(φ) = ∫_{(-1-ε)..(-1+ε)} φ''·exp(φ)`
  (set-to-interval), then change of variables `t ↦ -t` via
  `intervalIntegral.integral_comp_neg` plus evenness of `φ_S, φ''_S`.
* `TestFunction.layerLebesgueEnergyPos_eq` proved by pointwise
  simplification of the integrand on `layerPos` using
  `g_S' = phiDer2_S · exp(phi_S)/A_S`, `Real.exp_neg`, and `field_simp`,
  reducing the integral to `(1/A_S²) · A_S = 1/A_S`.
* `TestFunction.layerLebesgueEnergyNeg_eq` analogous, using `A_S_symm`.
* `TestFunction.E_phi_g_S_eq` proved by:
  - `withDensity` rewrite (`integral_withDensity_eq_integral_toReal_smul`)
    of the `ρ_S` integral as `(Z_S)⁻¹` times a Lebesgue integral;
  - `ENNReal.toReal_ofReal` + `smul_eq_mul` to expose the density factor;
  - splitting the volume integral over `layerPos ∪ layerNeg` (where the
    integrand vanishes off the layers via `g_S'_off_layers`); and
  - identifying each piece with the corresponding layer Lebesgue energy.

### Earlier in current sequence (already at axiom count 30)

* `TestFunction.g_S_continuous` proved via FTC for primitives applied to
  `N_S` and `Continuous.if_le` for the nested piecewise gluing.

To preserve the topological order required by Lean (definitions before
uses), `q_S_asymp` and `t_S_asymp` are placed at the end of
`Normalization.lean` (after `exists_S_Z_S_ge_one`), and
`exists_S_q_S_lt_one` is moved after `q_S_asymp`.

## What remains as axioms (23)

### TestFunction.lean (4 remaining)

* `A_S_asymp` — `A_S − S = O(S⁻¹)` as `S → ∞`. Genuinely asymptotic.
* `integral_g_S_eq_q_plus_error` — expansion of `∫ g_S dρ_S = q_S + R`
  with `|R| ≤ t_S`. Requires splitting over core / layers / exterior,
  using `g_S = 0` on core and `g_S = 1` on exterior, plus the symmetry
  identity `tailInt_S(left) = tailInt_S(right)` from `phi_S_even`.
* `integral_g_S_sq_eq_q_plus_error` — analogous for `g_S²`.
* `Var_phi_g_S_expansion` — derivable from `Var_phi_g_S_isBigO` and
  `q_S_isBigO`; previous attempts failed on `Asymptotics.IsBigO`
  bookkeeping.

### Normalization.lean (8 remaining)

* `phi_S_tail`, `phi_S_boundary_small`, `phi_S_layer_small`,
  `tailInt_S_tail_eq`, `tail_gaussian_bound`, `tailInt_S_asymp`,
  `Z_S_asymp` — change-of-variables and asymptotic bookkeeping for
  the partition function.
* `exp_negPhiS_integrable` — Gaussian-domination integrability.

### OneDimensional.lean (6 remaining)

* `rho_S_isProb`, `rho_S_reflection_invariant` — proofs sketched in
  comments; the unconditional form needs `0 < S` for measurability.
* `phiDer_S_memL2`, `g_S_memL2` — L² membership for inner products.
* `EE_phi_S_asymp`, `Var_f_S_asymp` — final asymptotics.

### HigherDimensional.lean (5 remaining)

* `stdGaussian`, `stdGaussian_isProb`, `stdGaussian_first_moment`,
  `integral_prod_first_coord`, `integral_prod_separable`,
  `prodSpace_iso_euclidean` — Mathlib has `gaussianReal`,
  `Measure.pi`, `MeasureTheory.integral_prod`; lifting to this file's
  forms is a substantial task.

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
