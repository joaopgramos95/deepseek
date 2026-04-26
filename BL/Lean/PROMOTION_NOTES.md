# Promotion notes (orchestrator)

## State

| File                    | Status     | Local axioms |
|-------------------------|------------|--------------|
| Basic.lean              | promoted   | 0            |
| Bump.lean               | promoted   | 0            |
| Potential.lean          | promoted   | 0            |
| Normalization.lean      | promoted   | 19           |
| TestFunction.lean       | promoted   | 15           |
| OneDimensional.lean     | promoted   | 12           |
| HigherDimensional.lean  | promoted   | 15           |

`lake build L2Counterexample` succeeds. Zero `sorry` remaining
(the two `grep` hits in Normalization and HigherDimensional are inside
comments, not in code).

## Naming canon (mine)

Adopted across all files; resolves the prior identifier and semantic
collisions described in the original note.

| Concept                        | Canonical name      | Defined in           |
|--------------------------------|---------------------|----------------------|
| Smooth bump                    | `kappa`             | `Bump.lean`          |
| ε parameter (= S^-3)           | `eps_S`             | `Potential.lean`     |
| η parameter (= S^-4)           | `eta_S`             | `Potential.lean`     |
| Potential                      | `phi_S`             | `Potential.lean`     |
| First derivative               | `phiDer_S`          | `Potential.lean`     |
| Second derivative              | `phiDer2_S`         | `Potential.lean`     |
| Evenness of `phi_S`            | `phi_S_even`        | `Potential.lean`     |
| Oddness of `phiDer_S`          | `phiDer_S_odd`      | `Potential.lean`     |
| Evenness of `phiDer2_S`        | `phiDer2_S_even`    | `Potential.lean`     |
| Quadratic lower bound          | `phi_S_quadratic_lower` | `Potential.lean` |
| Core formula                   | `phi_S_core`        | `Potential.lean`     |
| Partition function             | `Z_S`               | `Normalization.lean` |
| Tail integral (∫_{1+ε}^∞ exp-φ)| `tailInt_S`         | `Normalization.lean` |
| Layer normalizer (blueprint A) | `A_S`               | `TestFunction.lean`  |
| Tail / layer masses            | `q_S`, `t_S`        | `Normalization.lean` |
| Test function                  | `g_S`               | `TestFunction.lean`  |
| Centered test function         | `ff_S`              | `OneDimensional.lean`|
| Centering constant             | `cc_S`              | `OneDimensional.lean`|
| Probability measure            | `rho_S`             | `TestFunction.lean`  |
| BL energy / variance / deficit | `EE_phi_S`, `Var_f_S`, `delta_phi_S` | `OneDimensional.lean` |

The blueprint reservation `A_S` = layer normalizer is honored: the
right-tail integral that used to share the name `A_S` is now
`tailInt_S` in `Normalization.lean`.

## Resolved semantic / hypothesis collisions

The original note flagged four blockers; here is what each became.

1. **`A_S` clash** — fixed by renaming Normalization's right-tail
   integral to `tailInt_S`. TestFunction now defines `A_S` directly as
   the layer integral via `noncomputable def`, so
   `A_S_intervalIntegral_def` is `rfl`.
2. **`Z_S_pos` hypothesis mismatch** — Normalization's `Z_S_pos` keeps
   the weaker `0 < S` hypothesis. TestFunction provides a thin wrapper
   `Z_S_pos_TF` that takes `1 < S` and forwards via
   `lt_trans zero_lt_one`. Call sites in TestFunction were updated.
3. **BigOInv vs IsBigO** — added `BigOInv.toIsBigO_aux` (private bridge
   in TestFunction) and re-exported the asymptotic axioms in `IsBigO`
   form as `q_S_isBigO`, `t_S_isBigO`. Existing TF proofs that needed
   the IsBigO formulation (`Var_phi_g_S_isBigO`) were rewired to use
   `t_S_isBigO`.
4. **Identifier conventions across files** — every file now uses
   `phi_S, phiDer_S, phiDer2_S, eps_S, eta_S` from `Potential.lean`.
   Old per-file aliases (`phi_S'`, `phi''_S`, `phi'_S`, `epsOf`,
   `etaOf`, `epsS`, `etaS`, `phiP_S`, `phiPP_S`, `phi_Sc`) were renamed.

## Remaining axioms

The 61 axioms in the canonical files are *deliberately* axiomatised:
they are either

- analytic facts that need real measure theory (`exp_negPhiS_integrable`,
  `tailInt_S_tail_eq`, `tail_gaussian_bound`, `phi_S_layer_small`, the
  Laplace transforms, the standard Gaussian moments, the product
  Fubini bridges); or
- the asymptotic estimates from sections 3–4 of the paper
  (`tailInt_S_asymp`, `Z_S_asymp`, `q_S_asymp`, `t_S_asymp`,
  `EE_phi_S_asymp`, `Var_f_S_asymp`, `phi_S_boundary_small`,
  `exp_neg_phi_boundary_asymp`, `one_div_tildeS_asymp`,
  `delta_phi_S_HD_eventually_pos`, `distSq_phi_S_over_delta_unbounded`,
  `no_uniform_L2_stability_1D`, `A_S_asymp`); or
- placeholders for things that *should* be proven from upstream but
  haven't been bridged yet (`phi_S_measurable`, `phi_S_tail`,
  `rho_S_isProb`, `rho_S_reflection_invariant`, `phiDer_S_measurable`,
  `g_S_measurable`, `phiDer_S_memL2`, `g_S_memL2`,
  `phiDer_g_integrable`, `Var_gg_eq_Var_ff`, `hasDerivAt_g_S_layer_pos`,
  `hasDerivAt_g_S_layer_neg`, `g_S_continuous`,
  `layerLebesgueEnergyPos_eq`, `layerLebesgueEnergyNeg_eq`,
  `E_phi_g_S_eq`, `q_S_abs_le_one`, `t_S_le_one`, `t_S_nonneg_axiom`,
  `integral_g_S_eq_q_plus_error`, `integral_g_S_sq_eq_q_plus_error`,
  `Var_phi_g_S_expansion`, `A_S_symm`, `f_S`, `E_phi_S`, `Var_phi_S`,
  `distSq_phi_S`, `f_S_integral_zero`, `f_S_orth_phiDer_S`,
  `prodSpace_iso_euclidean`, `stdGaussian`, `stdGaussian_isProb`,
  `stdGaussian_first_moment`, `integral_prod_first_coord`,
  `integral_prod_separable`).

The HigherDimensional file's `f_S, E_phi_S, Var_phi_S, distSq_phi_S,
delta_phi_S_HD` and the `*_HD` deficit are **deliberately** kept as
distinct symbols from `OneDimensional`'s `ff_S, EE_phi_S, Var_f_S, ...`.
Bridging them requires substantive work to express the higher-dim
quantities in terms of the 1D ones (per the product Fubini decomposition
the file already sets up). This is the natural next refactor and would
let `no_uniform_L2_stability_1D` and `distSq_phi_S_over_delta_unbounded`
in HigherDim be replaced by re-exports of OneDimensional's
`no_uniform_L2_stability_one_dim` and `var_over_delta_unbounded`.

## Recommended next refactor

1. Bridge `OneDimensional` ↔ `HigherDimensional`: define
   `delta_phi_S_HD := delta_phi_S` (etc.), then derive HigherDim's
   `no_uniform_L2_stability_1D` and `distSq_phi_S_over_delta_unbounded`
   from the corresponding OneDimensional theorems.
2. Discharge the analytic/asymptotic axioms one by one as time
   permits. The `BigOInv` algebra in `Normalization.lean` and the
   parity infrastructure in `Basic.lean` are reusable.

## WIP files

Each `WIP_*.lean` is now identical to its canonical counterpart (or
contains the same content modulo the agent header). Future agents can
edit the WIP files; the orchestrator promotes by `cp WIP_X.lean X.lean`
and re-running `lake build`.
