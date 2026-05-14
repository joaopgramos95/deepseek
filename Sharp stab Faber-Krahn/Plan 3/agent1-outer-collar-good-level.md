# Agent 1 — Outer-Collar Good-Level Extraction

Plan 3 deployment, sub-task 1.

*Note: this file was assembled from the agent's returned summary; its
Write call into `Plan 3/` was blocked at the sub-agent permission layer.*

## Result classification

Pure Plan 2 (no Plan 1, no Serrin stability, no selection principle).
Avoids the discredited "A0 metric Lipschitz" argument.

## What is proved (unconditional)

Working from the exact identity of `Plan 2/level-set-deficit-identity.md`,
`2 delta_T = ∫ (D_H + D_I) dν` with `dν = dt / (c_n m^{1-2/n})`,
plus the profile-gap bound `0 ≤ b − v ≤ 2 δ_T / s` and Lemma 8.1 of that file:

**Proposition 3.1 (good-level extraction, `t`-collar).**
Fix the outer collar
\[ T_{coll} = \{ t : c_1 \eta_* \le L - m(t) \le c_2 \eta_* \},
   \qquad \eta_* = \sqrt{\delta_T \cdot L^{1-2/n}} \]
(`= sqrt(δ_T)` in normalized scale). Under the smallness
`δ_T ≤ c_n R² c_1 η_*`, the collar has weighted mass
`ν(T_coll) ≍ η_*/L`, and for every `η > 0`,
\[ \nu\bigl(\{ t \in T_{coll} : D_H(t) + D_I(t) > \eta \}\bigr)
   \le \frac{2 \delta_T}{\eta}. \]

Equivalently, a fraction
`1 − O(δ_T / (η · η_*/L)) = 1 − O(sqrt(δ_T)/η)` of the collar (by `ν`)
is good. For thresholds `η ≫ sqrt(δ_T)` the good set has the same order
of mass as the collar.

## What is conditional / flagged

**Proposition 4.1 (`ρ`-collar form).** Translating to volume radius
`ρ` requires controlling `1/a(t)` = the coarea Jacobian. This is recorded as

> **Hypothesis (A): `a(t) ∈ [c, C]` on the collar.**

Proposition 4.1 is stated *conditional* on (A). This is **not** the discredited
"A0 metric Lipschitz"; it is genuine coarea nondegeneracy needed for the
change of variables `t → ρ`.

## Failure mode addressed

- No `η^{-1}` factor on the deficit; the collar is fixed at `sqrt(δ_T)`
  independent of the threshold `η`.
- No averaging over a slab that introduces `η^{-1}` loss large enough to
  kill the sharp rate after transfer.

## What this does NOT do

Proposition 3.1 alone gives only the `sqrt(δ_T)` scale; it does not
produce a level with `D_H + D_I = O(δ_T)`. Sharp rate requires
Agents 2–4 (graph entry, cohesion, perturbative extraction).

## Files used

- `Plan 2/level-set-deficit-identity.md` (exact identity + Lemma 8.1)
- `Plan 2/global-foliation-trace.md`
- `Plan 2/selected-boundary-layer-theorem.md`
- `Plan 2/weighted-serrin-collar-reduction.md`
- `Plan 2/plan2.md`
- `Plan 2/concrete-next-steps.md`
