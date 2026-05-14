# Agent 4 — One-Level Perturbative Extraction

Plan 3 deployment, sub-task 4.

*Note: this file was assembled from the agent's returned summary; its
Write call into `Plan 3/` was blocked at the sub-agent permission layer.*

## Result classification

Pure Plan 2 (foliation route). No "A0" metric-Lipschitz, no selection
principle, no Serrin stability, no Markov on a thin window.

## Extraction theorem

**Hypotheses.**

**(A2)** Outer-collar graph entry on `ρ ∈ [ρ_*, 1]` with
`‖h(ρ)‖_{C^{1,γ_*}} / ρ ≤ ε_0`, `|z(ρ)| ≤ ε_0 ρ`, plus a pointwise
`L^∞` graph-entry bound
\[ \|h\|_\infty^2 \le \frac{C (D_H + D_I)}{\rho^{n-2}}. \]

**(A3)** Cohesion / action bound (F) of `Plan 2/global-foliation-trace.md`:
\[ \int_{\rho_*}^1 \bigl(\rho^{n+1} \|\partial_\rho h\|_{L^2}^2
   + \rho^{n-1} Q(h)\bigr) d\rho \le C_F \delta_T. \]

**Conclusion.** There exists `ρ̂ ∈ [ρ_*, 1]` such that
\[ \widetilde\delta(E_{t_{\hat{}}}) :=
   \rhô^{-2} \|h(\rhô)\|_{H^1}^2
   + \rhô^{-2} |z(\rhô)|^2
   + \|h(\rhô)\|_{L^\infty}^2
   \le C(n, \rho_*) \, \delta_T(\Omega). \]

## Mechanism (proof sketch)

Three independent Chebyshev selections on the **fixed** window `[ρ_*, 1]`
produce a positive-measure subset `G_1 ∩ G_2 ∩ G_3`:

1. **`G_1`** controls `Q(h(ρ̂))` (giving `H¹` via non-neutral coercivity);
2. **`G_2`** controls `|z'(ρ̂)|` (giving `|z(ρ̂)|` via `H¹` trace, after
   pinning `z(1)=0` using `Ω = E_0`);
3. **`G_3`** controls `D_H + D_I` at `ρ̂` (feeding (A2)'s quantitative
   entry to give `L^∞`).

No window shrinks with `δ_T`, hence no `1/sqrt(δ_T)` reappears.

## Match to closure

The chosen `widetilde δ` dominates `‖g‖_{H^{1/2}}²` used in
`Final/NearlySphericalClosure.tex`, Theorem `thm:NS`, via the embedding
`H¹ ↪ H^{1/2}`, after rescaling `E_{t̂}` to unit volume and shifting
by `z(ρ̂)`.

## Regularity gap (flagged, not closed here)

`thm:NS` needs `C^{2,γ_0}`; (A2) provides only `C^{1,γ_*}`.
A Schauder / interpolation upgrade is flagged as a downstream obligation,
not part of this extraction theorem.

## Failure mode addressed

No re-running of Markov on a too-small window. The window `[ρ_*, 1]`
is independent of `δ_T`, so the old `sqrt(δ_T)` issue does not return.

## Files used

- `Plan 2/level-set-deficit-identity.md`
- `Plan 2/global-foliation-trace.md` (action bound (F))
- `Plan 2/selected-boundary-layer-theorem.md`
- `Plan 2/weighted-serrin-collar-reduction.md`
- `Plan 2/plan2.md`
- `Plan 2/concrete-next-steps.md`
- `Final/NearlySphericalClosure.tex` (Theorem `thm:NS`)
