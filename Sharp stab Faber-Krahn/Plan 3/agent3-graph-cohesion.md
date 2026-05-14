# Agent 3 — Graph levels stay graph: outer-collar cohesion

Plan 3 deployment, sub-task 3.

*Note: file assembled from the agent's full returned text (Write inside
the sub-agent was denied; content was relayed via the final message).*

## Files used

1. `Plan 2/level-set-deficit-identity.md` — `D_H, D_I`, velocity identity
   `|∇u| = -t_ρ/V`, parallel-surface expansion (Lemma 8.4).
2. `Plan 2/global-foliation-trace.md` — modulated graph gauge
   `∂E_ρ = z(ρ) + (ρ + h(ρ,θ)) θ`, action functional (F).
3. `Plan 2/selected-boundary-layer-theorem.md` — parallel-surface
   Lemma 3.1, `r_t(y) = t/q(y) + O(t^{1+γ})`.
4. `Plan 2/weighted-serrin-collar-reduction.md` — `D_H` → Bernoulli
   interpolation.
5. `Final/GraphEntry.tex` — radial graph gauge, tubular threshold
   `μ_tub = 1/4`.
6. `Final/NearlySphericalClosure.tex` — `C^{2,γ_0} / H^{1/2}` norm
   conventions.

## 1. Setting

`Ω ⊂ B_R`, `|Ω| = ω_n`, `-Δu = 1`, `u = 0` on `∂Ω`. `E_t = { u > t }`,
`m(t) = |E_t|`, `Σ_t = { u = t }`, `ρ(t) = (m(t)/ω_n)^{1/n}`.

**Standing hypotheses at the entry level `t_0 = t(ρ_0)`, `ρ_0 ∈ [ρ_*, 1]`:**

- **(G0)** `∂E_{t_0} = { z_0 + (ρ_0 + h_0(θ)) θ : θ ∈ ∂B_1 }` with
  `‖h_0‖_{C^{1,γ}(∂B_1)} ≤ ε_0`, `‖h_0‖_∞ ≤ ρ_0 / 4`; first-mode-neutralised.
- **(B)** Bernoulli: `0 < q_- ≤ |∇u| ≤ q_+`, `[|∇u|]_{C^γ(Σ_{t_0})} ≤ M`.
- **(C)** Collar `U_{coll} ⊃ Σ_{t_0}` with `|∇u| ≥ q_-/2` and
  `u ∈ C^{2,γ}_{loc}`.

**Caveats.**
- (G0) is *not* automatic from "rough level + small `D_I`"; that is
  exactly Agent 2's missing theorem.
- (B) is procured from small `D_H(t_0)` via
  `weighted-serrin-collar-reduction.md` §3.
- (C) is the local PDE input that prevents the
  "boundary is a graph ⇒ everything is a graph" failure mode.

## 2. Tubular collar

`Ψ_{t_0}(y, s) = y - s ν_{t_0}(y)` is a `C^{1,γ}`-diffeomorphism on
`Σ_{t_0} × (-r_0, r_0)` for some `r_0 = r_0(κ_*, q_-, q_+, M)`,
and `s` is the `C^{1,γ}` signed normal distance.

## 3. Implicit function theorem

**Lemma 3.1.** For `|s| ≤ r_1`,
`q_-/4 ≤ -∂_s u(Ψ_{t_0}(y, s)) ≤ 2 q_+`; `r_1` depends only on
`(q_-, q_+, M, ‖D²u‖_{L^∞(U_{coll})})`. Proof: continuity from (B)+(C).

**Proposition 3.2.** There exists `δ_1 = q_- r_1 / 16 > 0` such that for
`|τ| ≤ δ_1`, `y ∈ Σ_{t_0}`, the equation `u(Ψ_{t_0}(y, s)) = t_0 + τ` has
a unique `C^{1,γ}` solution `s = σ(y, τ)` with `σ(y, 0) = 0`,
`∂_τ σ(y, 0) = -1/|∇u|(y) ∈ [-1/q_-, -1/q_+]`, and
\[ \Sigma_{t_0 + \tau} \cap \Psi_{t_0}(\Sigma_{t_0} \times (-r_1, r_1))
   = \{ \Psi_{t_0}(y, \sigma(y, \tau)) : y \in \Sigma_{t_0} \}. \]

This is the *local* version of `selected-boundary-layer-theorem.md`
Lemma 3.1, with `Σ_{t_0}` replacing `∂U` and (G0)+(B)+(C) replacing
BDV regularity.

## 4. Normal-graph ↔ radial-graph bridge

**Lemma 4.1.** If `Σ = { z_0 + (ρ_0 + h_0) θ }` with
`‖h_0‖_{C^{1,γ}} ≤ ε_0 ≤ ρ_0/4` and
`Σ' = { y - σ(y) ν(y) : y ∈ Σ }` has `‖σ‖_{C^{1,γ}}` small, then
`Σ' = { z_0 + (ρ_0 + h) θ }` with
`‖h - h_0‖_{C^{1,γ}(∂B_1)} ≤ C(ε_0, n) ‖σ‖_{C^{1,γ}(Σ)}`.
(Standard radial-projection composition; slope threshold `μ_tub = 1/4`
of `GraphEntry.tex`.)

## 5. Main theorem (graph cohesion)

**Theorem 5.1.** Under (G0)+(B)+(C), there exist `δ_1 > 0` and
`C_1 > 0` (depending on the data plus `ε_0`) such that for every
`|τ| ≤ δ_1`:

(i) `Σ_{t_0 + τ}` is `C^{1,γ}`, normal-graph over `Σ_{t_0}` of size
   `≤ (1/q_-)|τ| + C_1 |τ|^{1+γ}`.

(ii) **Radial gauge:** there exist `z(τ) ∈ ℝ^n`, `ρ(τ) > 0`,
   `h(τ, ·) ∈ C^{1,γ}(∂B_1)` first-mode-neutralised such that
   `∂E_{t_0 + τ} = { z(τ) + (ρ(τ) + h(τ, θ)) θ : θ ∈ ∂B_1 }`.

(iii) **Quantitative motion:**
   `|z(τ) - z_0| + |ρ(τ) - ρ_0| ≤ C_1 |τ|` and
   `‖h(τ, ·) - h_0‖_{C^{1,γ}} ≤ C_1 |τ|`.

(iv) **Reparametrisation in `ρ`:** `τ ↦ ρ(τ)` is `C^{1,γ}` with
   `ρ'(0) = m'(t_0) / (n ω_n ρ_0^{n-1}) < 0`
   (bounded away from 0 by (B) + coarea); its inverse gives the
   foliation gauge `z(ρ), h(ρ, θ)` on a parameter interval containing
   `ρ_0`, satisfying the volume / first-mode normalizations of
   `global-foliation-trace.md` §1.

(v) **Norm propagation in the foliation gauge:**
   - `‖∂_ρ h(ρ, ·)‖_{L^2(∂B_1)}^2
      ≤ C_2 · D_H(t(ρ)) / ((-t_ρ) ρ^{2n-2}) + C_2 ‖h‖_{C^1}^2`,
   - `Q(h(ρ, ·))
      ≤ C_2 · D_I(t(ρ)) / ρ^{2n-4} + C_2 ‖h‖_{C^1}^3`.

These are *upper* bounds populating the action (F) of
`global-foliation-trace.md`; the *lower-bound* (reverse) direction is
the separate task of §§3–4 there.

**Proof sketch of (v).** `V(τ, θ) = ∂_τ X · ν_τ = 1 / |∇u|(X(τ, θ))` by
(3.3); differentiating the volume + first-moment constraints expresses
`∂_τ h` (non-neutral part) in terms of the variance of `V`, which equals
the variance of `1/|∇u|` and is controlled by `D_H` through
`level-set-deficit-identity.md` §6. The `Q(h)` bound is the standard
Fuglede expansion.

## 6. From one entry level to a fixed outer annulus

**Corollary 6.2.** If (G0)+(B)+(C) holds at a finite family
`{ ρ_0^{(j)} } ⊂ [ρ_*, 1]` with mutual spacing
`≤ Δρ ≃ 2 δ_1 / (q_+ ρ_0^{n-1})` and uniform parameters, then iterating
Theorem 5.1 gives a single foliation gauge `(z(ρ), h(ρ, ·))` on the
entire `[ρ_*, 1]` with `‖h(ρ, ·)‖_{C^{1,γ}} ≤ C ε_0`, satisfying
(5.1)–(5.6) pointwise. Action bound (F) on `[ρ_*, 1]` follows.

## 7. Hypothesis ledger

| Hypothesis | Used in | Strength |
|---|---|---|
| (G0) `C^{1,γ}` graph at entry | §2, §4, §5(i)–(iii) | `C^{1,γ}` + small `L^∞` |
| (B) two-sided Bernoulli | §3 | pointwise two-sided |
| (C) one-sided collar `|∇u| ≥ q_-/2` | §3 | open-neighbourhood lower bound |
| `‖D²u‖_{L^∞}` on collar | §3 (radius `r_1`) | upper bound, consequence of (C) |

**Not used:** any global Bernoulli on `∂Ω`; any BDV / selection-principle
regularity; the invalid "A0" metric Lipschitz bound.

## 8. Status

**Proved (conditional on (G0)+(B)+(C)):** Theorem 5.1, Corollary 6.2.

**Heuristic only:** explicit constants in Fuglede expansion (5.6);
explicit dependence of `C_1, C_2, δ_1` on `(ε_0, q_-, q_+, M, R)`.

**Out of scope:** producing (G0) (Agent 2); pushing `ρ_* → 0` (the brief
explicitly warned against this and required only fixed outer collar);
the reverse lower bounds — `D_H + D_I` controls action — which is the
actual sharp content of `global-foliation-trace.md`.

**Classification.** **Pure Plan 2.** No hybrid with Plan 1. The
radial/normal slope-`μ_tub = 1/4` lemma appearing in `GraphEntry.tex`
is reused as a calculus fact, not as a Plan 1 black box.
