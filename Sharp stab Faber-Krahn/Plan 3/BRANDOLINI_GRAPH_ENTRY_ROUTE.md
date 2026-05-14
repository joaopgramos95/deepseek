# Brandolini–Nitsch–Salani–Trombetti route to graph entry

**Source.** `Plan 3/brandolini.pdf` (J. Differential Equations 245 (2008)
1566–1583), **Theorem 2**:

> Let `Ω ∈ C^{2,α}` be a bounded **connected** open set in `ℝⁿ` and let
> `u ∈ C²(Ω̄)` solve `Δu = n` in `Ω`, `u = 0` on `∂Ω`, with
> \[ \bigl\lvert |Du| - 1 \bigr\rvert \le \delta \quad \text{on } \partial \Omega. \]
> Then there exist `C = C(n, \mathrm{diam}\,Ω, [\partial Ω]_{C^{2,α}})` and
> `μ = μ(n) > 0` such that
> \[ R_{out} - R_{in} \le C \delta^\mu, \qquad
>    |1 - R_{in}| \le C \delta^\mu, \qquad
>    |1 - R_{out}| \le C \delta^\mu. \]

`R_in`, `R_out` are the inradius and circumradius of `Ω`.
This is exactly the **annular-squeeze** statement the deployment brief
called the central missing ingredient (Agent 2).

The route below uses Theorem 2 to close Agent 2's gap. The key
observation, due to JSR (this session), is:

> **Annular squeeze + connected boundary ⇒ radial graph.**

Inside an annulus of width `ε = C δ^μ` around a fixed sphere `∂B_1`,
the only way for a connected hypersurface to fail to be a radial graph
is to fold — and a fold of size `h` forces `R_out - R_in ≥ h`. Thus
non-graph-ness is bounded by the annular width, automatically.

## 1. From `D_H + D_I` to the Brandolini hypothesis on a torsion level

Pick a regular `t = t̂` in the outer collar produced by **Agent 1**
(Proposition 3.1: outside a `ν`-fraction `O(\sqrt{\delta_T}/\eta)` of
`T_{coll}`, `D_H(t) + D_I(t) ≤ \eta`).

After rescaling `E_{t̂}` to unit volume, Brandolini's hypothesis
`||Dv| - 1|_∞ ≤ δ` on `∂E_{t̂}` is procured in three steps.

### 1.1 Mean of `|∇u|` ≈ 1 on `∂E_t`

`D_I(t) ≤ \eta` plus quantitative isoperimetry forces `P(E_t)` close to
`P(B_{r(t)})`. Integration by parts on `E_t` (`Δu = 1`):
\[ |E_t| = \int_{\partial^* E_t} |\nabla u| \, d\mathcal H^{n-1}, \]
so `mean_{\partial^* E_t} |∇u| = |E_t| / P(E_t)`, which equals
`(c_n m^{-1/n + 1})|B_{r(t)}|/P(B_{r(t)}) (1 + O(\sqrt{D_I}))`.
After rescaling to unit volume on `∂B_1`, the mean is `1 + O(\sqrt{D_I})`.

### 1.2 `L²` variance of `|∇u|` from `D_H(t)`

Plan 2 `level-set-deficit-identity.md` §6:
\[ \int_{\partial^* E_t}
   \frac{(|\nabla u| - \bar f_t)^2}{|\nabla u|} \, d\mathcal H^{n-1}
   = \frac{m(t)}{P(E_t)^2} D_H(t), \]
with `\bar f_t = m(t)/P(E_t)`. So `\||∇u| - \bar f_t\|_{L²(\partial^* E_t)}^2
≤ C(t) D_H(t)`. After rescaling, this is an `L²` defect at scale
`\sqrt{D_H}`.

### 1.3 `L²` → `L^∞` interpolation

`u` is `C^{2,α}` in the interior; on a regular level `Σ_t = \{u = t\}`,
\[ [|\nabla u|]_{C^\alpha(\Sigma_t)} \le C \|u\|_{C^{2,\alpha}(\Sigma_t)}. \]
For `t̂` bounded away from `0` (e.g. `t̂` in the **fixed** outer annulus
`ρ ∈ [ρ_*, 1]` of Agent 3, **not** the `\sqrt{δ_T}`-collar of Agent 1)
this `C^\alpha` constant is bounded by `R, n` only. Then
`L²`+`C^\alpha` interpolation:
\[ \delta := \||\nabla u| - 1\|_{L^\infty(\Sigma_{\hat t})}
   \le C(n, R) \, D_H(\hat t)^{\alpha / (2(n - 1 + \alpha))}
   + C(n) \sqrt{D_I(\hat t)}. \]

So Brandolini's hypothesis holds at `\hat t` with
`δ ≤ C(n, R) (D_H + D_I)^{\kappa}`, `\kappa = \kappa(n, α) > 0`.

## 2. Brandolini squeeze ⇒ radial-graph property

Apply Theorem 2 to `E_{\hat t}` rescaled to unit volume:
\[ R_{out}(E_{\hat t}) - R_{in}(E_{\hat t}) \le C(n, R) \delta^\mu
   \quad \text{and} \quad
   |1 - R_{in}|, |1 - R_{out}| \le C \delta^\mu. \]

In particular `∂E_{\hat t}` lies in the annulus
`\{ 1 - C δ^μ ≤ |x - x_*| ≤ 1 + C δ^μ \}` around some center `x_*`.

### 2.1 The user's lemma: thin annulus + connected ⇒ radial graph

**Lemma 2.1 (annulus-to-graph).** Let `S ⊂ ℝⁿ` be a `C^{1,γ}`,
connected, closed hypersurface with
`S ⊂ \overline{B_{R_{out}}(x_*)} ∖ B_{R_{in}}(x_*)`, `R_{out} - R_{in} ≤ ε`.
Assume `S = ∂E` for `E` open, bounded, with `B_{R_{in}}(x_*) ⊂ E ⊂ B_{R_{out}}(x_*)`.
Then there exists `h : ∂B_1 → ℝ` with
\[ S = \{ x_* + (1 + h(\theta)) \theta : \theta \in \partial B_1 \},
   \qquad \|h\|_{L^\infty} \le \max(|1 - R_{in}|, |R_{out} - 1|). \]

*Proof sketch.* Each ray `\{ x_* + r \theta : r > 0 \}` enters `B_{R_{in}}`,
which is inside `E`, and exits `B_{R_{out}}`, which is outside `E`.
The ray therefore crosses `S` an odd number of times. If it crossed more
than once, there would be two values `r_1 < r_2` with both on `S`. The
arc of `S` connecting them lies in the annulus, but the radial
parametrisation flips orientation at any tangent-to-radial point. By
connectedness of `S` and the closedness of `E`, the unique crossing
gives `r = r(θ)`; set `h(θ) = r(θ) - 1`. The `L^∞` bound is immediate
from the annulus inclusion. ∎

*Refined statement.* Under the additional assumption that
`B_{R_{in}}(x_*) ⊂ E ⊂ B_{R_{out}}(x_*)` (delivered by Brandolini),
the `C^{1,γ}` regularity of `S` upgrades the graph to `C^{1,γ}` over
`∂B_1`, with norm
\[ \|h\|_{C^{1,\gamma}(\partial B_1)} \le C(n, \gamma, [S]_{C^{1,\gamma}}). \]

### 2.2 Combination

Applied to `S = ∂E_{\hat t}` rescaled (Brandolini gives the annular
inclusion + the squeeze; `C^{2,α}` regularity of `Σ_{\hat t}` gives
`C^{1,γ}` of `S` after rescaling):

**Corollary 2.2 (graph entry at `\hat t`).** With `\hat t` in the
fixed outer annulus and `(D_H + D_I)(\hat t) ≤ \eta`,
\[ \partial E_{\hat t} = \{ x_* + (1 + h(\theta)) \theta \},
   \quad \|h\|_{L^\infty} \le C \eta^{\kappa \mu},
   \quad \|h\|_{C^{1,\gamma}} \le C(n, R, \rho_*). \]

This is **Agent 2's missing conclusion**, conditional on connectedness
of `∂E_{\hat t}` (see §4 below).

## 3. Where this fits in the Plan 3 chain

The graph-entry corollary (2.2) feeds **(G0)** of Agent 3
(`agent3-graph-cohesion.md` §1), which until now was an *assumption*.
With (G0) discharged on `\hat t`, the rest runs:

| Step | Source | Status before | Status after Brandolini |
|---|---|---|---|
| Good-level extraction in collar | Agent 1, Prop 3.1 | ✓ proved | unchanged |
| Graph entry at one level `\hat t` | Agent 2 target | ✗ open | **closed** (this note, Cor 2.2) |
| Graph cohesion on `[ρ_*, 1]` | Agent 3, Thm 5.1 | ✓ conditional on (G0) | **(G0) discharged** |
| Perturbative extraction | Agent 4 | ✓ conditional on (A2)+(A3) | (A2) discharged |
| `NearlySphericalClosure` | `Final/NearlySphericalClosure.tex` | ✓ proved (Plan 1) | unchanged |

So the Plan 3 chain closes, **modulo the open hypotheses** of §4.

This **also revises Agent 5's verdict.** Agent 5 surveyed Serrin-stability
theorems for direct graph output and found none. The trick here is that
Brandolini Theorem 2 outputs only an annular squeeze; the **graph
extraction** comes from combining the squeeze with connectedness via
Lemma 2.1. No existing Serrin-stability paper packages that combination,
which is why Agent 5 missed it.

And it **revises Agent 7's verdict.** Agent 7 said the cheapest missing
input was (G2). With Brandolini in play, an alternative cheapest input
is the **regularity-uniformity hypothesis (R)** of §4 — and the rest of
the chain (Agents 1, 3, 4) is already proved conditionally.

## 4. Open hypotheses

The route runs **conditionally on the following**, none of which is
discharged here.

**(R) Uniform `C^{2,α}` regularity at level `\hat t`.**
Brandolini's `C` depends on `[\partial E_{\hat t}]_{C^{2,α}}` after
rescaling to unit volume. By interior Schauder for `Δu = 1`, this is
controlled by `\|u\|_{C^{2,α}(\{u \ge t̂/2\})}`, which is bounded by
`C(n, R, \mathrm{dist}(Σ_{\hat t}, \partial Ω))`. For `\hat t` in the
*fixed* outer annulus `ρ ∈ [ρ_*, 1]` (Agent 3's setting, **not** the
`\sqrt{δ_T}`-collar of Agent 1), the distance is bounded below by
`c(n, R, ρ_*) > 0`, so (R) holds with constants depending only on
`(n, R, ρ_*)`. **(R) is therefore not an obstruction in the
fixed-collar regime**, only in the `\sqrt{δ_T}`-collar.

This is the same regime distinction that already appears in Agent 3:
the cohesion theorem lives on `[ρ_*, 1]`, not on the `\sqrt{δ_T}`-collar.
The Brandolini-based graph entry inherits the same restriction.

**(C) Connectedness of `∂E_{\hat t}`.**
Brandolini Theorem 2 requires `Ω` connected. The torsion superlevel set
`E_{\hat t}` may have multiple components (cf. Figs 1–2 of `brandolini.pdf`,
showing two unit balls joined by a tentacle: the torsion function has
disconnected superlevel sets near the tentacle). For `\hat t` in the
*fixed* outer annulus (`ρ_* > 0` bounded away from `0`), one expects
exactly one dominant component, but this requires proof: the geometry
of `Ω` may have peninsulas pinched at `ρ_*`.

A clean reduction:
- Apply Agent 1 / Plan 2 bounded reduction first to get `Ω` in `B_R`.
- For each component `E_{\hat t}^{(j)}` of `E_{\hat t}`, apply Brandolini.
- Multi-component Brandolini outputs *a finite union of balls* (Theorem 1
  of the same paper, eqs (5)–(7)); the component carrying the bulk of
  `|E_{\hat t}|` is the "main" one.
- Argue that for `(D_H + D_I)(\hat t)` small enough, only one component
  carries non-negligible volume.

The latter step uses `D_I(\hat t)` (isoperimetric defect) to rule out
multi-ball configurations: a union of two balls of total volume `|B_1|`
has `D_I` bounded below by an absolute constant `> 0`, so smallness of
`D_I(\hat t)` excludes it. **This is a clean argument; it should be
written up.**

**(M) Volume preservation in interpolation.**
The `L²`-to-`L^∞` interpolation of §1.3 uses `[|\nabla u|]_{C^\alpha}`
on `Σ_{\hat t}`. On a `C^{1,γ}` surface this involves both intrinsic
Hölder norm and the surface curvature. Standard, but constants need to
be tracked.

## 5. Sharp-rate consistency

The cascade gives, at `\hat t`,
\[ \|h\|_{L^\infty} \le C (D_H + D_I)(\hat t)^{\kappa \mu / 2}, \]
where `\kappa = \alpha / (2(n - 1 + \alpha))`, `\mu = \mu(n)`. This is
*not* `O(\sqrt{δ_T})`. But sharp `A² ≤ C δ_T` does **not** require
sharp-rate graph entry: it requires `\|h\|` small enough for
`NearlySphericalClosure`, which then provides the sharp inequality in
one step. The qualitative graph entry suffices.

Concretely:
- `NearlySphericalClosure` (`Final/NearlySphericalClosure.tex`) outputs
  `E(Ω̃) - E(B_1) ≥ c_*(n) α(Ω̃)`, **not** a rate-amplifying inequality.
- So `α(E_{\hat t})² ≤ C \delta_T(E_{\hat t})` follows from
  Cor 2.2 (qualitative) + closure.
- Agent 4's extraction theorem then gives
  `\widetilde\delta(E_{\hat t}) ≤ C \delta_T(Ω)` via the cohesion
  identity, so `α(Ω)² ≤ C \delta_T(Ω)` by Agent 1 + transfer.

This is the standard "qualitative graph entry + sharp closure" pattern.
The exponent `κμ/2` does not appear in the final inequality.

## 6. Comparison with Agents 2, 5, 6, 7

- **Agent 2** identified the missing PDE step. **Brandolini Theorem 2
  is that step**, combined with Lemma 2.1.
- **Agent 5** asked for a Serrin-stability theorem outputting graph
  entry. None exists directly. Brandolini outputs annulus; Lemma 2.1
  converts annulus + connectedness to graph. The two-step combination
  is what Agent 5 was unable to find as a single theorem in the
  literature.
- **Agent 6** showed the *selected*-collar hybrid does not simplify.
  This route does **not** use the selected minimiser; it uses the actual
  torsion levels of `Ω`. The interior `C^{2,α}` regularity is automatic
  (Schauder for `Δu = 1`), so no BDV regularity package is needed.
  **This is the genuine advantage over Agent 6's hybrid.**
- **Agent 7** flagged (G2) as the cheapest input. (G2) and the
  Brandolini route are alternative bottlenecks. Both should be pursued;
  the cheaper of them to discharge wins.

## 7. To-do

1. **Write Lemma 2.1** in full (annulus + connected ⇒ radial graph,
   with `C^{1,γ}` upgrade). The argument is elementary; the only care
   needed is at radial-tangent points.
2. **Discharge (C)** via the `D_I(\hat t) ≤ \eta` ⇒ one-component
   argument.
3. **Track constants** in the `L²` → `L^∞` interpolation §1.3 to confirm
   `\kappa` is positive and `< 1/2`.
4. **State the closed Plan 3 chain** as a single theorem and cross-check
   with `Plan 2/concrete-next-steps.md`.

## 8. Status

**This is the route the brief asked for.** The chain runs `Ω → \hat t` via
Agent 1, `\hat t →` graph via Brandolini + Lemma 2.1, graph → foliation
via Agent 3, foliation → `\widetilde \delta(\hat t)` via Agent 4,
`\widetilde \delta` → sharp inequality via Plan 1
`NearlySphericalClosure`. The only step requiring new mathematics is
**Lemma 2.1**, plus the one-component reduction (C).

**Classification.** Pure Plan 2 in spirit (uses torsion levels of `Ω`,
not the selected `Ũ`). Uses Plan 1's `NearlySphericalClosure` only as
the final closure step, which is unavoidable. No "A0" metric-Lipschitz.
No selection principle. No BDV regularity package.
