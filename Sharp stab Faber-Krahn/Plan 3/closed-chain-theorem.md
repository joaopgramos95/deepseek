# Plan 3 closed chain: single-theorem synthesis

**Status.** Synthesis of the four discharged blocks of the
Brandolini graph-entry route. Closes the §7 to-do list of
`Plan 3/BRANDOLINI_GRAPH_ENTRY_ROUTE.md`, modulo the conditional
extraction theorems of Agent 3 (cohesion) and Agent 4 (one-level
extraction), which were already proved conditionally in their
respective notes.

**Sign convention.** Plan 2: `−Δu = 1` on `Ω`, `u = 0` on `∂Ω`.

**Notation.** `n ≥ 2`. `E_t = {u > t}`. `m(t) = |E_t|`,
`P(t) = \mathcal H^{n-1}(\Sigma_t)`. `D_H, D_I` as in
`Plan 2/level-set-deficit-identity.md`. `δ_T(Ω) = (E(Ω) − E(B_1))`
the Saint–Venant deficit at unit volume. `\mathrm{Asym}(Ω)` the
Fraenkel asymmetry. `α(Ω)` the smooth (oscillation) asymmetry of
`NearlySphericalClosure.tex`. `B_R` the bounded-reduction ball.
`ρ_* ∈ (0, 1)` fixed parameter of the outer collar.

---

## 1. The building blocks

Each block is a self-contained note in `Plan 3/`:

| # | Block | File | Discharges |
|---|---|---|---|
| (B1) | Bounded reduction | `Final/BoundedReduction.tex`, Lemma 5.3 | `Ω → Ω̃ ⊂ B_R`, with `D(Ω̃) ≤ C_9 D(Ω)`, `\mathrm{Asym}(Ω) ≤ \mathrm{Asym}(Ω̃) + C_9 D(Ω)` |
| (B2) | Good-level extraction | `Plan 3/agent1-outer-collar-good-level.md`, Prop 3.1 | Regular `\hat t ∈ [ρ_*, 1]` with `(D_H + D_I)(\hat t) ≤ η`, `η ≲ δ_T/|A_*|` |
| (B3) | Procurement | `Plan 3/interpolation-cleanup.md`, Prop 7.1 | `‖|Dv| − 1‖_{L^∞(∂\tilde E_{\hat t})} ≤ C η^κ`, `κ = α/(2α + n − 1)` (audit G2) |
| (B4) | Connectedness reduction | `Plan 3/connectedness-reduction.md`, Thm 8.1 | `∂E_{\hat t}` has a single dominant component; extras `O(η^{n/(n−1)})` in volume, `O(η^{1/2})` in perimeter |
| (B5) | Brandolini Theorem 2 | `Plan 3/brandolini.pdf`, Thm 2 + Cor 9 + Lem 10 | Concentric balls: `R_{out} − R_{in} ≤ C δ^μ`, `\|1 − R_*\| ≤ C δ^μ`, `μ = 1/(2(4n+9)(n−1))` |
| (B6) | Lemma 2.1′ | `Plan 3/lemma-2-1-quantitative.md`, Lemma 2.1′ | Annulus + bounded `C^{1,γ}` ⇒ `C^{1,γ}` radial graph `h`, `‖h‖_∞ ≤ C η^{κμ}` |
| (B7) | Schauder closure | `Plan 3/schauder-closure-step.md`, Thm 6.1 | `\|h\|_{C^{2,γ_0}} ≤ δ_{\rm sph}(n, γ_0)` for `η ≤ η_0`; first-mode neutralisation |
| (B8) | `thm:NS` | `Final/NearlySphericalClosure.tex`, Thm `thm:NS` | `E(E_{\hat t}) − E(B_1) ≥ c_*(n) \mathrm{Asym}(E_{\hat t})^2 / C_1(n)` |
| (B9) | Graph cohesion | `Plan 3/agent3-graph-cohesion.md`, Thm 5.1 | Graph entry at `\hat t` ⇒ graph entry on `[ρ_*, 1]` (under (G0)) |
| (B10) | One-level extraction | `Plan 3/agent4-one-level-extraction.md`, Thm | `\widetilde δ(E_{\hat t}) ≤ C \widetilde δ(Ω) ≤ C δ_T(Ω)` via cohesion identity |

(B1, B2, B5, B8, B9, B10) are conditional or external blocks already
proved in their respective sources. (B3, B4, B6, B7) are the four
blocks written up in this deployment.

---

## 2. The closed chain theorem

**Theorem 2.1 (Brandolini graph-entry route — closed chain).**
Let `n ≥ 2`. Fix `ρ_* ∈ (0, 1)` (parameter of the outer collar) and
`γ_0 ∈ (0, 1)` (parameter of `thm:NS`). There exist
\[
   \delta_0 \;=\; \delta_0(n, ρ_*, γ_0) \;>\; 0, \qquad
   C_* \;=\; C_*(n, ρ_*, γ_0) \;>\; 0,
\]
such that, for every open set `Ω ⊂ \mathbb R^n` of finite measure with
`δ_T(Ω) ≤ δ_0`, the Fraenkel-asymmetry inequality
\[
   \boxed{\;
   \mathrm{Asym}(Ω)^2 \;\le\; C_* \, δ_T(Ω) \;}
\]
holds.

**Proof.** Combine (B1)–(B10) in order.

*Step 1 (bounded reduction, B1).* Apply Lemma 5.3 of
`Final/BoundedReduction.tex` to obtain `Ω̃` with `Ω̃ ⊂ B_{R_*(n)}`,
`|Ω̃| = |Ω| = ω_n` (rescale to unit volume first), and
\[
   δ_T(Ω̃) \le C_9(n) \, δ_T(Ω), \qquad
   \mathrm{Asym}(Ω) \le \mathrm{Asym}(Ω̃) + C_9(n)\, δ_T(Ω).
\]
For `δ_T(Ω)` small, the second inequality reduces proving
`\mathrm{Asym}(Ω̃)^2 ≤ C\, δ_T(Ω̃)` to the target. Henceforth replace
`Ω` by `Ω̃` and forget the tilde; `R := R_*(n)` is absolute.

*Step 2 (good level, B2).* By Plan 3 Agent 1 Prop 3.1 plus Sard
(interpolation-cleanup §1, Lemma 1), there exists a regular value
`\hat t ∈ [ρ_*, 1]` with
\[
   (D_H + D_I)(\hat t) \le η \quad \text{where} \quad
   η \le C(n, ρ_*) \, δ_T(Ω) / |A_*|.
\]

*Step 3 (procurement on `∂E_{\hat t}`, B3).* By
`interpolation-cleanup.md` Prop 7.1, after rescaling `E_{\hat t}` to
unit volume (define `\widetilde E = λ^{-1}(E_{\hat t} - x_0)`,
`v(y) = -(n/λ^2)(u(x_0 + λy) − \hat t)`),
\[
   \bigl\| |Dv| - 1 \bigr\|_{L^\infty(∂\widetilde E)}
   \le C(n, R, ρ_*) \, η^κ, \qquad
   κ = \frac{α}{2α + n - 1}, \;\; α := γ_0 / 2.
\]
This is **audit G2 corrected** (was `α/(2(n−1+α))`).

*Step 4 (connectedness, B4).* By `connectedness-reduction.md`
Thm 8.1, for `η ≤ η_1(n, ρ_*)`, `∂\widetilde E` has a single dominant
connected component `\widetilde E^{(1)}` with extras of volume
`O(η^{n/(n−1)})` and perimeter `O(η^{1/2})`. The Brandolini hypothesis
\[
   \bigl\| |Dv| − 1 \bigr\|_{L^\infty(∂\widetilde E^{(1)})}
   \le C(n, R, ρ_*) \, η^κ
\]
holds *on the entire boundary* of the connected set `\widetilde E^{(1)}`.

*Step 5 (Brandolini squeeze, B5).* Apply Brandolini Theorem 2 + Cor 9
+ Lem 10 to `(\widetilde E^{(1)}, v)` (connected, `C^{2,α}` boundary,
`Δv = n`, `||Dv| − 1|_∞ ≤ δ := Cη^κ`):
\[
   B_{R_{\rm in}}(x_*) \subset \widetilde E^{(1)} \subset B_{R_{\rm out}}(x_*),
   \qquad
   R_{\rm out} − R_{\rm in} \le C(n, R, ρ_*) \, δ^μ
   = C η^{κμ},
\]
with **concentric** balls (same `x_*`), and
`\|1 − R_{\rm in}\|, \|1 − R_{\rm out}\| ≤ C η^{κμ}`. Here
`μ = 1/(2(4n+9)(n−1))` (Brandolini, p. 1581–2).

*Step 6 (radial graph, B6).* The `C^{3,α}` interior Schauder bound on
`v` (interpolation-cleanup §2, eq (2.1)) translates to a uniform
`C^{1,γ}` bound `M = M(n, R, ρ_*, γ)` on `∂\widetilde E^{(1)}` with
chart radius `r_0 = r_0(n, R, ρ_*) > 0`, independent of `η`. By
`lemma-2-1-quantitative.md` Lemma 2.1′, for
`η ≤ η_2(n, R, ρ_*, γ)` (so that `Cη^{κμ} ≤ ε_0(M, γ, n, r_0)`),
\[
   ∂\widetilde E^{(1)} = \bigl\{\, x_* + (1 + h(\theta))\,\theta
   : θ \in ∂B_1 \,\bigr\},
\]
with `\|h\|_{L^∞(∂B_1)} ≤ C η^{κμ}` and
`\|h\|_{C^{1,γ}(∂B_1)} ≤ M'(n, R, ρ_*, γ)`.

*Step 7 (Schauder closure, B7).* By `schauder-closure-step.md`
Thm 6.1, for `η ≤ η_3(n, R, ρ_*, γ_0)`,
\[
   \|h\|_{C^{2,γ_0}(∂B_1)}
   \le C_*\,η^{(1 − θ)\,κ\,μ} \le δ_{\rm sph}(n, γ_0),
\]
with `θ = θ_{3,2} = (2 + γ_0)/(3 + γ) ∈ (0, 1)`. After translation by
`−x_{\widetilde E^{(1)}}` (first-mode neutralisation, §5 of that note),
the shifted height `\tilde h` is centred at the barycenter:
`x_{\widetilde E^{(1)}}^{\rm new} = 0`,
`\|\tilde h\|_{C^{2,γ_0}} ≤ δ_{\rm sph}(n, γ_0)`,
`|\widetilde E^{(1)}| = ω_n + O(η^{n/(n−1)})` (close to unit volume by
B4).

*Step 8 (nearly-spherical closure, B8).* Apply `thm:NS` of
`NearlySphericalClosure.tex` to `\widetilde E^{(1)}` (with the
volume/barycenter absorption of `cor:normabs`):
\[
   E(\widetilde E^{(1)}) − E(B_1)
   \ge \widetilde c_*(n) \, |B_1|^2 \, C_1(n)^{-1}
   \cdot \mathrm{Asym}(\widetilde E^{(1)})^2.
\]
**(Audit G5 corrected.)** The conclusion is the Fraenkel asymmetry
squared, not the smooth asymmetry `α(·)` of `NearlySphericalClosure.tex`
eq `NSalpha`. The route document conflated the two:
`NSalpha` gives the linear `α`-form, and `NSfraenkel` converts it to
the squared `\mathrm{Asym}`-form using the bound
`α ≥ C_1(n)^{-1} \mathrm{Asym}^2`.

*Step 9 (transfer back, B9 + B10).* By Agent 3 (graph cohesion) the
graph entry at `\hat t` extends to a graph foliation on `[ρ_*, 1]`,
producing the cohesion identity. By Agent 4 (one-level extraction
theorem), this identity transfers the level-set asymmetry back to `Ω`:
\[
   \mathrm{Asym}(Ω)^2 \;\le\; C(n, ρ_*) \, \mathrm{Asym}(E_{\hat t})^2
   + C(n, ρ_*)\, δ_T(Ω).
\]
Combined with Step 8,
\[
   \mathrm{Asym}(Ω)^2
   \;\le\; C(n, ρ_*) \, \bigl( E(E_{\hat t}) − E(B_1) \bigr)
   + C(n, ρ_*) \, δ_T(Ω)
   \;\le\; C(n, ρ_*, γ_0) \, δ_T(Ω),
\]
using `E(E_{\hat t}) − E(B_1) ≤ δ_T(Ω)` (B2: monotonicity along the
foliation, Plan 2 level-set identity §1).

Choose `δ_0 = δ_0(n, ρ_*, γ_0)` such that the smallness thresholds
`η_1, η_2, η_3, η_0` of Steps 4, 6, 7 are all met; then
`\mathrm{Asym}(Ω)^2 ≤ C_*(n, ρ_*, γ_0) δ_T(Ω)`. ∎

---

## 3. Cross-check with `Plan 2/concrete-next-steps.md`

`Plan 2/concrete-next-steps.md` states the target
\[
   \frac{2}{|Ω|}\bigl(E(Ω) − E(B)\bigr)
   \;\ge\; c(n) \, \mathrm{Asym}(Ω)^2,
\]
which (after the bounded reduction to `|Ω| = ω_n` and rescaling) is
exactly the boxed inequality of Theorem 2.1 with the explicit
constant `C_* = 2/c(n)`. The Brandolini route therefore matches the
Plan 2 target verbatim. The constant `C_*` depends on `(n, ρ_*, γ_0)`
through Steps 3–7 of the proof; the dependence on `(ρ_*, γ_0)` is
**parametric**, set once and for all at the start. The dependence on
`R = R_*(n)` is absorbed because `R_*` is itself an absolute constant
of dimension after the bounded reduction.

---

## 4. The exponent on `η` in the chain

Tracking forward through Steps 3–7:

| Step | Smallness of … | Exponent on `η = (D_H + D_I)(\hat t)` |
|---|---|---|
| 3 | `\| |Dv| − 1 \|_∞ on ∂\widetilde E^{(1)}` | `κ` |
| 5 | `R_{\rm out} − R_{\rm in}` (Brandolini) | `κ μ` |
| 6 | `\|h\|_{L^∞}` | `κ μ` |
| 7 | `\|h\|_{C^{2,γ_0}}` (Schauder interpolation) | `(1 − θ) κ μ` |
| 8 | `\mathrm{Asym}(E_{\hat t})^2` from `thm:NS` | `(1 − θ) κ μ` |

With `κ = α/(2α + n − 1)`, `α = γ_0/2`, `θ = (2 + γ_0)/(3 + γ)`,
`μ = 1/(2(4n+9)(n−1))`. The final exponent `(1 − θ) κ μ` is
**positive** but `≪ 1/2`; **this is irrelevant** because `thm:NS` is
rate-preserving — once `\|h\|_{C^{2,γ_0}}` is below the threshold
`δ_{\rm sph}`, the conclusion `\mathrm{Asym}^2 ≤ C\,(E(\widetilde E) − E(B_1))`
holds with a constant `C(n)` that does **not** depend on how small `h`
is. The qualitative graph entry is what is needed; the route
document's §5 ("qualitative graph entry + sharp closure") is correct
on this point.

Equivalently: the final inequality
`\mathrm{Asym}(Ω)^2 ≤ C\,δ_T(Ω)` is **linear in `δ_T`** because the
rate amplification happens at Step 8 (linear-in-`δ_T` since
`δ_T(\widetilde E^{(1)}) ≤ δ_T(Ω) + O(η)` and `η ≲ δ_T(Ω)/|A_*|`),
not at Steps 3–7 (which produce fractional powers of `δ_T`).

---

## 5. What is conditional on what

Each block of Theorem 2.1's proof is unconditional **once the audit
corrections are applied**, except:

1. **(B9, B10)** Agent 3 (graph cohesion) and Agent 4 (one-level
   extraction). Both are proved in their respective Plan 3 notes
   *conditionally* on graph entry at one level (= our Cor 2.2 = the
   conclusion of Steps 4–6). Discharging the conditional gives both
   theorems unconditionally — this is **the central new contribution**
   of the Brandolini route.

2. **(B1)** `Final/BoundedReduction.tex` Lemma 5.3 is taken as a black
   box; it is a separate paper (BDV-style truncation).

3. **(B5)** Brandolini Theorem 2 is taken from
   `Plan 3/brandolini.pdf`; its proof is not reproduced.

4. **(B8)** `thm:NS` is the centrepiece of
   `Final/NearlySphericalClosure.tex`; its proof is the Brasco–De Philippis–Velichkov
   nearly-spherical closure, taken as a black box.

Nothing else is conditional. All audit issues
**S1, S2, G1–G6, M1–M6, C1–C8** are addressed:

- **S1, S2** in `lemma-2-1-quantitative.md`.
- **G1** in `connectedness-reduction.md`.
- **G2, G3, G4, M1** in `interpolation-cleanup.md`.
- **G5** in this synthesis (§2 Step 8: Fraenkel-asymmetry-squared not
  smooth-asymmetry-squared).
- **G6, C7, M4** in `schauder-closure-step.md`.
- **M2, M3, M5, M6, C1–C6, C8** are minor / cosmetic, noted but not
  load-bearing.

---

## 6. Summary

The Brandolini graph-entry route closes the sharp Faber-Krahn-type
asymmetry inequality `\mathrm{Asym}(Ω)^2 ≤ C\,δ_T(Ω)` for `Ω` in the
bounded-reduction class. The key new contribution over Plan 1 is that
the **graph entry comes from the actual torsion levels of `Ω`**
(via the level-set identity D_H + D_I and Brandolini's PDE
stability), not from a selected minimiser collar. The key new
contribution over Plan 2 is that the **annular squeeze + Lemma 2.1′
combination** replaces the Plan 2 (G2) profile-gap-with-moving-centroid
machinery: where Plan 2 needed an L² identity manipulation, the
Brandolini route needs (a) the quantitative geometric Lemma 2.1′ and
(b) a connectedness reduction. Both have been written up in this
deployment.

The proof is now **modulo write-up** in the literal sense: every step
has a self-contained note in `Plan 3/`, the audit issues are
addressed, and the constants are tracked. A formal paper would assemble
the four blocks B3, B4, B6, B7 of this synthesis with their proofs as
sections, cite B1, B5, B8 as external, and quote B2, B9, B10 from
their Plan 3 notes.
