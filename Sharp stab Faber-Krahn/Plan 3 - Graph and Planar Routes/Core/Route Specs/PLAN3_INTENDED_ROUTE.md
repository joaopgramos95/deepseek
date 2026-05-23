# Plan 3 — the intended route (authoritative, v3)

Corrected per the user's red-pen of `MY_UNDERSTANDING.md` (2026-05-15).
This version supersedes all earlier framings. Earlier assistant
confusions are explicitly struck in §3 so they do not recur. This file
fixes *what we are trying to do*; it does not claim the route closes.

Setup: `−Δu = 1` in `Ω`, `u = 0` on `∂Ω`. `E_t = {u > t}`,
`Σ_t = ∂E_t = {u = t}`. The "zero level" is `∂Ω`. `δ_T(Ω)` =
Saint–Venant deficit. `Asym` = Fraenkel asymmetry. Goal:
`Asym(Ω)² ≤ C(n) δ_T(Ω)`.

Only `D_H` is used. `D_I` is **not** part of this route.

## The route (single level, static)

**Step 1 — Chebyshev extraction of a good near-boundary level.**
The exact level-set identity gives `∫ (D_H\text{-integrand})(t)\,dt
≲_n δ_T(Ω)`. Fix a **small absolute constant `θ`** (a fixed small
number, *not* `δ_T`-small, *not* `1/C`-small). By Chebyshev/Markov,
\[
   \bigl|\{\, t : (D_H\text{-integrand})(t) > θ \,\}\bigr|
   \;\le\; \frac{C_n}{θ}\,δ_T(Ω).
\]
The bad set has measure `O_θ(δ_T)`. Hence there exists a good level
`t̂` with `D_H(t̂) ≤ θ` that **lurks within distance `O_θ(δ_T)` of the
boundary** (a good level is found inside any near-boundary window of
length `> (C_n/θ)δ_T`).

**Step 2 — `D_H` small ⇒ `∂E_{t̂}` is a graph (regularity-free).**
Each component of `∇u` is harmonic: `Δ(∂_i u) = ∂_i(Δu) =
∂_i(−1) = 0`. `D_H(t̂) ≤ θ` says `|∇u|` is close to a constant on
`Σ_{t̂}` in an **integrated (`L²`) sense**. An **interior estimate for
harmonic functions** — Harnack / mean-value / interpolation-style for
the harmonic vector `∇u`, *not* any regularity of `∂Ω` — should upgrade
the integrated closeness to the pointwise bound
`\|\,|∇u| − c\,\|_{L^∞(Σ_{t̂})}` small. The inner level `Σ_{t̂}` is,
for a.e. `t̂`, a smooth (real-analytic) hypersurface for free (Sard +
interior analyticity of `u`; we are on an *inner* level, never on
`∂Ω`). With `|∇u| ≈ c` in `L^∞` on a smooth inner level, `∂E_{t̂}` is
a genuine graph over a sphere (Serrin-stability sense — the `L^∞`
bound is *earned from `D_H`*, not assumed as a hypothesis).

**Step 3 — graph subdomain with `O(δ_T)` deficit.**
`Ω̃ := E_{t̂} ⊂ Ω` is a level set of `u`, now a graph, and its own
Saint–Venant deficit satisfies `δ_T(Ω̃) = O(δ_T(Ω))`. (Clean
mechanism, the one reusable fact from the deleted building blocks:
`u − t̂` is *exactly* the torsion function of `E_{t̂}` — it solves
`−Δ(u−t̂) = 1`, vanishes on `∂E_{t̂}` — so `δ_T(Ω̃)` is computed
exactly, not by a comparison inequality, and the collar `{0<u≤t̂}`
of measure `O(δ_T)` is the only loss.)

**Step 4 — perturbative finish.**
It suffices to prove the sharp inequality for domains whose boundary
is a (small) graph over a sphere; apply it to `Ω̃`:
`Asym(Ω̃)² ≲ δ_T(Ω̃) ≲ δ_T(Ω)`.

**Step 5 — transfer back, `δ_T` of room to spare.**
`|Ω ∖ Ω̃| = O(δ_T)` (the level lurks `O_θ(δ_T)` from `∂Ω`), so the
superlevel transfer error squares to `≪ δ_T`. Hence
`Asym(Ω)² ≲ δ_T(Ω)`.

## What is NOT in the route

- No Plan 2 foliation, no action bound `(F)`, no `∂_ρ`
  derivative/variation, no `t`-family / cohesion. Single level, static.
- No `D_I` / isoperimetric-Fuglede argument. Only `D_H`.

## Explicitly struck (assistant confusions — recorded so they do not recur)

These were introduced by the assistant / sub-agents and are **not** the
route:

- **(BReg) / "assume `∂Ω ∈ C^{2,α}`" / boundary regularity / the weak
  selection principle.** We never use Serrin stability on `∂Ω`, only on
  an *inner* level set, which is smooth for free. The "regularisation"
  detour was confusion.
- **"Deeper level ⇒ smaller graph norm" / a depth parameter `C` / the
  `Cδ_T`-collar with `D_H ≲ 1/C` / the window `1≪C≪δ_T^{-1/2}`.**
  Hallucinated. The mechanism is plain Chebyshev (Step 1): the bad-level
  set has measure `O_θ(δ_T)`, so a good level with `D_H ≤ θ` (small
  absolute constant) sits within `O_θ(δ_T)` of the boundary.
- **The `√δ_T`-collar.** Wrong scale. The collar is `O(δ_T)`.
- **Brandolini's `L^∞` theorem used with its `L^∞` hypothesis assumed
  as an input.** Backwards. The `L^∞` gradient bound is *produced from
  `D_H`* via the harmonic-function interior estimate (Step 2).

## The single genuine crux

**Step 2's upgrade:** from `D_H(t̂) ≤ θ` (integrated `L²` closeness of
`|∇u|` to a constant on `Σ_{t̂}`) to `\|\,|∇u|−c\,\|_{L^∞(Σ_{t̂})}`
small, using only that `∇u` is a vector of harmonic functions plus
interior estimates — no regularity of `∂Ω`. This is the node to
develop. Everything else (Steps 1, 3, 4, 5) is structurally in hand
from existing notes (Chebyshev extraction; the `u−t̂` is exactly the
torsion function of `E_{t̂}` deficit transfer; perturbative
sharp-FK-for-graph-domains; the superlevel transfer lemma).

## Status

The corrected *idea* is fixed above. The proof attempt (max-effort,
2026-05-15) produced a substantive update that **pivots the mechanism
away from the graph framing of Steps 2/4 written above** — recorded
here, not silently rewritten into the body, because the body is the
user's red-penned text.

**Graph framing refuted for `n ≥ 3` (`tentacle-model.md`).** For
`Ω = B_1 ∪ (w,L)`-tentacle: `δ_T(Ω) ≍_n |T| = w^{n-1}L` (sharp,
independent energy expansion), while reaching a tentacle-free /
graph-like inner level needs an escape-layer `≍_n |T| + w²`. For
`n ≥ 3` the `w²` ball-shell floor dominates `|T|`, so a tentacle-free
level is **unreachable within an `O(δ_T)` layer**. Steps 2-as-graph
and 4 (perturbative) are therefore dead for `n ≥ 3`. (`n = 2`
survives.) Tentacles are *not* counterexamples to the theorem:
`Asym ≍ |T|`, `δ_T ≍ |T|`, so `Asym² ≍ |T|² ≪ |T| ≍ δ_T` — they
satisfy the target inequality with large room.

**Working proof is graph-free "Chain B" (`proof-step2.md`,
verified `verify-chainB.md`).** It bypasses the graph entirely:
\[
  \text{Step 1 (Chebyshev, `proof-step1.md`)} \;\to\;
  \underbrace{\;\delta_T(E_{\hat t}) \gtrsim_n |E_{\hat t}|^{-1}\!\!\int_{E_{\hat t}}\!\!|D^2u+\tfrac1nI|^2\;}_{(T)\text{ Weinberger, reg.-free}}
  \;+\; \text{Step 3 (`proof-step3.md`)} \;+\;
  \underbrace{(\text{CONV})}_{H^2\text{-rigidity}\Rightarrow\text{Asym}}
\]
giving `Asym(E_{\hat t})² ≤ C(n,\mathrm{diam},M)\,δ_T(Ω)`, then
Step 5 (`proof-step5.md`) `⟹ Asym(Ω)² ≤ C_*(n)\,δ_T(Ω)`,
**sharp-linear, regularity-free, all `n`**. The route is
`Step 1 → Step 2(Chain B) → Step 5`; Step 3 is internal to Chain B;
Step 4 and the `n≥3` graph obstruction are **moot**.

**Verification state.** `verify-chainB.md` (explicit adversarial pass)
returns **VALID**: `(T)` regularity-free with purely dimensional
`c(n)`; the KEY BOUND independently reproduces `tentacle-model.md`'s
`D_H ≍_n w^{n-3}L` exactly (independent cross-check); `(CONV)`'s
constant stays dimensional on the pinched tentacled family (the
divergent coarea `1/s_0` is quarantined in an excised set paid
additively; `s_0 ≍_n 1/n` is dimensional). One honest non-fatal patch:
`(CONV)` must be stated per connected component (the Saint-Venant
strict-stability dichotomy handles disconnection — large asymmetry
costs `Θ(1)` deficit, disjoint from the small-`δ_T` regime).

**Not yet asserted closed.** This is an agent verification with
independent cross-corroboration — the strongest state reached — but
not human-refereed. The two load-bearing analytic inputs a referee
must check: **(T)** the regularity-free Weinberger *quantitative*
inequality, and **(CONV)** the `H²`-rigidity ⟹ Fraenkel-asymmetry
harmonic-replacement step. Pending the user's decision to pivot the
spec body to Chain B.
