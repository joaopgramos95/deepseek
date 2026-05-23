# Strategy A — Part B (Step 1): selection-as-regulariser, what it delivers

Independent investigation (2026-05-15). Setup: `−Δu=1` in `Ω`, `u=0`
on `∂Ω`, `|Ω|=ω_N`, `Ω⊂B_R`, `R≥2`; `δ_T(Ω)=E(Ω)−E(B_1)≥0` the
Saint–Venant deficit; `Asym` the Fraenkel asymmetry; `α(Ω)=
∫_{Ω△B_1(x_Ω)}\bigl||x−x_Ω|−1\bigr|` the BDV smooth asymmetry, which
controls `Asym(Ω)^2≲_N α(Ω)`. Sources: BDV `1306.0392v1.pdf`
§4 (Lemmas 4.5–4.18), `Plan 1/quantitative-selection-principle.md`,
`Plan 1/WHAT_PLAN1_DOES.md`, `Plan 1/corrections-needed.md`.

The question (used only as a regularisation device): does the BDV
penalised-minimiser construction produce, from a near-extremal `Ω`, a
competitor `Ω'` with (a) a smooth boundary with `(n,R)`-uniform
derivative bounds, (b) `δ_T(Ω')≤C(n,R)δ_T(Ω)`, (c) `Asym(Ω')≥
c·Asym(Ω)−C·δ_T`?

## 1. The construction, stated as a regulariser

Fix `R≥2`. Let `Ω₀⊂B_R`, `|Ω₀|=ω_N`,
`ε:=α(Ω₀)>0`, `δ:=δ_T(Ω₀)`, `q:=δ/α(Ω₀)`. Let `f_{η̂}` be the
BDV volume penalty (Lemma 4.5; `η̂=η̂(R)`, `B_1` minimises
`F_{η̂}=E+f_{η̂}`). Pick `τ` with `q≪τ²≪1` (e.g. `τ=q^{1/4}`)
and `τ≤τ_ex(n,R)`. Minimise over quasi-open `U⊂B_R`

  `G_{ε,τ}(U) = F_{η̂}(U) + √(ε² + τ²(α(U)−ε)²)`.

A minimiser `U_*` exists (BDV Lemma 4.6 with `τ` in place of `σ`,
once `C₂τ≤η̂/2`). Volume-normalise: `Ω' := (ω_N/|U_*|)^{1/N} U_*`.
This is the single-set version of BDV's penalised functional (4.10).

## 2. What is genuinely obtained — (b) deficit and (c) asymmetry

These two are clean and quantitative; they are *not* the obstruction.

**(b) Deficit kept O(δ_T).** Minimality against `Ω₀` plus that `B_1`
minimises `F_{η̂}` give `0≤F_{η̂}(U_*)−F_{η̂}(B_1)≤δ`
(`Plan 1` Lemma 1, faithful to BDV (4.16)–(4.17)). Comparison of
`U_*` with the equimeasured ball through Lemma 4.5's modulus gives
`||U_*|−ω_N|≤C(n,R)δ`, hence the dilation factor obeys
`|λ−1|≤C(n,R)δ`. Since `U_*⊂B_R`, `E(λU_*)=λ^{n+2}E(U_*)` and the
energy is `O_{n,R}(1)`, so

  **`δ_T(Ω') ≤ C₁(n,R) · δ_T(Ω₀)`**,  `C₁=C₁(n,R)` explicit in
  `η̂(R), C₄(n,R)`. ✔ (b) holds, constant depends only on `(n,R)`.

**(c) Asymmetry comparable.** From the `√·` term in the minimality
inequality, `τ²(α(U_*)−ε)²≤2εδ+δ²`, so

  `|α(U_*)−α(Ω₀)| ≤ √(2εδ+δ²)/τ = α(Ω₀)·√(2q+q²)/τ`.

Adding the dilation error `|α(Ω')−α(U_*)|≤C(n,R)ε q` (Lipschitz of
`α` on the fixed perimeter class `P(U_*)≤P_sel(n,R)` from Lemma 4.6),

  **`α(Ω') ≥ (1 − ρ(q,τ))·α(Ω₀)`**,  `ρ(q,τ)=√(2q+q²)/τ +
  C(n,R)q`.

With `τ=q^{1/4}`, `ρ=O(q^{1/4})`, so `α(Ω')≥½α(Ω₀)` once `q≤
q_sel(n,R)`. Translating into `Asym` and `δ_T`: since `Asym²≲_N α`
and `α(Ω')≥α(Ω₀)−C√(εδ)/τ`,

  **`Asym(Ω')² ≥ c(n)α(Ω₀) − C(n,R)√(α(Ω₀)δ_T)/τ`**;

i.e. `Asym(Ω')²/δ_T(Ω') ≥ c·Asym(Ω₀)²/δ_T(Ω₀)` up to `(n,R)`. ✔ (c)
holds *in the ratio form actually needed for transfer* — but note the
preservation is multiplicative on `α` only because `√(εδ)/τ≪ε`,
i.e. it presupposes `q≪τ²`, the small-quotient regime. The honest
caveat (P1, `corrections-needed.md`): this multiplicative bound is
exactly the historically hard part; here it is bought by the
algebraic `√·`-penalty inequality and is sound *as a ratio bound*,
but it does not give `Asym(Ω')≳Asym(Ω₀)` with an absolute constant
outside the small-`q` regime, and it gives nothing if `q⋧τ²`.

## 3. What is genuinely obtained — (a) regularity and its constants

This is where the precise answer is delicate. Decompose into three
layers.

**Layer 1 — reduced-boundary `C^{1,γ}`, unconditional, but with a
singular set.** `U_*={u_*>0}` satisfies the perturbed one-phase
quasi-minimality (BDV (4.19) with `τ`):
`½∫|∇u_*|²−∫u_* + f_{η̂}(|{u_*>0}|) ≤ (same for v) + C_Rτ|{u_*>0}△
{v>0}|`. For `τ≤τ_reg(n,R):=min{τ_ex,σ₂,σ₃}` the Alt–Caffarelli
package of BDV applies:

- nondegeneracy + `u_*≈dist(·,∂U_*)` (Lemma 4.9, 4.11(i)): constants
  `C₆,%₀=C₆,%₀(n,R)`;
- equi-Lipschitz `‖∇u_*‖_{L^∞}≤C₆(n,R)` (Lemma 4.11(ii));
- two-sided density `c≤|U_*∩B_r|/|B_r|≤C` (Lemma 4.11(iii)),
  `c=c(n,R)`;
- a Bernoulli measure `−Δu_*=1_{U_*}−q_{u_*}H^{n−1}⌊∂*U_*` with
  `0<c≤q_{u_*}≤C`, `c,C=c,C(n,R)` (Lemma 4.12).

So the **reduced** boundary `∂*U_*` is `C^{1,γ}` with `(n,R)`-uniform
nondegeneracy/density constants, *unconditionally* (no smallness of
`δ_T`). But this is one-phase Alt–Caffarelli regularity: in general
`H^{n−1}(∂U_*∖∂*U_*)=0` is all one gets, and a singular set is *not*
excluded by Layers 1 alone. There is no general `C^{1,γ}` statement
for the *full* topological boundary, and no derivative bound on a
global parametrisation, at this layer.

**Layer 2 — `C^∞` of the Bernoulli coefficient, with `(n,R)`-uniform
`C^k` bounds, conditional on smallness of `τ` only.** BDV Lemma 4.15
computes the Euler–Lagrange law and Lemma 4.16 gives the explicit
formula

  `q_{u_*}(x)² = Λ + [ τ²(α(U_*)−ε)/√(ε²+τ²(α(U_*)−ε)²) ]·Ψ_{U_*}(x)`,

with `Ψ_{U_*}(x)=(|x−x_{U_*}|−∫_{U_*}\frac{y−x_{U_*}}{|y−x_{U_*}|}dy·x)`
smooth and the bracket `≤C(n,R)τ`. For `τ≤σ₃(n,R)`, `Λ` is
two-sided bounded by `(n,R)` and (using `|x−x_{U_*}|≥1/2`, which
itself requires the Hausdorff closeness `B_{1−δ}⊂U_*⊂B_{1+δ}` — see
the circularity note below) `q_{u_*}∈C^∞(N_{δ̂}(∂U_*))` with

  **`‖q_{u_*}‖_{C^k(N_{δ̂}(∂U_*))} ≤ C(k,n,R)`**,  `δ̂=δ̂(n,R)`.

This `C^k` bound on the coefficient is `(n,R)`-uniform and does *not*
need `δ_T` small — it needs only `τ≤σ₃(n,R)` and the Hausdorff
closeness `(4.34)`.

**Layer 3 — flatness improvement to a global `C^{k+1,γ}` graph
(BDV Theorem 4.18 / Alt–Caffarelli–De Silva).** Theorem 4.18: if
`u_*` is of class `F(μ,1,+∞)` in `B_{4%}(x₀)` with `μ≤μ̄` and
`%≤κ̄μ²`, then `∂U_*∩B_%(x₀)` is a `C^{1,γ}` graph with norm
`≤C(n,R)μ`; and if `q_{u_*}∈C^{k,γ}` of a neighbourhood then the
graph is `C^{k+1,γ}` with `‖f‖_{C^{k+1,γ}}≤C(n,R,‖q_{u_*}‖_{C^{k,γ}})`.
The constants `γ,μ̄,κ̄,C` depend only on `min q_{u_*}, max q_{u_*},
Lip(q_{u_*}), R, n` — all `(n,R)`-uniform by Layer 2.

**Therefore**, once *every* boundary point can be put into class
`F(μ,1,+∞)` at a *fixed* `(n,R)`-scale `%(μ)` with a *fixed* `μ=
μ(n,R)≤μ̄`, the local graphs patch (radial projection over `∂B_1`)
to a single

  `∂Ω' = {(1+g(θ))θ : θ∈∂B_1}`,  `‖g‖_{C^∞}` with **`(n,R)`-uniform
  `C^k` bounds for every `k`**, and the singular set is *excluded*
  (every point carries an A–C graph).

This is genuinely "smooth with `(n,R)`-uniform derivative bounds" —
*provided the hypothesis of the previous sentence holds*. It does not
hold for free; see §4.

## 4. The decisive obstruction: the flatness hypothesis is bought only
   by smallness of `α`, and that smallness is not provided by the
   deficit at this step

To get *every* point into class `F(μ,1,+∞)` at a fixed scale one
needs the global Hausdorff closeness

  `d_H(∂U_*,∂B_1(x_{U_*})) ≤ h_F(n,R,μ)`   (BDV (4.34)),

with `h_F≲μ%(μ)` a fixed `(n,R)`-quantity. The only available route
to Hausdorff closeness from a *single* set is the `α`→Hausdorff
estimate (`Plan 1` Lemma 5, from the two-sided density):

  `d_H(∂U_*,∂B_1) ≤ C_H(n,R)·α(U_*)^{1/(2n)}`.

So a *global* smooth graph with `(n,R)`-uniform derivative bounds is
delivered **iff** `α(U_*)≤α_graph(n,R):=(h_F/C_H)^{2n}`, an absolute
`(n,R)` threshold (`Plan 1` Corollary 8). Three consequences,
stated plainly:

1. **The regulariser is conditional on small asymmetry, not on small
   deficit.** Step 1 outputs a global, `(n,R)`-uniformly smooth graph
   only in the regime `α(Ω₀)≲α_graph(n,R)`. This is *not* a
   restriction that the deficit being `O(δ_T)` removes: the deficit
   controls `q=δ/α`, not `α` itself. In the genuinely interesting
   near-extremal regime `α` *is* small, so the threshold is met — but
   then the input to Step 1 already presupposes the kind of
   closeness-to-a-ball that the whole programme is trying to *prove
   quantitatively*. This is the (P1) circularity flagged in
   `corrections-needed.md`, here localised exactly: **the `(n,R)`-
   uniform higher-derivative bounds of Layer 2/3 use the Hausdorff
   bound `|x−x_{U_*}|≥1/2` and the flatness `(4.34)`, which use
   `α≤α_graph` — i.e. they consume the smallness they are meant to
   provide.** Layer 1 (reduced-boundary `C^{1,γ}` with a possible
   singular set) is the only part free of this.

2. **Quantitatively, away from the small-`α` regime the answer to (a)
   is: only reduced-boundary `C^{1,γ}` with a singular set possibly
   present in dimension `n` large.** BDV inherit Alt–Caffarelli
   one-phase regularity; the singular set of a one-phase A–C minimiser
   is empty for `n` below the Caffarelli–Jerison–Kenig / De Silva–
   Jerison dimension and is only known to have `H^{n−1}`-measure zero
   in general. The "smooth everywhere" statement in BDV holds *only
   after* the flatness improvement covers every point, which again
   needs `α≤α_graph`. So: outside the small-`α` regime, (a) is
   **reduced-boundary `C^{1,γ}` only**, constants `(n,R)`-uniform on
   `∂*U_*`, no global parametrisation, singular set not excluded.

3. **Even inside the small-`α` regime, the construction is not a
   single-set deterministic map in BDV's own proof.** BDV's
   Proposition 4.4 — the statement that yields the `C^k`-converging
   smooth `U_j` — is itself proved *by contradiction along a sequence*
   `σ_j→0`, with Kuratowski convergence `∂Ω_j→∂B_1` (Lemma 4.13) and
   the global `C^k` bound coming from **Ascoli–Arzelà on that
   sequence** (`g_j→0` in `C^{k−1}`). The single-set replacement
   (`Plan 1` Prop. 4 + Lemmas 5–7) removes the sequence *for the
   deficit/asymmetry ratio* (§2 above is genuinely sequence-free), but
   the *regularity* output still rests on `Plan 1` Lemmas 6–7, whose
   constant tracking (Hausdorff→flatness at one A–C scale, then
   patching) is explicitly listed there as the **two unproved
   constant-tracking tasks**. So the `(n,R)`-uniform derivative bounds
   are *reduced to*, not *established by*, the present construction.

## 5. Precise verdict

| Output | Status | Constant dependence |
|---|---|---|
| `δ_T(Ω')≤C₁δ_T(Ω₀)` | proved, sequence-free | `C₁=C₁(n,R)` explicit |
| `α(Ω')≥(1−ρ)α(Ω₀)`, ratio transfer | proved in regime `q≪τ²` | `ρ=O(q^{1/4})`, else conditional |
| `∂*U_*` is `C^{1,γ}`, density/nondeg | proved, unconditional | `(n,R)`-uniform; **singular set not excluded** |
| `q_{u_*}∈C^∞`, `‖·‖_{C^k}≤C(k,n,R)` | proved **assuming** `(4.34)` | `(n,R)`-uniform but conditional on Hausdorff closeness |
| global smooth graph, `‖g‖_{C^k}≤C(k,n,R)`, no singular set | proved **only if** `α(U_*)≤α_graph(n,R)` | `(n,R)`-uniform; **conditional on small `α`** |

**Bottom line.** The selection construction is a *legitimate and
sequence-free* device for keeping the deficit `O(δ_T)` and the
deficit-to-asymmetry ratio comparable (parts (b),(c) — clean,
`(n,R)`-explicit). For part (a) it delivers, *unconditionally*, only
**reduced-boundary `C^{1,γ}` with `(n,R)`-uniform nondegeneracy and
density constants and a possibly non-empty singular set**. The
"smooth with `(n,R)`-uniform `C^k` derivative bounds" conclusion is
genuine but **conditional on `α(Ω₀)≲α_graph(n,R)`**, an absolute
asymmetry threshold that the deficit smallness does *not* supply. In
the near-extremal regime where it does hold, the higher-derivative
bounds are obtained by *consuming* the very ball-closeness the
programme aims to quantify — the (P1) circularity, here pinned to the
use of `(4.34)`/`|x−x_{U_*}|≥1/2` in Lemma 4.16 and of
`α≤α_graph` in the flatness step. As a pure regulariser (not closing
the proof) this is acceptable: one may *assume* the near-extremal set
is already Hausdorff-close (passing to the inside is a separate,
legitimate move), and then Step 1 hands back a `(n,R)`-uniformly
`C^∞` graph at `O(δ_T)` deficit cost and comparable asymmetry. What
it does **not** do is *manufacture* that closeness from the deficit;
Step 1 is a smoother, not a closeness-generator.
