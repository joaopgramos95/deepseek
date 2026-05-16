# What Plan 1 does

A plain account of the Plan 1 programme, written so its logical skeleton
and its conditional points are visible at a glance. Sources: `plan1.md`,
`quantitative-selection-principle.md`, `route-A-summary.md`,
`PLAN1_AGENT_REPORT.md`, `corrections-needed.md`, and the BDV paper
`1306.0392v1.pdf`.

## The goal

Prove the sharp quantitative Faber–Krahn inequality
`λ₁(Ω) − λ₁(B) ≥ c(n) Asym(Ω)²` (equivalently the sharp Saint–Venant
form `E(Ω) − E(B) ≥ c(n) Asym(Ω)²`, `E = −T/2`). This is exactly
Brasco–De Philippis–Velichkov's (BDV) theorem. Plan 1 does **not** aim
at a new theorem; it aims to make BDV's *proof* quantitative — to remove
the one non-constructive step and track all constants in `(n,R)`.

## What is non-constructive in BDV, and Plan 1's replacement

BDV prove sharp Saint–Venant by a **selection principle**. Given a
sequence of near-counterexamples (deficit `→0`, asymmetry bounded
below), they pass to *penalised minimisers*, use free-boundary
regularity to make these smooth and converging to a ball, and reach a
contradiction with the nearly-spherical second variation. The
non-constructive part is the **sequential selection + compactness limit
+ contradiction**.

Plan 1's single conceptual contribution is to replace this by a
**single-set penalised selection map** (`quantitative-selection-principle.md`,
its Theorem 2.2). From one set `Ω₀` with small deficit and asymmetry
`α(Ω₀)` (BDV's smooth asymmetry
`α(Ω)=∫_{Ω△B}\,\bigl||x−x_Ω|−1\bigr|`), it constructs *one* selected
quasi-open minimiser `Ω̃` of a penalised functional
`J_{τ,η̂,Ω₀}` such that

- `α(Ω̃) ≥ (1−ρ) α(Ω₀)` (asymmetry not destroyed), and
- the badness ratio `Q_α(Ω̃) := δ(Ω̃)/α(Ω̃)` satisfies
  `Q_α(Ω̃) ≤ (C_sel/(1−ρ)) Q_α(Ω₀)` (deficit-to-asymmetry not worsened
  beyond a constant).

No sequence, no compactness, no contradiction: a lower bound
`Q_α(Ω̃) ≥ c_*(n)` then transfers to `Q_α(Ω₀) ≥ c_*/(2C_sel)`, i.e. the
sharp inequality, *by computation*.

## The chain (Route A, the unconditional one in Plan 1's telling)

1. **Single-set selection** (Theorem 2.2): `Ω₀ → Ω̃`, preserving
   `α` up to `(1−ρ)` and `Q_α` up to `C_sel(n,R)`. Uses BDV's
   penalised-minimiser density/nondegeneracy lemmas (BDV 4.9, 4.12,
   4.16) as black boxes for the *regularity* of `Ω̃`.
2. **Graph entry**: below an explicit asymmetry threshold
   `α_graph(n,R)`, the free boundary `∂Ω̃` is a `C^{1,γ}` graph over a
   sphere (BDV's Alt–Caffarelli flatness improvement, BDV Theorem 4.18,
   fed by an `α→`Hausdorff`→`flatness chain).
3. **Bootstrap to small `C^{2,γ_0}`**: uniform Schauder bounds
   (hodograph + Kinderlehrer–Nirenberg) give a fixed-order high
   `C^{m,γ}` bound on the graph; interpolating that fixed bound against
   the *small* `L^∞`/Hausdorff size of the graph yields a *small*
   `C^{2,γ_0}` norm — the input BDV Theorem 3.3 needs.
4. **Closure**: BDV's nearly-spherical second variation (BDV Theorem
   3.3) applied to the small-`C^{2,γ_0}` graph gives `Q_α(Ω̃) ≥ c_*(n)`.
5. **Kohler–Jobin transfer**: converts sharp Saint–Venant into sharp
   Faber–Krahn with a universal-in-`n` multiplier.

(Plan 1 also has a *Route B*: a Bernoulli spectral closure replacing
step 4's second variation, conditional on a bilinear source-term
enumeration with constants. Route B is explicitly conditional and is
not the load-bearing route.)

## Honest status, from Plan 1's own correction notes

`corrections-needed.md` and `PLAN1_AGENT_REPORT.md` already record:

- **(P1) The single-set selection bound `C_sel`** (Theorem 2.2) is the
  conceptual core. It is *claimed* rigorous, but `C_sel` is a
  named-not-computed constant and the proof leans on BDV's
  penalised-minimiser regularity (BDV 4.9/4.12/4.16) as black boxes.
  Whether the single-set construction genuinely avoids the compactness
  it replaces — i.e. whether `α(Ω̃) ≥ (1−ρ)α(Ω₀)` and the `Q_α` bound
  hold *without* a hidden limiting/contradiction argument — is the
  central structural question.
- **(P2) Normalisation.** `Ω̃` is volume-normalised after construction;
  the notes admit the transformed Euler–Lagrange/Bernoulli law is
  asserted, not written out.
- **(P3) The `C^{1,γ}→` small-`C^{2,γ_0}` bootstrap** (step 3) is
  exactly the recurring norm-gap. Earlier drafts "jumped" it; it is
  claimed repaired by uniform Schauder + interpolation, but the
  smallness constants `σ_*, δ_*, q_*` are not tracked.
- **(P4) BDV Theorem 3.3's hypothesis** is small `C^{2,γ_0}`; the
  deficit only controls a half-derivative (`H^{1/2}`) of the graph, so
  step 3 is doing real work, not bookkeeping.
- **(P5) Route B** remains conditional (bilinear source enumeration).

## One-line summary

Plan 1 = "make BDV constructive": replace BDV's sequential
selection-plus-compactness contradiction by a single penalised
selection map preserving the deficit-to-asymmetry ratio, then run BDV's
own regularity + nearly-spherical second variation with tracked
constants. Its soundness rests on (P1) the single-set selection bound
genuinely removing the contradiction, and (P3) the small-`C^{2,γ_0}`
bootstrap.
