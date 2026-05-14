# Plan 3 Deployment — Synthesis

Outcome of the seven parallel agents launched from
`Plan 3/claude-agent-deployment.md`.

## Bottom-line verdict

The Plan 3 hybrid route (outer-collar graph entry from `D_H + D_I`,
followed by Plan-1-style perturbative closure) **does not close as
originally posed**. Two of the seven agents return obstructions
strong enough to redirect the program:

- **Agent 2** (graph entry): smallness of `D_H + D_I` gives
  FMP / Fusco–Julin / weighted-Serrin defect statements, none of which
  delivers a Lipschitz graph. The missing ingredient is a uniform
  two-sided density/nondegeneracy package for torsion levels of
  *arbitrary* `Ω`. Existing Serrin-stability theorems take Lipschitz
  graphs as **input**, not output.
- **Agent 5** (Serrin survey): `D_H` natively produces only a weighted
  `L²` variance of `|∇u|`. *No* Serrin-stability theorem in the
  literature is compatible with that native norm and outputs graph
  entry. Magnanini–Poggesi is the only candidate stated in `L²(∂D)`
  and it outputs Hausdorff closeness, not `C^{1,α}` graphs.
- **Agent 6** (hybrid with selected collar): the hybrid can be **stated
  rigorously** as a conditional theorem, but its interface step needs
  the BDV regularity package, which is available only on `Ũ`
  (the selected minimiser), not on `Ω`. Once `Ũ` is in hand, Plan 1
  already closes the proof and Plan 2 becomes decorative.

Agents **1, 3, 4** are positive conditional results: they show that
*if* graph entry is granted, the rest of the route (good-level
extraction, graph cohesion, one-level perturbative extraction) goes
through cleanly on a fixed outer annulus `[ρ_*, 1]`, `ρ_* > 0`.

Agent **7** identifies the **cheapest** missing input that would still
let the route close — and it is **not** graph entry. It is the
integrated `L²` normal-oscillation bound (B²-int), which reduces to a
single open lemma:

> **(G2)** — the ρ-Fubini profile-gap conversion with moving centroid
> centre, `Plan 2/wave3-G-route-delta-assembly.md` §3.

Everything in the chain *except* (G2) is already proved.

## Per-agent summary

| # | Task | Output | Verdict |
|---|------|--------|---------|
| 1 | Outer-collar good-level extraction | Proposition 3.1 (good levels in `t`-collar); Proposition 4.1 conditional on coarea hypothesis (A) | Pure Plan 2; proves `sqrt(δ_T)`-scale collar with good-level mass `1 − O(sqrt(δ_T)/η)` |
| 2 | Graph entry from `D_H + D_I` | Three defect statements (FMP, FJ, weighted-Serrin variance); explicit obstruction at (G1)–(G3) | Pure `D_H + D_I` smallness does **not** imply graph entry on arbitrary `Ω` |
| 3 | Graph cohesion in graph regime | Theorem 5.1 + Corollary 6.2: graph-entry level + (B) + (C) ⇒ foliation gauge on `[ρ_*, 1]` with upper-bound action (F) | Pure Plan 2; conditional on (G0)+(B)+(C) |
| 4 | One-level perturbative extraction | Three-Chebyshev extraction: action bound + graph entry + cohesion ⇒ ∃ `ρ̂` with `widetilde δ ≤ C δ_T`, matching `H^{1/2}` input of `NearlySphericalClosure` | Pure Plan 2; conditional on (A2)+(A3) |
| 5 | Serrin-stability survey | Theorem table over Magnanini–Poggesi, ABR, BNST, CMV, CV; norm-match verdict | **No** existing Serrin theorem is compatible with native `D_H` and outputs graph entry |
| 6 | Hybrid with selected collar | Conditional theorem (a)–(d) with Interface Lemma I | Hybrid does not genuinely simplify; reduces to Plan 1; useful only diagnostically |
| 7 | Obstruction report | Cheapest missing input is **not** graph entry; it is (G2) — ρ-Fubini profile-gap with moving centroid | Pure Plan 2; closes the chain if (G2) closes |

## Where the route now stands

Two coherent program-level conclusions emerge.

**A. The intended Plan 3 program (graph entry from `D_H + D_I`,
followed by Plan-1-style closure) is blocked at graph entry.** Both
Agent 2 and Agent 5 give independent reasons why this step does not
go through with the available technology. Agent 6 confirms that
retreating to a selected hybrid does not buy back the sharp exponent.

**B. There is a strictly cheaper route, identified by Agent 7.**
The chain runs end-to-end without ever forming a graph, **if**
Wave 3 Agent G's sub-claim (G2) — the ρ-Fubini profile-gap conversion
with moving centroid centre — closes. (G2) is flagged open by
`Plan 2/wave3-J-route-delta-repair.md`'s 2026-05-14 re-audit. Every
other brick (Agent 1 deficit identity, Lemma 8.1 profile gap,
Wave 3 F H¹-centroid bound, Wave 3 G §2 Fubini identity, the
`sqrt(δ)`-collar transfer of §2 of
`Plan 2/outer-foliation-entry-proof-attempt.md`, Plan 1
`GraphEntry`/`NearlySphericalClosure`) is proved.

## Recommendation for the next wave

Focus the next push on **(G2)** rather than on graph entry. If (G2)
closes, the chain delivers `A(Ω)² ≤ C(n, R) δ_T(Ω)` purely inside
Plan 2, with no Plan 1 hybrid, no graph chart, and no Serrin stability.

The agents 1, 3, 4 results remain useful: they package the
"if graph entry is granted" half of the route into clean, conditional
theorems, which is the right archival form even if the focus shifts
to the (G2) route.

## Provenance note

Agents 2 and 5 wrote their own full `.md` files via the sub-agent
Write tool. Agents 3 and 6 returned the full deliverable as text in
their final message (sub-agent Write was denied for them); the parent
relayed the content into `Plan 3/`. Agents 1, 4, 7 returned only
summary blocks (full Write attempts were denied at the sub-agent
permission layer and not echoed in their final messages); the parent
captured the substantive mathematical content of each summary into
its file. All seven deliverables now live in `Plan 3/`.
