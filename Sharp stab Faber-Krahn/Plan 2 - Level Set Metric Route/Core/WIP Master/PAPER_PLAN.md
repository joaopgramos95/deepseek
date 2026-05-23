# Plan 2 LaTeX Paper Assembly — Agent Chain Plan

This directory contains the LaTeX building blocks of the Plan 2 paper
(no-selection, no-graph, no-Schauder proof of sharp quantitative
Faber–Krahn stability). The current shortest proof is recorded in
`WIP_master.tex`: it uses seven WIP blocks plus the Plan 1
bounded-reduction / Kohler–Jobin imports. `WIP_CentroidBound.tex` and
`WIP_SpaceTimeIdentity.tex` remain auxiliary diagnostics.

## Pass 1: initial drafts (parallel)

Seven part-agents write their `WIP_X.tex` from the Plan 2 markdown
sources. Each agent matches the style of the corresponding Plan 1
Final/ block (article class, theorem environments numbered by
section, shared macros, cross-references via `\cite` to siblings).

| File | Topic | Sources |
|------|-------|---------|
| `WIP_LevelSetIdentity.tex` | Exact deficit identity on reduced-boundary levels | `agent1-finite-perimeter-identity.md` |
| `WIP_MetricFramework.tex` | $\mathcal X$, metric first variation, per-$\rho$ velocity defect | `agent3-metric-first-variation.md` (+ Wave 2 C §C2 Sobolev–Sard citation patch) |
| `WIP_FJCenterBridge.tex` | Same-centre Fusco--Julin package + radial/homothetic trace bridge | May 14 bridge pass |
| `WIP_TrimmedVelocityRepair.tex` | Self-truncated velocity defect replacing Hyp-G(lower) | May 14 repair pass |
| `WIP_WeightedMetricTrace.tex` | Conditional integrated action / kinetic / endpoint trace | `agent4-weighted-metric-trace.md` + `wave2-B-kinetic-bound.md` + trimmed velocity repair |
| `WIP_BoundaryLayerTransfer.tex` | Transfer $E_{\widehat\rho}\to\Omega$; bounded sharp Saint–Venant | `metric-finite-perimeter-closure.md` §6 + `level-set-deficit-identity.md` Lemma 8.3 |
| `WIP_GlobalAssembly.tex` | Bounded reduction + Kohler–Jobin transfer → sharp Faber–Krahn | `agent5-final-assembly.md` (citing existing `Final/BoundedReduction.tex` and `Final/KohlerJobinTransfer.tex`) |

Auxiliary, not load-bearing in the current shortest route:

| File | Topic |
|------|-------|
| `WIP_CentroidBound.tex` | H¹ centroid bound |
| `WIP_SpaceTimeIdentity.tex` | Space-time $\Pi$ identity + slicing-then-squaring diagnostics |

## Pass 2: master and audit

A master pass writes `WIP_master.tex` as the compact proof program
(target theorem, normalisation, chained estimates, and audit
checklist). It also records which WIP files are load-bearing and which
are auxiliary.

## Pass 3 (if needed): targeted fixes

If Pass 2 finds substantial issues, individual fix passes are
launched on the affected `WIP_X.tex` files.

## Shared conventions

- LaTeX article class, 11pt, `a4paper,margin=1in`.
- `\R, \Fr, \Om, \Otilde, \eps` macros as in Plan 1 Final/.
- Theorem environments numbered by section.
- Citations to siblings: `\cite{LevelSetIdentity}`, etc.
- Bibliography entries keyed: `LevelSetIdentity`, `MetricFramework`,
  `FJCenterBridge`, `TrimmedVelocityRepair`, `WeightedMetricTrace`,
  `BoundaryLayerTransfer`, `GlobalAssembly`.
- External references shared with Plan 1 Final/master.tex.

## Post-audit corrections incorporated

The LaTeX writeup reflects all corrections from the Plan 2 audit chain:

1. **Centroid route demoted.** The centroid field is auxiliary only.
   The load-bearing route now isolates a same-centre
   Fusco--Julin/radial-trace bridge in `WIP_FJCenterBridge.tex`.

2. **Sobolev–Sard citation (Wave 2 C §C2).** Cite Figalli–Maggi 2011
   App. A Thm. A.1.

3. **gmt-inputs §1 rewrite (Wave 2 C §C3 + Wave 2 D §H-7 revision).**
   (1.2) is attributed to (B²-int) — the integrated form — and
   closed via the present route δ, NOT to a pointwise (R) statement.

4. **Slicing-then-squaring (Wave 3 J).** Agent G's broken Cauchy–
   Schwarz proof of (G4) §5.2 is replaced by the direct slicing
   decomposition $T_1 = T_1^{\rm rad,slic} + T_1^{\rm tan}$, squaring
   before integrating, exploiting $|EΔB_\rho|^2 \le C\Pi$.

5. **Honesty about open per-ρ inputs.** Pointwise (R) / (B²) /
   gmt-inputs (1.2)/(2.4) are explicitly NOT used; the paper closes
   only their integrated form, which is what Plan 2's chain actually
   needs.

6. **Hyp-G(lower) removed from the load-bearing route.** The current
   metric trace uses `WIP_TrimmedVelocityRepair.tex`: on
   Fusco–Julin good levels, the low-gradient part of the level surface
   is charged directly by `D_H`, so no pointwise lower gradient bound is
   assumed.

7. **Current truthful conditionality.**
   `WIP_LevelSetIdentity.tex` is repaired and load-bearing.
   `WIP_MetricFramework.tex` now states the finite-perimeter
   first-variation theorem conditionally on an upper-gradient recovery
   theorem.
   `WIP_WeightedMetricTrace.tex` no longer hides unsupported `A0`
   claims; it states explicit bad-level kinetic hypotheses and a
   same-centre FJ trace hypothesis.
