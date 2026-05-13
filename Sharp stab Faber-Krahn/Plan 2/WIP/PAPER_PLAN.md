# Plan 2 LaTeX Paper Assembly — Agent Chain Plan

This directory contains the LaTeX building blocks of the Plan 2 paper
(no-selection, no-graph, no-Schauder proof of sharp quantitative
Faber–Krahn stability). Following the Plan 1 / Final/ pattern, the
proof is split into 7 self-contained building blocks plus a master
document, each as a separate `.tex` file.

## Pass 1: initial drafts (parallel)

Seven part-agents write their `WIP_X.tex` from the Plan 2 markdown
sources. Each agent matches the style of the corresponding Plan 1
Final/ block (article class, theorem environments numbered by
section, shared macros, cross-references via `\cite` to siblings).

| File | Topic | Sources |
|------|-------|---------|
| `WIP_LevelSetIdentity.tex` | Exact deficit identity on reduced-boundary levels | `agent1-finite-perimeter-identity.md` |
| `WIP_MetricFramework.tex` | $\mathcal X$, metric first variation, per-$\rho$ velocity defect | `agent3-metric-first-variation.md` (+ Wave 2 C §C2 Sobolev–Sard citation patch) |
| `WIP_CentroidBound.tex` | H¹ centroid bound — the new structural input | `wave3-F-h1-center-bound.md` |
| `WIP_SpaceTimeIdentity.tex` | Space-time $\Pi$ identity + (B²-int) via slicing-then-squaring | `wave3-G-route-delta-assembly.md` §1–§4 + `wave3-J-route-delta-repair.md` |
| `WIP_WeightedMetricTrace.tex` | Integrated action → pointwise endpoint at $\widehat\rho$ | `agent4-weighted-metric-trace.md` + `wave2-B-kinetic-bound.md` + `wave3-G-route-delta-assembly.md` §5.3 |
| `WIP_BoundaryLayerTransfer.tex` | Transfer $E_{\widehat\rho}\to\Omega$; bounded sharp Saint–Venant | `metric-finite-perimeter-closure.md` §6 + `level-set-deficit-identity.md` Lemma 8.3 |
| `WIP_GlobalAssembly.tex` | Bounded reduction + Kohler–Jobin transfer → sharp Faber–Krahn | `agent5-final-assembly.md` (citing existing `Final/BoundedReduction.tex` and `Final/KohlerJobinTransfer.tex`) |

## Pass 2: master and audit

A master agent writes `WIP_master.tex` (intro, abstract, theorem
statement, chained statements, bibliography). It also performs a
light audit of the seven part files for notational consistency,
missing cross-references, and statement compatibility.

## Pass 3 (if needed): targeted fixes

If Pass 2 finds substantial issues, individual fix passes are
launched on the affected `WIP_X.tex` files.

## Shared conventions

- LaTeX article class, 11pt, `a4paper,margin=1in`.
- `\R, \Fr, \Om, \Otilde, \eps` macros as in Plan 1 Final/.
- Theorem environments numbered by section.
- Citations to siblings: `\cite{LevelSetIdentity}`, etc.
- Bibliography entries keyed: `LevelSetIdentity`, `MetricFramework`,
  `CentroidBound`, `SpaceTimeIdentity`, `WeightedMetricTrace`,
  `BoundaryLayerTransfer`, `GlobalAssembly`.
- External references shared with Plan 1 Final/master.tex.

## Post-audit corrections incorporated

The LaTeX writeup reflects all corrections from the Plan 2 audit chain:

1. **Centroid choice (Wave 3 F).** All centre-fields are the centroid
   $\bar z_\rho$, not the FvHT block centre or Fraenkel centre.
   Centroid–Fraenkel offset $O(\sqrt{\delta_T})$ absorbed into
   constants (Wave 2 C §C1).

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
