# Agents Deployed — Manuscript Assembly Pipeline

This file lists all 21 agents in the manuscript assembly pipeline,
their assigned tasks, deliverables, and current deployment status.

The numbering matches `MANUSCRIPT_ASSEMBLY_AGENTS.md`. Agents 2–18
may not begin work until Agents 0 and 1 have produced the notation
register, source map, and bibliography inventory.

| # | Agent | Task | Deliverable | Status |
|---|---|---|---|---|
| 0 | Assembly Lead | Create the working manuscript directory; fix global notation and source map; record list of all deployed agents | `Manuscript/00_notation_register.md`, `Manuscript/source_map.md`, `Manuscript/agents_deployed.md` | **Deployed (this pass).** Outputs in place. |
| 1 | Bibliography and Related Work Inventory | Build the bibliography inventory before the Introduction is written | `Manuscript/04_references_audit.md` | **To be deployed next.** Reads: `Final/master.tex` bibliography, `Plan 2/WIP/WIP_master.tex` bibliography, source map item set F. Must resolve flag G1 (B8 source) and G2 (Nicola–Tilli). |
| 2 | Preliminaries — Geometric Measure Theory | Draft finite-perimeter and coarea preliminaries | Section draft in `Manuscript/01_preliminaries_draft.tex` (Part A items) | Pending Agents 0 & 1. |
| 3 | Preliminaries — Torsion, Rearrangement, Deficits | Draft torsion and rearrangement preliminaries | Section draft in `Manuscript/01_preliminaries_draft.tex` (Part B items) | Pending. |
| 4 | Preliminaries — Quantitative Isoperimetry and Oscillation | Draft quantitative isoperimetric preliminaries | Section draft in `Manuscript/01_preliminaries_draft.tex` (Part C items, including divergence identity for `β(E,z)²`) | Pending. |
| 5 | Plan 1 — Selection Principle | Write full selection-principle part of Plan 1 (D.1) | Subsection in `Manuscript/02_plan1_draft.tex` | Pending. |
| 6 | Plan 1 — Graph Entry and Regularity | Write graph-entry and Schauder/interpolation part of Plan 1 (D.2) | Subsection in `Manuscript/02_plan1_draft.tex` | Pending. |
| 7 | Plan 1 — Nearly Spherical Closure and Saint–Venant | Write BDV nearly-spherical closure + sharp Saint–Venant in bounded class (D.3) | Subsection in `Manuscript/02_plan1_draft.tex` | Pending. |
| 8 | Plan 1 — Kohler–Jobin and Faber–Krahn Transfer | Write final Plan 1 transfer to Faber–Krahn (D.4) | Final subsection in `Manuscript/02_plan1_draft.tex` | Pending. |
| 9 | Plan 2 — Level-Set Deficit Identity | Write exact level-set deficit identity with full finite-perimeter detail (E.1) | First subsection in `Manuscript/03_plan2_draft.tex` | Pending. |
| 10 | Plan 2 — Metric Framework | Write the metric quotient and first-variation theorem (E.2) | Subsection in `Manuscript/03_plan2_draft.tex` | Pending. Must **not** assume global Lipschitz boundary regularity. |
| 11 | Plan 2 — Fusco–Julin Center and Oriented Radial Trace | Write the centre package and the oriented radial trace lemma in full detail (E.3) | Subsection in `Manuscript/03_plan2_draft.tex` | Pending. **Critical load-bearing block.** Vector field `X(x) = ||x − z̄_ρ|/ρ − 1| · (x − z̄_ρ)/|x − z̄_ρ|` with full finite-perimeter divergence/truncation argument. No ray-slicing shortcut. |
| 12 | Plan 2 — Integrated Action and Weighted Metric Trace | Write integrated action + weighted metric trace argument (E.4) | Subsection in `Manuscript/03_plan2_draft.tex` | Pending. Must include good/bad-level Markov, kinetic Lebesgue bound, abstract weighted trace lemma, existence of `ρ̂`. |
| 13 | Plan 2 — Boundary-Layer Transfer and Global Assembly | Write Plan 2 final transfer and global conclusion (E.5) | Final subsection in `Manuscript/03_plan2_draft.tex` | Pending. Must square the `O(√{δ_T})` layer after transfer, not before. |
| 14 | Plan 2 Auxiliary Route Note | Write a short optional note on centroid / space–time Π route (E.6) | Optional remark/subsection in `Manuscript/03_plan2_draft.tex` | Pending. **Explicitly marked auxiliary**; not load-bearing. |
| 15 | Internal Audit Agent — Plan 1 | Audit Plan 1 draft against source blocks | `Manuscript/audit_plan1.md` | Pending; runs after Agents 5–8. |
| 16 | Internal Audit Agent — Plan 2 | Audit Plan 2 draft against source blocks | `Manuscript/audit_plan2.md` | Pending; runs after Agents 9–14. Must check that no load-bearing use of the centroid Π-route is made. |
| 17 | Notation and Normalization Unification Agent | Unify notation across the whole manuscript after Plan 1 and Plan 2 drafts exist | `Manuscript/06_notation_unification_report.md` + patch instructions | Pending; runs after Agents 15 and 16. |
| 18 | Introduction and Historical Story Agent | Write the Introduction last, after references and notation are unified | `Manuscript/05_intro_story_draft.tex` | Pending; runs after Agent 17. |
| 19 | Final Assembly Agent | Assemble the final TeX manuscript: integrate all audited drafts, create theorem environments and numbering, include the bibliography, compile | `Manuscript/main.tex` | Pending. |
| 20 | Final Adversarial Audit Agent | Last review after `Manuscript/main.tex` compiles | `Manuscript/final_adversarial_audit.md` | Pending. |

## Deployment order (assembly schedule)

1. **Agent 0** (this pass): create directory, register, map, agent list. ✅
2. **Agent 1**: bibliography inventory. → next.
3. **Agents 2, 3, 4** in parallel: preliminaries.
4. **Agents 5, 6, 7, 8** in parallel (after Agent 0 fixes notation): Plan 1.
5. **Agents 9, 10, 11, 12, 13** in parallel (after Agent 0): Plan 2.
   **Agent 14** (auxiliary remark) optional, in parallel.
6. **Agent 15** audits Plan 1.
7. **Agent 16** audits Plan 2.
8. **Agent 17** unifies notation.
9. **Agent 18** writes Introduction.
10. **Agent 19** assembles `main.tex`.
11. **Agent 20** final adversarial audit.

## Hard stop conditions (per brief)

Any agent must halt and raise a blocking issue if it encounters:

- a theorem used without proof or reference;
- a hidden smoothness assumption inside a finite-perimeter section;
- a rate loss converting `δ_T → √{δ_T}` that is not later squared;
- an unconditional statement relying on the conditional Bernoulli
  spectral closure (Plan 1 alternate);
- an unconditional statement relying on the centroid Π-route
  (Plan 2 auxiliary);
- inconsistent normalisation between Plan 1 and Plan 2 final
  theorems.

## Cross-cutting warnings for downstream agents

1. **Dimension symbol**: write `n`, never `N`. The Plan 1 source files
   (`Final/*.tex`) use `N`; Agents 5–8 must convert at draft time.
2. **`R` symbol**: never use `R = (|Ω|/ω_n)^{1/n}` without renaming
   to `R_Ω`; reserve `R` for the confining radius.
3. **`α` symbol**: BDV smooth asymmetry vs coarea `α(t)`. Use
   `α_BDV(Ω)` when both occur. Agent 6's draft must take care.
4. **`Ω̃`**: Plan 1 = volume-normalised companion; Plan 2 space–time
   identity domain renamed `Ω_Π`. Agent 14 must use the renamed form.
5. **`σ`**: Fubini density. The BDV main-theorem constant is
   `c_FK^{BDV}(n)`, not `σ(n)`.
6. **Centre field**: bulk centroid `z̄_ρ` throughout. Agent 11 must
   not silently switch to a Fraenkel-optimal or FvHT centre.
7. **Sharp exponent preservation**: at the boundary-layer transfer
   step (Agent 13), the squaring `(a + b)² ≤ 2a² + 2b²` is applied
   **after** the transfer, not before. The `O(√{δ_T})` layer becomes
   `O(δ_T)` after squaring.
8. **Constant tracking**: every constant `C, c, δ_0, κ` must declare
   its dependence on `(n)`, `(n, R)`, or `(n, R, ρ_*)` at first use.
   Bare `C` is not permitted.
9. **Hypothesis class**: stated theorems must cover open
   `Ω ⊂ ℝⁿ` with finite measure; bounded `Ω ⊂ B_R` is allowed only
   in the bounded chain, and the bounded reduction step removes the
   `R`-dependence.
