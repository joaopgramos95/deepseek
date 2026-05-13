# Manuscript Final Source Map

Produced by Agent 19 (Final Assembly Agent). This file links each
manuscript section / theorem / lemma in `Manuscript/main.tex` back
to (i) the agent draft that produced it and (ii) the original source
files (Plan 1 / Plan 2 / Final / WIP).

For the global inventory of building blocks (E*, C*, B*, D* items)
see `Manuscript/source_map.md` (Agent 0). For the bibliographic audit
of external references see `Manuscript/04_references_audit.md`
(Agent 1).

## 1. Manuscript file layout

`Manuscript/main.tex` is the single coherent TeX manuscript. It loads
the canonical macros (`macros.tex`, Agent 17) and inputs the section
drafts in the following order:

| Section | File | Origin |
|---------|------|--------|
| Introduction | `05_intro_story_draft.tex` | Agent 18 |
| Preliminaries | `01_preliminaries_draft.tex` | Agent 19 wrapper |
| Plan 1 proof | `02_plan1_draft.tex` | Agent 19 wrapper |
| Plan 2 proof | `03_plan2_draft.tex` | Agent 19 wrapper |
| References | `references.bib` via `\bibliography{references}` | Agent 1 + Agent 19 stubs |

The three wrapper files (`01_`, `02_`, `03_`) declare the section
heading and `\input` the agent-specific drafts in the canonical order.

## 2. Preliminaries (Section 2 of `main.tex`)

Wrapper: `01_preliminaries_draft.tex`. Subsections:

| Subsection | Source file | Agent | Original sources |
|------------|-------------|-------|------------------|
| Geometric measure theory | `preliminaries_gmt.tex` | Agent 2 | Maggi 2012 (Thm 12.1, 13.1, 15.5, 15.9, 16.3); AFP 2000 (Thm 2.38, 3.40, 3.59); Figalli–Maggi 2011 (App. A); Federer 1969 (§2.13); Castaing–Valadier 1977 (Thm III.6, III.8) |
| Torsion, rearrangement, deficits | `preliminaries_torsion.tex` | Agent 3 | Pólya–Szegő 1951; Talenti 1976; Kawohl 1985; Henrot 2006; Kesavan 2006; Bandle 1980; BDV 2015 (§2); Brasco 2014 (Thm 3.3, KJ); BBC 1975 |
| Quantitative isoperimetry | `preliminaries_quant_isoperimetry.tex` | Agent 4 | FMP 2008; FMP 2010; Fusco–Julin 2014 (Thm 1.1); Maggi 2008 survey; Fusco survey |

## 3. Plan 1: selection-principle route (Section 3 of `main.tex`)

Wrapper: `02_plan1_draft.tex`. Subsections:

| Subsection | Source file | Agent | Original sources |
|------------|-------------|-------|------------------|
| Quantitative selection principle | `plan1_selection.tex` | Agent 5 | `Plan 1/quantitative-selection-principle.tex`; `Final/SelectionPrinciple.tex`; BDV 2015 (§4 selection, Lemmas 4.6, 4.9, 4.12, 4.16; Thm 4.18) |
| Graph entry and regularity | `plan1_graph_entry.tex` | Agent 6 | `Plan 1/graph-entry-closure.tex`; `Final/GraphEntry.tex`; `Final/SchauderInterpolation.tex`; Alt–Caffarelli 1981; Kinderlehrer–Nirenberg 1977; Lieberman 1986 (Li86a/b); Gilbarg–Trudinger; Bergh–Löfström |
| Nearly-spherical closure | `plan1_nearly_spherical.tex` | Agent 7 | `Plan 1/route-A-summary.tex`; `Final/NearlySphericalClosure.tex`; `Final/SaintVenantAssembly.tex`; BDV 2015 (Thm 3.3, Lem 5.1–5.2); Fuglede 1989 |
| Bounded reduction + Kohler–Jobin | `plan1_kohler_jobin_transfer.tex` | Agent 8 | `Plan 1/faber-krahn-transfer.tex`; `Final/BoundedReduction.tex`; `Final/KohlerJobinTransfer.tex`; BDV 2015 (Lem 5.3); Brasco 2014 (Thm 3.3) |

Plan 1 closing theorem: `thm:plan1-FK-upper-intro`, statement of
$\Fr(\Om)^2\le C_{\rm FK}(n)\,\deltaFK(\Om)$, proved in
`plan1_kohler_jobin_transfer.tex`.

## 4. Plan 2: level-set / metric route (Section 4 of `main.tex`)

Wrapper: `03_plan2_draft.tex`. Subsections:

| Subsection | Source file | Agent | Original sources |
|------------|-------------|-------|------------------|
| Exact level-set deficit identity | `plan2_levelset_identity.tex` | Agent 9 | `Plan 2/WIP/WIP_LevelSetIdentity.tex`; `Plan 2/level-set-deficit-identity.md`; Talenti 1976; BBC 1975; AFP 2000 (Thm 3.40, 3.99); Maggi 2012 (Thm 13.1) |
| Metric framework / first variation | `plan2_metric_framework.tex` | Agent 10 | `Plan 2/WIP/WIP_MetricFramework.tex`; `Plan 2/gmt-inputs-for-metric-closure.md`; `Plan 2/metric-finite-perimeter-closure.md`; AGS 2008 (Def 1.1.1, Thm 1.1.2); AFP 2000 (Thm 2.38, 3.84) |
| Fusco–Julin centre and oriented radial trace | `plan2_fj_center_radial_trace.tex` | Agent 11 | `Plan 2/WIP/WIP_WeightedMetricTrace.tex`; `Plan 2/wave3-J-route-delta-repair.md`; `Plan 2/wave3-F-h1-center-bound.md`; Fusco–Julin 2014; Federer 1969 (§2.13); Maggi 2012 (Thm 16.3) |
| Integrated action + weighted metric trace | `plan2_weighted_metric_trace.tex` | Agent 12 | `Plan 2/WIP/WIP_WeightedMetricTrace.tex`; `Plan 2/WIP/WIP_MetricFramework.tex`; `Plan 2/WIP/WIP_LevelSetIdentity.tex`; Talenti 1976 (bad-set Lebesgue bound); Kesavan 2006 (Thm 1.3.2) |
| Boundary-layer transfer + final theorem | `plan2_boundary_layer_assembly.tex` | Agent 13 | `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`; `Plan 2/WIP/WIP_GlobalAssembly.tex`; `Final/BoundedReduction.tex`; `Final/KohlerJobinTransfer.tex` |
| Auxiliary centroid / space-time Π note | `plan2_aux_centroid_note.tex` | Agent 14 | `Plan 2/WIP/WIP_CentroidBound.tex`; `Plan 2/WIP/WIP_SpaceTimeIdentity.tex` (auxiliary, NOT load-bearing per `audit_plan2.md`) |

Plan 2 closing theorem: `thm:plan2-FK-intro`, statement of
$\deltaFK(\Om)\ge c_{\rm FK}(n)\,\Fr(\Om)^2$, proved in
`plan2_boundary_layer_assembly.tex` with the explicit dimensional
constant $c_{\rm FK}(n)$ identical to the one in
`thm:plan1-FK-upper-intro`.

## 5. Bibliography

The unified `references.bib` (Agent 1, with stubs added by Agent 19
for keys that appear in section drafts but were not in Agent 1's
inventory: `Wave2A`, `Wave3F`, `Wave3J`, `WIP_*`, `Plan2-LevelSet`,
`Plan1Selection`, `Final-*`, `AKN-Faber-Krahn`, `AltCaffarelli`,
`BDV2013`, `Li86`, alias entries for `Henrot`, `Kawohl1985`,
`PolyaSzego`, `FMP-torsion`, etc.) is loaded by
`\bibliography{references}` in `main.tex`. Citation style: `plain`.

## 6. Modifications applied by Agent 19

1. **Label-collision repairs**. The following labels collided across
   drafts and were renamed (the canonical use is in preliminaries):
   - `eq:KJ-linear`, `eq:KJ-ptwise`, `eq:onevar`, `lem:onevar`
     renamed to `eq:plan1-KJ-linear`, `eq:plan1-KJ-ptwise`,
     `eq:plan1-onevar`, `lem:plan1-onevar` inside
     `plan1_kohler_jobin_transfer.tex`.
   - `eq:FJ-scaled`, `thm:FJ-scaled` renamed to `eq:plan2-FJ-scaled`,
     `thm:plan2-FJ-scaled` inside the Plan 2 draft files.
   - `eq:centroid-def` renamed to `eq:aux-centroid-def` inside
     `plan2_aux_centroid_note.tex`.

2. **Label aliases for cross-section references**. The following alias
   labels were added next to existing canonical labels to satisfy
   cross-section references that used non-canonical names:
   - `lem:fj-center-package` ↔ `lem:FJ-package`.
   - `thm:mf-AC` ↔ `thm:metric:AC`.
   - `thm:radial-trace` ↔ `thm:fj-radial-divergence`,
     `lem:radial-trace-master`.
   - `thm:wmt:trace` ↔ `thm:weighted-trace`.
   - `thm:deficit` ↔ `thm:lsid:identity`, `thm:plan2-levelset-id`.
   - `lem:DH-DI-pos` ↔ `lem:lsid:CS-defect`, `prop:lsid:CS-defect`.
   - `lem:cov` ↔ `lem:lsid:DHDI-psi`.
   - `thm:plan2-FJ-scaled` ↔ `prop:fj-scaled`.
   - `lem:mf-attain` ↔ `lem:metric:attain`,
     `lem:metric-translation-volume`.

3. **Section-level label aliases** added at the top of each `\input`
   in `02_plan1_draft.tex` and `03_plan2_draft.tex` for cross-section
   references such as `subsec:metric-framework`,
   `subsec:level-set-identity`, etc.

4. **Section-heading downgrades**. The preliminaries drafts were
   downgraded one heading level (so `\section` → `\subsection` and
   `\subsection` → `\subsubsection`) to fit under the global
   `\section{Preliminaries}`. The starred-section headings in
   `plan2_fj_center_radial_trace.tex`,
   `plan2_weighted_metric_trace.tex`, and
   `plan2_aux_centroid_note.tex` were converted to non-starred,
   one level lower.

5. **Bibliography stubs**. Missing keys were added to `references.bib`
   as alias entries or internal Plan-1/Plan-2 working-note stubs (see
   Agent 19 block at the end of `references.bib`).

6. **Embedded local bibliography disabled**. The local
   `thebibliography` block at the end of `preliminaries_torsion.tex`
   was wrapped in `\iffalse … \fi` to avoid duplicate `\bibitem`
   warnings.

7. **Macros added**. `\Div`, `\Lip`, `\diam`, `\hH`, `\NS`, `\fint`
   were added to `macros.tex` to satisfy drafts that used them.
   `\rhad` was redefined as `{\widehat{\rho}}` (brace-wrapped) to
   prevent double-subscript / missing-brace errors when used as a
   subscript.

8. **Punctual edits**. `u^*_\Bstar` was rewritten as
   `u^*_{\Bstar}` in `preliminaries_torsion.tex` to avoid double
   superscript; `\BDValpha` was wrapped in math mode in
   `plan1_nearly_spherical.tex` (line 167); the `\cite` keys
   `Final/BoundedReduction.tex`, `Final/KohlerJobinTransfer.tex`,
   `wave2-B-kinetic-bound.md`, `agent4-weighted-metric-trace.md`
   were normalised to dot-free keys. The optional argument of one
   `remark` in `plan2_fj_center_radial_trace.tex` was wrapped in
   `{...}` to escape the `]` inside its math content.

## 7. Compilation status

`main.tex` compiles cleanly with the sequence
`pdflatex; bibtex; pdflatex; pdflatex` (exit code 0, no warnings).
Final document: 120 pages.

## 8. Cross-checks for Agent 20 (final audit)

The next agent should verify in particular:

- That the two final theorems
  (`thm:plan1-FK-upper-intro` and `thm:plan2-FK-intro`) really agree
  in normalisation and constant.
- That no load-bearing Plan 2 step references the auxiliary
  centroid / Π note (`plan2_aux_centroid_note.tex`); cf.
  `audit_plan2.md` and `audit_plan2_repair_report.md`.
- That every theorem citation actually exists in `references.bib`
  (Agent 19 added stubs for several keys; some of them are alias
  entries pointing to canonical entries — this is intentional but
  should be reviewed for bibliographic style).
- That the label aliases introduced in §6 above point to the
  intended mathematical object in every case where a cross-section
  reference uses the alias name.
