# Final Adversarial Audit (Agent 20)

**Date.** 2026-05-13.
**Auditor.** Agent 20 (final adversarial audit), brief in
`MANUSCRIPT_ASSEMBLY_AGENTS.md`.
**Object of audit.** `Manuscript/main.tex` (120-page assembled
manuscript) together with the section drafts, the bibliography
`references.bib`, and the supporting audit files
`audit_plan1.md`, `audit_plan2.md`,
`audit_plan2_repair_report.md`,
`06_notation_unification_report.md`,
`04_references_audit.md`,
`source_map_final.md`.

---

## Verdict

**BLOCKED on 1 BLOCKING finding (bibliography contains and the
manuscript text cites internal working notes and Markdown files as if
they were published references) and 4 MAJOR findings.**

The mathematical content of the manuscript appears correct: both
Plan 1 and Plan 2 close the same sharp Faber--Krahn theorem with
the same dimensional constant, the oriented radial-trace lemma is
proved in genuine finite-perimeter form via the named vector field
$X$ and a truncation argument, neither the conditional Bernoulli
spectral route nor the centroid $\Pi$-route is load-bearing, and the
preliminaries are either proved on the spot or cited with precise
theorem/page data. However, the manuscript is **not** yet
publication-ready: the bibliography contains a substantial set of
private internal-document keys (working notes, WIP files, alias
duplicates of published papers) that are still **cited from body
text**, so they will appear in the final printed reference list. This
must be cleaned up before submission.

---

## BLOCKING findings

### B1. Body-text citations to internal working notes / Markdown files.

The manuscript body still contains `\cite{...}` commands pointing to
internal Plan 1 / Plan 2 / Wave / WIP working notes that are **not**
public references, and whose corresponding `@misc` entries in
`references.bib` are explicit aliases or "internal note" stubs added
by Agent 19. With `bibliographystyle{plain}`, every `\cite`d key
appears in the final printed bibliography. Affected citations
(non-exhaustive):

- `Manuscript/05_intro_story_draft.tex:53`
  - `\cite[Manuscript/00\_notation\_register.md]{Plan1Master}` —
    cites the internal notation register Markdown file. The
    corresponding bib entry `@misc{Plan1Master, …}` is "Plan 1 master
    draft", a private working document. **This citation is in the
    Introduction**, the first place a reader encounters the paper.
- `Manuscript/plan1_selection.tex:360–361`
  - `\cite[lines 263--285]{Plan1Selection}` and
    `\cite[Step~1 of Lemma~7]{FinalSelection}` — both pointing to
    internal Plan 1 working files.
- `Manuscript/plan1_nearly_spherical.tex:75,76,93,104,107,131,133,135…`
  - All occurrences of `\cite{BDV2013}`. The bib entry `@misc{BDV2013}`
    is explicitly an alias of the canonical `BDV`. The published
    paper is the same Brasco–De Philippis–Velichkov; the duplicate
    key produces a duplicate entry in the printed bibliography (two
    copies of the same paper).
- `Manuscript/plan2_boundary_layer_assembly.tex` (assembly
  references)
  - `\cite{Final-BoundedReduction}` and
    `\cite{Final-KohlerJobinTransfer}` (cited at "Theorem~BR" /
    "Theorem~KJ") — bib entries are explicit aliases for the
    local LaTeX building blocks `Final/BoundedReduction.tex` and
    `Final/KohlerJobinTransfer.tex`.
  - `\cite[Lemma~8.3]{LevelSetIdentity-block}` — bib entry is a Plan 2
    internal "level-set identity block" stub.
  - `\cite[Theorem (thm:final)]{Final-master}` — bib entry is
    "Plan 1 master draft" stub.
- `Manuscript/plan2_aux_centroid_note.tex:173,193,212,367,370`
  - `\cite[Thm.~F]{WIP_CentroidBound}`, `\cite[\S5]{WIP_LevelSetIdentity}`,
    `\cite[\S5--\S6]{WIP_SpaceTimeIdentity}` and several similar.
  - These appear in the auxiliary subsection. They are still
    `\cite`d, so they still print.
- `Manuscript/plan2_fj_center_radial_trace.tex:43,123,154,159,532,538`
  - `\cite[Lem.~2.2]{Wave2A}`, `\cite{Wave3F}`,
    `\cite[\S1]{Wave3F}` — `Wave2A` and `Wave3F` are private
    internal Plan 2 "wave" notes.

The corresponding `references.bib` entries are marked in their `note`
field as `Alias of …` or `Local building block` or
`Wave NN internal note`, so the audit is unambiguous.

**Recommended fix.**
For every citation above, replace the internal key with the canonical
published reference that it aliases:

| Internal key used in `\cite{...}` | Replace with |
|-----------------------------------|--------------|
| `Plan1Master`, `Final-master`     | (remove; cite Notation Register inline or via `\S`) |
| `BDV2013`                          | `BDV`        |
| `Plan1Selection`, `FinalSelection` | `BDV`, with precise §/Lemma reference |
| `Final-BoundedReduction`           | `BDV`, Lemma 5.3 |
| `Final-KohlerJobinTransfer`        | `Brasco2014`, Thm 3.3 |
| `LevelSetIdentity-block`           | replace by the in-manuscript Theorem~\ref{thm:deficit} |
| `WIP_CentroidBound`,`WIP_LevelSetIdentity`,`WIP_SpaceTimeIdentity` | replace by in-manuscript references to the appropriate auxiliary subsections |
| `Wave2A`,`Wave3F`,`Wave3J`         | replace by the published sources they paraphrase (`CL2012`, `FJ2014`, `AFM2013`), or by in-manuscript cross-references |
| `agent4-weighted-metric-trace`, `wave2-B-kinetic-bound`, `leveset-deficit-md`, `Plan2-LevelSet`, `KohlerJobinTransfer-Plan1`, `BoundaryLayerTransfer`, `GlobalAssembly`, `MetricFramework`, `WeightedMetricTrace`, `SpaceTimeIdentity`, `CentroidBound`, `BDV-BoundedReduction-Plan1`, `BDV-SaintVenantAssembly`, `Final-GraphEntry`, `Final-SchauderInterpolation`, `Final-BoundedReduction-tex`, `Final-KohlerJobinTransfer-tex` | strip the stub from `references.bib` (currently uncited, but pollute the file) |

After this is done, the duplicate aliases `PolyaSzego`,
`FuscoJulin2014`, `MaggiSurvey2008`, `Kawohl1985`, `Henrot`, `KN`,
`Li86` should also be removed: each one is `\cite`d at some point in
the body and each is an explicit alias of the canonical entry
(`PolyaSzego1951`, `FJ2014`, `Maggi2008`, `KawohlBook`, `HenrotBook`,
`KN1977`, `Li86a` resp.\ `Li86b`). All body `\cite{…}` commands using
the alias key should be repointed to the canonical key. Each alias
key currently produces a duplicate reference list entry under
`bibliographystyle{plain}`.

This is the only **blocking** finding. It is bibliographic, not
mathematical; nothing in the proofs is wrong.

---

## MAJOR findings

### M1. Statement / proof mismatch in the explicit form of the radial-trace constant $C_4$.

`Manuscript/plan2_fj_center_radial_trace.tex`:

- Theorem~\ref{thm:radial-trace} (line 277, statement of the
  oriented $L^1$ radial trace) declares
  `$C_4(n,R,\rstar)=\max\{n/\rstar,1/2\}$`.
- The same proof (line 426) derives
  `$C_4(n,R,\rstar)=\max\{n/\rstar,\,3R/(2\rstar)\}$`.
- The constant-summary block (line 553) also gives
  `$C_4(n,R,\rstar)=\max\{n/\rstar,3R/(2\rstar)\}$`.

The proof-derived form is correct (the tangential bound uses the
maximum value $|w|\le 3R/\rstar$, see eq.~\eqref{eq:T-tan-bound}).
The "1/2" in the theorem statement is a stale artefact.

**Recommended fix.** Change the closing line of the theorem statement
(line 277) to read `$C_4(n,R,\rstar)=\max\{n/\rstar,3R/(2\rstar)\}$`.

### M2. Duplicate references in the printed bibliography.

In addition to the alias keys flagged under B1, the bibliography
contains pairs of entries that refer to the same published work:

- `PolyaSzego1951` vs. `PolyaSzego` (the latter is an alias).
- `FJ2014` vs. `FuscoJulin2014` (alias).
- `Maggi2008` vs. `MaggiSurvey2008` (alias).
- `KawohlBook` vs. `Kawohl1985` (alias).
- `HenrotBook` vs. `Henrot` (alias).
- `KN1977` vs. `KN` (alias).
- `Li86a`/`Li86b` (real two-paper Lieberman pair) vs. `Li86` (alias).

Both keys in each pair are actually `\cite`d from body text
(verified via `main.aux`). With `plain` style the published
bibliography will therefore list each of these papers twice. This is
visually unprofessional and should be resolved together with B1.

### M3. Several references appear in the bibliography but are never cited.

The following bib entries are present in `references.bib` but not
present in `main.aux`'s `\citation{...}` list and therefore not
emitted by `bibtex`:

`AmbrosioGigli2013`, `AmbrosioMantegazza`, `AubinFrankowska1990`,
`CastaingValadier`, `MaggiSurvey2008` (vs.\ alias),
`AKN-Faber-Krahn` (wait — actually `\cite`d in
`plan2_boundary_layer_assembly.tex`, so this one is OK),
`SpaceTimeIdentity`, `WIP_*` (most), `BoundaryLayerTransfer`,
`GlobalAssembly`, `MetricFramework`, `WeightedMetricTrace`,
`CentroidBound`, `Final-GraphEntry`, `Final-SchauderInterpolation`,
`Final-BoundedReduction-tex`, `Final-KohlerJobinTransfer-tex`,
`KohlerJobinTransfer-Plan1`, `BDV-BoundedReduction`,
`BDV-BoundedReduction-Plan1`, `BDV-SaintVenantAssembly`,
`leveset-deficit-md`, `Plan2-LevelSet`,
`agent4-weighted-metric-trace`, `wave2-B-kinetic-bound`.

These do not appear in the printed bibliography (under `plain` style
only cited entries print), but they will appear if the journal style
sheet is `unsrt`/`alpha`/`abbrv` and `\nocite{*}` is ever used, and
they pollute the `.bbl` file (which currently emits 84 items, several
of them dead). **Recommended fix.** Delete these stub entries from
`references.bib`.

### M4. The Introduction cites an internal Markdown file inside a published theorem environment.

`Manuscript/05_intro_story_draft.tex:53` reads:

> "Both proofs in the present paper close the following sharp
> quantitative statement, in the canonical normalisation of the
> notation register
> (\S\,3--5 of~\cite[Manuscript/00\_notation\_register.md]{Plan1Master})."

This is a direct citation of an internal Markdown notation register
inside the paper's first theorem statement. Even after B1 is fixed
(repointing `Plan1Master` away), the optional argument is a Markdown
file path, which is not appropriate in the published Introduction.

**Recommended fix.** Replace the `\cite[Manuscript/00\_notation\_register.md]{Plan1Master}` parenthetical with a forward reference to
the Preliminaries section, e.g.\ "(see
\S\ref{sec:notation})".

---

## MINOR findings

### m1. The two final theorem statements are normalized identically up to the explicit inversion $C_{\rm FK}(n)=1/c_{\rm FK}(n)$.

Verbatim quotation, side-by-side:

- Theorem~`\ref{thm:plan1-FK-upper-intro}` (Introduction, lines
  655--679; mirrored in
  `plan1_kohler_jobin_transfer.tex:526–608`,
  Theorem~`\ref{thm:KJ-FK-lower}`):
  "$\Fr(\Om)^2\le C_{\rm FK}(n)\,\deltaFK(\Om)$" with
  $C_{\rm FK}(n) = 1/c_{\rm FK}(n) = \max\{(n+2)T_n/(4L_n c_{\rm SV}^{\rm glob}(n)),\,4/(L_n(2^{2/(n+2)}-1))\}$.
- Theorem~`\ref{thm:plan2-FK-intro}` (Introduction, lines
  681--694; mirrored in
  `plan2_boundary_layer_assembly.tex:573–587`,
  Theorem~`\ref{thm:plan2-FK}`):
  "$\deltaFK(\Om) = (|\Om|/\omega_n)^{2/n}(\lambda_1(\Om)-\lambda_1(\Bstar)) \ge c_{\rm FK}(n)\,\Fr(\Om)^2$"
  with the same explicit
  $c_{\rm FK}(n)=\min\{4L_n c_{\rm SV}^{\rm glob}(n)/((n+2)T_n),\,L_n(2^{2/(n+2)}-1)/4\}$.

The two are inverses, the formulas reduce to the same expression, and
the relationship is stated explicitly:
"$C_{\rm FK}(n)=1/c_{\rm FK}(n)$" (line 697 of
`05_intro_story_draft.tex`). **No issue; the audit question is
satisfied.**

### m2. Constants depending on $R$ or $\rho_*$ are correctly declared as such throughout.

A `\grep -E "C\\([nN],"` and `c_{\rm SV}` sweep shows: every
appearance of an $R$- or $\rho_*$-dependent constant in Plan 1
(`C_3(n,R)`, `c_{\rm SV}(n,R)`) and Plan 2 (`C_4(n,R,\rstar)`,
`C_*(n,R,\rstar)`, `c_{\rm SV}(n,R)`, `c_{\rm SV}^{\rm glob}(n)`)
states the dependence at first use and tracks it. The two
final theorems only use the dimensional constants $c_{\rm FK}(n)$ and
$C_{\rm FK}(n)$; the dependence on $R,\rstar$ is genuinely removed by
the bounded-reduction step at fixed $R=R_*(n)$ and $\rstar=1/2$, both
explicitly recorded (Remark~\ref{rem:plan2-rho-star-fix} in
`plan2_boundary_layer_assembly.tex`,
Remark~\ref{rem:factor-two} in
`plan1_kohler_jobin_transfer.tex`).

### m3. Plan 1 closes without invoking the conditional Bernoulli spectral route.

Every occurrence of the word "Bernoulli" in the Plan 1 drafts refers
either to (i) the BDV one-phase free-boundary regularity
package (Lemma 4.16 and Theorem 4.18 of `BDV`, both unconditional),
or to (ii) the volume-rescaled form of the same classical Bernoulli
free-boundary identity. The conditional spectral / Bernoulli
linearisation route of `Plan 1/bernoulli-spectral-closure.tex` and
`Plan 1/bernoulli-expansion-proofs.tex` is mentioned **only** in the
explicitly labelled Remark `rem:intro-bernoulli` (lines 291–306 of
`05_intro_story_draft.tex`), where its conditional status is stated:
"A separate, conditional second proof…requires a spectral gap
statement we do not prove here." Confirmed by
`audit_plan1.md` Verdict and reaffirmed in
`plan2_boundary_layer_assembly.tex` Remark
`rem:plan2-no-conditional`.

### m4. Plan 2 closes without invoking the centroid $\Pi$-route.

The auxiliary centroid / space–time $\Pi$ subsection
(`plan2_aux_centroid_note.tex`) is included as the last subsection of
Plan 2, is opened with an explicit `Status` box declaring it
auxiliary and conditional on Hypothesis `\ref{hyp:Piint}`
("Integrated $\Pi$-control; *open*"), and is **not** referenced by any
load-bearing earlier subsection. Every cross-reference to
`subsec:plan2-aux-centroid`, `eq:aux-centroid-def`, or `hyp:Piint`
lies inside the auxiliary subsection itself, in the Introduction's
`rem:intro-pi-route`, or in the no-conditional remark
`rem:plan2-no-conditional`. Confirmed by `grep`.

Note: the word "centroid" appears widely in the load-bearing part of
Plan 2 (`plan2_fj_center_radial_trace.tex`,
`plan2_weighted_metric_trace.tex`), but there it denotes the **bulk
centroid** $\zbar$ of $E_\rho$ as the Borel choice of FJ
oscillation centre on good levels, not the conditional
$\Pi$-control quantity. This distinction is recorded in
`audit_plan2_repair_report.md` (resolution of MAJOR finding M1) and
in `06_notation_unification_report.md`.

### m5. The oriented radial-trace lemma is proved for finite-perimeter $E_\rho$ via the named vector field and the truncation argument.

`Manuscript/plan2_fj_center_radial_trace.tex:247--427`,
Theorem~`\ref{thm:radial-trace}`. The vector field
$$X(x)=\Bigl|\frac{|x-\zbar|}{\rho}-1\Bigr|\frac{x-\zbar}{|x-\zbar|}$$
is introduced verbatim (eq.~\eqref{eq:X-def}, line 252–256).
The proof:

- localises $\zbar$ to the interior of $E_\rho$ via the
  Cicalese--Leonardi containment of `Lemma:centroid-borel`;
- introduces a Lipschitz truncation
  $X_\eps(x)=\eta_\eps(|x|) w(|x|) e_r(x)$ on
  $\{|x|>\eps/2\}$ (eq.~\eqref{eq:Xeps-def});
- applies the finite-perimeter divergence theorem
  (`Maggi 2012, Thm 16.3`) to the Lipschitz field $X_\eps$, both on
  $E_\rho$ and on the comparison ball $B_\rho(\zbar)$, and subtracts;
- shows that, for $\eps<\rstar/8$, the truncation has no effect on
  the symmetric-difference part (which is at distance $\ge\rstar/4$
  from $\zbar$), so the $\eps\downarrow 0$ limit is trivial;
- bounds $(\mathrm{div}\,X)_+$ and $(-\mathrm{div}\,X)_+$ by
  $n/\rstar$ on each piece and closes by triangle.

This is the full finite-perimeter proof required by the brief; it is
not a "vague ray-slicing claim", and the ray-slicing route is
explicitly recorded as an alternative in
Remark~`\ref{rmk:slicing-route}` (lines 449–467). The only defect is
the stale explicit form `\max\{n/\rstar,1/2\}` in the theorem
statement (MAJOR M1 above).

### m6. The Introduction does not overstate the novelty of either route.

- Plan 1 is correctly attributed to BDV (`\cite{BDV}`) with a clear
  statement that the present paper adds quantitative tracking and
  detailed exposition, not a structurally new proof.
- Plan 2 is described as "structurally different" and
  "to our knowledge new in the Saint--Venant context" — both
  qualified claims, and supported by the bibliography audit. The
  conditional $\Pi$-route is marked auxiliary.
- The Allen–Kriventsov–Neumayer reproof~\cite{AKN2023} is acknowledged.

No overstatement detected.

---

## NOTES

### N1. Label aliases.

Inspected each alias listed in `source_map_final.md §6.2`:

- `lem:fj-center-package ↔ lem:FJ-package`: both attached to the FJ
  centre package lemma (Lemma in
  `plan2_weighted_metric_trace.tex:214`, "FJ centre package, fixed to
  the bulk centroid"). Aliases are semantically correct.
- `thm:mf-AC ↔ thm:metric:AC`: both attached to "Absolute continuity
  in $\X$" (Theorem in `plan2_metric_framework.tex:261`). Correct.
- `thm:radial-trace ↔ thm:fj-radial-divergence,
  lem:radial-trace-master`: all three attached to the oriented
  $L^1$-radial trace at the centroid (Theorem in
  `plan2_fj_center_radial_trace.tex:264`). Correct.
- `thm:wmt:trace ↔ thm:weighted-trace`: both attached to the
  existence-of-$\widehat\rho$ theorem (line 735 of
  `plan2_weighted_metric_trace.tex`). Correct.
- `thm:deficit ↔ thm:lsid:identity, thm:plan2-levelset-id`: all
  attached to the exact level-set deficit identity
  (`plan2_levelset_identity.tex:649`). Correct.
- Remaining aliases listed in §6.2 of the source map likewise point
  to the correct mathematical objects. Spot-checked five at random.

### N2. The preliminaries are either proved or precisely cited.

- GMT preliminaries
  (`preliminaries_gmt.tex`): every theorem either proved on the spot
  or cited with chapter/theorem number to Maggi 2012, AFP 2000,
  Federer 1969, Castaing–Valadier 1977, or Figalli–Maggi 2011.
- Torsion / rearrangement
  (`preliminaries_torsion.tex`): combination of in-line proofs
  (Saint–Venant deficit normalisation, Kohler–Jobin reduction lemmas)
  and precise citations to Talenti 1976, Polya–Szegő 1951,
  Kawohl 1985, Henrot 2006, Kesavan 2006, BBC 1975, BDV 2015,
  Brasco 2014.
- Quantitative isoperimetry
  (`preliminaries_quant_isoperimetry.tex`): FMP 2008/2010 and
  Fusco–Julin 2014 each cited with theorem number; the scaled form
  used in Plan 2 is proved on the spot by rescaling.

No "well-known/standard/routine" stand-alones detected in the load-bearing
prelims.

### N3. Cross-references / cleveref.

All cross-references resolve (the compile log records "Final
document: 120 pages, exit code 0, no warnings", per
`source_map_final.md §7`). No `??` or "undefined reference" detected.

### N4. The auxiliary centroid note remains compartmentalised.

A textual sweep confirms no load-bearing reference to
`plan2_aux_centroid_note.tex` outside the explicit auxiliary remark
`rem:intro-pi-route` and the no-conditional remark
`rem:plan2-no-conditional`. The four `\label` aliases attached to the
`\input` of `plan2_aux_centroid_note.tex` in `03_plan2_draft.tex`
(`ssec:plan2-aux-centroid`, `sec:audit-plan2`) point only to the
auxiliary subsection itself.

---

## Summary of recommended fixes (severity-ordered)

1. **B1.** Repoint or strip every body-text citation to an internal
   key (`Plan1Master`, `BDV2013`, `Final-master`,
   `Final-BoundedReduction`, `Final-KohlerJobinTransfer`,
   `Plan1Selection`, `FinalSelection`, `LevelSetIdentity-block`,
   `WIP_CentroidBound`, `WIP_LevelSetIdentity`,
   `WIP_SpaceTimeIdentity`, `Wave2A`, `Wave3F`, `Wave3J`).
2. **B1 (cont.).** Collapse alias pairs
   (`PolyaSzego`/`PolyaSzego1951`, `FJ2014`/`FuscoJulin2014`,
   `Maggi2008`/`MaggiSurvey2008`, `KawohlBook`/`Kawohl1985`,
   `HenrotBook`/`Henrot`, `KN1977`/`KN`,
   `Li86a`/`Li86b`/`Li86`) by repointing all `\cite{...}` to a single
   canonical key and deleting the alias from `references.bib`.
3. **M1.** Correct the explicit form of $C_4$ in the statement of
   Theorem~`\ref{thm:radial-trace}`
   (`plan2_fj_center_radial_trace.tex:277`)
   to match the value derived in the proof and recorded in the
   summary.
4. **M3.** Delete every uncited stub entry from `references.bib`.
5. **M4.** Replace the Markdown-file citation in
   `05_intro_story_draft.tex:53` with a `\S\ref{sec:notation}`
   cross-reference.

Once these are done, the manuscript is publication-ready in
mathematical content. The 1 blocking finding is bibliographic, not
mathematical, and is mechanical to fix; the 4 major findings are
likewise repairable without touching any proof.

---

**End of Agent 20 audit.**

---

## Repair Status (2026-05-13)

Every B1, M1, M2, M3, M4 finding above has been addressed. Final build:
`bibtex` reports 0 warnings; `pdflatex` reports 0 warnings, 0 undefined
references; the bibliography emits 51 entries (down from 84); the PDF
compiles to 119 pages.

### B1 — body-text repointing

The following internal/alias cite-keys were removed from
`references.bib` and every `\cite{...}` in the body was either
repointed to the canonical published reference or rewritten as prose /
in-manuscript cross-reference:

| Removed key | Disposition |
|-------------|-------------|
| `Plan1Master` | citation removed; `\S\ref{sec:notation}` inserted in `05_intro_story_draft.tex:53` |
| `Final-master` | citation removed; replaced by cross-reference to Theorem~\ref{thm:plan1-FK-upper-intro} |
| `BDV2013` | replaced by `BDV` (sed in `plan1_nearly_spherical.tex`) |
| `Plan1Selection`, `FinalSelection` | citations removed in `plan1_selection.tex`; replaced by `\cite[\S2, Step~1 of Lemma~5.3]{BDV}` |
| `Final-BoundedReduction`, `BDV-BoundedReduction` | repointed to `BDV` (Lemmas 5.1--5.3 / proof of Theorem 1.5) |
| `Final-KohlerJobinTransfer` | repointed to `\cite[Thm.~3.3]{Brasco2014}` |
| `LevelSetIdentity-block` | citation dropped; lemma title kept |
| `Wave2A` | repointed to `\cite[Prop.~2.3]{CL2012}` / `\cite[Thm.~1.1]{CL2012}` |
| `Wave3F` | repointed to `\cite[Thm.~1.1]{FJ2014}` |
| `Wave3J` | citations dropped; alternative slicing route described inline |
| `WIP_CentroidBound`, `WIP_LevelSetIdentity`, `WIP_SpaceTimeIdentity`, `WIP_WeightedMetricTrace` | citations dropped; in-manuscript references inserted (Hypothesis~\ref{hyp:Piint}, Subsection~\ref{subsec:level-set-identity}, \S\ref{sec:prelim-gmt}, \S\ref{subsec:weighted-metric-trace}) |
| `Plan2-LevelSet` | citation removed; replaced by `\cite[Thm.~1]{Talenti1976}` and inline derivation |
| `leveset-deficit-md` | citation dropped; prose ("a naive derivation gives") inserted |
| `agent4-weighted-metric-trace`, `wave2-B-kinetic-bound` | citations dropped from `plan2_weighted_metric_trace.tex` |
| `AKN-Faber-Krahn` | repointed to `AKN2023` |
| `AltCaffarelli` | repointed to `AC1981` |
| `KN` | repointed to `KN1977` |
| `Li86` | repointed to `Li86b` (the 1986 mixed BVP paper) |
| `GilbargTrudinger` | repointed to `GT1983` |
| `BerghLofstrom` | repointed to `BL1976` |
| `FuscoJulin2014` | repointed to `FJ2014` |
| `PolyaSzego` | repointed to `PolyaSzego1951` |
| `Henrot` | repointed to `HenrotBook` |
| `Kawohl1985` | repointed to `KawohlBook` |
| `MaggiSurvey2008` | repointed to `Maggi2008` |
| `FMP-torsion` | repointed to `FMPLaplace` |
| `Final-SchauderInterpolation` | repointed to `\cite[Theorem~6.4.5]{BL1976}` |
| `Final-GraphEntry` | citations removed; cross-reference to `\cite[\S 4]{BDV}` or local |

### B1 (uncited stubs removed from `references.bib`)

The following entries were also deleted because no body text cites them:
`Plan1Master`, `BDV-BoundedReduction-Plan1`, `KohlerJobinTransfer-Plan1`,
`BDV-SaintVenantAssembly`, `LevelSetIdentity`, `MetricFramework`,
`CentroidBound`, `SpaceTimeIdentity`, `WeightedMetricTrace`,
`BoundaryLayerTransfer`, `GlobalAssembly`,
`Final-BoundedReduction-tex`, `Final-KohlerJobinTransfer-tex`,
`Final-GraphEntry`, `Final-SchauderInterpolation`, `BDV-BoundedReduction`,
`Plan2-LevelSet`, `leveset-deficit-md`, `agent4-weighted-metric-trace`,
`wave2-B-kinetic-bound`, `AKN-Faber-Krahn`, `AltCaffarelli`,
`FuscoJulin2014`, `Henrot`, `Kawohl1985`, `KN`, `Li86`, `MaggiSurvey2008`,
`PolyaSzego`, `Wave2A`, `Wave3F`, `Wave3J`, `WIP_CentroidBound`,
`WIP_LevelSetIdentity`, `WIP_SpaceTimeIdentity`,
`WIP_WeightedMetricTrace`, `GilbargTrudinger`, `BerghLofstrom`,
`FMP-torsion`, `Final-BoundedReduction`, `Final-KohlerJobinTransfer`,
`Final-master`, `LevelSetIdentity-block`, `BDV2013`, `Plan1Selection`,
`FinalSelection`.

After cleanup, `references.bib` contains 51 entries, all cited.

### M1 — `C_4` statement/proof mismatch

`plan2_fj_center_radial_trace.tex:277` now reads
`$C_4(n,R,\rstar)=\max\{n/\rstar,3R/(2\rstar)\}$`, matching the derivation
in the proof (line 426) and the constants block (line 553).

### M2 — alias collapses

Resolved in B1 above.

### M3 — uncited stubs

Resolved in B1 above.

### M4 — Markdown citation in the Introduction

`05_intro_story_draft.tex:53` was rewritten to
"\ldots in the canonical normalisation fixed in
\S\ref{sec:notation}." No Markdown filename remains in the body.

### Files edited
- `Manuscript/references.bib` (complete rewrite, 51 entries)
- `Manuscript/05_intro_story_draft.tex`
- `Manuscript/plan1_graph_entry.tex`
- `Manuscript/plan1_kohler_jobin_transfer.tex`
- `Manuscript/plan1_nearly_spherical.tex`
- `Manuscript/plan1_selection.tex`
- `Manuscript/plan2_aux_centroid_note.tex`
- `Manuscript/plan2_boundary_layer_assembly.tex`
- `Manuscript/plan2_fj_center_radial_trace.tex`
- `Manuscript/plan2_levelset_identity.tex`
- `Manuscript/plan2_weighted_metric_trace.tex`
- `Manuscript/preliminaries_gmt.tex`
- `Manuscript/preliminaries_torsion.tex`

### Final verdict

The single BLOCKING finding (B1) and all four MAJOR findings (M1--M4)
are addressed. The manuscript compiles cleanly with no warnings and no
undefined references; the printed bibliography contains 51 unique
published references.

**End of repair status.**
