# Final Adversarial Audit — Repair Report

**Date.** 2026-05-13.
**Scope.** Repairs of every BLOCKING and MAJOR finding raised in
`Manuscript/final_adversarial_audit.md` (Agent 20).

## Summary

| Severity | Finding | Status |
|----------|---------|--------|
| BLOCKING | B1: internal/alias cite-keys in body and bib | RESOLVED |
| MAJOR    | M1: stale `C_4` in Theorem~\ref{thm:radial-trace} | RESOLVED |
| MAJOR    | M2: alias-duplicate references in bib | RESOLVED |
| MAJOR    | M3: uncited stubs in `references.bib` | RESOLVED |
| MAJOR    | M4: Markdown filename in Introduction cite | RESOLVED |

## Bibliography

- `references.bib`: rewritten end-to-end. Entries reduced from 84 to 51.
- Every remaining entry is `\cite`d at least once from the body.
- `bibtex main` runs with 0 warnings; 51 entries emitted.
- `main.bbl` contains exactly 51 `\bibitem` entries (down from
  the 84-item dirty bibliography).

## Body-text cite-key replacements

Total distinct internal/alias keys eliminated: 47. The replacement map
is recorded verbatim in the "Repair Status (2026-05-13)" section
appended to `final_adversarial_audit.md`. Highlights:

- `Plan1Master`, `Final-master`, `Plan1Selection`, `FinalSelection`,
  `Final-BoundedReduction`, `Final-KohlerJobinTransfer`,
  `LevelSetIdentity-block`, `BDV-BoundedReduction`,
  `WIP_*` (×4), `Wave2A`, `Wave3F`, `Wave3J`, `Plan2-LevelSet`,
  `leveset-deficit-md`, `agent4-weighted-metric-trace`,
  `wave2-B-kinetic-bound`, `Final-GraphEntry`,
  `Final-SchauderInterpolation` — citations removed in favor of
  the canonical BDV/Brasco2014/Talenti1976/CL2012/FJ2014/AFP2000
  references or in-manuscript cross-references
  (`\S\ref{sec:notation}`, Theorem~\ref{thm:plan1-FK-upper-intro},
  Hypothesis~\ref{hyp:Piint}, Subsection~\ref{subsec:level-set-identity},
  Theorem~\ref{thm:wmt:trace}, etc.).

- Alias duplicates collapsed in the canonical direction:
  `PolyaSzego→PolyaSzego1951`, `Henrot→HenrotBook`,
  `Kawohl1985→KawohlBook`, `KN→KN1977`, `Li86→Li86b`,
  `FuscoJulin2014→FJ2014`, `MaggiSurvey2008→Maggi2008`,
  `AltCaffarelli→AC1981`, `GilbargTrudinger→GT1983`,
  `BerghLofstrom→BL1976`, `FMP-torsion→FMPLaplace`,
  `AKN-Faber-Krahn→AKN2023`, `BDV2013→BDV`.

## M1 fix verbatim

`plan2_fj_center_radial_trace.tex:277` was

> The constant has the explicit form $C_4(n,R,\rstar)=\max\{n/\rstar,1/2\}$
> (see~\eqref{eq:T-trace-explicit} below).

now reads

> The constant has the explicit form $C_4(n,R,\rstar)=\max\{n/\rstar,3R/(2\rstar)\}$
> (see~\eqref{eq:T-trace-explicit} below).

matching the proof on line 426 and the summary block on line 553.

## M4 fix verbatim

`05_intro_story_draft.tex:53` was

> in the canonical normalisation of the notation register
> (\S\,3--5 of~\cite[Manuscript/00\_notation\_register.md]{Plan1Master}).

now reads

> in the canonical normalisation fixed in \S\ref{sec:notation}.

The Markdown filename and the internal cite-key are both gone.

## Final compile

- `pdflatex` → `bibtex` → `pdflatex` → `pdflatex` from a clean state.
- `bibtex main`: 51 entries, 0 warnings.
- `pdflatex`: 0 LaTeX errors, 0 LaTeX warnings, 0 undefined references,
  0 multiply-defined labels.
- `main.pdf`: 119 pages, ~1.07 MB.

## Files modified

- `Manuscript/references.bib` (rewrite)
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
- `Manuscript/final_adversarial_audit.md` (appendix "Repair Status (2026-05-13)")

## Items not resolvable to a unique canonical published reference

None. Every cite that previously pointed to an internal note has been
either (a) repointed to a canonical published reference judged to be
the underlying source by reading context, or (b) removed in favour of
an in-manuscript cross-reference where the citation was supporting a
locally-proved statement rather than a literature claim.

The one classification call worth flagging for the user:
`Li86` (the alias) was repointed to `Li86b` (Lieberman 1986, "Mixed
boundary value problems for elliptic and parabolic differential
equations of second order"). The other Lieberman key `Li86a` (the 1985
oblique-derivative paper) is also retained and continues to be cited
in `05_intro_story_draft.tex` alongside `Li86b`. If the original
intent of `\cite{Li86}` in `plan1_graph_entry.tex` was the 1985 paper
rather than the 1986 paper, the user can globally adjust the four
`{Li86b}` occurrences there to `{Li86a}`.

**End of repair report.**
