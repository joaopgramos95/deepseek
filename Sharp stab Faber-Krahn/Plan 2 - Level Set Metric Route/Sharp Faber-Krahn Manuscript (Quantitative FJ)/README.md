# Sharp Faber–Krahn Manuscript (Quantitative FJ)

This directory holds the self-contained version of the Plan 2 manuscript in
which the Fusco–Julin strong-form quantitative isoperimetric inequality
appears as an internal theorem with a computable dimensional constant,
rather than as a black-box external citation.

## Contents

- `FK_quantitative_FJ.tex` — the integrated manuscript (≈ 4900 lines, 83 pp).
  - **Main body (§§1–8 + Appendices A, B)**: identical in mathematical content
    to the sibling `Sharp Faber-Krahn Manuscript/FK_standard_FuscoJulin.tex`,
    with abstract/intro/dependency-certificate language updated so that FJ
    is no longer described as the deep external input.
  - **Appendix C — *The Fusco–Julin strong form: a constructive proof with
    computable constant*** (≈ 3000 lines).  The proof is the composition of
    *Attempt I* (explicit nearly-spherical, constant $2n/(n+1)$) and
    *Attempt II* (regularising selection penalising the true $\beta^2$,
    annular trapping + localisation of potential centres, finite spectral
    truncation in place of the harmonic-approximation compactness, and the
    coordinate-slicing computable confinement) from
    `Sharp Faber-Krahn Manuscript/FJ_quantitative_attempts.tex`, culminating
    in `thm:global-computable-FJ` and `cor:original-FJ-computable`.
- `FJ_quantitative_attempts_source.tex` — read-only copy of the source file
  from which Appendix C was distilled. Kept here for traceability.

## Provenance of the integrated proof

The truly quantitative argument is the regularised-selection branch of
`FJ_quantitative_attempts.tex` (Attempts I + II + the FMP–FJ confinement).
Attempts III (Reilly/torsion) and IV (intrinsic slicing for $n\ge 3$) of the
source file are NOT included here: they are unfinished and not load-bearing.

After integration the manuscript imports no theorem whose constant is
non-computable.  In particular the corollary `cor:original-FJ-computable`
gives an explicit value for the comparison constant,
$$
   C_{\mathrm{cmp}}(n) = 1 + \sqrt{2} + \sqrt{8n\omega_n/(n-1)} ,
$$
and the final same-centre Fusco–Julin constant is
$$
   \widehat C_{\mathrm{FJ}}^{\mathrm{comp}}(n)
   = \bigl(1+\sqrt{2}+\sqrt{8n\omega_n/(n-1)}\bigr)^{2}\,
     C_{\mathrm{FJ}}^{\mathrm{comp}}(n),
$$
with $C_{\mathrm{FJ}}^{\mathrm{comp}}(n)$ assembled from the four explicit
dimensional constants $A_{\mathrm{red}}(n)$, $B_{\mathrm{red}}(n)$,
$R_{\mathrm{red}}(n)$, and $C_{\mathrm{reg}}(n,R_{\mathrm{red}}(n),2n)$ from
`lem:computable-confinement` and `prop:true-beta-bounded-close`.

## Verification status

The manuscript was produced from the sibling `Sharp Faber-Krahn Manuscript/`
sources in a single integration pass followed by four parallel verification
audits.  Findings from those audits were applied: the diagnostic
potential-deficit attempt of Attempt II was compressed (saving ≈ 500 lines
without removing load-bearing math); the Gram-determinant exponent, the
second-order perimeter expansion, and the potential continuity/decay at
infinity were filled in; the last remaining black-box import (Proposition
1.2 of [FJ2014]) was inlined with explicit constants; `d_{\mathrm{cut}}`
was displayed; the Tamanini-iteration sketch was annotated with its
explicit dimensional ingredients; broken citation keys
(`Maggi`→`Maggi2012`, `FJ`→`FJ2014`, `FigalliMaggiPratelli`→`FMP2010`)
were repaired and the FMP 2008 Annals + FMP 2010 mass-transport bib
entries were added.

The file compiles clean (three pdflatex passes, exit 0, no undefined
references, no multiply-defined labels, no warnings).
