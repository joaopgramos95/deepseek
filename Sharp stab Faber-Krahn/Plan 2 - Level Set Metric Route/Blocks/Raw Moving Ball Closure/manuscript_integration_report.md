# Self-Contained Manuscript Integration — Execution Report

**Target:** `Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex`
**Plan executed:** `lets-get-retarded.md`
**Outcome:** the manuscript is now self-contained — every necessary result is
either proved in the file or quoted from a named published theorem. Compiles
clean (`pdflatex -interaction=nonstopmode -halt-on-error`, two passes,
**19 pages**, all cross-references resolve, no undefined citations).
**Date:** 2026-05-25.

---

## 1. Dependency inventory

Status legend: INTERNAL (proved in the TeX) · EXTERNAL-CITED (named published
theorem) · REPO-IMPORT (depended on another repo block — **eliminated**) ·
REMOVE.

| Result | Before | After | Location now |
|---|---|---|---|
| Exact level-set deficit identity | REPO-IMPORT (`LevelSetIdentity`) | **INTERNAL** | Thm `thm:id-main`, §3 |
| Flux identity `∫_{∂*E_t}\|∇u\|=m(t)` | REPO-IMPORT | **INTERNAL** | Lem `lem:id-flux`, §3 |
| Coarea form of `−m'` (`=α`) | (used implicitly) | **INTERNAL** | Lem `lem:id-coarea`, §3 |
| Rearranged primitive, `I''=−1/α` | REPO-IMPORT | **INTERNAL** | Lem `lem:id-I`, §3 |
| Critical-set / level conventions | asserted | **INTERNAL** | Lem `lem:id-noatoms`, §3 |
| Profile derivative-gap identity | INTERNAL (Prop) | INTERNAL | Prop `prop:levelset`, §4 |
| Bad-density estimate `\|B_τ\|≤Cδ_T` | INTERNAL | INTERNAL | Prop `prop:levelset`, §4 |
| Fusco–Julin strong quant. isoperimetry | EXTERNAL-CITED | EXTERNAL-CITED | Thm `thm:FJ-strong` `[FJ2014]` |
| Unnormalised same-centre consequences | INTERNAL | INTERNAL | Cor `cor:FJ-unnormalised`, §5 |
| Oriented radial trace | INTERNAL | INTERNAL | Lem `lem:oriented-radial-trace`, §5 |
| Same-centre good-level package | INTERNAL | INTERNAL | Thm `inp:samecenter`, §5 |
| Velocity defect (`≤D_H`) | INTERNAL | INTERNAL | Lem `lem:velocity`, §5 |
| Superlevel→domain asymmetry transfer | INTERNAL | INTERNAL | Lem `lem:superlevel-transfer`, §5 |
| Variable-thickness coarea differentiation | INTERNAL | INTERNAL | Lem `lem:varcoarea`, §6 |
| Shell-admissible radii | INTERNAL | INTERNAL | §6 |
| Local BV deformation tail | INTERNAL | INTERNAL | Lem `lem:BV-tail`, §6 |
| Affine shell estimate | INTERNAL | INTERNAL | Lem `lem:shell`, §7 |
| One-sided first variation of `q` | INTERNAL | INTERNAL | Thm `thm:qplus`, §7 |
| Unconditional Lipschitz bound for `q` | INTERNAL | INTERNAL | Lem `lem:qLip`, §7 |
| Centre-transfer | INTERNAL | INTERNAL | Lem `lem:center-transfer`, §8 |
| Positive kinetic estimate | INTERNAL | INTERNAL | Prop `prop:positivekinetic`, §8 |
| Endpoint trace | INTERNAL | INTERNAL | Lem `lem:endpoint`, §9 |
| Bounded SV stability (main thm) | INTERNAL | INTERNAL | Thm `thm:boundedSV`, §9 |
| Large-deficit fallback | INTERNAL | INTERNAL | proof of `thm:boundedSV` |
| BV coarea / Gauss–Green / Reshetnyak | (used) | EXTERNAL-CITED | App. A `[AFP2000,Maggi2012]` |
| De Giorgi isoperimetric · Talenti · BBC · Stampacchia · Pólya–Szegő | (used) | EXTERNAL-CITED | bib |

**Repo-imports remaining: none.** The single REPO-IMPORT (the deficit-identity
block) is now proved internally in §3.

## 2. Self-contained manuscript outline (final structure)

1. Introduction (`sec:intro`) — main theorem and route.
2. Standing notation and scope (`sec:notation`) — torsion, `δ_T`, `E_ρ`,
   `t(ρ)`, `w`, `dμ`, normal/trace conventions, Fraenkel asymmetry.
3. **Finite-perimeter level-set identities** (`sec:identity`) — regularity &
   level conventions; coarea form of `−m'`; flux identity by Lipschitz
   truncation; rearranged primitive with corrected `I''=−1/α`; the boxed exact
   deficit identity.
4. Profile gap and bad-density estimate (`sec:profilegap`).
5. Quantitative isoperimetry and same-centre trace control (`sec:samecentre`).
6. Coarea differentiation and shell-admissible radii (`sec:coarea`).
7. Affine moving-ball first variation (`sec:shell`).
8. Positive kinetic estimate (`sec:kinetic`).
9. Endpoint trace and bounded stability (`sec:endpoint`).
- Proof architecture and constants (`sec:architecture`).
- Appendix A: Standard tools for sets of finite perimeter (`app:bv`).
- Appendix B: Dependency certificate (`app:constants`).

This matches the recommended target structure.

## 3. Repo material integrated

From `Blocks/Level Set Identity/LevelSetIdentity.tex`, ported into §3 (with
notation reconciled to the manuscript's `|Ω|=ω_n`, `B_1` the equal-volume ball,
macros `\Hn,\Per,\Om`; all labels prefixed `id-` to avoid the pre-existing
`lem:endpoint` clash):

- `lem:noatoms` → `lem:id-noatoms` (Stampacchia critical-set nullity, no atoms,
  finite-perimeter/normal/critical-boundary level conventions).
- `lem:coarea` → `lem:id-coarea`; `lem:flux` → `lem:id-flux` (Lipschitz
  truncation).
- `lem:I3a/b/c` → consolidated `lem:id-I` (`I'=u^*`, `I''=−1/α`), with the
  α-vs-β remark (`rem:id-alpha`).
- `lem:Gpp,cov,gap,endpoint` → `lem:id-Gpp/cov/gap/endpoint`; `thm:main` →
  `thm:id-main` (boxed identity), carrying the corrected
  `∫_{B_1}u_{B_1}=ω_n/(n(n+2))` endpoint computation.

**Not ported** (correctly): the conditional gradient-hypothesis section (Hyp-G,
`prop:V-bar-V`, `cor:int-V-bar-V`) — it is explicitly unused by the identity and
superseded in this route by the in-file velocity lemma `lem:velocity`; the
smooth-only note `level-set-deficit-identity.tex`; and the profile-gap/bad-set
lemmas, which the manuscript already re-derives in Prop `prop:levelset`.

The `LevelSetIdentity.tex` block itself is left untouched on disk; the
manuscript simply no longer depends on it.

## 4. External theorem / citation list (final bibliography)

- `FJ2014` — Fusco–Julin, strong quantitative isoperimetric inequality (the one
  substantive external theorem).
- `AFP2000`, `Maggi2012` — BV coarea, Sobolev chain rule, reduced boundaries,
  finite-perimeter Gauss–Green, strict-BV/Reshetnyak continuity.
- `DeGiorgi1958` — isoperimetric inequality.
- `Talenti1976` — rearrangement `L^∞` bound.
- `BBC1975` — absolutely continuous monotone inverse.
- `Stampacchia1965` — `D²u=0` a.e. on `{∇u=0}`.
- `GilbargTrudinger2001` — interior `W^{2,p}` regularity, weak maximum principle.
- `PolyaSzego1951`, `Bandle1980` — ball-energy identification.

Added relative to the previous bibliography: `Bandle1980, BBC1975,
DeGiorgi1958, GilbargTrudinger2001, PolyaSzego1951, Stampacchia1965,
Talenti1976`. No dead entries (the earlier dead entries CL2012/FMP2008 had
already been pruned).

## 5. TeX patch sequence applied

1. Rewrote the abstract; added `§1 Introduction` with the main theorem and route.
2. Inserted `§3 Finite-perimeter level-set identities` (the ported proof);
   split the old combined section into `§4 Profile gap and bad-density estimate`
   and `§5 Quantitative isoperimetry and same-centre trace control`.
3. Rewired Prop `prop:levelset` to cite `thm:id-main` (`eq:levelset-identity`),
   replacing the `eq:imported-levelset-identity` import paragraph; updated its
   two internal back-references.
4. Renamed the `varcoarea` slab-endpoint functions `α,β → ξ,ζ` (removing the
   clash with the coarea integrals `α(t),β(t)` of §3) and pointed its
   critical-set step to `lem:id-noatoms`(a).
5. Retitled the moving-ball sections to the recommended headings; added stable
   section labels (`sec:coarea/shell/kinetic/endpoint/profilegap/samecentre`).
6. Replaced `Status of the repair` with `Proof architecture and constants`
   (clean proof map + constants trace), and added Appendix A (BV tools) and
   Appendix B (dependency certificate).
7. Expanded the bibliography (8 entries) with precise locators.
8. QA: two-pass compile; stale/hidden-risk phrase scrub
   (`imported/repository/raw/repair/status/candidate/old route/rescaled
   metric/Hyp-G/BDV/selection principle/smooth boundary` — none remain except
   honest "we do **not** use graph/pointwise-lower-bound" disclaimers).

## 6. Risks that remain after integration

- **One math fix made during the port:** the `lem:id-noatoms`(c) finite-perimeter
  step originally drafted compared `P(E_t)` to `β(t)` (invalid); corrected to the
  `φ=1` coarea form `∫_0^M P(E_t)dt = ∫_{0<u<M}|∇u| < ∞`. Now correct.
- **`∂*E_t ⊂ Ω` for `t>0`** rests on the precise representative of `u∈H^1_0`
  vanishing `H^{n-1}`-a.e. outside `Ω`, cited to `[AFP2000,Maggi2012]` rather
  than re-derived; this is standard but is the softest cited step.
- **Constants** depend only on `n, R, ρ_*` and `C_FJ(n)`; verified in
  `sec:architecture`. The large-deficit regime is closed by the `4/δ_0`
  fallback with no regularity assumption.
- No dependency on any other repository block remains; the argument is checkable
  from this file plus the cited literature.

---

### Certificate

The manuscript proves `𝒜(Ω)² ≤ C(n,R,ρ_*) δ_T(Ω)` internally, modulo the
Fusco–Julin theorem and standard finite-perimeter / rearrangement /
isoperimetric tools, all cited. Self-contained: **yes**. Compiles: **yes (19 pp).**
