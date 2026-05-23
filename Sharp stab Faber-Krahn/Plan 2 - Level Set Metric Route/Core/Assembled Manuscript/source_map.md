# Manuscript Source Map

This map lists every load-bearing theorem, lemma, definition, and
estimate planned for the final manuscript. For each item, the **Status**
column records one of:

- **DRAFT(§)** — to be drafted in the manuscript section §, by the
  named agent;
- **LOCAL(file)** — copied or adapted from a local building block
  (relative path inside the working directory);
- **CITE(?)** — literature citation to be supplied by Agent 1 in
  `04_references_audit.md`; the placeholder name in parentheses
  identifies the result;
- **MISSING** — explicitly flagged as not yet available.

Dependencies are listed with the canonical notation register entries
(`00_notation_register.md`). Constant dependence on `(n, R, ρ_*)` is
shown in the **Constants** column.

---

## A. Preliminaries — Geometric Measure Theory (§2.1, Agent 2)

| # | Item | Status | Constants | Notes |
|---|---|---|---|---|
| A1 | Finite perimeter, reduced boundary, De Giorgi normal `ν` | CITE(Maggi2012) + CITE(AFP2000) | — | Notational; no proof. |
| A2 | BV coarea theorem for `u ∈ H¹_0(Ω) ∩ L^∞` | CITE(Maggi2012 Thm 13.1), CITE(AFP2000 Thm 3.40) | — | Statement only. |
| A3 | Sobolev–Sard for the torsion function: `V_ρ = −t'(ρ)/|∇u|` ℋ^{n−1}-a.e. on `∂*E_ρ` for a.e. ρ | CITE(FigalliMaggi2011, App. A, Thm A.1) | — | Load-bearing for `MetricFramework`. |
| A4 | Divergence theorem for finite-perimeter sets | CITE(Maggi2012 Thm 16.3) | — | |
| A5 | Lipschitz / truncation argument for `x/|x|`-type vector fields | DRAFT(§2.1, Agent 2) | constants explicit | Used in Agent 11 radial trace. |
| A6 | `L¹` convergence and lower semicontinuity of perimeter | CITE(Maggi2012 Prop 12.15) | — | |
| A7 | Measurable selection of levelwise centres | DRAFT(§2.1, Agent 2) + CITE(Federer §2.13) | — | Used in `MetricFramework`. |
| A8 | Reshetnyak lower semicontinuity for linear-growth integrands | CITE(AFP2000 Thm 2.38) | — | Used in `MetricFramework`. |

## B. Preliminaries — Torsion, Rearrangement, Deficits (§2.2, Agent 3)

| # | Item | Status | Constants | Notes |
|---|---|---|---|---|
| B1 | Torsion energy `E(Ω)`, rigidity `T(Ω)`; normalisation `E = −T/2` | DRAFT(§2.2, Agent 3) | — | Notation register §3. |
| B2 | Saint–Venant deficit `δ_T(Ω)` | DRAFT(§2.2, Agent 3) | — | |
| B3 | Fraenkel asymmetry `𝓐(Ω)` and basic properties | DRAFT(§2.2, Agent 3) + CITE(Maggi2008 survey) | — | |
| B4 | Faber–Krahn deficit `δ_FK(Ω)` | DRAFT(§2.2, Agent 3) | — | |
| B5 | Talenti pointwise comparison `u*_Ω ≤ u*_B` | CITE(Talenti1976) | — | Used in `LevelSetIdentity`. |
| B6 | Volume-radius parametrisation `E_ρ = {u > t(ρ)}`, `|E_ρ| = ω_n ρⁿ` | DRAFT(§2.2, Agent 3) | — | Notation register §7. |
| B7 | Profile-gap estimate `‖u‖_∞ ≤ R²/(2n)` | CITE(Talenti1976) | `R = (|Ω|/ω_n)^{1/n}` | |
| B8 | Bad-set Lebesgue estimate (Talenti gap on `{|∇u| ≪}`) | DRAFT(§2.2, Agent 3) + CITE source TBD | `C(n, R, ρ_*)` | Load-bearing for `WeightedMetricTrace` kinetic bound. **Flag: Agent 1 to find a published source; if none, Agent 3 proves it.** |
| B9 | Kohler–Jobin inequality `T(Ω) λ_1(Ω)^{(n+2)/2} ≥ T(B^*) λ_1(B^*)^{(n+2)/2}` | CITE(Brasco2014 Thm 3.3); original CITE(KohlerJobin1978) | — | |

## C. Preliminaries — Quantitative Isoperimetry (§2.3, Agent 4)

| # | Item | Status | Constants | Notes |
|---|---|---|---|---|
| C1 | FMP quantitative isoperimetric inequality: `𝓐(E)² ≤ C(n) (P(E) − P(B^*))/P(B^*)` | CITE(FMP2008) | `C(n)` | |
| C2 | Fusco–Julin strong form: `𝓐(E)² + β(E)² ≤ C(n) 𝓓(E)` | CITE(FJ2014) | `C(n)` | Here `β` is the FJ oscillation, **not** the coarea `β(t)`. Notation register §8 disambiguates. |
| C3 | Scaled version on `\{|E| = ω_n ρⁿ, ρ ∈ [ρ_*, 1]\}` with explicit constants | DRAFT(§2.3, Agent 4) | `C(n, ρ_*)` | Load-bearing for `WeightedMetricTrace`. |
| C4 | Divergence identity converting `β(E, z)²` into normal oscillation `∫|ν − e_r|² dℋ^{n−1}` | DRAFT(§2.3, Agent 4) | constants explicit | Load-bearing for Agent 11 radial trace. |
| C5 | Hypothesis matrix: finite perimeter, finite measure, boundedness for the scaled form | DRAFT(§2.3, Agent 4) | — | |
| C6 | Cicalese–Leonardi selection principle for isoperimetric inequality (referenced in intro) | CITE(CL2012) | — | Background only. |

## D. Plan 1 (§3, Agents 5–8)

### D.1 Selection principle (§3.1, Agent 5)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| D1.1 | BDV penalised functional `J_Ω_0(U) = E(U) + f_{η̂}(|U|) + √(ε² + τ²(α(U) − ε)²)` | LOCAL(Final/SelectionPrinciple.tex) + LOCAL(Plan 1/quantitative-selection-principle.tex) | `ε_sel(n,R), q_sel(n,R), C_sel(n,R)` | |
| D1.2 | Existence by direct method | LOCAL(Final/SelectionPrinciple.tex Thm) | `C_sel(n,R)` | |
| D1.3 | Volume-normalised companion `Ω̃ = r_*^{−1} U_*`, preservation of asymmetry | LOCAL(Final/SelectionPrinciple.tex) | `C_sel(n,R)` | |
| D1.4 | Inheritance of BDV regularity package (density estimates, Lipschitz nondegeneracy, smooth Bernoulli coefficient) | LOCAL(Final/SelectionPrinciple.tex) + CITE(BDV Lem 4.6, 4.9, 4.12) | `C(n,R)` | |
| D1.5 | Volume-rescaled Bernoulli law on `∂Ω̃` | LOCAL(Final/SelectionPrinciple.tex) | — | |

### D.2 Graph entry and Schauder/interpolation (§3.2, Agent 6)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| D2.1 | BDV Lemma 4.2 chain: `𝓐 → α → Hausdorff` | CITE(BDV Lem 4.2) | `C(n)` | |
| D2.2 | Alt–Caffarelli flatness theorem (BDV Theorem 4.18 form) | CITE(BDV Thm 4.18); origin CITE(AC1981) | `C(n, R)` | |
| D2.3 | Global `C^{1,γ}` normal graph parametrisation; threshold `α_graph(n, R)` | LOCAL(Final/GraphEntry.tex Thm), LOCAL(Plan 1/graph-entry-closure.tex) | `α_graph, M_1, C_H''(n,R)`, `γ(n,R)` | |
| D2.4 | Kinderlehrer–Nirenberg hodograph straightening | CITE(KN1977) | — | |
| D2.5 | Lieberman oblique Schauder bootstrap to `C^{5,γ}` | CITE(Li86) | `M_5(n, R)` | |
| D2.6 | Gagliardo–Nirenberg interpolation `C^{2,γ_0} ≤ C ‖g‖_∞^{1−θ} ‖g‖_{C^{5,γ}}^θ` | CITE(GN classical; cite Brezis–Mironescu or Maz'ya for precise form) | `C_GN(n)`, `θ = (2+γ_0)/(5+γ)` | |
| D2.7 | Threshold `α_sph(n, R, γ_0)` | LOCAL(Final/SchauderInterpolation.tex) | explicit | |

### D.3 Nearly-spherical closure and Saint–Venant (§3.3, Agent 7)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| D3.1 | BDV nearly-spherical Theorem 3.3: `E(Ω) − E(B_1) ≥ (1/(32n²)) ‖g‖_{H^{1/2}}²` | CITE(BDV Thm 3.3); historical CITE(Fuglede) | `c_*(n) = 1/(32 n² C_3(n))` | |
| D3.2 | Trace–Poincaré comparison | DRAFT(§3.3, Agent 7) + CITE(BDV Lem 4.2(iii)) | `C_3(n)` | |
| D3.3 | Volume / barycentre normalisation absorbing `O(‖g‖_{L²})` correction | LOCAL(Final/NearlySphericalClosure.tex) | dimensional | |
| D3.4 | Small-α linear bound `E(Ω_0) − E(B_1) ≥ q_*(n,R) α(Ω_0)` | LOCAL(Final/SaintVenantAssembly.tex) | `q_*(n,R) = c_*(n)/(2 C_sel(n,R))` | |
| D3.5 | Conversion to `𝓐²`: `E − E(B_1) ≥ κ_near(n,R) 𝓐²` via BDV Lem 4.2(i) | LOCAL(Final/SaintVenantAssembly.tex) | `κ_near(n,R)` | |
| D3.6 | Far regime: BDV Lem 5.2 (the suboptimal `𝓐^4` bound) | CITE(BDV Lem 5.2) | `C_8'(n)` | Rearrangement-based; no contradiction. |
| D3.7 | Glue at threshold `a_near = a_far` (BDV Lem 4.2(ii)) | LOCAL(Final/SaintVenantAssembly.tex) | explicit | |
| D3.8 | Bounded sharp Saint–Venant: `E(Ω) − E(B_1) ≥ c_SV(n,R) 𝓐(Ω)²` for `Ω ⊂ B_R`, `|Ω| = ω_n` | LOCAL(Final/SaintVenantAssembly.tex Thm SV) | `c_SV(n,R)` | |

### D.4 Bounded reduction and Kohler–Jobin (§3.4, Agent 8)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| D4.1 | BDV constructive truncation lemma | CITE(BDV Lem 5.3) | `d(n), δ(n), C_9(n)` | |
| D4.2 | Global sharp Saint–Venant: `E(Ω) − E(B_1) ≥ c_SV^{glob}(n) 𝓐(Ω)²` | LOCAL(Final/BoundedReduction.tex Thm BR) | `c_SV^{glob}(n)` per (eq:cSVglob) | |
| D4.3 | Kohler–Jobin reduction `T(Ω) λ_1(Ω)^{(n+2)/2} ≥ T(B^*) λ_1(B^*)^{(n+2)/2}` | CITE(Brasco2014 Thm 3.3) | — | |
| D4.4 | Pointwise transfer `λ_1(Ω) ≥ λ_1(B^*)(T(B^*)/T(Ω))^{2/(n+2)}` | LOCAL(Final/KohlerJobinTransfer.tex) | — | |
| D4.5 | Elementary `(1−s)^{−p} − 1 ≥ p s` | DRAFT(§3.4, Agent 8) | — | |
| D4.6 | Final Plan 1 theorem: `δ_FK(Ω) ≥ c_FK(n) 𝓐(Ω)²` | LOCAL(Final/master.tex Thm final) + (eq:cFKdef) | `c_FK(n)` | |

## E. Plan 2 (§4, Agents 9–13)

### E.1 Level-set deficit identity (§4.1, Agent 9)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E1.1 | Coarea identity for `−m'(t)` | LOCAL(Plan 2/WIP/WIP_LevelSetIdentity.tex) | — | |
| E1.2 | Weak divergence-flux identity (Lipschitz truncation) | LOCAL(Plan 2/WIP/WIP_LevelSetIdentity.tex) | — | |
| E1.3 | Corrected distributional second derivative `I''(s) = −1/α(t(s))` | LOCAL(Plan 2/WIP/WIP_LevelSetIdentity.tex) | — | Wave 3 J correction. |
| E1.4 | Exact deficit identity: `(2/|Ω|)(E(Ω) − E(B^*)) = (1/|Ω|) ∫ (D_H + D_I)/(c_n m^{1−2/n}) dt` | LOCAL(Plan 2/WIP/WIP_LevelSetIdentity.tex Thm) | — | Notation register §8. |
| E1.5 | Pólya–Szegő identification of ball energy (endpoint) | CITE(KawohlBook) + LOCAL(Plan 2/WIP/WIP_LevelSetIdentity.tex) | — | |
| E1.6 | Profile gap consequence used in `WeightedMetricTrace` | LOCAL(Plan 2/level-set-deficit-identity.md, Lemma 8.3) | `C(n)` | Bad-set transfer. |

### E.2 Metric framework (§4.2, Agent 10)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E2.1 | Definition of `𝓧, d_𝓧` and attainment of translation infimum | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex Def 2.1, Lem 2.2) | — | |
| E2.2 | Rescaled curve `ρ ↦ [F_ρ]` and `|F_ρ| = ω_n` | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex Def 2.3) | — | |
| E2.3 | Absolute continuity of `ρ ↦ [F_ρ]` in `𝓧` | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex) | — | |
| E2.4 | Smooth-flow first variation identity | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex) + CITE(AGS2008) | — | |
| E2.5 | Finite-perimeter passage of (E2.4) using Reshetnyak l.s.c. | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex) + CITE(AFP2000 Thm 2.38) | — | |
| E2.6 | Metric first-variation bound (T): `|F_ρ ̇|_𝓧 ≤ C(n, ρ_*, R) inf_a ∫ |V_ρ − H_{z_ρ, ρ} − a · ν_ρ| dℋ^{n−1}` | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex Thm M) | `C(n, ρ_*, R) = ρ_*^{−n}` (canonical) | |
| E2.7 | Translation-volume identity for finite-perimeter sets | LOCAL(Plan 2/WIP/WIP_MetricFramework.tex) + CITE(Maggi2012) | — | |

### E.3 Fusco–Julin centre, oriented radial trace (§4.3, Agent 11)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E3.1 | Scaled Fusco–Julin on `|E_ρ| = ω_n ρⁿ` | DRAFT(§4.3, Agent 11) + CITE(FJ2014) | `C(n, ρ_*)` | Cf. C2, C3. |
| E3.2 | Borel measurable centre selection on good levels | LOCAL(Plan 2/gmt-inputs-for-metric-closure.md) + DRAFT | — | A7. |
| E3.3 | Fraenkel bound from FJ at centroid: `|E_ρ Δ B_ρ(z̄_ρ)| ≤ C 𝓓(E_ρ)^{1/2}` | DRAFT(§4.3, Agent 11) | `C(n, ρ_*)` | |
| E3.4 | Normal oscillation bound: `∫_{∂*E_ρ} |ν_ρ − e_r|² dℋ^{n−1} ≤ C 𝓓(E_ρ)` | DRAFT(§4.3, Agent 11) + CITE(FJ2014) | `C(n, ρ_*)` | C4. |
| E3.5 | **Oriented radial trace lemma**: `T_ρ ≤ C (|E_ρ Δ B_ρ(z̄_ρ)| + ∫_{∂*E_ρ}|ν_ρ − e_r|² dℋ^{n−1})` | DRAFT(§4.3, Agent 11) | `C(n, ρ_*)` | **Critical load-bearing lemma.** Vector field `X(x) = ||x − z̄_ρ|/ρ − 1| · (x − z̄_ρ)/|x − z̄_ρ|` with finite-perimeter divergence/truncation argument. |
| E3.6 | Sobolev–Sard application: `V_ρ = −t'(ρ)/|∇u|` ℋ^{n−1}-a.e. | CITE(FigalliMaggi2011 App. A Thm A.1) | — | A3. |

### E.4 Integrated action and weighted metric trace (§4.4, Agent 12)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E4.1 | Good / bad isoperimetric-defect level decomposition | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex) | `C(n, R, ρ_*)` | |
| E4.2 | Markov bound on bad-level mass | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex) | `C(n, R, ρ_*)` | |
| E4.3 | Integrated action bound: `∫ (d_𝓧(F_ρ, B_1)² + |F_ρ ̇|_𝓧²) dμ ≤ C δ_T` | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex Thm) | `C(n, R, ρ_*, κ)` | |
| E4.4 | Bad-`−t'` decomposition and kinetic bound: `∫ |F_ρ ̇|_𝓧² dρ ≤ C' δ_T` | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex Thm K) | `C'(n, R, ρ_*, κ)` | B8 dependency. |
| E4.5 | Abstract weighted metric trace lemma | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex) | — | |
| E4.6 | Endpoint `d_𝓧(F_{ρ̂}, B_1)² ≤ C_* δ_T` for some `ρ̂ ∈ [ρ_δ − C_* δ_T, ρ_δ]` | LOCAL(Plan 2/WIP/WIP_WeightedMetricTrace.tex Thm trace) | `C_*(n, R, ρ_*)` | |

### E.5 Boundary-layer transfer and global assembly (§4.5, Agent 13)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E5.1 | Boundary-layer volume estimate `|Ω \\ E_{ρ̂}| = ω_n(1 − ρ̂ⁿ) ≤ C √{δ_T}` | LOCAL(Plan 2/WIP/WIP_BoundaryLayerTransfer.tex) | `C(n, κ)` | |
| E5.2 | Superlevel transfer: `𝓐(Ω) ≤ 𝓐(E_{ρ̂}) + 2|Ω\\E_{ρ̂}|/ω_n` | LOCAL(Plan 2/level-set-deficit-identity.md Lem 8.3) | dimensional | |
| E5.3 | Squaring `(a+b)² ≤ 2a² + 2b²` preserving exponent 2 | DRAFT(§4.5, Agent 13) | — | |
| E5.4 | Bounded sharp Saint–Venant: `𝓐(Ω)² ≤ C(n,R,ρ_*) δ_T(Ω)` for `Ω ⊂ B_R, |Ω|=ω_n` | LOCAL(Plan 2/WIP/WIP_BoundaryLayerTransfer.tex Thm main) | `C(n, R, ρ_*)` | |
| E5.5 | FMP fallback for `δ_T ≥ δ_0`: yields trivial bound after enlarging `C` | LOCAL(Plan 2/WIP/WIP_BoundaryLayerTransfer.tex) + CITE(FMP2008) | `C(n)` | |
| E5.6 | Bounded reduction (Plan 1 import) | LOCAL(Final/BoundedReduction.tex) | `c_SV^{glob}(n)` | Shared with Plan 1. |
| E5.7 | Kohler–Jobin transfer (Plan 1 import) | LOCAL(Final/KohlerJobinTransfer.tex) | `c_FK(n)` | Shared with Plan 1. |
| E5.8 | Final Plan 2 theorem: `δ_FK(Ω) ≥ c_FK(n) 𝓐(Ω)²` | LOCAL(Plan 2/WIP/WIP_GlobalAssembly.tex Thm) | `c_FK(n)` per (eq:cFKdef) | Identical normalisation to Plan 1. |

### E.6 Auxiliary route note (§4.6 optional, Agent 14)

| # | Item | Status | Constants | Source |
|---|---|---|---|---|
| E6.1 | Centroid kinematic identity (no homothety) | LOCAL(Plan 2/WIP/WIP_CentroidBound.tex) | — | Conditional. |
| E6.2 | `H¹`-in-`ρ` centroid bound (F): `∫ |z̄_ρ'|² (−t'(ρ)) dρ ≤ C_cent δ_T` | LOCAL(Plan 2/WIP/WIP_CentroidBound.tex Thm F) | `C_cent(n, R, ρ_*)` | Used to state (T_1²-int), (B²-int). |
| E6.3 | Space–time `Π` identity | LOCAL(Plan 2/WIP/WIP_SpaceTimeIdentity.tex) | — | Auxiliary. |
| E6.4 | Slicing-then-squaring decomposition `T_1 = T_1^{rad,slic} + T_1^{tan}` | LOCAL(Plan 2/WIP/WIP_SpaceTimeIdentity.tex) | — | |
| E6.5 | Slice-rearrangement `|E_ρ Δ B_ρ|² ≤ C Π(E_ρ, z̄_ρ)` | LOCAL(Plan 2/WIP/WIP_SpaceTimeIdentity.tex) | `C(n)` | |

> **Status flag (§4.6).** Per the brief, this section is an
> auxiliary remark. **It is not load-bearing for the repaired
> Plan 2 proof.** The repaired chain uses only the **integrated**
> forms (B²-int) and (T_1²-int), proved via (F) of `CentroidBound`,
> and the centroid choice `z̄_ρ`. Pointwise per-ρ statements (R) and
> (B²) are not used.

## F. Introduction and references (§1, Agents 1 and 18)

| # | Item | Status |
|---|---|---|
| F1 | Faber 1923 / Krahn 1925 historical | CITE(Faber1923), CITE(Krahn1925) |
| F2 | Modern accounts | CITE(KawohlBook), CITE(HenrotBook), CITE(BucurButtazzo) |
| F3 | Hansen–Nadirashvili, Melas, Bhattacharya | CITE(HansenNadirashvili1994), CITE(Melas1992), CITE(Bhattacharya2001) |
| F4 | FMP Faber–Krahn (exponent 4) | CITE(FMPLaplace) |
| F5 | BDV sharp main theorem | CITE(BraDeP2017) / CITE(BDV) |
| F6 | FMP isoperimetric, Cicalese–Leonardi, Figalli–Maggi–Pratelli, Fusco–Julin | CITE(FMP2008), CITE(CL2012), CITE(FMP2010), CITE(FJ2014) |
| F7 | Acerbi–Fusco–Morini selection | CITE(AFM2013) |
| F8 | Kohler–Jobin, Brasco 2014 | CITE(KohlerJobin), CITE(Brasco2014) |
| F9 | Alt–Caffarelli regularity | CITE(AC1981) |
| F10 | Fuglede stability | CITE(Fuglede) |
| F11 | Cianchi–Fusco–Maggi–Pratelli Sobolev | CITE(CFMP) |
| F12 | Neumayer Wulff | CITE(NeumayerWulff) |
| F13 | Brasco–Pratelli second eigenvalue | CITE(BrascoPratelli) |
| F14 | Allen–Kriventsov–Neumayer | CITE(AKN) |
| F15 | Ambrosio–Gigli–Savaré metric framework | CITE(AGS2008) |
| F16 | Talenti rearrangement | CITE(Talenti1976) |
| F17 | Maggi finite-perimeter book; AFP BV book | CITE(Maggi2012), CITE(AFP2000) |
| F18 | Figalli–Maggi App. A (Sobolev–Sard) | CITE(FigalliMaggi2011) |
| F19 | Kinderlehrer–Nirenberg, Lieberman | CITE(KN), CITE(Li86) |
| F20 | Fusco survey, Maggi survey | CITE(FuscoSurvey), CITE(Maggi2008) |
| F21 | De Giorgi 1958 reduced boundary | CITE(DeGiorgi1958) |
| F22 | Nicola–Tilli convexity / rearrangement proof | CITE — Agent 1 to locate. **Status flag.** |

## G. Missing items (explicitly flagged)

| # | Item | Severity | Note |
|---|---|---|---|
| G1 | Published reference for B8 (Talenti bad-set Lebesgue estimate) | MED | If not found, Agent 3 proves it. |
| G2 | F22 Nicola–Tilli rearrangement convexity proof | LOW | Discussion-only; Intro reference. |
| G3 | Pointwise per-ρ radial trace (R) | INFO | Explicitly **not used**; auxiliary. |
| G4 | Pointwise per-ρ normal-oscillation bound (B²) | INFO | Explicitly **not used**; auxiliary. |
| G5 | Conditional centroid Π-route | INFO | Explicitly **not load-bearing** (Agent 14 remark only). |
| G6 | Conditional Bernoulli spectral closure (Plan 1 alternate) | INFO | Discussed as alternative only; not in main Plan 1 chain. |

## H. Cross-file consistency notes for later agents

1. **Notation conflicts** (`Ω̃`, `α`, `σ`, `R`, `C_*` vs `c_*`,
   `N` vs `n`) are resolved in `00_notation_register.md` §17. All
   section agents must apply those conventions.
2. The bounded Saint–Venant theorem statement is **the same** in
   Plan 1 (D3.8) and Plan 2 (E5.4): `𝓐(Ω)² ≤ C(n, R, ρ_*) δ_T(Ω)` for
   `Ω ⊂ B_R`, `|Ω| = ω_n`. The Plan 1 constant has no `ρ_*` dependence
   (`ρ_*` is intrinsic to the Plan 2 foliation). Agent 17 must verify.
3. The **final** Faber–Krahn theorem statement is the same in Plan 1
   (D4.6) and Plan 2 (E5.8) with the same `c_FK(n)`. Both call into
   the same bounded reduction (`Final/BoundedReduction.tex`) and the
   same Kohler–Jobin transfer (`Final/KohlerJobinTransfer.tex`).
4. **Centre field globally**: all centre-dependent estimates use the
   bulk centroid `z̄_ρ`. The Fraenkel-optimal centre and the FvHT
   block centre are explicitly not load-bearing.
5. **Constant tracking**: every `C` written without `(n)`, `(n, R)`,
   `(n, R, ρ_*)` etc. must be qualified at first occurrence.
6. The **boundary layer** `|Ω \\ E_{ρ̂}| = O(√{δ_T})` must be **squared**
   inside the transfer step (E5.3), not before; this is the
   sharp-exponent-preserving step (Wave 3 J).
