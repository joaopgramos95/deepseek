# Global Notation Register

**Status.** Canonical for the whole manuscript. All section drafts
(Agents 2–18) must use these symbols and conventions. Local
deviations are allowed only inside a smooth-approximation subproof and
must be unwound at the end of that subproof.

This register fixes:

1. dimension and ambient space;
2. domain class and standing radii;
3. balls;
4. torsion and Saint–Venant energies / deficit;
5. Dirichlet eigenvalue and Faber–Krahn deficit;
6. asymmetries (Fraenkel and BDV smooth);
7. quotients (Q_α);
8. level-set foliation (E_t, E_ρ, F_ρ, the measure μ);
9. velocities (V_ρ, H_{z,ρ}, ν_ρ);
10. centre fields (z_ρ, z̄_ρ);
11. metric space (𝓧, d_𝓧);
12. radii ρ_*, ρ_δ, ρ̂;
13. constants C, c, δ_0, κ, σ;
14. Π and σ(x);
15. coarea quantities α(t), β(t), D_H, D_I.

For every entry the table shows:

- **Symbol** = the canonical form;
- **Definition** = the precise definition used in the manuscript;
- **Source(s)** = where the convention appears in the source files;
- **Conflict resolution** = if sources disagree, the choice made and why.

The TeX macros at the end of this register are the ones that all
manuscript drafts should include in their preamble.

---

## 1. Dimension, ambient space, standing parameters

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `n` | Ambient dimension, `n ≥ 2`. | `Plan 2/WIP/*` use `n`; `Final/master.tex` uses `N`. | **Canonical `n`** (matches Plan 2; aligns with the brief, Agent 17). Plan 1 drafts must convert `N → n` at unification. |
| `ℝⁿ` | Ambient Euclidean space. | All sources. | No conflict. |
| `R` | Confining radius, fixed `R ≥ 2`. | `Final/master.tex`, `WIP_MetricFramework.tex`, etc. | Standardised: `R` is a generic confining radius for bounded statements. |
| `R_*(n)` | Bounded-reduction radius, `R_*(n) := max{d(n), 2}` where `d(n)` is the diameter constant of BDV Lemma 5.3. | `Final/master.tex` §VI; `WIP_GlobalAssembly.tex`. | Canonical. |
| `ρ_*` | Inner cut-off radius for the foliation, fixed `ρ_* ∈ (0,1)`; **default `ρ_* = 1/2`**. | `WIP_master.tex` (sets `ρ_* = 1/2`); `WIP_MetricFramework.tex` (general). | Manuscript fixes `ρ_* = 1/2` in final assembly; Plan 2 building blocks may state results for general `ρ_* ∈ (0,1)` and then specialise. |

## 2. Domain class

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `Ω` | A non-empty open set in `ℝⁿ` with `0 < |Ω| < ∞`. | All. | Default class for the final theorems. |
| `B_r(z)` | Open ball of radius `r > 0` centred at `z ∈ ℝⁿ`. | All. | Canonical. |
| `B_r` | `B_r(0)`. | All. | Canonical. |
| `B_1` | Unit ball at the origin. | All. | Canonical. |
| `B^*` | Ball with `|B^*| = |Ω|`, **centred at the origin** unless an explicit translate is written. | Both masters. | Canonical. The translated ball `B^* + x_0` is used only inside the Fraenkel asymmetry. |
| `ω_n` | `ω_n := |B_1|`. | All. | Canonical. |
| `R := (|Ω|/ω_n)^{1/n}` | Radius of `B^*` (local symbol in some Plan 2 blocks). | `WIP_LevelSetIdentity.tex`. | **Conflict**: this `R` clashes with the confining radius `R`. Resolution: inside any block using `(|Ω|/ω_n)^{1/n}`, write **`R_Ω`** instead of `R`. The confining radius `R` is reserved for `Ω ⊂ B_R`. |

## 3. Torsion energy, torsional rigidity, Saint–Venant deficit

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `u_Ω` (also `u`) | Variational torsion function: unique minimiser of `v ↦ (1/2)∫|∇v|² − ∫v` on `H¹_0(Ω)`. Equivalently `−Δu = 1`, `u = 0` on `∂Ω` in trace sense. `u ≥ 0` a.e. | All sources. | Canonical. |
| `T(Ω)` | Torsional rigidity, `T(Ω) := ∫_Ω u_Ω dx`. | All. | Canonical. |
| `E(Ω)` | **BDV-normalised** Saint–Venant energy: `E(Ω) = −T(Ω)/2 = min{(1/2)∫|∇v|² − ∫v : v ∈ H¹_0(Ω)}`. Note `E(Ω) ≤ 0` on every admissible set. | `Final/master.tex`, all WIP blocks. | Canonical. **Conflict**: some informal Plan 1 notes use "torsion energy" for `T`; the manuscript reserves `E` for the BDV-normalised functional and `T` for the rigidity. |
| `δ_T(Ω)` | Saint–Venant deficit at fixed volume `|Ω| = |B^*|`: `δ_T(Ω) := E(Ω) − E(B^*) ≥ 0`. | `WIP_master.tex`, `WIP_BoundaryLayerTransfer.tex`. | Canonical. Plan 1's `δ(Ω)` (`quantitative-selection-principle.md`) is identified with `δ_T(Ω)`. |
| `T_n` | Universal: `T_n := T(B_1) = ω_n / (n(n+2))`. | `Final/master.tex`, `WIP_master.tex`. | Canonical. |
| `δ` | Used as a shorthand for `δ_T(Ω)` only **inside** Plan 2 blocks where context is unambiguous (e.g. `WIP_WeightedMetricTrace.tex` writes `δ := δ_T(Ω)`). Manuscript prose must use `δ_T(Ω)` on first use of a result and may use `δ` afterwards. | `WIP_WeightedMetricTrace.tex`. | Allowed local shorthand. |

## 4. Dirichlet eigenvalue and Faber–Krahn deficit

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `λ_1(Ω)` | First Dirichlet eigenvalue of `−Δ` on `Ω`, `λ_1(Ω) = min_{H¹_0\\{0}} ∫|∇u|²/∫u²`. | All. | Canonical. |
| `L_n` | `L_n := λ_1(B_1)`. | `Final/master.tex`, `WIP_master.tex`. | Canonical. |
| `δ_FK(Ω)` | Scale-normalised Faber–Krahn deficit: `δ_FK(Ω) := (|Ω|/ω_n)^{2/n} (λ_1(Ω) − λ_1(B^*))`. | Brief; `Final/master.tex` writes the same quantity inline; `WIP_master.tex` writes the same. | **New canonical name** (sources never give it a short name). Use `δ_FK` for the LHS of the final Faber–Krahn theorem. |

## 5. Asymmetries

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `𝓐(Ω)` | Fraenkel asymmetry: `𝓐(Ω) := inf_{x_0 ∈ ℝⁿ} |Ω Δ (B^* + x_0)| / |B^*| ∈ [0, 2)`. | All sources use macro `\Fr` for `𝓐`. | Canonical. |
| `α(Ω)` | **BDV smooth asymmetry**: `α(Ω) := ∫_{Ω Δ B_1(x_Ω)} |1 − |x − x_Ω|| dx`, where `x_Ω` is the barycentre, in the convention of `[BDV, Def. 4.1]`. Used **only** inside the Plan 1 selection / graph-entry / Schauder chain. | `Final/master.tex`, `Plan 1/quantitative-selection-principle.md`. | Canonical. **Naming conflict**: the symbol `α` is also used in Plan 2 for the coarea quantity `α(t) = ∫_{∂*E_t}|∇u|^{−1} dH^{n−1}`. Resolution: where both occur in the same passage, write **`α_BDV(Ω)`** for the BDV smooth asymmetry and `α(t)` for the coarea quantity. Default: `α` without arguments means the BDV smooth asymmetry; `α(t)` means the coarea quantity. |
| `x_Ω` | Barycentre of `Ω`. | `Plan 1/quantitative-selection-principle.md`. | Canonical (Plan 1 use only). |

## 6. Quotients

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `Q_α(Ω)` | At fixed volume `|Ω| = ω_n`: `Q_α(Ω) := (E(Ω) − E(B_1)) / α(Ω) = δ_T(Ω) / α(Ω)`. | `Final/master.tex`. | Canonical. |

## 7. Level-set foliation and slicing

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `E_t` | Super-level set `E_t := {u_Ω > t}`, precise representative. Used in `LevelSetIdentity`. | `WIP_LevelSetIdentity.tex`. | Canonical, "level-set parametrisation". |
| `m(t)` | `m(t) := |E_t|`. | `WIP_LevelSetIdentity.tex`. | Canonical. |
| `t(ρ)` | Inverse distribution: the level for which `|{u > t(ρ)}| = ω_n ρⁿ`. Absolutely continuous on `[ρ_*, 1]`, with `t'(ρ) ≤ 0`. | All WIP blocks. | Canonical. |
| `E_ρ` | Volume-radius super-level: `E_ρ := {u_Ω > t(ρ)}` with `|E_ρ| = ω_n ρⁿ`, `ρ ∈ [ρ_*, 1]`. | All WIP blocks. | Canonical, "volume-radius parametrisation". |
| `F_ρ` | Rescaled level set: `F_ρ := ρ^{−1} E_ρ`, so `|F_ρ| = ω_n` for all `ρ`. | `WIP_MetricFramework.tex` and downstream. | Canonical. |
| `[F_ρ]` | Class of `F_ρ` in the metric quotient `𝓧`. | All WIP blocks. | Canonical. |
| `∂*E_ρ`, `∂*E_t` | De Giorgi reduced boundary. | `WIP_LevelSetIdentity.tex` etc. | Canonical. |
| `ν_ρ` | Outer measure-theoretic unit normal on `∂*E_ρ`. | All WIP blocks. | Canonical. |
| `P(E_ρ)` | De Giorgi perimeter: `P(E_ρ) = ℋ^{n−1}(∂*E_ρ)`. | All. | Canonical. |
| `μ(dρ)` | The measure `μ(dρ) := (−t'(ρ)) dρ` on `[ρ_*, 1]`. | All WIP blocks. | Canonical. |

## 8. Coarea quantities and deficit identity

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `α(t)` | `α(t) := ∫_{∂*E_t} |∇u|^{−1} dℋ^{n−1}` (defined for a.e. `t`). | `WIP_LevelSetIdentity.tex`. | Canonical. **Naming**: see entry for `α(Ω)`. |
| `β(t)` | `β(t) := ∫_{∂*E_t} |∇u| dℋ^{n−1}`. | `WIP_LevelSetIdentity.tex`. | Canonical. |
| `D_H(t)` | Cauchy–Schwarz defect: `D_H(t) := α(t) β(t) − P(E_t)²`. | `WIP_LevelSetIdentity.tex`. | Canonical. `D_H ≥ 0` a.e. |
| `D_I(t)` | Squared-perimeter isoperimetric defect: `D_I(t) := P(E_t)² − n² ω_n^{2/n} m(t)^{2 − 2/n}`. | `WIP_LevelSetIdentity.tex`. | Canonical. `D_I ≥ 0` a.e. |
| `c_n` | `c_n := n² ω_n^{2/n}`. | `WIP_LevelSetIdentity.tex`. | Canonical. |
| Deficit identity | `(2/|Ω|)(E(Ω) − E(B^*)) = (1/|Ω|) ∫_0^{‖u‖_∞} (D_H + D_I)/(c_n m(t)^{1−2/n}) dt`. | `WIP_LevelSetIdentity.tex` Thm 3.x; `WIP_master.tex` Thm 3.1. | Canonical statement. |

## 9. Velocities and oriented quantities

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `V_ρ(x)` | Normal velocity of the foliation: `V_ρ(x) := −t'(ρ)/|∇u(x)|`, defined ℋ^{n−1}-a.e. on `∂*E_ρ` for a.e. `ρ` (Sobolev–Sard, Figalli–Maggi 2011, App. A, Thm A.1). | `WIP_MetricFramework.tex`, `WIP_master.tex`. | Canonical. |
| `H_{z, ρ}(x)` | Homothetic radial field at centre `z`: `H_{z,ρ}(x) := (x − z) · ν_ρ(x) / ρ`. | `WIP_master.tex`, `WIP_MetricFramework.tex`. | Canonical. |
| `e_r(x)` | Unit radial direction at centre `z`: `e_r(x) := (x − z)/|x − z|`. The centre is implicit from context. | `WIP_master.tex` (uses `e_r` in (B²-int)). | Canonical, with centre always specified. |
| `T_ρ` | Oriented `L¹` radial trace at centre `z_ρ`: `T_ρ := ∫_{∂*E_ρ} ||x − z_ρ|/ρ − 1| dℋ^{n−1}`. | Brief Agent 11; `wave3-G-route-delta-assembly.md`. | Canonical. |

## 10. Centre fields

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `z̄_ρ` | **Bulk centroid** of `E_ρ`: `z̄_ρ := |E_ρ|^{−1} ∫_{E_ρ} x dx`. | `WIP_master.tex`, `WIP_CentroidBound.tex`. | Canonical. **This is the centre that the repaired Plan 2 chain uses globally.** |
| `z_ρ` | Generic Borel measurable centre field, `|z_ρ| ≤ R'`. Used as a placeholder in `MetricFramework`. | `WIP_MetricFramework.tex`. | Canonical placeholder; resolved to `z̄_ρ` in the repaired chain, optionally to a Fusco–Julin oscillation centre on small-isoperimetric-defect levels. |
| `x_Ω` | Barycentre of `Ω`, only inside the BDV smooth asymmetry. | Plan 1. | Canonical. |
| FvHT centre | **Explicitly not used** as a load-bearing object in the manuscript. May appear only as a remark; resolved in favour of `z̄_ρ` by Wave 3 F. | `wave3-F-h1-center-bound.md`. | **Conflict resolution**: all centre-fields in the final manuscript are `z̄_ρ`. The Fraenkel-optimal centre and FvHT block centre are not load-bearing. |

## 11. Metric space

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `𝓧` | Quotient `𝓧 := 𝔐 / ℝⁿ` where `𝔐` is the set of `ℒⁿ`-equivalence classes of indicator functions `𝟙_A` with `|A| < ∞`, equipped with `d_{L¹}(𝟙_A, 𝟙_C) = |A Δ C|`, and `ℝⁿ` acts by translation. | `WIP_MetricFramework.tex` Def. 2.1. | Canonical. |
| `d_𝓧` | `d_𝓧([A],[C]) := inf_{a ∈ ℝⁿ} |A Δ (C + a)|`. | `WIP_MetricFramework.tex`. | Canonical. |
| `|F_ρ ̇|_𝓧` (metric derivative) | The Ambrosio–Gigli–Savaré metric derivative of `ρ ↦ [F_ρ]` in `(𝓧, d_𝓧)`. | `WIP_MetricFramework.tex`, `WIP_WeightedMetricTrace.tex`. | Canonical. |

## 12. Radii along the foliation

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `ρ_*` | Inner cut-off, fixed; default `1/2`. | All. | Canonical. |
| `ρ_δ` | `ρ_δ := 1 − κ √{δ_T(Ω)}`, with `κ > 0` an explicit constant fixed in `WeightedMetricTrace`. | `WIP_master.tex`. | Canonical. |
| `ρ̂` | The metric-trace radius, `ρ̂ ∈ [ρ_δ − C_* δ_T, ρ_δ]`. Output of `WeightedMetricTrace`. | `WIP_master.tex`, `WIP_WeightedMetricTrace.tex`. | Canonical. |
| `κ` | Explicit positive constant fixing the size of the boundary layer `{ρ > ρ_δ}`. **Manuscript convention**: `κ = κ(n, R, ρ_*)`, with the exact choice fixed inside `WeightedMetricTrace` (Agent 12). | `WIP_master.tex`, `WIP_WeightedMetricTrace.tex`. | Canonical. |

## 13. Π and Fubini density σ

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `Π(E_ρ, z̄_ρ)` | Signed radial moment: `Π(E_ρ, z̄_ρ) := (n − 1) ∫ (𝟙_{B_ρ(z̄_ρ)}(x) − 𝟙_{E_ρ}(x)) |x − z̄_ρ|^{−1} dx`. | `WIP_master.tex` §IV. | Canonical. **Status**: auxiliary; manuscript records that the load-bearing chain uses only integrated forms (B²-int), (T_1²-int) — see Agent 14 / brief. |
| `σ(x)` | Fubini density appearing in the space–time Π identity. Defined inside `SpaceTimeIdentity`. | `WIP_master.tex` §IV. | Canonical name. |
| `Ω̃` | Domain of integration in the space–time identity, fixed inside `SpaceTimeIdentity`. | `WIP_master.tex` §IV. | Canonical. Not to be confused with Plan 1's `\widetilde{\Omega}` for volume-normalised companion. |

> **Conflict resolution (Ω̃)**. Plan 1 writes `Ω̃` for the volume-normalised companion of a selected minimiser (`Final/master.tex`, macro `\Otilde`). Plan 2 writes `Ω̃` for the integration domain of the space–time identity. The manuscript reserves **`Ω̃`** for the Plan 1 companion. The space–time identity domain is renamed **`Ω_Π`** in the unified manuscript.

## 14. Constants

| Symbol | Definition / convention | Sources | Resolution |
|---|---|---|---|
| `C` | Generic positive constant. Dependence is **always** declared at first use: `C = C(n)`, `C = C(n, R)`, `C = C(n, R, ρ_*)`, etc. **No occurrence of `C` without declared dependence is allowed.** | Brief; all sources. | Canonical. |
| `c` | Same convention as `C`. Used when the constant appears on the lower side of an estimate. | All. | Canonical. |
| `δ_0` | Smallness threshold (a positive constant). Always declared with its dependence, e.g. `δ_0(n, R, ρ_*)`. | `WIP_WeightedMetricTrace.tex`, `WIP_BoundaryLayerTransfer.tex`. | Canonical. |
| `κ` | See entry above (boundary-layer constant). | All WIP. | Canonical. |
| `σ` | **Symbol clash**: in `Final/master.tex` `σ = σ(n)` is the BDV main-theorem constant; in `WIP_master.tex` `σ(x)` is the Fubini density. Manuscript reserves `σ(x)` for the Fubini density and writes the BDV constant as `c_FK^{BDV}(n)`. | Both masters. | Resolution as stated. |
| `c_SV(n, R)`, `c_SV^{glob}(n)` | Bounded and global sharp Saint–Venant constants. Defined in `SaintVenantAssembly` and `BoundedReduction`. | `Final/master.tex`, both masters. | Canonical. |
| `c_FK(n)` | Final sharp Faber–Krahn constant, given by (`Final/master.tex` (eq:cFKdef) ≡ `WIP_master.tex` (eq:cFKdef)). | Both masters. | Canonical. |
| `c_*(n)` | BDV nearly-spherical closure constant. Used in Plan 1 only. | `Final/master.tex`. | Canonical. |
| `C_*`  | Constant in the metric-trace endpoint estimate `d_𝓧(F_{ρ̂}, B_1)² ≤ C_* δ_T`. Used in Plan 2. | `WIP_master.tex`, `WIP_WeightedMetricTrace.tex`. | Canonical. **Conflict**: `C_*` and `c_*` are distinct symbols (Plan 2's `C_*` is a metric-trace constant; Plan 1's `c_*(n)` is the BDV nearly-spherical constant). Manuscript keeps both, with explicit subscripts on first use: `c_*^{NS}(n)` for the Plan 1 constant and `C_*^{trace}(n, R, ρ_*)` for the Plan 2 constant if the same paragraph mentions both. |

## 15. TeX preamble macros

The following macros must be loaded at the top of every section draft.
The `\Fr`, `\Om`, `\eps` macros match the existing `Final/` and
`Plan 2/WIP/` files.

```latex
\newcommand{\R}{\mathbb{R}}
\newcommand{\Fr}{\mathcal{A}}
\newcommand{\Om}{\Omega}
\newcommand{\Otilde}{\widetilde{\Omega}}
\newcommand{\eps}{\varepsilon}
\newcommand{\rstar}{\rho_{*}}
\newcommand{\rhad}{\widehat{\rho}}
\newcommand{\rhodelta}{\rho_{\delta}}
\newcommand{\zbar}{\bar z_{\rho}}
\newcommand{\X}{\mathcal{X}}
\newcommand{\dX}{d_{\mathcal{X}}}
\newcommand{\Bstar}{B^{*}}
\newcommand{\Erho}{E_{\rho}}
\newcommand{\Frho}{F_{\rho}}
\newcommand{\Vrho}{V_{\rho}}
\newcommand{\nurho}{\nu_{\rho}}
\newcommand{\PiE}{\Pi(E_{\rho},\zbar)}
\newcommand{\deltaT}{\delta_{T}}
\newcommand{\deltaFK}{\delta_{\mathrm{FK}}}
\newcommand{\BDValpha}{\alpha_{\mathrm{BDV}}}
\newcommand{\OmPi}{\Omega_{\Pi}}
\DeclareMathOperator{\dist}{dist}
```

## 16. Hypothesis-tracking conventions

To meet the "no hidden hypotheses" rule of the brief:

- **Domain class.** Every theorem statement must say "open `Ω ⊂ ℝⁿ`
  with `0 < |Ω| < ∞`" unless the section is a smooth-approximation
  subproof. The bounded class "`Ω ⊂ B_R`, `|Ω| = ω_n`" is the standing
  hypothesis of the entire bounded sharp Saint–Venant chain
  (Theorems `SV` and `BL`).
- **Finite perimeter.** All boundary integrals on `∂*E_ρ` are on the
  reduced boundary in the De Giorgi sense (see Agent 2 preliminaries).
- **Bounded reduction.** The reduction `c_SV(n, R_*(n)) ⇒ c_SV^{glob}(n)`
  must be stated as a separate theorem with the dependence on `R`
  explicitly displayed on the input and absent on the output.
- **Centre field.** Every centre-dependent estimate must declare which
  centre is used (canonical: `z̄_ρ`).
- **Smooth approximation.** Whenever a smooth-flow argument is invoked,
  the section must end with a finite-perimeter passage statement and a
  proof or citation of the passage.

## 17. Known notation conflicts resolved

1. **`N` vs `n`** (dimension). Canonical `n`. All Plan 1 drafts must
   convert at unification.
2. **`R` ambiguity** (confining radius vs `(|Ω|/ω_n)^{1/n}`). Confining
   radius keeps `R`; volume radius written `R_Ω`.
3. **`α(·)`** (BDV smooth asymmetry vs coarea α(t)). Use `α_BDV` if
   ambiguous; `α(t)` always means the coarea quantity.
4. **`Ω̃`** (Plan 1 volume-normalised companion vs Plan 2 space–time
   identity domain). Canonical `Ω̃` = Plan 1 companion; Plan 2 domain
   renamed `Ω_Π`.
5. **`σ`** (BDV main-theorem constant vs Fubini density). Canonical
   `σ(x)` = Fubini density; BDV constant written `c_FK^{BDV}(n)` or
   "the BDV main-theorem constant".
6. **`δ`** vs `δ_T(Ω)` (Saint–Venant deficit). Local shorthand allowed
   inside Plan 2 blocks; first occurrence in any subsection must use
   `δ_T(Ω)`.
7. **Centre field choice.** Canonical: bulk centroid `z̄_ρ`. The
   Fraenkel-optimal centre and FvHT block centre are not load-bearing
   (resolved by Wave 3 F).
8. **`δ_FK` vs `δ_T`.** The Saint–Venant deficit is `δ_T`. The
   Faber–Krahn deficit is `δ_FK`. The Kohler–Jobin transfer turns one
   into the other.

End of register.
