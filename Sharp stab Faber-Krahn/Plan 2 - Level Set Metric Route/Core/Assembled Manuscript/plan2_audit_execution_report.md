# Plan 2 Audit Execution Report

Date: 2026-05-14

Executed from: `Manuscript/plan2_audit_agent_instructions.md`

Agents run: A--G.  
Agent H was not run, because the instruction file says to run it only after the Manuscript files are rewritten.

## Overall Verdict

`BLOCKED`, but with a useful separation:

1. The self-truncated velocity repair replacing Hyp-G is internally sound on the intended good levels.
2. The downstream boundary-layer transfer preserves the sharp square exponent if the upstream metric trace is granted.
3. The current route is blocked by measure-theoretic and finite-perimeter gaps upstream of the metric trace.

The most important conclusion is that the old Hyp-G obstruction has likely been removed, but the proof cannot yet be regarded as closed. The remaining hard points are not cosmetic: they are load-bearing for the endpoint trace.

## Agent Status

| Agent | Scope | Verdict |
|---|---|---|
| A | End-to-end Plan 2 chain | `BLOCKED` |
| B | Level-set identity | `BLOCKED` |
| C | Metric first variation | `BLOCKED` |
| D | Hyp-G replacement / trimmed velocity repair | `PASS WITH MAJOR CAVEAT` |
| E | Fusco--Julin and oriented radial trace | `BLOCKED` |
| F | Weighted metric trace | `BLOCKED` |
| G | Boundary-layer transfer and global assembly | `PASS WITH MAJOR GAPS` |
| H | Manuscript integration readiness | Not run yet |

## Blocking Issues

### 1. Level-Set Identity Needs a Measure-Theoretic Repair

Files:

1. `Plan 2/WIP/WIP_LevelSetIdentity.tex`
2. `Manuscript/plan2_levelset_identity.tex`

Problems found:

1. Plateau handling in the coarea and layer-cake steps is not justified.
2. The proof identifies the coarea integral with `|{alpha0<u<beta0}|=m(alpha0)-m(beta0)` without excluding positive-measure level sets inside the interval.
3. The inverse-function step proving `I''=(u*)'=-1/alpha` is too terse.
4. Endpoint differentiation at `s=L` should be one-sided and justified.
5. The integrated Talenti/profile-gap estimate needed later is not proved in `WIP_LevelSetIdentity.tex`.

Required repair:

Either prove a no-atoms statement for positive torsion levels, or rewrite the rearrangement section using an atom-aware generalized inverse theorem. Then add a standalone profile-gap/bad-set lemma strong enough to imply

```tex
|\{\rho:-t'(\rho)<\rho_*/(2n)\}| \le C\delta_T.
```

### 2. Metric Framework Does Not Yet Prove the Required Upper Gradient

Files:

1. `Plan 2/WIP/WIP_MetricFramework.tex`
2. `Manuscript/plan2_metric_framework.tex`
3. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`

Problems found:

1. The finite-perimeter passage uses lower semicontinuity in the wrong direction.
2. Reshetnyak gives a lower bound on the relaxed limit cost, while the proof needs an upper bound by the target boundary integral.
3. Velocity-measure convergence is assumed, not proved.
4. The claimed uniform metric Lipschitz bound on bad levels is unsupported; boundedness of sets does not give a perimeter-free dilation Lipschitz constant.
5. The smooth translation-mode calculation has a scaling mismatch, although this is likely repairable by renaming the translation parameter.

Required repair:

Replace Theorem T's finite-perimeter closure with either a genuine limsup/recovery theorem for the boundary action, or a direct BV/finite-perimeter deformation estimate. Separately reprove or remove the bad-level `A0` Lipschitz input.

### 3. Fusco--Julin Center Package Is Not Yet Correctly Imported

Files:

1. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
2. `Manuscript/plan2_fj_center_radial_trace.tex`
3. `Manuscript/preliminaries_quant_isoperimetry.tex`

Problems found:

1. The proof needs a same-center FJ package: one center must control both symmetric difference and normal oscillation.
2. The current preliminaries state separately minimized quantities, then try to use a beta-minimizing center to control asymmetry. This gives the wrong inequality direction.
3. The WIP measurable-selection construction selects near asymmetry minimizers, not necessarily centers satisfying the normal oscillation bound.
4. The manuscript replacement by bulk centroids is unsupported and reintroduces an unproved centroid route.
5. The oriented radial trace proof in the manuscript relies on false or unproved inner containment around the centroid.

Required repair:

State the exact same-center FJ theorem needed, with one normalization and one scaling convention. Then select from a compact-valued multifunction of joint FJ centers or joint almost-minimizers, proving measurability and center localization.

### 4. Weighted Metric Trace Depends on Missing Inputs

File:

1. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`

Problems found:

1. The Lebesgue kinetic bound depends on the missing integrated Talenti/profile-gap estimate.
2. The trace mass hypothesis uses the same missing estimate.
3. The import of the metric derivative theorem depends on the unresolved metric-framework upper-gradient issue.
4. The smallness condition must explicitly include `\delta <= ((1-\rho_*)/(2\kappa))^2` or an equivalent bound ensuring the window around `\rho_\delta` is nonempty and order-one.
5. The `dt` / `d\rho` conversion is substantively correct later, but written with the wrong sign in the exposition.
6. The abstract trace lemma's H2/H3 bookkeeping should be cleaned so the exact hypotheses are visible.

### 5. Boundary Transfer and Global Assembly Are Conditional, Not Blocking

Files:

1. `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`
2. `Plan 2/WIP/WIP_GlobalAssembly.tex`
3. `Final/BoundedReduction.tex`
4. `Final/KohlerJobinTransfer.tex`

Problems found:

1. The boundary-transfer constant is claimed polynomial, but the final large-deficit constant includes `4/\delta_0`. The dependence of `\delta_0^{-1}` must be controlled.
2. The smallness window must explicitly guarantee `\rho_\delta>\rho_*`.
3. `GlobalAssembly` says bounded reduction preserves Faber--Krahn deficit; it should say Saint--Venant deficit/asymmetry until the Kohler--Jobin stage.
4. `KohlerJobinTransfer` is stated for bounded open sets, while `GlobalAssembly` concludes for all finite-measure open sets. Either cite the finite-measure version or add an exhaustion argument.
5. Boundary-layer constants contain minor stale inconsistencies: `C'_n=n(\kappa+C_*)` versus `C'_n=n\kappa`.

Checks passed:

1. The boundary transfer itself is exponent-safe.
2. Fraenkel asymmetry is treated modulo translations.
3. Bounded reduction absorbs the radius dependence after fixing `R_*(n)`.
4. The Kohler--Jobin normalization is internally consistent with `E=-T/2`.

## Hyp-G Replacement Assessment

The self-truncated velocity repair is the strongest positive result of the audit.

Files:

1. `Plan 2/WIP/WIP_TrimmedVelocityRepair.tex`
2. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`

Checks passed:

1. The low-gradient algebra is correct.
2. The estimate for `\int_{f<\bar f/2}1/f` follows from the weighted variance identity and the volume lower bound `|E_\rho|\ge \omega_n\rho_*^n`.
3. The velocity defect estimate

```tex
\left(\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}\right)^2
\le C D_H(\rho)
```

is valid on perimeter-controlled good levels.

4. The proof uses a perimeter good-level bound, not a pointwise lower bound for `|\nabla u|`.
5. No load-bearing global Hyp-G lower bound was found in the active WIP chain.

Major caveat:

The swept low-gradient control is proved only on the isoperimetric-good set `G_I`. This is enough for the current good-level metric derivative repair if bad levels are handled by a valid separate argument. It should not be stated as an unrestricted sweep estimate.

## Recommended Patch Order

1. Repair `WIP_LevelSetIdentity.tex`: no-atoms or atom-aware inverse theory, `I''=-1/alpha`, endpoint derivatives, and the missing Talenti/profile-gap bad-set lemma.
2. Repair `WIP_MetricFramework.tex`: replace the semicontinuity passage with a true upper-gradient proof and remove unsupported compactness/Lipschitz assertions from the manuscript.
3. Repair the FJ package: same-center theorem, scaling, measurable selection, and removal of centroid substitution from the load-bearing route.
4. Rebuild `WIP_WeightedMetricTrace.tex` using the repaired inputs; fix `rho_delta` smallness, `dt/d\rho` sign, and trace-lemma hypotheses.
5. Clean `WIP_BoundaryLayerTransfer.tex` and `WIP_GlobalAssembly.tex`: endpoint smallness, constants, finite-measure KJ scope, and stale wording.
6. After the Manuscript files are rewritten, run Agent H from the audit instruction file.

## Short Conclusion

Plan 2 is not closed yet. The trimmed velocity repair gives a credible replacement for Hyp-G, and the final boundary transfer preserves the sharp exponent. The proof now hinges on three rigorous upgrades: level-set measure theory/profile gap, finite-perimeter metric derivative, and same-center Fusco--Julin selection.

