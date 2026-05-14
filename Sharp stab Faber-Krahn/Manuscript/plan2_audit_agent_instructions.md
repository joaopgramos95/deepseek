# Plan 2 Audit Agent Instructions

This file is a deployment plan for future audit agents. Do not deploy agents from this file by itself. Its purpose is to give precise scopes, proof obligations, and reporting standards for rigorous audits of the current Plan 2 route toward sharp Faber--Krahn stability.

The current source of truth is the condensed material in `Plan 2/WIP/`, especially `WIP_master.tex`. The files in `Manuscript/` are expected to change soon; when they are rewritten, agents should compare them against the WIP chain below and flag any drift.

## Final Goal

The target theorem is the sharp quantitative Faber--Krahn stability bound

```tex
\mathcal F r(\Omega)^2 \le C_n \, \delta_{FK}(\Omega),
```

via the torsional route, Kohler--Jobin transfer, and bounded reduction. Every local audit should be judged by whether it preserves the sharp square rate, keeps constants under control, and avoids hidden regularity or pointwise-gradient assumptions.

## Current Load-Bearing Chain

Agents should read `Plan 2/WIP/WIP_master.tex` first, then audit the following chain.

1. `Plan 2/WIP/WIP_LevelSetIdentity.tex`
2. `Plan 2/WIP/WIP_MetricFramework.tex`
3. `Plan 2/WIP/WIP_TrimmedVelocityRepair.tex`
4. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
5. `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`
6. `Plan 2/WIP/WIP_GlobalAssembly.tex`

Auxiliary diagnostics, not currently load-bearing unless explicitly promoted:

1. `Plan 2/WIP/WIP_CentroidBound.tex`
2. `Plan 2/WIP/WIP_SpaceTimeIdentity.tex`

Related manuscript or final files to consult when relevant:

1. `Manuscript/plan2_levelset_identity.tex`
2. `Manuscript/plan2_metric_framework.tex`
3. `Manuscript/plan2_fj_center_radial_trace.tex`
4. `Manuscript/plan2_weighted_metric_trace.tex`
5. `Manuscript/plan2_boundary_layer_assembly.tex`
6. `Final/BoundedReduction.tex`
7. `Final/KohlerJobinTransfer.tex`

## Global Audit Rules

Each agent should produce a report only unless separately instructed to edit files. Reports must be adversarial but constructive: identify exact gaps, explain why they matter for the final theorem, and state what lemma or correction would close them.

Findings must be classified as:

```text
BLOCKING: invalidates the route or loses the sharp square rate.
MAJOR: serious proof gap, hidden assumption, or unstable constant.
MINOR: local clarification, notation issue, missing reference, or repairable exposition flaw.
NOTE: useful observation that does not affect correctness.
```

Every finding should include file and line references when possible, the exact claim being challenged, the reason it is not yet justified, and the dependency it affects downstream.

Agents must explicitly check for stale assumptions. In particular, the old global Hyp-G type lower bound on `|\nabla u|` must not be used as a load-bearing hypothesis. The replacement mechanism is the self-truncated low-gradient/velocity repair in `WIP_TrimmedVelocityRepair.tex`.

## Hard Stop Conditions

Any of the following should be marked `BLOCKING`.

1. A hidden use of a pointwise lower bound `|\nabla u| \ge m_0` on full level boundaries.
2. A return to the old global Hyp-G mechanism instead of the trimmed velocity repair.
3. A load-bearing use of the centroid or space-time route without a complete proof in the current chain.
4. A ray-slicing or pointwise radial trace argument that is not justified for finite-perimeter sets.
5. A rate loss that gives only `\mathcal F r(\Omega) \lesssim \delta^{1/4}` or otherwise fails to recover the sharp square rate after transfer.
6. Constants depending on uncontrolled geometry of `\Omega` rather than only on the dimension and the bounded-reduction parameters.
7. A finite-perimeter divergence theorem, coarea step, or lower-semicontinuity passage used without the required hypotheses.
8. Failure of the good-level set selection to provide enough measure, enough profile gap, or the perimeter bounds needed by the velocity repair.

## Agent A: End-to-End Chain Audit

Scope:

```text
Plan 2/WIP/WIP_master.tex
Plan 2/WIP/HANDOFF.md
Plan 2/WIP/PAPER_PLAN.md
the six load-bearing WIP files listed above
```

Tasks:

1. Reconstruct the proof dependency graph from the WIP files.
2. Check that the route really proves a sharp squared Fraenkel-asymmetry estimate for torsion.
3. Verify that `CentroidBound` and `SpaceTimeIdentity` are not silently used as load-bearing inputs.
4. Check all constants and smallness regimes: dimension, bounded-reduction radius, inner collar endpoint, good-level windows, and deficit thresholds.
5. Identify any theorem statement in `WIP_master.tex` that is stronger than the supporting files prove.

Required output:

```text
Verdict: PASS / PASS WITH MAJOR GAPS / BLOCKED
Dependency graph:
Findings:
Checks passed:
Open questions:
Suggested patch targets:
```

## Agent B: Level-Set Identity Audit

Scope:

```text
Plan 2/WIP/WIP_LevelSetIdentity.tex
Manuscript/plan2_levelset_identity.tex
```

Tasks:

1. Verify the coarea identities for torsion level sets `E_t={u>t}` and the change of variables to the ball profile.
2. Check the corrected second-derivative identity, including the sign and normalization of the profile quantity, especially claims of the form `I''=-1/\alpha`.
3. Confirm that the deficit weights are exactly those needed downstream by `WeightedMetricTrace`.
4. Check that the level-set deficits are nonnegative in the required sense and match the isoperimetric or torsional comparison being used.
5. Identify every regular-level or approximation argument needed to pass from smooth levels to finite-perimeter levels.

Special scrutiny:

The audit should make sure there is no hidden assumption that the level boundaries are smooth for almost every level beyond what Sard/coarea/finite-perimeter theory gives.

## Agent C: Metric First-Variation Audit

Scope:

```text
Plan 2/WIP/WIP_MetricFramework.tex
Manuscript/plan2_metric_framework.tex
```

Tasks:

1. Check the quotient metric definition and the role of translations.
2. Verify the first-variation formula for moving finite-perimeter regions.
3. Check the translation mode `a \cdot \nu`, including the minimization or orthogonality condition used to quotient translations.
4. Audit the approximation scheme: smooth approximation, strict convergence, lower semicontinuity, and passage of boundary integrals.
5. Confirm that all metric derivative estimates are compatible with the velocity fields used later.

Special scrutiny:

The metric framework must not smuggle in smooth normal variations of rough sets without a clearly stated approximation theorem and lower-semicontinuity argument.

## Agent D: Hyp-G Replacement / Trimmed Velocity Repair Audit

Scope:

```text
Plan 2/WIP/WIP_TrimmedVelocityRepair.tex
Plan 2/WIP/WIP_WeightedMetricTrace.tex
```

This is the critical audit. The old Hyp-G lower-gradient hypothesis has been superseded by a self-truncated argument. The audit must decide whether that replacement is actually valid.

Tasks:

1. Check the definition of `f=|\nabla u|`, the average scale `\bar f`, and the low-gradient set `L_\rho={f<\bar f/2}`.
2. Verify the algebra proving

```tex
\int_{L_\rho} {1 \over f}\,d\mathcal H^{n-1}
    \le C\,D_H(\rho)
```

or the exact stated version, including constants and dimensional normalization.
3. Check how the perimeter good-level bound enters. In particular, confirm the proof only uses controlled perimeter excess, not a pointwise lower bound for `f`.
4. Verify the passage from the low-gradient estimate to the velocity defect estimate

```tex
\left(\int_{\partial^*E_\rho}
      |V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}\right)^2
      \le C\,D_H(\rho).
```

5. Check the treatment of the quadratic or high-velocity term, including any inequality of the form `\lambda^2 D_H \le C \lambda P(B_\rho)\beta`.
6. Confirm the swept low-gradient region is deficit-controlled and cannot affect the final boundary-layer transfer.
7. Identify exactly where the argument requires good levels, profile gap, or collar localization.

Special scrutiny:

Tiny remote components or tiny low-gradient regions must be disposable only because their total effect is controlled by the deficit. The report must verify this quantitatively, not merely heuristically.

## Agent E: Fusco--Julin and Oriented Radial Trace Audit

Scope:

```text
Plan 2/WIP/WIP_WeightedMetricTrace.tex
Manuscript/plan2_fj_center_radial_trace.tex
Manuscript/preliminaries_quant_isoperimetry.tex
```

Tasks:

1. Check the exact Fusco--Julin input used: statement, normalization, scaling, and dependence of constants.
2. Verify the selection and measurability of the FJ centers over the level-set family.
3. Confirm that the centers are sufficiently localized to support the radial trace and later boundary-layer transfer.
4. Audit the oriented radial trace identity: vector field, truncation, divergence calculation, boundary terms, and finite-perimeter justification.
5. Check the normal-oscillation-to-radial-trace passage and whether translation modes are correctly removed.
6. Verify that no ray-by-ray slicing argument is being used where the proof requires a divergence theorem argument.

Special scrutiny:

The FJ package should give a robust center and normal oscillation control. It should not be asked to prove more than the actual theorem supplies.

## Agent F: Weighted Metric Trace Audit

Scope:

```text
Plan 2/WIP/WIP_WeightedMetricTrace.tex
Plan 2/WIP/WIP_LevelSetIdentity.tex
Plan 2/WIP/WIP_MetricFramework.tex
Plan 2/WIP/WIP_TrimmedVelocityRepair.tex
```

Tasks:

1. Check the good/bad level decomposition and the measure estimate for bad levels.
2. Verify the weighted measure `d\mu`, the conversion between `dt` and `d\rho`, and all profile weights.
3. Check that the abstract trace lemma is applied with the right hypotheses: distance term, metric derivative term, endpoint control, and enough good-level mass.
4. Verify the Markov and Cauchy--Schwarz steps used to convert integrated action bounds into a pointwise or endpoint trace statement.
5. Confirm that the velocity repair from Agent D supplies exactly the missing metric derivative estimate.
6. Check endpoint choices, especially the boundary-collar endpoint `\rho_\delta`, and ensure its distance to the physical boundary is compatible with later transfer.

Special scrutiny:

This file is the bridge from integrated deficit to one good boundary-layer trace. It must not lose the square rate or rely on an unproved uniform-in-level estimate.

## Agent G: Boundary-Layer Transfer and Global Assembly Audit

Scope:

```text
Plan 2/WIP/WIP_BoundaryLayerTransfer.tex
Plan 2/WIP/WIP_GlobalAssembly.tex
Final/BoundedReduction.tex
Final/KohlerJobinTransfer.tex
```

Tasks:

1. Check the boundary-layer transfer from one good inner level to the original set `\Omega`.
2. Verify that the collar volume and symmetric-difference errors are of the required order and are squared only at the correct stage.
3. Check that the final estimate is for Fraenkel asymmetry modulo translations, not just a centered or radial discrepancy.
4. Audit the large-deficit branch and bounded-reduction argument.
5. Verify the Kohler--Jobin transfer from torsion stability to first-eigenvalue Faber--Krahn stability, including normalization and constants.
6. Confirm that final constants depend only on the dimension after bounded reduction.

Special scrutiny:

The transfer must not convert a sharp `\delta` control into a weaker square-root final estimate. Track every exponent explicitly.

## Agent H: Manuscript Integration Readiness Audit

Scope:

```text
Manuscript/
Plan 2/WIP/
Final/
```

Run this audit only after the Manuscript files are rewritten.

Tasks:

1. Compare each rewritten manuscript section against the corresponding WIP source.
2. Check that theorem and lemma names, equation labels, and notation are consistent across files.
3. Flag stale references to Hyp-G, the old centroid route, or an unsupported space-time argument.
4. Verify that the manuscript contains all hypotheses needed by each imported WIP lemma.
5. Check that every final theorem has a clear dependency path to the WIP proof chain or to an external cited theorem.

Required output:

```text
Verdict:
Mismatch table:
Stale claims:
Missing imports:
Notation conflicts:
Suggested manuscript patches:
```

## Report Standard

Each agent report should be short enough to be actionable but detailed enough that a proof author can patch the manuscript without rerunning the audit. Do not give generic approval. A useful report contains exact claims, exact missing hypotheses, and exact downstream consequences.

When a claim is correct but fragile, agents should say what makes it correct. When a claim is wrong, agents should propose the weakest plausible repair that preserves the final sharp theorem.
