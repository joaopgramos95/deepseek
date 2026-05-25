# Raw Moving-Ball Closure Audit Guideline

This file is a deployment guide for future manuscript-grade audits of
`faber_krahn_raw_moving_ball_closure.tex`. Do not deploy agents from this
file by itself. Its purpose is to give precise scopes, proof obligations, and
reporting standards for rigorous later checks of the raw moving-ball closure.

The source of truth is:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

## Current Status for Claude Verification

Status as of 2026-05-25:

```text
Candidate route: CLOSED IN THE TEX FILE
Certification status: NOT YET CERTIFIED
Required audit posture: hostile manuscript-grade verification
```

The previous multi-agent audit found the route blocked at the affine
shell/coarea step. The TeX file has since been patched, and a second local adversarial pass on
2026-05-25 further tightened the coarea exceptional-set language, the
critical-boundary justification, the BV-tail limiting argument, and the local
plus tail proof of the affine shell estimate. Claude should not re-audit the
obsolete proof; it should audit the current patched route.

Current patched locations:

```text
Section "A coarea differentiation lemma"              around line 615
Subsection "Shell-admissible radii"                    around line 691
Lemma "Local BV deformation tail"                      around line 746
Lemma "Affine shell estimate"                          around line 800
Theorem "One-sided first variation of q"               around line 947
Proposition "Positive kinetic bound"                   around line 1093
Section "Status of the repair"                         around line 1246
```

Prior blocking findings and claimed repairs:

```text
OLD BLOCKER 1:
The admissible-radius family depended on the tested radius through
    -w(rho), 1/rho, z, a.

PATCH CLAIM:
The file now registers a fixed countable family using rational parameters
    c, p, q, lambda, r, z, a, U
and defines "shell-admissible" radii by requiring Lemma varcoarea for every
registered pair. Claude must verify that this really gives a full-measure
set of radii and is strong enough for arbitrary real z,a in Lemma shell.

OLD BLOCKER 2:
The Borel coarea approximation error was measured against perimeter rather
than dH/|grad u|.

PATCH CLAIM:
Lemma varcoarea now uses the error
    2 eta * int_{partial*{u>s}} 1/|grad u| dH.
Claude must verify the full Borel-approximation argument, not just this line.

OLD BLOCKER 3:
The compact exhaustion in Lemma shell had no valid tail estimate outside the
interior compact set.

PATCH CLAIM:
The shell proof now splits the tail into
    (E_{rho+h} Delta E) outside U
and
    (E Delta T_h(E)) outside U.
The first is controlled by localized coarea. The second is controlled by the
new Local BV deformation-tail lemma. Claude must verify both estimates.
```

Bottom line for Claude:

```text
Treat the proof as a serious candidate, not as proved.
The route is closed only if the patched coarea/admissibility/BV-tail/shell
block survives line-by-line scrutiny.
```

The central claim to audit is that the unscaled moving-ball distance

```tex
q(\rho):=\inf_{z\in\mathbb R^n}|E_\rho\Delta B_\rho(z)|
```

closes the bad-density step in the level-set route to sharp bounded
Saint--Venant stability. In particular, nestedness should give an
unconditional Lipschitz bound for `q`, while the one-sided finite-perimeter
first variation should supply the positive kinetic estimate on good levels.

No verifier should edit source files unless separately instructed. The default
deliverable is an adversarial mathematical report. If Claude is used as a
single verifier, it should simulate the six scopes below and return a
sectioned report with one verdict per scope plus a consolidated verdict.

## Claude Master Prompt

Use the following prompt when handing this file to Claude:

```text
You are verifying a candidate manuscript-grade proof in
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex.

The route was previously blocked at the affine shell/coarea step, but the TeX
file has now been patched. Your job is to decide whether the patched route is
actually closed. Be adversarial and precise.

Read the TeX source first. Use this markdown file only as an audit guide. Do
not assume any claim is correct because it appears in the guide. Focus first
on the patched block:
  - variable-thickness coarea differentiation;
  - shell-admissible radii and the full-measure argument;
  - Local BV deformation tail;
  - Affine shell estimate;
  - use of Theorem qplus inside the positive kinetic estimate.

Return:
  1. a consolidated verdict: PASS / PASS WITH MAJOR GAPS / BLOCKED;
  2. one verdict for each audit scope A-F;
  3. all blocking or major findings with exact TeX locations;
  4. checks that genuinely passed;
  5. precise patch suggestions for every serious gap.

Do not give broad reassurance. A proof step passes only if the stated
hypotheses actually justify the conclusion with constants depending only on
(n,R,rho_*) and the explicitly imported constants.
```

## Context Files

Use these as supporting context, not as replacements for the source of truth.

```text
Blocks/Raw Moving Ball Closure/faber_krahn_remaining_steps.tex
Core/Assembled Manuscript/plan2_audit_agent_instructions.md
Audits/agent6-adversarial-audit.md
```

Consult the older level-set, Fusco--Julin/radial trace, and metric-framework
blocks only when a claim in the raw closure imports or contradicts them.

## Global Audit Rules

Every agent should classify findings as follows.

```text
BLOCKING: invalidates the route, the final theorem, or the sharp square rate.
MAJOR: serious proof gap, hidden assumption, bad citation, or uncontrolled constant.
MINOR: local clarification, notation issue, missing citation, or repairable exposition flaw.
NOTE: useful observation that does not affect correctness.
```

Every finding must include the exact claim being challenged, file and line
references when possible, why the justification is insufficient, and what
downstream step depends on it.

Hard-stop checks for every agent:

- No hidden pointwise lower bound on `|\nabla u|`.
- No hidden smoothness of level boundaries beyond BV/coarea/Sobolev-Sard facts.
- No invalid finite-perimeter Gauss--Green, coarea, or differentiation step.
- No misquoted Fusco--Julin theorem or unjustified same-centre conclusion.
- No return to the old rescaled metric route, graph parametrisation, BDV theorem,
  selection principle, or global Hyp-G mechanism.
- No rate loss to only `delta_T^{1/2}` at the level of squared asymmetry.
- No constants depending on uncontrolled geometry of `Omega` rather than only
  on `(n,R,rho_*)` and explicitly imported constants.

## Claude / Agent Deployment Plan

When requested, deploy the following six scopes. They can be assigned to
separate `gpt-5.4 high` agents, or Claude can run them sequentially as a
single hostile audit. Each scope should read the source file first and then
consult context only as needed.

### Agent A: End-to-End Dependency Audit

Scope:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

Tasks:

1. Reconstruct the proof graph from Proposition `levelset` through Theorem
   `boundedSV`.
2. Check that the final estimate
   `Fr(Omega)^2 <= C delta_T(Omega)` follows with constants depending only on
   `(n,R,rho_*)`.
3. Verify that the manuscript really avoids the old rescaled metric route,
   graph parametrisation, BDV theorem, selection principle, and global Hyp-G
   lower-gradient assumption.
4. Identify any theorem statement that is stronger than the lemmas actually
   prove.

### Agent B: Level-Set Import and Bad-Density Audit

Scope:

```text
Proposition levelset and its proof
all definitions of D_H, D_I, w, dmu, rho_delta, B_tau, G_tau
```

Tasks:

1. Verify the imported exact level-set identity and the change of variables
   `t=t(rho)`.
2. Check the normalization and nonnegativity of `D_H` and `D_I`.
3. Verify the profile-gap identity, including the factor
   `rho^n(a_B(rho)-a(rho))`.
4. Check the bounds `0 <= w(rho) <= rho/n <= 1/n`.
5. Verify `|B_tau| <= C delta_T(Omega)` with the stated threshold
   `tau_0=rho_*/(2n)`.
6. Confirm that the definition of `rho_delta` and the smallness regime are
   compatible with all later interval inclusions.

### Agent C: Fusco--Julin Same-Centre and Radial Trace Audit

Scope:

```text
Theorem FJ-strong
Corollary FJ-unnormalised
Lemma oriented-radial-trace
Theorem samecenter
Lemma center-transfer, only for centre transfer dependencies
```

Tasks:

1. Check whether the cited Fusco--Julin theorem is stated exactly strongly
   enough to give one common centre for symmetric difference and normal
   oscillation.
2. Verify scaling from the normalized FJ statement to radii
   `rho in [rho_*,1]`.
3. Check the passage from perimeter deficit to `D_I`.
4. Audit the finite-perimeter Gauss--Green proof in the radial trace lemma,
   including the singular center cutoff and the integrability of `1/|x-z|`.
5. Verify the conversion from normal oscillation plus symmetric difference to
   the homothetic trace bound for `H_{z,rho}`.
6. Check localization of the FJ centre and the later transfer to a
   distance-minimising centre.

### Agent D: Velocity Defect and Coarea Slab Audit

Scope:

```text
Lemma velocity
Section "A coarea differentiation lemma"
Lemma varcoarea
Subsection "Shell-admissible radii"
Lemma BV-tail
Lemma shell
```

Tasks:

1. Verify the identity
   ```tex
   \left(\int_{\partial^*E_\rho}|V_\rho-\bar V_\rho|\,d\mathcal H^{n-1}\right)^2
   \le D_H(t(\rho)).
   ```
2. Check every use of the flux identity, coarea parametrisation, and
   `w alpha = P(B_rho)`.
3. Audit the two-sided variable-thickness coarea differentiation lemma for
   bounded Borel endpoint functions.
4. Verify the analytic critical-set discard in Lemma `varcoarea`: it must be
   legitimate for bounded open `Omega`, possibly with many components.
5. Verify the countability/admissibility construction for the parameter
   family `(c,p,q,lambda,r,z,a,U)` and outward buffers.
6. Verify the pullback of exceptional level sets through the monotone
   absolutely continuous map `t`; the one-dimensional area formula must
   justify full-measure shell-admissible radii on `G_tau`.
7. Audit Lemma `BV-tail`: the mollification, change of variables, compact
   support/cutoff assumptions, strict `BV_loc` convergence, and order of
   `limsup_{h->0}` versus `epsilon->0`.
8. Check the affine shell limsup estimate for finite-perimeter levels,
   including:
   - local Taylor/slab inclusion on `U`;
   - dense rational parameters to arbitrary real `z,a`;
   - the level-set tail outside `U`;
   - the deformation tail outside `U`;
   - letting the compact-exhaustion error go to zero.
9. Confirm that no smooth foliation, graph parametrisation, hidden pointwise
   lower bound for `|grad u|`, or unstated normal transport theorem is used.

### Agent E: Moving-Ball First Variation and Kinetic Estimate

Scope:

```text
Theorem qplus
Lemma qLip
Lemma center-transfer
Proposition positivekinetic
```

Tasks:

1. Check existence of minimising centres for `q(rho)`.
2. Verify the affine comparison
   `T_h(B_rho(z_rho))=B_{rho+h}(z_rho+ha)`.
3. Check the Jacobian contribution
   `(1+h/rho)^n q(rho)` and the resulting `(n/rho)q(rho)` term.
4. Verify that the one-sided Dini derivative gives the correct a.e. bound for
   `q'_+`.
5. Check the nestedness proof of the unconditional Lipschitz bound for `q`.
6. Audit the good/bad decomposition in Proposition `positivekinetic`,
   including payment of bad-density levels by measure and payment of
   bad-isoperimetric good-density levels by the `D_I` budget.
7. Confirm that the estimate is genuinely in unweighted `d rho`, not only in
   `d mu`.

### Agent F: Endpoint Trace and Final Stability Transfer

Scope:

```text
Lemma superlevel-transfer
Lemma endpoint
Theorem boundedSV
```

Tasks:

1. Verify the superlevel-to-domain asymmetry transfer with the correct
   normalization for different ball volumes.
2. Check the endpoint interval
   `J=[rho_delta-L_0,rho_delta]` and the inclusion
   `J subset [rho_*,rho_delta]`.
3. Verify the averaging step that produces `rho_0 in J` with
   `q(rho_0)^2 <= C delta_T`.
4. Check the use of positive kinetic energy to propagate the bound from
   `rho_0` to `rho_delta`.
5. Verify the boundary-layer volume estimate
   `|Omega \ E_{rho_delta}| <= C sqrt(delta_T)`.
6. Check the final squaring and large-deficit fallback.
7. Confirm that the proof preserves the sharp squared asymmetry rate.

## Required Report Format

Each agent, or Claude for each simulated scope, must return:

```text
Verdict: PASS / PASS WITH MAJOR GAPS / BLOCKED

Claims audited:

Findings:

Checks passed:

Open mathematical questions:

Suggested patch targets:
```

Findings should be ordered by severity. If there are no findings at a given
severity, say so explicitly.

## Manuscript-Grade Standards

Agents should be adversarial but constructive. A finding is useful only if it
states exactly what is missing and what kind of lemma, citation, or correction
would close it.

Special scrutiny belongs to:

- the same-centre interpretation of Fusco--Julin;
- the finite-perimeter radial trace lemma;
- the variable-thickness coarea differentiation;
- the full-measure shell-admissible radius construction;
- the new Local BV deformation-tail lemma;
- the affine shell estimate;
- the transition from `D^+q` to `q'_+`;
- the bad-density bookkeeping in unweighted `d rho`;
- preservation of the final `Fr(Omega)^2 <= C delta_T` rate.

The report should distinguish genuine mathematical gaps from exposition gaps.
Do not accept a proof merely because the intended strategy is plausible.
