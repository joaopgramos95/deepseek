# Manuscript Assembly Agent Brief

This file instructs Codex, Claude, or other LLM agents how to assemble the
full manuscript from the existing Plan 1, Plan 2, WIP, and Final building
blocks.

The manuscript must contain exactly the following major parts, in this order:

1. Introduction and history of the problem.
2. Preliminaries.
3. First proof: Plan 1 execution.
4. Second proof: Plan 2 execution.
5. References.

Later additions may add appendices or refinements, but this is the current
target structure.

## Non-Negotiable Standards

Use one agent per task. Do not assign two logically distinct tasks to the same
agent. The point is to keep every agent narrow enough to write with full rigor
and enough explanation.

Every agent must produce a source map. For each theorem, lemma, estimate, or
definition it writes, it must state one of:

- proved in the drafted manuscript section;
- copied/adapted from a named local building block;
- cited from the literature with exact theorem/proposition/page information;
- left as an explicitly named assumption or missing lemma.

Do not use vague status words such as "plausible", "standard", "known", or
"routine" unless immediately followed by a precise reference or proof.

Do not compress proofs. The Plan 1 proof must be written with detail at least
as complete as the local building blocks. The Plan 2 proof must be written with
detail substantially greater than the local building blocks, especially at the
finite-perimeter, metric-derivative, and radial-trace steps.

Do not hide constants. Constants may be denoted by symbols such as
\(C(n,R,\rho_*)\), but every dependence must be stated at the first use and
tracked through the section where it matters.

Do not assume smoothness unless the section is explicitly in a smooth
approximation subproof. The final statements must cover the stated finite
perimeter/open-set class.

Do not edit the final assembled manuscript until the relevant task draft has
passed an internal audit. Agents should write task-local drafts first, then the
assembly agent integrates them.

## Source Files

### Plan 1 Source Files

Use the following as the source of truth for the first proof:

- `Plan 1/README.md`
- `Plan 1/plan1.md`
- `Plan 1/quantitative-selection-principle.md`
- `Plan 1/quantitative-selection-principle.tex`
- `Plan 1/graph-entry-closure.md`
- `Plan 1/graph-entry-closure.tex`
- `Plan 1/route-A-summary.md`
- `Plan 1/route-A-summary.tex`
- `Plan 1/faber-krahn-transfer.md`
- `Plan 1/faber-krahn-transfer.tex`
- `Plan 1/PLAN1_AGENT_REPORT.md`
- `Final/SelectionPrinciple.tex`
- `Final/GraphEntry.tex`
- `Final/SchauderInterpolation.tex`
- `Final/NearlySphericalClosure.tex`
- `Final/SaintVenantAssembly.tex`
- `Final/BoundedReduction.tex`
- `Final/KohlerJobinTransfer.tex`
- `Final/master.tex`

The reliable Plan 1 route is:

\[
\text{selection principle}
\to \text{graph entry}
\to \text{Schauder/interpolation entry}
\to \text{BDV nearly spherical closure}
\to \text{sharp Saint--Venant}
\to \text{Kohler--Jobin transfer}
\to \text{sharp Faber--Krahn}.
\]

The Bernoulli spectral route in Plan 1 may be discussed as an alternative or
remark only if its conditional status is stated explicitly. It is not the main
Plan 1 proof.

### Plan 2 Source Files

Use the WIP files as the source of truth for the second proof:

- `Plan 2/WIP/PAPER_PLAN.md`
- `Plan 2/WIP/WIP_LevelSetIdentity.tex`
- `Plan 2/WIP/WIP_MetricFramework.tex`
- `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
- `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`
- `Plan 2/WIP/WIP_GlobalAssembly.tex`
- `Plan 2/WIP/WIP_CentroidBound.tex`
- `Plan 2/WIP/WIP_SpaceTimeIdentity.tex`
- `Plan 2/PLAN2_AGENT_REPORT.md`
- `Plan 2/level-set-deficit-identity.md`
- `Plan 2/gmt-inputs-for-metric-closure.md`
- `Plan 2/metric-finite-perimeter-closure.md`
- `Plan 2/wave3-J-route-delta-repair.md`

The current repaired Plan 2 route is:

\[
\text{LevelSetIdentity}
\to \text{MetricFramework}
\to \text{WeightedMetricTrace}
\to \text{BoundaryLayerTransfer}
\to \text{GlobalAssembly}.
\]

The centroid and space--time \(\Pi\) blocks are auxiliary diagnostics and may
be included as remarks, optional subsections, or alternate-route discussion.
They are not load-bearing for the repaired Plan 2 proof unless the manuscript
explicitly decides to present the centroid route as a separate conditional
argument.

The load-bearing Plan 2 mechanism is:

1. Exact level-set deficit identity:
   \[
   \delta_T(\Omega)
   \simeq
   \int (D_H(t)+D_I(t))\,w(t)\,dt.
   \]
2. Metric first variation in the quotient space \(\mathcal X\) of sets modulo
   translations.
3. Levelwise Fusco--Julin oscillation centers on good isoperimetric-defect
   levels.
4. Oriented radial-trace estimate:
   \[
   \int_{\partial^*E_\rho}
   \left|\frac{|x-z_\rho|}{\rho}-1\right|\,d\mathcal H^{n-1}
   \le
   C\left(
   |E_\rho\Delta B_\rho(z_\rho)|
   +
   \int_{\partial^*E_\rho}
   \left|\nu_\rho-\frac{x-z_\rho}{|x-z_\rho|}\right|^2d\mathcal H^{n-1}
   \right).
   \]
5. Fusco--Julin controls both terms by \(D_I(t(\rho))^{1/2}\) and
   \(D_I(t(\rho))\), respectively.
6. Good/bad level decomposition converts this to the integrated metric action.
7. Talenti/profile bad-set control converts weighted kinetic energy into
   Lebesgue kinetic energy.
8. Weighted metric trace finds \(\widehat\rho\) close to
   \(\rho_\delta=1-\kappa\sqrt{\delta_T}\).
9. Boundary-layer transfer returns from \(E_{\widehat\rho}\) to \(\Omega\).
10. Bounded reduction plus Kohler--Jobin gives Faber--Krahn.

## Manuscript Output Rules

The final manuscript should be a single coherent TeX manuscript. Before writing
that manuscript, agents must write intermediate section drafts and audits.

Recommended intermediate files:

- `Manuscript/00_notation_register.md`
- `Manuscript/01_preliminaries_draft.tex`
- `Manuscript/02_plan1_draft.tex`
- `Manuscript/03_plan2_draft.tex`
- `Manuscript/04_references_audit.md`
- `Manuscript/05_intro_story_draft.tex`
- `Manuscript/06_notation_unification_report.md`
- `Manuscript/main.tex`

If the `Manuscript/` directory does not exist, the assembly lead should create
it.

## Agent Deployment Plan

Deploy exactly one agent for each task below. Agents may read all source files
they need, but each agent must write only its assigned deliverable unless the
assembly lead explicitly asks for integration edits.

### Agent 0: Assembly Lead

Task: Create the working manuscript directory and maintain the global source
map.

Deliverables:

- `Manuscript/00_notation_register.md`
- `Manuscript/source_map.md`
- a list of all deployed agents and their deliverables

Responsibilities:

- decide global notation;
- prevent duplicate theorem numbering;
- record all literature references needed by later agents;
- ensure no agent silently changes hypotheses.

This agent does not write the Introduction, Plan 1 proof, or Plan 2 proof.

### Agent 1: Bibliography and Related Work Inventory

Task: Build the bibliography inventory before the Introduction is written.

Deliverable:

- `Manuscript/04_references_audit.md`

Required content:

- Brasco--De Philippis--Velichkov selection principle and quantitative
  Faber--Krahn/Saint--Venant work;
- Kohler--Jobin transfer;
- Fusco--Maggi--Pratelli quantitative isoperimetry;
- Fusco--Julin strong quantitative isoperimetry and oscillation index;
- Figalli--Maggi Sobolev--Sard/reduced-boundary level facts;
- Maggi/AFP finite-perimeter tools;
- Talenti rearrangement and Nicola--Tilli style convexity proof;
- any Faber--Krahn historical references already present in `Final/master.tex`
  and local bibliographies.

For every item, include:

- exact bibliographic data;
- theorem/proposition/page used;
- where it enters the manuscript;
- whether the manuscript should prove, cite, or sketch it.

### Agent 2: Preliminaries - Geometric Measure Theory

Task: Draft the finite-perimeter and coarea preliminaries.

Deliverable:

- a section draft to be included in `Manuscript/01_preliminaries_draft.tex`

Must include:

- finite perimeter, reduced boundary, perimeter notation;
- BV coarea theorem;
- slicing/coarea tools actually used;
- divergence theorem for finite-perimeter sets;
- truncation argument for vector fields with locally integrable singularity
  such as \(x/|x|\);
- \(L^1\) convergence and lower semicontinuity of perimeter;
- measurable selection statement used for levelwise centers.

Prove short facts when not cumbersome. Otherwise cite exact theorem numbers.

### Agent 3: Preliminaries - Torsion, Rearrangement, and Deficits

Task: Draft the torsion and rearrangement preliminaries.

Deliverable:

- a section draft to be included in `Manuscript/01_preliminaries_draft.tex`

Must include:

- torsion energy \(E(\Omega)\), torsional rigidity \(T(\Omega)\), and
  normalization;
- Saint--Venant deficit \(\delta_T\);
- Fraenkel asymmetry;
- Faber--Krahn deficit and eigenvalue normalization;
- Talenti comparison;
- volume-radius parametrization \(E_\rho=\{u>t(\rho)\}\);
- profile-gap estimates and bad-set estimates used in Plan 2;
- Kohler--Jobin inequality statement used in the final transfer.

### Agent 4: Preliminaries - Quantitative Isoperimetry and Oscillation

Task: Draft all quantitative isoperimetric preliminaries.

Deliverable:

- a section draft to be included in `Manuscript/01_preliminaries_draft.tex`

Must include:

- FMP quantitative isoperimetric inequality;
- Fusco--Julin strong form:
  \[
  \mathcal A(E)^2+\beta(E)^2\le C(n)\mathcal D(E);
  \]
- scaled version for \(|E|=|B_\rho|\), \(\rho\in[\rho_*,1]\);
- divergence identity converting \(\beta(E,z)^2\) into normal oscillation;
- exact hypotheses: finite perimeter, finite measure, boundedness when needed.

The scaled form must be written explicitly with constants depending only on
\(n,R,\rho_*\) where relevant.

### Agent 5: Plan 1 - Selection Principle

Task: Write the full selection-principle part of Plan 1.

Sources:

- `Plan 1/quantitative-selection-principle.tex`
- `Final/SelectionPrinciple.tex`
- BDV source paper in `Plan 1`

Deliverable:

- subsection draft for `Manuscript/02_plan1_draft.tex`

Required level of detail:

- define the penalized selection problem;
- prove existence and compactness;
- prove preservation of the deficit-to-asymmetry ratio;
- state all constants and thresholds;
- make clear where volume normalization enters.

### Agent 6: Plan 1 - Graph Entry and Regularity

Task: Write the full graph-entry and regularity part of Plan 1.

Sources:

- `Plan 1/graph-entry-closure.tex`
- `Final/GraphEntry.tex`
- `Final/SchauderInterpolation.tex`

Deliverable:

- subsection draft for `Manuscript/02_plan1_draft.tex`

Required level of detail:

- explain how the selected minimizer enters the graph regime;
- state the regularity theorem used;
- track the threshold from small asymmetry to \(C^{1,\gamma}\) and then to the
  \(C^{2,\gamma_0}\)-small regime;
- include interpolation and Schauder details at least as detailed as the
  building blocks.

### Agent 7: Plan 1 - Nearly Spherical Closure and Saint--Venant

Task: Write the BDV nearly-spherical closure and sharp Saint--Venant conclusion.

Sources:

- `Plan 1/route-A-summary.tex`
- `Final/NearlySphericalClosure.tex`
- `Final/SaintVenantAssembly.tex`

Deliverable:

- subsection draft for `Manuscript/02_plan1_draft.tex`

Required level of detail:

- state the nearly-spherical theorem exactly;
- show how graph parametrization, barycenter/translation normalization, and
  volume constraint are enforced;
- carry the contradiction or direct estimate to
  \[
  \mathcal A(\Omega)^2\le C\,\delta_T(\Omega)
  \]
  in the bounded class.

### Agent 8: Plan 1 - Kohler--Jobin and Faber--Krahn Transfer

Task: Write the final Plan 1 transfer to Faber--Krahn.

Sources:

- `Plan 1/faber-krahn-transfer.tex`
- `Final/BoundedReduction.tex`
- `Final/KohlerJobinTransfer.tex`

Deliverable:

- final subsection draft for `Manuscript/02_plan1_draft.tex`

Required level of detail:

- include bounded reduction;
- state Kohler--Jobin with correct normalization;
- derive the sharp Faber--Krahn asymmetry estimate with constants.

### Agent 9: Plan 2 - Level-Set Deficit Identity

Task: Write the exact level-set deficit identity with full finite-perimeter
detail.

Sources:

- `Plan 2/WIP/WIP_LevelSetIdentity.tex`
- `Plan 2/level-set-deficit-identity.tex`

Deliverable:

- first subsection draft for `Manuscript/03_plan2_draft.tex`

Required level of detail:

- prove coarea identities for a.e. reduced-boundary level;
- prove weak divergence/flux identity;
- prove the corrected \(I''\) formula;
- derive the exact deficit identity with \(D_H+D_I\);
- include the profile-gap and bad-set consequences needed later.

### Agent 10: Plan 2 - Metric Framework

Task: Write the metric quotient and first-variation theorem.

Sources:

- `Plan 2/WIP/WIP_MetricFramework.tex`
- `Plan 2/gmt-inputs-for-metric-closure.md`
- `Plan 2/metric-finite-perimeter-closure.md`

Deliverable:

- subsection draft for `Manuscript/03_plan2_draft.tex`

Required level of detail:

- define \(\mathcal X\) and prove/quote metric facts;
- prove absolute continuity of \(\rho\mapsto[F_\rho]\);
- derive the finite-perimeter metric first-variation bound;
- justify the normal velocity \(V_\rho=-t'(\rho)/|\nabla u|\);
- write the smooth-flow proof and then the finite-perimeter passage.

This agent must not assume global Lipschitz boundary regularity.

### Agent 11: Plan 2 - Fusco--Julin Center and Oriented Radial Trace

Task: Write the center package and radial-trace proof in full detail.

Sources:

- `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
- `Plan 2/gmt-inputs-for-metric-closure.md`

Deliverable:

- subsection draft for `Manuscript/03_plan2_draft.tex`

Required level of detail:

- state and scale Fusco--Julin;
- choose a bounded Borel center field on good levels;
- prove Fraenkel and normal oscillation bounds;
- prove the oriented radial trace lemma:
  \[
  T_\rho
  \le
  C\left(
  |E_\rho\Delta B_\rho(z_\rho)|
  +
  \int_{\partial^*E_\rho}
  \left|\nu_\rho-\frac{x-z_\rho}{|x-z_\rho|}\right|^2
  d\mathcal H^{n-1}
  \right).
  \]

The proof must include the vector field
\[
X(x)=\left|\frac{|x-z_\rho|}{\rho}-1\right|\frac{x-z_\rho}{|x-z_\rho|}
\]
and the finite-perimeter divergence/truncation argument. This is a critical
load-bearing lemma. Do not replace it with a vague ray-slicing claim.

### Agent 12: Plan 2 - Integrated Action and Weighted Metric Trace

Task: Write the integrated action and weighted metric trace argument.

Sources:

- `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
- `Plan 2/WIP/WIP_MetricFramework.tex`
- `Plan 2/WIP/WIP_LevelSetIdentity.tex`

Deliverable:

- subsection draft for `Manuscript/03_plan2_draft.tex`

Required level of detail:

- define good and bad isoperimetric-defect levels;
- prove the Markov bound for bad levels;
- combine \(D_H\), FJ, and oriented radial trace into
  \[
  \int(d_\mathcal X(F_\rho,B_1)^2+|\dot F_\rho|_\mathcal X^2)\,d\mu
  \le C\delta_T;
  \]
- prove the bad-\(-t'\) decomposition and Lebesgue kinetic bound;
- prove the abstract weighted metric trace lemma;
- derive existence of \(\widehat\rho\).

### Agent 13: Plan 2 - Boundary-Layer Transfer and Global Assembly

Task: Write the Plan 2 final transfer and global conclusion.

Sources:

- `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`
- `Plan 2/WIP/WIP_GlobalAssembly.tex`
- `Final/BoundedReduction.tex`
- `Final/KohlerJobinTransfer.tex`

Deliverable:

- final subsection draft for `Manuscript/03_plan2_draft.tex`

Required level of detail:

- estimate the removed layer
  \(|\Omega\setminus E_{\widehat\rho}|=O(\sqrt{\delta_T})\);
- prove the superlevel transfer of asymmetry;
- square the transfer error without losing the sharp exponent;
- perform bounded reduction and Kohler--Jobin transfer;
- state the final Plan 2 theorem in the same normalization as Plan 1.

### Agent 14: Plan 2 Auxiliary Route Note

Task: Write a short optional note on the centroid/space--time \(\Pi\) route.

Sources:

- `Plan 2/WIP/WIP_CentroidBound.tex`
- `Plan 2/WIP/WIP_SpaceTimeIdentity.tex`

Deliverable:

- optional remark/subsection draft for `Manuscript/03_plan2_draft.tex`

Required content:

- centroid kinematic identity;
- space--time \(\Pi\) identity;
- explain that this route is auxiliary unless the integrated \(\Pi\)-control
  estimate is proved;
- do not present it as load-bearing for the repaired proof.

### Agent 15: Internal Audit Agent - Plan 1

Task: Audit the Plan 1 draft against the source blocks.

Deliverable:

- `Manuscript/audit_plan1.md`

Audit checklist:

- every theorem has hypotheses;
- every constant dependence is stated;
- no conditional Bernoulli route is accidentally used as unconditional;
- bounded reduction and Kohler--Jobin normalization match the final theorem;
- no proof is shorter or less rigorous than its source block.

### Agent 16: Internal Audit Agent - Plan 2

Task: Audit the Plan 2 draft against the source blocks.

Deliverable:

- `Manuscript/audit_plan2.md`

Audit checklist:

- no load-bearing use of the centroid \(\Pi\)-route;
- finite-perimeter first variation is not smoothed away without a recovery
  argument;
- Fusco--Julin is scaled correctly;
- oriented radial trace is proved, not handwaved;
- good/bad level split preserves the \(\delta_T\) rate;
- weighted metric trace uses both weighted action and Lebesgue kinetic bounds;
- boundary-layer transfer squares the \(O(\sqrt{\delta_T})\) layer correctly.

### Agent 17: Notation and Normalization Unification Agent

Task: After the Plan 1 and Plan 2 drafts exist, unify notation across the
whole manuscript.

Deliverable:

- `Manuscript/06_notation_unification_report.md`
- edits or patch instructions for the section drafts

Must unify:

- dimension notation: choose \(n\), not \(N\), unless quoting;
- ball notation \(B_r(z)\), \(B_1\), \(B^*\);
- torsion energy sign convention;
- Saint--Venant deficit notation;
- Faber--Krahn deficit notation;
- Fraenkel asymmetry notation;
- \(\rho_*\), \(\rho_\delta\), \(\widehat\rho\);
- \(\mathcal X\), \(F_\rho\), \(E_\rho\);
- constants \(C,c,\delta_0,\kappa\).

This agent must run before the Introduction agent writes the final story.

### Agent 18: Introduction and Historical Story Agent

Task: Write the Introduction last, after references and notation are unified.

Deliverable:

- `Manuscript/05_intro_story_draft.tex`

Required content:

- history of the Faber--Krahn inequality;
- Saint--Venant/torsion analogue;
- quantitative stability problem and sharp exponent;
- selection-principle/BDV route and its role;
- quantitative isoperimetry background;
- Kohler--Jobin bridge;
- Nicola--Tilli/rearrangement/level-set viewpoint;
- what Plan 1 proves and why it is included;
- what Plan 2 proves and why it is structurally different;
- precise statement of the two proofs in the paper;
- related work, with as many relevant references as supported by
  `Manuscript/04_references_audit.md`.

This agent must tell a coherent mathematical story, but must not introduce
new claims not already supported by the body or reference audit.

### Agent 19: Final Assembly Agent

Task: Assemble the final TeX manuscript.

Deliverable:

- `Manuscript/main.tex`

Required actions:

- integrate all audited drafts;
- create theorem environments and numbering;
- include the bibliography;
- compile the manuscript;
- fix local cross-references;
- produce a final source map linking each manuscript section to its agent
  draft and source files.

This agent may edit the final manuscript but should not rewrite proofs unless
an audit item explicitly requires it.

### Agent 20: Final Adversarial Audit Agent

Task: Perform the last review after `Manuscript/main.tex` compiles.

Deliverable:

- `Manuscript/final_adversarial_audit.md`

Audit questions:

- Is every result in the preliminaries either proved or precisely cited?
- Does Plan 1 really close without conditional Bernoulli spectral inputs?
- Does Plan 2 really close without centroid \(\Pi\)-control?
- Does the oriented radial trace proof work for finite-perimeter sets?
- Are the two final theorem statements normalized identically?
- Are any constants claimed universal when they depend on \(R\) or
  \(\rho_*\)?
- Are all references present and used?
- Does the Introduction overstate the novelty or the status of any route?

The final audit should lead with findings, ordered by severity. If no blocking
findings remain, say so explicitly.

## Required Final Theorem Format

Both Plan 1 and Plan 2 sections should culminate in a theorem of the following
form, with the exact constants and normalizations chosen by the notation agent:

\[
\mathcal A(\Omega)^2\le C(n)\,\delta_{\mathrm{FK}}(\Omega)
\]

for the sharp quantitative Faber--Krahn inequality, after reduction from the
bounded Saint--Venant form

\[
\mathcal A(\Omega)^2\le C(n,R)\,\delta_T(\Omega).
\]

If the manuscript states bounded intermediate theorems, make the dependence on
\(R\) explicit and explain how bounded reduction removes it.

## Assembly Order

Use this order. Do not start later integration before earlier audits exist.

1. Agent 0 creates notation register and source map.
2. Agent 1 creates bibliography and related-work inventory.
3. Agents 2--4 draft preliminaries in parallel.
4. Agents 5--8 draft Plan 1 in parallel only after Agent 0 has fixed notation.
5. Agents 9--14 draft Plan 2 in parallel only after Agent 0 has fixed notation.
6. Agent 15 audits Plan 1.
7. Agent 16 audits Plan 2.
8. Agent 17 unifies notation and normalizations.
9. Agent 18 writes the Introduction and historical story.
10. Agent 19 assembles `Manuscript/main.tex`.
11. Agent 20 performs final adversarial audit.

## Stop Conditions

An agent must stop and flag a blocking issue if it finds:

- a theorem used without proof or reference;
- a hidden smoothness assumption in a finite-perimeter section;
- a rate loss that changes \(\delta_T\) into \(\sqrt{\delta_T}\);
- an unconditional statement relying on the conditional Bernoulli route;
- an unconditional statement relying on the centroid \(\Pi\)-route;
- inconsistent normalization between Plan 1 and Plan 2.

Flagging a blocking issue is not a failure. Hiding it is.

