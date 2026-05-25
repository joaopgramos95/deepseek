# Self-Contained Manuscript Integration Plan

Source manuscript to grow:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

Purpose:

This plan is for turning the candidate moving-ball closure into a true
self-contained manuscript. "Self-contained" here means that every necessary
result currently imported from the repository is either proved in the
manuscript, quoted with an exact external citation, or stated as a clearly
named external theorem with no hidden repo dependency.

The target reader should not need to inspect other repo files to verify the
argument.

## Global Output Standard

Claude should produce a concrete integration plan first, then a patch plan.
Do not edit the TeX until each imported dependency has been classified.

Classification labels:

```text
INTERNAL: already fully proved in the TeX.
EXTERNAL-CITED: can remain as a named published theorem with exact citation.
REPO-IMPORT: currently depends on another repo block and must be integrated.
MISSING: used but not proved or cited.
REMOVE: unnecessary or misleading statement.
```

## Phase 1: Build the Dependency Inventory

Read the TeX and create a dependency table with columns:

```text
Label / theorem name
Current location in TeX
Used by
Status: INTERNAL / EXTERNAL-CITED / REPO-IMPORT / MISSING / REMOVE
Required action
```

At minimum classify:

```text
Exact level-set deficit identity
Flux identity on reduced-boundary level sets
Profile derivative gap identity
Bad-density estimate |B_tau| <= C delta_T
Finite-perimeter superlevel package
Fusco--Julin strong quantitative isoperimetry
Unnormalised same-centre consequences
Oriented radial trace lemma
Same-centre good-level geometric package
Velocity defect bound
Variable-thickness coarea lemma
Shell-admissible radii
Local BV deformation tail
Affine shell estimate
One-sided first variation of q
Unconditional Lipschitz bound for q
Centre-transfer lemma
Positive kinetic estimate
Endpoint trace
Superlevel-to-domain asymmetry transfer
Large-deficit fallback
```

Deliverable:

```text
dependency-inventory table
list of items that must be integrated from repository files
list of items that may remain external citations
```

## Phase 2: Integrate the Level-Set Identity Block

Current risk:

The manuscript still imports the exact level-set identity and associated
profile-gap information from the repository's `LevelSetIdentity` block.
For a self-contained manuscript, this is the largest missing body of proof.

Relevant local repo files to inspect:

```text
Blocks/Level Set Identity/LevelSetIdentity.tex
Blocks/Level Set Identity/level-set-deficit-identity.tex
```

Tasks:

1. Extract the exact theorem statement actually needed here.
2. Integrate definitions of:
   ```tex
   m(t), alpha(t), D_H(t), D_I(t), t(rho), w(rho), dmu
   ```
   without conflicting notation.
3. Prove or cite the finite-perimeter superlevel facts:
   finite perimeter for a.e. level, coarea identities, normal convention.
4. Prove the reduced-boundary flux identity
   ```tex
   int_{partial*{u>t}} |grad u| dH = |{u>t}|
   ```
   using the weak torsion equation and admissible truncations.
5. Derive the exact deficit identity.
6. Derive the profile derivative gap identity:
   ```tex
   int_0^1 rho^n (rho/n - w(rho)) d rho = 2 delta_T / omega_n.
   ```
7. Derive `0 <= w <= rho/n` and the bad-density estimate.
8. Remove language saying the result is "imported from the repository".

Deliverable:

```text
new self-contained section outline
proof snippets to import
TeX patch targets
remaining external citations, if any
```

## Phase 3: Normalize External Published Theorems

External theorems that may remain cited:

```text
Fusco--Julin strong quantitative isoperimetry
standard BV coarea theorem
finite-perimeter Gauss--Green theorem
strict BV convergence / Reshetnyak continuity
basic elliptic interior analyticity or unique continuation for torsion
```

Tasks:

1. Check every external theorem is stated in exactly the needed form.
2. Add precise citations for:
   - BV coarea;
   - finite-perimeter Gauss--Green;
   - strict BV convergence of mollifications;
   - Reshetnyak continuity for continuous compactly supported weights;
   - interior regularity/analyticity for `-Delta u=1`.
3. Decide whether Fusco--Julin should be quoted as a theorem or restated as
   an input with exact bibliographic reference.
4. Remove unused bibliography entries and add missing ones.

Deliverable:

```text
external theorem list
exact citation targets
bibliography patch list
```

## Phase 4: Make the Moving-Ball Core Self-Contained

The moving-ball core should remain in the manuscript, but it needs all local
technical lemmas written at full strength.

Tasks:

1. Keep and polish:
   ```text
   varcoarea
   shell-admissible radii
   BV-tail
   affine shell estimate
   qplus
   qLip
   positivekinetic
   endpoint
   boundedSV
   ```
2. Add a short "regularity and level conventions" subsection before the
   coarea block, collecting:
   - orientation of `nu_rho`;
   - relation `nu_rho=-grad u/|grad u|`;
   - finite-perimeter level conventions;
   - how all a.e. radius sets are intersected.
3. Make every null-set restriction explicit:
   - finite perimeter;
   - flux identity;
   - `t` differentiability;
   - coarea admissibility;
   - `q` differentiability.
4. Add a named proposition collecting "full-measure good radii" so later
   proofs do not repeatedly reassemble null sets.
5. Expand any "standard" finite-perimeter step that is actually load-bearing.

Deliverable:

```text
moving-ball self-contained patch checklist
new propositions/lemmas to introduce
statements to shorten or relocate
```

## Phase 5: Restructure the Manuscript

Recommended final structure:

```text
1. Introduction and theorem statement
2. Notation, torsion preliminaries, and Fraenkel asymmetry
3. Finite-perimeter level-set identities
4. Profile gap and bad-density estimate
5. Quantitative isoperimetry and same-centre trace control
6. Coarea differentiation and shell-admissible radii
7. Affine moving-ball first variation
8. Positive kinetic estimate
9. Endpoint trace and proof of bounded Saint--Venant stability
Appendix A. BV tools used
Appendix B. Constants and dependency map
```

Tasks:

1. Move imported level-set proofs before they are used.
2. Move same-centre/Fusco--Julin material before kinetic estimates.
3. Move all pure BV technical tools either before the shell proof or into an
   appendix.
4. Ensure theorem numbering and labels remain stable.
5. Replace the "Status of the repair" section with a manuscript-appropriate
   "Proof architecture and constants" section or remove it.

Deliverable:

```text
new table of contents
section-by-section move plan
labels that must be preserved
labels that should be renamed
```

## Phase 6: Constants and Quantifiers Audit

Tasks:

1. Track every constant and verify dependence only on:
   ```text
   n, R, rho_*
   ```
   plus explicitly cited universal constants.
2. Track every smallness threshold:
   ```text
   delta_0, eta_I, kappa, tau_0, L_0
   ```
3. Verify the large-deficit fallback closes the theorem without hidden
   regularity assumptions.
4. Add a final constants paragraph that is honest but not bloated.

Deliverable:

```text
constant-dependency table
smallness-threshold table
patches needed for incorrect dependencies
```

## Phase 7: Final Manuscript QA

Tasks:

1. Compile the TeX twice with:
   ```text
   pdflatex -interaction=nonstopmode -halt-on-error
   ```
2. Search for stale phrases:
   ```text
   imported from the repository
   raw
   repair
   status
   TODO
   input
   assumed
   old route
   blocked
   candidate
   ```
3. Search for hidden-risk phrases:
   ```text
   smooth boundary
   regular level
   graph
   pointwise lower bound
   selection principle
   BDV
   Hyp-G
   ```
4. Check all references and citations.
5. Produce a final dependency certificate saying what is proved internally
   and what remains externally cited.

Deliverable:

```text
final QA report
compile status
remaining manuscript risks
dependency certificate
```

## Final Claude Output

Claude should return:

```text
1. Dependency inventory
2. Self-contained manuscript outline
3. Exact repo material to integrate
4. External theorem/citation list
5. Concrete TeX patch sequence
6. Risks that remain even after integration
```

The goal is not a longer manuscript for its own sake. The goal is a manuscript
whose proof can be checked from the file itself, with no hidden dependency on
other repository blocks except for explicitly cited published theorems.
