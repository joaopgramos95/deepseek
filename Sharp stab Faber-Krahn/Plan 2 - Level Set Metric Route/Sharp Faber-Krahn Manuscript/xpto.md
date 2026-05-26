# XPTO Agent Plan: Rigorous Attack on the FMP / Capacitary Workaround

This is the deployment brief for Claude agents. The goal is to turn the workaround sketched in `FK_exploratory_Serrin.tex`, Remark 5.3, into a rigorous replacement for the current constructive strong-form assumption.

The failed target is the global weighted Hessian estimate

\[
\int_\Omega u^2 |D^2u+I/n|^2 \le C(n)\delta_T(\Omega),
\]

which is false on punctured-ball examples. The replacement target is a geometric, level-by-level estimate based on the Fusco--Maggi--Pratelli oscillation index and a radial potential deficit.

Primary manuscript file: `FK_exploratory_Serrin.tex`.
Primary location: Remark 5.3, especially the FMP/capacitary workaround.
Primary source to audit: Fusco--Maggi--Pratelli, *The sharp quantitative isoperimetric inequality*, Annals of Mathematics 168 (2008), 941--980.

## Target Theorem

For every finite-perimeter set `E` satisfying

\[
|E|=|B_\rho|,\qquad E\subset B_R,\qquad \rho\in[\rho_*,1],
\]

prove that there is a centre `z=z_E` such that

\[
|E\Delta B_\rho(z)|^2+
\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
\le C(n,R,\rho_*)\bigl(P(E)-P(B_\rho)\bigr),
\tag{A}
\]

where `e_z(x)=(x-z)/|x-z|`. Applied to torsion superlevel sets `E_rho`, this gives

\[
|E_\rho\Delta B_\rho(z_\rho)|^2+
\int_{\partial^*E_\rho}|\nu_\rho-e_{z_\rho}|^2\,d\mathcal H^{n-1}
\le C(n,R,\rho_*)D_I(t(\rho)).
\tag{B}
\]

This should replace Assumption 5.2 on good levels and feed the homothetic trace estimate needed in the variation argument for `q`.

## Core Mechanism

For `|E|=|B_rho|`, define the FMP oscillation index

\[
\beta(E)^2:=P(E)-(n-1)\sup_y\int_E |x-y|^{-1}\,dx.
\]

FMP should provide

\[
\beta(E)^2\le C(n)(P(E)-P(B_\rho)).
\tag{1}
\]

Choose `z` maximizing the potential. Define

\[
\mathcal C_z(E):=(n-1)\int_{B_\rho(z)}|x-z|^{-1}\,dx
-(n-1)\int_E|x-z|^{-1}\,dx.
\]

Since `(n-1) int_{B_rho(z)} |x-z|^{-1} dx=P(B_rho)`, the chosen centre gives

\[
\beta(E)^2=P(E)-P(B_\rho)+\mathcal C_z(E).
\tag{2}
\]

Thus FMP controls the radial potential deficit:

\[
\mathcal C_z(E)\le C(n)(P(E)-P(B_\rho)).
\tag{3}
\]

A BV Gauss--Green identity for the radial vector field gives

\[
\frac12\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
=P(E)-P(B_\rho)+\mathcal C_z(E).
\tag{4}
\]

The remaining elementary geometric lemma is

\[
|E\Delta B_\rho(z)|^2\le C(n,R,\rho_*)\mathcal C_z(E).
\tag{5}
\]

Equations (3), (4), and (5) prove (A).

## Agent A: FMP Source Audit

Verify the exact oscillation-index statement in FMP.

Deliverables:

1. Locate the theorem proving (1).
2. Check whether FMP normalizes `|E|=|B_1|`; if yes, write the scaling to arbitrary `rho`.
3. Verify finite-perimeter hypotheses and absence of connectedness or smoothness assumptions.
4. Check whether `beta(E)` is squared or unsquared in their notation.
5. Produce a TeX-ready proposition and exact citation.

Red flags: do not accidentally import Fusco--Julin or a compactness-only strong form. The intended imported theorem is FMP oscillation index.

## Agent B: Radial BV Gauss--Green

Prove (4) for finite-perimeter sets.

Proof route:

1. Translate so `z=0`.
2. Approximate `e(x)=x/|x|` by smooth bounded radial fields `e_epsilon`.
3. Apply Gauss--Green on finite-perimeter sets.
4. Pass to the limit using local integrability of `|x|^{-1}` and dominated convergence on `partial^*E`.
5. Check the sign convention by testing on `E=B_rho(z)`, where `nu_E=e_z` and the left side is zero.

Deliverables: a TeX-ready lemma valid for all `n>=2`, including the cases `z in E`, `z in partial E`, and `z notin closure(E)`.

## Agent C: Potential Controls Same-Centre Volume

Prove (5) without using quantitative isoperimetry.

Proof route:

1. Translate `z=0`; write `B=B_rho`, `A=B\setminus E`, `F=E\setminus B`.
2. Since `|E|=|B|`, set `a=|A|=|F|`, so `|E Delta B|=2a`.
3. Use the bathtub principle. The potential loss is minimized by taking `A` to be the inner shell just inside `partial B_rho` and `F` to be the outer shell just outside `partial B_rho`.
4. Reduce to the one-dimensional shell calculation with `s_-` and `s_+` defined by

   \[
   |B_\rho\setminus B_{s_-}|=a,
   \qquad
   |B_{s_+}\setminus B_\rho|=a.
   \]

5. Prove

   \[
   \int_{B_\rho\setminus B_{s_-}}|x|^{-1}\,dx
   -\int_{B_{s_+}\setminus B_\rho}|x|^{-1}\,dx
   \ge c(n,R,\rho_*)a^2.
   \]

For small `a`, the first-order terms cancel and the second-order term is positive. For larger `a`, either keep the explicit formula or use a compactness argument over `rho in [rho_*,1]` and admissible `a`.

Deliverables: a fully written TeX lemma with constants depending only on `n,R,rho_*`.

Red flags: the bound must be quadratic in `|E Delta B|`, not linear. The constant is allowed to blow up as `rho_* downarrow 0`.

## Agent D: Homothetic Trace and Centre Transfer

Convert (A) into the trace estimate needed by the variation formula for `q`.

Target:

\[
\left(\int_{\partial^*E_\rho}|H_{z_\rho,\rho}-\bar V_\rho|\,d\mathcal H^{n-1}\right)^2
\le C(n,R,\rho_*)D_I(t(\rho)).
\tag{6}
\]

Important centre issue: the first variation of `q` uses a centre minimizing `z mapsto |E_rho Delta B_rho(z)|`; the FMP package gives a potential-maximizing centre. Use the existing transfer argument in the manuscript: small symmetric difference between the two balls forces the two centres close, except on a set of radii paid for by Chebyshev.

Deliverables:

1. TeX-ready trace proposition.
2. Explicit handling of transfer from the FMP centre to a Fraenkel-minimising centre.
3. A note identifying which parts of the current Assumption 5.2 become unnecessary.

## Agent E: Level-Set Integration

Apply the finite-perimeter theorem to `E_rho={u>t(rho)}`.

Steps:

1. Work only on good levels `rho in [rho_*,rho_delta]` where finite-perimeter and coarea identities hold.
2. Use

   \[
   D_I(t(\rho))=P(E_\rho)^2-P(B_\rho)^2
   =(P(E_\rho)-P(B_\rho))(P(E_\rho)+P(B_\rho)).
   \]

3. Since `rho>=rho_*`, bound

   \[
   P(E_\rho)-P(B_\rho)\le C(n,\rho_*)D_I(t(\rho)).
   \]

4. Integrate the resulting estimates against `dmu(rho)` and use the budget

   \[
   \int (D_H+D_I)\,d\mu\le C\delta_T(\Omega).
   \]

Deliverables: a manuscript patch replacing the integrated strong-form assumption on good levels.

## Agent F: Stress Tests

Test the proposed theorem on:

1. Punctured balls and annuli.
2. Off-centre tiny holes.
3. Disjoint unions of balls.
4. Long thin tentacles.
5. Highly oscillatory nearly spherical boundaries.
6. Shifted balls.

Expected outcome: the old Hessian route fails on punctures, but the FMP/capacitary route survives because perimeter and radial potential pay at the correct scale.

## Agent G: Final Manuscript Patch

Make the final TeX changes:

1. Add the FMP oscillation-index proposition.
2. Add the radial Gauss--Green lemma.
3. Add the potential-to-volume lemma.
4. Add the same-centre FMP/capacitary proposition.
5. Replace or discharge Assumption 5.2 on good levels.
6. Update Remark 5.3 so it says the Hessian route fails but the FMP route closes the needed geometric input.
7. Compile with `pdflatex -interaction=nonstopmode -halt-on-error FK_exploratory_Serrin.tex`.
8. Search the log for undefined references and citations.

Success criteria:

- The manuscript compiles.
- The final proof does not use the false weighted Hessian/L4 closure.
- The only substantial imported theorem is FMP oscillation index.
- The geometric input for the variation of `q` is fully proved.
