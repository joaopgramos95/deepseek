# XPTO: Rigorous Attack Plan for the FMP / Capacitary Workaround

This file is a deployment brief for Claude agents. The goal is to turn the workaround currently sketched in `FK_exploratory_Serrin.tex`, Remark 5.3, into a fully rigorous replacement for the failed global weighted Hessian route.

The mathematical target is not to prove the false Hessian estimate

\[
\int_\Omega u^2 |D^2u+I/n|^2 \le C(n)\,\delta_T(\Omega),
\]

which is ruled out by punctured-ball examples. The target is to bypass it by proving a radial capacitary trace estimate on almost-isoperimetric torsion superlevel sets, using the Fusco--Maggi--Pratelli oscillation-index estimate.

Primary manuscript location: `Sharp Faber-Krahn Manuscript/FK_exploratory_Serrin.tex`, especially Remark 5.3, part (10).

Primary external source to audit:

- Fusco--Maggi--Pratelli, *The sharp quantitative isoperimetric inequality*, Annals of Mathematics 168 (2008), 941--980.
- Annals page: https://annals.math.princeton.edu/2008/168-3/p06
- PDF: https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n3-p06.pdf

## 1. End Goal

Replace the provisional strong-form assumption with a theorem of the following shape.

Let `E` be a finite-perimeter set with

\[
|E|=|B_\rho|, \qquad E\subset B_R, \qquad \rho\in[\rho_*,1].
\]

Then there exists a center `z=z_E` such that, with `B=B_\rho(z)` and `e_z(x)=(x-z)/|x-z|`, one has

\[
|E\Delta B|^2+\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
\le C(n,R,\rho_*)\bigl(P(E)-P(B_\rho)\bigr).
\tag{A}
\]

For torsion superlevel sets `E_t={u>t}`, parameterized by the radius `rho(t)` through `|E_t|=|B_{rho(t)}|`, this should imply on the good range `rho(t) >= rho_*`

\[
|E_t\Delta B_{\rho(t)}(z_t)|^2
+\int_{\partial^*E_t}|\nu_{E_t}-e_{z_t}|^2\,d\mathcal H^{n-1}
\le C(n,R,\rho_*)D_I(t),
\tag{B}
\]

where

\[
D_I(t)=P(E_t)^2-P(B_{\rho(t)})^2.
\]

This gives the missing same-centre information without using any pointwise gradient control or any global `L^4` Hessian closure.

## 2. Core Definitions to Use

For a finite-perimeter set `E` with `|E|=|B_rho|`, define the FMP oscillation index

\[
\beta(E)^2
:= P(E)-(n-1)\sup_{y\in\mathbb R^n}\int_E \frac{dx}{|x-y|}.
\tag{1}
\]

For a chosen center `z`, define the radial potential deficit

\[
\mathcal C_z(E)
:=(n-1)\int_{B_\rho(z)}\frac{dx}{|x-z|}
-(n-1)\int_E\frac{dx}{|x-z|}.
\tag{2}
\]

Since

\[
(n-1)\int_{B_\rho(z)}\frac{dx}{|x-z|}=P(B_\rho),
\]

choosing `z` to maximize the potential gives the exact decomposition

\[
\beta(E)^2=P(E)-P(B_\rho)+\mathcal C_z(E).
\tag{3}
\]

FMP should give

\[
\beta(E)^2\le C_\beta(n)\bigl(P(E)-P(B_\rho)\bigr).
\tag{4}
\]

Therefore

\[
\mathcal C_z(E)\le (C_\beta(n)-1)_+\bigl(P(E)-P(B_\rho)\bigr).
\tag{5}
\]

The radial Gauss--Green identity should give

\[
\frac12\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
=P(E)-P(B_\rho)+\mathcal C_z(E),
\tag{6}
\]

hence, together with (4),

\[
\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
\le 2C_\beta(n)\bigl(P(E)-P(B_\rho)\bigr).
\tag{7}
\]

The remaining non-FMP ingredient is the same-centre volume estimate

\[
|E\Delta B_\rho(z)|^2\le C(n,R,\rho_*)\mathcal C_z(E).
\tag{8}
\]

Equations (5), (7), and (8) imply (A).

## 3. Agent Assignments

Run these as separate agents. Each agent should produce a short proof memo plus a TeX-ready lemma/proposition block.

### Agent A: FMP Oscillation-Index Audit

Task: Verify the exact statement needed from Fusco--Maggi--Pratelli.

Deliverables:

1. Locate the theorem/lemma in FMP proving

   \[
   \beta(E)^2\le C(n)\bigl(P(E)-P(B_\rho)\bigr)
   \]

   for arbitrary finite-perimeter sets of volume `|B_rho|`.

2. Check scaling. If FMP states the result for `|E|=|B_1|`, write the dilation argument explicitly:

   - `P(lambda E)=lambda^{n-1}P(E)`.
   - `int_{lambda E}|x-y|^{-1}dx = lambda^{n-1} int_E |x-y/lambda|^{-1}dx`.
   - Therefore `beta(lambda E)^2=lambda^{n-1} beta(E)^2`.

3. Check hypotheses: finite perimeter, measurable set, positive finite volume, no connectedness, no smoothness.

4. Check the convention for normals and whether FMP uses `nu_E` or `-nu_E`; this affects signs in the Gauss--Green identity but not the squared norm.

5. Provide a BibTeX entry if the manuscript does not already have one named `FMP`.

Red flags:

- If FMP defines `beta(E)` with a square root or with normalized perimeter deficit, translate carefully.
- If FMP only proves the bound after choosing a center in a restricted class, record the precise center selection.
- Do not replace FMP by Fusco--Julin; the point of this workaround is to avoid the stronger machinery unless absolutely necessary.

### Agent B: BV Gauss--Green Identity with Singular Radial Field

Task: Prove rigorously that

\[
\frac12\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
=P(E)-(n-1)\int_E |x-z|^{-1}\,dx.
\tag{9}
\]

Since `|E|=|B_rho|`, equation (9) is equivalent to (6).

Proof skeleton:

1. Use the vector field

   \[
   e_z(x)=\frac{x-z}{|x-z|}.
   \]

   Its distributional divergence away from `z` is

   \[
   \operatorname{div} e_z = \frac{n-1}{|x-z|}.
   \]

2. Start with a smooth truncation `e_{z,epsilon}` such as

   \[
   e_{z,\epsilon}(x)=\frac{x-z}{\max\{|x-z|,\epsilon\}}
   \]

   or a smooth radial approximation. Apply the Gauss--Green theorem for finite-perimeter sets.

3. Let `epsilon downarrow 0`. Justify:

   - `|e_{z,epsilon}| <= 1` and `e_{z,epsilon} -> e_z` away from `z`.
   - The boundary integral converges by dominated convergence on `partial^*E`; a single point has zero `H^{n-1}` measure.
   - The volume integral converges because `|x-z|^{-1}` is locally integrable for every `n >= 2`.

4. Use

   \[
   |\nu_E-e_z|^2=2-2\nu_E\cdot e_z
   \]

   and the finite-perimeter identity

   \[
   \int_{\partial^*E}\nu_E\cdot e_z\,d\mathcal H^{n-1}
   =(n-1)\int_E |x-z|^{-1}\,dx.
   \]

   Confirm the sign convention in the manuscript. If the manuscript uses the outer measure-theoretic normal, this is the correct sign: on a ball centered at `z`, `nu_E=e_z`, and both sides give equality.

Deliverables:

- A TeX-ready lemma named something like `Radial Gauss--Green identity`.
- A short note explaining the case `z in E`, `z in partial E`, and `z notin closure(E)` are all covered by the same truncation.

Red flags:

- Do not assume smooth boundary.
- Do not invoke pointwise traces of `e_z` at `z`; the point is invisible to `H^{n-1}`.

### Agent C: Centered Potential Controls Same-Centre Volume

Task: Prove

\[
|E\Delta B_\rho(z)|^2\le C(n,R,\rho_*)\mathcal C_z(E)
\tag{10}
\]

under

\[
E\subset B_R,\qquad |E|=|B_\rho|,\qquad \rho\in[\rho_*,1].
\]

This is the most delicate self-contained lemma. It should not rely on the quantitative isoperimetric inequality; otherwise the workaround becomes circular.

Proof skeleton:

1. Translate `z=0`. Let `B=B_rho`, `A=B\setminus E`, and `F=E\setminus B`. Then

   \[
   |A|=|F|=:a,\qquad |E\Delta B|=2a.
   \]

2. Since `r -> r^{-1}` is strictly decreasing,

   \[
   \mathcal C_0(E)
   =(n-1)\left(\int_A |x|^{-1}\,dx-\int_F |x|^{-1}\,dx\right)\ge 0.
   \]

3. Use the bathtub principle. Among all holes `A subset B_rho` of volume `a`, the integral over `A` is minimized when `A` is the outer shell of volume `a` adjacent to `partial B_rho`. Among all excess sets `F subset B_R\setminus B_rho` of volume `a`, the integral over `F` is maximized when `F` is the outer shell adjacent to `partial B_rho`.

   Therefore it suffices to estimate the one-dimensional shell gap.

4. Let `s_-` and `s_+` be defined by

   \[
   |B_\rho\setminus B_{s_-}|=a,
   \qquad
   |B_{s_+}\setminus B_\rho|=a.
   \]

   Then

   \[
   \mathcal C_0(E)
   \ge (n-1)n\omega_n
   \left(\int_{s_-}^{\rho} r^{n-2}\,dr
   -\int_\rho^{s_+}r^{n-2}\,dr\right).
   \tag{11}
   \]

   Be careful with constants depending on whether `omega_n` denotes volume of the unit ball or surface measure divided by `n`.

5. For small `a`, write the shell thicknesses as

   \[
   h_-\simeq \frac{a}{P(B_\rho)},
   \qquad
   h_+\simeq \frac{a}{P(B_\rho)}.
   \]

   Since the two first-order terms cancel, the second-order term is positive and gives

   \[
   \mathcal C_0(E)\ge c(n,\rho_*)a^2.
   \]

   The sign can be checked from the fact that removing mass just inside `rho` and adding it just outside `rho` loses potential at order `h^2`.

6. For non-small `a`, either continue the explicit shell estimate or use compactness in one dimension to show a positive lower bound proportional to `a^2`, with constants depending only on `n,R,rho_*`.

7. Conclude

   \[
   |E\Delta B_\rho|^2=4a^2\le C(n,R,\rho_*)\mathcal C_0(E).
   \]

Deliverables:

- A TeX-ready lemma with an explicit proof.
- Ideally, an appendix-style calculation of the shell lower bound in terms of `a`, avoiding vague asymptotics.

Red flags:

- The lemma is false without same volume.
- The constant must deteriorate as `rho_* downarrow 0`; that is acceptable.
- The assumption `E subset B_R` matters only to control the admissible exterior shell for large `a` and to ensure constants stay uniform.
- Do not accidentally prove only a linear bound. The needed result is quadratic in the symmetric difference.

### Agent D: Homothetic Trace Lemma

Task: Turn the radial normal and same-centre volume estimates into the modified trace estimate needed by the constructive Serrin route.

Current target:

For `E`, `rho`, and `z` as above, prove an estimate of the form

\[
\left(\int_{\partial^*E}|H_{z,\rho}-\bar V_\rho|\,d\mathcal H^{n-1}\right)^2
\le C(n,R,\rho_*)\bigl(P(E)^2-P(B_\rho)^2\bigr),
\tag{12}
\]

where `H_{z,rho}` is the homothetic vector field used in the manuscript and `bar V_rho` is the corresponding ball value.

Proof skeleton:

1. Re-read the existing same-centre proof around the original Assumption 5.2 and identify where it used

   \[
   |E\Delta B_\rho(z)|^2
   +\int_{\partial^*E}|\nu_E-e_z|^2
   \]

   or equivalent quantities.

2. Replace the old input by (A).

3. Use

   \[
   P(E)^2-P(B_\rho)^2
   =\bigl(P(E)-P(B_\rho)\bigr)\bigl(P(E)+P(B_\rho)\bigr).
   \]

   On `rho >= rho_*`, the factor `P(E)+P(B_rho)` is bounded below by a positive dimensional constant, so

   \[
   P(E)-P(B_\rho)
   \le C(n,\rho_*)\bigl(P(E)^2-P(B_\rho)^2\bigr).
   \]

4. Confirm whether (12) should be linear or square-root in the deficit. The existing manuscript likely integrates the square of the trace, so the squared form above is the safe target.

Deliverables:

- A TeX-ready proposition proving the trace estimate from the FMP/capacity package.
- A list of exact manuscript equations that can be deleted, replaced, or weakened.

Red flags:

- Do not reintroduce a gradient upper bound for the torsion function.
- Do not use the false global Hessian inequality.
- Track the center `z=z_E`; it is selected by maximizing the FMP potential and may vary with the level.

### Agent E: Integration into the Level-Set Proof

Task: Convert the pointwise finite-perimeter result into the torsion level-set estimate.

Proof skeleton:

1. For almost every `t`, the superlevel set

   \[
   E_t=\{u>t\}
   \]

   has finite perimeter, and the coarea identities used elsewhere in the manuscript apply.

2. Define `rho(t)` by

   \[
   |E_t|=|B_{\rho(t)}|.
   \]

3. On the good range `rho(t) >= rho_*`, apply (A) to `E_t`.

4. Since

   \[
   D_I(t)=P(E_t)^2-P(B_{\rho(t)})^2,
   \]

   and `P(E_t)+P(B_{rho(t)}) >= c(n,rho_*)`, obtain

   \[
   P(E_t)-P(B_{\rho(t)})\le C(n,\rho_*)D_I(t).
   \]

5. Therefore

   \[
   |E_t\Delta B_{\rho(t)}(z_t)|^2
   +\int_{\partial^*E_t}|\nu_{E_t}-e_{z_t}|^2
   \le C(n,R,\rho_*)D_I(t).
   \]

6. Integrate over `t` using the existing budget inequality in the manuscript, currently labelled near `eq:budget`:

   \[
   \int D_I(t)\,dt \le C\delta_T(\Omega)
   \]

   or whatever exact weighted version appears in the text.

Deliverables:

- A TeX-ready theorem/corollary that replaces Assumption 5.2 on good levels.
- A patch plan for updating theorem statements, dependency summaries, and the final status text.

Red flags:

- Check whether the manuscript integrates in `t`, `rho`, or another variable. Insert the correct Jacobian if the parameter is changed.
- Check whether bad small levels `rho < rho_*` are already negligible in the paper. If not, isolate the exact existing lemma handling them.
- Do not claim a single global center works for all levels. The workaround gives level-dependent centers unless an additional selection argument is proved.

### Agent F: Adversarial Examples and Sanity Checks

Task: Attack the proposed estimates with examples before they enter the main theorem.

Examples to test:

1. Punctured balls / annuli. The old Hessian estimate fails, but the radial normal/perimeter estimate should survive because the inner boundary costs perimeter of order `a^{n-1}`.

2. Off-centre tiny holes. Verify the maximizing center does not produce a false estimate.

3. Disjoint union of two equal balls. The radial normal term and potential deficit should be large enough; the Hessian defect may vanish on each component, which is exactly why the old route failed.

4. Long thin tentacles. Perimeter deficit should dominate both the radial normal term and same-centre volume after FMP.

5. Highly oscillatory nearly spherical boundaries. Confirm the normal term is controlled by perimeter deficit through FMP beta, not by an unproved smooth graph estimate.

6. Shifted balls. If `E=B_rho(w)`, the maximizing center should be `z=w`, and all quantities should vanish.

Deliverables:

- A short sanity-check memo.
- Any correction to constants, hypotheses, or center selection that these examples force.

Red flags:

- If any example breaks (A), identify whether the problem is the center, the volume estimate, or a missing boundedness hypothesis.

### Agent G: Final TeX Implementation and Compile Audit

Task: Once Agents A--F finish, edit the manuscript.

Required manuscript changes:

1. Add the FMP theorem or proposition in the preliminaries, with exact citation.

2. Add the radial Gauss--Green lemma.

3. Add the centered potential-to-volume lemma.

4. Add the FMP/capacitary same-centre proposition.

5. Replace the provisional assumption in the constructive Serrin section, or explicitly downgrade it to a historical note and state that the FMP package closes the gap.

6. Update Remark 5.3 so it no longer says this step remains open, except perhaps as historical explanation.

7. Update the dependency certificate/status paragraph if the manuscript has one.

8. Compile with

   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error FK_exploratory_Serrin.tex
   ```

9. Search the log for unresolved references and fatal errors.

Success criteria:

- The manuscript compiles.
- No undefined references or citations remain.
- The final theorem does not depend on the false Hessian/L4 estimate.
- The proof uses only: FMP oscillation index, BV Gauss--Green, bathtub/shell potential lemma, coarea/isoperimetric budget already present in the paper.

## 4. Suggested TeX Lemma Package

The final manuscript should contain a compact package like this.

### Lemma 1: FMP Oscillation Index

Let `E` be a finite-perimeter set with `|E|=|B_rho|`. Then

\[
P(E)-(n-1)\sup_y\int_E|x-y|^{-1}\,dx
\le C(n)\bigl(P(E)-P(B_\rho)\bigr).
\]

### Lemma 2: Radial Gauss--Green

For every finite-perimeter set `E` with finite measure and every `z`,

\[
\frac12\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
=P(E)-(n-1)\int_E|x-z|^{-1}\,dx.
\]

If `|E|=|B_rho|`, this becomes

\[
\frac12\int_{\partial^*E}|\nu_E-e_z|^2
=P(E)-P(B_\rho)+\mathcal C_z(E).
\]

### Lemma 3: Centered Potential Controls Volume

If `E subset B_R`, `|E|=|B_rho|`, and `rho in [rho_*,1]`, then for every `z` with `B_rho(z) subset B_R` or with the appropriate translated boundedness hypothesis,

\[
|E\Delta B_\rho(z)|^2\le C(n,R,\rho_*)\mathcal C_z(E).
\]

If the exact boundedness condition needs adjustment, Agent C should state it precisely. Since `E_t subset Omega` and `Omega` is bounded in the intended application, this should be harmless.

### Proposition 4: FMP Same-Centre Selection

Under the hypotheses of Lemma 3, choose `z` maximizing the potential. Then

\[
|E\Delta B_\rho(z)|^2
+\int_{\partial^*E}|\nu_E-e_z|^2\,d\mathcal H^{n-1}
\le C(n,R,\rho_*)\bigl(P(E)-P(B_\rho)\bigr).
\]

### Corollary 5: Torsion Level Sets

For almost every good level `t`, there is a center `z_t` such that

\[
|E_t\Delta B_{\rho(t)}(z_t)|^2
+\int_{\partial^*E_t}|\nu_{E_t}-e_{z_t}|^2
\le C(n,R,\rho_*)D_I(t).
\]

This is the direct replacement for the strong-form assumption on good levels.

## 5. Key Technical Point: The Shell Calculation

Agent C should be especially careful here. A clean way to present the proof is to define

\[
\Psi_\rho(a)
:=\inf\left\{\int_A |x|^{-1}\,dx-\int_F|x|^{-1}\,dx:
A\subset B_\rho,\ F\subset B_R\setminus B_\rho,
|A|=|F|=a\right\}.
\]

By the bathtub principle, the minimizers are adjacent shells. Thus

\[
\Psi_\rho(a)
=\int_{B_\rho\setminus B_{s_-(a)}}|x|^{-1}\,dx
-\int_{B_{s_+(a)}\setminus B_\rho}|x|^{-1}\,dx.
\]

Here

\[
\omega_n(\rho^n-s_-^n)=a,
\qquad
\omega_n(s_+^n-\rho^n)=a.
\]

The desired bound is

\[
\Psi_\rho(a)\ge c(n,R,\rho_*)a^2.
\]

For small `a`, this can be proved by Taylor expansion in `a`. For all admissible `a`, either maintain an explicit formula or split into `a <= a_0` and `a >= a_0`; in the second regime, monotonicity and compactness in the parameters `(rho,a)` give a positive lower bound. If using compactness, write the argument so it is still rigorous and elementary.

## 6. Avoid These Pitfalls

1. Do not try to resurrect the global Hessian estimate. It is false on punctured balls.

2. Do not rely on smooth boundaries. Torsion level sets are only finite-perimeter sets for almost every level.

3. Do not assume a fixed center across levels.

4. Do not hide the dependence on `rho_*`. Constants are allowed to blow up as `rho_* downarrow 0`.

5. Do not use a compactness theorem where a one-dimensional bathtub calculation is available, unless the compactness step is written with precise admissible parameter ranges.

6. Do not confuse the volume deficit `|E Delta B|` with its square. The potential deficit controls the square of the same-centre volume error.

7. Do not normalize away scaling without restoring it in the final theorem.

## 7. Final Deliverable Expected from the Agent Team

The final result should be a manuscript patch, not merely notes. It should include:

1. A rigorous FMP/capacity subsection.
2. A replacement of the provisional strong-form assumption on good levels.
3. A revised Remark 5.3 explaining that the Hessian route fails but the FMP oscillation-index route closes the same-centre trace estimate.
4. A successful LaTeX compile.
5. A short audit note listing any theorem that remains imported from the literature. Ideally, the only substantial imported theorem is the FMP oscillation-index estimate.
