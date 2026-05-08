# Referee Evaluation & Journal Matching

**Paper:** "Quantitative Stability for Minkowski's problem"  
**Authors:** Károly Böröczky, João Miguel Machado, João P.G. Ramos  
**Source file:** `main_stability_Minkowski.tex`

*Evaluation conducted following the `journal.md` rubric (LLM Referee Agent).*

---

## 1. Summary of Findings

The paper proves quantitative stability estimates for both the classical Minkowski problem and the \(L_p\)-Minkowski problem (\(1 \le p \neq n\)), bounding the Hausdorff distance and Fraenkel asymmetry between Minkowski bodies in terms of the dual-convex distance between the associated surface measures. The core innovation is a variational formulation that treats the Minkowski body as a minimizer of an energy functional depending on the prescribed measure, then leverages the quantitative Brunn–Minkowski and isoperimetric inequalities as substitutes for Łojasiewicz-type curvature bounds. The paper is technically rigorous and addresses a natural question; the main risk is whether the synthesis — coupling Diskant-type and Figalli–Maggi–Pratelli estimates into the final exponents — is presented with enough detail to survive a top-tier referee.

---

## 2. Detailed Referee Comments

### Originality

- **Variational formulation.** Casting the Minkowski body as a minimizer of \(\mathscr{F}_\mu(K) = \int h_K d\mu / |K|^{1/n}\) provides a clean bridge between the measure perturbation (\(\dc(\mu,\nu)\)) and the geometric deficit (Brunn–Minkowski deficit). This viewpoint is well-motivated via the Łojasiewicz inequality analogy and appears to be new in this context.
- **Extension to \(L_p\).** The adaptation of the same variational scheme to the \(L_p\)-Minkowski problem, including the derivation of quantitative \(L_p\) Brunn–Minkowski and isoperimetric inequalities from their classical counterparts, is a solid contribution. The functional \(\Theta_+\) as a quantitative replacement for the "not supported on a hemisphere" condition is natural and useful.
- **Sharpness examples.** Examples 1 and 2 in the introduction demonstrating optimality of the exponents are stated but not fully written out in the visible portion of the manuscript. These should be expanded into a proper subsection with explicit constructions.
- **Relation to prior work.** The paper correctly situates itself relative to Hug–Schneider (2002), whose bounds depend on inner/circumradii of the specific bodies, and Abdallah–Mérigot (2015). The advance here — uniformity in the class \(\{\mu : \Theta(\mu) \ge \vartheta\}\) — is clearly articulated.

### Technical Accuracy

- **Variational Lemma (Lemma 3.1 / Lemma 5.3 equivalent).** The statement that \(\lambda_\mu\) is the minimum value and \(E_\mu\) is the unique centered minimizer is correctly argued via the Wulff inequality. The Lipschitz estimate for \(\mu \mapsto \lambda_\mu\) with respect to \(\dc\) is crucial; the proof uses the first-variation formula and the bounds on \(R_{E_\mu}\). This chain should be checked for a missing factor of \(n\) in the scaling.
- **Quantitative \(L_p\) Brunn–Minkowski (Lemma 5.1).** Deriving this from the classical quantitative Brunn–Minkowski via Jensen's inequality and concavity of \(t \mapsto t^{p/n}\) is clean. The explicit constant dependence on \(p\), \(n\), and geometry should be displayed in a single inequality rather than buried in the proof text.
- **Diskant's estimate.** The paper relies on Diskant's 1972 quantitative Brunn–Minkowski inequality, which requires uniform bounds on inradius and circumradius. Sections 2.2 and 2.3 establish these bounds from \(\Theta(\mu) \ge \vartheta\), which is the right approach. The constants \(c_n\) and \(C_n\) in Lemma 2.1 are explicitly computed — this is good practice and should be retained.
- **John ellipsoid usage.** The proof of Lemma 2.1 uses the John ellipsoid and projection-area estimates. The chain of inequalities from \(\Theta(S_K)\) to \(r_K\) and \(R_K\) is sound.
- **Fraenkel asymmetry bound.** The exponent \(2\) on the Fraenkel asymmetry term matches the sharp exponent from the quantitative isoperimetric inequality (Fusco–Maggi–Pratelli, Figalli–Maggi–Pratelli). The coupling with Diskant's estimate to get the exponent \(1 + 1/(n-1)\) on \(\dc(\mu,\nu)\) is a non-trivial combination — a full derivation with all intermediate exponents would strengthen the manuscript for a top-tier referee.
- **Hausdorff distance exponent sharpness (Example 1).** The claim that \(1/(n-1)\) is optimal is plausible, but the construction needs to be written out. The same holds for Example 2 (Fraenkel sharpness in dimension 2).

### Clarity and Structure

- The introduction is well-written and does an excellent job motivating the choice of distances (dual-convex, Hausdorff, Fraenkel) and the role of the functional \(\Theta\).
- The Łojasiewicz inequality analogy is insightful and makes the variational approach accessible to readers from optimization and PDE backgrounds.
- **Section labels.** The TeX source uses `\ref{sec.case_p1}` and `\ref{secp>1}`; the latter label is missing an underscore and may produce broken cross-references. Fix `secp>1` → `sec.case_p>1` or similar.
- **Notation.** Uses `\dc` for dual-convex distance, `\dH` for Hausdorff distance, `\Theta` and `\Theta_+` — all clearly defined. `\eqdef` (= with "def." superscript) is used consistently.
- **Abstract.** Well-structured, includes keywords and MSC codes.

### Literature Positioning

- Core references are solid: Minkowski (1903, 1911), Alexandrov (1938, 1996), Nirenberg, Cheng–Yau, Pogorelov, Caffarelli for regularity; Lutwak for \(L_p\) Brunn–Minkowski; Hug–Schneider (2002) and Abdallah–Mérigot (2015) for prior stability.
- The quantitative Brunn–Minkowski literature (Diskant, Figalli–Maggi–Pratelli, Fusco–Maggi–Pratelli, Figalli–van Hirtum) is well-cited.
- **Missing.** No reference to the recent Böröczky–De–Eles–Figalli–van Hirtum work on quantitative stability of the logarithmic Minkowski problem, which is closely related. The first author is a co-author here and should cross-reference recent parallel developments.
- **Missing.** The paper Machado–Ramos (2025) on quantitative stability of moment measures is cited as a preprint; confirm its publication status.

---

## 3. Ranked Journal List

*Constraints assumed*: hybrid/subscription acceptable; target is solid Q1 in geometry, analysis, or PDE. Metrics are approximate as of 2026 — **verify all on official publisher/JCR/Scopus pages before submission.**

| Rank | Journal | Aims & Scope Fit | Rationale | Indexing / Metrics | Est. Review Speed |
|---:|---|---|---|---|---|
| 1 | **Journal de Mathématiques Pures et Appliquées** | Excellent: rigorous analysis, geometric PDE, convex geometry, quantitative inequalities | Strongest fit among top generalist analysis journals. The journal has a tradition of publishing deep convex geometry and Monge–Ampère work (Figalli, Caffarelli, etc.). The variational + quantitative stability framework aligns with recent trends in the journal. | ISSN 0021-7824; Elsevier; IF ~1.9; SCIE/Scopus; hybrid OA | ~4–8 months typical |
| 2 | **Advances in Mathematics** | Strong: broad, high-impact, accepts deep convex geometry and geometric analysis | Solid choice with wider readership. The Łojasiewicz/variational framing and the link to quantitative Brunn–Minkowski broaden the appeal beyond convex geometry specialists. | ISSN 0001-8708; Elsevier; IF ~1.7; SCIE/Scopus; hybrid OA | ~6–12 months typical |
| 3 | **Mathematische Annalen** | Strong: classical venue for deep geometry and analysis | Long tradition of publishing major work in convex geometry. The quantitative stability angle fits the journal's recent scope. Slightly higher prestige than CVPDE in pure mathematics circles. | ISSN 0025-5831; Springer; IF ~1.4; SCIE/Scopus; hybrid OA | ~6–10 months typical |
| 4 | **Calculus of Variations and Partial Differential Equations** | Very good: variational methods, geometric inequalities, stability | Safe backup. The variational core of the paper fits naturally, and the journal regularly publishes quantitative geometric inequalities. Lower prestige than the three above, but thematically aligned. | ISSN 0944-2669; Springer; IF ~2.1; SCIE/Scopus; hybrid OA | ~4–8 months typical |
| 5 | **Journal of Differential Geometry** | Good: geometric aspects of Minkowski bodies, surface measures as geometric objects | Top differential geometry journal. Would require reframing to emphasize the geometric significance of Minkowski bodies. Highly selective. | ISSN 0022-040X; Lehigh Univ.; IF ~1.5; SCIE/Scopus; subscription | ~6–12 months typical |

### Stretch Option

**Geometric and Functional Analysis (GAFA)** publishes landmark work in convex geometry and geometric inequalities. Böröczky has published there. If the authors believe the variational synthesis and the sharpness examples constitute a genuinely major advance, this is the ambitious target. ISSN 1016-443X; Springer; IF ~1.8; very selective.

### Submission Strategy

Submit first to **JMPA** — it offers the best balance of prestige and thematic fit for a paper centered on quantitative convex geometry with a variational engine. If rejected, **Advances in Mathematics** is the natural next target with broader readership. **Mathematische Annalen** is a strong European alternative. **CVPDE** serves as the safe thematic backup; **JDG** as the ambitious geometric play.

---

## 4. Refinement Questions

- Should the paper emphasize the **variational / Łojasiewicz** angle (→ JMPA / CVPDE) or the **convex geometry / Minkowski problem** angle (→ JDG / Advances)?
- Would a **GAFA** submission be considered? If so, the sharpness examples and the coupling of Diskant + Figalli–Maggi–Pratelli estimates need to be presented at a higher level of polish.
- Is there a **page limit or cost constraint**?
- Are the **sharpness examples** (Examples 1 and 2 in the introduction) already written in full, or do they need to be expanded before submission?
- What is the publication status of the **Machado–Ramos (2025)** preprint on moment measures? This affects how the paper positions its novelty relative to that work.
