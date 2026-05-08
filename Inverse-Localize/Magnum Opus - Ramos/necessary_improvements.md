# Necessary Improvements for `main_expanded.tex`

*Compiled from referee-style evaluation of the manuscript "Eigenfunctions, Free Boundaries, and Time-Frequency Localization" (João P.G. Ramos). Sorted by priority and section.*

---

## A. High-Priority Technical Gaps

### A1. Section 3 — Inverse construction (Theorem 1.1 / 3.1)

- **Implicit function theorem setup.** State the exact Banach spaces for the boundary graph and the moment map. Define the Fréchet derivative of the moment map at the disk and compute its invertibility on the orthogonal complement of the kernel explicitly. The current text says the linearization is "diagonal in Fourier modes" — this needs a displayed computation, not a sketch.
- **Characteristic-polynomial argument (Step 3).** The passage from the symmetrized moment identity to the original eigenvalue equation invokes an ODE argument with a polynomial `P`. Spell out the growth estimates, the role of `P` non-vanishing on `U`, and why no hidden finite-dimensional obstruction remains after symmetrization.
- **Coefficientwise conjugate differential operator.** Define this operator explicitly and justify why it can be applied term-by-term to the eigenvalue equation.
- **Moment-to-Cauchy-transform conversion.** The Laplace-transform step claims equality for large real `ζ` yields the full exterior Cauchy-transform identity. Justify the analytic continuation explicitly and verify that all required higher moments vanish.

### A2. Section 4 — Abreu–Dörfler rigidity (Theorem 1.2 / 4.1)

- **Ehrenpreis–Malgrange divisibility lemma.** State the lemma precisely with its hypotheses (growth conditions, support, complex lines). Clarify whether this is quoted verbatim from a reference, reformulated, or proved as a lemma. A referee will check the exact statement.
- **Paley–Wiener argument.** The reduction to vanishing of a Fourier transform along complex lines needs a more detailed justification — specify the function class and the exact Paley–Wiener theorem variant invoked.
- **No-boundary-regularity proof (Section 4.2).** If this proof genuinely avoids all boundary regularity, state this as a theorem-strengthening and highlight where the earlier \(C^2\) assumption is bypassed.

### A3. Section 5 — Sharpness of GGRT (Theorem 1.3 / 5.1)

- **Principal eigenvalue identification.** The constructed eigenvalue must be proved to be the *first* (principal) eigenvalue of \(\mathcal{L}_{U_\varepsilon}\). Currently the text assumes this without a perturbative argument. Provide a spectral gap estimate or a continuation argument from the disk.
- **Area-normalizing dilation.** The claim that rescaling changes \(\lambda_1\) by only \(O(\varepsilon^2)\) needs a self-contained computation or a precise citation.
- **First-variation / transport formula.** State the Reynolds transport theorem in the form used, specify the regularity of the deformation field, and compute the first variation of the eigenvalue with respect to the boundary perturbation explicitly.
- **Second-order harmonics and symmetric difference.** The geometric measure estimate comparing \(U_\varepsilon\) with arbitrary disks should be written out with explicit constants. The argument that second-order harmonics cannot be eliminated by translations needs a short lemma.

### A4. Section 6 — Local maximizers (Theorem 6.1)

- **Definition of "local maximizer."** Define the topology precisely. The text refers to a weighted symmetric-difference topology; explain compatibility with the Lebesgue measure constraint and justify why this topology is natural for the problem.
- **From maximizer to superlevel set.** Derive the superlevel-set characterization with clear hypotheses. Cite or prove the bathtub principle variant used.
- **Boundary regularity of a maximizer.** If the maximizer is only measurable, explain how boundary analyticity and the divergence-theorem argument are justified. Either derive regularity or state it as an additional hypothesis (e.g., maximizer is open with \(C^{1,\alpha}\) boundary).
- **Simplicity of the first eigenvalue.** Prove or cite that the first eigenvalue is simple at a local maximizer. This is used in the argument that derivatives of the eigenfunction remain eigenfunctions.

### A5. Section 7 — Concentration-compactness / Nicola–Tilli (Theorem 7.1)

- **Profile decomposition in \(\mathcal{F}^2(\mathbb{C})\).** State the full profile decomposition theorem with its convergence properties (strong vs. weak, remainder estimates). Address the lack of translation compactness in the Fock space — this is a known subtlety.
- **Ruling out dichotomy.** The argument that dilation/scaling prevents dichotomy needs more detail. Show that the concentration function is indeed subadditive in the relevant limit.
- **Uniqueness of the global maximizer.** The conclusion that disks are the *unique* global maximizers follows from the local rigidity theorem but should be stated with a brief justification (any global maximizer is a local maximizer, hence a disk; all disks of the same area are translates of each other, and the eigenvalue is translation-invariant).

---

## B. Missing Structural Elements

- **Keywords and MSC codes.** Add immediately after the abstract. Suggested: *Gaussian STFT, localization operators, Bargmann–Fock space, inverse spectral problem, free boundary, quadrature domains, Faber–Krahn inequality, time-frequency concentration.* MSC candidates: `42B10`, `42C15`, `30H20`, `35R35`, `35R30`, `47B35`, `49Q10`.
- **"Main technical inputs" subsection.** Add a short paragraph in the preliminaries (Section 2) listing exactly which external theorems are used and in what form: Isakov's perturbative free-boundary theorem, Cherednichenko's inverse potential result, the bathtub principle, the concentration-compactness profile decomposition, etc. For each, state whether the theorem is quoted verbatim, adapted with proof, or proved as a lemma.
- **Acknowledgment of known vs. new results.** Add a sentence in the introduction clarifying which theorems are *new results* (1.1, 1.3, 6.1) and which are *new proofs of known results* (1.2 → Abreu–Dörfler; 1.4 → Nicola–Tilli). This prevents a referee from accusing the paper of repackaging existing work.

---

## C. Technical Cross-References to Strengthen

- **Free-boundary literature.** Sharpen the comparison with quadrature domain theory. Cite specific theorems from Gustafsson–Shahgholian and explain how the weighted-moment equations in Section 3 differ from classical quadrature-domain identities (the presence of the Gaussian weight and the eigenvalue parameter).
- **Toeplitz/Fock-space inverse problems.** Add references to recent inverse spectral results for Toeplitz operators on Bergman/Fock spaces if any exist, to distinguish the present construction.
- **Concentration-compactness in time-frequency analysis.** Beyond Nicola–Romero–Trapasso, cite other recent uses of profile decompositions in phase-space analysis (e.g., works on Fourier concentration, polyanalytic Fock spaces).

---

## D. Editorial / Polish

- **Remove source artifacts.** The file contains `:contentReference[oaicite:0]{index=0}` near the end of the introduction in at least one version. Remove all such artifacts.
- **Standardize names.** Check and unify: "Gómez" / "Gomez" / "Gomez-Guerra"; "Dörfler" / "Doerfler"; "Faber–Krahn" / "Faber-Krahn"; "Nicola–Tilli" throughout.
- **Abstract length.** Tighten the abstract to 8–10 lines. Currently it is substantial but could lose a sentence or two.
- **Decide authoritative version.** The directory contains both `main.tex` and `main_expanded.tex`. Clarify in a comment or README which is the canonical version and remove stale auxiliary files before submission.
- **Check for truncated proofs.** The RLM analysis flagged possible truncation at the end of Section 5 and in the profile decomposition tail (Section 7). Verify that all `\end{proof}` tags are present and that no `\section` or `\subsection` is cut off mid-sentence.
- **Label equations used across sections.** Several key identities (the eigenvalue equation in Bargmann–Fock form, the symmetrized moment system) are used in multiple sections. Tag them with `\label` and cross-reference by number rather than repeating the derivation.

---

## E. Optional / Nice-to-Have

- **Numerical illustration.** A figure or table showing the perturbed domain \(U_\varepsilon\) for a simple choice of \(f_0\) (e.g., \(h_0 + \varepsilon h_2\)) would help readers visualize the inverse construction.
- **Explicit example.** Provide a fully worked example of Theorem 1.1 for \(N=2\) with explicit coefficients, showing the resulting domain equation.
- **Discussion of higher eigenvalues.** Mention whether the inverse construction extends to higher eigenvalues or whether the method is specific to the principal eigenvalue.
- **Open problems section.** Add a short paragraph on open questions (e.g., inverse construction far from the Gaussian, characterization of all possible eigenfunctions, stability of the inverse map).
