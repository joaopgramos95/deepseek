# Summary: Eigenfunctions, Free Boundaries, and Time-Frequency Localization

**Author**: João P.G. Ramos  
**File**: `main_expanded.tex`

---

## Overview

The paper studies Gaussian time–frequency localization operators through their Bargmann–Fock representation, developing a unified **inverse and free-boundary framework**. The central philosophy is that eigenfunctions should be treated as *geometric data*: they determine the domain, and prescribing them has strong consequences for variational concentration problems.

The paper has four main results, organized into Sections 2–7.

---

## Main Results

### 1. Perturbative Inverse Construction (Theorem 1.1 / Thm 3.1)

For any eigenvalue \(\lambda \in (0,1)\) and integer \(N\), there exists \(\varepsilon_0(\lambda,N) > 0\) such that if

\[
f_0 = h_0 + \sum_{k=1}^N a_k h_k
\]

is a small perturbation of the ground-state Hermite function (all \(|a_k| < \varepsilon_0\)), then a domain \(U_\lambda\) exists with \(\mathcal{L}_{U_\lambda} f_0 = \lambda f_0\).

This is the first systematic construction of localization domains for non-trivial linear combinations of Hermite functions. The proof reformulates the problem as an infinite system of weighted moment equations on an analytic radial graph over the disk, then applies an implicit-function theorem in analytic boundary spaces. This is the *inverse* counterpart to the Abreu–Dörfler rigidity phenomenon.

### 2. Two New Proofs of Abreu–Dörfler Rigidity (Theorem 1.2 / Thm 4.1)

If a Hermite function is an eigenfunction of the localization operator for a **simply connected bounded domain**, then the domain is necessarily a disk.

- **First proof**: Assumes \(C^2\) boundary, uses overdetermined boundary conditions and quadrature-domain theory (logarithmic potential must be radial on the boundary).
- **Second proof**: Requires *no boundary regularity*, relying purely on an explicit potential representation and a holomorphic auxiliary function. A Paley–Wiener argument plus an Ehrenpreis–Malgrange-type divisibility lemma forces radiality.

### 3. Sharpness of the GGRT Stability Inequality (Theorem 1.3 / Thm 5.1)

The exponent **1/2** in the stability estimates of Gómez–Guerra–Ramos–Tilli is optimal:

\[
\|f_U - c\phi_{z_0}\|_{L^2} \leq C e^{|U|/2} \left(1 - \frac{\lambda_1(U)}{1 - e^{-|U|}}\right)^{1/2}
\]

The paper constructs a one-parameter family of domains via Theorem 1.1 whose boundary is governed by second-order Fourier harmonics (which cannot be eliminated by translations). Comparing symmetric differences against arbitrary disks yields lower bounds matching the upper bounds, proving the square-root rate is tight — no \(\beta > 1/2\) can replace the exponent.

### 4. Local and Global Maximizers → Nicola–Tilli (Section 6–7)

**Local maximizers** (Theorem 6.1): Every local maximizer of \(\lambda_{1,\varphi}(\Omega)\) under a measure constraint is, up to translation, a disk. The proof uses a first-variation identity (divergence theorem / Reynolds transport), showing the maximizing eigenfunction must be Gaussian, which forces the domain to be a disk.

**Global maximizers** (Theorem 7.1): Through a **concentration-compactness** argument (profile decomposition in the Fock space), existence of a global maximizer is proved. Since any global maximizer is also a local one, the rigidity result applies, yielding a new proof that disks are the unique global maximizers — i.e., a new proof of the Nicola–Tilli theorem.

---

## Framework and Key Objects

| Object | Definition |
|---|---|
| Gaussian STFT | \(V_\varphi f(x,\omega) = \int_{\mathbb{R}} f(t) 2^{1/4} e^{-\pi(t-x)^2} e^{-2\pi i t\omega} dt\) |
| Bargmann transform | \(\mathcal{B}f(z) = 2^{1/4} \int_{\mathbb{R}} f(t) e^{2\pi t z - \pi t^2 - \frac{\pi}{2}z^2} dt\) |
| Fock space \(\mathcal{F}^2(\mathbb{C})\) | Entire functions with \(\|F\|^2 = \int_{\mathbb{C}} |F(z)|^2 e^{-\pi|z|^2} dA(z)\) |
| Density \(u_F(z)\) | \(|F(z)|^2 e^{-\pi|z|^2}\) — encodes STFT energy |
| Hermite → monomial | \(\mathcal{B} h_k = e_k\), where \(e_k(z) = (\pi^k/k!)^{1/2} z^k\) |
| Localization operator \(\mathcal{L}_U\) | Integral operator whose eigenfunctions maximize \(\int_U u_F\) |

Key identity: \(|V_\varphi f(x,\omega)|^2 = u_F(z)\) with \(z = x + i\omega\).

The reproducing kernel is \(K_w(z) = e^{\pi z \overline{w}}\), and Weyl translation operators \(T_a F(z) = e^{\pi a z - \frac{\pi}{2}|a|^2} F(z-a)\) provide unitary invariance.

---

## Methods Used

- **Free-boundary problems & quadrature domains**: Isakov's perturbative theorem, logarithmic potentials, overdetermined Poisson problems.
- **Complex analysis**: Holomorphic auxiliary functions, Cauchy–Riemann equations, Paley–Wiener arguments, Ehrenpreis–Malgrange divisibility.
- **Implicit function theorem in Banach spaces**: Used in the inverse construction on analytic boundary spaces.
- **First-variation / transport formulas**: Reynolds transport theorem for derivatives of domain integrals.
- **Concentration-compactness**: Profile decomposition in \(\mathcal{F}^2(\mathbb{C})\), ruling out vanishing and dichotomy.
- **Bathtub principle / rearrangement**: For the superlevel-set characterization of maximizers.

---

## Structure

- **Section 2**: Preliminaries — Fock space properties, \(u_F\) density, \(I_F(s)\) functional, Weyl operators, auxiliary lemmas.
- **Section 3**: Proof of Theorem 1.1 (perturbative inverse).
- **Section 4**: Two proofs of Abreu–Dörfler rigidity.
- **Section 5**: Sharpness of GGRT (Theorem 1.3).
- **Section 6**: Local maximizers are disks.
- **Section 7**: Concentration-compactness → existence of global maximizer → new proof of Nicola–Tilli.

---

## Significance

The paper establishes a **bridge between time-frequency analysis, inverse spectral theory, and free-boundary problems**. It resolves several open problems:

- First general inverse construction of localization domains beyond symmetric examples.
- Settles the optimal exponent in quantitative stability for the Gaussian STFT Faber–Krahn inequality.
- Provides a unified variational framework that recovers and refines the Nicola–Tilli theorem without relying on rearrangement inequalities.
- The second rigidity proof removes boundary regularity assumptions entirely.
