# Response to the corrections-needed audit

This note responds, point by point, to `corrections-needed.md`. See
`corrections-response.tex/.pdf` for the full proofs.

## Disposition of each audit item

| Item | Issue | Response |
|------|-------|----------|
| 1 | Overclaim "end-to-end and rigorous" | **Adopted** conditional wording (Section 7 of audit). |
| 2 | Volume normalization for Bernoulli law | **Written out** (§1 here). |
| 3 | C^{1,γ} → small C^{2,γ_0} upgrade | **Corrected**: uniform Schauder bounds plus interpolation (§2 here). |
| 4 | Tame remainder source enumeration | **Partial**: $S_1, S_2$ enumerated; IBP step is avoided. |
| 5 | Final theorem in correct regime | **Adopted** (§4 here). |
| 6 | Sign typo $\partial_r\widetilde u_g\ge 1/(2N)$ | **Fixed in place** in `fixed-domain-bernoulli-expansion.tex`. |
| 7 | Status wording | **Adopted** (§5 here). |

## 1. Volume-normalized Bernoulli law (audit point 2)

Let $r_* = (|U_*|/|B_1|)^{1/N}$. Set $\widetilde U = r_*^{-1}U_*$,
$\widetilde u(x) = r_*^{-2}u_{U_*}(r_*x)$. Then on $\partial\widetilde U$:

\[
|\nabla\widetilde u(y)|^2 = \widetilde\Lambda + \widetilde a_\sigma\widetilde\Psi(y),
\]

with $\widetilde\Lambda = r_*^{-2}\Lambda$, $\widetilde a_\sigma = r_*^{-1}a_\sigma$,
and $\widetilde\Psi$ the $\alpha$-bracket on $\widetilde U$. Since
$|r_*-1| \le C\delta_T$ where $\delta_T = E(U_*) - E(B_1)$, the constants
degrade by $(1+O(\delta_T))$. This is absorbed into the smallness regime
$\sigma\le\sigma_*/2$.

## 2. Uniform Schauder bootstrap + interpolation (audit point 3)

By the hodograph transform applied to the torsion function near $\partial U$,
plus Schauder for oblique boundary-value problems
(Kinderlehrer-Nirenberg 1977, Lieberman 1985), the explicit smooth selected
Bernoulli law gives uniform higher regularity after BDV Lemma 4.16 supplies
the starting coefficient bounds:

\[
\|g\|_{C^{m,\gamma}(\partial B_1)}\le M_m(N,R)
\qquad(m\ge3).
\]

This alone is not a smallness estimate. The missing smallness comes from the
Hausdorff part of graph entry:

\[
\|g\|_{L^\infty}\le C\,d_H(\partial U,\partial B_1)
\le C\alpha(U)^{1/(2N)}.
\]

Interpolating between \(C^0\) and \(C^{m,\gamma}\) gives

\[
\|g\|_{C^{2,\gamma_0}}
\le C\|g\|_{L^\infty}^{1-\theta}M_m(N,R)^\theta.
\]

Thus the needed small \(C^{2,\gamma_0}\) regime is reached by strengthening
the asymmetry threshold, not by pretending the fixed \(L_q(N,R)\) term can be
made small.

## 3. Second-variation source enumeration (audit point 4)

The bilinear source $S(s,g)$ in
$-\nabla\cdot(A_{sg}\nabla w''(sg)(g,g)) = S(s,g)$ splits into two leading
terms:

- $S_1(g) = \nabla\cdot(Q_A(g,g)\nabla u_{B_1}) + Q_J(g,g)$ — quadratic
  coefficient applied to the ball torsion potential.
- $S_2(g) = 2\nabla\cdot(L_A(g) \cdot \nabla\widetilde u'(g))$ — linear
  coefficient applied to the first variation.

Each is bounded in $L^2(B_1)$ by $C\|g\|_{C^{2,\gamma}}\|g\|_{H^1(\partial B_1)}$
by pairing the highest-derivative factor in $L^\infty$ and the lowest in
$L^2$. The key observation:

- $\|g\nabla^2 g\|_{L^2(\partial B_1)} \le \|\nabla^2 g\|_{L^\infty}\|g\|_{L^2}$
  — gives the $L^2$-tame estimate.
- $\|(\nabla g)^2\|_{L^2} \le \|\nabla g\|_{L^\infty}\|\nabla g\|_{L^2}$
  — gives the $H^1$-tame estimate.

Both pair into $\|\cdot\|_{C^{2,\gamma}}\cdot\|\cdot\|_{H^1}$, **without
needing integration by parts on $S^{N-1}$**. The earlier note's claim that
IBP was needed for the highest-derivative pairing was overcautious; the
direct $L^\infty\cdot L^2$ pairing handles all cases.

Higher-order tails ($S_3, S_4$) come from cubic-and-higher Taylor terms
and are uniformly small for $\|g\|_{C^{2,\gamma}}\le\delta_0$.

**What is NOT done:** numerical tracking of constants in each step.

## 4. Final theorem in the correct regime (audit points 1, 5, 7)

**Theorem (sharp Faber-Krahn, audit-conditional form):** there exist
$\mathcal A_*, c_{\rm FK} > 0$ depending on $(N,R)$ such that for every
open $\Omega \subset B_R$ with $|\Omega| = |B^*|$ and
$\mathcal A(\Omega) \le \mathcal A_*$,

\[
\lambda_1(\Omega) - \lambda_1(B^*) \ge c_{\rm FK}(N,R)\mathcal A(\Omega)^2,
\]

**provided** sharp Saint-Venant stability is supplied by either:

1. **BDV's nearly spherical second variation** — unconditional and standard;
2. **The Bernoulli spectral closure of `fixed-domain-bernoulli-expansion.md`** —
   conditional on §3 of this response being completed with explicit constants.

Both routes share:
- selection (`quantitative-selection-principle.md`),
- graph entry (`graph-entry-closure.md`),
- volume normalization (§1 here),
- uniform Schauder/interpolation entry (§2 here),
- Kohler-Jobin transfer (`faber-krahn-transfer.md`).

They differ only in the final closure step: BDV's second variation vs.\ the
Bernoulli spectral closure.

## 5. Status wording (adopted from audit Section 7)

> The selection principle and graph-entry steps are quantitative. The
> Bernoulli spectral closure is a promising conditional route, but the
> fully rigorous closure still requires either a completed tame remainder
> proof (now reduced to source enumeration with constants, §3) or the BDV
> nearly spherical second variation as the final step.
