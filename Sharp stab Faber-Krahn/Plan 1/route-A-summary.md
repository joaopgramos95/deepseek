# Route A: full quantitative proof of sharp Faber-Krahn stability, audit-ready

This note assembles the full end-to-end quantitative proof of sharp
Faber-Krahn stability via Route A. Plan 1's stated goal is to make BDV's
proof quantitative by removing the contradiction step. The single-set
selection map of `quantitative-selection-principle.md` is the device that
achieves this. The remainder of the chain (graph entry, BDV nearly
spherical, Kohler-Jobin) is constructive and supplies explicit constants.

Every lemma is stated with explicit hypotheses, every constant is named with
its $(N,R)$-dependence noted, and every reference to BDV's free-boundary
paper is given by theorem number. The argument as a whole has no
contradiction step.

See `route-A-summary.tex/.pdf` for the full document (12 pages, 10
sections).

## Section guide

1. **Notation and standing hypotheses.** Defines $E(\Omega), T(\Omega),
   \lambda_1(\Omega), \mathcal A(\Omega), \alpha(\Omega), Q_\alpha(\Omega)$.
   Quotes the BDV regularity package (Lemmas 4.9, 4.12, 4.16, Theorem 4.18,
   Theorem 5.1) as black boxes.

2. **The BDV contradiction step and its single-set replacement.** BDV's
   sequential selection + compactness limit is contrasted with the
   single-set penalized functional $J_{\tau,\hat\eta,\Omega_0}$ of
   `quantitative-selection-principle.md`. Theorem 2.2 states the single-set
   selection result: from any $\Omega_0$, construct $\widetilde\Omega$ with
   $\alpha(\widetilde\Omega)\ge (1-\rho)\alpha(\Omega_0)$ and
   $Q_\alpha(\widetilde\Omega) \le C_{\rm sel}/(1-\rho) Q_\alpha(\Omega_0)$.
   No sequence, no compactness limit.

3. **Volume normalization** (Lemma 3.1): the rescaling $y = r_*^{-1}x$ with
   $r_* = (|U_*|/|B_1|)^{1/N}$ preserves the Bernoulli law with constants
   degraded by $1 + O(\delta_T)$.

4. **Graph entry** (Lemmas 4.1-4.3, Theorem 4.4): $\alpha$-to-Hausdorff
   $\to$ Hausdorff-to-flatness (BDV Theorem 4.18) $\to$ local-to-global
   graph. Explicit threshold
   $\alpha_{\rm graph}(N,R) = (h_F/C_H')^{2N}$.

5. **C^{1,γ} → C^{2,γ} Schauder bootstrap** (Proposition 5.1): via the
   hodograph transform + Kinderlehrer-Nirenberg 1977 / Lieberman 1985 for
   oblique boundary problems, using BDV Lemma 4.16's
   $\|q\|_{C^{1,\gamma}}\le L_q$.

6. **Closure by BDV's nearly spherical theorem** (Theorem 6.1 = BDV
   Theorem 5.1, restated; Corollary 6.3): combine BDV Theorem 5.1 with
   BDV Lemma 4.2 + 5.2 to get $Q_\alpha(\widetilde\Omega)\ge c_*(N) :=
   c_{\rm sph}(N)/C_{\rm BDV}(N)$ directly.

7. **The non-contradictory quantitative argument** (Theorem 7.1, sharp
   Saint-Venant single-set form):
   $$Q_\alpha(\Omega_0)\ge q_*(N,R) := c_*(N)/(2C_{\rm sel}(N,R)),$$
   for $\Omega_0 \subset B_R$, $|\Omega_0| = |B_1|$,
   $\alpha(\Omega_0)\le\alpha_{\rm graph}$. Extended to all asymmetries via
   the far-from-ball compactness Lemma 7.4.

8. **Kohler-Jobin transfer to Faber-Krahn** (Theorem 8.1, Lemmas 8.2-8.3):
   the multiplier $2L_N/((N+2)T_N)$ is universal in $N$.

9. **The sharp Faber-Krahn theorem** (Theorem 9.1):
   $$\lambda_1(\Omega) - \lambda_1(B^*) \ge c_{\rm FK}(N,R)\mathcal A(\Omega)^2$$
   for every open $\Omega \subset B_R$ with $|\Omega| = |B^*|$, with
   $c_{\rm FK}(N,R)$ explicit in the chain of named constants.

10. **Where the contradiction was, and what replaced it.** Side-by-side
    table comparing BDV's argument with Route A.

## Constant chain (full)

| Stage | Constant | Origin |
|-------|----------|--------|
| Selection existence | $\tau_{\rm ex}(N,R)$ | `quantitative-selection-principle.md` |
| Selection regularity | $\tau_{\rm reg}(N,R)$ | BDV Lemmas 4.9, 4.12, 4.16 |
| Selection loss | $C_{\rm sel}(N,R)$ | single-set selection bound |
| Selection threshold | $q_{\rm sel}(N,R)$ | $\rho \le 1/2$ |
| Hausdorff/asymmetry | $C_H'(N,R)$ | BDV Lemma 4.2 + density |
| Flatness threshold | $h_F = \mu\rho_\mu/16$ | BDV Theorem 4.18 thresholds |
| Graph entry | $\alpha_{\rm graph}(N,R) = (h_F/C_H')^{2N}$ | combined |
| Schauder bootstrap | $C_{\rm boot}(N,R)$ | Kinderlehrer-Nirenberg + BDV 4.16 |
| Nearly spherical | $c_{\rm sph}(N), \delta_{\rm sph}(N)$ | BDV Theorem 5.1 |
| Asymmetry vs $L^2$ | $C_{\rm BDV}(N)$ | BDV Lemmas 4.2, 5.2 |
| Quotient lower bound | $c_*(N) = c_{\rm sph}/C_{\rm BDV}$ | combined |
| Saint-Venant small | $q_*(N,R) = c_*/(2C_{\rm sel})$ | Theorem 7.1 |
| Saint-Venant far | $c_{\rm far,SV}(N,R)$ | compactness, Lemma 7.4 |
| Saint-Venant global | $c_{\rm SV} = \min(q_*/C_{\rm Fr}, c_{\rm far,SV})$ | Theorem 7.2 |
| Kohler-Jobin multiplier | $2L_N/((N+2)T_N)$ | universal in $N$ |
| Faber-Krahn small | $L_N c_{\rm SV}/((N+2)T_N)$ | Theorem 9.1 |
| Faber-Krahn far | $c_{\rm far,FK}(N,R)$ | compactness |
| Final $c_{\rm FK}(N,R)$ | $\min(L_N c_{\rm SV}/((N+2)T_N), c_{\rm far,FK}/4)$ | Theorem 9.1 |

Every constant in this chain depends only on $(N,R)$ and is traceable to
named BDV regularity constants.

## What's used from BDV as black box

- **Lemma 4.2**: $\mathcal A(\Omega)^2 \le C_{\rm Fr}(N)\alpha(\Omega)$.
- **Lemma 4.9**: density estimates for penalized minimizers.
- **Lemma 4.12**: Lipschitz/nondegeneracy of torsion potential.
- **Lemma 4.16**: $C^{1,\gamma}$ smoothness of Bernoulli coefficient $q$.
- **Theorem 4.18**: Alt-Caffarelli flatness improvement.
- **Theorem 5.1**: nearly spherical second variation.
- **Lemma 5.2**: $\alpha(U) \le C\|g\|_{L^2}^2$ for graph minimizers.

All cited by theorem number. None are reproved here.

## What's new vs BDV

1. **Single-set selection** (Theorem 2.2): replaces BDV's sequential
   selection + compactness limit. This is the key conceptual contribution.
2. **Explicit graph-entry threshold** $\alpha_{\rm graph}(N,R)$
   (Theorem 4.4): replaces BDV's qualitative "for $n$ large" with an
   explicit number.
3. **Explicit Schauder bootstrap** (Proposition 5.1): writes out the
   hodograph + Kinderlehrer-Nirenberg step that BDV use implicitly.
4. **Full constant chain** (Remark after Theorem 9.1): every constant is
   named and $(N,R)$-trackable.

The output is BDV's Theorem 1.1, with the proof's selection step now
quantitative and constants tracked through the chain.

## What this is NOT

- It's not a new theorem; the statement is BDV's.
- It's not a numerically explicit version; constants are named but not
  computed.
- It doesn't avoid BDV's nearly spherical theorem (Theorem 5.1); that's
  what Route B (`fixed-domain-bernoulli-expansion.md`) would do, and it
  remains conditional on the source enumeration in
  `corrections-response.md`, §3.

## What it IS

A direct, computational proof of the sharp Faber-Krahn inequality with
explicit dependence on $(N,R)$ through the entire chain. Auditable: every
step is either elementary, written out here, or quoted from BDV by theorem
number.

## Where the contradiction was, and what replaced it

| Step | BDV | Plan 1 / Route A |
|------|-----|------------------|
| Selection | sequential + compactness limit (contradiction) | single-set + explicit $C_{\rm sel}(N,R)$ |
| Limit existence | qualitative, $U_n \to U_\infty$ in $L^1$ | not needed |
| $\alpha \to$ graph | qualitative from limit | explicit $\alpha_{\rm graph}(N,R)$ |
| Bootstrap | implicit in BDV regularity | explicit Schauder (Kinderlehrer-Nirenberg) |
| Nearly spherical | BDV Theorem 5.1 | unchanged |
| Quotient lower bound | contradiction with $\alpha(U_\infty)>0$ | direct, $Q_\alpha\ge c_*(N)$ |
| Saint-Venant | by contradiction | by computation |
| Faber-Krahn transfer | Kohler-Jobin | unchanged |

The single contradiction step that was removed: BDV's sequential
selection + compactness limit. Plan 1's single-set selection map is the
device that performs the same regularization in one step, with named
constants.
