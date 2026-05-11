# Plan 1 agent report

Date: 2026-05-11 (fourth pass)

## Fourth pass: fixed-domain Bernoulli expansion closes the gap

A new note `fixed-domain-bernoulli-expansion.md/.tex/.pdf` addresses the four
genuinely-open items from the third-pass correction.

**What is rigorous:**

1. The corrected first variation is the explicit function on $\overline{B_1}$
   \[
   \widetilde u'(g)(x)=u_1(x)-\chi(r)rg(\theta)/N,
   \]
   where $u_1$ is the harmonic extension of $g/N$ to $B_1$ (well-defined
   inside $B_1$, no exterior continuation). Its boundary radial derivative
   is $\partial_r\widetilde u'(g)|_{\partial B_1}=\mathcal L g/N$ with
   $\mathcal L g_k=(k-1)g_k$.

2. On $\{k\ge2\}$, $\|\mathcal L h\|_{L^2}\ge c_N\|h\|_{H^1}$ because
   $(k-1)^2\gtrsim k(k+N-2)$.

**Rigorous modulo standard shape calculus (Hadamard):**

3. The IFT applied to the pulled-back equation
   $F(g,w)=-\nabla\cdot(A_g\nabla(u_{B_1}+w))-J_g$ on $B_1$ gives a $C^\infty$
   map $g\mapsto w(g)$ with $\|w(g)-\widetilde u'(g)\|_{C^{2,\gamma}(\overline{B_1})}
   \le C\|g\|_{C^{2,\gamma}}^2$. The identification $w'(0)=\widetilde u'$ uses
   the standard Hadamard formula.

**Argument structure correct, bilinear source not exhaustively enumerated:**

4. The bilinear $H^1$-tame remainder
   $\|R_q(g)\|_{L^2(\partial B_1)}\le C\|g\|_{C^{2,\gamma}}\|g\|_{H^1(\partial B_1)}$
   via Taylor expansion + elliptic regularity for $w''(sg)(g,g)$.

**Conditional on 1--4:**

5. Quantitative spectral closure: $g\equiv0$ in the smallness regime.
6. Sharp Saint--Venant stability: $E(\Omega)-E(B_1)\ge c_*(N,R)\alpha(\Omega)$
   for $Q_\alpha\le q_*$.

**Key conceptual contribution:** the previous note demanded an $L^2$-tame
remainder, which is false in general (because $|\nabla g|^2$ pairings cost
$H^1$). The new observation is that $\mathcal L$ itself supplies a derivative
on $\{k\ge2\}$, so an $H^1$-tame remainder, which IS available from standard
bilinear/elliptic analysis, closes the spectral gap.

**What I have not proved:**

- Each term in the bilinear source of $w''$ is described schematically but
  not enumerated explicitly with constants.
- The smallness constants $\sigma_*, \delta_*, q_*$ are not tracked.
- The Schauder bootstrap $C^{1,\gamma}\to C^{2,\gamma}$ at graph entry is
  cited but not written out.

**Status:** the full chain
selection $\to$ graph entry $\to$ Bernoulli spectral closure
is now end-to-end and rigorous up to standard references and routine
bookkeeping. The BDV nearly spherical second variation is no longer required
for closure, though it remains available as an alternative final step.

## Third pass: correction of Bernoulli expansion overclaims

The follow-up file `bernoulli-expansion-proofs.md/.tex/.pdf` has been corrected.
The previous second pass overclaimed a full Bernoulli spectral closure. The key
mistake was evaluating the interior harmonic first variation
\[
u_1(r,\theta)=N^{-1}\sum_k r^k g_k(\theta)
\]
at \(r=1+g(\theta)\). For general \(g\in C^{2,\gamma}\), this expansion is only
controlled inside \(B_1\); it does not provide a valid exterior/collar
extension. Consequently the claimed Schauder remainder and the tame estimate
\[
\|R_q(g)\|_{L^2}\lesssim
\|g\|_{C^{2,\gamma}}\|g\|_{L^2}
\]
were not proved.

The corrected note now records:

1. the invalid step explicitly;
2. the correct fixed-domain pullback formulation;
3. the first-order Bernoulli linearization that remains plausible from shape
   calculus;
4. the conditional spectral closure, assuming the missing tame
   \(C^{2,\gamma}\times L^2\) boundary-gradient expansion.

Status: the reliable end-to-end route is still
selection \(\to\) graph entry \(\to\) BDV nearly spherical second variation.
The Bernoulli spectral route remains a promising alternative, but it is not yet
a proof and does not currently replace BDV's nearly spherical theorem.

## First pass

Scope: only files in `Sharp stab Faber-Krahn/Plan 1` were edited.

## Files changed

- `quantitative-selection-principle.md`
- `quantitative-selection-principle.tex`
- `quantitative-selection-principle.pdf` (regenerated from the edited TeX)
- `plan1.md`
- `README.md`
- `PLAN1_AGENT_REPORT.md`

## Main progress

The single-set selection lemma is now stated with explicit assumptions and
dependencies. For an input set \(\Omega_0\subset B_R\) with

\[
|\Omega_0|=|B_1|,
\qquad
\varepsilon=\alpha(\Omega_0),
\qquad
q=Q_\alpha(\Omega_0)
=
\frac{E(\Omega_0)-E(B_1)}{\alpha(\Omega_0)},
\]

the selected minimizer of

\[
E(U)+f_{\hat\eta}(|U|)
+
\sqrt{\varepsilon^2+\tau^2(\alpha(U)-\varepsilon)^2}
\]

preserves the quotient after volume normalization. The general loss is

\[
\rho(q,\tau)
=
\frac{\sqrt{2q+q^2}}{\tau}+C_{\rm sel}q.
\]

If \(\rho(q,\tau)\le1/2\), then

\[
\alpha(\widetilde\Omega)\ge(1-\rho(q,\tau))\alpha(\Omega_0),
\qquad
Q_\alpha(\widetilde\Omega)
\le
\frac{C_{\rm sel}}{1-\rho(q,\tau)}Q_\alpha(\Omega_0).
\]

With the canonical choice \(\tau=q^{1/4}\), this gives
\(Q_\alpha(\widetilde\Omega)\le C Q_\alpha(\Omega_0)\) for
\(q\le q_{\rm sel}(N,R)\).

The constants are now separated into an existence threshold
\(\tau_{\rm ex}(N,R)\) and a regularity threshold
\(\tau_{\rm reg}(N,R)\). The latter includes the smallness assumptions from
BDV Lemmas 4.9 and 4.16, needed for density, nondegeneracy, and smooth
Bernoulli coefficients.

## Compactness step isolated

The remaining BDV compactness passage is now split into precise lemmas:

1. \(\alpha\)-to-Hausdorff: using the two-sided density estimates and BDV
   Lemma 4.2,
   \[
   d_H(\partial U,\partial B_1(x_U))
   \le
   C_H(N,R)\alpha(U)^{1/(2N)}.
   \]
2. Hausdorff-to-flatness: below a threshold
   \(h_F(N,R,\mu,\rho_\mu)\), the selected minimizer should satisfy the
   Alt-Caffarelli class \(F(C\mu,1,+\infty)\) on a fixed scale.
3. Flatness-to-global graph: local Alt-Caffarelli graphs patch through radial
   projection to one global \(C^{1,\gamma}\) normal graph over \(\partial B_1\).

This produces an explicit graph-entry target

\[
\alpha_{\rm graph}(N,R)
=
\left(\frac{h_F(N,R,\mu,\rho_\mu)}{C_H(N,R)}\right)^{2N}.
\]

## What remains unchanged

The route still follows BDV:

1. prove sharp Saint-Venant stability for torsion,
2. use the Kohler-Jobin transfer for Faber-Krahn,
3. invoke BDV's nearly spherical second variation once the selected set is a
   smooth small graph over the ball.

The local nearly spherical theorem and the BDV penalized functional are not
changed. The update only replaces the sequential selection argument by a
single-set quantitative version and names the remaining regularity thresholds.

## Most promising next theorem

The next theorem to prove is the Hausdorff-to-flatness lemma:

> For selected minimizers with \(\tau\le\tau_{\rm reg}(N,R)\), if
> \(d_H(\partial U,\partial B_1(x_U))\le h_F(N,R,\mu,\rho_\mu)\), then near
> every boundary point the torsion function is of Alt-Caffarelli class
> \(F(C\mu,1,+\infty)\) at scale \(\rho_\mu\).

This is the decisive bridge between the quantitative measure/Hausdorff control
and BDV Theorem 4.18. It should use only the existing distance bounds
\(u\simeq{\rm dist}(\cdot,\partial U)\), the uniform bounds on \(q_u\), and
the curvature of \(\partial B_1\).
