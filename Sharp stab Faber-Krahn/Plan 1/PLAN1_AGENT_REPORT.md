# Plan 1 agent report

Date: 2026-05-11 (second pass)

## Second pass: Bernoulli expansion proofs and closure

A follow-up pass added `bernoulli-expansion-proofs.md/.tex/.pdf`, which closes
the analytical gap flagged at the end of `bernoulli-spectral-closure.md`:

1. **Lemma `lem:lin`.** A clean Schauder remainder estimate for the
   pulled-back torsion potential. The key identity
   \(\nabla\cdot(A_g\nabla(f\circ\Phi_g))=J_{\Phi_g}\cdot(\Delta f)\circ\Phi_g\)
   makes the function
   \(\rho_g(x):=\widetilde u_g(x)-u_{B_1}(\Phi_g(x))-u_1(\Phi_g(x))\)
   \(A_g\)-harmonic. Its boundary trace is \(O(\|g\|_{C^{2,\gamma}}^2)\).
   Schauder for the variable-coefficient Dirichlet problem gives
   \(\|\rho_g\|_{C^{2,\gamma}}\le C\|g\|_{C^{2,\gamma}}^2\).

2. **Lemma 5.1 (Bernoulli map expansion), proved.** From \(u_g=u_{B_1}+u_1+r_g\)
   with quadratic remainder, the boundary expansion of
   \(\nabla u_g\) at \(\partial U_g\) yields exactly the spectral operator
   \(\mathcal L:g_k\mapsto(k-1)g_k\).

3. **Lemma 5.2 (\(\alpha\)-bracket expansion), proved.** Explicit
   polynomial expansion of the centroid integral identifies the linear part
   as the degree-1 spherical-harmonic projection.

4. **Volume normalization, handled.** Dilation by \(r_*=1+O(\delta_T)\)
   absorbs into smallness constants.

5. **Quantitative spectral closure theorem.** In the smallness regime,
   the projected nonlinear equation
   \(\mathcal L g_{\ge2}=O(\sigma+\delta_*)g_{\ge2}+\hbox{quadratic}\)
   combined with the Steklov gap forces \(g\equiv0\).

6. **Sharp Saint--Venant/Faber--Krahn stability** (Theorem 8.1 in the new
   note): \(E(\Omega)-E(B_1)\ge c_*(N,R)\alpha(\Omega)\) for small
   \(Q_\alpha\).

7. **Boundary deficit propagation on the selected class** (Theorem 9.1):
   the apparent \(k^2\) vs.\ \(k\) paradox flagged in
   `../Plan 2/weighted-serrin-collar-reduction.md` is resolved because the
   Bernoulli + spectral-gap filtering forces high-frequency modes to vanish.

The selection-principle route is now end-to-end:
selection \(\to\) graph entry \(\to\) Bernoulli spectral closure
\(\Rightarrow\) sharp stability. No external Serrin theorem and no
near-spherical second variation are needed.

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
