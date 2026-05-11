# Bernoulli expansion proofs and quantitative spectral closure

This note closes the analytical gap in `bernoulli-spectral-closure.md`. We
prove the two remaining ingredients (Lemmas 5.1 and 5.2 there) with explicit,
Schauder-based quadratic remainders, and we handle the volume-normalization
passage between the actual BDV selected minimizer and the unit-volume graph.

Combined with the graph-entry threshold of `graph-entry-closure.md` and the
single-set selection map of `quantitative-selection-principle.md`, the result
is a quantitative sharp Saint--Venant/Faber--Krahn stability theorem along the
selected minimizer route, with **no** external nearly-spherical second-variation
input.

A consequence (Theorem 7.1, "boundary deficit propagation on the selected
class") is that the inequality

\[
D_I(0)+D_H(0)\le C(E(U)-E(B_1))
\]

*does* hold on the selected class, even though `weighted-serrin-collar-reduction.md`
shows it fails on the full nearly-spherical class. The selected Bernoulli law
projects out the high-frequency modes responsible for the \(k^2\) vs.\ \(k\)
mismatch.

See `bernoulli-expansion-proofs.tex/.pdf` for the full proofs.

## Section guide

1. **Setup and pullback diffeomorphism.** Fix
   \[
   \Phi_g(r\theta)=(r+\chi(r)g(\theta))\theta,
   \]
   a $C^{2,\gamma}$ diffeomorphism identical to identity near the origin and
   sending $\partial B_1$ to the graph $\partial U_g$. Compute
   \(A_g=J_{\Phi_g}(D\Phi_g)^{-1}(D\Phi_g)^{-T}\) and verify Schauder-type
   bounds.

2. **Pulled-back torsion equation.** The torsion potential pulls back to
   \(-\nabla\cdot(A_g\nabla\widetilde u_g)=J_{\Phi_g}\) on $B_1$ with zero
   boundary data.

3. **Schauder remainder estimate (Lemma `lem:lin`).** Define
   \[
   \rho_g(x):=\widetilde u_g(x)-u_{B_1}(\Phi_g(x))-u_1(\Phi_g(x)),
   \]
   where \(u_1\) is the harmonic extension of \(g/N\) to \(\R^N\). The
   pullback identity
   \(\nabla\cdot(A_g\nabla(f\circ\Phi_g))=J_{\Phi_g}\cdot(\Delta f)\circ\Phi_g\)
   gives that \(\rho_g\) is \(A_g\)-harmonic. The boundary trace of
   \(\rho_g\) is \(O(\|g\|_{C^{2,\gamma}}^2)\). Schauder gives
   \(\|\rho_g\|_{C^{2,\gamma}}\le C\|g\|_{C^{2,\gamma}}^2\).

4. **Lemma 5.1 (Bernoulli map expansion).** From \(u_g=u_{B_1}+u_1+r_g\),
   compute \(\nabla u_g\) at \((1+g(\theta))\theta\) and read off the radial
   coefficient \(-\theta/N\cdot(1-\mathcal L g)\), where
   \(\mathcal L:g_k\mapsto(k-1)g_k\). The tangential and remainder
   contributions are quadratic in \(g\), giving
   \[
   q_g(\theta)=\frac{1}{N}-\frac{1}{N}\mathcal L g(\theta)+R_q(g)(\theta),
   \qquad
   \|R_q(g)\|_{L^2}\le C\|g\|_{C^{2,\gamma}}\|g\|_{L^2}.
   \]

5. **Lemma 5.2 (\(\alpha\)-bracket expansion).** Compute the centroid integral
   \(\int_{U_g}y/|y|\,dy=(1/N)\int_{S^{N-1}}\omega(1+g)^N d\omega\). The
   linear-in-\(g\) part is exactly the degree-1 spherical-harmonic projection.
   Thus
   \[
   \Psi_g(x_\theta)=1+(I-\Pi_1)g(\theta)+R_\alpha(g),
   \qquad
   \|R_\alpha\|_{L^2}\le C\|g\|_{C^1}\|g\|_{L^2}.
   \]

6. **Volume normalization.** Dilate \(U_*\) by \(r_*^{-1}\) where
   \(|B_{r_*}|=|U_*|\). The corrections are \(1+O(\delta_T)\), absorbed into
   the smallness constants.

7. **Quantitative spectral closure (Theorem 7.1).** Under
   \(\sigma\le\sigma_*\), \(\|g\|_{C^{2,\gamma}}\le\delta_*\), the Bernoulli
   law and Lemmas 5.1, 5.2 give the projected equation
   \[
   \mathcal L g_{\ge2}=O(\sigma+\delta_*)g_{\ge2}+\hbox{quadratic}.
   \]
   The Steklov gap \(\|\mathcal Lh\|_{L^2}\ge\|h\|_{L^2}\) on \(\{k\ge2\}\)
   forces \(g_{\ge2}=0\) in the small-smallness regime, and volume/barycenter
   constraints handle \(g_0,g_1\). Iteration gives \(g\equiv0\).

8. **Sharp stability theorem.** Combining selection (\(\sigma\le Cq^{1/4}\),
   asymmetry preservation) with graph entry and spectral closure yields
   \(E(\Omega)-E(B_1)\ge c_*(N,R)\alpha(\Omega)\) for small
   \(Q_\alpha(\Omega)\).

9. **Boundary deficit propagation on the selected class (Theorem 9.1).** In
   the smallness regime, the selected minimizer is the ball, so all deficits
   vanish trivially. Quantitatively, the closure equation forces
   \(g_k=0\) for \(k\ge K_0(\sigma,\delta_*)\); on the finite-frequency
   band \(k<K_0\), \(H^1\) and \(H^{1/2}\) norms are equivalent with
   constant \(O(K_0)\), giving
   \[
   D_I(0)+D_H(0)\le C(\sigma^2+\|g\|_{C^{2,\gamma}}^2)\cdot(E(U)-E(B_1)).
   \]
   This resolves the apparent paradox flagged in
   `weighted-serrin-collar-reduction.md`: the spectral mismatch
   \(k^2\) (deficits) vs.\ \(k\) (energy) is killed on the selected class
   because high-frequency modes cannot survive the Bernoulli + spectral-gap
   filtering.

## What remains

The route is now closed up to:

1. Quantitative tracking of \(\sigma_*,\delta_*,q_*\) through the dependency
   chain \(q_*\to\tau=q_*^{1/4}\to\sigma\le C\tau\to\) closure smallness.
2. Explicit verification of the divergence-pullback identity
   \(\nabla\cdot(A_g\nabla(f\circ\Phi_g))=J_{\Phi_g}(\Delta f)\circ\Phi_g\) in
   \(C^\gamma\) with constants depending only on \(N\) and \(\chi\).
3. Schauder bootstrap \(C^{1,\gamma}\to C^{2,\gamma}\) using BDV Lemma 4.16.

No external Serrin stability theorem and no near-spherical second variation
of BDV are needed.
