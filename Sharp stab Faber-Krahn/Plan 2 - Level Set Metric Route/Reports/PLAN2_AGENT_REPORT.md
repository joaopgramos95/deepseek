# Plan 2 Agent Report

Work scope: only files inside `Sharp stab Faber-Krahn/Plan 2`.

## What changed

1. `level-set-deficit-identity.md`

   Added an explicit near-boundary replacement packet:

   - profile-height lemma on slabs \(S_\eta=[L-2\eta,L-\eta]\);
   - good-level lemma on the corresponding level interval \(T_\eta\);
   - superlevel replacement/transfer estimate
     \[
     \mathcal A(\Omega)\le \mathcal A(E_t)+2|\Omega\setminus E_t|/|\Omega|;
     \]
   - selected-minimizer boundary-layer trace lemma explaining what Plan 1
     regularity must provide.

2. `nicola-tilli-stability-import.md`

   Added a GGRT-to-torsion replacement dictionary and a hybrid Plan 1/Plan 2
   route. The main point is that the profile-gap and transfer-back steps are
   already quantitative; the remaining gap is regularity and boundary-layer
   trace control for selected minimizers.

3. `analytic-native-route.md`

   Added the concrete native-space linearization at the ball:

   - \(h=u+|x|^2/(2N)\) has first variation equal to the harmonic extension of
     the boundary graph;
   - the harmonic Dirichlet norm gives the \(H^{1/2}\) spherical-harmonic
     weights;
   - \(\mathcal K_s\) was rewritten as
     \[
     \mathcal K_s(\Omega)=\int (u_\Omega-t_\Omega)_+ + t_\Omega s,
     \]
     which makes the moving-level first variation cancel;
   - a concrete second-variation formula was isolated;
   - in dimension two, the holomorphic field
     \[
     F_\Omega=\partial_z u_\Omega+\bar z/4
     \]
     was tied to Bergman/Hardy norms through the coefficients of
     \(\partial_z u_1\).

4. `concrete-next-steps.md`

   Added a new Section 0 naming the next best theorem: a selected-minimizer
   boundary-layer theorem that combines the level-set deficit identity with
   Plan 1 regularity.

## What remains unchanged

- I did not edit the `.tex` files or regenerate PDFs.
- I did not change the finite-perimeter proof outline; it remains the clean
  standalone theorem to write.
- I did not claim the pure level-set route is sharp for arbitrary rough domains.
  The current notes still identify a real \(1/\eta\) loss in the slab average.

## Open points

1. The finite-perimeter identity still needs a fully written proof using
   coarea, truncation tests, and distributional differentiation of the profile
   functional.

2. The boundary-slab good-level lemma is quantitative but not sharp by itself:
   it gives
   \[
   D_H(t)+D_I(t)\lesssim \delta_T/\eta.
   \]
   This is why selected-minimizer boundary traces are needed.

3. The approximate-Serrin step still needs an input theorem compatible with the
   weighted \(L^2\) defect
   \[
   \int_{\{u=t\}}\frac{(|\nabla u|-\bar f_t)^2}{|\nabla u|}.
   \]
   Selected-minimizer regularity should allow interpolation to stronger norms,
   but this has not been proved here.

4. The native-space second variation for \(\mathcal K_s\) is now reduced to a
   concrete harmonic calculation, but the coefficients \(a_k(\rho)\) have not
   yet been computed.

## Next best theorem to prove

Prove the selected-minimizer boundary-layer theorem stated in
`concrete-next-steps.md`:

> For a BDV/Plan 1 selected minimizer \(U=\{u>0\}\), find a near-boundary level
> \(E_t=\{u>t\}\) with boundary-layer volume
> \(O(|U|\delta_T(U)^{1/2})\), where \(\delta_T\) is the normalized torsion
> deficit, regular approximate-Serrin geometry, and
> \[
> \mathcal A(U)^2
> \le
> C\left(
> \frac{D_I(t)+D_H(t)}{|U|^{2-2/n}}
> +\delta_T(U)
> \right).
> \]

This theorem is the most promising bridge between the GGRT-style superlevel
replacement strategy and the sharp BDV exponent. It uses Plan 1 only where it
is strongest: turning small positive torsion levels into controlled normal
graphs over the selected free boundary.
