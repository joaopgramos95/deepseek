# Dependency audit for `sections/07_affine_remark.tex`

This remark is explanatory and is not used to prove the counterexample. It
would still need the following facts if formalized end-to-end.

## Common mathematics

1. **Affine pushforward of an absolutely continuous measure.**

   Precise form: let `T(x)=A x+b` with `A ∈ GL_d(R)`. If
   `rho_phi` has density `Z_phi^{-1} exp(-phi(x)) dx`, and
   `tilde_phi(y)=phi(T^{-1}y)`, then
   `rho_tilde_phi = T_# rho_phi`, after accounting for the Lebesgue
   change-of-variables factor in the normalization constant:
   `Z_tilde_phi = |det A| Z_phi`.

2. **Gradient chain rule for affine changes.**

   Precise form: if `tilde_f(y)=f(T^{-1}y)` and `T^{-1}(y)=A^{-1}(y-b)`, then
   `grad tilde_f(y)=A^{-T} grad f(T^{-1}y)`.

3. **Hessian chain rule for affine changes.**

   Precise form: if `tilde_phi(y)=phi(T^{-1}y)`, then
   `D^2 tilde_phi(y)=A^{-T} D^2 phi(T^{-1}y) A^{-1}`.

4. **Inverse of an affine-conjugated positive definite matrix.**

   Precise form: if `H` is invertible and
   `tilde_H=A^{-T} H A^{-1}`, then
   `tilde_H^{-1}=A H^{-1} A^T`.

5. **Invariance of the Brascamp--Lieb energy under affine pushforward.**

   Precise form: with the notation above,
   `∫ <(D^2 tilde_phi)^{-1} grad tilde_f, grad tilde_f> d rho_tilde_phi`
   equals
   `∫ <(D^2 phi)^{-1} grad f, grad f> d rho_phi`.

6. **Variance preservation under measure-preserving pushforward.**

   Precise form: if `nu=T_# mu` and `tilde_f=f∘T^{-1}`, then
   `∫ tilde_f dnu = ∫ f dmu` and `Var_nu(tilde_f)=Var_mu(f)`.

7. **Optimizer space covariance.**

   Precise form: if `tilde_phi=phi∘T^{-1}`, then
   `{a·grad tilde_phi + b : a∈R^d,b∈R}`
   equals `{(c·grad phi+b)∘T^{-1} : c∈R^d,b∈R}` with the coefficient relation
   `c=A^{-1}a` (or equivalently `a=A c` depending on column convention).

8. **`L^2` isometry under pushforward.**

   Precise form: if `nu=T_# mu`, then the map
   `U : L^2(mu) -> L^2(nu)`, `U f = f∘T^{-1}`, is an isometric linear
   isomorphism. Consequently, for any subspace `M`,
   `dist_{L^2(nu)}(U f, U M)=dist_{L^2(mu)}(f,M)`.

9. **Affine invariance of the ratio.**

   Precise form: combining energy, variance, deficit, optimizer-space
   covariance, and distance preservation gives
   `dist^2/delta` unchanged by invertible affine reparametrizations.

10. **Scaling of the Euclidean Poincare constant under linear maps.**

    Precise form: if the Euclidean Poincare constant of `mu` is the best
    constant `C_P(mu)` in
    `Var_mu(f) <= C_P(mu) ∫ |grad f|^2 dmu`, and `T(x)=A x`, then the
    Poincare constant of `T_# mu` can change by factors controlled by the
    singular values of `A`; in particular for anisotropic diagonal `A`, it can
    be multiplied by the square of the stretching scale in the tested
    direction.

11. **Rayleigh quotient interpretation of the constructed mode.**

    Precise form: for a mean-zero `f` orthogonal to the optimizer space,
    `E_phi(f)/Var_phi(f) -> 1` means that `f` is a near-equality mode for the
    Brascamp--Lieb Rayleigh quotient outside the optimizer space.

## Quoted results from other places

None. The remark references the general Brascamp--Lieb framework but does not
quote a theorem beyond the Brascamp--Lieb inequality/equality case already
listed in `01_statement_and_spectral_proof_relevant.md`.

