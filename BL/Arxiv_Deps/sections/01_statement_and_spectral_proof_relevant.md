# Proof-relevant dependency audit for `sections/01_statement_and_spectral.tex`

This file covers the parts of the statement/spectral chunk that are used, or
can be used, in the proof of the counterexample. Context-only spectral
interpretations are listed separately in
`01_statement_and_spectral_contextual.md`.

## Common mathematics

1. **Definition of essential continuity for convex functions.**

   Precise form: a proper convex function
   `phi : R^d -> R ∪ {+infinity}` is essentially continuous if it is lower
   semicontinuous, finite and continuous on the interior of its effective
   domain, and the set of boundary points of the effective domain where
   continuity fails has `(d-1)`-dimensional Hausdorff measure zero. The theorem
   later specializes to smooth finite-valued strictly convex potentials, so the
   proof does not use this definition.

2. **Locally Lipschitz functions are a.e. differentiable and have weak gradients.**

   Precise form: if `f : R^d -> R` is locally Lipschitz, then `f` is Borel
   measurable, differentiable Lebesgue-a.e. by Rademacher's theorem, and its
   a.e. gradient can be used in the energy integral when the integrand is
   integrable.

3. **Positive definite Hessian and inverse Hessian.**

   Precise form: if `phi : R^d -> R` is smooth and strictly convex with
   positive definite Hessian `D^2 phi(x)` for all `x`, then
   `(D^2 phi(x))^{-1}` exists and is positive definite for all `x`; hence
   `<(D^2 phi)^{-1} grad f, grad f> >= 0` a.e.

4. **Normalization of a finite density into a probability measure.**

   Precise form: if `phi : R^d -> R` is measurable and
   `0 < Z = ∫ exp(-phi x) dx < infinity`, then
   `rho(A) = Z^{-1} ∫_A exp(-phi x) dx` defines a probability measure
   absolutely continuous with respect to Lebesgue measure, with density
   `Z^{-1} exp(-phi)`.

5. **Variance definition and centered norm identity.**

   Precise form: for a probability measure `mu` and `f ∈ L^2(mu)`,
   `Var_mu(f) = ∫ (f - ∫ f dmu)^2 dmu = ∫ f^2 dmu - (∫ f dmu)^2`.
   If `∫ f dmu = 0`, then `Var_mu(f) = ||f||_{L^2(mu)}^2`.

6. **Distance to a linear subspace in a Hilbert space.**

   Precise form: if `H` is a real Hilbert space, `M` is a linear subspace, and
   `x ⟂ M`, then `dist(x, M) = ||x||`. If `M` is finite-dimensional, no closure
   qualifier is needed.

7. **Convex coercive tails in one dimension.**

   Precise form: if `phi : R -> R` is convex, finite-valued, and
   `∫_R exp(-phi x) dx < infinity`, then `phi(x) -> +infinity` as
   `x -> +infinity` and as `x -> -infinity`. If `phi` is differentiable and
   strictly convex, then `phi'` is strictly increasing; in particular, for some
   `x0 > 0`, `phi'(x) >= 0` for `x >= x0` and `phi'(x) <= 0` for `x <= -x0`.

8. **Monotonicity of derivatives of convex functions.**

   Precise form: if `phi : R -> R` is differentiable and convex, then `phi'` is
   monotone nondecreasing. If `phi` is twice differentiable and `phi'' > 0`,
   then `phi'` is strictly increasing.

9. **Integration by parts on finite intervals for locally Lipschitz functions.**

   Precise form: if `h` and `w` are locally absolutely continuous on `[a,b]`,
   then `∫_a^b h w' = h(b)w(b) - h(a)w(a) - ∫_a^b h' w`.
   Used with `w = exp(-phi)`, so `w' = -phi' exp(-phi)`.

10. **Improper integration by parts through vanishing boundary subsequences.**

   Precise form: let `h, phi` satisfy
   `h exp(-phi), h' exp(-phi), h phi' exp(-phi) ∈ L^1(R)`. If there exist
   `R_n -> +infinity` and `R'_n -> -infinity` such that
   `h(R_n) exp(-phi(R_n)) -> 0` and
   `h(R'_n) exp(-phi(R'_n)) -> 0`, then
   `∫ h phi' exp(-phi) = ∫ h' exp(-phi)`.

11. **Existence of boundary-vanishing subsequences for integrable functions.**

   Precise form: if `F : [a, infinity) -> [0, infinity)` is measurable and
   integrable, then there exists a sequence `x_n -> infinity` such that
   `F(x_n) -> 0`. Similarly on `(-infinity, a]`.

12. **Cauchy--Schwarz integrability transfer.**

   Precise form: if `mu` has density `exp(-phi) dx / Z`, and
   `f,g ∈ L^2(mu)`, then `fg exp(-phi) ∈ L^1(dx)`. Also if `g ∈ L^2(mu)`,
   then `g exp(-phi) ∈ L^1(dx)` because `mu` is finite.

13. **Bounded Hessian converts the Brascamp--Lieb form-domain condition to an ordinary derivative `L^2` condition.**

   Precise form: in dimension one, if `0 < phi'' <= M` and
   `∫ (h')^2 / phi'' d rho < infinity`, then
   `∫ (h')^2 d rho <= M ∫ (h')^2 / phi'' d rho < infinity`.

14. **Weak identity for `phi'`.**

   Precise form: let `phi : R -> R` be smooth, strictly convex,
   `∫ exp(-phi) dx ∈ (0, infinity)`, `phi''` bounded, and
   `phi' ∈ L^2(rho_phi)`. For every locally Lipschitz `g ∈ L^2(rho_phi)` with
   `∫ (g')^2 / phi'' d rho_phi < infinity`,
   `∫ g' d rho_phi = ∫ g phi' d rho_phi`, and hence
   `E_phi(phi', g) = <phi', g>`. In particular,
   `∫ phi' d rho_phi = 0` and `E_phi(phi') = Var_{rho_phi}(phi')`.

15. **Finite-dimensional optimizer family as an `L^2` subspace.**

   Precise form: if the functions `1` and `∂_j phi` belong to `L^2(rho_phi)`,
   then `{a · grad phi + b : a ∈ R^d, b ∈ R}` is a finite-dimensional real
   linear subspace of `L^2(rho_phi)`.

## Quoted results from other places

1. **Brascamp--Lieb variance inequality with equality cases.**

   Precise form needed for this paper's general statement: let
   `phi : R^d -> R` be smooth and strictly convex with
   `0 < ∫ exp(-phi) dx < infinity`; let `rho_phi` be the normalized measure.
   For every sufficiently regular real-valued `f` with `f ∈ L^2(rho_phi)` and
   finite energy,
   `Var_{rho_phi}(f) <= ∫ <(D^2 phi)^{-1} grad f, grad f> d rho_phi`.
   Equality holds exactly for functions of the form
   `f(x) = a · grad phi(x) + b`, subject to membership in `L^2(rho_phi)`.

   Reference: H. J. Brascamp and E. H. Lieb, *On extensions of the
   Brunn--Minkowski and Prékopa--Leindler theorems, including inequalities for
   log-concave functions, and with an application to the diffusion equation*,
   J. Funct. Anal. 22 (1976), 366--389.
