# Dependency audit for `sections/06_higher_dimensions.tex`

## Common mathematics

1. **Smoothness and strict convexity of product/sum potentials.**

   Precise form: if `phi_S : R -> R` is `C^\infty` and strictly convex, then
   `Phi_S(x,y)=phi_S(x)+|y|^2/2` on `R × R^{d-1}` is `C^\infty` and strictly
   convex for every integer `d >= 2`.

2. **Block diagonal Hessian.**

   Precise form:
   `D^2 Phi_S(x,y)=diag(phi''_S(x), I_{d-1})`, and if `phi''_S(x)>0`, then
   `(D^2 Phi_S(x,y))^{-1}=diag(1/phi''_S(x), I_{d-1})`.

3. **Product density factorization.**

   Precise form: if
   `Phi_S(x,y)=phi_S(x)+|y|^2/2`, then the normalized probability measure
   with density proportional to `exp(-Phi_S)` is
   `rho_S ⊗ gamma_{d-1}`, where `gamma_{d-1}` is the standard Gaussian
   probability measure on `R^{d-1}`.

4. **Gaussian normalization and first moments.**

   Precise form: for the standard Gaussian `gamma_{d-1}`,
   `∫ 1 d gamma_{d-1}=1` and `∫ y_j d gamma_{d-1}=0` for
   `j=1,...,d-1`.

5. **Gradient of a function depending on one coordinate.**

   Precise form: if `F(x,y)=f(x)`, then
   `grad F(x,y)=(f'(x),0,...,0)`.

6. **Pointwise quadratic form with block diagonal inverse Hessian.**

   Precise form:
   `<(D^2 Phi_S)^{-1} grad F, grad F> = (f'(x))^2 / phi''_S(x)`.

7. **Fubini/Tonelli for product measures.**

   Precise form: if `G(x,y)=g(x)` is integrable with respect to
   `rho_S ⊗ gamma_{d-1}`, then
   `∫ G d(rho_S⊗gamma)=∫ g d rho_S * ∫1 d gamma = ∫ g d rho_S`.
   Similarly, if `G(x,y)=g(x)h(y)`, then
   `∫G d(rho⊗gamma)=∫g d rho * ∫h d gamma`, provided the factors are integrable.

8. **Variance of a pullback to a product space.**

   Precise form: if `F(x,y)=f(x)` and the second factor is a probability
   measure, then `Var_{rho⊗nu}(F)=Var_rho(f)`.

9. **Optimizer space for product potential.**

   Precise form: for `Phi_S(x,y)=phi_S(x)+|y|^2/2`,
   `grad Phi_S=(phi'_S(x), y_1,...,y_{d-1})`; hence
   `{a·grad Phi_S+b}` is
   `span_R{1, phi'_S(x), y_1,...,y_{d-1}}`, with all generators in `L^2` under
   `rho_S⊗gamma`.

10. **Orthogonality factorization.**

    Precise form: if `F(x,y)=f(x)`, then
    `<F, phi'_S(x)> = <f, phi'_S>_{L^2(rho_S)}`,
    and `<F,y_j> = (∫ f d rho_S)(∫ y_j d gamma)=0`.

11. **Divergent ratio preserved under identical numerator and denominator.**

    Precise form: if for the product construction
    `dist_{Phi_S}(F_S)^2 = dist_{phi_S}(f_S)^2` and
    `delta_{Phi_S}(F_S)=delta_{phi_S}(f_S)`, then the ratio is unchanged.

## Quoted results from other places

None.

