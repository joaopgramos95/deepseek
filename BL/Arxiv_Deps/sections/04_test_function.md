# Dependency audit for `sections/04_test_function.tex`

## Common mathematics

1. **Fundamental theorem of calculus for parameter-dependent integrals.**

   Precise form: if `F` is continuous on `[a,b]`, then
   `G(x)=∫_a^x F(t) dt` is `C^1` on `[a,b]` and `G'(x)=F(x)`.
   Applied to `F = phi''_S exp(phi_S)` on the transition layers.

2. **Derivative of a composition with absolute value on separated intervals.**

   Precise form: on `(1-eps,1+eps)`, `d |x|/dx = 1`; on
   `(-1-eps,-1+eps)`, `d |x|/dx = -1`.

3. **Continuity of a piecewise-defined function at endpoints.**

   Precise form: if adjacent formulas have the same endpoint values, the
   piecewise function is continuous at the endpoint. Here the integral formula
   gives `0` at `|x|=1-eps` and `1` at `|x|=1+eps`.

4. **Piecewise bounded derivative plus continuity gives global Lipschitz on finitely many intervals.**

   Precise form: if `R` is partitioned into finitely many intervals, a function
   is continuous globally and has derivative bounded by `M` on the interior of
   each interval, then it is globally Lipschitz with constant at most `M` on the
   union, provided it is constant outside the outer intervals as here.

5. **Bounded functions belong to `L^2` for probability measures.**

   Precise form: if `mu` is a probability measure and `|f| <= M`, then
   `f ∈ L^2(mu)` and `||f||_2 <= M`.

6. **Weighted one-dimensional Dirichlet minimization.**

   Precise form: let `I=(a,b)` be a bounded interval, `w:I -> R` measurable
   with `0 < m <= w(x) <= M < infinity` a.e., and `Delta ∈ R`. Among
   absolutely continuous functions `h` on `[a,b]` with `h(a)=0`, `h(b)=Delta`
   and `h' ∈ L^2(I)`, the minimum of `∫_a^b (h')^2 w dx` is
   `Delta^2 / ∫_a^b w^{-1} dx`. The minimizer is unique and satisfies
   `h'(x)=Delta w(x)^{-1}/∫_a^b w^{-1}` a.e.

   In the paper, `w=e^{-phi_S}/phi''_S`, so `w^{-1}=phi''_S e^{phi_S}`.

7. **Sobolev trace and affine boundary-value subspace on an interval.**

   Precise form: each `W^{1,2}(a,b)` function has well-defined endpoint traces,
   and the set of functions with prescribed traces `h(a)=0`, `h(b)=Delta` is a
   nonempty affine translate of `W^{1,2}_0(a,b)`.

8. **Strict convexity/coercivity of the weighted quadratic functional.**

   Precise form: if `w` is bounded above and below by positive constants, then
   `h -> ∫ (h')^2 w` is strictly convex in the derivative and coercive on the
   affine space of fixed boundary values modulo constants; with fixed endpoints
   this gives existence and uniqueness of the minimizer.

9. **Symmetry of layer integrals.**

   Precise form: if `phi_S` and `phi''_S` are even, then
   `∫_{I_S^-} phi''_S exp(phi_S) = ∫_{I_S^+} phi''_S exp(phi_S)` by the change
   of variables `x -> -x`.

10. **Energy of a function constant outside layers.**

    Precise form: if `g' = 0` a.e. outside `I_S^+ ∪ I_S^-`, then
    `E_phi(g)` is the sum of the two layer energy integrals divided by `Z_S`.

11. **Bounds from `0 <= g <= 1`.**

    Precise form: if `0 <= g <= 1`, then `0 <= g^2 <= 1`, hence for any set
    `A`, `0 <= ∫_A g dmu <= mu(A)` and `0 <= ∫_A g^2 dmu <= mu(A)`.

12. **Variance algebra with small errors.**

    Precise form: if `∫g dmu = q + R1`, `∫g^2 dmu = q + R2`,
    `|R1|, |R2| <= C S^{-3}`, and `q=O(S^{-1})`, then
    `Var_mu(g)=q(1-q)+O(S^{-3})`.

13. **Expansion of `q(1-q)`.**

    Precise form: if `q=S^{-1}-S^{-2}+O(S^{-3})`, then
    `q^2=S^{-2}-2S^{-3}+O(S^{-4})` and
    `q(1-q)=S^{-1}-2S^{-2}+O(S^{-3})`.

## Quoted results from other places

None.

