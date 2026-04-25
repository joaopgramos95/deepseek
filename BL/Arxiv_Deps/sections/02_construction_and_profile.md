# Dependency audit for `sections/02_construction_and_profile.tex`

## Common mathematics

1. **Existence of a smooth even probability bump.**

   Precise form: there exists `kappa : R -> R` such that `kappa ∈ C^\infty`,
   `kappa(x) >= 0` for all `x`, `support(kappa) ⊆ [-1,1]`,
   `kappa(-x) = kappa(x)` for all `x`, and `∫_R kappa(x) dx = 1`.

2. **Smooth reconstruction from a prescribed second derivative.**

   Precise form: if `h : R -> R` is smooth, then there is a unique smooth
   `phi : R -> R` satisfying `phi'' = h`, `phi(0) = 0`, and `phi'(0) = 0`,
   namely `phi'(x) = ∫_0^x h(t) dt` and
   `phi(x) = ∫_0^x ∫_0^u h(t) dt du`.

3. **Even second derivative gives even potential and odd derivative.**

   Precise form: if `h` is even and `phi'' = h`, `phi(0)=phi'(0)=0`, then
   `phi` is even and `phi'` is odd.

4. **Strict convexity from positive second derivative.**

   Precise form: if `phi ∈ C^2(R)` and `phi''(x) >= eta > 0` for all `x`, then
   `phi` is strictly convex.

5. **Quadratic lower bound from `phi'' >= eta`.**

   Precise form: if `phi'' >= eta > 0`, `phi(0)=0`, and `phi'(0)=0`, then
   `phi(x) >= eta x^2 / 2` for all `x`.

6. **Gaussian domination gives integrability.**

   Precise form: if `phi(x) >= eta x^2 / 2` for all `x`, with `eta > 0`, then
   `∫_R exp(-phi(x)) dx <= ∫_R exp(-eta x^2/2) dx < infinity`.

7. **Support-scaled bump integral.**

   Precise form: if `kappa` is supported in `[-1,1]`, then
   `kappa((x-1)/eps)` is supported in `[1-eps, 1+eps]`, and
   `∫_{1-eps}^{1+eps} (S/eps) kappa((x-1)/eps) dx = S`.
   Similarly for the bump centered at `-1`.

8. **Derivative and potential formulas on regions outside bump support.**

   Precise form: with `phi''_S` as in the paper and `eps < 1/4`,
   on `[-1+eps, 1-eps]`, both bump terms vanish and
   `phi'_S(x)=eta x`, `phi_S(x)=eta x^2/2`.
   On `(1+eps, infinity)`, the right bump has total mass `S`, the left bump has
   total mass `S`, but by oddness and normalization the right-tail formula is
   `phi'_S(x)=eta x + S`; integrating gives
   `phi_S(x)=phi_S(1+eps)+S(x-1-eps)+eta/2*(x^2-(1+eps)^2)`.

9. **Elementary estimates for exponential near zero.**

   Precise form: if `0 <= u <= C S^{-2}` for sufficiently large `S`, then
   `exp(u)=1+O(S^{-2})` and `|exp(u)-1| <= u exp(u) = O(S^{-2})`.

10. **Integral estimate with a uniformly small multiplicative error.**

    Precise form: if `F_S >= 0`, `∫_I F_S = S + O(S^{-7})`, and
    `G_S = 1 + O(S^{-2})` uniformly on `I`, then
    `∫_I F_S G_S = S(1 + O(S^{-2}))`.

11. **Big-O substitutions for the chosen parameters.**

    Precise form: for `eps=S^{-3}` and `eta=S^{-4}`,
    `S eps = S^{-2}`, `eta eps = S^{-7}`, and `eta/S = S^{-5}`.

## Quoted results from other places

None.

