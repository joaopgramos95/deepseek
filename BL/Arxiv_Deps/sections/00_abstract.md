# Dependency audit for `sections/00_abstract.tex`

The abstract summarizes the main construction and the relationship between the
asymptotic ratio and failure of a uniform stability constant.

## Common mathematics

1. **Ratio divergence implies no uniform square-root stability constant.**

   Precise form: let `(X_n, d_n, delta_n, A_n)` be data with `delta_n > 0` and
   `d_n^2 / delta_n -> +infty`. Then there is no finite constant `C` such that
   `d_n <= C * sqrt(delta_n)` for all `n`. Equivalently, if such a `C` existed,
   then `d_n^2 / delta_n <= C^2` for all `n`.

2. **Asymptotic square root.**

   Precise form: if `R(S) = S * (1 + O(S^{-1}))` as `S -> infinity` and
   `R(S) > 0` for all sufficiently large `S`, then
   `sqrt(R(S)) = sqrt(S) * (1 + O(S^{-1}))`.

3. **Big-O arithmetic over real-valued functions.**

   Precise form: for functions of a real parameter `S -> infinity`,
   multiplication, division by a nonzero asymptotic unit, and square roots of
   positive asymptotic units preserve the expected `O` estimates.

## Quoted results from other places

1. **Sharp uniform `L^1` stability estimate for the Brascamp--Lieb variance inequality.**

   This is mentioned for context in the first sentence and is not used in the
   proof of the counterexample. A formalization of that historical claim would
   need the exact theorem statement from:

   Reference: J. M. Machado and J. P. G. Ramos, *Quantitative stability for
   Brascamp--Lieb and moment measures*, arXiv:2511.22636v2.

   The present paper only uses the existence of the constructed family and does
   not invoke the `L^1` stability theorem.

