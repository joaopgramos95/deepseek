# Dependency audit for `sections/03_normalization.tex`

## Common mathematics

1. **Change of variables on a half-line.**

   Precise form: for measurable integrable `F`,
   `∫_{1+eps}^{infinity} F(x) dx = ∫_0^infinity F(1+eps+u) du`.

2. **Tail formula substitution.**

   Precise form: if for `x > 1+eps`,
   `phi_S(x)=phi_S(1+eps)+S(x-1-eps)+eta/2*(x^2-(1+eps)^2)`, then after
   `u=x-1-eps`,
   `phi_S(1+eps+u)=phi_S(1+eps)+(S+eta(1+eps))u+eta u^2/2`.

3. **Elementary exponential inequality.**

   Precise form: for all `v >= 0`, `0 <= 1 - exp(-v) <= v`.

4. **Exponential moment integral.**

   Precise form: for `a > 0`,
   `∫_0^infinity exp(-a u) du = 1/a` and
   `∫_0^infinity u^2 exp(-a u) du = 2/a^3`.

5. **Asymptotic reciprocal expansion.**

   Precise form: if `a_S = S + O(S^{-4})`, then
   `1/a_S = 1/S + O(S^{-6})`. More generally,
   if `a_S = S(1 + O(S^{-5}))`, then `1/a_S = S^{-1}(1+O(S^{-5}))`.

6. **Multiplication of asymptotic estimates.**

   Precise form: if `A_S=1+O(S^{-2})` and `B_S=S^{-1}+O(S^{-6})`, then
   `A_S B_S = S^{-1}+O(S^{-3})`.

7. **Small-parameter finite interval integral.**

   Precise form: uniformly for `x ∈ [0,1]`,
   `exp(-eta x^2/2)=1+O(eta)` as `eta -> 0`; hence
   `∫_0^{1-eps} exp(-eta x^2/2) dx = (1-eps)+O(eta)`.

8. **Layer integral estimate from uniform exponential control.**

   Precise form: if `exp(-phi_S)=1+O(S^{-2})` uniformly on an interval of
   length `2 eps`, then the integral over that interval is
   `2 eps + O(eps S^{-2})`.

9. **Probability mass from density integral.**

   Precise form: for `rho_S(A)=Z_S^{-1}∫_A exp(-phi_S) dx`, if
   `A` is the union of two symmetric tails and each tail integral is
   `S^{-1}+O(S^{-3})`, then
   `rho_S(A)=(2/S+O(S^{-3}))/Z_S`.

10. **Bounding measure by length times supremum.**

    Precise form: if `A` has Lebesgue measure `|A|`, and a density `p(x)` is
    bounded above by `M` on `A`, then `∫_A p(x) dx <= M |A|`.
    Used with `A=T_S`, `|T_S|=4 eps`, and density
    `Z_S^{-1} exp(-phi_S)`.

11. **Geometric reciprocal expansion.**

    Precise form: if `r_S = 1/S + O(S^{-3})`, then
    `(1+r_S)^{-1} = 1 - 1/S + 1/S^2 + O(S^{-3})`.

12. **Big-O arithmetic for `q_S`.**

    Precise form: from
    `q_S = S^{-1} (1+O(S^{-2})) (1 - S^{-1} + S^{-2} + O(S^{-3}))`,
    conclude `q_S = S^{-1} - S^{-2} + O(S^{-3})`.

## Quoted results from other places

None.

