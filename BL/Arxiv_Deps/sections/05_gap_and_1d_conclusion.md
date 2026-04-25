# Dependency audit for `sections/05_gap_and_1d_conclusion.tex`

## Common mathematics

1. **Adding a constant does not change derivative energy.**

   Precise form: for locally Lipschitz `g` and constant `c`,
   `(g-c)' = g'` a.e.; hence `E_phi(g-c)=E_phi(g)`.

2. **Adding a constant does not change variance.**

   Precise form: for any probability measure `mu`,
   `Var_mu(g-c)=Var_mu(g)`.

3. **Mean-zero centering.**

   Precise form: if `c=∫g dmu`, then `∫(g-c)dmu=0`.

4. **Parity under even measures.**

   Precise form: if `mu` has an even density on `R`, `f` is even, and `h` is
   odd with `fh ∈ L^1(mu)`, then `∫ f h dmu = 0`.

5. **Integrability of the orthogonality product.**

   Precise form: if `f, phi' ∈ L^2(rho_S)`, then
   `f phi' ∈ L^1(rho_S)` by Cauchy--Schwarz.

6. **Linear independence of `1` and a nonconstant function in `L^2`.**

   Precise form: if `u` is not a.e. constant with respect to `mu`, then
   `{1,u}` is linearly independent in `L^2(mu)`.

7. **Orthogonality to generators implies orthogonality to their span.**

   Precise form: if `<f,e_i>=0` for every generator `e_i` of a finite-dimensional
   subspace `M`, then `f ⟂ M`.

8. **Distance to an orthogonal finite-dimensional subspace.**

   Precise form: if `f ⟂ M`, then
   `dist_{L^2}(f,M)^2 = ||f||_2^2`.

9. **Centered `L^2` norm equals variance.**

   Precise form: if `∫f dmu=0`, then `||f||_2^2=Var_mu(f)`.

10. **Deficit is energy minus variance.**

    Precise form: by definition,
    `delta_{BL,phi}(f)=E_phi(f)-Var_{rho_phi}(f)`.

11. **Asymptotic subtraction.**

    Precise form: if
    `E(S)=S^{-1}-S^{-2}+O(S^{-3})` and
    `V(S)=S^{-1}-2S^{-2}+O(S^{-3})`, then
    `E(S)-V(S)=S^{-2}+O(S^{-3})`.

12. **Eventual positivity from a positive leading term.**

    Precise form: if `a(S)=S^{-2}(1+O(S^{-1}))`, then there exists `S0` such
    that `a(S)>0` for all `S>=S0`.

13. **Asymptotic division.**

    Precise form: if
    `N(S)=S^{-1}(1-2/S+O(S^{-2}))` and
    `D(S)=S^{-2}(1+O(S^{-1}))`, then
    `N(S)/D(S)=S(1+O(S^{-1}))`.

14. **Failure of a uniform constant from divergent ratios.**

    Precise form: if a putative inequality
    `dist(f_S,O_S) <= C sqrt(delta(f_S))` held for all sufficiently large `S`,
    then `dist(f_S,O_S)^2/delta(f_S) <= C^2`, contradicting
    `dist(f_S,O_S)^2/delta(f_S) -> infinity`.

## Quoted results from other places

None. The one-dimensional conclusion does not invoke the Brascamp--Lieb
inequality once the deficit has been explicitly computed and shown positive for
large `S`.

