# Contextual dependency audit for `sections/01_statement_and_spectral.tex`

These statements explain the spectral viewpoint but are not necessary for the
direct counterexample proof, which uses explicit functions, energies,
orthogonality, and asymptotics.

## Common mathematics

1. **Closure of a nonnegative symmetric Dirichlet form gives a self-adjoint operator.**

   Precise form: let `H` be a Hilbert space and `q` a densely defined,
   nonnegative, symmetric, closed quadratic form. Then there exists a unique
   nonnegative self-adjoint operator `L` such that
   `q(f,g) = <L f, g>` for all `f ∈ Dom(L)` and `g ∈ Dom(q)`.

2. **Rayleigh quotient lower bound and spectral infimum.**

   Precise form: for a nonnegative self-adjoint operator `L` associated with
   a closed form `q`, the assertion `q(f) >= c ||f||^2` for all
   `f ∈ Dom(q) ∩ M`, where `M` is a closed invariant subspace, is equivalent to
   `inf spec(L restricted to M) >= c`.

3. **Rayleigh quotients close to a lower spectral bound imply no uniform spectral gap.**

   Precise form: if for a family of self-adjoint operators `L_S` and closed
   subspaces `M_S` there exist nonzero `f_S ∈ Dom(q_S) ∩ M_S` with
   `q_S(f_S) / ||f_S||^2 -> 1`, then the quantities
   `inf spec(L_S restricted to M_S) - 1` cannot be bounded below by a positive
   constant, assuming `q_S >= ||.||^2` on `M_S`.

4. **Compact resolvent turns spectral infimum above the first eigenspace into a next eigenvalue.**

   Precise form: if a nonnegative self-adjoint operator has compact resolvent,
   then its spectrum consists only of eigenvalues of finite multiplicity with
   no finite accumulation except infinity. In that case, a Rayleigh-quotient
   collapse on the orthogonal complement of the first eigenspace can be phrased
   as collapse of the next eigenvalue.

## Quoted results from other places

None beyond the Brascamp--Lieb inequality and equality cases listed in
`01_statement_and_spectral_proof_relevant.md`.

