# Big Lean formalization tasks (superseded)

This file extracts the proof-relevant dependencies from `Arxiv_Deps` that are
unlikely to be one-line mathlib lookups or routine algebra. Contextual and
historical items are intentionally omitted: the `L^1` stability reference,
the spectral-operator motivation, and the affine-invariance/Poincare remark
are not needed for the direct formalization of the counterexample.

## 1. Brascamp--Lieb variance inequality and equality cases

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`,
`bibliography.md`.

Status: quoted external theorem; likely a major formalization project.

Reference:
H. J. Brascamp and E. H. Lieb, *On extensions of the Brunn--Minkowski and
Prekopa--Leindler theorems, including inequalities for log-concave functions,
and with an application to the diffusion equation*, J. Funct. Anal. 22 (1976),
366--389.

Precise form needed if the whole exposition is formalized:

Let `d : Nat`, let `phi : R^d -> R` be smooth and strictly convex, with
positive definite Hessian `D^2 phi(x)` for all `x`, and assume
`0 < Z_phi = ∫ exp(-phi x) dx < infinity`. Let `rho_phi` be the probability
measure with density `Z_phi^{-1} exp(-phi)`. For every sufficiently regular
real-valued `f` with `f ∈ L^2(rho_phi)` and finite energy,

```text
Var_{rho_phi}(f)
  <= ∫ <(D^2 phi x)^{-1} grad f x, grad f x> d rho_phi(x).
```

Equality holds exactly for `L^2(rho_phi)` functions of the form

```text
f(x) = a · grad phi(x) + b
```

with `a : R^d` and `b : R`.

Notes:
The direct counterexample proof computes a positive deficit explicitly for the
constructed examples, so the inequality is not needed to prove the divergence.
It is still a nontrivial quoted statement present in the paper.

## 2. Locally Lipschitz analysis and a.e. gradients

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`.

Status: likely a large analysis infrastructure task unless already available in
the required generality.

Precise form needed:

If `f : R^d -> R` is locally Lipschitz, then:

1. `f` is Borel measurable.
2. `f` is differentiable Lebesgue-a.e. (Rademacher theorem).
3. The a.e. derivative defines a measurable weak/a.e. gradient.
4. The Brascamp--Lieb energy integrand
   `<(D^2 phi)^{-1} grad f, grad f>` is measurable when `phi` is smooth and
   `D^2 phi` is positive definite.
5. In dimension one, locally Lipschitz functions are locally absolutely
   continuous, so the fundamental theorem of calculus and integration by parts
   can be applied on compact intervals.

Why this is big:
The paper states the deficit for locally Lipschitz functions. A Lean
formalization can reduce some work by restricting the final test functions to
piecewise `C^1`/absolutely continuous functions, but if the paper is
formalized exactly as written, the locally Lipschitz-to-a.e.-gradient bridge is
substantial.

## 3. Improper weighted integration by parts on the real line

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`.

Status: medium-to-large custom analysis lemma.

Precise form needed:

Let `phi : R -> R` be smooth with `exp(-phi x) -> 0` at both infinities. Let
`h : R -> R` be locally absolutely continuous. Assume

```text
h * exp(-phi)       ∈ L^1(dx),
h' * exp(-phi)      ∈ L^1(dx),
h * phi' * exp(-phi) ∈ L^1(dx).
```

Assume there exist sequences `R_n -> +infinity` and `L_n -> -infinity` such
that

```text
h(R_n) exp(-phi(R_n)) -> 0,
h(L_n) exp(-phi(L_n)) -> 0.
```

Then

```text
∫_R h(x) phi'(x) exp(-phi(x)) dx
  = ∫_R h'(x) exp(-phi(x)) dx.
```

Auxiliary lemma also needed:
If `F : [a, infinity) -> [0, infinity)` is measurable and integrable, then
there exists a sequence `x_n -> infinity` with `F(x_n) -> 0`; similarly on
`(-infinity,a]`.

Why this is big:
It combines improper integrals, locally absolutely continuous functions,
boundary subsequences, and weighted integrability. It is not a deep theorem,
but in Lean this is more than routine algebra.

## 4. Smooth compactly supported even probability bump

Source audit:
`sections/02_construction_and_profile.md`.

Status: potentially a big task depending on available smooth bump functions in
mathlib.

Precise form needed:

There exists `kappa : R -> R` such that:

```text
kappa ∈ C^\infty,
kappa(x) >= 0 for all x,
support(kappa) ⊆ [-1,1],
kappa(-x) = kappa(x) for all x,
∫_R kappa(x) dx = 1.
```

Why this is big:
Constructing and normalizing a nonnegative compactly supported `C^\infty`
bump is a standard smooth-manifold analysis fact. It may be present in some
form in mathlib, but the exact real-line, even, normalized, support-controlled
version may require nontrivial adaptation.

Possible simplification:
For this paper, the shape of `kappa` is irrelevant beyond smoothness,
nonnegativity, evenness, support, and integral one. If a mathlib bump has
slightly different support, rescaling can be used.

## 5. Reconstructing a smooth potential from a prescribed second derivative

Source audit:
`sections/02_construction_and_profile.md`.

Status: medium task, especially with smoothness and parity.

Precise form needed:

If `h : R -> R` is smooth, define

```text
phi'(x) = ∫_0^x h(t) dt,
phi(x)  = ∫_0^x phi'(u) du.
```

Then:

```text
phi ∈ C^\infty,
phi(0)=0,
phi'(0)=0,
phi''=h.
```

If `h` is even, then `phi` is even and `phi'` is odd. If `h(x) >= eta > 0`
for all `x`, then `phi` is strictly convex and

```text
phi(x) >= eta * x^2 / 2.
```

Why this is big:
The calculus is elementary, but a polished Lean version needs the fundamental
theorem of calculus for parameterized integrals, smoothness under integration,
parity lemmas, and convexity from a positive second derivative.

## 6. Gaussian domination and explicit exponential integrals

Source audit:
`sections/02_construction_and_profile.md`,
`sections/03_normalization.md`,
`sections/06_higher_dimensions.md`.

Status: medium-to-large depending on existing integral library coverage.

Precise forms needed:

1. If `eta > 0`, then

   ```text
   ∫_R exp(-eta*x^2/2) dx < infinity.
   ```

2. If `phi(x) >= eta*x^2/2`, then

   ```text
   ∫_R exp(-phi(x)) dx < infinity.
   ```

3. For `a > 0`,

   ```text
   ∫_0^∞ exp(-a*u) du = 1/a,
   ∫_0^∞ u^2 * exp(-a*u) du = 2/a^3.
   ```

4. The standard Gaussian measure on `R^n` is normalized and has zero coordinate
   means:

   ```text
   ∫ 1 dγ_n = 1,
   ∫ y_j dγ_n = 0.
   ```

Why this is big:
Mathlib likely contains many Gaussian/exponential integral facts, but the
exact half-line moment identities and the finite-dimensional product Gaussian
normalization may require locating or proving reusable lemmas.

## 7. Weighted one-dimensional Dirichlet minimization

Source audit:
`sections/04_test_function.md`.

Status: big custom variational lemma.

Precise form needed:

Let `I=(a,b)` be a bounded interval and let `w : I -> R` be measurable with

```text
0 < m <= w(x) <= M < infinity
```

for a.e. `x ∈ I`. Let `Delta : R`. Among absolutely continuous functions
`h : [a,b] -> R` with endpoint traces

```text
h(a)=0, h(b)=Delta,
```

and `h' ∈ L^2(I)`, the minimum of

```text
∫_a^b (h'(x))^2 * w(x) dx
```

is

```text
Delta^2 / ∫_a^b w(x)^{-1} dx.
```

The unique minimizer satisfies

```text
h'(x) = Delta * w(x)^{-1} / ∫_a^b w^{-1}
```

a.e.

In this paper:

```text
w(x) = exp(-phi_S(x)) / phi''_S(x),
w(x)^{-1} = phi''_S(x) exp(phi_S(x)).
```

Why this is big:
This packages Sobolev traces on intervals, coercivity, existence/uniqueness of
a minimizer, Euler--Lagrange equations, and the explicit Cauchy--Schwarz or
calculus-of-variations resistance formula. It is probably the largest
paper-specific lemma after Brascamp--Lieb if formalized in this variational
language.

Possible simplification:
The proof does not actually need the full minimization theorem. It only needs
the explicit derivative formula for the chosen `g_S` and the resulting energy
identity. A Lean formalization could bypass minimization and prove directly:

```text
if g'_S = phi''_S exp(phi_S) / A on I_S^+,
then ∫ (g'_S)^2 / phi''_S * exp(-phi_S) = 1/A.
```

This would avoid Sobolev trace and minimizer-existence infrastructure.

## 8. Piecewise-defined globally Lipschitz test function

Source audit:
`sections/04_test_function.md`,
`sections/05_gap_and_1d_conclusion.md`.

Status: medium-to-large if using locally Lipschitz APIs; smaller if using a
custom piecewise absolutely continuous representation.

Precise form needed:

The function `g_S : R -> [0,1]` defined by:

```text
g_S = 0 on C_S,
g_S = 1 on E_S,
g_S(x) = (∫_{1-eps}^{|x|} phi''_S(t) exp(phi_S(t)) dt)
         / (∫_{I_S^+} phi''_S(t) exp(phi_S(t)) dt)
         on the two transition layers
```

is:

```text
continuous,
even,
globally Lipschitz,
locally absolutely continuous on each region,
0 <= g_S <= 1,
g'_S = 0 a.e. outside the layers,
g'_S = ± phi''_S exp(phi_S) / A on the layers.
```

Why this is big:
Lean formalization of piecewise functions with absolute values, interval
endpoints, a.e. derivatives, and global Lipschitz continuity can be technical.
This is not conceptually hard, but it tends to be time-consuming.

Possible simplification:
Avoid proving global Lipschitz if the formal deficit is defined on a custom
class of piecewise absolutely continuous functions sufficient for the example.

## 9. Product measure and product potential reduction

Source audit:
`sections/06_higher_dimensions.md`.

Status: medium-to-large, depending on available product-measure and Gaussian
library support.

Precise form needed:

For `d >= 2`, define

```text
Phi_S(x,y) = phi_S(x) + |y|^2/2
```

on `R × R^{d-1}`. Then:

1. The normalized density proportional to `exp(-Phi_S)` is
   `rho_S ⊗ gamma_{d-1}`.
2. `D^2 Phi_S = diag(phi''_S, I)` and
   `(D^2 Phi_S)^{-1}=diag(1/phi''_S, I)`.
3. For `F_S(x,y)=f_S(x)`,

   ```text
   E_{Phi_S}(F_S)=E_{phi_S}(f_S),
   Var_{rho_{Phi_S}}(F_S)=Var_{rho_S}(f_S),
   delta_{Phi_S}(F_S)=delta_{phi_S}(f_S).
   ```

4. The optimizer space is

   ```text
   span_R {1, phi'_S(x), y_1, ..., y_{d-1}},
   ```

   and `F_S` is orthogonal to all these generators.

Why this is big:
It mixes finite-dimensional calculus, block matrices, product probability
measures, Fubini/Tonelli, Gaussian coordinate moments, and finite-dimensional
subspace orthogonality.

## 10. Asymptotics library for the concrete parameter `S -> infinity`

Source audit:
`sections/00_abstract.md`,
`sections/02_construction_and_profile.md`,
`sections/03_normalization.md`,
`sections/04_test_function.md`,
`sections/05_gap_and_1d_conclusion.md`.

Status: likely many pieces are in mathlib, but the paper uses enough concrete
`O` arithmetic that a dedicated local asymptotics toolkit may be needed.

Precise forms needed:

For real `S -> infinity`, prove reusable lemmas for:

```text
S * S^{-3} = S^{-2},
S^{-4} * S^{-3} = S^{-7},
(1 + O(S^{-k}))^{-1} = 1 + O(S^{-k}) when k > 0,
(1 + 1/S + O(S^{-3}))^{-1}
  = 1 - 1/S + 1/S^2 + O(S^{-3}),
(S^{-1} - S^{-2} + O(S^{-3}))^2
  = S^{-2} - 2S^{-3} + O(S^{-4}),
(S^{-1} - 2S^{-2} + O(S^{-3})) / (S^{-2}+O(S^{-3}))
  = S(1+O(S^{-1})).
```

Why this is big:
Not mathematically deep, but if the goal is an end-to-end Lean proof, a large
amount of time can disappear into normalizing real powers, inverses, eventual
positivity, and filter-based `IsBigO`/`Tendsto` manipulations.

## Explicitly omitted as historical/contextual

The following audit entries were intentionally not included as big tasks:

1. The Machado--Ramos sharp uniform `L^1` stability theorem mentioned in the
   abstract.
2. The spectral-operator interpretation in
   `sections/01_statement_and_spectral_contextual.md`, including closed forms,
   compact resolvent, and spectral-infimum language.
3. The affine-invariance/Poincare discussion in `sections/07_affine_remark.md`.
4. The definition of essential continuity for extended-valued convex functions,
   because the proof and theorem construction use smooth finite-valued strictly
   convex potentials.
