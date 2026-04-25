# Big Lean Formalization Tasks

This file lists the dependency items that are likely to be substantial Lean
work. It is optimized for verifying the direct counterexample proof, not for
formalizing every contextual sentence in the paper.

The tasks are divided into:

- **Required for the direct counterexample proof**: needed to prove the main
  theorem as an explicit family of examples.
- **Optional if formalizing the paper verbatim**: needed only for quoted or
  explanatory material that the direct proof can avoid.
- **Omitted contextual/historical material**: intentionally ignored.

Throughout, one should make an early formalization choice:

- either work over `EuclideanSpace R (Fin d)`;
- or prove the higher-dimensional theorem directly on product spaces
  `R × (Fin (d-1) -> R)` and later transport it to `R^d`.

## Required For The Direct Counterexample Proof

### 1. Smooth compactly supported even probability bump

Source audit:
`sections/02_construction_and_profile.md`.

Precise form needed:

Construct `kappa : R -> R` such that:

```text
ContDiff R ⊤ kappa,
Integrable kappa volume,
0 <= kappa x for all x,
|x| > 1 -> kappa x = 0,
kappa (-x) = kappa x for all x,
∫ x, kappa x = 1,
∃ M, ∀ x, |kappa x| <= M.
```

Why this is big:
The paper needs smoothness, support control, normalization, evenness, and
boundedness. A compactly supported smooth bump may exist in mathlib, but this
exact normalized even real-line version may require adaptation.

Possible simplification:
Any compact support interval can be rescaled to `[-1,1]`, provided the
normalization and evenness are preserved.

### 2. Reconstructing the potential from the prescribed second derivative

Source audit:
`sections/02_construction_and_profile.md`.

Precise form needed:

For smooth `h : R -> R`, define using oriented interval integrals

```text
psi x = ∫ t in 0..x, h t
phi x = ∫ u in 0..x, psi u.
```

Then prove:

```text
ContDiff R ⊤ phi,
ContDiff R ⊤ psi,
phi 0 = 0,
psi 0 = 0,
deriv phi = psi,
deriv psi = h,
deriv (deriv phi) = h.
```

If `h` is even, prove:

```text
psi (-x) = -psi x,
phi (-x) = phi x.
```

If `eta > 0` and `h x >= eta` for all `x`, prove:

```text
StrictConvexOn R Set.univ phi,
phi x >= eta * x^2 / 2.
```

Why this is big:
It uses the fundamental theorem of calculus for interval integrals, smoothness
under integration, parity arguments, and strict convexity from second
derivative lower bounds.

### 3. Explicit regional formulas for `phi_S`, `phi'_S`, and `phi''_S`

Source audit:
`sections/02_construction_and_profile.md`,
`sections/03_normalization.md`.

Precise form needed:

For parameters

```text
epsilon S = S^(-3),
eta S = S^(-4),
S sufficiently large,
```

and

```text
phi''_S x =
  eta + (S/epsilon) * kappa ((x-1)/epsilon)
      + (S/epsilon) * kappa ((x+1)/epsilon),
```

prove:

```text
phi''_S x >= eta > 0,
phi''_S x = eta on C_S and on the exterior of the two layers,
phi'_S x = eta*x on C_S,
phi'_S x = eta*x + S on (1+epsilon, infinity),
phi'_S x = eta*x - S on (-infinity, -1-epsilon),
phi_S x = eta*x^2/2 on C_S,
phi_S x =
  phi_S(1+epsilon)
  + S*(x-1-epsilon)
  + eta/2*(x^2-(1+epsilon)^2)
  for x > 1+epsilon.
```

Also prove support-scaling identities:

```text
∫ x in 1-epsilon..1+epsilon,
  (S/epsilon) * kappa ((x-1)/epsilon) = S,
```

and the analogous identity at `-1`.

Why this is big:
The facts are elementary, but Lean will require detailed support,
change-of-variables, interval-membership, and endpoint bookkeeping.

### 4. Positivity and finiteness of all constants and denominators

Source audit:
all proof files.

Precise form needed:

For all sufficiently large `S`, prove:

```text
0 < epsilon,
0 < eta,
0 < phi''_S x for all x,
0 < Z_S = ∫ x, exp (-phi_S x),
Z_S < infinity,
0 < A_S = ∫ x in 1-epsilon..1+epsilon,
          phi''_S x * exp (phi_S x),
A_S < infinity,
delta_S = E_phi_S f_S - Var rho_S f_S > 0 eventually,
all denominators used in ratios are nonzero eventually.
```

Why this is big:
Lean will not infer denominator positivity from context. These lemmas occur
throughout the proof and should be centralized.

### 5. Gaussian domination and explicit exponential integrals

Source audit:
`sections/02_construction_and_profile.md`,
`sections/03_normalization.md`,
`sections/06_higher_dimensions.md`.

Precise forms needed:

For `eta > 0`:

```text
Integrable (fun x : R => exp (-(eta*x^2/2))) volume.
```

If `phi` is measurable or continuous and
`phi x >= eta*x^2/2` for all `x`, prove:

```text
Integrable (fun x => exp (-phi x)) volume.
```

For `a > 0`, prove half-line identities, with a chosen Lean representation of
half-line integration, e.g.

```text
∫ u in Set.Ioi (0:R), exp (-a*u) ∂volume = 1/a,
∫ u in Set.Ioi (0:R), u^2 * exp (-a*u) ∂volume = 2/a^3.
```

For the standard Gaussian on `(Fin n -> R)`, define or use a measure `γ_n`
such that:

```text
γ_n Set.univ = 1,
∫ y, y j ∂γ_n = 0,
γ_n has density proportional to exp (-||y||^2/2).
```

Why this is big:
Some of this may exist in mathlib, but the exact half-line moment identities
and finite-dimensional Gaussian normalization/factorization can take time to
locate or prove.

### 6. Normalization and tail asymptotics

Source audit:
`sections/03_normalization.md`.

Precise form needed:

Formalize the estimates:

```text
∫ x in Set.Ioi (1+epsilon), exp (-phi_S x)
  = 1/S + O(S^(-3)),

Z_S = ∫ x, exp (-phi_S x)
  = 2 + 2/S + O(S^(-3)),

q_S = rho_S {x | |x| > 1+epsilon}
  = 1/S - 1/S^2 + O(S^(-3)),

t_S = rho_S T_S = O(S^(-3)).
```

Key analytic ingredients:

```text
0 <= 1 - exp (-v) <= v for v >= 0,
∫_0^∞ exp (-a*u) du = 1/a,
∫_0^∞ u^2 * exp (-a*u) du = 2/a^3,
change of variables x = 1+epsilon+u,
bounded-density estimate measure(A) <= length(A) * sup density.
```

Why this is big:
This is where most concrete real-analysis estimates enter. It is not
conceptually deep, but it combines change of variables, improper integrals,
and filter/asymptotic bookkeeping.

### 7. Concrete energy/deficit definition for the constructed function class

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`,
`sections/04_test_function.md`,
`sections/05_gap_and_1d_conclusion.md`.

Precise form needed:

Define for the one-dimensional constructed potentials and piecewise absolutely
continuous functions:

```text
E_phi(f) = ∫ x, (f_deriv x)^2 / phi'' x ∂rho_phi,
delta_phi(f) = E_phi(f) - Var rho_phi f.
```

Here `f_deriv` must be a specified a.e. derivative or a piecewise derivative
representative. Prove that changing `f_deriv` on a null set does not change
the integral, or avoid equivalence classes by using an explicit derivative
formula for the constructed `f_S`.

Why this is big:
The paper writes derivatives classically. Lean needs an exact representation of
derivatives for piecewise functions and of the weighted energy integral.

### 8. Piecewise test function `g_S`

Source audit:
`sections/04_test_function.md`,
`sections/05_gap_and_1d_conclusion.md`.

Precise form needed:

Define a real-valued function `g_S : R -> R`, not a subtype-valued function,
by:

```text
g_S x = 0 on C_S,
g_S x = 1 on E_S,
g_S x =
  (∫ t in 1-epsilon..|x|, phi''_S t * exp (phi_S t))
  / A_S
  on the two transition layers,
```

where

```text
A_S = ∫ t in 1-epsilon..1+epsilon,
      phi''_S t * exp (phi_S t).
```

Prove:

```text
0 <= g_S x <= 1 for all x,
g_S is even,
g_S is continuous,
g_S(±(1-epsilon)) = 0,
g_S(±(1+epsilon)) = 1,
g_S is locally absolutely continuous on each region,
g'_S x = 0 outside I_S^+ ∪ I_S^- away from endpoints,
g'_S x =  phi''_S x * exp (phi_S x) / A_S on I_S^+,
g'_S x = -phi''_S x * exp (phi_S x) / A_S on I_S^-.
```

Optional, only if matching the paper's admissibility class exactly:

```text
g_S is globally Lipschitz.
```

Why this is big:
Piecewise functions, absolute values, endpoint matching, and a.e. derivatives
are typically technical in Lean.

### 9. Direct layer energy identity

Source audit:
`sections/04_test_function.md`.

Precise form needed:

Avoiding the full weighted Dirichlet minimization theorem, prove directly:

```text
If A_S = ∫_{I_S^+} phi''_S * exp(phi_S),
and g'_S = phi''_S * exp(phi_S) / A_S on I_S^+,
then
∫_{I_S^+} (g'_S)^2 / phi''_S * exp(-phi_S)
  = 1 / A_S.
```

Similarly on `I_S^-`, using the negative derivative but the same square.

Then prove:

```text
E_phi_S(g_S)
  = 2 / (Z_S * A_S)
  = 2/(Z_S*S) * (1 + O(S^(-2))).
```

Why this is big:
This is the essential energy computation. It is much smaller than formalizing
the variational minimizer theorem but still requires interval restrictions,
derivative formulas, and integral algebra.

### 10. Variance computation for `g_S`

Source audit:
`sections/04_test_function.md`.

Precise form needed:

Using `0 <= g_S <= 1`, `g_S=1` on the exterior, `g_S=0` on the central
plateau, and `rho_S(T_S)=O(S^(-3))`, prove:

```text
∫ g_S ∂rho_S  = q_S + O(S^(-3)),
∫ g_S^2 ∂rho_S = q_S + O(S^(-3)),
Var rho_S g_S = q_S*(1-q_S) + O(S^(-3)),
Var rho_S g_S = 1/S - 2/S^2 + O(S^(-3)).
```

Why this is big:
This is mostly measure decomposition and asymptotic algebra. It should be
straightforward once the region partition and asymptotics are set up, but it
is a core proof component.

### 11. Parity package and orthogonality

Source audit:
`sections/05_gap_and_1d_conclusion.md`.

Precise form needed:

Prove:

```text
phi_S is even,
phi'_S is odd,
exp(-phi_S) is even,
rho_S has even density,
g_S is even,
c_S = ∫ g_S ∂rho_S,
f_S = g_S - c_S is even,
∫ f_S ∂rho_S = 0,
∫ f_S * phi'_S ∂rho_S = 0.
```

The key general lemma:

```text
If p is even, u is odd, and u*p is integrable,
then ∫ u(x)*p(x) dx = 0.
```

or, equivalently, if `mu` is invariant under `x -> -x`, the integral of an
integrable odd function is zero.

Why this is big:
The mathematical idea is simple, but the proof uses measure invariance under
reflection, integrability, and parity of constructed functions.

### 12. Distance to the finite-dimensional optimizer space

Source audit:
`sections/05_gap_and_1d_conclusion.md`,
`sections/06_higher_dimensions.md`.

Precise form needed:

Define the one-dimensional optimizer subspace as:

```text
O_S = span_R {1, phi'_S} ⊆ L^2(rho_S).
```

Prove:

```text
1 ∈ L^2(rho_S),
phi'_S ∈ L^2(rho_S),
1 and phi'_S are linearly independent,
f_S ⟂ 1,
f_S ⟂ phi'_S,
f_S ⟂ O_S,
dist(f_S, O_S)^2 = ||f_S||^2 = Var rho_S g_S.
```

Why this is big:
This requires choosing how to represent `L^2` functions and finite-dimensional
subspaces in Lean, and moving between pointwise functions and `L^2` equivalence
classes.

### 13. One-dimensional deficit asymptotics and failure of a uniform constant

Source audit:
`sections/05_gap_and_1d_conclusion.md`.

Precise form needed:

From the energy and variance estimates, prove:

```text
E_phi_S(f_S) = 1/S - 1/S^2 + O(S^(-3)),
Var rho_S f_S = 1/S - 2/S^2 + O(S^(-3)),
delta_phi_S(f_S) = 1/S^2 + O(S^(-3)),
dist(f_S,O_S)^2 / delta_phi_S(f_S)
  = S * (1 + O(S^(-1))).
```

Then prove the logical conclusion:

```text
No finite C satisfies
dist(f,O_phi) <= C * sqrt(delta_phi(f))
for all smooth strictly convex one-dimensional phi and admissible f.
```

Why this is big:
Mostly asymptotics and quantifier management. The final contradiction needs
careful eventual positivity of `delta_phi_S(f_S)`.

### 14. Product extension to higher dimensions

Source audit:
`sections/06_higher_dimensions.md`.

Precise form needed:

For `d >= 2`, either work on `R × (Fin (d-1) -> R)` or provide an explicit
equivalence with `EuclideanSpace R (Fin d)`. Define:

```text
Phi_S(x,y) = phi_S(x) + ||y||^2/2,
F_S(x,y) = f_S(x).
```

Prove:

```text
rho_{Phi_S} = rho_S ⊗ gamma_{d-1},
Z_{Phi_S} = Z_S * ∫ y, exp(-||y||^2/2),
D^2 Phi_S = blockDiag (phi''_S) I,
(D^2 Phi_S)^(-1) = blockDiag (1/phi''_S) I,
E_{Phi_S}(F_S) = E_{phi_S}(f_S),
Var rho_{Phi_S} F_S = Var rho_S f_S,
delta_{Phi_S}(F_S) = delta_{phi_S}(f_S).
```

Define the product optimizer space:

```text
span_R {1, phi'_S(x), y_1, ..., y_{d-1}},
```

and prove `F_S` is orthogonal to all generators. This uses:

```text
∫ 1 ∂gamma = 1,
∫ y_j ∂gamma = 0,
Fubini/Tonelli for product measures.
```

Why this is big:
It combines product measures, Gaussian moments, finite-dimensional calculus,
block matrices, Fubini, and `L^2` subspaces.

### 15. Concrete asymptotics toolkit for `S -> infinity`

Source audit:
`sections/00_abstract.md`,
`sections/02_construction_and_profile.md`,
`sections/03_normalization.md`,
`sections/04_test_function.md`,
`sections/05_gap_and_1d_conclusion.md`.

Precise form needed:

Choose one parameter model:

- real filter `S -> infinity` with eventual hypotheses `S >= 1`, or
- a sequence `S_n : Nat -> R`, e.g. `S_n = n+1`.

Develop reusable lemmas for:

```text
epsilon=S^(-3), eta=S^(-4),
S*epsilon = S^(-2),
eta*epsilon = S^(-7),
eta/S = S^(-5),

exp(O(S^(-2))) = 1 + O(S^(-2))
  for eventually nonnegative small exponents,

(1 + O(S^(-k)))^(-1) = 1 + O(S^(-k))
  with eventual nonzero denominators,

(1 + 1/S + O(S^(-3)))^(-1)
  = 1 - 1/S + 1/S^2 + O(S^(-3)),

(1+O(S^(-2))) * (S^(-1)+O(S^(-6)))
  = S^(-1)+O(S^(-3)),

(S^(-1)-S^(-2)+O(S^(-3)))^2
  = S^(-2)-2*S^(-3)+O(S^(-4)),

S^(-2)+O(S^(-3)) = S^(-2)*(1+O(S^(-1))),

(S^(-1)-2*S^(-2)+O(S^(-3)))
  /(S^(-2)+O(S^(-3)))
  = S*(1+O(S^(-1))),

sqrt(S*(1+O(S^(-1))))
  = sqrt(S)*(1+O(S^(-1))),

eventual positivity from positive leading term.
```

Why this is big:
The facts are elementary, but Lean proofs involving `IsBigO`, real powers,
inverses, square roots, and eventual nonzero denominators can be time-consuming.

## Optional If Formalizing The Paper Verbatim

These are not needed for the direct counterexample proof if the formalization
is allowed to streamline the exposition around the explicit examples.

### A. Brascamp--Lieb variance inequality and equality cases

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`,
`bibliography.md`.

Reference:
H. J. Brascamp and E. Lieb, *On extensions of the Brunn--Minkowski and
Prekopa--Leindler theorems, including inequalities for log-concave functions,
and with an application to the diffusion equation*, J. Funct. Anal. 22 (1976),
366--389.

Precise form:

Let `d > 0`, let `phi : EuclideanSpace R (Fin d) -> R` be smooth, with
positive definite Hessian everywhere, and assume
`0 < Z_phi = ∫ x, exp(-phi x) < infinity`. Let `rho_phi` be the probability
measure with density `Z_phi^{-1} exp(-phi)`. For every chosen admissible class
of real-valued functions `f`,

```text
Var rho_phi f
  <= ∫ x, <(D^2 phi x)^(-1) (grad f x), grad f x> ∂rho_phi.
```

Equality means equality a.e. in `L^2(rho_phi)` with a function
`x => a · grad phi x + b`, subject to that function belonging to `L^2`.

### B. General locally Lipschitz/Rademacher infrastructure

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`.

Needed only if the deficit is defined for all locally Lipschitz functions as in
the paper. The exact formalization must choose whether the gradient is:

- pointwise derivative where it exists and zero elsewhere,
- weak derivative,
- a Sobolev representative,
- or some existing mathlib a.e. derivative object.

### C. Weak `phi'` integration-by-parts lemma

Source audit:
`sections/01_statement_and_spectral_proof_relevant.md`.

Needed only if formalizing Lemma `lem:phi-prime-eigen`. The direct
counterexample only needs parity orthogonality to `phi'_S`, not the weak
eigenvalue identity.

Precise form:

Let `phi : R -> R` be `C^1`, with `exp(-phi x) -> 0` at both infinities. Let
`h` be locally absolutely continuous with an a.e. derivative `h_deriv`.
Assume:

```text
h * exp(-phi)        ∈ L^1(dx),
h_deriv * exp(-phi)  ∈ L^1(dx),
h * deriv phi * exp(-phi) ∈ L^1(dx).
```

If boundary subsequences make `h(x) exp(-phi x)` tend to zero at both
infinities, then:

```text
∫ x, h x * deriv phi x * exp(-phi x)
  = ∫ x, h_deriv x * exp(-phi x).
```

### D. Weighted one-dimensional Dirichlet minimization theorem

Source audit:
`sections/04_test_function.md`.

Needed only if preserving the variational "energy-minimizing interpolation"
explanation. The direct proof can use Task 9 instead.

Precise form:

For `a < b`, measurable `w` on `[a,b]` with
`0 < m <= w x <= M < infinity` a.e., and `Delta : R`, among absolutely
continuous functions on `[a,b]` with `h(a)=0`, `h(b)=Delta`, the minimum of

```text
∫ x in a..b, (h_deriv x)^2 * w x
```

is:

```text
Delta^2 / ∫ x in a..b, (w x)^(-1).
```

The minimizer is unique, with derivative a.e.

```text
h_deriv x =
  Delta * (w x)^(-1) / ∫ x in a..b, (w x)^(-1).
```

## Omitted Contextual/Historical Material

The following are intentionally not included as big tasks for the direct
formalization:

1. The Machado--Ramos sharp uniform `L^1` stability theorem mentioned in the
   abstract.
2. The spectral-operator interpretation in
   `sections/01_statement_and_spectral_contextual.md`, including closed forms,
   compact resolvent, and spectral-infimum language.
3. The affine-invariance/Poincare discussion in `sections/07_affine_remark.md`.
4. Essential continuity of extended-valued convex functions, unless one wants
   to formalize the broad introductory setup verbatim rather than the smooth
   constructed counterexample.

