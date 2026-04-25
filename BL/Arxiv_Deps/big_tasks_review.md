# Review report for `big_tasks.md`

This report checks `Arxiv_Deps/big_tasks.md` for mistakes and Lean-relevant
imprecision. I take the dependency audits in the other `Arxiv_Deps` files as
given, and I ignore explicitly historical/contextual material.

## Overall Assessment

The file is useful as a first triage, but it is not yet precise enough to guide
an end-to-end Lean formalization. The main problems are:

1. Some listed tasks are optional for the direct proof and should be labeled as
   optional, not required.
2. Several statements use informal mathematical notation that hides important
   Lean choices: the type of `R^d`, interval integrals versus set integrals,
   derivatives of equivalence classes, and subtype-valued versus real-valued
   functions.
3. A few statements are too strong, too vague, or not quite the version the
   paper actually needs.
4. Some genuinely large proof-relevant tasks are missing or only implicit.

## Issues By Location

### Lines 9-47: Brascamp--Lieb inequality and equality cases

**Issue 1: This is not needed for the direct counterexample proof.**

The note at lines 44-47 correctly says the direct proof computes the deficit
explicitly and does not use Brascamp--Lieb nonnegativity. If the goal is only
to Lean-verify the theorem "no uniform `L^2` stability constant exists", then
the Brascamp--Lieb inequality can be omitted entirely. What is needed is only
the definition of the optimizer space as the affine span
`{a · grad phi + b}`.

Recommendation: label this task as "needed only to formalize the quoted
Brascamp--Lieb statement/equality-case paragraph, not needed for the
counterexample theorem."

**Issue 2: The statement is not Lean-precise.**

The phrase "sufficiently regular" at line 28 is not a formal hypothesis. A Lean
statement must choose a domain: for example, `f` locally Lipschitz with finite
energy, or `f` smooth compactly supported, or a Sobolev/form-domain class.

Recommendation: replace "sufficiently regular" by one exact function class.

**Issue 3: The type `R^d` is ambiguous in Lean.**

Line 25 uses `R^d`. In Lean this should likely be `(Fin d -> R)` with its
Euclidean norm and inner product, or `EuclideanSpace R (Fin d)`. The case
`d=0` should be excluded or handled.

Recommendation: specify `d : Nat`, `[Fact (0 < d)]`, and a concrete Euclidean
space type.

**Issue 4: Strict convexity and positive definite Hessian are not equivalent.**

Line 25 assumes both smooth strict convexity and positive definite Hessian. The
paper's theorem says "smooth strictly convex"; the constructed potentials do
have positive Hessian. For the full quoted Brascamp--Lieb theorem, the standard
form uses strict/uniform Hessian positivity or a positive definite Hessian a.e.,
depending on regularity.

Recommendation: say explicitly that the formalized quoted theorem is being
restricted to the stronger `D^2 phi(x)` positive definite version.

**Issue 5: Equality cases require care.**

Lines 36-42 say equality holds exactly for all `L^2` functions of the form
`a · grad phi + b`. In formalization, this statement also needs:

- finite energy for those functions,
- membership of `grad phi` components in `L^2(rho_phi)`,
- a precise meaning of equality in `L^2`, i.e. almost everywhere.

Recommendation: write equality as "`f =ᵐ[mu] fun x => a · grad phi x + b`".

### Lines 49-76: Locally Lipschitz analysis and a.e. gradients

**Issue 6: This task may be avoidable.**

The final test function is explicitly piecewise smooth/absolutely continuous.
If the formal development defines the deficit on a narrower class sufficient
for the constructed examples, then Rademacher's theorem and general locally
Lipschitz gradient infrastructure are unnecessary.

Recommendation: label this as "only needed if formalizing the paper's
locally-Lipschitz generality exactly."

**Issue 7: The statement conflates derivative and gradient choices.**

Line 63 says the a.e. derivative defines a measurable weak/a.e. gradient. In
Lean, a locally Lipschitz function is a pointwise function, while `L^2`
gradients are usually a.e. objects. One must choose whether the energy is
defined using:

- pointwise derivative where it exists and zero elsewhere,
- weak derivative,
- a Sobolev representative,
- or piecewise derivative for the explicit example.

Recommendation: add this design choice explicitly. Without it, the task is too
vague to implement.

**Issue 8: Rademacher is likely too large for this project.**

If the only locally Lipschitz function used is `g_S`, it is better to prove
directly that it is piecewise absolutely continuous and has the required a.e.
derivative.

Recommendation: move the full Rademacher task to an optional section.

### Lines 78-119: Improper weighted integration by parts

**Issue 9: This task is not needed for the direct counterexample after the optimizer space is defined.**

The integration-by-parts lemma proves the weak identity for `phi'`. The
counterexample proof only uses that `1` and `phi'_S` generate the optimizer
space and that `f_S` is orthogonal to them by parity. For the explicit
potentials, integrability of `phi'_S` can be proved directly from tail formulas.

Recommendation: mark this task as optional unless the formalization includes
Lemma `lem:phi-prime-eigen`.

**Issue 10: The hypotheses are incomplete for the finite-interval integration by parts step.**

Line 88 assumes `h` locally absolutely continuous and `phi` smooth. That is
enough locally, but the statement should also require `exp(-phi)` locally
absolutely continuous and `(exp(-phi))' = -phi' exp(-phi)`, or simply derive it
from `phi` being `C^1`.

Recommendation: include `phi` continuously differentiable, not just smooth in
informal prose.

**Issue 11: The boundary subsequence assumption is stronger than the actual auxiliary lemma.**

The auxiliary lemma at lines 111-114 gives boundary subsequences for
nonnegative integrable functions. To obtain both endpoint vanishings
simultaneously, one applies it separately to the two tails and then pairs the
sequences. This is fine, but should be stated.

Recommendation: add "choose the positive and negative tail sequences
separately."

**Issue 12: The notation `h'` is not Lean-safe.**

For locally absolutely continuous functions, the derivative exists a.e., not
necessarily everywhere. The statement should use an a.e. derivative or a
specified representative.

Recommendation: phrase the theorem using `HasDerivAt` a.e. or an integrable
function `h_deriv` with `h y - h x = ∫_[x,y] h_deriv`.

### Lines 121-150: Smooth compactly supported even probability bump

**Issue 13: Missing boundedness/supremum consequence.**

The paper later uses that `phi''_S` is bounded, via
`||kappa||_infty`. The task lists compact support and smoothness but does not
explicitly include the theorem that a smooth compactly supported function is
bounded and has finite supremum norm.

Recommendation: add the consequence:
`∃ M, ∀ x, |kappa x| <= M`, and preferably `M = sup |kappa|`.

**Issue 14: "support(kappa) ⊆ [-1,1]" needs a precise support convention.**

In Lean, support may mean topological support or function support
`Function.support`. For smooth compact support, topological support is usually
intended. The paper only needs `kappa(x)=0` for `|x|>1`.

Recommendation: state the needed version directly:
`∀ x, |x| > 1 -> kappa x = 0`.

**Issue 15: Integral normalization over all `R` needs integrability.**

The statement says `∫ kappa = 1`, but should include `Integrable kappa` or
derive it from compact support and continuity.

Recommendation: add `Integrable kappa volume`.

### Lines 152-187: Reconstructing a smooth potential

**Issue 16: The notation `phi'` as a defined function is ambiguous.**

Lines 163-165 define `phi'(x)` and `phi(x)`. In Lean, `phi'` is not a separate
name unless explicitly introduced; it also visually conflicts with derivative
notation.

Recommendation: define `psi(x) = ∫_0^x h(t) dt` and
`phi(x) = ∫_0^x psi(u) du`; then prove `deriv phi = psi` and `deriv psi = h`.

**Issue 17: The integral `∫_0^x` must be an oriented interval integral.**

For negative `x`, the paper's formula is an oriented integral. A Lean
formalization should use interval integral notation, not Lebesgue integration
over the unordered set `[0,x]`.

Recommendation: write `∫ t in 0..x, h t`.

**Issue 18: Smoothness from integration is a nontrivial theorem.**

The file says this is a medium task, which is fair, but the precise statement
should include that `h` is smooth on all `R`, and the conclusion should be
`ContDiff R ⊤ phi`.

Recommendation: specify `ContDiff R ⊤ h -> ContDiff R ⊤ phi`.

**Issue 19: Convexity conclusion needs the exact convexity notion.**

Line 178 says `phi` is strictly convex if `h >= eta > 0`. In Lean, strict
convexity may be stated on a convex set. The set here is `univ`.

Recommendation: state `StrictConvexOn R Set.univ phi`.

### Lines 189-230: Gaussian domination and explicit exponential integrals

**Issue 20: The Gaussian domination statement needs measurability.**

Line 206 says if `phi(x) >= eta*x^2/2`, then `∫ exp(-phi) < infinity`.
This also requires measurability of `phi` or of `exp(-phi)`. In the paper,
`phi` is smooth, so this is automatic.

Recommendation: include `phi` measurable/continuous.

**Issue 21: The half-line integral identities need the measure/domain specified.**

Lines 212-217 write `∫_0^∞`. In Lean this can mean an integral over
`Set.Ioi 0` with volume restricted, or an interval integral with infinite
endpoint if available.

Recommendation: state as
`∫ u in Set.Ioi (0:R), exp(-a*u) ∂volume = 1/a` and similarly for `u^2`.

**Issue 22: Product Gaussian normalization is underspecified.**

Lines 219-225 refer to `γ_n` without defining it. For Lean, specify whether
`γ_n` is mathlib's Gaussian measure, a product of one-dimensional standard
normal measures, or the normalized density
`(2π)^(-n/2) exp(-||y||^2/2)`.

Recommendation: define `γ_n` concretely.

**Issue 23: Missing factorization of the unnormalized Gaussian integral.**

The higher-dimensional argument needs the normalized product measure. To prove
that the density proportional to `exp(-phi_S(x)-|y|^2/2)` factors as
`rho_S ⊗ gamma`, one needs the normalization
`∫ exp(-|y|^2/2) dy = (2π)^{n/2}` or an equivalent definition of `gamma`.

Recommendation: add this to the task.

### Lines 232-298: Weighted one-dimensional Dirichlet minimization

**Issue 24: This task is optional, not required.**

Lines 288-298 correctly note that the proof can bypass minimization and prove
the energy identity directly. Since the user asked for big tasks needed for
Lean verification, this should either be removed from the required list or
retitled "optional if preserving the variational explanation."

Recommendation: move this to an optional subsection and make the direct energy
identity the required task.

**Issue 25: The formal statement mixes open intervals and endpoint traces.**

Line 241 defines `I=(a,b)`, while lines 247-252 use functions on `[a,b]` with
endpoint values. In Lean, decide between functions on `R` restricted to
`Set.Icc a b`, functions on `Set.Icc a b`, or Sobolev functions on `Ioo a b`
with traces.

Recommendation: for this paper, avoid Sobolev traces and use absolutely
continuous functions on `Set.Icc a b`.

**Issue 26: Missing assumption `a < b`.**

The interval must be nonempty.

Recommendation: add `a < b`.

**Issue 27: Missing integrability/positivity of `∫ w^{-1}`.**

The bounds `0 < m <= w <= M` on a bounded interval imply this, but the theorem
statement should include or derive
`0 < ∫_a^b w^{-1}`.

Recommendation: include the derived positivity in the precise form.

**Issue 28: Unique minimizer statement requires equality up to a.e. derivative or pointwise function?**

For absolutely continuous functions with fixed endpoint values, if derivatives
agree a.e., then functions agree everywhere. This is another theorem.

Recommendation: state the uniqueness criterion explicitly.

### Lines 300-340: Piecewise-defined test function

**Issue 29: Wrong codomain for `g_S`.**

Line 311 says `g_S : R -> [0,1]`. The paper needs a real-valued function,
because it later defines `f_S = g_S - c_S`. In Lean, a subtype-valued function
would make subtraction awkward and is not the paper's object.

Recommendation: write `g_S : R -> R` plus range theorem `∀x, 0 <= g_S x ∧ g_S x <= 1`.

**Issue 30: The derivative formula is underspecified.**

Line 330 says `g'_S = ± ... / A` on the layers. It should say:

- on `I_S^+`, `g'_S(x)=phi''_S(x) exp(phi_S(x))/A`,
- on `I_S^-`, `g'_S(x)=-phi''_S(x) exp(phi_S(x))/A`,
- outside `I_S^+ ∪ I_S^-`, `g'_S(x)=0`,
- all derivative claims are a.e. or away from the four endpoints.

Recommendation: spell out all three derivative regions and the endpoint
exception.

**Issue 31: Global Lipschitz is optional.**

For the energy computation, it is enough that `g_S` is absolutely continuous on
the finitely many regions with the specified derivative. Global Lipschitz is
only needed to match the paper's admissibility class.

Recommendation: classify global Lipschitz as optional if the formal admissible
class is narrowed.

**Issue 32: Missing denominator positivity.**

The definition divides by
`A = ∫_{I_S^+} phi''_S exp(phi_S)`. One must prove `A > 0`.

Recommendation: add a required lemma:
`A > 0`, from `phi''_S >= eta > 0` and `exp(phi_S)>0` on a nonempty interval.

**Issue 33: Missing continuity at endpoints as a Lean task.**

Continuity is listed, but the precise endpoint values should be included:
`g_S(±(1-eps))=0`, `g_S(±(1+eps))=1`, with the left-layer sign handled by
absolute value.

Recommendation: add these endpoint lemmas.

### Lines 342-383: Product measure and product potential reduction

**Issue 34: The type `R × R^{d-1}` is not a natural Lean target for the theorem over `R^d`.**

The paper writes `R × R^{d-1}` mathematically. In Lean, if the final theorem is
over `EuclideanSpace R (Fin d)`, one needs an explicit linear isometry or
coordinate equivalence between `Fin d -> R` and `R × (Fin (d-1) -> R)` for
`d >= 2`.

Recommendation: add a task for the coordinate equivalence and transport of
all constructions across it, or formulate the theorem directly on product
spaces.

**Issue 35: The normalized density factorization needs constants.**

Line 360 says the density proportional to `exp(-Phi_S)` is
`rho_S ⊗ gamma`. To prove this, Lean needs:

```text
Z_{Phi_S} = Z_S * ∫ exp(-|y|^2/2) dy,
gamma density = (∫ exp(-|y|^2/2) dy)^{-1} exp(-|y|^2/2).
```

Recommendation: include this normalization identity explicitly.

**Issue 36: Hessian/block matrix statements need a matrix representation.**

Lines 362-363 use `diag(phi''_S,I)`. In Lean, Hessians are bilinear maps,
matrices in a basis, or `ContinuousLinearMap`s depending on the differentiability
API.

Recommendation: choose a representation before listing this as a task.

**Issue 37: Optimizer-space equality in products needs coefficient bookkeeping.**

Line 372 says the optimizer space is a span. To prove equality, one must show
that every `a · grad Phi + b` corresponds exactly to coefficients of
`1`, `phi'_S(x)`, and coordinate functions `y_j`.

Recommendation: add the finite-sum/coordinate expansion as a subtask.

### Lines 385-416: Asymptotics library

**Issue 38: The listed asymptotic lemmas are not sufficient.**

The paper also uses:

- `exp(O(S^{-2})) = 1 + O(S^{-2})` for small nonnegative exponents,
- products like `(1+O(S^{-2}))(S^{-1}+O(S^{-6}))`,
- eventual positivity of denominators,
- conversion from `S^{-2}+O(S^{-3})` to `S^{-2}(1+O(S^{-1}))`,
- square-root asymptotics for the final "constant blows up like sqrt S" claim,
- estimates involving `eps=S^{-3}` and `eta=S^{-4}` inside integrals.

Recommendation: expand the asymptotics task or say it is only a sample list.

**Issue 39: The first two displayed equalities are algebra, not asymptotics.**

Lines 402-403 list exact algebraic equalities involving powers of `S`. These
are not big tasks, though normalization of real powers can be annoying.

Recommendation: separate "power-normalization simp lemmas" from actual `O`
arithmetic.

**Issue 40: Need specify the parameter type.**

Line 399 says "real `S -> infinity`". The construction uses real `S`, but many
formalizations prefer a sequence `S : Nat -> R`, e.g. `S_n = n+1`. If using
real filters, every statement needs eventual assumptions `S >= 1` and
`S` nonzero for powers.

Recommendation: choose either real-filter `atTop` on `R` with eventual
positivity or a natural sequence version.

### Lines 418-430: Explicitly omitted section

**Issue 41: Essential continuity omission is correct only for the proof, not for the full statement paragraph.**

The omission at lines 428-430 is fine for verifying the constructed smooth
counterexample. It is not fine if formalizing the entire introductory statement
exactly as written, because the statement begins with essentially continuous
convex functions.

Recommendation: say "omitted for the formalization of the counterexample
theorem; needed only if formalizing the broad introductory setup verbatim."

**Issue 42: Affine-invariance omission is correct.**

No issue. The affine/Poincare remark is explanatory and not used.

## Missing Big Tasks

### Missing Task A: Exact definition of the formal Brascamp--Lieb deficit for the constructed class

The file never explicitly says that one must define, in Lean, the concrete
one-dimensional energy and deficit used in the proof:

```text
E_phi(f) = ∫ (f')^2 / phi'' d rho_phi,
delta_phi(f) = E_phi(f) - Var_rho_phi(f).
```

This definition must handle the fact that `f_S` is only piecewise differentiable
and its derivative is an a.e. object.

### Missing Task B: Explicit formulas for `phi_S`, `phi'_S`, and `phi''_S` on all regions

The file has reconstruction and bump tasks, but it does not list the extensive
case-splitting needed to prove:

- `phi''_S=eta` on the plateau and exterior,
- `phi'_S=eta x` on the central plateau,
- `phi'_S=eta x + S` on the right exterior,
- the symmetric left exterior formula,
- the corresponding formula for `phi_S` on the right exterior,
- uniform smallness of `phi_S` on the transition layers.

These are not deep, but they will be substantial Lean work because of supports,
interval membership, and endpoint inequalities.

### Missing Task C: Positivity and finiteness of all normalizing constants and denominators

Lean will require explicit proofs of:

- `Z_S > 0`,
- `Z_S < infinity`,
- `A_S = ∫_{I_S^+} phi''_S exp(phi_S) > 0`,
- `A_S < infinity`,
- `phi''_S(x) > 0` for all `x`,
- denominators appearing in ratios are eventually nonzero.

These should be a separate task because they occur throughout the proof.

### Missing Task D: Parity package for the constructed functions and measure

The proof relies heavily on:

- `phi_S` even,
- `phi'_S` odd,
- `rho_S` has even density,
- `g_S` and `f_S` are even,
- the integral of an odd integrable function against an even density is zero.

Some pieces are listed, but the integrated parity package is not identified as
a task. In Lean this will be a recurring source of proof obligations.

### Missing Task E: Distance to finite-dimensional optimizer spaces

The file lists finite-dimensional subspace facts in dependencies, but does not
include them as a big task. For Lean, this may be easy if Hilbert-space
orthogonality infrastructure is available, but it still requires setting up:

- the optimizer space as a submodule/subspace of `L^2`,
- the generators as `L^2` elements,
- orthogonality to each generator,
- `dist(f, M)^2 = ||f||^2`.

This is not as large as the analysis tasks, but it is big enough to list as a
Lean integration task.

## Recommended Rewrite of `big_tasks.md`

I would restructure the file into:

1. **Required for the direct counterexample proof**
   - Construct smooth bump and potential.
   - Prove region formulas and normalizing constants.
   - Define the concrete energy/deficit for piecewise absolutely continuous
     functions.
   - Construct `g_S`, prove derivative/range/parity.
   - Compute energy and variance.
   - Prove orthogonality/distance to finite-dimensional optimizer space.
   - Handle product extension to higher dimensions.
   - Handle asymptotic algebra.

2. **Optional if formalizing the paper verbatim**
   - Brascamp--Lieb inequality and equality cases.
   - General locally Lipschitz/Rademacher infrastructure.
   - Weak `phi'` integration-by-parts lemma.
   - Weighted Dirichlet minimization theorem.

3. **Omitted contextual/historical**
   - `L^1` stability theorem.
   - Spectral closed-form/operator theory.
   - Affine/Poincare remark.

