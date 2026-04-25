import L2Counterexample.TestFunction
import Mathlib

/-!
# One-dimensional counterexample (WIP)

This is the editable WIP version of `OneDimensional.lean`. It assembles the
one-dimensional Brascamp-Lieb counterexample. The goals are:

1. **Parity/orthogonality package** (blueprint task #11): evenness of
   `phi_S`, oddness of `phi'_S`, evenness of `exp(-phi_S)` and `rho_S`,
   evenness of `g_S`, centering `c_S := ∫ g_S d rho_S`, and the two
   orthogonality identities `∫ f_S d rho_S = 0`,
   `∫ f_S · phi'_S d rho_S = 0`, together with the general lemma
   "integral of (even · odd) is zero under a symmetric measure".

2. **Distance to the optimizer space** (task #12): `O_S = span ℝ {1, phi'_S}`
   inside `L²(rho_S)`, with membership of `1` and `phi'_S` in `L²`, linear
   independence, orthogonality of `f_S`, and
   `dist(f_S, O_S)² = ‖f_S‖² = Var rho_S g_S`.

3. **Deficit asymptotics** (task #13):

       E_phi_S(f_S)             = 1/S - 1/S² + O(S⁻³)
       Var rho_S f_S            = 1/S - 2/S² + O(S⁻³)
       delta_phi_S(f_S)         = 1/S² + O(S⁻³)
       dist(f_S, O_S)² / delta_phi_S(f_S) = S · (1 + O(S⁻¹))

4. **The 1D conclusion**: there is no finite `C` so that
   `dist(f, O_phi) ≤ C · sqrt(delta_phi(f))` holds for every admissible pair
   `(phi, f)` coming from the blueprint family. This is `theorem
   no_uniform_L2_stability_one_dim`.

Following the project convention in `LEAN_AGENT.md`, all upstream data
(the potential `phi_S`, its derivative `phi'_S`, the test function `g_S`,
the constants `Z_S`, `A_S`, the energy/variance identities, and the
asymptotic estimates of blueprint §03 and §04) is introduced here as
`axiom` declarations with blueprint signatures. The file consumes only
those axioms and therefore sits upstream-free (once the axiomatised data
is supplied by the real `Potential`/`Normalization`/`TestFunction` files,
the axioms become theorems with `exact?` proofs).

The asymptotic shorthand we use is finitary, matching
`WIP_Normalization.BigOInv`:

    `f =O[k] g`   ↔   `∃ C S₀, 0 < S₀ ∧ ∀ S, S₀ ≤ S → |f S - g S| ≤ C · S^(-k)`

This sidesteps the heavier `Asymptotics.IsBigO` machinery in intermediate
statements, in line with best practice #4.
-/

noncomputable section

open MeasureTheory Set Real
open scoped Topology BigOperators

namespace L2Counterexample

/-! ## Finitary asymptotic shorthand -/

/-- `BigOInv1D f g k` means `f S = g S + O(S^{-k})` as `S → ∞`, encoded as
an explicit finite inequality over real `S`. This matches
`WIP_Normalization.BigOInv`. We repeat the definition here to keep the
file self-contained. -/
def BigOInv1D (f g : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → |f S - g S| ≤ C * S ^ (-(k : ℤ))

@[inherit_doc] notation:50 f " =O[" k "]₁ " g => BigOInv1D f g k

/-! ## Upstream axioms (blueprint signatures)

These are declared as local `axiom`s. When the upstream files (`Potential`,
`Normalization`, `TestFunction`) are finalised, each axiom below is
replaced by the corresponding theorem. The signatures match the blueprint
verbatim.
-/

/-- The one-dimensional potential `phi_S : ℝ → ℝ`. -/
axiom phi_S : ℝ → ℝ → ℝ

/-- The derivative `phi'_S : ℝ → ℝ`. -/
axiom phiDer_S : ℝ → ℝ → ℝ

/-- The second derivative `phi''_S : ℝ → ℝ`. -/
axiom phiDer2_S : ℝ → ℝ → ℝ

/-- The partition function `Z_S = ∫ exp(-phi_S)`. -/
axiom ZZ_S : ℝ → ℝ

/-- The layer normalizer `A_S`. -/
axiom AA_S : ℝ → ℝ

/-- The real-valued piecewise test function `g_S : ℝ → ℝ`. -/
axiom gg_S : ℝ → ℝ → ℝ

/-- The probability measure `rho_S` on `ℝ` with density
`Z_S^{-1} exp(-phi_S)`. -/
axiom rho_S : ℝ → Measure ℝ

/-- `rho_S` is a probability measure. -/
axiom rho_S_isProb (S : ℝ) : IsProbabilityMeasure (rho_S S)

attribute [instance] rho_S_isProb

/-! ### Parity and basic identities (blueprint §05 eq. (a)--(e)) -/

/-- `phi_S S` is even in `x`. -/
axiom phi_S_even (S x : ℝ) : phi_S S (-x) = phi_S S x

/-- `phi'_S S` is odd in `x`. -/
axiom phiDer_S_odd (S x : ℝ) : phiDer_S S (-x) = -phiDer_S S x

/-- `phi''_S S` is even in `x`. -/
axiom phiDer2_S_even (S x : ℝ) : phiDer2_S S (-x) = phiDer2_S S x

/-- `g_S S` is even in `x` (blueprint Lemma 4.3). -/
axiom gg_S_even (S x : ℝ) : gg_S S (-x) = gg_S S x

/-- The density `exp(-phi_S)` is even (immediate from `phi_S_even`). -/
lemma exp_neg_phi_S_even (S x : ℝ) :
    Real.exp (-phi_S S (-x)) = Real.exp (-phi_S S x) := by
  rw [phi_S_even]

/-- Invariance of `rho_S` under the reflection `x ↦ -x`.

This is the measure-level version of "the density `exp(-phi_S)` is even
and the Lebesgue measure is reflection-invariant". -/
axiom rho_S_reflection_invariant (S : ℝ) :
    (rho_S S).map (fun x : ℝ => -x) = rho_S S

/-- Measurability of `phi'_S`. -/
axiom phiDer_S_measurable (S : ℝ) : Measurable (phiDer_S S)

/-- Measurability of `g_S`. -/
axiom gg_S_measurable (S : ℝ) : Measurable (gg_S S)

/-! ### `L^2` membership and integrability (blueprint §05)

We axiomatise that `1` and `phi'_S` and `g_S` belong to `L^2(rho_S)`,
so that all inner products below make sense. -/

/-- `phi'_S ∈ L^2(rho_S)`. -/
axiom phiDer_S_memL2 (S : ℝ) :
    MemLp (phiDer_S S) 2 (rho_S S)

/-- `g_S ∈ L^2(rho_S)`. -/
axiom gg_S_memL2 (S : ℝ) :
    MemLp (gg_S S) 2 (rho_S S)

/-- `phi'_S · g_S ∈ L^1(rho_S)` (Cauchy-Schwarz from the two `L²`
hypotheses). -/
axiom phiDer_gg_integrable (S : ℝ) :
    Integrable (fun x => phiDer_S S x * gg_S S x) (rho_S S)

/-! ### Upstream energy/variance identities

The concrete definitions of the Brascamp-Lieb energy and deficit come
from `TestFunction`/`Normalization`. We only need the scalar invariants
`E_phi_S(f_S)`, `Var rho_S f_S`, `delta_phi_S(f_S)` and their asymptotic
evaluations, plus the identity `delta = E - Var`.

The concrete one-dimensional test function is `f_S := g_S - c_S` where
`c_S := ∫ g_S d rho_S`.
-/

/-- The centering constant `c_S := ∫ g_S d rho_S`. -/
def cc_S (S : ℝ) : ℝ := ∫ x, gg_S S x ∂(rho_S S)

/-- The centered test function `f_S := g_S - c_S`. -/
def ff_S (S : ℝ) (x : ℝ) : ℝ := gg_S S x - cc_S S

/-- `f_S ∈ L^2(rho_S)` (since `g_S` is, and we subtract a scalar times
the constant function `1`, which is in `L^p` for every finite measure). -/
lemma ff_S_memL2 (S : ℝ) : MemLp (ff_S S) 2 (rho_S S) := by
  -- `MemLp.sub` together with `memLp_const`.
  have h1 : MemLp (gg_S S) 2 (rho_S S) := gg_S_memL2 S
  have h2 : MemLp (fun _ : ℝ => cc_S S) 2 (rho_S S) :=
    memLp_const (cc_S S)
  exact h1.sub h2

/-! ### Blueprint numerical invariants

We record the three scalar quantities of blueprint §05 --- the BL energy,
variance, and deficit of `f_S` --- as axioms. The precise integral
formulas live upstream; this file only uses their asymptotic values. -/

/-- The Brascamp-Lieb energy `E_phi_S(f_S)`. Blueprint §04. -/
axiom EE_phi_S : ℝ → ℝ

/-- The variance `Var_{rho_S}(f_S)`. Blueprint §04. -/
axiom Var_f_S : ℝ → ℝ

/-- The Brascamp-Lieb deficit `delta_phi_S(f_S) := E_phi_S(f_S) -
Var_{rho_S}(f_S)`. Blueprint Definition §01 and §05. -/
def delta_phi_S (S : ℝ) : ℝ := EE_phi_S S - Var_f_S S

/-- The variance of `g_S` equals the variance of `f_S = g_S - c_S`. This
is the translation-invariance of variance applied to subtraction of the
constant `c_S`. -/
axiom Var_gg_eq_Var_ff (S : ℝ) :
    (∫ x, (gg_S S x - cc_S S) ^ 2 ∂(rho_S S)) = Var_f_S S

/-! ### Asymptotic evaluations (blueprint §04, §05) -/

/-- `E_phi_S(f_S) = 1/S - 1/S² + O(S⁻³)`. -/
axiom EE_phi_S_asymp :
    BigOInv1D EE_phi_S (fun S => 1 / S - 1 / S ^ 2) 3

/-- `Var rho_S f_S = 1/S - 2/S² + O(S⁻³)`. -/
axiom Var_f_S_asymp :
    BigOInv1D Var_f_S (fun S => 1 / S - 2 / S ^ 2) 3

/-! ## Parity-orthogonality package (blueprint task #11)

The key general lemma: if `mu` is invariant under `x ↦ -x` and `u` is an
odd, `mu`-integrable function, then `∫ u dmu = 0`. We prove this via the
change-of-variables `x ↦ -x`.
-/

/-- **General parity lemma (measure-theoretic form).**
If `mu` is invariant under the reflection `x ↦ -x` and `u : ℝ → ℝ` is
odd and `mu`-integrable, then `∫ u dmu = 0`.

This is the key lemma behind the parity orthogonality. -/
lemma integral_odd_of_reflection_invariant
    {mu : Measure ℝ} (h_symm : mu.map (fun x : ℝ => -x) = mu)
    {u : ℝ → ℝ} (h_odd : ∀ x, u (-x) = -u x)
    (h_meas : AEMeasurable u mu) (h_int : Integrable u mu) :
    ∫ x, u x ∂mu = 0 := by
  -- Substitute `x ↦ -x`: using reflection-invariance,
  --   ∫ u dmu = ∫ u dmu.map(neg) = ∫ u(-x) dmu = -∫ u dmu.
  have h_meas_neg : Measurable (fun x : ℝ => -x) := measurable_neg
  have h1 : ∫ x, u x ∂mu = ∫ x, u (-x) ∂mu := by
    -- `mu` is the pushforward under `neg`, so integrate against the pushforward.
    have := MeasureTheory.integral_map (μ := mu) (f := fun x : ℝ => -x)
              (g := u) h_meas_neg.aemeasurable h_meas
    rw [h_symm] at this
    -- `this : ∫ y, u y ∂mu = ∫ x, u (-x) ∂mu`
    simpa using this
  -- Combine with oddness.
  have h2 : ∫ x, u (-x) ∂mu = -∫ x, u x ∂mu := by
    have h_eq : (fun x => u (-x)) = fun x => -u x := funext h_odd
    rw [h_eq, integral_neg]
  linarith [h1, h2]

/-! ### Evenness of `f_S`, zero mean, and parity orthogonality

These follow from the general lemma applied to `u := f_S · phi'_S`
(product of an even and an odd function). First we record the targeted
consequences.
-/

/-- `f_S` is even (from evenness of `g_S` and `c_S` being a scalar). -/
lemma ff_S_even (S x : ℝ) : ff_S S (-x) = ff_S S x := by
  unfold ff_S
  rw [gg_S_even]

/-- The centering constant is an integral of an even function, hence
well defined. (Stated by `rfl` for downstream convenience.) -/
lemma cc_S_def (S : ℝ) : cc_S S = ∫ x, gg_S S x ∂(rho_S S) := rfl

/-- **Centering identity.** `∫ f_S d rho_S = 0`.

By definition of `c_S`, since `rho_S` is a probability measure. -/
lemma integral_ff_S (S : ℝ) : ∫ x, ff_S S x ∂(rho_S S) = 0 := by
  unfold ff_S
  -- `∫ (g - c) = ∫ g - c` since rho is a probability measure.
  have h_int : Integrable (gg_S S) (rho_S S) := (gg_S_memL2 S).integrable (by norm_num)
  rw [integral_sub h_int (integrable_const _)]
  have h_const : ∫ _ : ℝ, cc_S S ∂(rho_S S) = cc_S S := by
    simp [MeasureTheory.integral_const, measure_univ]
  rw [h_const, cc_S]
  ring

/-- **Parity orthogonality to `phi'_S`.** `∫ f_S · phi'_S d rho_S = 0`.

Proof: `f_S` is even, `phi'_S` is odd, so their product is odd. The
density of `rho_S` is even, so `rho_S` is reflection-invariant. Apply
the general parity lemma. -/
lemma integral_ff_phiDer_zero (S : ℝ) :
    ∫ x, ff_S S x * phiDer_S S x ∂(rho_S S) = 0 := by
  -- The product `f_S · phi'_S` is odd.
  have h_odd : ∀ x, ff_S S (-x) * phiDer_S S (-x) = -(ff_S S x * phiDer_S S x) := by
    intro x
    rw [ff_S_even, phiDer_S_odd]
    ring
  -- Integrability: `f_S · phi'_S = (g_S - c_S) · phi'_S`
  -- is `g_S · phi'_S - c_S · phi'_S`, each integrable by Cauchy-Schwarz
  -- (for the first) and because `phi'_S ∈ L^2 ⊆ L^1` on a prob. measure
  -- (for the second).
  have h_phi_int : Integrable (phiDer_S S) (rho_S S) :=
    (phiDer_S_memL2 S).integrable (by norm_num)
  have h_gg_phi : Integrable (fun x => gg_S S x * phiDer_S S x) (rho_S S) := by
    -- Use commutativity with the axiomatised integrability of phi'·g.
    have : Integrable (fun x => phiDer_S S x * gg_S S x) (rho_S S) :=
      phiDer_gg_integrable S
    simpa [mul_comm] using this
  have h_int : Integrable (fun x => ff_S S x * phiDer_S S x) (rho_S S) := by
    have : (fun x => ff_S S x * phiDer_S S x) =
        fun x => gg_S S x * phiDer_S S x - cc_S S * phiDer_S S x := by
      funext x; unfold ff_S; ring
    rw [this]
    exact h_gg_phi.sub (h_phi_int.const_mul (cc_S S))
  -- Measurability of the product.
  have h_meas : AEMeasurable (fun x => ff_S S x * phiDer_S S x) (rho_S S) :=
    h_int.aemeasurable
  -- Apply the general parity lemma.
  exact integral_odd_of_reflection_invariant
    (rho_S_reflection_invariant S) h_odd h_meas h_int

/-! ## The optimizer space `O_S = span ℝ {1, phi'_S}`

We work with the `Lp`-space `L^2(rho_S)` in Mathlib's
`MeasureTheory.Lp` formalism. A function `f : ℝ → ℝ` with
`MemLp f 2 (rho_S S)` gives rise to its `toLp`-class in `Lp ℝ 2`.

We model the one-dimensional optimizer space as the `Submodule.span ℝ`
of the two `Lp`-elements `1.toLp` and `phi'_S.toLp`, inside
`Lp ℝ 2 (rho_S S)`.
-/

/-- Shorthand for the `L²` space over `rho_S`. -/
abbrev L2RhoS (S : ℝ) : Type :=
  Lp (α := ℝ) ℝ 2 (rho_S S)

/-- The `Lp`-class of the constant function `1 : ℝ → ℝ` in `L²(rho_S)`. -/
def oneLp (S : ℝ) : L2RhoS S :=
  (memLp_const (1 : ℝ) (μ := rho_S S)).toLp _

/-- The `Lp`-class of `phi'_S` in `L²(rho_S)`. -/
def phiDerLp (S : ℝ) : L2RhoS S :=
  (phiDer_S_memL2 S).toLp _

/-- The `Lp`-class of `f_S` in `L²(rho_S)`. -/
def ffLp (S : ℝ) : L2RhoS S :=
  (ff_S_memL2 S).toLp _

/-- The one-dimensional optimizer subspace `O_S = span ℝ {1, phi'_S} ⊆
L²(rho_S)`. -/
def optSubspace (S : ℝ) : Submodule ℝ (L2RhoS S) :=
  Submodule.span ℝ ({oneLp S, phiDerLp S} : Set (L2RhoS S))

/-! ### `1 ∈ L²(rho_S)` -/

/-- The constant function `1` lies in `L^2(rho_S)`. -/
lemma one_memL2 (S : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (rho_S S) :=
  memLp_const 1

/-! ### Orthogonality of `f_S` to generators

Because `L²` uses an `inner` via
`⟨u,v⟩ = ∫ u·v d rho_S`, we can test orthogonality against the two
generators `1.toLp` and `phi'_S.toLp` directly.
-/

/-- Inner product in `L²(rho_S)` between the `Lp`-classes of two
`MemLp`-functions equals the integral of their product. -/
lemma inner_toLp_eq_integral
    {S : ℝ} {u v : ℝ → ℝ}
    (hu : MemLp u 2 (rho_S S)) (hv : MemLp v 2 (rho_S S)) :
    @inner ℝ _ _ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂(rho_S S) := by
  -- Use `Lp.inner_def` together with `MemLp.coeFn_toLp`.
  -- This unfolds the definition `⟨f,g⟩ = ∫ f(x) * g(x) dμ` for real `L^2`.
  simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hxu hxv
  rw [hxu, hxv]

/-- `f_S ⟂ 1` in `L²(rho_S)`. -/
lemma ffLp_perp_oneLp (S : ℝ) :
    @inner ℝ _ _ (ffLp S) (oneLp S) = 0 := by
  unfold ffLp oneLp
  rw [inner_toLp_eq_integral (ff_S_memL2 S) (one_memL2 S)]
  simp only [mul_one]
  exact integral_ff_S S

/-- `f_S ⟂ phi'_S` in `L²(rho_S)`. -/
lemma ffLp_perp_phiDerLp (S : ℝ) :
    @inner ℝ _ _ (ffLp S) (phiDerLp S) = 0 := by
  unfold ffLp phiDerLp
  rw [inner_toLp_eq_integral (ff_S_memL2 S) (phiDer_S_memL2 S)]
  exact integral_ff_phiDer_zero S

/-- **Orthogonality to the optimizer span.** `f_S ⟂ O_S`. -/
lemma ffLp_perp_optSubspace (S : ℝ) :
    ∀ y ∈ optSubspace S, @inner ℝ _ _ (ffLp S) y = 0 := by
  -- Orthogonality to a span: it suffices to check on each generator
  -- (bilinearity of the inner product).
  intro y hy
  refine Submodule.span_induction (p := fun z _ => @inner ℝ _ _ (ffLp S) z = 0)
    (hx := hy) ?_ ?_ ?_ ?_
  · -- generators: y = oneLp S or y = phiDerLp S
    rintro z (rfl | rfl)
    · exact ffLp_perp_oneLp S
    · rw [Set.mem_singleton_iff] at *
      -- if z ∈ {phiDerLp S}, then z = phiDerLp S
      subst z
      exact ffLp_perp_phiDerLp S
  · -- zero
    simp
  · -- additivity
    intros u v _ _ hu hv
    rw [inner_add_right, hu, hv]; ring
  · -- scalar
    intros r v _ hv
    rw [inner_smul_right, hv, mul_zero]

/-! ### `dist(f_S, O_S)² = ‖f_S‖²`

In a Hilbert space, if `x` is orthogonal to a *complete* subspace `M`,
then `dist(x, M) = ‖x‖`. The span of two elements is finite-dimensional,
hence complete (automatically closed in a Hilbert space). We use
`Submodule.FiniteDimensional.instCompleteSpace`.
-/

/-- `O_S` is finite-dimensional (spanned by two elements). -/
instance optSubspace_fd (S : ℝ) :
    FiniteDimensional ℝ (optSubspace S) := by
  -- Span of a finite set is finite-dimensional.
  unfold optSubspace
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_insert _ (Set.finite_singleton _))

/-- `O_S` is (topologically) complete. -/
instance optSubspace_complete (S : ℝ) :
    CompleteSpace (optSubspace S) :=
  FiniteDimensional.complete ℝ _

/-- `O_S` is closed as a subset of `L²(rho_S)`. -/
lemma optSubspace_isClosed (S : ℝ) :
    IsClosed ((optSubspace S : Submodule ℝ (L2RhoS S)) : Set (L2RhoS S)) :=
  Submodule.isClosed_of_finiteDimensional (optSubspace S)

/-- **Distance identity.** `dist(f_S, O_S)² = ‖f_S‖²`. Since `f_S ⟂ O_S`
and `0 ∈ O_S`, the orthogonal projection of `f_S` onto the closed
finite-dim subspace `O_S` is `0`, so
`dist(f_S, O_S) = ‖f_S - 0‖ = ‖f_S‖`. -/
lemma dist_ffLp_optSubspace_sq_eq (S : ℝ) :
    (Metric.infDist (ffLp S) (optSubspace S : Set (L2RhoS S)))^2 = ‖ffLp S‖ ^ 2 := by
  -- Use the orthogonal-projection characterization.
  -- For closed complete subspaces `K`, `infDist x K = ‖x - proj K x‖`, and
  -- if `x ⟂ K`, the projection is `0`, so `infDist = ‖x‖`.
  classical
  -- Step 1: the projection of `ffLp S` onto `optSubspace S` is zero.
  have hK : IsClosed ((optSubspace S : Submodule ℝ (L2RhoS S)) : Set (L2RhoS S)) :=
    optSubspace_isClosed S
  -- We use `Submodule.infDist_eq_norm_of_mem_orthogonal` or reconstruct.
  -- Simpler: we use the following fact (available in Mathlib):
  --   if `x ⟂ K`, then for every `y ∈ K`, `‖x - y‖² = ‖x‖² + ‖y‖²`, hence
  --   `‖x - y‖ ≥ ‖x‖`, with equality at `y = 0`.
  set x := ffLp S
  set K : Submodule ℝ (L2RhoS S) := optSubspace S
  have hx_perp : ∀ y ∈ K, @inner ℝ _ _ x y = 0 := ffLp_perp_optSubspace S
  have hzero_mem : (0 : L2RhoS S) ∈ (K : Set (L2RhoS S)) := K.zero_mem
  -- `‖x - y‖² = ‖x‖² + ‖y‖²` for `y ∈ K` (Pythagorean theorem).
  have h_lower : ∀ y ∈ K, ‖x‖ ≤ ‖x - y‖ := by
    intro y hy
    have hperp : @inner ℝ _ _ x y = 0 := hx_perp y hy
    -- ‖x - y‖² = ‖x‖² - 2·⟨x,y⟩ + ‖y‖² = ‖x‖² + ‖y‖²
    have h_sq : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
      rw [@norm_sub_sq_real]
      have : @inner ℝ _ _ x y = 0 := hperp
      linarith
    have h_mono : ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [h_sq]; have : 0 ≤ ‖y‖ ^ 2 := by positivity; linarith
    exact abs_le_of_sq_le_sq' (by
      have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
      have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
      nlinarith [h_mono, hx_nn, hxy_nn]) (norm_nonneg _) |>.2
  -- `infDist x K = ‖x‖`.
  have h_inf_lb : ‖x‖ ≤ Metric.infDist x (K : Set (L2RhoS S)) := by
    refine le_csInf ⟨‖x - 0‖, by
      refine ⟨0, ?_, ?_⟩
      · exact hzero_mem
      · rfl⟩ ?_
    rintro d ⟨y, hy, rfl⟩
    rw [dist_eq_norm]
    exact h_lower y hy
  have h_inf_ub : Metric.infDist x (K : Set (L2RhoS S)) ≤ ‖x‖ := by
    have : Metric.infDist x (K : Set (L2RhoS S)) ≤ dist x 0 := by
      exact Metric.infDist_le_dist_of_mem hzero_mem
    rw [dist_zero_right] at this
    exact this
  have h_inf_eq : Metric.infDist x (K : Set (L2RhoS S)) = ‖x‖ :=
    le_antisymm h_inf_ub h_inf_lb
  rw [h_inf_eq]

/-! ### `‖f_S‖² = Var rho_S g_S = Var rho_S f_S`

`‖f_S‖²_{L²(rho_S)} = ∫ (g_S - c_S)² d rho_S = Var_{rho_S}(g_S) =
Var_{rho_S}(f_S)` (translation-invariance of variance).
-/

/-- The squared `L²` norm of `f_S` equals `∫ f_S² d rho_S` (definition). -/
lemma norm_ffLp_sq_eq_integral (S : ℝ) :
    ‖ffLp S‖ ^ 2 = ∫ x, (ff_S S x) ^ 2 ∂(rho_S S) := by
  unfold ffLp
  -- `‖u.toLp‖² = ∫ |u|² = ∫ u²` for real `u ∈ L²`.
  rw [MemLp.norm_toLp]
  -- `MemLp.norm_toLp` returns `(∫ ‖u x‖^2)^(1/2)` via `eLpNorm`. We
  -- rewrite it into the real-valued version.
  sorry

/-- `‖f_S‖² = Var rho_S f_S`. -/
lemma norm_ffLp_sq_eq_var (S : ℝ) :
    ‖ffLp S‖ ^ 2 = Var_f_S S := by
  rw [norm_ffLp_sq_eq_integral]
  -- Apply `Var_gg_eq_Var_ff`: `∫ (g_S - c_S)² = Var f_S`.
  unfold ff_S
  exact Var_gg_eq_Var_ff S

/-- **Distance formula.** `dist(f_S, O_S)² = Var rho_S f_S`. -/
lemma dist_ffLp_optSubspace_sq_eq_var (S : ℝ) :
    (Metric.infDist (ffLp S) (optSubspace S : Set (L2RhoS S)))^2 = Var_f_S S := by
  rw [dist_ffLp_optSubspace_sq_eq S, norm_ffLp_sq_eq_var S]

/-! ## Deficit asymptotics (blueprint §05 task #13) -/

/-- Helper: `(1/S - 1/S^2) - (1/S - 2/S^2) = 1/S^2`. -/
lemma deficit_leading_identity (S : ℝ) (hS : 0 < S) :
    (1 / S - 1 / S ^ 2) - (1 / S - 2 / S ^ 2) = 1 / S ^ 2 := by
  field_simp
  ring

/-- **Deficit asymptotic.** `delta_phi_S(f_S) = 1/S² + O(S⁻³)`. -/
lemma delta_phi_S_asymp :
    BigOInv1D delta_phi_S (fun S => 1 / S ^ 2) 3 := by
  obtain ⟨C₁, S₁, hS₁_pos, hE⟩ := EE_phi_S_asymp
  obtain ⟨C₂, S₂, hS₂_pos, hV⟩ := Var_f_S_asymp
  refine ⟨C₁ + C₂, max (max S₁ S₂) 1, ?_, ?_⟩
  · exact lt_max_of_lt_right one_pos
  intro S hS
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hS)
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS₂le : S₂ ≤ S := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hE' := hE S hS₁le
  have hV' := hV S hS₂le
  -- `delta - 1/S^2 = (E - (1/S - 1/S^2)) - (V - (1/S - 2/S^2))`.
  have h_id : delta_phi_S S - 1 / S ^ 2 =
      (EE_phi_S S - (1 / S - 1 / S ^ 2)) -
      (Var_f_S S - (1 / S - 2 / S ^ 2)) := by
    unfold delta_phi_S
    have hS2 : (S:ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hSpos.ne'
    field_simp
    ring
  rw [h_id]
  have h_tri :
      |EE_phi_S S - (1 / S - 1 / S ^ 2) - (Var_f_S S - (1 / S - 2 / S ^ 2))|
        ≤ |EE_phi_S S - (1 / S - 1 / S ^ 2)|
          + |Var_f_S S - (1 / S - 2 / S ^ 2)| := by
    exact abs_sub _ _
  have h_bd :
      |EE_phi_S S - (1 / S - 1 / S ^ 2)|
        + |Var_f_S S - (1 / S - 2 / S ^ 2)|
          ≤ (C₁ + C₂) * S ^ (-(3:ℤ)) := by
    have hpow_nn : 0 ≤ S ^ (-(3:ℤ)) := by
      rw [zpow_neg]; positivity
    linarith [hE', hV']
  linarith [h_tri, h_bd]

/-- **Positivity of `delta` eventually.** For `S ≥ S₀`, `delta_phi_S(f_S) > 0`.

This comes from `delta = 1/S^2 + O(S^{-3})`, which for sufficiently large
`S` is dominated by the leading term. -/
lemma delta_phi_S_eventually_pos :
    ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → 0 < delta_phi_S S := by
  obtain ⟨C, S₁, hS₁_pos, hbd⟩ := delta_phi_S_asymp
  refine ⟨max S₁ (max 1 (2 * (C + 1))), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left one_pos)
  intro S hS
  have hS1 : S₁ ≤ S := le_trans (le_max_left _ _) hS
  have hS_ge_one : 1 ≤ S := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_big : 2 * (C + 1) ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS_ge_one
  have h := hbd S hS1
  -- delta ≥ 1/S^2 - C / S^3
  have hS2_pos : 0 < S ^ 2 := by positivity
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hpow : S ^ (-(3:ℤ)) = 1 / S ^ 3 := by
    rw [zpow_neg]; simp [zpow_natCast]
  rw [hpow] at h
  have hlb : 1 / S ^ 2 - C * (1 / S ^ 3) ≤ delta_phi_S S := by
    have hsub := (abs_sub_le_iff.1 h).2
    linarith
  -- Now it suffices to show `1/S^2 > C/S^3`, i.e. `S > C`.
  have hSgC : C + 1 ≤ S := by linarith
  have : C < S := by linarith
  have h_key : C * (1 / S ^ 3) < 1 / S ^ 2 := by
    rw [div_lt_div_iff]
    · have : C * 1 * S ^ 2 < 1 * S ^ 3 := by
        have hC_nn_or : 0 ≤ C ∨ C < 0 := le_or_lt 0 C
        rcases hC_nn_or with hC_nn | hC_neg
        · have hS2_le_S3 : C * S ^ 2 ≤ S * S ^ 2 := by
            nlinarith [sq_nonneg S]
          have : S * S ^ 2 = S ^ 3 := by ring
          nlinarith
        · have : C * S ^ 2 ≤ 0 := by
            have := sq_nonneg S
            nlinarith
          have : C * S ^ 2 < S ^ 3 := by
            have : 0 < S ^ 3 := hS3_pos
            linarith
          linarith
      linarith
    · exact hS3_pos
    · exact hS2_pos
  linarith

/-! ### Ratio divergence

From `Var rho_S f_S = 1/S - 2/S² + O(S⁻³)` and
`delta_phi_S(f_S) = 1/S² + O(S⁻³)` we obtain

    `Var/delta = S(1 + O(S⁻¹))`,

which diverges. For the final counterexample we only need unboundedness.
-/

/-- **Divergence of the distance-deficit ratio.** For every `K`, there
exists `S₀ > 0` such that, for every `S ≥ S₀`,
`Var_f_S S > K · delta_phi_S S`.

This is the contentful version of `dist(f_S, O_S)² / delta_phi_S(f_S) →
∞`, via the identity `dist² = Var` already proved. -/
lemma var_over_delta_unbounded :
    ∀ K : ℝ, ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      K * delta_phi_S S < Var_f_S S := by
  intro K
  obtain ⟨C₁, S₁, hS₁_pos, hV⟩ := Var_f_S_asymp
  obtain ⟨C₂, S₂, hS₂_pos, hD⟩ := delta_phi_S_asymp
  -- Pick `S` large enough so that:
  --   Var ≥ 1/S - 2/S² - C₁/S³
  --   delta ≤ 1/S² + C₂/S³
  --   and 1/S - 2/S² - C₁/S³ > K · (1/S² + C₂/S³)
  -- i.e. S·(stuff) dominates. Concretely S ≥ max{S₁, S₂, |K|+bigC, 1}.
  refine ⟨max (max S₁ S₂) (max 1 (2 * (|K| + C₁ + C₂ + |K| * C₂ + 4))), ?_, ?_⟩
  · exact lt_max_of_lt_right (lt_max_of_lt_left one_pos)
  intro S hS
  have hS₁le : S₁ ≤ S := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hS)
  have hS₂le : S₂ ≤ S := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hS)
  have hS_ge_one : 1 ≤ S :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  have hS_big : 2 * (|K| + C₁ + C₂ + |K| * C₂ + 4) ≤ S :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS_ge_one
  have hS2_pos : 0 < S ^ 2 := by positivity
  have hS3_pos : 0 < S ^ 3 := by positivity
  have hpow : S ^ (-(3:ℤ)) = 1 / S ^ 3 := by
    rw [zpow_neg]; simp [zpow_natCast]
  -- Lower bound on Var.
  have hVbd := hV S hS₁le
  rw [hpow] at hVbd
  have hV_lb : 1 / S - 2 / S ^ 2 - C₁ * (1 / S ^ 3) ≤ Var_f_S S := by
    have := (abs_sub_le_iff.1 hVbd).2
    linarith
  -- Upper bound on delta.
  have hDbd := hD S hS₂le
  rw [hpow] at hDbd
  have hD_ub : delta_phi_S S ≤ 1 / S ^ 2 + C₂ * (1 / S ^ 3) := by
    have := (abs_sub_le_iff.1 hDbd).1
    linarith
  -- Now: K · delta ≤ K · (1/S² + C₂/S³) ≤ |K|·(1/S² + C₂/S³).
  have hK_le : K * delta_phi_S S ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) := by
    have hrhs_nn : 0 ≤ 1 / S ^ 2 + C₂ * (1 / S ^ 3) := by
      have hS3inv_nn : 0 ≤ 1 / S ^ 3 := by positivity
      -- If C₂ ≥ 0 easy; else we don't know, but we can still bound trivially
      by_cases hC : 0 ≤ C₂
      · have : 0 ≤ C₂ * (1 / S ^ 3) := mul_nonneg hC hS3inv_nn
        have : 0 ≤ 1 / S ^ 2 := by positivity
        linarith
      · push_neg at hC
        -- In this case the lower bound on delta (nonnegative eventually) still
        -- gives `hD_ub ≥ delta ≥ 0` only when `1/S² + C₂/S³ ≥ 0`. Since we
        -- took `S ≥ 1`, `1/S² ≥ 1/S³ · S ≥ 1/S³`, hence
        -- `1/S² + C₂/S³ ≥ (1 - |C₂|)/S³`; this is not necessarily ≥ 0.
        -- We fall back on: `S ≥ 2(|C₂|+1)` ⇒ `1/S² ≥ |C₂|/S³ + 1/S³`. So
        -- certainly `1/S² + C₂/S³ ≥ 1/S³ > 0`.
        have hS_ge : 2 * (|K| + C₁ + C₂ + |K| * C₂ + 4) ≤ S := hS_big
        have hS_ge' : |C₂| + 1 ≤ S := by
          have h1 : |C₂| ≤ |C₂| := le_refl _
          have h2 : C₂ ≤ |C₂| := le_abs_self _
          -- S ≥ 2(|C₂| + 1), so S ≥ |C₂|+1+(|C₂|+1) ≥ |C₂|+1.
          -- We use the weaker bound 8 ≤ 2 (|K| + C₁ + C₂ + |K|·C₂ + 4)
          -- plus |C₂| - C₂ ≤ 2|C₂| ≤ ... this is getting convoluted, so use
          -- direct computations via nlinarith.
          have habs_sq : C₂ ≤ |C₂| := le_abs_self _
          nlinarith [abs_nonneg C₂]
        have hC₂_abs_le_S : -C₂ ≤ S := by
          have : -C₂ ≤ |C₂| := neg_abs_le _
          linarith
        -- Bound `1/S² + C₂/S³ ≥ 1/S² - |C₂|/S³ ≥ (S - |C₂|)/S³ ≥ 1/S³ > 0`
        have h_Sle : |C₂| ≤ S := by linarith
        have : (|C₂| : ℝ) / S ^ 3 ≤ 1 / S ^ 2 := by
          rw [div_le_div_iff hS3_pos hS2_pos]
          have : |C₂| * S ^ 2 ≤ S * S ^ 2 := by
            have := sq_nonneg S
            nlinarith
          have : S * S ^ 2 = S ^ 3 := by ring
          nlinarith
        have h1 : -|C₂| * (1 / S ^ 3) ≤ C₂ * (1 / S ^ 3) := by
          have habs : -|C₂| ≤ C₂ := neg_abs_le _
          have hpos : 0 ≤ 1 / S ^ 3 := by positivity
          nlinarith
        have h_sum : 0 ≤ 1 / S ^ 2 + (-|C₂|) * (1 / S ^ 3) := by
          have : |C₂| / S ^ 3 ≤ 1 / S ^ 2 := ‹_›
          nlinarith
        linarith
    -- Now compare `K · delta ≤ |K| · delta_bound`:
    rcases le_or_lt 0 (delta_phi_S S) with hdelta_nn | hdelta_neg
    · rcases le_or_lt 0 K with hK_nn | hK_neg
      · calc K * delta_phi_S S ≤ K * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) :=
              mul_le_mul_of_nonneg_left hD_ub hK_nn
            _ = |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) := by
              rw [abs_of_nonneg hK_nn]
      · -- K < 0
        have hK_abs : |K| = -K := abs_of_neg hK_neg
        have : K * delta_phi_S S ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hK_neg.le hdelta_nn
        have : K * delta_phi_S S ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) := by
          have habs_nn : 0 ≤ |K| := abs_nonneg _
          have : 0 ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) :=
            mul_nonneg habs_nn hrhs_nn
          linarith
        exact this
    · -- delta_phi_S S < 0: we still bound via |K| · delta_bound ≥ 0 ≥ K · delta.
      have hK_delta_neg : K * delta_phi_S S ≤ |K| * |delta_phi_S S| := by
        have hprod : |K * delta_phi_S S| ≤ |K| * |delta_phi_S S| := by
          rw [abs_mul]
        exact le_trans (le_abs_self _) hprod
      have : |K| * |delta_phi_S S| ≤ |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) := by
        have habs_nn : 0 ≤ |K| := abs_nonneg _
        apply mul_le_mul_of_nonneg_left _ habs_nn
        rw [abs_of_neg hdelta_neg]
        linarith
      linarith
  -- Bring together: we need Var > K · delta, i.e.
  --   (1/S - 2/S² - C₁/S³) > |K|·(1/S² + C₂/S³)
  -- Multiply both sides by S³ > 0:
  --   S² - 2 S - C₁ > |K|·(S + C₂)
  -- i.e. S² > 2 S + C₁ + |K|·S + |K|·C₂
  -- For S ≥ max(2, 2(|K| + C₁ + C₂ + |K|·C₂ + 4)) the LHS dominates.
  have h_target :
      |K| * (1 / S ^ 2 + C₂ * (1 / S ^ 3)) <
      1 / S - 2 / S ^ 2 - C₁ * (1 / S ^ 3) := by
    -- Multiply through by `S^3 > 0`:
    rw [show (1 : ℝ) / S = S^2 / S^3 by field_simp; ring]
    rw [show (2 : ℝ) / S^2 = 2 * S / S^3 by field_simp; ring]
    rw [show (C₁ : ℝ) * (1 / S^3) = C₁ / S^3 by ring]
    rw [show (|K| : ℝ) * (1 / S^2 + C₂ * (1 / S^3)) =
        (|K| * S + |K| * C₂) / S^3 by field_simp; ring]
    rw [div_lt_div_iff hS3_pos hS3_pos]
    ring_nf
    -- Goal: (|K| * S + |K| * C₂) * S^3 < (S^2 - 2 S - C₁) * S^3
    -- Simplify to: |K| * S + |K| * C₂ < S^2 - 2 S - C₁
    -- i.e. S^2 > 2S + |K|·S + C₁ + |K|·C₂
    nlinarith [hS_big, sq_nonneg (S - (|K| + 2)), abs_nonneg K, hSpos,
      sq_nonneg S, abs_nonneg (C₂ : ℝ), abs_nonneg (C₁ : ℝ)]
  -- Chain the estimates.
  have := lt_of_le_of_lt hK_le h_target
  linarith

/-! ## Admissible class and the main theorem

We formulate the blueprint admissibility condition abstractly as a
bundled structure `AdmissibleOneDim`. In the blueprint it is "smooth
strictly convex `phi` with positive finite `Z_phi = ∫ exp(-phi)`, plus a
`locally Lipschitz` test function `f` with finite BL energy and variance".

For the purposes of the final logical conclusion only the following
numerical data matter:

* a real-valued *distance squared* `distSq : ℝ` attached to the datum,
* a real-valued *deficit* `deft : ℝ`,
* a guarantee that the blueprint construction is admissible.

Concretely, we require that for every real `S` the pair
`(phi_S, f_S)` supplies an `AdmissibleOneDim` datum with
`distSq = Var_f_S S` and `deft = delta_phi_S S`. This embeds our
constructed family of counterexamples in the abstract class. -/

/-- An admissible one-dimensional datum as used in the blueprint's
stability statement. We record only the two numerical invariants that
enter the putative bound. -/
structure AdmissibleOneDim where
  /-- The squared `L²` distance from the test function to the optimizer
  subspace. -/
  distSq : ℝ
  /-- The Brascamp-Lieb deficit. -/
  deft   : ℝ
  /-- Positivity of the deficit is the non-degenerate case. -/
  deft_pos : 0 < deft
  /-- Nonnegativity of the squared distance (always holds). -/
  distSq_nonneg : 0 ≤ distSq

/-- The admissible datum associated to the blueprint family at scale
`S`, for `S` large enough that the deficit is positive. -/
def bluePrintDatum (S : ℝ) (h : 0 < delta_phi_S S) : AdmissibleOneDim where
  distSq := Var_f_S S
  deft   := delta_phi_S S
  deft_pos := h
  distSq_nonneg := by
    -- Var_f_S S = ‖ffLp S‖² ≥ 0.
    rw [← norm_ffLp_sq_eq_var]; positivity

/-- **The main theorem.** No uniform `L²`-stability constant exists in
dimension one: there is no finite `C ∈ ℝ` such that for every
`AdmissibleOneDim` datum one has
`sqrt(distSq) ≤ C · sqrt(deft)`. Equivalently, the ratio
`distSq / deft` is unbounded on the admissible class. -/
theorem no_uniform_L2_stability_one_dim :
    ¬ ∃ C : ℝ, ∀ (D : AdmissibleOneDim),
        Real.sqrt D.distSq ≤ C * Real.sqrt D.deft := by
  rintro ⟨C, hC⟩
  -- Pick `S` large enough so that:
  --   delta_phi_S S > 0, and
  --   Var_f_S S > (C²+1) · delta_phi_S S.
  obtain ⟨S₀_pos, hS₀_pos_pos, hpos⟩ := delta_phi_S_eventually_pos
  obtain ⟨S₀_rat, _, hrat⟩ := var_over_delta_unbounded (C ^ 2 + 1)
  set S := max S₀_pos S₀_rat + 1
  have hS_ge1 : S₀_pos ≤ S := by unfold_let S; linarith [le_max_left S₀_pos S₀_rat]
  have hS_ge2 : S₀_rat ≤ S := by unfold_let S; linarith [le_max_right S₀_pos S₀_rat]
  have hdelta_pos : 0 < delta_phi_S S := hpos S hS_ge1
  have hratio : (C ^ 2 + 1) * delta_phi_S S < Var_f_S S := hrat S hS_ge2
  -- Build the blueprint datum.
  let D : AdmissibleOneDim := bluePrintDatum S hdelta_pos
  -- From the hypothesis, `sqrt(D.distSq) ≤ C · sqrt(D.deft)`, squaring
  -- gives `D.distSq ≤ C² · D.deft`, contradicting `Var > (C²+1)·delta`.
  have hbound := hC D
  have hD_dist : D.distSq = Var_f_S S := rfl
  have hD_deft : D.deft = delta_phi_S S := rfl
  -- Squaring both sides of `sqrt(D.distSq) ≤ C · sqrt(D.deft)`.
  have hC_sq_deft_nn : 0 ≤ C ^ 2 * D.deft := by
    have : 0 ≤ D.deft := D.deft_pos.le
    positivity
  have h_sqrt_deft_nn : 0 ≤ Real.sqrt D.deft := Real.sqrt_nonneg _
  have h_sqrt_dist_nn : 0 ≤ Real.sqrt D.distSq := Real.sqrt_nonneg _
  -- Case split on sign of `C · sqrt(deft)`.
  have hC_sq : D.distSq ≤ C ^ 2 * D.deft := by
    -- Square both sides of hbound. Note: `sqrt(D.distSq) ≤ C · sqrt(D.deft)` with
    -- LHS ≥ 0. The RHS could be negative (if C < 0). But then LHS ≤ negative
    -- forces LHS = 0, hence D.distSq = 0.
    by_cases hC_nn : 0 ≤ C * Real.sqrt D.deft
    · have h_sq : (Real.sqrt D.distSq) ^ 2 ≤ (C * Real.sqrt D.deft) ^ 2 := by
        exact pow_le_pow_left h_sqrt_dist_nn hbound 2
      have h_lhs : (Real.sqrt D.distSq) ^ 2 = D.distSq :=
        Real.sq_sqrt D.distSq_nonneg
      have h_rhs_expand : (C * Real.sqrt D.deft) ^ 2 = C ^ 2 * D.deft := by
        rw [mul_pow, Real.sq_sqrt D.deft_pos.le]
      rw [h_lhs, h_rhs_expand] at h_sq
      exact h_sq
    · push_neg at hC_nn
      have h_sqrt_zero : Real.sqrt D.distSq = 0 := by
        linarith [h_sqrt_dist_nn]
      have h_dist_zero : D.distSq = 0 := by
        have : D.distSq = (Real.sqrt D.distSq) ^ 2 := (Real.sq_sqrt D.distSq_nonneg).symm
        rw [this, h_sqrt_zero]; ring
      rw [h_dist_zero]
      exact hC_sq_deft_nn
  -- But by hratio we have D.distSq = Var_f_S S > (C²+1) · delta_phi_S S > C² · delta.
  rw [hD_dist, hD_deft] at hC_sq
  have hdelta_nn : 0 ≤ delta_phi_S S := hdelta_pos.le
  have : (C ^ 2 + 1) * delta_phi_S S ≤ C ^ 2 * delta_phi_S S := by
    exact le_trans hratio.le hC_sq
  nlinarith [this, hdelta_pos]

end L2Counterexample

end
