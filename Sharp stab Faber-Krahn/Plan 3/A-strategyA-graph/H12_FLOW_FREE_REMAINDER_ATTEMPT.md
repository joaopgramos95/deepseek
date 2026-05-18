# H^{1/2} perturbative route: flow-free remainder attempt

**Status update.**  The `H^{1/2}`-coercive theorem targeted in this note is
false as stated.
See `H12_LOW_REGULARITY_OBSTRUCTION.md`.  Smooth radial graphs can have
`||phi||_{L^\infty}->0` and prescribed small `||phi||_{H^{1/2}}`, while their
torsion deficit tends to zero faster than `||phi||_{H^{1/2}}^2`.  Consequently
the tame Steklov remainder lemma below cannot hold without an additional
geometric hypothesis such as slope, perimeter, or high-norm control.

This does not refute the main `A(Omega)^2` theorem.  For that theorem the
right coercive scale is `L^2`/Fraenkel, not the full `H^{1/2}` graph norm; see
the direct non-BDV proof in `H12_ASYMMETRY_DIRECT_PROOF.tex`.

This note begins the direct low-regularity perturbative proof suggested in
`HALF_SMALL_PERTURBATIVE_TARGET.md`.  The aim is to avoid the BDV
Hadamard-flow remainder, whose constants require small `C^{2,gamma}` graph
norms, and replace it by a remainder estimate at the natural Steklov scale.

## 1. First realistic target

Start with smooth radial graphs, but require estimates independent of all high
norms:

```text
Omega_phi = { r theta : 0 < r < 1 + phi(theta) },
|Omega_phi| = |B_1|,
barycenter(Omega_phi)=0,
||phi||_{L^\infty} <= eta,
||phi||_{H^{1/2}} <= eps.
```

The desired theorem is:

```text
delta_T(Omega_phi) >= c(n) ||phi||_{H^{1/2}(S^{n-1})}^2
```

for `eta,eps <= eta_0(n)`, with `c(n)` independent of
`||phi||_{C^k}`.  This is weaker than the fully rough target because it still
assumes small radial amplitude, but it is much stronger than the BDV
near-spherical hypothesis: no small slope, curvature, or `C^{2,gamma}` norm.

After proving this smooth-uniform theorem, one could try to remove smoothness
by approximation.  Removing small `L^\infty` amplitude would require a separate
capacity/spike lemma; see Section 7.

## 2. Neutral modes are harmless

The constraints imply that the constant and first spherical harmonics of `phi`
are quadratic errors.

Indeed

```text
int_S (1+phi)^n dtheta = int_S 1 dtheta
```

gives, for `||phi||_infty <= eta`,

```text
n int phi + n(n-1)/2 int phi^2 = O(eta int phi^2),
```

hence

```text
|phi_0| <= C(n) ||phi||_{L^2}^2.
```

Similarly the barycenter condition

```text
int_S (1+phi)^{n+1} theta dtheta = 0
```

gives

```text
||P_1 phi||_{L^2} <= C(n) ||phi||_{L^2}^2.
```

Thus, in the small regime,

```text
||phi||_{H^{1/2}}^2
  <= 2 ||P_{>=2} phi||_{H^{1/2}}^2 + C ||phi||_{H^{1/2}}^4.
```

So it is enough to prove coercivity on `P_{>=2} phi`.

## 3. Quadratic form: known and correct

Let `H_phi` be the harmonic extension to `B_1` of the boundary datum
`P_{>=2} phi`.  Then

```text
int_{B_1} |grad H_phi|^2
  ~= sum_{k>=2} k ||phi_k||_{L^2(S^{n-1})}^2
  ~= ||P_{>=2} phi||_{\dot H^{1/2}}^2.
```

The second variation of the torsion deficit at the ball has the form

```text
Q(phi) = c_n <(Lambda - I) P_{>=2}phi, P_{>=2}phi> + lower normalizing terms,
```

where `Lambda Y_k = k Y_k` is the Steklov/Dirichlet-to-Neumann operator on the
unit sphere.  Therefore

```text
Q(phi) >= c(n) ||P_{>=2} phi||_{H^{1/2}}^2.
```

This is the same spectral core used in BDV; the issue is not the quadratic
form.

## 4. The central missing lemma

The route closes if one proves the following.

### Tame Steklov remainder lemma

For every smooth `phi` satisfying the assumptions of Section 1,

```text
delta_T(Omega_phi) = Q(phi) + R(phi)
```

with

```text
|R(phi)| <= C(n) ( ||phi||_{L^\infty} + ||phi||_{H^{1/2}} )
            ||P_{>=2} phi||_{H^{1/2}}^2.
```

The decisive feature is what is absent: no factor involving
`||nabla_tau phi||`, perimeter, curvature, or `C^{2,gamma}`.

If this lemma holds, choose `eta_0,eps_0` so that the prefactor is at most
`c(n)/2`.  Then

```text
delta_T(Omega_phi)
  >= (c(n)/2) ||P_{>=2} phi||_{H^{1/2}}^2
  >= c'(n) ||phi||_{H^{1/2}}^2,
```

using Section 2.  The asymmetry bound follows from the radial formula

```text
|Omega_phi Delta B_1|
  <= C(n) ||phi||_{L^1}
  <= C(n) ||phi||_{L^2}
  <= C(n) ||phi||_{H^{1/2}}.
```

## 5. Why this lemma is plausible

The high-frequency obstruction that kills `C^1` smallness is not an obstruction
to the lemma.  For a mode

```text
phi = a_k Y_k,     a_k ~ eps / sqrt(k),
```

one has

```text
||phi||_{H^{1/2}} ~ eps,
||nabla_tau phi||_{L^2} ~ eps sqrt(k),
Q(phi) ~ eps^2.
```

Any proof whose remainder sees `||nabla phi||` fails as `k -> infinity`.
But a flow-free proof should see only the harmonic energy of `H_phi`, and shell
errors should carry a factor equal to the shell thickness:

```text
int_{thin shell of thickness |phi|} |grad H_phi|^2
  <= ||phi||_{L^\infty} int_{annulus} |grad H_phi|^2
  ~= ||phi||_{L^\infty} ||phi||_{H^{1/2}}^2.
```

This is the heuristic source of the tame remainder.

## 6. How one might prove the lemma

A workable proof should avoid differentiating the moving boundary.  The most
promising formulation is variational.

Let

```text
u_B(r) = (1-r^2)/(2n),
H = harmonic extension of P_{>=2}phi,
v = u_B + (1/n) H + correction terms for k=0,1.
```

The correction terms enforce the volume and barycenter constraints at the same
order as the true shape derivative.  The desired expansion should follow from
testing the torsion variational principle with `v` on the common region and
using capacitary lower bounds for the mismatch on the moving boundary.

The technical heart is an annular trace/capacity estimate of the following
kind:

```text
For harmonic H in B_1 with boundary trace h,
the least Dirichlet energy needed to force a boundary displacement phi
is at least
  (1 - C||phi||_infty) <Lambda h,h>,
up to lower-order normalization errors.
```

Equivalently, the Dirichlet-to-Neumann operator for the rough radial boundary
`r=1+phi(theta)` should satisfy a one-sided quadratic-form comparison with the
ball operator:

```text
<Lambda_phi h,h>
  >= (1 - C ||phi||_infty) <Lambda_0 h,h> - lower-order normalization errors.
```

The corresponding two-sided or absolute estimate is probably false with
slope-independent constants: high-frequency roughness can increase the DtN
form.  That is harmless for stability.  The needed statement is only that
roughness cannot decrease the Steklov energy by more than an amplitude-small
factor.  The radial nature of the perturbation is the only reason this
one-sided estimate might be true without a slope bound.

## 7. Removing the L^\infty amplitude smallness

Small `H^{1/2}` alone does not imply small `L^\infty`, so the fully rough
target needs one more theorem.

A plausible replacement is a spike/capacity dichotomy:

```text
If |phi| > eta on a set A, then the torsion deficit is at least
  c eta^2 Cap_{1/2}(A),
```

while the `H^{1/2}` norm of the spike part is controlled by the same fractional
capacity.  This would let one split

```text
phi = phi_small_amplitude + phi_spike
```

and handle the first part by the tame remainder lemma and the second part by
capacity.  This is not in the repo, and it is a separate hard problem.

## 8. Current assessment

The route is viable if the tame Steklov remainder lemma can be proved.  That
lemma is exactly the place where the proof must be better than BDV's
Hadamard-flow expansion: it must be a quadratic-form estimate at the
Dirichlet-to-Neumann scale, uniform over high-frequency smooth approximants.

So the next concrete mathematical task is not to improve graph regularity.  It
is:

```text
Prove the quadratic-form stability of the ball DtN/torsion expansion under
small radial L^\infty perturbations, with constants independent of slope.
```
