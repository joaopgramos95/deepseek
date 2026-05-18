# H^{1/2}-small perturbations of the ball: target theorem and real gaps

**Status update.**  The genuinely low-regularity `H^{1/2}`-coercive target
below is false without extra geometry.  The counterexample is recorded in
`H12_LOW_REGULARITY_OBSTRUCTION.md`: high-frequency ripples of vanishing
amplitude can keep a prescribed small `H^{1/2}` norm while the torsion deficit
tends to zero faster than the square of that norm.  The classical `H^{1/2}`
spectral coercivity is therefore local in a stronger graph topology, not in the
bare `H^{1/2}` topology.  This is not an obstruction to the main
`A(Omega)^2` theorem; the direct non-BDV radial-graph proof at the asymmetry
scale is recorded in `H12_ASYMMETRY_DIRECT_PROOF.tex`.

This note isolates what would be needed to prove the sharp stability result
directly for perturbations whose small norm is only the natural
`H^{1/2}` boundary norm.

## 1. Two different meanings

There are two possible statements.

### Classical smooth near-spherical, measured by H^{1/2}

Assume

```text
partial Omega = { (1+phi(theta)) theta : theta in S^{n-1} },
|Omega| = |B_1|,
barycenter(Omega)=0,
||phi||_{C^{2,gamma}} <= eps_BDV.
```

Then BDV already gives

```text
delta_T(Omega) >= c(n) ||phi||_{H^{1/2}}^2
```

and hence `A(Omega)^2 <= C delta_T(Omega)`.  In this theorem the coercive
norm is `H^{1/2}`, but the smallness hypothesis is `C^{2,gamma}`.

If, in addition, one has a fixed high-norm bound

```text
||phi||_{C^{m,gamma}} <= M(n,R)
```

and `||phi||_{H^{1/2}}` is small, then the interpolation note
`expA-bootstrap.md` upgrades this to small `C^{2,gamma0}`.  This is useful,
but it is not a genuinely low-regularity perturbative theorem.

### Genuine H^{1/2} perturbative theorem

The genuinely new target is:

```text
Omega_phi = { r theta : 0 < r < 1 + phi(theta) },
|Omega_phi| = |B_1|,
barycenter(Omega_phi)=0,
1/2 <= 1+phi <= 3/2 a.e.,
||phi||_{H^{1/2}(S^{n-1})} <= eps_0(n),
```

with no small `C^1`, `H^1`, curvature, or `C^{2,gamma}` assumption.  Prove

```text
delta_T(Omega_phi) >= c(n) ||P_{>=2} phi||_{H^{1/2}}^2,
```

where the `k=0` and `k=1` modes are removed by the volume and barycenter
normalizations.  Since

```text
A(Omega_phi)^2 <= C(n) ||phi||_{L^2}^2
                 <= C(n) ||phi||_{H^{1/2}}^2,
```

this would close sharp stability in this perturbative class.

The pointwise admissibility `1/2 <= 1+phi <= 3/2` is not cosmetic:
`H^{1/2}(S^{n-1})` alone does not imply boundedness or positivity of the
radius.  Even in dimension two, `H^{1/2}(S^1)` does not embed in `L^\infty`.

## 2. Spectral core: already correct

For a smooth perturbation

```text
phi = sum_{k>=0} phi_k,
```

the first shape derivative of the torsion potential is harmonic in the ball
with boundary datum `phi/n`.  Its Dirichlet energy is

```text
int_{B_1} |grad H_phi|^2
  ~= sum_{k>=1} k ||phi_k||_{L^2(S^{n-1})}^2
  ~= ||phi||_{\dot H^{1/2}}^2.
```

After volume removes `k=0` and translation/barycenter removes `k=1`, the
second variation has a positive Steklov gap on `k>=2`.  This is the right
scale and is not the problem.

## 3. The missing theorem

What is missing is a low-regularity nonlinear remainder estimate:

```text
delta_T(Omega_phi)
  = Q(phi) + R(phi),
Q(phi) >= c(n) ||P_{>=2} phi||_{H^{1/2}}^2,
|R(phi)| <= o(1) ||P_{>=2} phi||_{H^{1/2}}^2
```

where `o(1)->0` as the admissible smallness tends to zero, and where the
estimate is uniform over smooth approximants with arbitrarily large
`C^1`, `H^1`, and curvature norms.

This is exactly what the published BDV nearly-spherical theorem avoids by
assuming small `C^{2,gamma}`: the Hadamard-flow proof differentiates a smooth
domain path and controls remainders by strong graph norms.  A genuine
`H^{1/2}` theorem would need a different proof.

## 4. Why the usual shortcuts do not suffice

Small `H^{1/2}` does not imply small slope.  A high-frequency perturbation

```text
phi(theta) = a_k Y_k(theta),     a_k ~ eps / sqrt(k)
```

has `||phi||_{H^{1/2}} ~ eps`, but `||nabla_tau phi||_{L^2} ~ eps sqrt(k)`
and `C^1`/curvature can blow up as `k -> infinity`.  Thus one cannot invoke
convexity, classical graph regularity, or a `C^1` small near-spherical
expansion.

Raw approximation by smooth functions is also insufficient unless the
perturbative inequality has constants independent of the approximating
`C^{2,gamma}` norms.  The current BDV-style constants do depend on those norms.

## 5. Plausible proof routes

### A. Flow-free variational expansion

Use the variational characterization of torsion directly on the radial graph,
not a smooth Hadamard flow.  One would try to compare the torsion function with
the ball torsion plus the harmonic extension of the boundary displacement:

```text
u_phi ~= u_B + (1/n) H_phi.
```

The desired lower bound should come from the harmonic Dirichlet energy
`int_B |grad H_phi|^2`, with shell-volume and nonlinear terms absorbed by
`||phi||_{L^\infty}` or by a small admissibility parameter.

This is the cleanest conceptual route, but it requires proving the remainder
bound without differentiating the rough boundary.

### B. Smooth truncation with uniform constants

Let `phi_{<=K}` be the spherical-harmonic truncation.  For each `K`, the
domain is smooth and the classical second variation applies.  The needed new
input is a uniform estimate

```text
delta_T(Omega_{phi_{<=K}}) >= c ||phi_{<=K}||_{H^{1/2}}^2
```

with `c` independent of `K`, followed by lower semicontinuity/continuity of
torsion under the radial-graph convergence.  The obstacle is again the uniform
remainder; truncation alone does not supply it.

### C. Boundary integral / Dirichlet-to-Neumann formulation

Reformulate the torsion deficit through the ball Dirichlet-to-Neumann operator
and prove that the nonlinear boundary operator is a small perturbation of
`Lambda_B - I` in the `H^{1/2} -> H^{-1/2}` topology.  This would match the
Steklov spectrum perfectly.

The hard point is defining and estimating this operator when the radial graph
is only `H^{1/2} cap L^\infty`; the usual pullback to the sphere is not a
Lipschitz change of variables.

## 6. Assessment

This is a real and attractive route.  The spectral mechanism is exactly right:
the ball sees `H^{1/2}` and the neutral modes are known.  The one theorem it
needs is not another compactness/regularity entry theorem, but a genuinely
low-regularity near-ball expansion with a remainder controlled at the same
`H^{1/2}` scale.

In short:

```text
H^{1/2} coercivity:      known / spectral / correct.
H^{1/2} admissible class: needs L^\infty positivity or equivalent.
H^{1/2} nonlinear theorem: open in the repo; this is the crux.
```
