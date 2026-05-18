# Obstruction to H^{1/2}-coercivity, not to the main theorem

This note records a decisive obstruction found while trying to prove the
flow-free `H^{1/2}`-coercive perturbative theorem.  It does **not** obstruct
the main sharp stability target

```text
delta_T(Omega) >= c A(Omega)^2.
```

## 1. The hoped-for statement

The target in `HALF_SMALL_PERTURBATIVE_TARGET.md` and
`H12_FLOW_FREE_REMAINDER_ATTEMPT.md` was, roughly:

```text
Omega_phi = { r theta : 0 < r < 1 + phi(theta) },
|Omega_phi| = |B_1|,
barycenter(Omega_phi)=0,
||phi||_{L^\infty} small,
||phi||_{H^{1/2}} small
```

implies

```text
delta_T(Omega_phi) >= c(n) ||phi||_{H^{1/2}}^2,
```

with no smallness or boundedness assumption on slope, perimeter, curvature, or
any higher graph norm.

This statement is false.

## 2. The two-dimensional counterexample

Work in dimension two.  Let

```text
R_{a,k}(theta) = c_a (1 + a cos(k theta)),
Omega_{a,k} = { r e^{i theta} : 0 < r < R_{a,k}(theta) },
```

where `k >= 2`, `0<a<<1`, and `c_a` is chosen so that
`|Omega_{a,k}|=|B_1|`.  Since

```text
average_theta (1 + a cos(k theta))^2 = 1 + a^2/2,
```

we have

```text
c_a = (1 + a^2/2)^(-1/2) = 1 + O(a^2).
```

Thus, with `phi_{a,k}=R_{a,k}-1`,

```text
||phi_{a,k}||_{L^\infty} <= C a,
```

and the constant mode is only `O(a^2)`.  The barycenter is exactly zero:
`R_{a,k}^3` has only Fourier modes which are multiples of `k`, hence no
first harmonic when `k>=2`.

The `H^{1/2}(S^1)` norm satisfies

```text
||phi_{a,k}||_{H^{1/2}}^2 = c k a^2 + O(a^2 + a^4).
```

Now choose, for instance,

```text
a_j = eps_j^3,
k_j ~ eps_j^2 / a_j^2 = eps_j^{-4},
eps_j -> 0.
```

Then

```text
||phi_{a_j,k_j}||_{H^{1/2}}^2 ~ eps_j^2,
||phi_{a_j,k_j}||_{L^\infty} ~ eps_j^3 -> 0.
```

So these are smooth radial graphs with arbitrarily small amplitude and
arbitrarily small `H^{1/2}` norm.

## 3. But the torsion deficit is much smaller

Since

```text
1 - C a <= R_{a,k}(theta) <= 1 + C a,
```

we have the inclusions

```text
B_{1-Ca} subset Omega_{a,k} subset B_{1+Ca}.
```

Torsion is monotone under inclusion, and the ball maximizes torsion among sets
of the same volume.  Hence

```text
0 <= T(B_1) - T(Omega_{a,k})
   <= T(B_1) - T(B_{1-Ca})
   <= C a.
```

Equivalently, for the energy deficit `delta_T` used in the notes,

```text
delta_T(Omega_{a,k}) <= C a.
```

For the sequence above this gives

```text
delta_T(Omega_{a_j,k_j}) <= C eps_j^3
     = o(eps_j^2)
     ~ o(||phi_{a_j,k_j}||_{H^{1/2}}^2).
```

Therefore no estimate of the form

```text
delta_T(Omega_phi) >= c ||phi||_{H^{1/2}}^2
```

can hold under only small `L^\infty` amplitude and small `H^{1/2}` norm.

This is not a counterexample to the main theorem.  In the same family,

```text
|Omega_{a,k} Delta B_1| = c a + O(a^2),
A(Omega_{a,k})^2 ~ a^2,
```

with constants independent of `k`.  The upper bound `delta_T <= C a` is
compatible with the desired lower bound `delta_T >= c A(Omega)^2 ~ c a^2`.
Only the stronger `H^{1/2}` right-hand side, whose size is `k a^2`, is ruled
out.

## 4. Interpretation

The classical second variation around the ball has `H^{1/2}` spectral weights,
but that expansion is local in a stronger geometry than the `H^{1/2}` topology.
High-frequency ripples can have vanishing amplitude while their frequency grows
fast enough to keep a prescribed small `H^{1/2}` norm.  The domains still
converge to the ball in Hausdorff distance.  The torsion deficit follows the
Hausdorff/amplitude scale, not the `H^{1/2}` scale.

Equivalently: the uniform tame Steklov remainder lemma proposed in
`H12_FLOW_FREE_REMAINDER_ATTEMPT.md` cannot be true.  The remainder must depend
on additional geometry, for instance a slope/perimeter/high-norm bound, or on a
relation between amplitude and frequency.

## 5. What survives

The following statements are still plausible or already known:

```text
small C^{2,gamma} graph       => BDV H^{1/2} coercivity;
small H^{1/2} + fixed C^{m,gamma} bound
                              => small C^{2,gamma0} by interpolation;
small H^{1/2} plus perimeter/slope control
                              => possible, but a different theorem.
```

The obstruction rules out the genuinely low-regularity `H^{1/2}`-coercive
route as a replacement for graph entry or Plan 2.  A route aimed at the actual
main theorem would have to control an `L^1`/`L^2` asymmetry quantity, such as
the radial second moment, rather than the full `H^{1/2}` norm.
