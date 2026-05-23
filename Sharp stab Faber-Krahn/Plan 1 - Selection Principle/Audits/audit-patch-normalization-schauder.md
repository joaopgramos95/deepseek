# Audit patch: normalization and Schauder bootstrap

This note patches the two remaining audit objections after the deterministic
graph-entry replacement:

- F4: volume normalization transported the Euler-Lagrange law but not the
  quasi-minimality used by the regularity theory.
- F3: the uniform Schauder constant `M_m(N,R)` was asserted without isolating
  why the nonlocal Bernoulli bracket has graph-independent higher derivatives.

The conclusion is that both points are patchable, but the order of the proof
must be changed.  Free-boundary regularity should be applied to the selected
minimizer before the final dilation to unit volume.  After that, the resulting
graph is rescaled and BDV's nearly spherical theorem is applied to the
rescaled set.

## 1. Correct order around volume normalization

Let `U={u>0}` be the single selected minimizer of the penalized functional in
`B_R`.  Write

```text
|U| = |B_r|,       x_U = |U|^{-1} integral_U x dx,
```

and let

```text
V := r^{-1}(U-x_U),        v(y) := r^{-2} u(x_U+r y).
```

The regularity package should be applied to `U`, not to `V`.  The reason is
simple: `U` is the actual minimizer of the penalized functional, hence it
satisfies BDV's perturbed one-phase minimality inequality.  The set `V` is only
the image of `U` under a fixed dilation and translation.  It is still a
quasi-minimizer for a rescaled functional, but proving that is an extra step.

Thus the patched order is:

1. Use the selected minimizer `U` and its quasi-minimality to obtain density,
   nondegeneracy, the Bernoulli coefficient, and Alt-Caffarelli graph entry.
2. Prove that `partial U` is a global graph over `partial B_r(x_U)`.
3. Prove the uniform high norm bound for this graph.
4. Dilate and translate to `V`; the graph norms change by constants depending
   only on the fixed range of `r`.
5. Apply BDV Theorem 3.3 to `V`.

Since the selection lemma already gives `|r-1| <= C delta_T`, the small-deficit
regime gives

```text
1/2 <= r <= 2
```

after shrinking the threshold.  Every graph norm and collar radius is therefore
changed by a dimensional constant under the final dilation.

## 2. If regularity is applied after dilation, quasi-minimality does transport

The previous paragraph avoids the issue, but it is also useful to record the
direct calculation.

Assume `u` satisfies BDV's perturbed minimality inequality

```text
E(u) + f(|{u>0}|)
<= E(w) + f(|{w>0}|) + C sigma |{u>0} Delta {w>0}|
```

for all admissible `w` in the ambient ball.  Here

```text
E(w) = 1/2 integral |grad w|^2 - integral w.
```

Given a competitor `zeta` for `v`, define

```text
w(x) = r^2 zeta((x-x_U)/r).
```

Then

```text
E(w) = r^{N+2} E(zeta),
|{w>0}| = r^N |{zeta>0}|,
|{u>0} Delta {w>0}| = r^N |{v>0} Delta {zeta>0}|.
```

Dividing the minimality inequality by `r^{N+2}` gives

```text
E(v) + r^{-(N+2)} f(r^N |{v>0}|)
<= E(zeta) + r^{-(N+2)} f(r^N |{zeta>0}|)
   + C sigma r^{-2} |{v>0} Delta {zeta>0}|.
```

So `v` is a quasi-minimizer for the rescaled volume penalty

```text
f_r(s) := r^{-(N+2)} f(r^N s)
```

with quasi-minimality parameter `C sigma r^{-2}`.  Since `r in [1/2,2]`, this
is still a uniform BDV-type quasi-minimality inequality.  This closes the
logical gap identified in F4.  The cleaner proof order above means the
downstream regularity arguments do not need this transported version.

## 3. Correct scaling of the Bernoulli bracket

The bracket should be written using the averaged vector

```text
A_U := |U|^{-1} integral_U (y-x_U)/|y-x_U| dy,
Psi_U(x) := |x-x_U| - A_U . (x-x_U).
```

This is the same first-variation term as BDV's formula; if one writes
`A_U . x` instead, the difference is the constant `A_U . x_U`, which is
absorbed into the Lagrange multiplier.  The factor `|U|^{-1}` is essential.
It is visible in BDV's derivation through the barycenter variation term.

Under `U=x_U+rV`,

```text
A_U = A_V,
Psi_U(x_U+r y) = r Psi_V(y).
```

Therefore a Bernoulli law

```text
|grad u(x)|^2 = Lambda + a Psi_U(x)
```

becomes

```text
|grad v(y)|^2 = r^{-2} Lambda + r^{-1} a Psi_V(y).
```

This gives the scaling claimed in the main summary, but only with the averaged
definition of `A_U`.  Any version of the notes omitting the `|U|^{-1}` factor
in the bracket should be corrected.

## 4. Uniform `C^k` bounds for the Bernoulli coefficient

This is the key point missing from the bootstrap proof.

Let the selected set satisfy the annular closeness obtained from deterministic
graph entry:

```text
B_{r-h}(x_U) subset U subset B_{r+h}(x_U),
        h <= r/4.
```

Then a fixed collar of `partial U` lies in

```text
{ x : r/2 <= |x-x_U| <= 3r/2 }.
```

The Bernoulli coefficient has the form

```text
q_U(x)^2 = Lambda + a Psi_U(x),
```

with

```text
|a| <= C sigma,       0 < q_- <= q_U <= q_+,
```

where the constants come from the selected minimality and BDV Lemma 4.12.
On the collar:

- `|A_U| <= 1`;
- `D^ell(A_U . (x-x_U)) = 0` for `ell >= 2`;
- `D^ell |x-x_U|` is bounded by `C_ell r^{1-ell}`;
- `r in [1/2,2]`.

Hence, for every integer `k`,

```text
||Psi_U||_{C^k(collar)} <= C_k(N,R).
```

Because `q_U >= q_-`, the square-root map is smooth on the relevant range, and
the higher chain rule gives

```text
||q_U||_{C^k(collar)} <= C_k(N,R)
```

for every fixed `k`.  This is exactly the single-set version of BDV Lemma 4.16.
There is no dependence on high derivatives of the unknown boundary graph:
the nonlocal term contributes only the constant vector `A_U`, whose norm is
bounded by one.

This corrects the audit's feedback concern.  The bracket is nonlocal as a
functional of `U`, but its derivatives with respect to the boundary variable
`x` are uniformly controlled once the boundary stays in the fixed annulus.

## 5. Non-circular construction of `M_m(N,R)`

Fix the flatness parameter `mu` below the Alt-Caffarelli threshold and fix the
scale `rho` used in graph entry.  The deterministic graph-entry lemma supplies
local class `F(C mu,1,+infty)` balls covering `partial U`.

For each local ball, BDV Theorem 4.18 gives:

```text
partial U cap B_rho(x_i) is a C^{1,gamma} graph,
||f_i||_{C^{1,gamma}} <= C mu.
```

Using the `C^{m-1,gamma}` bound for `q_U` from the previous section, the
higher-regularity part of BDV Theorem 4.18 gives

```text
||f_i||_{C^{m,gamma}} <= C_m(N,R)
```

for every fixed `m >= 2`.

The local charts cover `partial B_r(x_U)` with at most `L=L(N,rho)` balls.
The already-known `C^1` smallness makes radial projection a uniformly
nondegenerate coordinate map on every chart.  Transforming the finitely many
local `C^{m,gamma}` estimates through this atlas gives the global graph

```text
partial U = { x_U + (r+g(theta)) theta : theta in S^{N-1} }
```

with

```text
||g||_{C^{m,gamma}(S^{N-1})} <= M_m(N,R).
```

This is the missing uniform bootstrap.  It does not run a hodograph argument on
a graph whose high norm is being proved.  The only a priori geometric input is
the small `C^1` norm from Alt-Caffarelli graph entry, and the high derivatives
come from BDV Theorem 4.18 plus the ambient `C^{m-1,gamma}` bounds for `q_U`.

## 6. Interpolation and dilation

The interpolation step in the main summary is valid once `M_m(N,R)` is known:

```text
||g||_{C^{2,gamma_0}}
<= C ||g||_{L^\infty}^{1-theta} ||g||_{C^{m,gamma}}^theta
<= C ||g||_{L^\infty}^{1-theta} M_m(N,R)^theta.
```

Hausdorff closeness gives `||g||_{L^\infty} <= C h`.  Choosing the graph-entry
threshold so that `h` is small enough yields BDV's fixed nearly-spherical
threshold `delta_sph(N,gamma_0)`.

After the final dilation to unit volume,

```text
tilde g(theta) = r^{-1} g(theta),
```

up to the harmless translation by `x_U`; since `r in [1/2,2]`, the same
small `C^{2,gamma_0}` conclusion holds with constants depending only on
`(N,R)`.

## 7. Remaining dependence

This patch still relies on the single-set transfer of BDV Lemmas 4.9, 4.11,
4.12, 4.15, 4.16, and 4.18 for the selected minimizer with
`sigma <= sigma_reg(N,R)`.  Those lemmas are per-minimizer once the penalized
functional and the small parameter are fixed.  The sequential BDV Lemma 4.13 is
not used in this patched route; it is replaced by the deterministic
Hausdorff-to-flatness and finite-atlas graph patching step.

Thus F3 and F4 are patchable.  The main summary should be updated to replace
the old hodograph paragraph and to run free-boundary regularity before the
unit-volume dilation.
