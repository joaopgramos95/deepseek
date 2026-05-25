# Final Countdown Plan: Pressure-Point Verification

Source of truth:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

Purpose:

This plan is for Claude to execute a hostile, manuscript-grade verification
of the remaining high-value pressure points in the candidate closure. The
route should be treated as a serious proof candidate, not as certified.

Current target locations:

```text
Section "A coarea differentiation lemma"              around line 615
Subsection "Shell-admissible radii"                    around line 691
Lemma "Local BV deformation tail"                      around line 746
Lemma "Affine shell estimate"                          around line 800
Theorem "One-sided first variation of q"               around line 947
Proposition "Positive kinetic bound"                   around line 1093
```

## Verdict Standard

Claude must return one of:

```text
PASS
PASS WITH MAJOR GAPS
BLOCKED
```

Use `PASS` only if every pressure point below survives line-by-line scrutiny.
Use `BLOCKED` if any pressure point invalidates the affine shell estimate,
Theorem `qplus`, the positive kinetic estimate, or the final sharp square
rate. Use `PASS WITH MAJOR GAPS` for serious but locally repairable issues.

## Phase 1: Variable-Thickness Coarea

Audit Lemma `varcoarea`.

Check:

1. The equality for constant slabs
   ```tex
   |\{hp<u-s<hq\}\cap A|
   =
   \int_{s+hp}^{s+hq}
      \int_{\partial^*\{u>\tau\}} 1_A/|\nabla u| dH d\tau
   ```
   is legitimate after discarding the critical set.
2. The critical-set discard is valid for bounded open `Omega` with countably
   many connected components.
3. The Lebesgue-point argument handles negative `p,q` and intervals whose
   endpoints cross `s`.
4. The simple-function extension allows Borel partitions, not just open or
   smooth sets.
5. The bounded Borel approximation uses the correct error measure
   `dH/|grad u|`, never perimeter alone.
6. The dyadic simple sandwiches really produce one fixed exceptional null set
   depending only on `(alpha,beta)`.
7. The proof never assumes a pointwise lower bound for `|grad u|`.

Output required:

```text
Phase 1 verdict:
Blocking issues:
Major issues:
Patch suggestions:
```

## Phase 2: Shell-Admissible Radii

Audit the countable registration and full-measure claim.

Check:

1. The family of rational finite-union sets `U` is countable and cofinal for
   compact subsets of `Omega`.
2. The registered endpoint pairs are bounded Borel functions on `R^n`.
3. The parameters
   ```tex
   c,p,q,lambda,r,z,a,U
   ```
   are genuinely countable and independent of the tested radius.
4. The rational approximation in Lemma `shell` is covered by the registered
   family for arbitrary real `z,a` and arbitrary shell-admissible `rho`.
5. The pullback of exceptional level sets through the monotone absolutely
   continuous map `t` is justified:
   ```tex
   |{rho : t(rho) in N}| <= tau_0^{-1} int_{t^{-1}(N)} w(rho) d rho = 0.
   ```
   Check the one-dimensional area formula carefully, including possible flat
   parts of `t`.
6. The finite-perimeter, flux-identity, and critical-boundary conditions hold
   for a.e. radius in `G_tau`.

Output required:

```text
Phase 2 verdict:
Blocking issues:
Major issues:
Patch suggestions:
```

## Phase 3: Local BV Deformation Tail

Audit Lemma `BV-tail`.

Check:

1. `T_h=id+hW` is a diffeomorphism on a fixed ball for small `h`.
2. The initial change of variables loses only a `1+o(1)` factor.
3. Replacing `1_E` by `u_epsilon=1_E*phi_epsilon` is legitimate at fixed `h`.
4. The fundamental-theorem estimate for smooth `u_epsilon` is correct.
5. The maps `y -> y + theta h W(y)` are uniformly bi-Lipschitz for small
   `h`, uniformly in `theta`.
6. The weights `psi_h` are continuous, compactly supported, uniformly
   bounded, and converge uniformly to `eta |W|`.
7. Strict `BV_loc` convergence of mollifications applies on the common
   compact support.
8. Reshetnyak continuity is being used in the correct direction and only for
   continuous weights.
9. The order of limits is valid:
   first `epsilon -> 0` at fixed `h`, then `limsup h -> 0`.
10. The final estimate is strong enough for the shell tail and has constants
    independent of the compact exhaustion.

Output required:

```text
Phase 3 verdict:
Blocking issues:
Major issues:
Patch suggestions:
```

## Phase 4: Affine Shell Estimate

Audit Lemma `shell`.

Check:

1. The compact `K` can be chosen by inner regularity for the exact finite
   measure used in the proof.
2. The rational-open `U` can be chosen with `K subset U compactly contained
   Omega`.
3. Interior regularity gives uniform `C^1` Taylor expansion on `U`.
4. The inverse affine map expansion is uniform on `U`.
5. The two threshold descriptions of `E_{rho+h}` and `T_h(E)` have the
   correct signs.
6. The local symmetric difference is indeed contained in the registered
   outward slab.
7. The rational approximation of `-w`, `1/rho`, `z`, and `a` is enough after
   taking the buffer `r downarrow 0`.
8. The local coarea limit gives exactly
   ```tex
   int_{partial*E cap U} |w + grad u dot W| / |grad u| dH.
   ```
9. The level-set tail outside `U` follows from exact total shell volume minus
   the localized shell in `U`.
10. The affine deformation tail outside `U` follows from Lemma `BV-tail` with
    a cutoff equal to one on the relevant exterior region and zero near `K`.
11. The two tails are truly bounded by the compact-exhaustion error.
12. Letting `epsilon -> 0` gives the claimed global limsup.
13. The identification
    ```tex
    (w + grad u dot W)/|grad u| = V_rho - H_{z,rho} - a dot nu_rho
    ```
    has the correct sign convention.

Output required:

```text
Phase 4 verdict:
Blocking issues:
Major issues:
Patch suggestions:
```

## Phase 5: Downstream Propagation

Audit Theorem `qplus` and Proposition `positivekinetic` only after Phases
1-4 pass or have repairable issues.

Check:

1. The minimizer of `z -> |E_rho Delta B_rho(z)|` exists.
2. The affine map sends `B_rho(z_rho)` exactly to
   `B_{rho+h}(z_rho+h a)`.
3. The Jacobian contribution is exactly `(1+h/rho)^n q(rho)`.
4. At differentiability points of `q`, `D^+q=q'`.
5. Since the right side of `qplus` is nonnegative, it indeed controls
   `q'_+`.
6. The estimate on good levels is converted from `d mu` to unweighted
   `d rho` only on `G_tau`, using `w >= tau_0`.
7. Bad-density and bad-isoperimetric levels are paid only by measure, using
   the unconditional Lipschitz bound for `q`.
8. No hidden rescaled metric-route estimate is reintroduced.

Output required:

```text
Phase 5 verdict:
Blocking issues:
Major issues:
Patch suggestions:
```

## Final Deliverable

Claude should produce:

```text
Consolidated verdict:

Pressure-point summary:

Blocking findings:

Major findings:

Minor findings:

Passed checks:

Recommended TeX patches:

Certification status:
```

Certification status must be one of:

```text
certified closed
candidate closed but needs patching
blocked
```

Do not accept the route because it is plausible. Accept it only if the exact
finite-perimeter/coarea machinery written in the TeX proves what the
downstream kinetic argument needs.
