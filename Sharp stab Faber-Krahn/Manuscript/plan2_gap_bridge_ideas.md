# Plan 2 Gap-Bridge Ideas

Date: 2026-05-14

Purpose: this note is for a fresh proof-construction pass, not for another audit. It records the main rigorous ideas that seem most promising for closing the remaining load-bearing gaps in the current Plan 2 route.

The relevant current files are:

1. `Plan 2/WIP/WIP_master.tex`
2. `Plan 2/WIP/WIP_LevelSetIdentity.tex`
3. `Plan 2/WIP/WIP_MetricFramework.tex`
4. `Plan 2/WIP/WIP_FJCenterBridge.tex`
5. `Plan 2/WIP/WIP_TrimmedVelocityRepair.tex`
6. `Plan 2/WIP/WIP_WeightedMetricTrace.tex`
7. `Plan 2/WIP/WIP_BoundaryLayerTransfer.tex`
8. `Plan 2/WIP/WIP_GlobalAssembly.tex`

## 1. Current truthful status

What is now essentially closed:

1. `LevelSetIdentity`: the no-atoms/coarea/layer-cake/inverse-function issues are repaired, and the Talenti profile-gap bad-set estimate is now written explicitly.
2. `TrimmedVelocityRepair`: the old Hyp-G(lower) dependence is replaced by a self-truncated good-level velocity estimate.
3. `BoundaryLayerTransfer` and `GlobalAssembly`: endpoint admissibility, large-deficit bookkeeping, and the finite-measure Kohler-Jobin exhaustion step are in place.

What is still genuinely open:

1. `MetricFramework`: a rigorous finite-perimeter upper-gradient theorem.
2. `FJCenterBridge`: the exact same-centre Fusco-Julin theorem/citation and the measurable-selection input.
3. `WeightedMetricTrace`: removing or proving the remaining conditional hypotheses, especially bad-level kinetic control if it is really needed.

The key point is that the remaining gaps are now narrow and explicit. The route is no longer blocked by the old gradient lower bound issue.

## 2. Highest-leverage idea: avoid exact endpoint dependence if possible

The current `WeightedMetricTrace` is still phrased to reach the exact endpoint `rho_delta`. That may be stricter than necessary.

The boundary-layer transfer only needs a level `rho_hat` satisfying

```tex
rho_delta-rho_hat = O(\delta_T)
```

or any error smaller than the main collar size `1-rho_delta = kappa sqrt(delta_T)`.

Since

```tex
1-rho_hat = kappa sqrt(delta_T) + O(\delta_T),
```

the transferred collar volume is still `O(sqrt(delta_T))`, hence the sharp square rate survives unchanged.

This suggests a major simplification:

1. Work only on the good set
   `G := G_I cap G_tau`, where `G_tau = {-t' >= rho_*/(2n)}`.
2. Use the repaired integrated action and kinetic bounds on `G`.
3. Use the bad-set measure bounds
   `mu(B_I) = O(delta_T)` and `|B_tau| = O(delta_T)`.
4. Show there exists a good level `rho_hat` with
   `rho_delta-rho_hat = O(delta_T)` and
   `d_X(F_{rho_hat},B_1)^2 <= C delta_T`.
5. Transfer from `E_{rho_hat}` to `Omega` directly.

If this works, then the old need for a separate bad-level kinetic input may disappear completely. This is probably the single best structural simplification still available.

## 3. Metric-framework gap: two realistic routes

The current file correctly retreats to a conditional theorem. To close it rigorously, there are two plausible routes.

### Route A: direct finite-perimeter deformation estimate

This is the cleaner route if it can be made to work.

Idea:

1. Do not pass through a weak limit of metric derivatives.
2. Work directly with the nested family `E_rho`.
3. For small `h`, compare `F_{rho+h}` and `F_rho` by writing the symmetric difference in terms of the swept slab between `E_{rho+h}` and `E_rho`, together with the homothetic rescaling defect.
4. Express the first-order cost through the normal velocity
   `V_rho - H_rho - a·nu`.
5. Prove the upper bound on
   `limsup_{h->0} d_X(F_{rho+h},F_rho)/|h|`
   directly.

What is needed:

1. A rigorous BV transport lemma for nested finite-perimeter sets under volume-radius parametrization.
2. A precise way to encode the translation mode at first order.
3. No use of Reshetnyak in the final inequality direction.

Why this route is attractive:

The audit failure was exactly that lower semicontinuity gives the wrong direction. A direct limsup estimate avoids that problem entirely.

### Route B: prove a true upper-gradient recovery theorem

If Route A is too hard, then the right replacement is a genuine limsup approximation theorem.

Idea:

1. Approximate the torsion family by smooth families `E_rho^k`.
2. Require convergence strong enough not only for perimeters, but for the action measures
   `(V_rho^k - H_rho^k - a·nu_rho^k) H^{n-1}|∂E_rho^k`.
3. Prove

```tex
\limsup_k \int_{\partial E_rho^k} |V_rho^k-H_rho^k-a·nu_rho^k|
<=
\int_{\partial^* E_rho} |V_rho-H_rho-a·nu_rho|.
```

or an equivalent local recovery estimate.

This is harder than Route A, but if successful it matches the current architecture of `WIP_MetricFramework.tex`.

## 4. Same-centre Fusco-Julin gap: the right target

The central mistake in the old manuscript route was to use one center for asymmetry and a different center for normal oscillation, or to replace both by the centroid.

The right target is explicit:

1. One center `z` must control
   `|E Delta B_r(z)|`
   and
   `int |nu - (x-z)/|x-z||^2`.
2. The measurable selection must choose from the same admissible set.

Three promising approaches:

### Route A: exact theorem already in Fusco-Julin

Before inventing anything, check whether the exact same-centre statement is already present in the paper, perhaps under slightly different notation.

If yes, the job is:

1. rewrite the statement in one normalization;
2. scale it correctly;
3. isolate the compact center set on good levels;
4. invoke Kuratowski-Ryll-Nardzewski or Castaing-Valadier cleanly.

### Route B: joint almost-minimizer of a combined functional

If the paper only gives separate minima, define a joint functional

```tex
Phi_E(z) := alpha_FJ(E,z)^2 + b_FJ(E,z)^2
```

on a compact center set `K`.

Then try to prove:

1. `Phi_E` is lower semicontinuous in `z`;
2. `inf_K Phi_E <= C D(E)` on good levels;
3. the minimizer set
   `Gamma(E) := {z in K : Phi_E(z) <= C D(E)}`
   is nonempty and compact;
4. `rho -> Gamma(E_rho)` is measurable.

This is probably the most robust way to avoid the old center mismatch.

### Route C: good-level localization first, theorem second

Because the good levels already satisfy small `D_I`, one may first localize admissible centers to a compact set `K = \overline{B_{R+1}}`, then perform all minimization only on `K`.

This avoids fake coercivity statements like "`beta(E,z)` goes to infinity as `|z|->infty`", which the audit correctly rejected.

## 5. Weighted trace gap: likely best closure strategy

Once the metric and same-centre gaps are fixed, `WeightedMetricTrace` should probably be closed in the following order.

1. Keep the repaired sign convention
   `dmu = (-t') drho = -dt`.
2. Keep the explicit smallness
   `delta <= ((1-rho_*)/(2 kappa))^2`.
3. Use `LevelSetIdentity` for:
   `int (D_H + D_I) dmu <= C delta`
   and
   `|B_tau| <= C delta`.
4. Use the same-centre FJ bridge on `G_I`.
5. Use `TrimmedVelocityRepair` only on `G_I`.
6. Use the metric theorem only where it is valid.
7. Try to choose `rho_hat` near `rho_delta` inside the good set, instead of transporting through arbitrary bad intervals.

If that works, the bad-level kinetic hypotheses can be replaced by a softer statement:

```text
the good set reaches to within O(delta) of rho_delta.
```

That is much more plausible than a full bad-level pointwise Lipschitz theory.

## 6. Concrete mathematical subgoals for Claude

A useful deployment should aim at one of the following concrete deliverables, not a general discussion.

### Deliverable A: a replacement theorem for `MetricFramework`

Produce one precise theorem, either:

1. a direct finite-perimeter limsup deformation theorem, or
2. a recovery theorem with exact hypotheses and exact conclusion.

It must imply the current conditional Theorem T in `WIP_MetricFramework.tex`.

### Deliverable B: a same-centre FJ theorem in import-ready form

Produce one theorem of the form:

```tex
exists z such that alpha_FJ(E,z)^2 + b_FJ(E,z)^2 <= C D(E).
```

Either prove it from the cited FJ source or identify the exact missing external theorem.

### Deliverable C: a measurable-selection lemma

Produce a statement of the form:

```tex
rho -> z_rho
```

is Borel on good levels, with all required pointwise bounds preserved.

### Deliverable D: a good-endpoint variant of weighted trace

Produce a version of the trace theorem that ends at a good level
`rho_hat = rho_delta + O(delta)` or `rho_delta - O(delta)`, whichever is appropriate, and verify that `BoundaryLayerTransfer` still closes sharply.

This may be the best route if the bad-level kinetic hypotheses remain hard.

## 7. Things to avoid

Claude should avoid the following dead ends.

1. Do not reintroduce the centroid as a load-bearing center.
2. Do not use the old unsupported `A0` bad-level Lipschitz claim.
3. Do not use Reshetnyak lower semicontinuity to prove an upper bound.
4. Do not assume separate FJ minimizers can be replaced by one center without proof.
5. Do not insist on the exact endpoint `rho_delta` if a nearby good endpoint is enough.

## 8. Suggested order of attack

The strongest order is:

1. Try to replace exact-endpoint trace by nearby-good-endpoint trace.
2. In parallel, attack the metric-framework theorem by a direct limsup deformation argument.
3. In parallel, settle the same-centre FJ theorem plus measurable selection.
4. Only after that, rewrite `WeightedMetricTrace` as an unconditional block.

## 9. Bottom line

The remaining proof work is no longer diffuse. The decisive questions are:

1. Can the metric derivative upper bound be proved by a true limsup argument?
2. Can one get one same-centre FJ package with measurable selection?
3. Can the weighted trace be anchored at a nearby good endpoint so that bad-level kinetics become unnecessary?

If the answer to (3) is yes, that is probably the fastest rigorous route to closure.

