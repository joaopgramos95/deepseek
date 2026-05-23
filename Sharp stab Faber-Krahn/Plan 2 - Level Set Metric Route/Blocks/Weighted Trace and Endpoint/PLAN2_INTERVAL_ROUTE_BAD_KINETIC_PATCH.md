# Plan 2 interval route: bad-level kinetic patch and remaining crux

This note tries to close the current Plan 2 / Route delta interval proof.
The active chain is

```text
LevelSetIdentity
 -> LimsupDeformation
 -> SameCentreFJ
 -> TrimmedVelocityRepair
 -> WeightedMetricTrace
 -> GoodEndpointTrace
 -> BoundaryLayerTransfer.
```

The current WIP handoff identifies the remaining conditional input as
`WIP_WeightedMetricTrace.tex` Hypothesis 3.6: two bad-level kinetic action
bounds

```text
int_{B_I}     |dot F_rho|_X^2 dmu <= C delta,
int_{B_tau0} |dot F_rho|_X^2 drho <= C delta.
```

Here

```text
B_I      = {rho : D_I(t(rho)) > eta_I},
B_tau0  = {rho : w(rho)=-t'(rho) < tau0},  tau0=rho_*/(2n),
dmu      = w(rho) drho.
```

The outcome of this attempt is:

```text
bad-I action:      closes by a crude perimeter/deformation estimate;
bad-tau action:    closes on G_I, but remains open on B_tau0 cap B_I.
```

The remaining set `B_tau0 cap B_I` is now the precise crux of the interval
route.

## 1. Global crude metric speed bound

Use `WIP_LimsupDeformation.tex` with a fixed bounded centre, say `z=0`, and
with no translation correction. For a.e. regular `rho`,

```text
|dot F_rho|_X
 <= C(n,rho_*) int_{partial^* E_rho} |V_rho - H_{0,rho}| dH^{n-1},
```

where

```text
V_rho = w(rho)/|grad u|,
H_{0,rho}(x) = (x . nu_rho)/rho.
```

Since `E_rho subset Omega subset B_R`,

```text
|H_{0,rho}| <= R/rho_*.
```

Also the coarea/volume-radius identity gives

```text
int_{partial^*E_rho} V_rho dH^{n-1}
 = w(rho) int_{partial^*E_rho} |grad u|^{-1} dH^{n-1}
 = P(B_rho).
```

Therefore

```text
|dot F_rho|_X <= C(n,R,rho_*) (1 + P(E_rho)).
```

Since

```text
D_I(t(rho)) = P(E_rho)^2 - P(B_rho)^2,
```

and `rho in [rho_*,1]`, this gives the global crude estimate

```text
|dot F_rho|_X^2 <= C(n,R,rho_*) (1 + D_I(t(rho))).          (1)
```

This estimate is intentionally rough. It does not use same-centre FJ,
normal oscillation, lower-gradient bounds, or graph structure.

## 2. The bad-I kinetic action closes

On `B_I`, by definition `D_I > eta_I`. The level-set deficit identity gives

```text
int_{rho_*}^{rho_delta} D_I(t(rho)) dmu(rho) <= C(n,rho_*) delta.
```

Hence

```text
mu(B_I)
 <= eta_I^{-1} int D_I dmu
 <= C(n,rho_*,eta_I) delta.
```

Combining this with (1),

```text
int_{B_I} |dot F_rho|_X^2 dmu
 <= C int_{B_I} (1 + D_I) dmu
 <= C (mu(B_I) + int D_I dmu)
 <= C(n,R,rho_*,eta_I) delta.
```

Thus the first conditional bad-level input in `WIP_WeightedMetricTrace.tex`
is not actually needed.

## 3. The slow-profile action closes on good-I levels

On the Fusco-Julin good set

```text
G_I = {D_I <= eta_I},
```

the perimeter is bounded:

```text
P(E_rho)^2 <= P(B_rho)^2 + eta_I <= C(n,eta_I).
```

Then (1) gives a uniform metric speed bound on `G_I`:

```text
|dot F_rho|_X^2 <= C(n,R,rho_*,eta_I).
```

The profile-gap bad-set estimate in `WIP_LevelSetIdentity.tex` gives

```text
|B_tau0| <= C(n,rho_*) delta.
```

Therefore

```text
int_{B_tau0 cap G_I} |dot F_rho|_X^2 drho
 <= C(n,R,rho_*,eta_I) |B_tau0|
 <= C delta.
```

So the second conditional input is also closed on the `D_I`-good part of the
slow-profile set.

## 4. The remaining term

The only term not controlled by the existing identities is

```text
int_{B_tau0 cap B_I} |dot F_rho|_X^2 drho.                 (2)
```

Using (1), it would be enough to prove

```text
int_{B_tau0 cap B_I} D_I(t(rho)) drho <= C delta.          (3)
```

But the level-set identity controls only

```text
int D_I(t(rho)) w(rho) drho <= C delta,
```

and on `B_tau0` the density `w` is small. The profile-gap estimate gives only

```text
|B_tau0| <= C delta.
```

These two facts do not imply (3).

Indeed the scalar bookkeeping allows the following model on a set of length
`delta`:

```text
w(rho) = eps,
D_I(t(rho)) ~ eps^{-1}.
```

Then

```text
int D_I w drho ~ delta,
|B_tau0| ~ delta,
```

but

```text
int D_I drho ~ delta/eps,
```

which is unbounded as `eps -> 0`. This is only a scalar consistency model, not
a constructed torsion counterexample, but it shows that the present deficit
identities alone cannot prove (3).

## 5. Why the good-endpoint variant does not remove this by itself

`WIP_GoodEndpointTrace.tex` finds a level

```text
rho_hat in [rho_delta - C delta, rho_delta] cap G_I cap G_tau.
```

This is useful downstream, because the boundary-layer transfer absorbs the
`O(delta)` endpoint shift.

However the proof of the trace bound at `rho_hat` still invokes the uniform
trace theorem from `WIP_WeightedMetricTrace.tex`, and that theorem transports a
small-distance level through an order-one interval. Unless the metric variation
across `B_tau0 cap B_I` is controlled, the curve can jump across arbitrarily
small slow-profile holes. The measure estimate `|B_tau0|=O(delta)` alone does
not preclude this; the bad set may be highly disconnected or dense.

Thus GoodEndpointTrace improves the endpoint interface but does not by itself
remove the bad-tau kinetic input.

## 6. Attempted bypass by raw nestedness

There is one natural way to avoid transporting the rescaled curve through
`B_tau0 cap B_I`: do not use the metric derivative at all.  If
`rho_1 < rho_2`, nestedness gives `E_{rho_1} subset E_{rho_2}`.  Therefore,
for any fixed centre `z`,

```text
|E_{rho_2} Delta B_{rho_2}(z)|
 <= |E_{rho_1} Delta B_{rho_1}(z)|
    + |E_{rho_2}\setminus E_{rho_1}|
    + |B_{rho_2}\setminus B_{rho_1}(z)|.
```

Since the two shell volumes are both `O(rho_2-rho_1)` on the fixed annulus,
this propagates an unrescaled asymmetry estimate from `rho_1` to `rho_2` with
cost `O(rho_2-rho_1)`, without any perimeter or kinetic input.

This is rigorous, but it does not have the sharp scale.  If one searches for a
good level in a terminal window of length `L`, the weighted trace/distance
budget gives at best

```text
d_X(F_{rho_1},B_1)^2 <= C delta / L
```

at some `rho_1` in that window, while raw nested transfer to `rho_delta` costs
`O(L)` in asymmetry.  The resulting bound is

```text
A(E_{rho_delta}) <= C (sqrt(delta/L) + L).
```

Optimising gives `L ~ delta^{1/3}` and hence only
`A(E_{rho_delta})^2 <= C delta^{2/3}`.  Taking `L=O(delta)` makes the shell
cost sharp but loses the averaged-distance estimate; taking `L=O(1)` keeps the
averaged-distance estimate sharp but the shell cost is order one.

Thus raw nestedness is a valid fallback proof mechanism, but it cannot replace
the missing `L^2(drho)` kinetic control in the sharp interval route.

## 7. Possible ways to close the remaining crux

The route would close if one proves any of the following.

### A. Slow-and-bad kinetic estimate

Prove directly, using torsion geometry, that

```text
int_{B_tau0 cap B_I} |dot F_rho|_X^2 drho <= C delta.
```

Given (1), a sufficient form is (3). This would require converting the weighted
control `int D_I w drho` into unweighted control on the slow set. That cannot
come from profile-gap bookkeeping alone; it must use additional structure of
torsion level sets.

### B. A metric trace lemma with removable holes

Replace the global `L^2(drho)` kinetic hypothesis by a trace theorem that can
transport through a set of holes of total length `O(delta)` using only nested
level-set structure. For arbitrary metric curves this is false; it would need
a torsion-specific no-jump/no-fragmentation statement.

### C. A regularity or BV estimate for the profile density

If the slow set `B_tau0` had controlled component structure, or if `w=-t'`
had a quantitative BV/no-dense-holes bound, the good-endpoint argument could
choose a long good component and avoid slow holes. No such estimate is present
in the current notes.

## 8. Updated status

The Plan 2 interval route is still the most promising independent route
because it has the correct `H^{1/2}` scale. This patch improves its status:
one of the two bad kinetic hypotheses is eliminated, and the other is reduced
to the single mixed bad set

```text
B_tau0 cap B_I = { -t' < tau0 and D_I > eta_I }.
```

But the route is not closed. The exact remaining theorem is:

```text
Slow-bad kinetic theorem.
For torsion level sets in the bounded class,
int_{B_tau0 cap B_I} |dot F_rho|_X^2 drho <= C(n,R,rho_*) delta_T(Omega).
```

Equivalently, using the crude deformation bound, it would be enough to prove

```text
int_{B_tau0 cap B_I} D_I(t(rho)) drho <= C delta_T(Omega),
```

or to replace this sufficient condition by a sharper torsion-specific kinetic
estimate with an extra factor of `w`.
