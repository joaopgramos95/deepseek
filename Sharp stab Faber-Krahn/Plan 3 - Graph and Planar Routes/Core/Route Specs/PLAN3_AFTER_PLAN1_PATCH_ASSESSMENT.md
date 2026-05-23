# Plan 3 after the Plan 1 quantitative patch

This is an audit of the Plan 3 attempts with the new Plan 1 fact imported as
a quantitative lemma, not as a black-box proof of the final theorem.

## Imported fact from Plan 1

Call the new input **Plan1-QGE**:

For a BDV penalized selected minimizer `U_*`, once the selected asymmetry is
below the explicit threshold

```text
alpha_graph(N,R) = (h_F / C_H'(N,R))^(2N),
```

the normalized set is a global radial `C^{1,gamma}` graph over the ball. The
Bernoulli coefficient has graph-independent `C^k` bounds in a fixed annulus,
so BDV 4.18 gives

```text
||g||_{C^{m,gamma}} <= M_m(N,R).
```

Interpolation with the `L^infty` Hausdorff bound then puts the graph in the
small `C^{2,gamma_0}` nearly-spherical class. The constants are named and
computable by going through BDV/Alt-Caffarelli/Lieberman constants; no
compactness limit is used.

This fact applies only to **selected quasi-minimizers**. It does not apply to
an arbitrary original domain `Omega`, nor to an arbitrary torsion superlevel
`E_t={u>t}`.

## 1. Strategy A: selection as regularizer

**Status: revived, but it becomes Plan 1 / Route A.**

The old obstruction in `A-strategyA-graph/expA-step1-regularizer.md` was that
the regularizer only helps after one knows the selected minimizer has uniform
high graph norms; those were previously hidden in the compactness part of
Plan 1. Plan1-QGE now supplies exactly that.

So the following chain works:

```text
Omega -> one-step selected minimizer U_* -> quantitative graph entry
       -> uniform Schauder bounds -> small C^{2,gamma_0}
       -> nearly spherical Saint-Venant/Faber-Krahn closure
       -> transfer back to Omega by selection preservation.
```

This is not a new Plan 3 level-set proof. It is the now-quantitative Plan 1
proof expressed in Plan 3 language. It is still useful: it tells us the
regularizer branch is not dead. The only remaining smallness gate is the
standard one: the selected asymmetry must be below `alpha_graph`; outside it
one uses the usual far-from-ball/suboptimal stability alternative.

## 2. Strategy A: raw level-set graph route

**Status: still blocked. Plan1-QGE does not touch the blocker.**

Step 1 of Plan 3 gives a good torsion level with small integrated near-Serrin
defect. It does not make `E_t` a selected free-boundary minimizer. Therefore
Plan1-QGE cannot be applied to `E_t`.

The gap remains:

```text
weighted L^2 smallness of |grad u| on Sigma_t
    does not imply
uniform C^1, curvature, or high graph bounds for Sigma_t.
```

Any proof that treats `E_t` as already having controlled graph geometry is
still overclaiming. The old `dh-hodograph-bootstrap.md` diagnosis remains
right for raw levels: hodograph/Schauder works after a pointwise gradient
floor and a `C^{1,alpha}` seed, but the near-Serrin level-set data do not
provide that seed.

## 3. Level set, then select

**Status: possible but redundant unless a new input is added.**

One can try:

```text
choose good E_t, then run the Plan 1 selection on E_t.
```

This gives a smooth selected set, but it destroys the exact identity
`v = u - t` that made `E_t` special. To use only Plan1-QGE, one still needs a
quantitative reason that the selected asymmetry of `E_t` is already below
`alpha_graph`. Step 1 gives small `D_H` and a small removed layer; it does not
give small asymmetry.

If one imports suboptimal stability/far-regime information to force
`alpha(E_t)` small, then the route can be closed. But that is again the Plan 1
mechanism in disguise. Without that input, this hybrid does not close.

## 4. Any-graph monotonicity

**Status: not repaired.**

The radial-homotopy monotonicity attempt fails because the cubic and higher
shape terms have no sign for an arbitrary graph. Plan1-QGE helps only after
the graph is already a small selected graph, at which point the perturbative
nearly-spherical theorem applies directly and the any-graph monotonicity is
unneeded.

The positive nonperturbative idea in those notes is the Weinberger/P-function
route, i.e. Route B, not the radial homotopy route.

## 5. Self-quantify and propagate

**Status: still blocked for raw levels.**

The self-quantification notes correctly identify that the level-set identity
can give `L^1`/small-gradient-measure information, but not curvature or
high-norm graph control. Propagation from one good level to the boundary is
elliptic and loses constants at the distance-to-boundary scale.

Plan1-QGE supplies high norms only after selection. If selection is inserted,
the route collapses back to Strategy A/Plan 1. Without selection, the
propagation obstruction remains.

## 6. The `n=2` graph/convex route

**Status: tentacles are less dangerous in `n=2`, but the convexity claim is
false as stated.**

The tentacle accounting in `B-routeB-weinberger/tentacle-model.md` says that
the "remove an `O(delta_T)` layer to escape the tentacle" idea survives the
ball-plus-thin-tentacle model only in `n=2`. That is a real positive sign.

But the proposed next step

```text
small H^{1/2} graph  =>  convex set
```

is false. In polar form, take

```text
r(theta) = 1 + a sin(k theta),        a = eps k^(-1/2).
```

Then `||r-1||_{H^{1/2}} ~ eps`, but the curvature condition contains a second
derivative term of size `a k^2 = eps k^(3/2)`, which is arbitrarily large and
changes sign for large `k`. Thus a graph can be very small in the torsional
`H^{1/2}` scale and still be highly non-convex with unbounded curvature.

Removing a small part also does not automatically produce controlled geometry:
outward spikes may be cut away, but inward corrugations/fjords cannot be
fixed by removal alone, and parallel/torsion level sets can develop large
derivatives near the cut locus or where the gradient is small. Sard regularity
gives analyticity of a particular level, not uniform bounds on all derivatives.

So in `n=2` there may still be a special theorem worth seeking:

```text
good torsion level + n=2 topology + tentacle accounting
    => controlled John/convex-like geometry after O(delta_T) removal.
```

But it is not a consequence of `H^{1/2}` smallness, and Plan1-QGE does not
prove it for raw levels.

## 7. Route B: graph-free Weinberger route

**Status: promising, but not closed by the current notes; Plan1-QGE is mostly
orthogonal.**

There are two separate Route B stories.

### 7.1 The old dumbbell obstruction was partly an underclaim

The older `routeB-half2-adversarial.md` treated a symmetric thin-neck dumbbell
as a small-deficit obstruction. The newer `dk-nge4.md` correctly points out
that an equal-mass dumbbell has fixed Saint-Venant deficit relative to the
single volume-matched ball. Splitting one ball into two order-one masses loses
a fixed amount because

```text
T(B_V) = C_n V^((n+2)/n)
```

is strictly superadditive in the relevant comparison. So that dumbbell is not
a small-deficit counterexample. This is a genuine repair of an underclaim in
the older audit.

### 7.2 The thin-tentacle escape obstruction remains for the raw level route

The ball-plus-tentacle computation is still decisive for the "good level is
automatically tentacle-free" route:

```text
delta_T(Omega) ~ w^(n-1) L,
escape layer ~ |T| + w^2.
```

For `n >= 4`, the ratio of escape layer to deficit blows up like
`w^(-(n-3))`; for `n=3` it fails by a fixed constant margin in the model. In
`n=2`, this specific tentacle obstruction disappears. This does not give
convexity or uniform graph bounds; it only removes one obstruction.

### 7.3 The weighted Route B closure has two serious overclaims

The weighted Half-1 quantity is

```text
R_v(D) = integral_D v |D^2 v + (1/n)I|^2.
```

The deeper problem is spectral. On the unit ball, if `H_k=r^kY_k` is the
harmonic extension of a degree-`k` spherical harmonic, then

```text
integral_B |grad H_k|^2 = k,
integral_B v_B |D^2 H_k|^2 = k(k-1)/n.
```

Thus `R_v` sees an `H^1` boundary scale, while the Saint-Venant deficit sees
the sharp `H^{1/2}` scale. For nearly spherical perturbations
`r=1+eps Y_k`, this gives

```text
R_v / delta_T ~ k.
```

Therefore the claimed dimensional inequality

```text
delta_T(D) >= c(n) R_v(D)
```

is false even for smooth near-balls. This is written out in
`B-routeB-weinberger/weighted-square-function-repair-obstruction.md`.

There is also a second, more local error in the newer `dk-nge4.md` closure.
The newer `dk-nge4.md` tries to convert this to an unweighted Korn/Poincare
estimate by saying that on `D \ Z`, where `Z={|grad v| <= s0}`, one has a
dimensional lower bound `v >= v_*(n)`.

That implication is false. The ball is already a counterexample. For the unit
ball,

```text
v(r) = (1-r^2)/(2n),       |grad v| = r/n.
```

Near the boundary, `v -> 0` while `|grad v| -> 1/n`. Thus for any useful
`s0 < 1/n`, the boundary collar is not removed by `Z`, and `v` has no positive
lower bound on `D \ Z`.

Therefore the current proof of

```text
weighted Hessian defect -> unweighted Korn energy -> asymmetry
```

does not work. This is not fixed by Plan1-QGE.

### 7.4 What would have the right scale

The right ball-model quantity is not `integral v |D^2 w|^2`; it is the
first-order harmonic energy

```text
integral_B |grad H|^2 ~ ||trace H||_{\dot H^{1/2}(S^{n-1})}^2.
```

So a genuinely graph-free route must produce a first-order harmonic energy, or
use an interval of levels to recover a half-derivative trace. That points back
toward the Plan 2 metric/radial trace machinery. A single-level
Weinberger-Hessian defect has the wrong order.

## 8. What actually works now

The part that now works quantitatively is:

```text
Plan 3 Strategy A, but with the Plan 1 selected minimizer replacing raw levels.
```

This gives an effective proof with computable constants, provided one is
allowed to use the BDV regularity package and extract its constants.

The parts that do not work yet are:

```text
raw level -> graph/convexity,
raw H^{1/2} smallness -> controlled geometry,
radial any-graph monotonicity,
Route B via weighted/unweighted Hessian Half-1.
```

The most worthwhile Plan 3 direction after this audit is not another attempt
to force raw levels into classical `C^k` graph bounds, and not the
single-level Hessian Route B. It is either:

```text
Plan 1 / selected minimizer:
  use the now-quantitative graph entry and bootstrap;

or Plan 2 / metric trace:
  use an interval of levels to obtain the correct H^{1/2}-scale trace.
```

For `n=2`, there is a separate possible project: exploit the fact that the
thin-tentacle escape accounting is favorable, but the missing theorem is still
a quantitative geometry theorem for good levels. It is not merely a convex
domain theorem, because convexity has not been obtained.
