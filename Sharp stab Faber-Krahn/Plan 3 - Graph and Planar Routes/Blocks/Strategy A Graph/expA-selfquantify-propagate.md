# Part E — self-quantification + dispersive propagation: precise statements, proofs, obstruction

Independent investigation of the user's favoured Strategy-A variant
(`STRATEGY_A_PLAN.md`, "self-quantification + propagation"). Setup:
`−Δu=1` in `Ω`, `u=0` on `∂Ω`, `Σ_t={u=t}`, `E_t={u>t}`. We work on a
Sard-regular inner level `Σ_{\hat t}` extracted by Chebyshev so that
`D_H(\hat t)≤θ` (θ a small absolute constant, **not** δ_T-small) and
`|Ω∖E_{\hat t}|≤(C_n/θ)δ_T`. We track all constants. The boxed
identity used throughout:

```
∫_{Σ_{\hat t}} (|∇u|−\bar f)²/|∇u| dℋⁿ⁻¹ = m D_H/P² =: V̄ ≤ θ,
\bar f = m/P,   m=|E_{\hat t}|,   P=ℋⁿ⁻¹(Σ_{\hat t}).      (BOX)
```

The two sub-questions are answered in §1 and §2; the verdict is in §3.

---

## §1 Self-quantification on most of the boundary

### 1.1 What is genuinely free

**Lemma 1.1 (small-gradient set is small — restated with constants).**
For every `s>0`,

```
ℋⁿ⁻¹({|∇u|≤s}∩Σ_{\hat t}) ≤ 4 s \bar f^{-2} V̄ ≤ 4 s θ/\bar f².
```

*Proof.* Where `|∇u|≤s≤\bar f/2`, the integrand of (BOX) obeys
`(|∇u|−\bar f)²/|∇u| ≥ (\bar f/2)²/s = \bar f²/(4s)`. Integrate (BOX)
over that set only. ∎

This is the *only* pointwise non-degeneracy that `D_H` gives for free.
It says: the set where the normal speed is small has small
`ℋⁿ⁻¹`-measure, linearly in the threshold `s`. It does **not** give a
lower bound `|∇u|≥q_->0` everywhere; it tolerates a small-measure set
where `|∇u|` is arbitrarily small (a thin finger).

**Lemma 1.2 (L¹ closeness of `|∇u|`).** By Cauchy–Schwarz against
(BOX),

```
∫_{Σ_{\hat t}} ||∇u|−\bar f| dℋⁿ⁻¹
 = ∫ (||∇u|−\bar f|/|∇u|^{1/2})·|∇u|^{1/2}
 ≤ (m D_H/P²)^{1/2} (∫|∇u|)^{1/2} = (V̄)^{1/2} m^{1/2} ≤ (θ m)^{1/2}.
```

So `|∇u|` is within `(θ m)^{1/2}` of `\bar f` in `L¹(Σ_{\hat t})`, and
by Markov, for any `κ>0`,

```
ℋⁿ⁻¹({ ||∇u|−\bar f| > κ } ∩ Σ_{\hat t}) ≤ (θ m)^{1/2}/κ.       (M)
```

### 1.2 The curvature link, made precise

On `Σ_{\hat t}` write `q=|∇u|` (normal speed), `ν=−∇u/|∇u|` the outer
normal of `E_{\hat t}`, `H = ` sum of principal curvatures (so mean
curvature is `H/(n−1)`). The level-set second fundamental form identity
for `−Δu=1` (used in `proof-step2.md` (W), exact, regularity-free on a
smooth inner level) is

```
D²u(ν,ν) = Δu − H|∇u| = −1 − H q,    hence
∂_ν q = ∂_ν|∇u| = D²u(ν,ν)·(∇u/|∇u|·ν)/… ⟹  ½ ∂_ν q² = q + H q².   (CURV)
```

The clean consequence is the pointwise relation **on the surface**

```
H = (−1 − D²u(ν,ν))/q = −(1 + u_{νν})/|∇u|.                         (H-rel)
```

This is the precise "`|∇u|≈\bar f` ⇒ curvature control" link the
question asks for — and it is exactly where self-quantification stalls.

**Proposition 1.3 (what self-quantification can and cannot deliver).**

(a) *(positive, in measure)* On the good set
`G_κ := {||∇u|−\bar f|≤κ}∩Σ_{\hat t}`, by (M) the bad complement has
`ℋⁿ⁻¹(Σ_{\hat t}∖G_κ) ≤ (θ m)^{1/2}/κ`. Thus, off a set of
`ℋⁿ⁻¹`-measure `O((θ m)^{1/2}/κ)`, the *normal speed* is pinched:
`|∇u| ∈ [\bar f−κ, \bar f+κ]`.

(b) *(negative, decisive)* (a) gives **no** bound on `H`, on `D²u`, or
on any graph norm — not even on a large-measure subset. The relation
(H-rel) expresses `H` through the **tangential variation** of `|∇u|`,
i.e. through `∇_{tan}|∇u|` and `u_{νν}`, not through the **size** of
`|∇u|−\bar f`. A function can be `C⁰`-close to a constant in `L²` and
even pointwise on a large set while having arbitrarily large tangential
derivative on that same set: `D_H` is a *zeroth-order* (variance)
functional of `|∇u|`; curvature is *first-order* in `|∇u|` (or
second-order in `u`). No zeroth-order integral smallness controls a
first-order quantity without an *a priori* higher-order bound to
interpolate against.

*Proof of (b) — the missing modulus, quantified.* The standard surface
interpolation that would convert (BOX) into a pointwise/curvature
statement is

```
‖f‖_{L^∞(Σ)} ≲ ‖f‖_{L²(Σ)}^{ϑ} [f]_{C^α(Σ)}^{1−ϑ},
   ϑ = 2α/(2α+n−1),   f = |∇u|−\bar f.                               (INT)
```

`‖f‖_{L²}² ≍ D_H ≤ θ` is free; but (INT) needs a **δ_T-uniform**
`C^α(Σ_{\hat t})`-seminorm of `|∇u|`, equivalently a uniform interior
`C^{1,α}` bound on `u` near the level. The only interior bound available
is Schauder/De Giorgi on a ball `B_r(x)` with `x∈Σ_{\hat t}`:

```
[∇u]_{C^α(B_{r/2}(x))} ≤ C(n) r^{-1-α} ‖∇u‖_{L^∞(B_r(x))},
   valid for B_r(x) ⊂⊂ Ω,  i.e.  r < dist(x, ∂Ω).                   (SCH)
```

Here is the quantitative breakage. The good level lurks at
`dist(Σ_{\hat t}, ∂Ω) = O(δ_T)` (Step 1 budget, sharp: the level is
*forced* near `∂Ω`, it does not get to sit deep — that would cost an
`O(1)` collar, not `O(δ_T)`). So in (SCH) one must take
`r ≤ dist(x,∂Ω) = O(δ_T)`, giving

```
[∇u]_{C^α(Σ_{\hat t} near x)} ≤ C(n) δ_T^{-1-α} · ‖∇u‖_{L^∞} .
```

Feeding this into (INT) with `‖f‖_{L²}²≍θ`:

```
‖|∇u|−\bar f‖_{L^∞} ≲ θ^{ϑ/2} · (δ_T^{-1-α})^{1−ϑ} · ‖∇u‖_∞^{1−ϑ}.
```

The factor `δ_T^{-(1+α)(1−ϑ)} → ∞` as `δ_T→0`. The interpolation does
not produce smallness; it produces a quantity that **blows up** as the
deficit shrinks, because the only place a smooth inner level is
guaranteed to exist (within the `O(δ_T)` Chebyshev budget) is a
`δ_T`-thin shell where interior Schauder constants degrade like
`δ_T^{-1-α}`. ∎

**Verdict of §1.** Self-quantification delivers, *with explicit
constants*:

- `|∇u|` within `(θ m)^{1/2}` of `\bar f` in `L¹(Σ_{\hat t})`
  (Lemma 1.2);
- `ℋⁿ⁻¹({|∇u|≤s}) ≤ 4sθ/\bar f²` (Lemma 1.1);
- hence, off an `ℋⁿ⁻¹`-set of measure `O((θm)^{1/2}/κ)`, the **normal
  speed** is pinched into `[\bar f−κ,\bar f+κ]` (Prop. 1.3(a)).

It delivers **nothing** about the second fundamental form, `D²u`, or
any graph norm — not on a large set, not anywhere — because `D_H` is a
zeroth-order variance and curvature is first-order in `|∇u|`, and the
interpolation that would bridge the order gap requires a uniform
`C^α`/Hessian modulus that interior Schauder supplies only with a
constant `≍ dist(Σ_{\hat t},∂Ω)^{-1-α} ≍ δ_T^{-1-α} → ∞`. "Controlled
geometry in most places" is **not** provable from near-Serrin `L²`
smallness alone. This is the obstruction (Mod) of `two-strategies.tex`
§Strategy-A, here quantified to `δ_T^{-1-α}`.

---

## §2 Dispersive-style propagation to the whole boundary

The proposed remedy: go a further `O(δ_T)` inside, from `Σ_{\hat t}` to
`Σ_{\hat t+c}`, and let interior regularity / a smoothing along the
foliation upgrade "controlled on a large-measure part of `Σ_{\hat t}`"
to "controlled on all of `Σ_{\hat t+c}`". We formulate the lemma and
identify the precise obstruction.

### 2.1 The propagation lemma, as it would have to read

**Lemma 2.1 (sought propagation).** *Suppose `|∇u|∈[\bar f−κ,\bar f+κ]`
on `Σ_{\hat t}∖B` with `ℋⁿ⁻¹(B)≤β`. Then there is `c≍δ_T` such that on
**all** of `Σ_{\hat t+c}` one has a controlled second fundamental form
`|H| ≤ Λ(n,κ,β)`, with `Λ` independent of δ_T.*

We show Lemma 2.1 is **false** at the depth budget the route allows,
via the tentacle of `tentacle-model.md`, and identify the mechanism.

### 2.2 The depth budget vs. the smoothing scale

Two scales compete.

**(i) Available depth.** The Chebyshev extraction forces
`|Ω∖E_{\hat t}|=O(δ_T)`, and any further descent to `Σ_{\hat t+c}` is
constrained by the *same* transfer budget: the total discarded collar
must remain `O(δ_T)` or Step 5's squared-collar `O(δ_T²)≪δ_T` margin is
lost. So the admissible extra depth, **measured in volume**, is
`|E_{\hat t}∖E_{\hat t+c}| = O(δ_T)`; in the near-boundary range where
`m↑|Ω|` and `|∇u|≍1`, this is a *spatial* depth `O(δ_T)` as well.

**(ii) Smoothing scale of the equation.** `−Δu=1` is **elliptic**, not
parabolic and not dispersive. Each Cartesian component `∂_i u` is
harmonic. The honest "smoothing" available is the interior gradient /
Schauder estimate: a feature of `∇u` of transverse width `ρ` is
regularised only over a comparable spatial scale `ρ`. There is no
finite speed of propagation and no decay-in-time mechanism that damps a
localized bad set as one moves a *fixed small distance* along the
foliation; an elliptic equation couples all scales instantaneously, and
the *quantitative* statement (SCH) is precisely that controlling
`[∇u]_{C^α}` at a point needs a ball of radius `r` clear of `∂Ω`, with
constant `r^{-1-α}`. To smooth a bad set of transverse width `ρ` one
must move an *order-`ρ` spatial distance*, with a regularising constant
`ρ^{-1-α}`.

The dispersive analogy fails at the formula level: there is no
Strichartz/`L^p→L^q` gain and no `t^{-(n−1)/2}` dispersive decay; the
Poisson equation's Green function decays only **algebraically**
(`|x|^{2−n}`) and is *not* a smoothing semigroup in any direction along
the foliation.

### 2.3 The tentacle realises the obstruction quantitatively

Take `Ω=B_1∪T`, tube radius `w→0`, length `L=O(1)`, `n≥3`
(`tentacle-model.md`). The relevant numbers, with the constants from
that file:

- True deficit: `δ_T(Ω) = (2n²ω_n)^{-1}|T|(1+o(1))`,
  `|T|=ω_{n−1}w^{n−1}L`, so `δ_T ≍_n w^{n−1}L`.
- Cap height: `t_cap = (1/(2(n−1))+1)w² ≍_n w²`; for `t≤t_cap` the
  level `Σ_t` carries a tube-finger `Γ_tube` of radius `r_t≍w`, axial
  length `≍L`, on which `|∇u|≍_n w` and
  `ℋⁿ⁻¹(Γ_tube)≍_n w^{n−2}L`.
- The finger's transverse width is `≍w`. Its second fundamental form on
  the cylindrical part has principal curvature `≍ 1/r_t ≍ 1/w → ∞`
  (the tube is a thin cylinder; one principal curvature is the inverse
  cross-radius). So `|H| ≍ 1/w` on the finger: curvature is **not**
  controlled there.

Now test Lemma 2.1.

**Step A — the bad set is small in `ℋⁿ⁻¹` but the route cannot reach
past it.** On `Σ_{\hat t}` for any `\hat t≤t_cap`, the finger is the bad
set `B=Γ_tube`, `ℋⁿ⁻¹(B)≍w^{n−2}L`. For `n≥4` this is `→0`, so
"`|∇u|≈\bar f` off a small-`ℋⁿ⁻¹`-set" holds. (Indeed the §1
self-quantification is satisfied on `Σ_{\hat t}` for these levels — the
finger is small-measure.) Yet the finger's curvature is `≍1/w`.

**Step B — propagating `c≍δ_T` inside does not remove the finger.** To
make `Σ_{\hat t+c}` finger-free one needs `\hat t+c > t_cap ≍ w²`. But
the route's depth budget is volumetric, `|E_{\hat t}∖E_{\hat t+c}|
=O(δ_T)=O(w^{n−1}L)`, while clearing the finger requires discarding the
escape layer `λ_esc ≍_n |T|+w² ≍_n w²` (the `w²` ball-shell is
unavoidable: `tentacle-model.md` Task 2, derived from the intact part
of `∂B_1`, constant `≍n²`). For `n≥4`:

```
λ_esc / δ_T ≍_n w² / w^{n−1}L = w^{-(n−3)}/L → ∞.
```

So a depth `c` large enough to push past `t_cap` (and thus remove the
high-curvature finger) costs a discarded volume
`≍ w² ≫ δ_T ≍ w^{n−1}L`, blowing the transfer budget by the unbounded
factor `w^{-(n−3)}`. For `n=3` the factor is a bounded constant `>1`
for all admissible `L≲diam` (so it still fails, by a fixed margin).

**Conclusion of §2 (Lemma 2.1 is false at the route's depth).** The
proposed smoothing does not occur:

1. *Wrong PDE class.* `−Δu=1` is elliptic. There is no
   dispersive/parabolic decay that damps a localized bad set as one
   moves a fixed small distance along the foliation; the only honest
   regularisation is (SCH), which to smooth a width-`ρ` feature
   requires an order-`ρ` spatial move with constant `ρ^{-1-α}`.

2. *Scale mismatch (the precise obstruction).* The bad set is, in the
   extremal tentacle, a finger of transverse width `≍w`. Smoothing it
   requires moving a spatial depth `≍w` (equivalently exiting the
   `w²`-tall cap), i.e. discarding volume `≍λ_esc≍w²`. The route's
   depth budget is volume `O(δ_T)=O(w^{n−1}L)`. For all `n≥3`,
   `λ_esc/δ_T ≥ ` a constant `>1` (unbounded `w^{-(n−3)}` for `n≥4`).
   The `O(δ_T)` depth does **not** suffice to smooth a width-`w`
   tentacle: the bad set is precisely a thin tube the equation does not
   smooth at the `O(δ_T)` depth scale, and the depth budget is short by
   the factor `λ_esc/δ_T ≍_n w^{-(n−3)}` (`n≥4`), `≍ const>1` (`n=3`).

This is the same `w²`-vs-`|T|` wall that obstructs the graph route in
`two-strategies.tex` §Strategy-A and `tentacle-model.md`; the
"dispersive propagation" framing does not evade it, it re-encounters it
as a depth-budget shortfall.

### 2.4 A caveat: the operating-regime objection, examined honestly

`two-strategies.tex` argues the tentacle is "vacuous in the operating
regime" because `D_H≤θ` *forbids* a tentacled level: on tube levels
`D_H(t)≍_n w^{n−3}L`. Examine whether this rescues Part E.

- For `n=2,3`: `D_H ≍ w^{n−3}L = w^{-1}L` (`n=2`) or `≍ L` (`n=3`).
  For `n=2` this `→∞`, so indeed no tentacled level has `D_H≤θ` — the
  Chebyshev good level is automatically finger-free, **and** `n=2`
  already escapes within `O(δ_T)` (`|T|≍wL≫w²`). For `n=2` the §2
  propagation is *not even needed*. So Part E's mechanism is
  vacuously consistent for `n=2`, but adds nothing beyond the plain
  graph route, which already closes for `n=2`.

- For `n≥4`: `D_H(t)≍_n w^{n−3}L → 0` on the tentacle levels. So a
  tentacled level **does** satisfy `D_H≤θ` for small `w`. The
  Chebyshev good level is *not* automatically finger-free for `n≥4`;
  it can be finger-*ful* with `D_H` as small as one likes. The
  "operating regime excludes tentacles" defence **fails for `n≥4`**
  (this is exactly `tentacle-model.md` Task 5 / `proof-step2.md` §6,
  the robust `n≥4` wall). Therefore §1's negative and §2's negative
  are *not* vacuous: there is a genuine family with `D_H≤θ` (the
  near-Serrin hypothesis satisfied), small-`ℋⁿ⁻¹` bad set (§1 holds),
  yet uncontrolled curvature `≍1/w` that no `O(δ_T)`-depth propagation
  removes.

So the honest position is: the operating-regime objection saves the
*single-level* `D_H` blindness story only for `n≤3`; for `n≥4` the
tentacle is *in* the operating regime, and Part E's chain provably
fails on it.

---

## §3 Verdict on the chain

The proposed chain is

> smooth boundary + near-Serrin
> ⇒ controlled in most places
> ⇒ (go `O(δ_T)` inside)
> ⇒ controlled everywhere
> ⇒ bootstrap to small `C³` graph.

**Link 1 ("controlled in most places").** Partially true and partially
false, precisely:
- True: `|∇u|` (the *normal speed* only) is pinched to
  `[\bar f−κ,\bar f+κ]` off an `ℋⁿ⁻¹`-set of measure
  `O((θm)^{1/2}/κ)`, and `{|∇u|≤s}` has measure `≤4sθ/\bar f²`
  (Lemmas 1.1–1.2, Prop. 1.3(a)). Explicit constants, no regularity.
- False as needed: this gives **no** control of `H`, `D²u`, or any
  graph norm anywhere. `D_H` is a zeroth-order variance; curvature is
  first-order in `|∇u|`. Bridging requires the interpolation (INT),
  whose required `C^α` modulus comes only from interior Schauder with
  constant `≍ dist(Σ_{\hat t},∂Ω)^{-1-α} ≍ δ_T^{-(1+α)} → ∞`. The
  chain breaks already at Link 1 → Link 2.

**Link 3 ("go `O(δ_T)` inside ⇒ controlled everywhere").** False at the
route's depth budget. `−Δu=1` is elliptic; there is no
dispersive/parabolic smoothing along the foliation. The only honest
regularisation is interior elliptic estimates, which smooth a
transverse-width-`ρ` feature only over spatial scale `ρ` with constant
`ρ^{-1-α}`. The extremal bad set is a tentacle finger of width `≍w`;
removing it needs depth `≍w` ⟺ discarding volume `≍λ_esc≍w²`, while
the budget is `O(δ_T)=O(w^{n−1}L)`. The shortfall is the exact factor

```
λ_esc/δ_T ≍_n w^{-(n−3)}  (n≥4, → ∞),    ≍ const>1  (n=3).
```

The bad set's influence does **not** decay at the `O(δ_T)` depth scale;
it persists with curvature `≍1/w`.

**Operating-regime rescue.** Works only for `n≤3` (where `D_H≍w^{n−3}L`
is bounded below on tube levels, so `D_H≤θ` excludes fingers — but
`n=2` already closes without Part E, and `n=3` fails the depth budget
by a bounded margin anyway). For **`n≥4`** the tentacle has
`D_H≍w^{n−3}L→0`, i.e. it *satisfies* the near-Serrin hypothesis, so
the counterexample to Links 1→2 and 3 is *inside* the operating regime.

### Final verdict

**The user's favoured chain does not close. It breaks at two
independent points, both quantified:**

1. **Self-quantification (Link 1→2):** near-Serrin `L²` smallness of
   `|∇u|−\bar f` controls only the *normal speed* (zeroth order) in
   measure; it does **not** control the second fundamental form / graph
   norm (first order in `|∇u|`) anywhere, because the bridging
   interpolation needs a uniform `C^α` modulus that interior Schauder
   supplies only with the divergent constant `δ_T^{-(1+α)}` on the
   `δ_T`-thin shell where the Chebyshev level is forced to live.

2. **Propagation (Link 3):** `−Δu=1` is elliptic; there is no
   dispersive/parabolic smoothing. Removing a width-`w` tentacle finger
   needs depth `≍w` ⟺ discarded volume `≍w²`, but the transfer budget
   is `O(δ_T)=O(w^{n−1}L)`; the depth is short by the factor
   `λ_esc/δ_T ≍_n w^{-(n−3)}` for `n≥4` (unbounded), a bounded `>1`
   constant for `n=3`. The "bad set is a thin tube the equation does
   not smooth at the `O(δ_T)` depth scale" scenario the question asked
   to check for is **exactly realised** by the tentacle, with the
   shortfall quantified.

For `n=2` the chain is vacuously consistent but redundant (the plain
graph route already closes `n=2`). For `n≥3` — and *robustly*, inside
the near-Serrin operating regime, for `n≥4` — Part E's chain provably
fails on the ball+tentacle family. The obstruction is the same
`w²`-shell vs `|T|`-deficit wall identified for Strategy-A in
`tentacle-model.md` and `two-strategies.tex`; the dispersive framing
does not evade it. The route that does *not* hit this wall is the
graph-free interior route (Chain B / Strategy B): it never needs
pointwise/curvature control of a level set, trading instead through the
interior `H²` quantity `∫|D²u+\tfrac1nI|²`, for which the sharp
quadratic relation is intrinsic and regularity-free.
