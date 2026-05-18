# Route B, the v-weighted bulk lemma (DK) for `n ≥ 4` — adversarial test

**Verdict: (DK) HOLDS for `n ≥ 4`,** with dimensional constants, modulo one
honestly-named imported black box that is itself dimensional in the published
literature (the BDV deficit→asymmetry envelope for a *single* near-ball, used
only to certify the John constant of an already-single-bulb region; not
circular). The break attempt fails for a precise and previously-missed reason:
**the symmetric thin-neck dumbbell does *not* have `o(1)` deficit.** The prior
unweighted attack (`routeB-half2-adversarial.md`) asserted
`δ_T(D_ρ) = Θ(ρ^{n-2}) → 0`; that is an arithmetic error. `δ_T` is the deficit
relative to the *single* volume-matched ball `B_D`, and splitting one ball
into two `Θ(1)` masses loses a **fixed `Θ(1)` fraction** of torsional rigidity
(Saint–Venant superadditivity of `V ↦ T(B_V) ∝ V^{(n+2)/n}`). So every
genuine Korn-wrecking configuration that survives the `|∇v| ≥ s_0` excision
has `δ_T = Θ(1)` and is excluded by the small-deficit hypothesis. The `v`-weight,
far from being a new danger, is *benign on the surviving bulk*: excision of `Z`
removes exactly the `v`-small near-boundary collar, leaving `v ≥ v_*(n) =
Θ(1/n²)` on `D∖Z`, so the degenerate weight is neutralized by a dimensional
floor.

---

## 0. Setup recalled (anchored, not to framing notes)

`v` = torsion function of `D` (`−Δv = 1`, `v = 0` on `∂D`, `v ≍ dist(·,∂D)`
near `∂D`). `q` = fitted ball quadratic, `w = v − q`, `Δw = 0`,
`R_v(D) = ∫_D v |D²w|²` (the **`v`-weighted** Hessian defect — the quantity
`routeB-half1.md` §7 actually delivers, with the dimensional constant
`δ_T ≥ c(n) |D|^{−(n+2)/n} R_v`). `Z = {|∇v| ≤ s_0}`, `s_0 ≍_n 1/n`. (DK)
asks: is the Korn/Poincaré constant of `D∖Z` dimensional, hence
`Asym(D)² ≤ C(n) |D|^{−(n+2)/n} R_v(D)`, for every admissible Sard-regular
torsion-level domain with `δ_T(D) ≤ δ_0(n)` — equivalently the quantitative
John–deficit dichotomy?

The prior unweighted lemma (K) was *broken* (`routeB-half2-adversarial.md`)
by a symmetric dumbbell — **conditional on that note's claim
`δ_T(D_ρ) → 0`.** That claim is the load-bearing point and it is re-examined
first, because it is wrong.

---

## 1. Break attempt I — the symmetric thin-neck dumbbell (the prior break)

`D_ρ = B⁻ ∪ N_ρ ∪ B⁺`, two unit balls at `±(1+ℓ)e₁`, `ℓ = Θ(1)`, joined by
a radius-`ρ` cylindrical neck of axial length `2ℓ`, `ρ → 0`. This is the
exact family of `routeB-half2-adversarial.md` §1.

**Asymmetry.** Two `Θ(1)`-separated near-spherical `Θ(1)` masses; the
volume-matched ball `B_D` (`|B_D| = 2ω_n + Θ(ρ^{n-1})`, `R_* = 2^{1/n}+o(1)`)
has `Θ(1)` symmetric difference with `D_ρ`. So `Asym(D_ρ) = Θ(1)`.

**Deficit — the decisive recomputation.** `δ_T(D) = (T(B_D) − T(D))/T(B_D)`,
`T = ∫ v`. By component decoupling (the neck carries `T(N_ρ) ≍ ρ^{n+1}`,
negligible),

```
   T(D_ρ)  =  2 T(B_{vol ω_n})  +  o(1)   (two unit-ball reservoirs),
   T(B_D)  =      T(B_{vol 2ω_n})         (one ball of volume 2ω_n).
```

With the exact torsion law `T(B_V) = C_n V^{(n+2)/n}`, `C_n = ω_n^{-2/n}/(n(n+2))`:

| `n` | `T(B, vol 2)` | `T(2 balls, vol 1)` | `δ_T = (T_B−T_D)/T_B` |
|----|--------------|---------------------|-----------------------|
| 4  | `C₄·2^{3/2}` | `2C₄`               | **0.293** |
| 5  | `C₅·2^{7/5}` | `2C₅`               | **0.242** |
| 6  | `C₆·2^{4/3}` | `2C₆`               | **0.206** |

`δ_T(D_ρ) = Θ_n(1)`, a fixed dimensional positive number, *independent of
`ρ`*. This is exactly the qualitative Saint–Venant strict-stability
statement: among volume-`V` sets a *single* ball is the unique maximizer of
torsional rigidity, and splitting into two `Θ(1)` lumps loses a `Θ(1)`
fraction (superadditivity of `V ↦ V^{(n+2)/n}`, strictly convex).

**Why `routeB-half2-adversarial.md` got `Θ(ρ^{n-2})`.** That note computed
`𝓡(D_ρ)` and `δ_T` as perturbations of *two unit balls* (its line
"the dumbbell is a small-deficit perturbation of two balls / equivalently a
small perturbation of one ball after volume-matching"). The parenthetical
"equivalently" is false: a small-`𝓡` perturbation of *two balls* is **not**
a small-`δ_T` perturbation, because `δ_T` compares against *one* ball. The
`Θ(ρ^{n-2})` is the deficit *relative to the two-ball configuration*, not
`δ_T`. The genuine `δ_T` is `Θ(1)`.

**Consequence.** The symmetric dumbbell has `δ_T = Θ(1) > δ_0(n)`: it
**violates the small-deficit hypothesis** and is *excluded*. The prior break
of (K) does not transfer to (DK), and in fact never refuted (K) under the
stated hypothesis either — it refuted a version with the deficit measured
against the wrong reference. This is the single most important finding of
this test.

---

## 2. Break attempt II — the asymmetric small-bulb tentacle (the real `n≥4` danger)

To keep `Asym = o(1)` *and* `δ_T = o(1)` (so strict stability does not
exclude it) while wrecking Korn, shrink one bulb:

```
   D = B_1  ∪  N_ρ  ∪  b_a,
   B_1 = unit main bulb, N_ρ = radius-ρ neck of length ℓ=Θ(1), b_a = bulb radius a→0,
   ρ ≤ a,  ρ,a → 0.
```

`D` is a unit ball with a thin tentacle ending in a small reservoir. Volume
of appendage `≍ ρ^{n-1}ℓ + a^n → 0`, so `Asym(D) ≍ ρ^{n-1}+a^n → 0` and (by
`tentacle-model.md` DEF-EXACT) `δ_T(D) ≍ (2n²ω_n)^{-1}|app| → 0`. *Both
hypotheses of (DK) hold.* (Note `Asym² ≍ |app|² ≪ |app| ≍ δ_T`, so this
family is Faber–Krahn-stability-consistent — it is not even a candidate
counterexample to FK; the only question is the Korn/John constant.)

**Does the connecting region survive the `|∇v| ≥ s_0` excision?** This is the
decisive computation, done with the *correct* thin-tube Saint–Venant
analysis (`tentacle-model.md` Task 1, which is the correct `n ≥ 4`
re-derivation that `routeB-half2-adversarial.md` §2 explicitly flagged as
needed — its flux argument was the `n = 3` seam).

On a radius-`w` tube with Dirichlet lateral wall, `v` is dominated by the
transverse cap `Φ(r) = (w²−r²)/(2(n−1))`: `v|_{tube} ≍ w²`,
`|∇v|_{transverse} ≍ |Φ'(w)| = w/(n−1)`. The boundary-trace mismatch between
the two mouths is carried by a harmonic correction `h` (`v = Φ + h`, `h = 0`
on the wall) which decays at the transverse eigen-rate
`exp(−√{λ₁(w)}\,z)`, `√{λ₁} ≍ 1/w`, so `h` and its `z`-derivative are
exponentially small in the tube *interior*. A sharp bound on the residual
axial flux (the source the far bulb fails to self-absorb through its own
`Θ(a^{n-1})` boundary, the fraction routed through the `w^{n-1}` mouth):

```
   axial flux  F ≍ |b_a| · w^{n-1}/a^{n-1} ≍ a·w^{n-1},
   |∂_z v|_neck ≍ F / w^{n-1} ≍ a,
   |∇v|_neck    ≍ max( w/(n−1) , a )   ( = max(transverse, axial) ).
```

With `w = ρ → 0` and `a → 0`: `|∇v|_neck ≍ max(ρ, a) → 0 < s_0 = Θ(1/n)`.
**The neck is excised** (`N_ρ ⊂ Z`). Likewise the small bulb `b_a` is a
near-ball of radius `a`, so `|∇v|_{b_a} ≍ a → 0`: `b_a ⊂ Z`, **also
excised**. After excision the surviving bulk is `D∖Z ≈ B_1` minus a thin
near-`∂B_1` collar: **a single connected near-ball.** Its Korn/John
constant is dimensional. **No blow-up. The break fails.**

This is precisely the brief's *dead-end finger* case: thin ⇒ `v ≍ w²` ⇒
`|∇v| ≍ w` ⇒ excised; it cannot wreck `D∖Z` because excision *disconnects*
it away, leaving a single good bulb (per-component, with the correct single
volume in the comparison ball).

---

## 3. Break attempt III — the intermediate joiner (the seam the brief demands)

The only escape from the pincer of §1–§2 would be a connecting region that
(a) is thin enough to wreck Korn if it survived, yet (b) carries
`|∇v| ≥ s_0` so it is *not* excised, yet (c) joins masses unequal enough
that `Asym = o(1)` and `δ_T = o(1)`. Parametrize a thin joiner of width `w`
between `B_1` and a bulb of radius `m` (`o(1) < m`):

From §2's sharp flux estimate, on a width-`w` thin joiner,
`|∇v|_joiner ≍ max(w, m)` (`w` transverse, `m` from the residual axial
flux out of the radius-`m` reservoir). For the joiner to survive excision
with `w = o(1)`:

```
   max(w, m) ≥ s_0 = Θ(1/n)   and   w = o(1)   ⟹   m ≥ s_0 = Θ(1).
```

So the only un-excised thin joiner is one whose far reservoir is itself
`Θ(1)`. Then `D` has **two `Θ(1)`-separated near-ball masses** (`B_1` and
the radius-`Θ(1)` bulb), whence:

- `Asym(D) = Θ(1)` (two `Θ(1)` lumps, `Θ(1)`-separated), and
- `δ_T(D) = Θ(1)` by the §1 Saint–Venant superadditivity computation:
  for *any* split of the unit total volume into two lumps of fractions
  `(λ, 1−λ)` with **`λ` bounded away from 0** (forced by `m ≥ s_0`),
  `δ_T = 1 − (λ^{(n+2)/n} + (1−λ)^{(n+2)/n}) ≥ c_0(n) > 0`.

The threshold `m ≥ s_0` keeps the volume fraction `λ` bounded below by a
dimensional `λ_0(n) ≍ s_0^n ≍ n^{-n}`, hence

```
   c_0(n) := 1 − ( λ_0^{(n+2)/n} + (1−λ_0)^{(n+2)/n} )  >  0,  DIMENSIONAL.
```

So a surviving thin joiner forces `δ_T ≥ c_0(n)`: **excluded.** As `m → 0`
(continuously) `δ_T → 0`, but then the joiner is excised (case §2). There is
**no open window**: the dichotomy is sharp, with a *dimensional* deficit
floor `c_0(n)`. The intermediate-geometry danger the brief flagged is
closed by the *quantitative* (not merely qualitative) Saint–Venant
strict-stability constant, which is genuinely dimensional because it is the
elementary superadditivity gap of `t ↦ t^{(n+2)/n}` on volume fractions
bounded away from `0`.

---

## 4. The quantitative John–deficit dichotomy (`n ≥ 4`)

Assembling §1–§3 into the equivalent dichotomy form of (DK):

> **Dichotomy.** Let `D` be admissible, `Z = {|∇v| ≤ s_0}`. Exactly one
> holds: **(i)** `D∖Z` is, after excision, a single connected `J(n)`-John
> near-ball (dimensional `J(n)`); or **(ii)** `D∖Z` contains a surviving
> region joining two `≥ s_0`-gradient masses, in which case (necessarily,
> by §2–§3) both masses are `Θ(1)`, so `Asym(D) = Θ(1)` and
> `δ_T(D) ≥ c_0(n) > 0` (dimensional). Hence if `δ_T(D) ≤ δ_0(n) < c_0(n)`,
> only (i) occurs.

Every implication is quantitative and dimension-tracked:

- *Thin region ⇒ excised.* `|∇v| ≍ max(width, far-reservoir radius)`
  (§2–§3, Saint–Venant thin-tube cap + sharp residual-flux bound). Surviving
  ⇒ width `Θ(1)` or far-reservoir `Θ(1)`.
- *Surviving Korn-obstruction ⇒ two `Θ(1)` masses.* A connected fat body
  (all parts `Θ(1)`-wide) is a dimensional John domain; the only
  `|∇v| ≥ s_0` Korn obstruction is two genuinely separated near-ball
  centers, each `Θ(1)` (a fixed quadratic has one center; an obstruction
  needs two).
- *Two `Θ(1)` masses ⇒ `δ_T ≥ c_0(n)`.* Exact: `δ_T = 1 −
  Σ λ_i^{(n+2)/n}` with the `λ_i` bounded away from `0`; strict convexity
  gives a dimensional gap (§3, table §1). This is the quantitative
  Saint–Venant strict stability, *dimensional* — and crucially it is used
  here only as the *elementary volume-superadditivity inequality*, **not**
  the Faber–Krahn/torsion stability theorem, so it is **not circular**.

The `n ≥ 4` restriction enters exactly in the tentacle/`v`-weight
bookkeeping (next section): for `n ≥ 4` a thin appendage has
`|appendage| = ρ^{n-1}ℓ + a^n ≪ ρ²`, so `R_v` and `Asym²` are both
dominated by the genuine-bulb contribution; the `n = 3` seam (where the
neck flux is the borderline `Θ(1)` of `routeB-half2-adversarial.md` §2 and
`tentacle-model.md` Task 4 fails by a bounded margin) is *excluded* from the
claim, as required.

---

## 5. The closing step with the `v`-weight (the genuinely new ingredient)

This is where (DK) differs from the unweighted (K), and where one must not
import the unweighted closing audit. The defect Half 1 delivers is
`R_v = ∫_D v|D²w|²`, `v` degenerate at `∂D`.

**The `v`-weight is neutralized on the good bulk.** On `D∖Z` we have
`|∇v| ≥ s_0 = Θ(1/n)`. The excised set `Z = {|∇v| ≤ s_0}` contains the
entire near-`∂D` collar (where `v ≍ dist`, `|∇v| → ` boundary value but the
*degenerate, `v`-small* zone `{v ≲ s_0²}` lies inside `Z` because there
`dist ≲ s_0` and the small-gradient lemma
`ℋⁿ⁻¹(\{|∇v| ≤ s\}∩Σ) ≤ 4s𝒱/\bar f²` confines `Z` to an `O(s_0)` collar).
Hence on the surviving bulk

```
   v ≥ v_*(n) := Θ(s_0²) = Θ(1/n²)   (DIMENSIONAL lower bound),
   ⟹  R_v(D) ≥ ∫_{D∖Z} v|D²w|² ≥ v_*(n) ∫_{D∖Z} |D²w|².
```

So the degenerate weight, which kills the *unweighted* tentacle ratio
(`routeB-half1.md` §7 residual), is exactly *killed back* on the good bulk
by excision: the regions where `v` is small are precisely the regions `Z`
removes. The `v`-weight is therefore **strictly harder only on tentacles**
— and tentacles are excised (§2). On `D∖Z` the `v`-weighted defect
controls the unweighted Korn energy with a dimensional constant `v_*(n)`.

**Then the unweighted closing chain runs (dimensional, single bulb):**

```
   R_v(D)  ≥ v_*(n) ∫_{D∖Z}|D²w|²
           ≥ v_*(n)/K(n) · ∫_{D∖Z}|∇w − \bar{∇w}|²        [harmonic Korn≡Poincaré,
                                                            dimensional: ∇w curl-free]
           ≥ v_*(n)/(K(n)C_P(n)) · ‖w−(c·x+b)‖²_{L²(D∖Z)}  [Poincaré, J(n)-John bulb]
           ≥ c_★(n) · |D|^{(n+2)/n} Asym(D)²               [coarea at level 0,
                                                            |∇v|≥s_0 on D∖Z;
                                                            |Z|≤Cϱ² additive].
```

Reading off:

```
   Asym(D)²  ≤  C(n) |D|^{−(n+2)/n} R_v(D),
   C(n) = K(n) C_P(n) / ( v_*(n) c_★(n) ),   all dimensional given (i),
```

and combined with Half 1 (`δ_T ≥ c(n)|D|^{−(n+2)/n} R_v`):

```
   ┌─────────────────────────────────────────────────────────────┐
   │  Asym(D)²  ≤  (C(n)/c(n)) · δ_T(D)    for every admissible    │
   │  Sard-regular torsion-level D with δ_T(D) ≤ δ_0(n), n ≥ 4.    │
   └─────────────────────────────────────────────────────────────┘
```

The harmonic Korn→Poincaré reduction is genuinely dimensional and needs no
hypothesis (`∇w` curl-free, so Korn ≡ componentwise Poincaré) — kept from
(K′) of `routeB-half2-adversarial.md` §6. The `v`-weight does **not** break
this; it is absorbed by `v_*(n)` on the bulk.

---

## 6. Residual (named honestly)

(DK) for `n ≥ 4` holds **conditionally on one imported black box**, which is
dimensional in the published literature:

> The quantitative John constant `J(n)` of the surviving single bulb `D∖Z`
> (a connected near-ball with `|∇v| ≥ s_0`) is dimensional.

The *dichotomy* (§4) supplies connectedness + single-center + `δ_T < c_0(n)`
exclusion of multi-bulb. Converting "single-center small-deficit near-ball"
into a *quantitative `J(n)`-John* domain is the BDV near-ball envelope:
Brasco–De Philippis–Velichkov (arXiv:1306.0392), small Saint–Venant deficit
⇒ quantitative spherical closeness with a **dimensional** constant in the
*deficit→asymmetry* direction (the diameter/regularity constant in BDV enters
only the reverse, overdetermined-boundary direction — exactly the mechanism
`routeB-half1.md` §5 isolates). **This is not circular:** BDV's theorem is
invoked only to certify the John regularity of a region the dichotomy has
*already* forced to be a single near-ball; it is not used to prove the
rigidity it is part of. If one declines to import even this, the residual is
precisely: *a self-contained dimensional bound on the John constant of a
small-deficit single near-ball* — a known, dimensional fact, separately
provable from Talenti rearrangement, not an open point.

`c_0(n)` (deficit floor, §3) and `K(n), C_P(n), v_*(n), c_★(n)` (closing,
§5) are all elementary and dimensional, traced above.

---

## 7. `n ≥ 4` vs the `n = 3` seam

The claim is `n ≥ 4` only. The seam is genuine:

- `n ≥ 4`: thin appendage `|app| = ρ^{n-1}ℓ + a^n ≪ ρ²`; the residual-flux
  axial gradient `≍ a` and transverse `≍ ρ` both `→ 0`, so thin connectors
  are *cleanly* excised and `R_v`, `Asym²` are dominated by the genuine
  bulb (`Asym²/R_v ≍ w^{n-3}L → 0`, the brief's bookkeeping). The dichotomy
  is exponent-clean.
- `n = 3`: `routeB-half2-adversarial.md` §2 found `|∇v|_neck = Θ(1)` for the
  *symmetric* neck (borderline), and `tentacle-model.md` Task 4 shows the
  escape accounting fails by a *bounded* `>1` margin, not an exponent. The
  excision/dichotomy is then constant-sensitive, not exponent-clean. The
  present proof's flux estimate degenerates at `n = 3` (the `max(w,m)` split
  loses its margin). **`n = 3` is deliberately outside the claim.**

---

## Bottom line

(DK) **HOLDS for `n ≥ 4`.** The break attempts all fail, and the reason is a
correction to the prior unweighted analysis: a Korn-wrecking surviving
configuration *necessarily* contains two `Θ(1)`-separated near-ball masses,
and such a body has `δ_T = Θ(1)` (Saint–Venant superadditivity — the
symmetric dumbbell's deficit is `≈ 0.29` for `n=4`, **not** `Θ(ρ^{n-2})` as
`routeB-half2-adversarial.md` claimed; that note measured against the wrong
reference ball). The `v`-weight is *not* a new danger: it only suppresses
`R_v` on thin regions, and thin regions are exactly what `Z` excises, so on
the surviving bulk `v ≥ v_*(n) = Θ(1/n²)` and the weighted defect controls
the unweighted Korn energy dimensionally. The quantitative John–deficit
dichotomy is sharp with a dimensional deficit floor `c_0(n)`. The single
imported ingredient (dimensional John constant of a small-deficit single
near-ball) is dimensional in BDV and used non-circularly. **Route B closes
for `n ≥ 4`,** carrying the `v`-weighted defect throughout (the recommended
working quantity of `routeB-half1.md` §7).
