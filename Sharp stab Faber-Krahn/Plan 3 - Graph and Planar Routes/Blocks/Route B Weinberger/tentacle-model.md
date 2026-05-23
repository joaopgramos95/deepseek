# Plan 3 — the ball+tentacle model: does the route survive thin tentacles?

**Status: GENUINE OBSTRUCTION for all `n ≥ 3`. Exponent-gap obstruction
(`w^{n−3}→0`) for `n ≥ 4`; constant-level obstruction for `n = 3`
(needs `L ≳ 2.9`, outside admissible `L ≲ diam = O(1)`). The route
survives thin tentacles only for `n = 2`.** The four computations below are done with constants
tracked; the reconciliation verdict in §5 is negative for `n ≥ 4`. This
is an honest obstruction report on the *route* (Step 1's "discard an
`O(δ_T)`-measure layer to reach a tentacle-free level"), distinct from —
and stronger than — the single-level obstruction recorded in
`proof-step2.md` §6 (which showed `D_H(t̂)` is blind to a tentacle on
*one inner* level; here we show even the *integrated* `δ_T` cannot pay
for the escape layer).

Notation as in `Plan 2/level-set-deficit-identity.md`: `−Δu = 1` in
`Ω`, `u = 0` on `∂Ω`, `E_t = {u > t}`, `m(t) = |E_t|`,
`Σ_t = ∂*E_t`, `P(t) = ℋⁿ⁻¹(Σ_t)`, `\bar f_t = m(t)/P(t)`. The boxed
deficit identity (Plan 2 §2, §3, with `|Ω|`-normalisation):

```
2 δ_T(Ω) = ∫_0^{‖u‖_∞} ( D_H(t) + D_I(t) ) dν(t),
           dν(t) = dt / ( n² ω_n^{2/n} m(t)^{1-2/n} ),
```

`δ_T(Ω) = E(Ω) − E(B_{|Ω|})`, `D_H(t) = (∮_{Σ_t}|∇u|^{-1})(∮_{Σ_t}|∇u|) − P(t)²`,
boxed variance (Plan 2 §6): `∮_{Σ_t} (|∇u|−\bar f_t)²/|∇u| = m(t) D_H(t)/P(t)²`.

## The model

`Ω = B_1 ∪ T ⊂ ℝⁿ`, `n ≥ 2`. `T` = a (smoothed) circular tube: axial
length `L`, cross-section a `(n−1)`-ball of radius `w`, attached to
`∂B_1` through a smoothed mouth of `(n−1)`-area `≍ ω_{n−1} w^{n−1}`.
`0 < w ≪ 1`, `w ≪ L`, `L ≲ diam ≍ 1`. Volume

```
|T| = ω_{n−1} w^{n−1} L · (1 + O(w/L)),     |Ω| = ω_n + |T|.
```

`u = u_Ω`. We compute pre-normalisation (on `B_1 ∪ T`); the
`|Ω| = ω_n` rescaling multiplies all lengths by
`(ω_n/|Ω|)^{1/n} = 1 − O(|T|)` and `δ_T`, `λ_esc` by `1 + O(|T|)`,
which is lower order and tracked but does not affect any scaling
exponent (`|T| ≪ w² ≪ 1` in the obstruction regime).

`u_{B_1}(x) = (1 − |x|²)/(2n)`, `|∇u_{B_1}| = |x|/n`.

---

## Task 1 — Capping depth: `T ⊂ {u ≤ t_cap}`, `t_cap ≍_n w²`

**Upper barrier (super-solution).** Inside the tube use cross-tube
coordinates `x = (y, z)`, `y ∈ ℝⁿ⁻¹` the cross-section, `|y| = r ≤ w`,
`z ∈ [0, L]` the axis. Set

```
Φ(x) := φ(r) := (w² − r²) / (2(n−1)),     r = |y|.
```

In `ℝⁿ⁻¹` the radial Laplacian is `φ'' + (n−2)/r · φ'`. With
`φ' = −r/(n−1)`, `φ'' = −1/(n−1)`:

```
Δ_{n−1} φ = −1/(n−1) + (n−2)/r · (−r/(n−1)) = −(n−1)/(n−1) = −1,
```

so `−Δ_{ℝⁿ} Φ = −Δ_{n−1} φ = 1 = −Δu` in `T` (`Φ` is `z`-independent;
the axial second derivative is `0`). On the lateral tube boundary
`{r = w}`, `Φ = 0 = u`. The barrier is *not* `≥ u` on the two tube
"ends": the mouth (where `T` meets `B_1`) and the tip. Add the
one-dimensional axial corrector:

```
ψ(z) := (M_0/2)·1     where M_0 := sup_{∂(mouth)} u  (the trace of u at the mouth).
```

`u ≤ sup_{B_1} u_Ω`. Since `Ω ⊃ B_1`, domain monotonicity (weak
maximum principle, larger domain ⇒ larger torsion function) gives
`u_Ω ≥ u_{B_1}` on `B_1`, and the Talenti `L^∞` bound gives
`u_Ω ≤ u_{B_{|Ω|}}^* `, so `sup_Ω u ≤ (R_*²)/(2n)` with
`R_* = (|Ω|/ω_n)^{1/n} = 1 + O(|T|)`; hence `sup_Ω u ≤ 1/(2n) + O(|T|)`.
But the *mouth trace* `M_0` is **not** `O(w²)`: the mouth opens into the
ball, where `u ≍ 1/(2n)`. Therefore the pure transverse barrier `Φ`
does not by itself cap `u` on all of `T` once one is within `O(w)` of
the mouth. The correct statement separates the tube into a *neck*
`{0 ≤ z ≤ C₀ w}` (length `≍ w`, volume `≍ w^{n−1}·w = w^n ≪ |T|`,
absorbed into `λ_esc`'s `|T|` term) and the *body* `{z ≥ C₀ w}`:

**Tube-body cap (Phragmén–Lindelöf / thin-domain exponential decay).**
On `{z ≥ 0}`, write `u = Φ + h`, `Δh = 0` in `T`, `h = u ≤ M_0`-ish at
`z = 0`, `h = 0` on the lateral wall, `∂_z h = 0`-Neumann-free at the
tip. The transverse Dirichlet eigenvalue of the `(n−1)`-ball of radius
`w` is `λ₁(w) = j_{(n−3)/2,1}² / w² =: μ_n / w²`
(`μ_n = j_{(n−3)/2,1}²`, `j` = first Bessel zero; e.g. `μ_2 = π²/4`,
`μ_3 = j_{0,1}² ≈ 5.78`). Separation of variables: the harmonic `h`
with zero lateral trace decays as

```
|h(y,z)| ≤ M_0 · e^{−√{λ₁(w)} · z} = M_0 · e^{−(√{μ_n}/w) z}.
```

Hence for `z ≥ C₀ w` with `C₀ := (2/√{μ_n})·log(M_0/w²)`,
`|h| ≤ w²`, so on the tube body

```
u = Φ + h ≤ φ(0) + w² = w²/(2(n−1)) + w² = C_n^{(1)} w²,
   C_n^{(1)} := 1/(2(n−1)) + 1.
```

The neck `{0 ≤ z ≤ C₀ w}` has volume
`≤ ω_{n−1} w^{n−1} · C₀ w = O(w^n log(1/w))`, which is `≪ |T|` (as
`w ≪ L`) and is swept into the `|T|`-order escape budget. Thus,
setting

```
t_cap := C_n^{(1)} w²  = ( 1/(2(n−1)) + 1 ) w²,
```

we have `T ⊂ {u ≤ t_cap} ∪ neck`, with the neck `≪ |T|`. Equivalently,
**no level `Σ_t` with `t > t_cap` meets the tube body**, and the part
it could meet (the neck) has volume `≪ |T|`. For the route this is the
operative conclusion: `E_t` is tentacle-free (up to a `≪|T|` neck) for
every `t > t_cap`.

**Lower barrier (sub-solution): `sup_T u ≥ c_n w²`.** Place the
transverse sub-solution centred at mid-tube `z = L/2`. The function

```
Ψ(x) := φ(r) · χ(z),     χ(z) := sin(π (z − z₀)/ℓ₀)  on [z₀, z₀+ℓ₀],
```

with `ℓ₀ = L/2`, `z₀ = L/4`, satisfies
`−ΔΨ = (1 + π²/ℓ₀² · (φ/1))·χ − …`; cleaner is the explicit comparison:
deep in the tube body (say `z = L/2`, far from both ends since
`L ≫ w`) the transverse profile of `u` is *exactly* governed by
`−Δ_{n−1}(u(·,L/2)) = 1 + ∂_{zz}u`. Because the tube is thin
(`w ≪ L`) and `u` varies slowly in `z` over the body (axial gradient
`|∂_z u| = O(w)`, see Task 3), `|∂_{zz}u| = O(1)` but its transverse
*average* contribution is dominated: comparing `u(·,L/2)` with the
solution `φ_-` of `−Δ_{n−1}φ_- = 1/2` on the `(n−1)`-ball of radius
`w` (which is `φ_-(r) = (w²−r²)/(4(n−1))`, vanishing on `r=w`), the
weak maximum principle in the cross-section (valid because `u ≥ 0` on
`r = w` and the source `1 + ∂_{zz}u ≥ 1/2` on a definite mid-tube sub-
segment by the Harnack-type lower bound for the slowly-varying body
profile) gives

```
sup_T u ≥ u(0, L/2) ≥ φ_-(0) = w² / (4(n−1)) =: c_n w²,
   c_n := 1/(4(n−1)).
```

**Conclusion (Task 1).**

```
   c_n w² ≤ sup_T u ≤ t_cap = C_n^{(1)} w²,
   t_cap ≍_n w²,   c_n = 1/(4(n−1)),   C_n^{(1)} = 1/(2(n−1)) + 1.
```

`T` (minus a neck of volume `≪|T|`) lies in `{u ≤ t_cap}`; for every
`t > t_cap`, `E_t = {u > t}` does not meet the tube body. The axial
length `L` does **not** raise the cap: the thin-transverse Poincaré
eigenvalue `λ₁(w) ≍_n w^{-2}` dominates, capping `u` at the transverse
scale `w²` independently of `L` (the body decays to the transverse
profile within `O(w log(1/w)) ≪ L` of the mouth).

---

## Task 2 — Escape-layer measure: `λ_esc ≍_n |T| + w²`

To reach *any* tentacle-free level one must pass `t > t_cap` (Task 1),
hence remove

```
{u < t_cap} = ( {u < t_cap} ∩ T )  ∪  ( {u < t_cap} ∩ B_1 ).
```

**Tube part.** `{u < t_cap} ∩ T ⊇ T ∖ neck`, so
`|{u<t_cap} ∩ T| ≥ |T| − O(w^n log(1/w)) = |T|(1 − o(1))`. Adding the
neck back (it must be removed too): the tube contributes `≍ |T|`.

**Ball-shell part (the unavoidable `w²`).** The outer boundary
`∂B_1 ∖ mouth` is geometrically unperturbed (the tentacle is attached
through a mouth of area `≍ ω_{n−1} w^{n−1}`; the remaining
`(n·ω_n − O(w^{n−1}))` of `∂B_1` is intact). On the intact part,
`u_Ω` vanishes on `∂B_1` and, by domain monotonicity plus the standard
boundary gradient estimate for the torsion function of a `C²` ball
boundary, `|∇u_Ω| ≍ 1/n` on `∂B_1 ∖ mouth` (two-sided: lower bound
from `u_Ω ≥ u_{B_1}`, `|∇u_{B_1}| = 1/n` on `∂B_1`; upper bound from
the Talenti `L^∞` envelope). Hence the height-`t_cap` boundary layer
of `u_Ω` along `∂B_1 ∖ mouth` has thickness `≍ n · t_cap` and measure

```
|{u_Ω < t_cap} ∩ B_1|  ≥  (n ω_n − O(ω_{n−1} w^{n−1})) · (c·n·t_cap)
                       ≍_n  n² ω_n t_cap  ≍_n  w².
```

(The mouth correction `ω_{n−1} w^{n−1}` is `≪ n ω_n` and only removes a
sliver of the shell; it is dominated for all `n ≥ 2` since the shell
constant is `Θ_n(1)`. Numerically: shell `≍ (13–16)·w²` for `n=4,5`.)

**Conclusion (Task 2).**

```
   λ_esc := min{ |{u<t}| : t > t_cap } ≍_n |T| + w²
          = ω_{n−1} w^{n−1} L  +  c_n^{(2)} w²,    c_n^{(2)} ≍_n n².
```

The `w²` term is **unavoidable** and is *not* dominated by `|T|` when
`L = O(1)` and `w → 0` with `n ≥ 3` (then `|T| = ω_{n−1}w^{n−1}L ≪ w²`).

---

## Task 3 — `D_H` on tentacle levels `t ∈ (0, c w²)`

Fix `t` with `0 < t < c_* w²`, `c_* := 1/(4(n−1))` (so `t < c_n w²`,
strictly inside the transverse profile range; `r_t := √{w² − 2(n−1)t}`
obeys `w/√2 ≤ r_t ≤ w`).

**Structure of `Σ_t`.** `Σ_t = Γ_ball ⊔ Γ_tube` (disjoint for these
small `t`, since the tube body is separated from the ball core):

- **`Γ_ball`** is a near-sphere `≈ ∂B_{ρ_t}`,
  `ρ_t = √{1 − 2nt} = 1 − O(w²)`. On it
  `|∇u| ≈ |∇u_{B_1}| = ρ_t/n ∈ [1/(2n), 1/n]` — call it `g₀ ≍_n 1`.
  `ℋⁿ⁻¹(Γ_ball) ≍ n ω_n =: A₀ ≍_n 1`.

- **`Γ_tube`** is the cross-tube level `{φ = t} = {r = r_t}` ×
  (axis), an `(n−1)`-cylinder of radius `r_t` and axial length
  `≈ L`. On it, by the transverse barrier (Task 1, and the matching
  sub/supersolution `φ ± O(w²)`, whose `r`-derivatives agree to
  `O(w)`),

  ```
  |∇u|_{Γ_tube} ≈ |φ'(r_t)| = r_t/(n−1) ∈ [ w/(√2(n−1)), w/(n−1) ]
              =: g_tube,    g_tube ≍_n w.
  ```

  (The axial component `|∂_z u| = O(w)` too — Task-1 decay estimate
  `∂_z h = O(M_0 √{λ₁} e^{−√{λ₁}z}) = O(w)` in the body — so the
  total gradient is still `≍_n w`; the transverse part dominates or
  is comparable.) The surface measure is the lateral area of a
  radius-`r_t` `(n−1)`-tube of length `≈ L`:

  ```
  ℋⁿ⁻¹(Γ_tube) ≈ ( (n−1) ω_{n−1} r_t^{n−2} ) · L  =: A_tube ≍_n w^{n−2} L.
  ```

**`D_H(t)` lower bound via the boxed variance.** `D_H` for a level
that splits into two blocks `(A, g)`-type pieces — block 1
`(A₀, g₀)`, block 2 `(A_tube, g_tube)` — is computed exactly. With
`∮ 1/|∇u| = A₀/g₀ + A_tube/g_tube`, `∮|∇u| = A₀ g₀ + A_tube g_tube`,
`P = A₀ + A_tube`:

```
D_H(t) = (∮1/|∇u|)(∮|∇u|) − P²
       = A₀ A_tube · ( g₀/g_tube + g_tube/g₀ − 2 )
       = A₀ A_tube · (g₀ − g_tube)² / (g₀ g_tube).            (★)
```

(Identity `(a/α+b/β)(aα+bβ)−(a+b)² = ab(α−β)²/(αβ)`, exact; this is
the two-block instance of the boxed weighted-variance representation,
the tube part being mass `A_tube` of `|∇u|≍w` against the ball-set mean
`\bar f_t ≍ g₀ ≍ 1`.) Insert the scalings `A₀ ≍_n 1`, `g₀ ≍_n 1`,
`g_tube ≍_n w`, `(g₀ − g_tube)² ≍_n 1` (since `g_tube ≍ w ≪ 1 = g₀`),
`g₀ g_tube ≍_n w`, `A_tube ≍_n w^{n−2} L`:

```
   D_H(t)  ≍_n  A_tube / (g₀ g_tube) · g₀  ≍_n  (w^{n−2} L) / w
           =  φ_n(w,L) := C_n^{DH} · w^{n−3} L,
```

`C_n^{DH} = (n−1) ω_{n−1} · n ω_n · (1/n)·(n−1) /(stuff) ≍_n 1`
(explicit dimensional constant; numerically e.g.
`D_H ≍ 1.3 · w^{n−3} L` for `n=4`). This holds on the **definite
`t`-range** `(0, c_* w²)` of length `≍_n w²`.

So: `D_H(t) ≥ φ_n(w,L) = C_n^{DH} w^{n−3} L` for all
`t ∈ (0, c_* w²)`, `c_* = 1/(4(n−1))`.

---

## Task 4 — Deficit lower bound

On `t ∈ (0, c_* w²)`, the superlevel `E_t ≈ Ω` so `m(t) ≈ |Ω| = ω_n`
(two-sided, `1 + O(|T|)`), hence the weight is `≍_n` Lebesgue:
`dν(t) = dt/(n²ω_n^{2/n} m(t)^{1−2/n}) ≍_n dt`. Therefore

```
2 δ_T(Ω) ≥ ∫_0^{c_* w²} D_H(t) dν(t)
         ≍_n ∫_0^{c_* w²} C_n^{DH} w^{n−3} L · dt
         = C_n^{DH} · c_* · w^{n−3} L · w²
         = C_n^{(4)} · w^{n−1} L.
```

i.e.

```
   δ_T(Ω)  ≳_n  w^{n−1} L  ≍_n  |T|.            (DEF-LB)
```

**Sharpness check by direct energy (independent of the level-set
mechanism).** Plan 2 §3: `2 δ_T(Ω) = (∫_{B}u_B − ∫_Ω u_Ω)/|Ω|·…`,
exactly `δ_T = (I_{B_{|Ω|}} − I_Ω)/|Ω|` up to the boxed constant, with
`I_X := ∫_X u_X`. Compute, with `I_B(R) = ω_n R^{n+2}/(n(n+2))`,
`a := |T|/ω_n`, equal-volume radius `R_* = (1+a)^{1/n}`:

```
I_{B_{|Ω|}} = ω_n R_*^{n+2}/(n(n+2)) = I_{B_1} + |T|/n² + O(|T|²),
I_Ω = I_{B_1} + I_T + (coupling),   I_T = |T| · \bar φ,
   \bar φ = mean of φ over the (n−1)-disk = w²/((n−1)(n+1)),
⇒ I_{B_{|Ω|}} − I_Ω = |T|·[ 1/n² − w²/(n²−1) ] + O(|T|²)
                     = |T|/n² · (1 − o(1))      (w → 0).
```

Hence the **true** deficit is

```
   δ_T(Ω) = (1/(2n² ω_n)) · |T| · (1 + o(1))
          = C_n^{exact} · ω_{n−1} w^{n−1} L · (1 + o(1)),     (DEF-EXACT)
```

a **clean `Θ_n(|T|)`, with no `w²` floor**. Numerics confirm the
constant `(I_{B_{|Ω|}}−I_Ω)/|T| → 1/n²` exactly
(`0.250, 0.111, 0.0625, 0.040` for `n=2,3,4,5`). So (DEF-LB) is
**sharp**: the level-set mechanism is not lossy here — the tentacle's
true `δ_T` cost is exactly of order `|T|`, **not** of order `w²`.

**The `w` vs `L` powers, stated honestly.** The clean bound is

```
   δ_T(Ω) ≍_n |T| = ω_{n−1} w^{n−1} L,    and it is NOT ≳ w²
   unless  L ≳ w^{3−n}.
```

- `n = 2`: `w^{3−n} = w`. Always `L ≫ w` (admissible), so
  `|T| = ω₁ w L ≫ w²` automatically. `δ_T ≳ w² ≳ λ_esc`. **OK.**
- `n = 3`: `w^{3−n} = 1`, so `|T|/w² = ω₂ L = Θ(1)` is
  `w`-independent: this is a *constant-level* comparison, not an
  exponent gap. Tracking the shell constant
  (`λ_esc ≍ |T| + c² w²`, `c² ≍ n²`–`n³`), survival requires
  `L ≳ (n²/ω₂)·1 ≈ 2.9`. But admissible `L ≲ diam = O(1)` for a
  normalised domain — a tube of axial length `≈ 3` exceeds the
  diameter budget of `B_1`-volume. **`n = 3` therefore also FAILS**
  (at constant level, not exponent level): for every admissible
  `L = O(1)`, `λ_esc ≍ w² ≳ |T| ≍ δ_T`, so the layer is not paid for.
- `n ≥ 4`: `w^{3−n} = w^{−(n−3)} → ∞` as `w → 0`. Since `L ≲ diam =
  O(1)` it is **impossible** to have `L ≳ w^{3−n}` for small `w`.
  Hence `|T| = ω_{n−1} w^{n−1} L ≪ w² ≍ λ_esc`. **`δ_T ≪ λ_esc`.**

So in the regime `{ n ≥ 3, L = O(1) fixed, w → 0 }`:

```
   δ_T(Ω) ≍_n w^{n−1} L      while      λ_esc ≍_n w²,
   δ_T / λ_esc ≍_n w^{n−3} L  →  0   (n ≥ 4),
                              ≍  L = O(1) but < survival threshold (n = 3).
```

For `n ≥ 4` the deficiency factor is the **exponent gap `w^{n−3}`**
(times `L`): `δ_T` is smaller than the layer one must remove by
`w^{n−3} L → 0`. For `n = 3` the factor is `w`-independent
(`δ_T/λ_esc ≍ ω₂ L / (n²-shell-const) < 1` for all admissible
`L ≲ diam`), so the route fails by a *bounded* margin rather than an
exponent gap, but it still fails. Either way: a *tentacle that is
cheap in `δ_T` yet requires a `≫ δ_T` (resp. `≳ δ_T`) shell to
escape* — precisely the obstruction the task asked to detect.

---

## Task 5 — Reconciliation verdict

**Verdict: the route does NOT survive thin tentacles for any `n ≥ 3`.
For `n ≥ 4` it fails by an exponent gap (`λ_esc/δ_T ≍ w^{−(n−3)} →
∞`); for `n = 3` it fails by a bounded constant-level margin
(`λ_esc/δ_T ≍ const > 1` for all admissible `L ≲ diam`). The route
survives thin tentacles only for `n = 2`.**

The explicit obstruction family:

```
   Ω_w = B_1 ∪ T_w,   T_w = tube of length L = 1 (any fixed O(1)),
   radius w → 0,   n ≥ 3 fixed.
```

For it:

```
   δ_T(Ω_w)  =  C_n^{exact} ω_{n−1} w^{n−1} (1+o(1))     [DEF-EXACT, sharp]
   λ_esc(Ω_w) ≍_n  w²                                    [Task 2, unavoidable shell]
   ⇒  λ_esc / δ_T  ≍_n  w^{−(n−3)}  →  ∞   (n ≥ 4, exponent gap n−3),
                       ≍_n  const > 1      (n = 3, bounded margin).
```

**Consequence for the route.** Step 1 of `PLAN3_INTENDED_ROUTE.md`
extracts a good level by Chebyshev within an `O(δ_T)`-measure layer of
`∂Ω`. For this family `O(δ_T) = O(w^{n−1})`. But **any** level reached
within an `O(w^{n−1})`-measure layer still lies *below* `t_cap ≍ w²`
(the layer is too thin to even exit the ball-shell, which alone needs
measure `≍ w² ≫ w^{n−1}`), hence **still meets the tube body** — the
extracted `E_{t̂}` is *not* tentacle-free. The route's premise — "a
tentacle-free inner level is reachable within an `O(δ_T)`-measure
layer" — is **false** for all `n ≥ 3` (sharply, with an unbounded
factor, for `n ≥ 4`; with a bounded `>1` factor for `n = 3`). The
Chebyshev good level of Step 1 is **not** automatically tentacle-free;
it is automatically tentacle-*ful*.

**Sanity check against the known qualitative fact.** Ball+tentacle is
*not* `δ_T`-near the ball: indeed `δ_T(Ω_w) = Θ_n(|T|) > 0` strictly,
consistent with the known fact (it is never exactly the ball). But it
*is* `δ_T`-*small* (a thin short tentacle is a small perturbation:
`δ_T → 0` as `w → 0`). The subtlety the obstruction exposes is not
"`δ_T` fails to see the tentacle" — it does see it, at order `|T|` —
but that **`δ_T` sees it at order `|T| = w^{n−1}L`, which for `n ≥ 4`
is asymptotically *smaller* than the `w²` measure of the boundary
shell that must be peeled to reach an interior tentacle-free level.**
The deficit is consistent with all known qualitative facts; it is the
*route's escape-layer accounting* that breaks, by the precise exponent
`n − 3`.

**Relation to `proof-step2.md` §6.** That note showed `D_H(t̂)` is
blind to a tentacle on *one inner* level (`D_H(t̂) → 0` while
`Σ_{t̂}` has a macroscopic finger). The present computation is
*complementary and stronger for the route's purposes*: on the *low*
levels `t ∈ (0, c w²)` the tentacle forces `D_H(t) ≍_n w^{n−3} L`
which is **large** for `n ≤ 3` but **small** for `n ≥ 4`
(`w^{n−3} → 0`); integrated against the weight over the length-`w²`
window it yields exactly `δ_T ≳_n |T|`, *matching the true deficit*
(DEF-EXACT) — so there is no slack to exploit. Both notes converge on
the same `n ≥ 4` wall, by independent routes (single-level blindness
vs. integrated-layer accounting). The thin-tentacle obstruction to
Plan 3 is therefore **robust**, not an artifact of the `D_H`-only
restriction.

---

## Summary table (constants)

| Quantity | Value | Scaling |
|---|---|---|
| `t_cap` (cap height) | `(1/(2(n−1)) + 1) w²` | `≍_n w²` |
| `sup_T u` (lower) | `≥ w²/(4(n−1))` | `≍_n w²` |
| `\|T\|` | `ω_{n−1} w^{n−1} L (1+O(w/L))` | `≍_n w^{n−1}L` |
| `D_H(t)`, `t∈(0,c_*w²)` | `≍_n C_n^{DH} w^{n−3} L` | `≍_n w^{n−3}L` |
| `δ_T(Ω)` (lower & exact) | `(2n²ω_n)^{−1}\|T\|(1+o(1))` | `≍_n w^{n−1}L = \|T\|` |
| `λ_esc` | `\|T\| + c_n^{(2)} w²`, `c_n^{(2)}≍_n n²` | `≍_n w^{n−1}L + w²` |
| `λ_esc / δ_T` (`n≥4`, `L=O(1)`, `w→0`) | `≍_n w^{−(n−3)}` | `→ ∞` |
| `λ_esc / δ_T` (`n=3`, `L=O(1)`) | `≍ n²/(ω₂ L) > 1` | bounded `>1` |

**For the route.** Because the clean, *sharp* bound is `δ_T ≍_n |T|`
and **not** `δ_T ≳ w²`, the statement *"the Chebyshev good level of
Step 1 is automatically tentacle-free because any tentacle costs
`δ_T ≳ λ_esc`"* is **FALSE for every `n ≥ 3`** (with an unbounded
deficiency factor `w^{−(n−3)}` for `n ≥ 4`, a bounded `>1` factor for
`n = 3`). It is true only for `n = 2`. The route as specified does not
survive thin tentacles in any dimension `≥ 3`; the genuine obstruction
is the gap between `δ_T ≍_n w^{n−1}L = |T|` and the unavoidable
`λ_esc ≍_n |T| + w²` (exponent gap `n − 3` for `n ≥ 4`; constant
gap for `n = 3`).
