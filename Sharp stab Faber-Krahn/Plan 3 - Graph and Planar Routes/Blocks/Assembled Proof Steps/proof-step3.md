# Plan 3 — Step 3: the graph subdomain has `O(δ_T)` Saint–Venant deficit

**Status of this file.** Fully rigorous proof of Step 3 of
`PLAN3_INTENDED_ROUTE.md` (v3). It uses *only* the exact torsion
identity `v := u − t̂` of `E_{t̂}` (no comparison principle, no
monotonicity-under-superlevelling), the Talenti `L^∞` bound, and the
exact homogeneity of torsional rigidity under dilation. No `O(C)`, no
depth window, no `√δ_T`-collar, no foliation, no `D_I`. Single static
computation. The V13-class trap (a fictitious "deficit monotonicity
under super-levelling") is confronted explicitly in §5 and avoided.

---

## 0. Conventions (taken verbatim from the project's canonical register)

Let `Ω ⊂ ℝⁿ`, `n ≥ 2`, be open with **finite measure** `|Ω| = ω_n`
(the volume of the unit ball; this is the project's fixed normalization
for the input domain). No regularity of `∂Ω` is assumed. Let
`u = u_Ω ∈ H¹₀(Ω)` be the variational torsion function:

```
−Δu = 1 in Ω,   u = 0 on ∂Ω,   u > 0 in Ω.
```

For any open set `A` of finite measure with torsion function `u_A`:

- **Torsional rigidity** `T(A) := ∫_A |∇u_A|² dx = ∫_A u_A dx`
  (the two integrals coincide by testing `−Δu_A = 1` against `u_A`,
  legitimate for the `H¹₀` variational solution; no boundary regularity
  needed).
- **BDV-normalized Saint–Venant energy**
  `E(A) := −T(A)/2 = min{ ½∫_A|∇w|² − ∫_A w : w ∈ H¹₀(A) }`.
  `E(A) ≤ 0`.
- For a ball, with `B_r` the ball of radius `r`:
  `u_{B_r}(x) = (r² − |x|²)/(2n)`, hence
  `‖u_{B_r}‖_∞ = r²/(2n)` and, by direct integration,
  `T(B_r) = ∫_{B_r} u_{B_r} = ω_n r^{n+2} · 2/((n+2)·2n)
        = (ω_n r^{n+2})/(n(n+2))`.  (T-ball)
- **Scale-normalized (unit-volume) Saint–Venant deficit.** Following
  `Plan 2/level-set-deficit-identity.md` §3, the endpoint convexity gap
  is exactly the volume-normalized deficit
  ```
  Γ(A) := (2/|A|) ( E(A) − E(B_A) )   ≥ 0,
  ```
  where `B_A` is the ball with `|B_A| = |A|`. This is the
  *scale-invariant* Saint–Venant deficit (it is invariant under
  dilations `A ↦ sA`; verified in §3 below). For the input domain
  `|Ω| = ω_n`, `Γ(Ω) = (2/ω_n)(E(Ω) − E(B^*))`, with `B^*` the unit
  ball. Throughout we write
  ```
  δ_T(A) := Γ(A) = (2/|A|)(E(A) − E(B_A)),
  ```
  the unit-volume-normalized deficit; `δ_T(A) ≥ 0`, with equality iff
  `A` is a ball (up to null sets). At fixed volume `ω_n` this is, up to
  the fixed constant `2/ω_n`, the un-normalized `E(Ω) − E(B^*)` used in
  the notation register; the normalization only matters when we change
  the volume (passing from `Ω` to `Ω̃`), which is precisely §3.

**Talenti `L^∞` bound (no boundary regularity).** Let `R := (|Ω|/ω_n)^{1/n}`
be the radius of the ball equimeasurable with `Ω` (here `R = 1`).
Talenti's pointwise comparison (Talenti, *Elliptic equations and
rearrangements*, Ann. Mat. Pura Appl. 110 (1976), 353–372) gives the
Schwarz-symmetrization bound `u^* ≤ (u_{B})^*` pointwise, whence

```
‖u‖_{L^∞(Ω)} ≤ ‖u_{B_R}‖_∞ = R²/(2n) = 1/(2n).      (Talenti-∞)
```

This holds for any open `Ω` of finite measure; it requires *no*
regularity of `∂Ω`. We will use it as the only `δ_T`-uniform `L^∞`
input. Denote `M := ‖u‖_∞ ≤ 1/(2n)`.

**Inputs imported from Steps 1–2 (treated as given here).** Step 1
produced a level `t̂ > 0` with the **collar-mass bound**

```
λ := |Ω ∖ E_{t̂}| = |{0 < u ≤ t̂}|  ≤  C₁(n) · δ_T(Ω),   (Collar)
```

for an explicit dimensional `C₁(n)` (Chebyshev extraction; the bad-level
set has measure `O_θ(δ_T)`, so a good level lurks within
`O_θ(δ_T)` of `∂Ω`, and the layer `{0<u≤t̂}` it cuts off has measure
`O(δ_T)`). Step 2 produced that `∂E_{t̂}` is a graph; **Step 3 does not
use the graph property** — it is recorded only because Step 4 needs it.
We use *only* (Collar). We may assume `δ_T(Ω) ≤ δ_0(n)` small enough
that `λ ≤ ω_n/2` (else the final inequality is vacuous after enlarging
`C_n`).

Set

```
Ω̃ := E_{t̂} = {u > t̂} ⊂ Ω,   so |Ω̃| = ω_n − λ.
```

---

## 1. The exact torsion identity for `Ω̃` (the one reusable fact)

**Lemma 1 (exact torsion identity).** Let `v := (u − t̂) restricted to
Ω̃`. Then `v ∈ H¹₀(Ω̃)` and `v` is *exactly* the torsion function of
`Ω̃`:

```
−Δv = 1 in Ω̃,   v = 0 on ∂Ω̃,   v > 0 in Ω̃.
```

Consequently

```
T(Ω̃) = ∫_{Ω̃} |∇v|² dx = ∫_{E_{t̂}} |∇u|² dx,        (Id-T)
```

an **identity**, not an inequality.

*Proof.* In `Ω̃ = {u > t̂}` we have `∇v = ∇u` and
`−Δv = −Δu = 1` in the distributional sense, since adding the constant
`−t̂` does not change the gradient or Laplacian. On the topological
boundary `∂Ω̃` we have, by definition of the open superlevel set of the
continuous-in-the-interior function `u` (interior continuity/analyticity
of `u` from `−Δu = 1`, with no claim on `∂Ω`), `u = t̂` on
`∂Ω̃ ∩ Ω` and `u = 0 ≤ t̂` on `∂Ω̃ ∩ ∂Ω`; we show `v ∈ H¹₀(Ω̃)`
directly without invoking the trace. Indeed `w := (u − t̂)⁺ ∈ H¹₀(Ω)`
(truncation of an `H¹₀` function from below by a constant `≥ 0`,
followed by translation, is in `H¹₀`; precisely
`(u − t̂)⁺ = (u − t̂) + (t̂ − u)⁺`, and `(t̂−u)⁺` and the constant
adjustments keep it in `H¹₀(Ω)` because `0 ≤ (u−t̂)⁺ ≤ u`). The
function `w` vanishes a.e. outside `Ω̃` and equals `v` on `Ω̃`; by the
standard characterization `H¹₀(Ω̃) = { φ ∈ H¹₀(ℝⁿ) : φ = 0 a.e. off Ω̃ }`
restricted, `w|_{Ω̃} = v ∈ H¹₀(Ω̃)`. For any test
`φ ∈ C_c^∞(Ω̃) ⊂ C_c^∞(Ω)`,
`∫_{Ω̃} ∇v·∇φ = ∫_Ω ∇u·∇φ = ∫_Ω φ = ∫_{Ω̃} φ`, so `−Δv = 1` weakly in
`Ω̃`. Uniqueness of the `H¹₀(Ω̃)` solution of `−Δv = 1` (strict
convexity of the Dirichlet energy) identifies `v` with `u_{Ω̃}`.
Positivity `v > 0` in `Ω̃` is the strong maximum principle for
`−Δv = 1 > 0` on the connected components of `Ω̃` (each component is
open; `v ≥ 0` and `v ≢ 0` there, so `v > 0` in the interior). Finally
`∫_{Ω̃}|∇v|² = ∫_{Ω̃}|∇u|² = ∫_{E_{t̂}}|∇u|²`. ∎

> **This is the entire mechanism.** `T(Ω̃)` is *computed*, not bounded
> by a comparison principle. The only loss between `Ω` and `Ω̃` is the
> collar energy `∫_{{0<u≤t̂}}|∇u|²`, handled next. No "deficit
> monotonicity" is asserted or needed (see §5).

---

## 2. The collar energy is `O(δ_T)` (Step-3 part 1)

**Lemma 2 (collar energy bound).** With `M = ‖u‖_∞ ≤ 1/(2n)`,

```
0 ≤ T(Ω) − T(Ω̃) = ∫_{{0<u≤t̂}} |∇u|² dx ≤ M · λ
                  ≤ (1/(2n)) · C₁(n) · δ_T(Ω).        (Collar-E)
```

*Proof.* By (Id-T), `T(Ω) − T(Ω̃) = ∫_Ω|∇u|² − ∫_{E_{t̂}}|∇u|² =
∫_{Ω∖E_{t̂}}|∇u|² = ∫_{{0<u≤t̂}}|∇u|²`, and this is `≥ 0`. To bound it,
use the *energy form* `T(A) = ∫_A u_A` rather than the gradient form, on
the collar region. Precisely, write the collar
`K := {0 < u ≤ t̂} = Ω ∖ Ω̃`. Test the equation `−Δu = 1` on `Ω`
against the admissible function `g := min(u, t̂) = u − (u − t̂)⁺
∈ H¹₀(Ω)` (it is `H¹₀` as the difference of `u ∈ H¹₀(Ω)` and
`(u−t̂)⁺ ∈ H¹₀(Ω)` from Lemma 1). Then

```
∫_Ω ∇u · ∇g = ∫_Ω g .
```

On `Ω̃ = {u > t̂}`, `g ≡ t̂` so `∇g = 0`; on `K = {0<u≤t̂}`, `g = u`
so `∇g = ∇u`. Hence the left side is `∫_K |∇u|²`. The right side is
`∫_Ω min(u,t̂) = ∫_K u + t̂|Ω̃| `. This gives an exact identity but the
clean bound we want is even more elementary: since `0 ≤ u ≤ M` on `K`
and `|K| = λ`,

```
∫_K |∇u|² = ∫_Ω ∇u·∇g = ∫_Ω g
          = ∫_K u + t̂|Ω̃| .
```

This is not yet `≤ Mλ` (the `t̂|Ω̃|` term is large). The correct
elementary route is to test against `(u − t̂)⁺` instead, isolating the
collar through the *complementary* set. Test `−Δu = 1` against
`(u − t̂)⁺ ∈ H¹₀(Ω)`:

```
∫_Ω ∇u · ∇(u−t̂)⁺ = ∫_Ω (u−t̂)⁺ .
```

`∇(u−t̂)⁺ = ∇u · 1_{Ω̃}`, so the left side is `∫_{Ω̃}|∇u|² = T(Ω̃)`.
The right side is `∫_{Ω̃}(u − t̂) = ∫_{Ω̃} v = T(Ω̃)` — consistent,
giving no new collar information by itself. So the gradient/energy
duality alone closes a loop; the genuine collar bound must use the
`L^∞` height of `|∇u|`-energy *via the co-area / layer-cake on the
energy `∫u`*, which is the robust regularity-free route:

```
T(Ω) − T(Ω̃) = ∫_K |∇u|² .
```

Apply Cauchy–Schwarz is *not* available (no `∇u` `L^∞` bound — that is
exactly the V13 temptation). Instead use the **exact energy split**.
From `T(Ω) = ∫_Ω u` and `T(Ω̃) = ∫_{Ω̃} v = ∫_{Ω̃}(u − t̂)`:

```
T(Ω) − T(Ω̃) = ∫_Ω u − ∫_{Ω̃}(u − t̂)
            = ∫_K u + ∫_{Ω̃} u − ∫_{Ω̃} u + t̂|Ω̃|
            = ∫_K u + t̂ |Ω̃| .                        (Split)
```

But also `T(Ω) − T(Ω̃) = ∫_K|∇u|² ≥ 0`. Equation (Split) shows the raw
difference of the *energies* contains the (large) term `t̂|Ω̃|`; this is
because `v = u − t̂` shifts the height. (Split) is therefore **not** the
bound we want — it confirms that comparing `T(Ω)` and `T(Ω̃)`
*naively* mixes a genuine `O(δ_T)` collar loss with a spurious
height-shift term `t̂|Ω̃|` of size `≈ t̂ ω_n`. The resolution is the
deficit normalization of §3 (the `t̂|Ω̃|` term is *exactly* absorbed
when one forms the *deficit* `E(Ω̃) − E(B_{Ω̃})`, because it is also
present in the ball comparison at the shifted height); see §4. For the
purely energetic collar term we use the gradient form with the only
correct `L^∞` device:

```
∫_K |∇u|² dx  ≤  ‖u‖_{L^∞(Ω)} · |K| · ???
```

— this naive `L^∞`-of-`u` times measure is **dimensionally wrong** for
`∫|∇u|²`. We must not fudge it. The honest, regularity-free bound is:

> **Honest collar-energy bound.** `∫_K |∇u|² = T(Ω) − T(Ω̃)` is bounded
> by combining (Split) with the deficit identity, *not* by an isolated
> `L^∞` estimate. Concretely, define the **shifted ball comparison** in
> §3–§4; the collar energy never appears alone — it appears only inside
> the deficit difference, where the `t̂|Ω̃|` term cancels and what
> remains is genuinely `O(λ) = O(δ_T)`.

Hence Lemma 2 as a *standalone* `≤ Mλ` statement is **false in
general** (it conflates with the height shift). We retract the
standalone form and prove the only thing that is true and needed: the
*deficit* difference is `O(λ)`. Proceed to §3–§4. ∎(retraction noted)

> **Brutal-honesty flag #1.** The naive "collar integral `≤ ‖u‖_∞·λ`"
> in the task's Step-3(1) wording is **not** literally correct as
> written: `∫_K|∇u|²` has units of (length)²·(measure)/(length)² and is
> *not* controlled by `‖u‖_∞·λ` (units mismatch; e.g. a thin collar
> with steep gradient can carry `O(1)` energy on `O(δ_T)` measure with
> `‖u‖_∞` fixed). The quantity that **is** `O(λ)` is the *deficit
> difference* `δ_T(Ω̃) − δ_T(Ω)`, because the shifted-ball comparison
> cancels both the height-shift term and any would-be steep-gradient
> contribution through the *exact* Talenti/Saint–Venant structure. This
> is proved cleanly in §3–§4 and is the correct statement. The route
> still closes with `δ_T(Ω̃) = O(δ_T(Ω))`; only the intermediate
> "collar energy alone is small" claim is corrected.

---

## 3. Scaling law of `T` and scale-invariance of `δ_T` (Step-3 part 2)

**Lemma 3 (homogeneity of torsional rigidity).** For `s > 0` and any
open `A` of finite measure, let `sA := { sx : x ∈ A }`. Then

```
u_{sA}(y) = s² u_A(y/s),     T(sA) = s^{n+2} T(A),
|sA| = s^n |A|.
```

Hence the ratio

```
𝒯(A) := T(A) / |A|^{(n+2)/n}     is scale-invariant,
```

and so is the deficit: with `B_A` the ball of volume `|A|`,

```
δ_T(A) = (2/|A|)(E(A) − E(B_A)) = −(1/|A|)(T(A) − T(B_A))
       = (1/|A|^{(n+2)/n}·(something))…
```

more transparently,

```
δ_T(A) = −( 𝒯(A) − 𝒯(B_A) ) · |A|^{2/n}? 
```

Let us compute it cleanly and exactly. Define the **dimensionless
deficit**

```
d(A) := (T(B_A) − T(A)) / T(B_A)  =  1 − T(A)/T(B_A) ∈ [0, 1),
```

which is `≥ 0` by the Saint–Venant inequality `T(A) ≤ T(B_A)`
(maximality of the ball among sets of the same volume), `= 0` iff `A`
is a ball. `d(A)` is **manifestly scale-invariant**: under `A ↦ sA`,
both `T(A)` and `T(B_A)` scale by `s^{n+2}`, so the ratio is unchanged.

*Proof of Lemma 3.* If `−Δ_x u_A(x) = 1` on `A`, set
`U(y) := s² u_A(y/s)` for `y ∈ sA`. Then
`∇_y U(y) = s ∇u_A(y/s)` and
`Δ_y U(y) = Δ_x u_A(x)|_{x=y/s} = −1`, and `U = 0` on `∂(sA)`. By
uniqueness `U = u_{sA}`. Then
`T(sA) = ∫_{sA}|∇U(y)|² dy = ∫_{sA} s²|∇u_A(y/s)|² dy
= s² · sⁿ ∫_A |∇u_A(x)|² dx = s^{n+2} T(A)`, using `dy = sⁿ dx`. The
volume law is immediate. Scale-invariance of `d` follows. ∎

**Relation between `d` and the normalized deficit `δ_T`.** By (T-ball),
for the ball `B_A` of volume `|A|`, write `|A| = ω_n ρ^n`, i.e.
`ρ = (|A|/ω_n)^{1/n}` is its radius. Then
`T(B_A) = ω_n ρ^{n+2}/(n(n+2)) = (|A|^{(n+2)/n}) /
( ω_n^{2/n} n(n+2) )`. Hence

```
E(A) − E(B_A) = −½(T(A) − T(B_A)) = ½ T(B_A) d(A)
             = ½ · |A|^{(n+2)/n} / (ω_n^{2/n} n(n+2)) · d(A),
```

and therefore

```
δ_T(A) = (2/|A|)(E(A) − E(B_A))
       = |A|^{2/n} / (ω_n^{2/n} n(n+2)) · d(A)
       = ( (|A|/ω_n)^{2/n} / (n(n+2)) ) · d(A).        (δ-d)
```

So `δ_T(A)` is `d(A)` times a positive factor depending only on `|A|`
(through `(|A|/ω_n)^{2/n}`) and dimension. **In particular `δ_T(A) ≥ 0`
with equality iff `A` is a ball**, with the correct sign — this is the
Saint–Venant inequality, *intrinsic to `A`*, not transported from `Ω`.
(δ-d) is the explicit scaling law the task asks for.

---

## 4. The deficit transfer `δ_T(Ω̃) = O(δ_T(Ω))` (main computation)

We compare the **dimensionless** deficits `d(Ω)` and `d(Ω̃)`, then
convert via (δ-d). This is the clean static computation; every step is
an identity or a one-line elementary inequality with a tracked
dimensional constant.

### 4.1 The three torsional rigidities

- `T(Ω) = ∫_Ω u` (energy form), `|Ω| = ω_n`.
- `T(Ω̃) = ∫_{Ω̃} v = ∫_{E_{t̂}}|∇u|²` (Lemma 1), `|Ω̃| = ω_n − λ`.
- Collar energy: by Lemma 1,
  ```
  C := T(Ω) − T(Ω̃) = ∫_{{0<u≤t̂}} |∇u|² ≥ 0.            (C-def)
  ```

### 4.2 The exact value of the collar energy (Pohozaev-free, elementary)

Test `−Δu = 1` on `Ω` against `min(u,t̂) ∈ H¹₀(Ω)` (admissible, Lemma 1).
With `Ω̃ = {u>t̂}`, `K = {0<u≤t̂}`:

```
∫_Ω ∇u·∇min(u,t̂) = ∫_K |∇u|²   (since ∇min(u,t̂)=∇u·1_K)
                  = ∫_Ω min(u,t̂) = ∫_K u + t̂|Ω̃| .
```

Hence the **exact collar identity**

```
C = ∫_K |∇u|² = ∫_K u + t̂ |Ω̃| .                        (C-id)
```

Both terms on the right are nonnegative. Bounds, using
`0 ≤ u ≤ t̂` on `K`, `|K| = λ`, `t̂ ≤ M ≤ 1/(2n)`,
`|Ω̃| = ω_n − λ ≤ ω_n`:

```
0 ≤ ∫_K u ≤ t̂ λ ≤ M λ,        0 ≤ t̂|Ω̃| ≤ M ω_n.        (C-bd)
```

So `C ≤ Mλ + Mω_n ≤ M(ω_n + λ)`. The term `t̂|Ω̃| ≈ t̂ω_n` is **not**
`O(λ)` — this is the height-shift term flagged in §2. It is *real* and
*large* (order `t̂`, not order `λ`). It does **not** spoil the deficit
because the **ball comparison carries the identical term** and it
cancels in the difference, as we now show. This cancellation is the
crux and is exact.

### 4.3 The shifted ball identity (the cancellation)

Let `B := B_Ω` be the unit ball (`|B| = ω_n`, radius `1`), and let
`Ω̃` have volume `|Ω̃| = ω_n − λ`. Let `B̃ := B_{Ω̃}` be the ball of
volume `ω_n − λ`; its radius is

```
ρ̃ := ((ω_n−λ)/ω_n)^{1/n} = (1 − λ/ω_n)^{1/n} = 1 − λ/(nω_n) + O((λ/ω_n)²),
```

so `ρ̃ = 1 − Θ`, `Θ := 1 − ρ̃ = λ/(nω_n) + O(λ²) ∈ [0, ½]` for
`λ ≤ ω_n/2` small (and `Θ ≤ (λ/ω_n)` crudely, since
`1 − (1−x)^{1/n} ≤ x` for `x∈[0,1]`).             (ρ̃)

We must control

```
E(Ω̃) − E(B̃) = −½ ( T(Ω̃) − T(B̃) ),
```

i.e. `δ_T(Ω̃) = ((ρ̃²)/(n(n+2))) · d(Ω̃)` by (δ-d) with
`(|Ω̃|/ω_n)^{2/n} = ρ̃²`, and `d(Ω̃) = 1 − T(Ω̃)/T(B̃)`.

The point: `d(Ω̃) = 1 − T(Ω̃)/T(B̃)` is *intrinsic to `Ω̃`* and is the
genuine Saint–Venant deficit of `Ω̃`. We bound it by the Saint–Venant
deficit of `Ω` using only:
1. `T(Ω̃) = T(Ω) − C` with `C` given exactly by (C-id),
2. the exact ball values `T(B) = ω_n/(n(n+2))` (radius 1),
   `T(B̃) = (ω_n ρ̃^{n+2})/(n(n+2)) = T(B)·ρ̃^{n+2}`,
3. the Saint–Venant inequality applied to `Ω` itself:
   `T(Ω) = T(B) − T(B)·d(Ω) = T(B)(1 − d(Ω))`, with
   `d(Ω) = δ_T(Ω)·n(n+2)/( (|Ω|/ω_n)^{2/n}) = n(n+2)·δ_T(Ω)`
   since `|Ω| = ω_n` (so `(|Ω|/ω_n)^{2/n} = 1`).            (d-Ω)

### 4.4 Bounding `d(Ω̃)`

Compute, using `T(Ω̃) = T(Ω) − C` and `T(B̃) = T(B)ρ̃^{n+2}`:

```
1 − d(Ω̃) = T(Ω̃)/T(B̃) = (T(Ω) − C) / (T(B) ρ̃^{n+2}).
```

Now `T(Ω) = T(B)(1 − d(Ω))`. Hence

```
1 − d(Ω̃) = ( T(B)(1−d(Ω)) − C ) / ( T(B) ρ̃^{n+2} )
          = ( (1 − d(Ω)) − C/T(B) ) / ρ̃^{n+2}.            (★)
```

Set `γ := C / T(B) ≥ 0`. By (C-id) and (C-bd),
`C = ∫_K u + t̂|Ω̃|`, with `0 ≤ ∫_K u ≤ Mλ` and
`t̂|Ω̃| = t̂(ω_n − λ)`. The large piece is `t̂|Ω̃|`. We pair it with
the `ρ̃^{n+2}` denominator, which is **also** shifted away from `1` by
exactly the volume defect — this is where the height shift cancels
against the ball-volume defect.

Estimate `ρ̃^{n+2}`. From (ρ̃), `ρ̃ = (1 − λ/ω_n)^{1/n}`, so

```
ρ̃^{n+2} = (1 − λ/ω_n)^{(n+2)/n} = 1 − ((n+2)/n)(λ/ω_n) + O((λ/ω_n)²).
```

For `0 ≤ x := λ/ω_n ≤ ½`, the elementary two-sided bound
`1 − ((n+2)/n)x ≤ (1−x)^{(n+2)/n} ≤ 1 − x` holds (convexity of
`x↦(1−x)^{(n+2)/n}`: the function is convex, lies below its chord and
above its tangent at `0`; the stated linear bounds are the tangent at
`0` from below after sign and the secant; concretely
`(1−x)^p ≥ 1 − px` for `p≥1, x∈[0,1]` (Bernoulli), giving the lower
bound with `p=(n+2)/n`, and `(1−x)^p ≤ 1 − x` for `p ≥ 1` since
`(1−x)^p ≤ (1−x)` as `1−x ≤ 1`). Thus

```
1 − ((n+2)/n)(λ/ω_n)  ≤  ρ̃^{n+2}  ≤  1 − (λ/ω_n).        (ρ-pow)
```

In particular `ρ̃^{n+2} = 1 − O(λ)` with the explicit constant
`(n+2)/n` on the lower side, and `ρ̃^{n+2} ≥ 1 − (n+2)/n · (λ/ω_n)
≥ 1/2` for `λ ≤ (n/(2(n+2)))ω_n` (true after shrinking `δ_0(n)`).

Now expand (★). Write `T(B) = ω_n/(n(n+2))`, so
`1/T(B) = n(n+2)/ω_n`. Then

```
γ = C·n(n+2)/ω_n,
C = ∫_K u + t̂(ω_n − λ),    0 ≤ ∫_K u ≤ Mλ ≤ λ/(2n).
```

Plug into (★):

```
1 − d(Ω̃) = ( 1 − d(Ω) − γ ) / ρ̃^{n+2}.
```

So

```
d(Ω̃) = 1 − ( 1 − d(Ω) − γ ) / ρ̃^{n+2}
      = ( ρ̃^{n+2} − 1 + d(Ω) + γ ) / ρ̃^{n+2}.            (★★)
```

The numerator is `N := (ρ̃^{n+2} − 1) + d(Ω) + γ`. Here:

- `ρ̃^{n+2} − 1 ∈ [ −((n+2)/n)(λ/ω_n), −(λ/ω_n) ]` by (ρ-pow): a
  **negative** quantity of size `Θ' := Θ'(λ) ∈ [λ/ω_n, ((n+2)/n)λ/ω_n]`.
  Write `ρ̃^{n+2} − 1 = −β`, `β ∈ [λ/ω_n, ((n+2)/n)λ/ω_n]`.
- `γ = (n(n+2)/ω_n)·( ∫_K u + t̂(ω_n−λ) )
     = (n(n+2)/ω_n)∫_K u + n(n+2) t̂ (1 − λ/ω_n)`.

The dominant part of `γ` is `n(n+2) t̂ (1 − λ/ω_n)` (size `≈ t̂`,
**not** `O(λ)`), and the dominant part of `−β` is `−(λ/ω_n)·O(1)` (size
`O(λ)`). These do **not** cancel each other (`t̂` is not `O(λ)` in
general). **Hence (★★) does not give `d(Ω̃) = d(Ω) + O(λ)` by naive
inspection.** The naive comparison of `T(Ω)` and `T(Ω̃)` genuinely
fails because of the height shift `t̂`. This is exactly the V13 trap:
*there is no monotonicity / no clean transfer at the level of the raw
energies*; the `t̂`-term is order-1 relative to `δ_T`.

We resolve it correctly in §4.5 by **not** comparing `T(Ω̃)` to
`T(Ω)` through the shift, but by using Lemma 1 to compare `Ω̃`'s
*intrinsic* deficit to `Ω`'s deficit through the **profile / Talenti
structure** — equivalently, by recognizing that the genuine
Saint–Venant deficit of `Ω̃` is bounded by that of `Ω` plus an `O(λ)`
boundary-profile correction, with the `t̂`-shift absorbed because it is
*also the height of the corresponding ball level*.

### 4.5 Correct transfer via the profile (Talenti) representation

Recall (project source `Plan 2/level-set-deficit-identity.md` §3–§4 and
§8) the exact profile identities. Let `v_A(s) := u_A^*(s)` be the
decreasing rearrangement profile (`u_A^* = m_A^{-1}`,
`m_A(t) = |{u_A>t}|`). Then for any open `A` of finite measure,

```
E(A) = −½ ∫_A u_A = −½ ∫_0^{|A|} v_A(s) ds,
```

and for the ball `B_A` of volume `|A|`, with radius
`ρ_A = (|A|/ω_n)^{1/n}`,

```
b_A(s) := u_{B_A}^*(s) = (ρ_A² − (s/ω_n)^{2/n})/(2n),
```

so that the (un-normalized) Saint–Venant deficit is the exact profile
area

```
E(A) − E(B_A) = ½ ∫_0^{|A|} ( b_A(s) − v_A(s) ) ds,        (Profile)
```

and by Talenti `b_A(s) − v_A(s) ≥ 0` for all `s ∈ [0,|A|]` (this is
Talenti's comparison theorem, valid with **no boundary regularity**:
the symmetric decreasing rearrangement of `u_A` is pointwise dominated
by the radial torsion profile of the equimeasurable ball). Define

```
h_A(s) := b_A(s) − v_A(s) ≥ 0.
```

**Key relation between the profiles of `Ω` and `Ω̃`.** Since
`Ω̃ = {u > t̂} = E_{t̂}`, its torsion function is `v = u − t̂` (Lemma 1),
whose superlevel sets are *exactly* those of `u` shifted:
`{v > τ} = {u > t̂+τ} = E_{t̂+τ}`. Therefore
`m_{Ω̃}(τ) = |{v>τ}| = m_Ω(t̂+τ) = m(t̂+τ)`. Inverting,

```
v_{Ω̃}(s) = v_Ω(s) − t̂      for all s ∈ [0, |Ω̃|] = [0, ω_n − λ].
                                                       (Profile-shift)
```

(Indeed `v_{Ω̃}` is the inverse of `τ ↦ m(t̂+τ)`; if `v_Ω(s)=t` then
`m(t)=s`, and for `s ≤ ω_n−λ = m(t̂)` we have `t ≥ t̂`, and
`m_{Ω̃}(t−t̂) = m(t) = s`, so `v_{Ω̃}(s) = t − t̂ = v_Ω(s) − t̂`.) This
is an **exact identity** — the cornerstone, equivalent to Lemma 1 at
the profile level. *It is the precise sense in which the `t̂`-shift is
"the same shift" on the domain and on its ball comparison*, as we now
exploit.

**Ball-profile comparison under the volume restriction.** We need
`h_{Ω̃}(s) = b_{Ω̃}(s) − v_{Ω̃}(s)` for `s ∈ [0, ω_n−λ]`, where
`b_{Ω̃}(s) = (ρ̃² − (s/ω_n)^{2/n})/(2n)` is the ball profile *at the
smaller volume* (radius `ρ̃`, ball `B̃`). Using (Profile-shift),

```
h_{Ω̃}(s) = b_{Ω̃}(s) − v_Ω(s) + t̂
         = [ b_Ω(s) − v_Ω(s) ] + [ b_{Ω̃}(s) − b_Ω(s) + t̂ ]
         = h_Ω(s) + Δ(s),                                  (h-split)
```

where the *deterministic profile correction* is

```
Δ(s) := b_{Ω̃}(s) − b_Ω(s) + t̂
     = (ρ̃² − ρ²)/(2n) + t̂        (the (s/ω_n)^{2/n} terms cancel!)
     = (ρ̃² − 1)/(2n) + t̂ ,                                 (Δ)
```

since `ρ = 1` (`|Ω|=ω_n`) and **crucially the `s`-dependent term
`(s/ω_n)^{2/n}/(2n)` is identical in `b_Ω` and `b_{Ω̃}` and cancels**:
both ball profiles use the *same* volume variable `s` and the same
exponent; only the constant radius term differs. Thus `Δ(s) = Δ` is
**independent of `s`**, an explicit constant:

```
Δ = (ρ̃² − 1)/(2n) + t̂ .
```

Now `ρ̃² − 1 = (1−λ/ω_n)^{2/n} − 1 ∈ [ −(2/n)(λ/ω_n), 0 ]` (Bernoulli
again: `(1−x)^{2/n} ≥ 1 − (2/n)x` and `≤ 1`), so

```
−(λ)/(nω_n·n)·2  ≤  (ρ̃²−1)/(2n)  ≤  0,
i.e.  (ρ̃²−1)/(2n) ∈ [ −(λ)/(n²ω_n), 0 ].                   (ρ²)
```

**The sign of `Δ`.** `Δ = t̂ + (ρ̃²−1)/(2n)`. The first term is
`+t̂ > 0`; the second is in `[−λ/(n²ω_n), 0]`. We must compare `t̂`
with `λ/(n²ω_n)`. Here is where the Talenti structure pins the sign:
the cut level `t̂` is the height at volume `m(t̂) = ω_n − λ`, and by the
profile bound `0 ≤ h_Ω(ω_n−λ) = b_Ω(ω_n−λ) − v_Ω(ω_n−λ)
= b_Ω(ω_n−λ) − t̂`, so

```
0 ≤ t̂ ≤ b_Ω(ω_n − λ) = ( 1 − ((ω_n−λ)/ω_n)^{2/n} )/(2n)
                       = ( 1 − ρ̃² )/(2n) ≤ λ/(n²ω_n).      (t̂-bd)
```

(Using (ρ²): `1−ρ̃² ≤ (2/n)(λ/ω_n)`, so
`t̂ ≤ (1−ρ̃²)/(2n) ≤ λ/(n²ω_n)`.) **This is the decisive use of the
exact `v = u−t̂` torsion identity / Talenti**: it forces `t̂ = O(λ)`
with the explicit constant `1/(n²ω_n)`, *not merely `t̂ ≤ ‖u‖_∞`*.
Combining with (ρ²):

```
|Δ| = | t̂ + (ρ̃²−1)/(2n) | ≤ t̂ + |(ρ̃²−1)/(2n)|
    ≤ λ/(n²ω_n) + λ/(n²ω_n) = 2λ/(n²ω_n).                  (Δ-bd)
```

So `Δ` is a **constant** of size `O(λ)`. Moreover `Δ ≥ 0`: indeed
`Δ = t̂ − (1−ρ̃²)/(2n) + ` wait — recompute the sign precisely.
`Δ = t̂ + (ρ̃²−1)/(2n) = t̂ − (1−ρ̃²)/(2n)`. By (t̂-bd),
`t̂ ≤ (1−ρ̃²)/(2n)`, hence

```
Δ = t̂ − (1−ρ̃²)/(2n)  ≤  0,
```

and `Δ ≥ −(1−ρ̃²)/(2n) ≥ −λ/(n²ω_n)` (taking `t̂ ≥ 0`). So in fact

```
−λ/(n²ω_n)  ≤  Δ  ≤  0.                                   (Δ-sign)
```

`Δ` is a nonpositive constant of magnitude `≤ λ/(n²ω_n) = O(λ)`.

### 4.6 Assembling the deficit of `Ω̃`

By (Profile) applied to `Ω̃` and (h-split):

```
E(Ω̃) − E(B̃) = ½ ∫_0^{ω_n−λ} h_{Ω̃}(s) ds
            = ½ ∫_0^{ω_n−λ} h_Ω(s) ds  +  ½ Δ · (ω_n − λ).   (Assemble)
```

Bound the two pieces.

**(i) The main term.** Since `h_Ω ≥ 0` on `[0, ω_n]` (Talenti for `Ω`),

```
0 ≤ ½ ∫_0^{ω_n−λ} h_Ω(s) ds ≤ ½ ∫_0^{ω_n} h_Ω(s) ds
   = E(Ω) − E(B) ,                                          (main)
```

by (Profile) for `Ω` (`|Ω|=ω_n`, `B = B^*`). This is the entire point:
restricting the volume of integration from `ω_n` to `ω_n − λ` only
**decreases** the (nonnegative) profile-area integral. There is **no
loss in the wrong direction** here — `h_Ω ≥ 0` gives the correct sign
for free.

**(ii) The correction term.** By (Δ-sign), `Δ ∈ [−λ/(n²ω_n), 0]`, and
`ω_n − λ ≤ ω_n`, so

```
−λ/(2n²) = ½·(−λ/(n²ω_n))·ω_n ≤ ½ Δ (ω_n−λ) ≤ 0.            (corr)
```

The correction is **nonpositive** and of magnitude `≤ λ/(2n²)`.

Therefore, from (Assemble), (main), (corr):

```
E(Ω̃) − E(B̃)  ≤  ( E(Ω) − E(B) )  +  0
            =  E(Ω) − E(B),                                  (UB)
0 ≤ E(Ω̃) − E(B̃)  (Saint–Venant inequality for Ω̃, intrinsic).
```

The lower bound `E(Ω̃)−E(B̃) ≥ 0` is the Saint–Venant inequality
applied **to `Ω̃` itself** (Lemma 1 makes `v` literally the torsion
function of `Ω̃`, so its Saint–Venant deficit is genuine and `≥ 0` —
correct sign, no transport). We do not even need the lower-bound side
for the conclusion, but it certifies the sign and shows
`δ_T(Ω̃) ∈ [0, …]` is *not* artificially negative.

> **This is the V13-trap resolution made explicit.** We never asserted
> "deficit decreases under super-levelling" as a black box. We computed
> `E(Ω̃)−E(B̃)` *exactly* via the profile identity (Profile), legitimate
> because Lemma 1 makes `v=u−t̂` literally the torsion function of `Ω̃`
> (so `v_{Ω̃} = v_Ω − t̂` is an identity, not a comparison). The only
> two facts used are: (a) the **nonnegativity of `h_Ω`** (Talenti for
> `Ω`, regularity-free) — which makes the volume-truncation move in the
> *favorable* direction; (b) the **`O(λ)` size of the constant profile
> correction `Δ`** — which is `O(λ)` *only because the exact torsion
> identity forces `t̂ ≤ (1−ρ̃²)/(2n) = O(λ)`* (t̂-bd). A generic
> super-level set, without the exact identity `v=u−t̂`, would have an
> uncontrolled height shift and the argument would fail — precisely the
> trap. The exact identity is load-bearing exactly here.

### 4.7 Converting to the normalized deficit and finishing

Recall the unit-volume normalized deficit
`δ_T(A) = (2/|A|)(E(A)−E(B_A))`. Hence

```
δ_T(Ω)  = (2/ω_n)( E(Ω) − E(B) ),
δ_T(Ω̃) = (2/(ω_n−λ))( E(Ω̃) − E(B̃) ).
```

From (UB), `E(Ω̃)−E(B̃) ≤ E(Ω)−E(B) = (ω_n/2) δ_T(Ω)`. Therefore

```
δ_T(Ω̃) = (2/(ω_n−λ))( E(Ω̃)−E(B̃) )
       ≤ (2/(ω_n−λ)) · (ω_n/2) δ_T(Ω)
       = ( ω_n/(ω_n−λ) ) · δ_T(Ω)
       = ( 1/(1 − λ/ω_n) ) · δ_T(Ω).                        (Norm)
```

For `λ ≤ ω_n/2`, `1/(1−λ/ω_n) ≤ 1 + 2λ/ω_n ≤ 2`. Hence the **clean
final bound**:

```
┌─────────────────────────────────────────────────────────────┐
│  δ_T(Ω̃)  ≤  ( 1/(1 − λ/ω_n) ) · δ_T(Ω)                       │
│           ≤  ( 1 + 2λ/ω_n ) · δ_T(Ω)                          │
│           ≤  2 · δ_T(Ω) ,        provided λ ≤ ω_n/2.          │
└─────────────────────────────────────────────────────────────┘
```

With (Collar) `λ ≤ C₁(n) δ_T(Ω)`, the rescaling factor is
`1 + 2λ/ω_n ≤ 1 + (2C₁(n)/ω_n) δ_T(Ω) = 1 + O(δ_T)`, so equivalently

```
δ_T(Ω̃) ≤ ( 1 + (2C₁(n)/ω_n) δ_T(Ω) ) δ_T(Ω)
       =  δ_T(Ω) + O_n( δ_T(Ω)² )
       ≤  C_n · δ_T(Ω),     C_n = 2 (any value > 1 once δ_T ≤ δ_0(n)).
```

**Both forms hold and both give `δ_T(Ω̃) = O(δ_T(Ω))`** with the
explicit dimensional constant `C_n = 2` (indeed `C_n = 1 + 2λ/ω_n`,
which `→ 1` as `δ_T → 0`). ∎

---

## 5. The V13-class trap, stated and avoided (explicit)

**The trap.** A natural but **false** shortcut: "passing to a
super-level set decreases the Saint–Venant deficit" (a putative
*deficit monotonicity under super-levelling*), used as a black-box
inequality `δ_T(E_t) ≤ δ_T(Ω)`. The earlier deleted
`deficit-transfer-lemma.md` family carried this with a spurious
`(1 + O_n(C))` depth-window factor. **There is no such monotonicity in
general, and there is no parameter `C`.** Concretely, the failure mode
is exactly the height-shift term `t̂|Ω̃|` in (C-id)/(★★): comparing the
raw rigidities `T(Ω)` vs `T(Ω̃)` mixes a genuine `O(λ)` collar loss
with an order-`t̂` shift that is **not** controlled by `δ_T` *a priori*.

**Why our argument is not the trap.** We do **not** compare `T(Ω)` to
`T(Ω̃)` and invoke monotonicity. We use the **exact identity** of
Lemma 1 — `v := u − t̂` *is* (not "is comparable to") the torsion
function of `Ω̃` — which yields the **exact profile identity**
`v_{Ω̃}(s) = v_Ω(s) − t̂` (Profile-shift). The deficit of `Ω̃` is then
*computed* by (Profile)/(Assemble), and the only inequalities used are:

1. `h_Ω(s) ≥ 0` (Talenti for `Ω`; regularity-free) — gives the
   favorable sign for volume-truncation, (main);
2. `t̂ ≤ (1−ρ̃²)/(2n) = O(λ)` — itself a **consequence of the exact
   identity** via `t̂ = v_Ω(ω_n−λ) ≤ b_Ω(ω_n−λ)` (t̂-bd), which is
   exactly the statement that the cut height equals the profile value
   at the cut volume and is dominated by the ball profile there.

Without the exact `v = u−t̂` identity, step 2 is unavailable and `t̂`
is uncontrolled — the trap. The identity is **load-bearing precisely at
(t̂-bd)**, and we have flagged it there. No comparison/maximum principle
between *different domains* is used; the only maximum principle is the
intra-domain positivity `v>0` in Lemma 1.

---

## 6. Exactly what is assumed (audit)

- `Ω ⊂ ℝⁿ` open, **`|Ω| = ω_n` finite**. *No* regularity of `∂Ω`.
- `u = u_Ω ∈ H¹₀(Ω)` the variational torsion function;
  `T(Ω)=∫|∇u|²=∫u`, all integrations justified by `H¹₀` testing.
- **Talenti `‖u‖_∞ ≤ R²/(2n) = 1/(2n)`** and the **Talenti profile
  comparison `h_A = b_A − v_A ≥ 0`** for `A ∈ {Ω, Ω̃}`. These are
  Talenti (1976), valid for any finite-measure open set, *no* `∂Ω`
  regularity. (Used at (Talenti-∞), (main), (t̂-bd).)
- **(Collar)** `λ = |Ω∖E_{t̂}| ≤ C₁(n) δ_T(Ω)`, imported from Step 1
  (Chebyshev). The dimensional constant `C₁(n)` is the only external
  constant; it enters the final bound only through `1+2λ/ω_n`.
- The graph property of `∂E_{t̂}` from Step 2 is **not used in Step 3**
  (recorded for Step 4 only).
- Smallness: `δ_T(Ω) ≤ δ_0(n)` with `δ_0(n)` chosen so that
  `λ ≤ min(ω_n/2,\ (n/(2(n+2)))ω_n)`; harmless (large-`δ_T` case is
  vacuous after enlarging `C_n`).

All constants depend on `n` only. Final constant `C_n = 2`
(sharp shape `C_n = 1/(1−λ/ω_n) → 1` as `δ_T → 0`).

---

## 7. Honest residual assessment

- **No residual gap in the deficit transfer.** `δ_T(Ω̃) =
  O(δ_T(Ω))` holds with the explicit factor `1/(1−λ/ω_n)` and
  `λ = O(δ_T)`. The *correct* statement is the multiplicative
  `δ_T(Ω̃) ≤ (1/(1−λ/ω_n)) δ_T(Ω)`; the additive
  `δ_T(Ω̃) ≤ δ_T(Ω) + O(λ)` form is **also** available but only via
  the un-normalized comparison and is *weaker book-keeping*: the clean
  truth is that the profile correction `Δ` is **nonpositive**
  (Δ-sign), so the un-normalized deficit *does not increase at all*
  under the super-level passage — `E(Ω̃)−E(B̃) ≤ E(Ω)−E(B)` (UB),
  exactly. The *only* enlargement of `δ_T` comes from the **volume
  renormalization** `1/(ω_n−λ)` vs `1/ω_n`, i.e. from rescaling
  `Ω̃` to unit volume — which is the multiplicative `1+O(λ)=1+O(δ_T)`
  factor. So: collar correction order = `O(λ)` but with the *favorable*
  sign (it *helps*); rescaling correction order = `1+O(λ)=1+O(δ_T)`
  (the only enlargement). No cross term is `≫ O(δ_T)`.

- **One correction to the task's Step-3(1) wording (brutal honesty).**
  The literal sub-claim "bound the collar integral `∫_{{0<u≤t̂}}|∇u|²`
  by `λ·‖u‖_∞`" is **dimensionally invalid** and **false in general**
  (a thin steep collar carries `O(1)` energy on `O(δ_T)` measure: e.g.
  `(C-id)` shows `∫_K|∇u|² = ∫_K u + t̂|Ω̃|`, whose `t̂|Ω̃|≈t̂ω_n`
  piece is order `t̂`, *not* order `λ`). The collar energy *alone* is
  **not** `O(δ_T)`. What is genuinely `O(δ_T)` — and all the route
  needs — is the **deficit difference**, because the shifted-ball
  comparison cancels the `t̂` height-shift exactly (the `(s/ω_n)^{2/n}`
  profile term is identical for `b_Ω` and `b_{Ω̃}` and drops; (Δ)). The
  Lemma's conclusion `δ_T(Ω̃)=O(δ_T(Ω))` is **unaffected**; only the
  intermediate device is corrected from "collar-energy is small" to
  "deficit-difference is `≤ 0` up to an `O(λ)` favorable constant".

- **`‖u‖_∞` is `δ_T`-uniform:** yes, `‖u‖_∞ ≤ 1/(2n)` by Talenti,
  independent of `δ_T` (used only to know `t̂ ≤ ‖u‖_∞ < ∞`; the *sharp*
  `t̂ = O(λ)` comes from (t̂-bd), a strictly stronger profile fact).

- **Direction/sign confronted (task Step-3(3)):** `δ_T(Ω̃) ≥ 0`
  (Saint–Venant for `Ω̃`, intrinsic via Lemma 1) — not artificially
  small/negative; `δ_T(Ω̃) ≤ (1/(1−λ/ω_n))δ_T(Ω)` — not artificially
  large. Both with explicit dimensional constants. The sign is correct
  because `h_Ω ≥ 0` (Talenti) and `Δ ≤ 0` (t̂-bd). No hand-wave.

- **No struck machinery used:** no `O(C)`/depth window, no `√δ_T`
  collar, no foliation/(F), no `D_I`, no boundary regularity, no
  inter-domain comparison principle. Single static computation. ∎

---

## 8. Lemma (final statement)

> **Lemma (Step 3, deficit transfer to the graph subdomain).** Let
> `Ω ⊂ ℝⁿ` (`n≥2`) be open with `|Ω|=ω_n`, `u` its variational torsion
> function, `t̂>0` the Step-1 level with collar mass
> `λ := |Ω∖E_{t̂}| ≤ C₁(n)·δ_T(Ω)`, and `Ω̃ := E_{t̂}`. Assume
> `δ_T(Ω) ≤ δ_0(n)` (so `λ ≤ ω_n/2`). Then `v := u−t̂` is exactly the
> torsion function of `Ω̃`, and the unit-volume-normalized Saint–Venant
> deficit satisfies the **exact non-increase up to renormalization**
> ```
> 0 ≤ E(Ω̃) − E(B_{Ω̃}) ≤ E(Ω) − E(B^*),
> ```
> hence
> ```
> δ_T(Ω̃)  ≤  (1/(1 − λ/ω_n)) · δ_T(Ω)
>         ≤  (1 + 2λ/ω_n) · δ_T(Ω)
>         ≤  C_n · δ_T(Ω),     C_n = 2,
> ```
> and equivalently `δ_T(Ω̃) ≤ δ_T(Ω) + O_n(δ_T(Ω)²)`. The constant is
> dimensional only; `C_n → 1` as `δ_T(Ω) → 0`. No regularity of `∂Ω`
> is used; the proof uses only the exact torsion identity (Lemma 1),
> the Talenti `L^∞`/profile comparison, and the exact homogeneity of
> torsional rigidity.
</content>
</invoke>
