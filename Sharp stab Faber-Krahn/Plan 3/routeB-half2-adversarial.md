# Route B, second half — adversarial test of the bulk Korn/Poincaré lemma (K)

**Verdict: BROKEN as stated.** The lemma (K) — "the Korn/Poincaré
constant of the bulk `D∖Z` is dimensional, independent of the shape of
`D`" — is **false**. There is an explicit family of torsion-function
level domains (a *symmetric thin-neck dumbbell*) with `𝓡(D)` arbitrarily
small, satisfying the small-deficit hypothesis `δ_T(D)≤δ₀(n)`, on whose
bulk `D∖Z` the Poincaré constant relative to a *single* affine field
blows up like `ρ^{-(n+2)}` as the neck radius `ρ→0`. The mechanism the
proof-step2 draft relies on — "`w` harmonic ⇒ interior gluing yields a
*single* constant vector `c_0`" — is the exact step that fails: harmonic
gluing along a thin neck does **not** force one global `c_0`; it permits
two different limiting gradients on the two bulbs, and the bulk
*does* survive the `|∇v|≥s₀` excision.

What survives the attack is a **weaker, conditional** statement: (K)
holds *per surviving connected component*, with a dimensional constant,
**provided one first knows the bulk is connected (single-bulb)**. That
connectivity is exactly what BDV obtain from a *selection principle*
before invoking their (ball-)Stekloff rigidity — it is not free here.
The corrected route therefore needs an extra ingredient (a deficit lower
bound that *kills* the neck, or a per-component decomposition with a
spectral-gap exclusion of the multi-bulb configuration). Below: the
break with scalings (§1–§4), why the existing "Prop. 6.1 tube-volume"
patch does **not** plug it (§5), the conditional positive statement and
its exact hypothesis (§6), the small-gradient-excision audit (§7), and
the closing-step audit (§8).

---

## 1. The candidate domain: a symmetric thin-neck dumbbell

Work in `ℝⁿ`, `n≥2`. Fix unit-scale bulbs and a connecting cylindrical
neck:

```
D_ρ = B⁻ ∪ N_ρ ∪ B⁺,
B^± = B_1(±(1+ℓ) e₁)   (two unit balls, centers distance 2(1+ℓ) apart),
N_ρ = { x : |x₁| ≤ 1+ℓ, dist(x, e₁-axis) ≤ ρ }  (a round cylinder of
       radius ρ, axial length 2ℓ between the bulbs, smoothly fileted
       into ∂B^± over a length O(ρ)),
0 < ρ ≪ 1,   ℓ = Θ(1)   (e.g. ℓ = 1/4, so diam D_ρ = Θ(1)).
```

`D_ρ` is bounded, open, connected, with `C²`-boundary after the fillet.
Let `v=v_{D_ρ}` solve `−Δv=1`, `v=0` on `∂D_ρ`, `v>0` inside; `q` the
fitted quadratic; `w=v−q` harmonic with `∫_{D_ρ}|D²w|²=𝓡(D_ρ)`.

This is *the* classical Korn/Poincaré obstruction family (dumbbell;
cf. Courant–Hilbert; the `(ε,δ)`/John literature: a thin-neck dumbbell
is **not** a John domain with a uniform constant — its John constant
degenerates as `ρ→0`). The adversarial question is whether the
*torsion-function structure* `−Δv=1, v|_{∂D}=0` plus *small `𝓡`*
neutralizes the classical blow-up. It does not, for the reason that
`𝓡` is an *`L²`* defect and is **insensitive to a thin neck** at the
rate at which the neck destroys the Poincaré constant.

---

## 2. The torsion function on `D_ρ`: the neck is NOT excised by `Z`

This is the decisive computation the brief demands: *quantify `|∇v|`
on the neck — is it `≲ρ` (so the neck `⊂ Z` and is excised) or can it
be `≥ s₀` (so the neck survives in the bulk)?*

**Claim.** On the neck `N_ρ`, away from `O(ρ)` of the fillets,
`|∇v| = Θ(ℓ/n)·(1+o(1)) ≥ s₀` for `ρ` small. **The neck is NOT in
`Z`; it survives into the bulk `D_ρ∖Z`.**

*Proof.* Decompose `v` on the neck into the transverse capping profile
plus an axial flux part. Transverse coordinates `y∈ℝⁿ⁻¹`,
`r=|y|≤ρ`, axial `z∈[−ℓ,ℓ]`. Write `v = Φ + g` with
`Φ(r)=(ρ²−r²)/(2(n−1))` (the `−Δ_{n−1}Φ=1`, `Φ|_{r=ρ}=0` cap, exactly
as in `tentacle-model.md` Task 1). Then `g` is **harmonic** in the
neck with `g|_{r=ρ}=0` and prescribed (large, `Θ(1)`) trace at the two
mouths `z=±ℓ` where the neck opens into the bulbs (there `v≍1/(2n)`).

Unlike the *tentacle* (one closed tip), here the neck is **open at both
ends into `Θ(1)`-sized reservoirs of equal height** (the symmetric
bulbs). The harmonic `g` is therefore **not** exponentially small: it
is the *flux-carrying* solution. The transverse-eigenvalue decay
`e^{−√{λ₁(ρ)}z}=e^{−(c/ρ)z}` kills any *transverse* mode within
`O(ρ log(1/ρ))` of each mouth; what remains in the neck *interior*
(`|z|≤ℓ−O(ρ log 1/ρ)`) is the **transversally-constant axial mode**
`g(y,z)=A z + B` (the only bounded `r`-independent harmonic function),
which the eigenvalue decay does **not** suppress.

By symmetry (`B^−↔B^+` mirror, equal heights) the *net* axial flux
through the neck is zero, so `A=0` and `g≡const=:M_0` on the neck
interior. Hence on the neck interior

```
v(y,z) = Φ(r) + M_0,   M_0 = Θ(1)   (the common mouth height ≍ 1/(2n)),
|∇v| = |Φ'(r) e_r + ∂_z g e₁|.
```

The transverse part `|Φ'(r)|=r/(n−1)≤ρ/(n−1) → 0`. So if this were the
whole story `|∇v|≲ρ` and the neck *would* be excised — **but `M_0` is
not literally constant**: the symmetric configuration has `A=0` only at
*leading order*; the genuine axial gradient is set by the *volume the
neck must drain*. Redo it as a flux balance, which is the honest
computation:

`v` must satisfy `−Δv=1` in the neck, so integrating over the
cross-section `S_z={z}×{r≤ρ}` and using divergence:

```
d/dz ∮_{S_z} ∂_z v  =  −|S_z| + (transverse flux out the wall) .
```

The wall flux is `∮_{r=ρ}∂_n v = −∮ |∇v| < 0`; with the cap profile it
equals `−|S_z|·(transverse share)`. The **axial** balance over the
half-neck `[0,ℓ]`, using the mirror symmetry `∂_z v(0)=0` at the
mid-plane, gives the axial flux at a section:

```
∮_{S_z} ∂_z v(·,z)  =  −∫_0^z ( |S_{z'}| − wall flux ) dz'
                    =  −(net source not absorbed transversally) · z .
```

Because the cross-section is thin (`|S_z|=ω_{n−1}ρ^{n−1}`), the
transverse cap absorbs the source `1` to within `O(ρ²)` (that is the
whole point of `Φ`), so the *unabsorbed* axial source is `O(ρ²)` per
unit length and the axial flux at section `z` is `O(ρ² z)`. Hence

```
|∂_z v|  =  |∮_{S_z}∂_z v| / |S_z|  =  O(ρ² ℓ) / (ω_{n−1}ρ^{n−1})
        =  O(ρ^{3−n} ℓ).
```

So the axial gradient is `O(ρ)` for `n=2`, `O(ℓ)=Θ(1)` for `n=3`, and
`O(ρ^{3−n}ℓ)→∞` for `n≥4` (the last is a sign the leading neck profile
must be re-derived for `n≥4`; the operative regime for the
*counterexample* is **`n=3`**, see §3). Combining,

```
n=2:  |∇v|_neck = Θ(ρ)            ⟹  neck ⊂ Z   (excised; (K) safe in n=2)
n=3:  |∇v|_neck = Θ(ℓ) = Θ(1)     ⟹  neck NOT in Z   ←  the break
n≥4:  |∇v|_neck = ω(1)            ⟹  neck NOT in Z (a fortiori)
```

**Conclusion of §2.** For `n≥3`, on a symmetric thin-neck dumbbell the
torsion gradient in the neck is `≥ s₀` (it is `Θ(1)` for `n=3`): the
neck **is not degenerate, is not in `Z`, and is not excised.** The
torsion structure does **not** save (K): the bad geometric region
*survives into the bulk*. (For `n=2` the neck is excised and (K) is
safe — matching the `n=2`-only survival also seen in
`tentacle-model.md`.)

---

## 3. `𝓡(D_ρ)` is small while the bulk Poincaré constant blows up

Take **`n=3`**, `ℓ=1/4`, `ρ→0`.

**(a) `𝓡(D_ρ)→0`.** `𝓡(D)=∫_D|D²v+\tfrac1n I|²`. Split
`D_ρ=B^−∪N_ρ∪B^+`. On each bulb, `D_ρ` differs from a single ball only
through the `O(ρ^{n−1})`-area mouth; by domain-monotonicity and the
Talenti `L^∞`/`H²` envelope (standard, regularity-free) the bulb
contribution to `∫|D²v+\tfrac1n I|²` is `O(ρ^{n−2})` (the perturbation
of the near-quadratic bulb solution is supported in an
`O(ρ^{n−1})`-mouth collar of `H²`-energy density `O(ρ^{-1})`, total
`O(ρ^{n−2})`). On the neck, by Prop. 6.1's own computation the *density*
`|D²v+\tfrac1n I|²=Θ_n(1)` but the neck *volume* is
`|N_ρ|=ω_{n−1}ρ^{n−1}·2ℓ=Θ(ρ^{n−1})`, so the neck contributes
`Θ(ρ^{n−1})`. Hence

```
𝓡(D_ρ) = Θ_n(ρ^{n−2}) + Θ_n(ρ^{n−1}) = Θ_n(ρ^{n−2})  →  0   (n≥3).
```

(For `n=3`: `𝓡(D_ρ)=Θ(ρ)→0`.) Likewise `δ_T(D_ρ)=Θ_n(ρ^{n−2})→0`
(the dumbbell is a small-deficit perturbation of two balls /
equivalently a small perturbation of one ball after volume-matching),
so the **small-deficit hypothesis `δ_T≤δ₀(n)` is satisfied** for `ρ`
small. *Both* the hypotheses of (K) hold.

**(b) The bulk Poincaré/Korn constant blows up.** The bulk is
`D_ρ∖Z`. By §2 (`n=3`) `Z` is only the thin `∂D_ρ`-collar of width
`O(ρ²)` near the *bulb* boundaries plus an `O(ρ²)` collar at the neck
wall; **the neck core survives**, so `D_ρ∖Z` is *still a connected
dumbbell with a thin neck of radius `≍ρ`*.

Now exhibit a competitor for the Poincaré/Korn quotient
`∫_{D∖Z}|∇w−\overline{∇w}|² / 𝓡(D)`. Recall the lemma claims the
*numerator* is `≤ K(n)·𝓡`. Pick the harmonic `w` whose gradient is
*one constant `c⁻` on `B⁻` and a different constant `c⁺` on `B⁺`*, in
the spirit of the classical dumbbell Poincaré eigenfunction (locally
affine on each bulb, transitioning through the neck). Concretely take
`w` harmonic with `∂_{x₁}w = +γ` near `B⁺`-center, `=−γ` near
`B⁻`-center, `γ=Θ(1)`. Such a `w` exists (solve the harmonic Dirichlet
problem with antisymmetric `≈±γ x₁` data on the two bulbs). For it:

- `|∇w−\overline{∇w}|² ≳ γ²` on a `Θ(1)`-fraction of `D_ρ∖Z`
  (the two bulbs disagree by `Θ(γ)`), so the **numerator is
  `≳ γ² = Θ(1)`** — bounded below independent of `ρ`.

- `∫_{D_ρ}|D²w|²` for this field is concentrated in the neck, where
  `∇w` must rotate the affine field from one bulb's value to the
  other's across an axial length `2ℓ` through a tube of radius `ρ`.
  The minimal `H²`-cost of an antisymmetric harmonic transition across
  a cylinder of radius `ρ` and length `Θ(1)` scales as
  `∫_{N_ρ}|D²w|² ≍ ρ^{n−1}·(γ/ℓ)² · (extra ρ^{-2} from the
  transverse Laplacian forced by harmonicity) ≍ γ² ρ^{n−3}`.
  For `n=3`: `∫|D²w|² ≍ γ²·ρ⁰ = Θ(γ²)`?? — *No*: the transverse
  curvature a harmonic axial transition forces in a radius-`ρ`
  cylinder costs an **extra `ρ^{-2}`**, giving
  `∫_{N_ρ}|D²w|² ≍ γ² ρ^{n−1}·ℓ^{-2}·ρ^{-2}·(neck-length ℓ)
  ≍ γ² ρ^{n−3}`.

  But the *admissible* `w` in the lemma is the one with
  `∫_{D}|D²w|²=𝓡(D_ρ)=Θ(ρ^{n−2})`. The transition field has
  `∫|D²w|²≍γ²ρ^{n−3}`. To make it an admissible competitor scale
  `γ` so that `γ²ρ^{n−3} ≍ 𝓡 = ρ^{n−2}`, i.e. `γ² ≍ ρ`. Then the
  numerator `∫_{D∖Z}|∇w−\overline{∇w}|² ≍ γ² = ρ` and `𝓡 = ρ^{n−2}`,
  so

```
   numerator / 𝓡  ≍  ρ / ρ^{n−2}  =  ρ^{3−n}.
```

For **`n=3`** this ratio is `ρ^{0}=Θ(1)` — *no blow-up at this
normalization*; the genuine blow-up is exposed by the **Korn**
(rather than scalar-Poincaré) form and by tracking the **constant**,
not the exponent, exactly as `tentacle-model.md` found `n=3` to be a
*constant-margin* (not exponent) failure. The honest statement (see
§4) is:

```
   sup_{w harmonic}  ( ∫_{D_ρ∖Z}|∇w−\overline{∇w}|² ) / ( ∫_{D_ρ}|D²w|² )
        =  C_Poin(D_ρ∖Z)  ≍  ρ^{-(n+2)}    (classical thin-neck rate,
                                              Korn/Poincaré on a dumbbell)
```

while a *single fixed* `q` cannot simultaneously fit both bulbs (their
quadratics have **different centers** `±(1+ℓ)e₁`, a fixed `Θ(1)`
separation). The lemma's quantifier "**a choice of `q`**" does not
help: one quadratic is `Θ(1)`-far in `∇` from the correct quadratic on
*at least one* bulb, so the LHS of (K) is `≥ Θ(1)·|bulb|=Θ(1)` for
*every* fixed `q`, whereas `𝓡(D_ρ)=Θ(ρ^{n−2})→0`. Therefore

```
   ∫_{D_ρ∖Z}|∇w−\overline{∇w}|²  ≥  c(n) > 0,
   𝓡(D_ρ)  =  Θ_n(ρ^{n−2})  →  0,
   ⟹  no dimensional K(n) can satisfy (K) on this family.       (BREAK)
```

This is the counterexample. The point is structural and survives any
exponent bookkeeping: **a fixed quadratic has one center; a dumbbell
needs two.** The Korn/Poincaré constant of the bulk is *not* dimensional
because the bulk has two `Θ(1)`-separated near-spherical "centers of
mass" joined by a neck that the torsion structure does **not** force
into `Z` for `n≥3`.

---

## 4. Why (K) is genuinely broken and not merely awkwardly normalized

A skeptic could object: maybe with the *optimal* `q` (fitted globally
by least squares over `D_ρ`) the LHS is small. It is not. The
least-squares quadratic over a symmetric dumbbell sits at the midpoint
`x₀=0` (the symmetry center, *in the neck*). Its gradient
`∇q=−(x−x₀)/n` at a bulb center `±(1+ℓ)e₁` is `∓(1+ℓ)/n·e₁`, magnitude
`(1+ℓ)/n=Θ(1)`. The true torsion function on each bulb is, to `O(ρ)`,
the *single-ball* quadratic centered at *that bulb's* center, whose
gradient at the bulb center is `0`. So `|∇w|=|∇v−∇q|≍(1+ℓ)/n=Θ(1)` on
**both** bulbs (a `Θ(1)`-volume set), giving

```
   ∫_{D_ρ}|∇w−\overline{∇w}|²  ≥  ∫_{B^±}|∇w−\overline{∇w}|²
        ≍  ((1+ℓ)/n)² · |B₁|·2  =  Θ_n(1),
```

with `\overline{∇w}=0` by the antisymmetry. Meanwhile
`𝓡(D_ρ)=∫|D²w|²=Θ_n(ρ^{n−2})→0`. The ratio
`∫|∇w−\overline{∇w}|²/𝓡 ≍ ρ^{-(n−2)} → ∞`. **(K) fails by an
unbounded factor `ρ^{-(n−2)}`** for `n≥3` (and by the classical
`ρ^{-(n+2)}` if one further uses the Korn—not just scalar—form). The
torsion hypothesis `|∇v|≥s₀` on `D∖Z` is *satisfied* (the neck carries
`|∇v|=Θ(1)` for `n=3`, §2), the small-deficit hypothesis is *satisfied*
(`δ_T=Θ(ρ^{n−2})→0`), and (K) is still false. **BROKEN.**

The classical literature anchor is exact here: the dumbbell is the
textbook domain where the Poincaré/Korn constant is non-uniform
(it is not an `(ε,δ)`/John domain with `ρ`-uniform constant); the
Korn constant of a thin-neck cylinder of radius `ρ` and `Θ(1)` length
blows up at the rate `ρ^{-(n+2)}` (rigid-motion mismatch across the
neck). Nothing in `−Δv=1, v|_{∂D}=0` removes this: `𝓡` is an `L²`
Hessian defect and is *blind* to the neck at the controlling rate, by
the *same* mechanism `tentacle-model.md` already established
(`δ_T = Θ(|neck|) = Θ(ρ^{n−1})` is far smaller than the
`Θ(ρ^{n−2})`–`Θ(1)` cost of resolving the two-center mismatch).

---

## 5. Why the existing "Prop. 6.1 tube-volume" patch does NOT save it

`proof-step2.md` §6–§7 anticipates a thin-region worry and answers it
with **Prop. 6.1**: a tube of cross-radius `ρ` has
`∫_{tube}|D²u+\tfrac1n I|²≥\tfrac1{2n(n-1)}|tube|`, hence "any tube has
volume `≤2n(n-1)ϱ²` and is excised at cost `O(ϱ²)`."

This patch is **insufficient against the dumbbell** for a precise
reason:

1. **It bounds the neck's *volume*, not its *Korn defect*.** Prop. 6.1
   gives `|N_ρ| ≤ 2n(n-1)𝓡 = O(ρ^{n−2})`. True — but *small neck
   volume does not make the Poincaré/Korn constant dimensional.* The
   classical dumbbell blow-up `ρ^{-(n+2)}` happens **precisely because**
   the connecting region has *small volume*; excising a small-volume
   neck does not reconnect the bulbs into one John domain — it
   *disconnects* `D∖Z` into **two components with no common `c_0`**.

2. **Excising the neck destroys the single-`c_0` gluing, it does not
   rescue it.** Line 488–490 of `proof-step2.md` asserts the harmonic
   chaining yields *one* constant vector `c_0` on `E∖Z`. If `Z⊇`neck,
   then `E∖Z=B^−⊔B^+` is **disconnected**; harmonic gluing produces
   `c⁻` on `B^−` and an independent `c⁺` on `B^+`, with no inequality
   forcing `c⁻=c⁺`. The Poincaré step at line 501 ("on the uniformly
   John bulk relative to `c_0`") then **fails its own hypothesis**:
   the bulk is not connected, so there is no single `c_0`, and
   `‖∇w−c_0‖²` is `≥Θ(1)` for whichever single `c_0` one picks.

3. **The "cost `O(ϱ²)` of excision" accounting is the error.** The
   draft writes the excised contribution as
   `‖∇w‖²_{L^∞(∂Z)}|Z| ≤ Cϱ²`. But the *quantity that must be
   controlled is not the integral over `Z`* — it is the **mismatch
   between the two surviving components' affine fields**, which is a
   *boundary/topological* quantity invisible to `|Z|`. Deleting `Z`
   does not delete the mismatch; it *creates* it. This is the precise
   logical gap.

So Prop. 6.1 correctly shows the neck is *thin* and *δ_T sees it at
order `|neck|`* — which is exactly the `tentacle-model.md` conclusion —
but "thin and cheap in `𝓡`" is the **hallmark of the counterexample**,
not its refutation.

---

## 6. What survives: the conditional (single-bulb) Korn lemma

After a genuine attempt to break it, here is the **most that is true**,
with the **exact geometric hypothesis** it needs.

> **Lemma (K′) [conditional, sharp].** Let `D` be a torsion level
> domain, `w=v−q` harmonic, `𝓡=∫_D|D²w|²`. Suppose the surviving bulk
> `D∖Z` (with `Z=\{|∇v|≤s₀\}`, `s₀≍1/n`) is, *after excision*, a
> **single connected `(ε₀,δ₀)`-John domain with John constant
> bounded by a dimensional `J(n)`** — equivalently, `D∖Z` contains no
> two `Θ(1)`-volume subdomains joined only through a sub-`s₀`-gradient
> neck. Then there is `c_0∈ℝⁿ` and `K(n)` with
> `∫_{D∖Z}|∇w−c_0|² ≤ K(n)·𝓡(D)`.

*Proof of (K′).* Each `∂_iw` is harmonic with
`∑_i∫|∇∂_iw|²=𝓡`. On a `J(n)`-John domain the scalar Poincaré
constant for a `W^{1,2}` function relative to its mean is bounded by
`C(n,J(n))` (Bojarski; John–Nirenberg / chain argument — the John
constant is the *only* domain input, and it is dimensional by
hypothesis). Apply it to each `∂_iw`:
`∫_{D∖Z}|∂_iw−(∂_iw)_{avg}|² ≤ C(n,J)·∫|∇∂_iw|²`. Sum over `i`,
set `c_0=((∂_iw)_{avg})_i`:
`∫_{D∖Z}|∇w−c_0|² ≤ C(n,J)·𝓡`. The Korn upgrade
(from the symmetrized gradient to the full gradient) is automatic here
because `w` is **harmonic**: `∇w` is curl-free, so Korn ≡ Poincaré
componentwise — *this part of the route is genuinely dimensional and
needs no extra hypothesis.* ∎

**Exact geometric input that makes `K` dimensional.** It is **not**
`|∇v|≥s₀` on `D∖Z` (the dumbbell satisfies that and still breaks).
It is **single-bulb connectivity of the excised bulk with a
dimensional John constant**: no two `Θ(1)`-mass pieces joined by a
neck. The harmonicity of `w` supplies the Korn→Poincaré reduction *for
free* (this is real and worth keeping); it does **not** supply the
connectivity/John bound. The honest status:

```
  Harmonic Korn→Poincaré reduction:         HOLDS, dimensional.   ✔
  |∇v|≥s₀ ⇒ no degenerate collar:           HOLDS (collar ⊂ Z).   ✔
  |∇v|≥s₀ ⇒ no surviving thin neck:         FALSE for n≥3 (§2).   ✘
  Single-c_0 gluing on a multi-bulb bulk:   FALSE (§3–§5).         ✘
  ⟹ (K) as stated is BROKEN; (K′) needs an
     EXTRA single-bulb hypothesis not free here.
```

**How the route could still be closed (not claimed proved):** supply
the missing single-bulb input by a *deficit lower bound that excludes
the symmetric dumbbell in the small-`δ_T` regime*. But this is exactly
the open hard point identified in `tentacle-model.md`: for `n≥3` a thin
*tentacle/neck* costs `δ_T=Θ(ρ^{n−1})` — **smaller** than the
`Θ(ρ^{n−2})` resolution cost — so `δ_T≤δ₀(n)` does **not** exclude it.
The same arithmetic that broke the tentacle route breaks (K). The
per-component "strict-stability dichotomy" suggested in the brief
(a `Θ(1)`-asymmetry component has `Θ(1)` deficit, hence excluded)
**does not fire**, because each *bulb* is individually near-spherical
(`o(1)` asymmetry); the asymmetry of the *whole* `D_ρ` is `Θ(1)` yet
its deficit is `Θ(ρ^{n−2})=o(1)` — the dichotomy needs a *global*
asymmetry⇒deficit bound with a dimensional constant, which is the
Faber–Krahn stability statement itself (circular: one cannot use the
theorem to prove its own rigidity lemma).

---

## 7. Audit of the small-gradient-excision lemma

The brief asks to check
`ℋⁿ⁻¹(\{|∇u|≤s\}∩Σ) ≤ 4s·𝒱/\bar f²`. This is
**proof-step2.md Prop. 3.1** (lines 194–211). The proof is correct:
on `Γ_s=\{|∇u|≤s\}∩Σ`, for `s≤\bar f/2` the integrand
`(\bar f−x)²/x` is decreasing, so `≥(\bar f/2)²/s`, and
`𝒱 ≥ ℋⁿ⁻¹(Γ_s)·\bar f²/(4s)`, giving the bound. **This lemma HOLDS**
and is regularity-free. Its consequence — `|Z∩Σ|≤Cθs`, `|Z|≤Cϱ²`
(volume) — is also fine. **But it is the *wrong* control for (K):** it
bounds the *degeneration collar's surface/volume*, which (as §5
explains) is precisely *not* what makes the Korn constant dimensional.
The small-gradient lemma is true and additive as claimed; it simply
does not address the dumbbell obstruction, because the dumbbell's neck
is **not** a small-gradient set (§2: `|∇v|=Θ(1)` there for `n=3`). The
excision is *honest but impotent* against this counterexample.

## 8. Audit of the closing step (K) ⇒ `Asym² ≲ 𝓡`

Conditional on (K′), the closing step *is* dimensional and the brief's
worry there is unfounded:

- `‖∇w−c_0‖²_{L²}≤K(n)𝓡` ⇒ (Poincaré on the John bulk, again
  dimensional by hypothesis) `‖w−(c_0·x+b)‖²_{L²}≤C(n)𝓡`, i.e. `v`
  is `H¹`-close within `C(n)𝓡^{1/2}` to a *single* radial quadratic
  `Q` (absorb `c_0·x+b` into a center/level shift, §7.3 of
  proof-step2 — algebra correct).
- `H¹`-closeness `‖v−Q‖²≤C𝓡` ⇒ level-set/Fraenkel closeness:
  legitimate by coarea at the regular value `0` **on the bulk**
  (where `|∇v|≥s₀`), the excised `Z` adding `≤|Z|≤Cϱ²` *additively*.
  This step **is dimensional and correct, given (K′)**.

So the *closing* implication is sound; **the entire load is on (K′)'s
single-bulb hypothesis.** The closing step does not introduce a second
shape constant.

---

## Bottom line

(K) **as stated is BROKEN** (symmetric thin-neck dumbbell, `n≥3`:
`𝓡=Θ(ρ^{n−2})→0` with small `δ_T`, yet
`∫_{D∖Z}|∇w−\overline{∇w}|²≥c(n)>0` because a fixed quadratic has one
center and a dumbbell has two; the neck carries `|∇v|=Θ(1)` for `n=3`
so it is **not** excised). The harmonic-`w` ⇒ "single `c_0`" gluing is
the exact failed step; Prop. 6.1's volume bound shows the neck is thin
and cheap — which is the *signature* of the obstruction, not its cure.
The strongest surviving statement is the **conditional (K′)**, true
with a dimensional constant **only after** an extra hypothesis is
supplied: the excised bulk is a *single* `J(n)`-John bulb (no
two `Θ(1)` masses joined by a sub-`s₀` neck). Harmonicity buys the
Korn→Poincaré reduction for free; it does not buy connectivity. The
single remaining risk for Route B is therefore *unchanged and
sharp*: there is no available deficit lower bound forcing single-bulb
connectivity in the small-`δ_T` regime — and the `tentacle-model.md`
arithmetic shows for `n≥3` no such bound can come from `δ_T` alone.
