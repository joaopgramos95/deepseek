# Plan 3 — Step 5: the final transfer, fully rigorous

**Scope.** This note proves *Step 5* of the route fixed in
`PLAN3_INTENDED_ROUTE.md` (v3): the superlevel→domain Fraenkel-asymmetry
transfer, the volume-normalization composition across Steps 3/4/5, and
the assembled final inequality `Asym(Ω)² ≤ C_*(n) δ_T(Ω)` with `C_*(n)`
explicit and dimensional.

Steps 1, 3, 4 are treated as **hypotheses** (labelled **(H1)**, **(H3)**,
**(H4)** below); Step 5 is proved *conditionally* on them. The only
non-bookkeeping subtlety — the scale-(non-)invariance of `δ_T` versus the
scale-invariance of `Asym`, and whether the `|Ω̃| ≠ ω_n` mismatch is
genuinely absorbed — is isolated and resolved in §2 and audited in §5.

No struck machinery is used: no foliation, no action bound `(F)`, no
`∂_ρ` variation, no `D_I`-Fuglede, no boundary regularity, no
`√δ_T`-collar, no depth parameter. The transfer lemma is *exactly*
Lemma 8.3 of `Plan 2/level-set-deficit-identity.md` §8, reproved here
with its exact constant and its hypothesis verified.

Throughout: `−Δu = 1` in `Ω`, `u = 0` on `∂Ω`; `E_t = {u>t}`;
`ω_n = |B_1|`; `B_r` a ball of radius `r`; `B^{(V)}` a ball of volume
`V`. The Fraenkel asymmetry of a set `F` of finite positive measure is

  `Asym(F) := min{ |F Δ B| / |F| : B a ball with |B| = |F| }`,        (Asym)

a scale- and translation-invariant quantity in `[0, 2)`. (The minimum is
attained: `x ↦ |F Δ B(x,r_F)|`, `|B(x,r_F)|=|F|`, is continuous and
`→ 2|F|` as `|x|→∞`.)

The Saint–Venant deficit is taken **exactly as in
`level-set-deficit-identity.md` §3 (line 206–215) and §8 (line 456)**:

  `δ_T(F) := E(F) − E(B^{(|F|)})`,   `E(F) = −½ ∫_F u_F`.            (δ_T)

This is the **unnormalized** deficit; it is *not* scale-invariant
(scaling: §2.1). Its scale-invariant companion is

  `δ̄_T(F) := δ_T(F) / |F|^{(n+2)/n}`.                                 (δ̄_T)

The boxed identity of §3 of that file, `Γ(F) = 2 δ_T(F)/|F|`, and the
energy scaling computed in §2.1, give the relation used repeatedly:

  `δ̄_T(F) = ½ Γ(F) · |F|^{-2/n}`  is scale-invariant.

---

## 0. The three imported hypotheses (Steps 1, 3, 4)

These are *quoted as given*; Step 5 does not reprove them. They are
stated with explicit constants and with the scale-invariant deficit
`δ̄_T`, which is the only normalization under which the chain is
dimensionally consistent (§2, §5).

**(H1) [Step 1 — small collar].** There is a level `t̂ > 0` with the
extracted superlevel set `Ω̃ := E_{t̂} ⊂ Ω` open, and

  `λ := |Ω ∖ Ω̃| = |Ω| − |Ω̃|`  satisfying  `λ ≤ A_1(n) · |Ω| · δ̄_T(Ω)`,   (H1)

for a dimensional constant `A_1(n) < ∞`. (In the route this is the
Chebyshev/profile output: the good level lurks within boundary-*volume*
`O_θ(δ_T)`; `|Ω ∖ E_{t̂}|` is exactly that boundary volume. Equivalently,
in the unnormalized form of §8: `λ = η` with `η ≤ A_1'(n) δ_T(Ω)/R^{2}`,
`R = (|Ω|/ω_n)^{1/n}`; the two forms agree via (δ̄_T) — see §2.3. The
*only* facts about `Ω̃` used downstream are: `Ω̃ ⊂ Ω` measurable, and the
volume bound (H1).)

**(H3) [Step 3 — deficit of the subdomain].** With `Ω̃ = E_{t̂}`,

  `δ̄_T(Ω̃) ≤ C_n · δ̄_T(Ω)`,                                          (H3)

for a dimensional constant `C_n < ∞`. (Mechanism, recorded for honesty,
not reproved: `u − t̂` is *exactly* the torsion function of `Ω̃ = E_{t̂}`
— it solves `−Δ(u−t̂)=1` in `Ω̃`, vanishes on `∂Ω̃` — so `δ_T(Ω̃)` is an
exact quantity, and the only loss is the collar of measure `λ`. The
inequality (H3) is in the *scale-invariant* deficit; this is the form
that composes — see §2.2.)

**(H4) [Step 4 — sharp FK for graph subdomains].** Since (by Step 2)
`∂Ω̃` is a graph over a sphere, the perturbative sharp Faber–Krahn
inequality applies to `Ω̃`:

  `Asym(Ω̃)² ≤ c(n) · δ̄_T(Ω̃)`,                                       (H4)

for a dimensional constant `c(n) < ∞`. (Left side scale-invariant by
(Asym); right side scale-invariant by (δ̄_T); so (H4) is a statement
about the *shape* of `Ω̃`, independent of its volume — this is what makes
the volume mismatch in §2 harmless.)

> **Honesty note on the hypotheses' normalization.** The spec writes
> (H3),(H4) as `δ_T(Ω̃) ≤ C_n δ_T(Ω)` and `Asym(Ω̃)² ≤ c(n) δ_T(Ω̃)`
> with the *unnormalized* `δ_T`. As shown in §2.1, unnormalized `δ_T`
> scales like `ρ^{n+2}`, while `Asym²` is scale-invariant; so an
> inequality `Asym(Ω̃)² ≤ c(n) δ_T(Ω̃)` with unnormalized `δ_T` is
> *dimensionally inhomogeneous* and can only be intended with a fixed
> volume normalization (`|Ω̃| = ω_n`) or, equivalently and
> scale-cleanly, with `δ̄_T`. We adopt `δ̄_T` throughout; §2.4 records
> the *exact* dictionary to the fixed-volume reading and shows the two
> are identical up to the harmless `(1−λ/|Ω|)`-type factors tracked
> below. This is the place the user flagged for sign/constant errors;
> it is resolved with no uncontrolled term (§5).

---

## 1. Lemma 8.3 (superlevel replacement and transfer back), with proof and exact constant

We restate Lemma 8.3 of `Plan 2/level-set-deficit-identity.md` §8
*verbatim* (lines 595–624), then give a complete, self-contained proof,
extract the exact constant, and verify the hypothesis.

> **Lemma 8.3 (verbatim, §8, lines 595–624).**
> Let `E_t = {u>t}`, `s = |E_t| = L − η`, and assume `E_t ⊂ Ω`. Then
>
>   `𝒜(Ω) ≤ 𝒜(E_t) + 2 η/L`.
>
> Indeed, if `B_s` is an optimal ball for `E_t` and `B_L` is the
> concentric dilate with volume `L`, then
>
>   `|Ω Δ B_L| ≤ |Ω ∖ E_t| + |E_t Δ B_s| + |B_L ∖ B_s|`.
>
> Combining this with the quantitative isoperimetric inequality gives the
> immediate replacement estimate
>
>   `𝒜(Ω)² ≤ C_n D_I(t)/m(t)^{2−2/n} + C η²/L²`.
>
> This is the torsion analogue of the GGRT step "replace the arbitrary
> set by a matched superlevel set, prove stability there, then transfer
> back".

We use the *first* assertion (the elementary set-theoretic transfer),
which is exactly what Step 5 needs and which requires **no** isoperimetric
input and **no** regularity. (The displayed `𝒜(Ω)² ≤ C_n D_I/… + Cη²/L²`
is the *`D_I`-route* variant, which the route explicitly does **not**
use; we neither need nor invoke it. Only the bound
`𝒜(Ω) ≤ 𝒜(E_t) + 2η/L` is used, with `𝒜(E_t)` later fed by the
`D_H`-only Step 4.)

**Lemma 8.3′ (the exact statement proved here).**
Let `Ω̃ ⊂ Ω` be measurable with `0 < |Ω̃| < |Ω| =: L`, and set
`λ := |Ω| − |Ω̃| = |Ω ∖ Ω̃| > 0`. Then

  `Asym(Ω) ≤ Asym(Ω̃) + 2 λ / |Ω|`,                                  (8.3)

with the **dimension-free constant `C(n) = 2`** (independent of `n`, of
`Ω`, of `Ω̃`). The *only* hypothesis is `Ω̃ ⊂ Ω` measurable with
`|Ω̃| < |Ω|`. No regularity of `∂Ω`, `∂Ω̃`, of `u`, no isoperimetric
inequality, no graph property is used. In particular a superlevel set
`Ω̃ = E_{t̂}` (which is open, hence measurable, and `⊂ Ω` with
`|E_{t̂}| < |Ω|` whenever `t̂>0`) qualifies.

**Proof.** Write `L := |Ω|`, `s := |Ω̃| = L − λ ∈ (0, L)`.

*Step A: the symmetric-difference triangle inequality.* For measurable
sets `A, C, D` of finite measure, `1_{A Δ C} ≤ 1_{A Δ D} + 1_{D Δ C}`
pointwise a.e. (if `x` lies in `A Δ C` it lies in exactly one of `A, C`;
comparing with membership in `D` puts it in `A Δ D` or `D Δ C`).
Integrating,

  `|A Δ C| ≤ |A Δ D| + |D Δ C|`.                                     (T)

*Step B: choice of comparison balls.* By (Asym) and its attainment,
choose a ball `B_s` with `|B_s| = |Ω̃| = s` realizing the minimum for
`Ω̃`:

  `|Ω̃ Δ B_s| = Asym(Ω̃) · |Ω̃| = Asym(Ω̃) · s`.                       (B1)

Let `B_L` be the **concentric** ball with the same center as `B_s` and
`|B_L| = L`. Since `s < L`, the two concentric balls satisfy
`B_s ⊂ B_L`, hence

  `B_s Δ B_L = B_L ∖ B_s`,   `|B_s Δ B_L| = |B_L| − |B_s| = L − s = λ`.   (B2)

*Step C: assemble.* Apply (T) twice (with `A = Ω`):

  `|Ω Δ B_L| ≤ |Ω Δ Ω̃| + |Ω̃ Δ B_s| + |B_s Δ B_L|`.                  (C)

(This is precisely the displayed inequality in the verbatim Lemma 8.3,
with `B_s Δ B_L = B_L ∖ B_s`.) Now evaluate the three terms:

- `|Ω Δ Ω̃| = |Ω ∖ Ω̃| + |Ω̃ ∖ Ω| = λ + 0 = λ`, because `Ω̃ ⊂ Ω`.
- `|Ω̃ Δ B_s| = Asym(Ω̃) · s` by (B1).
- `|B_s Δ B_L| = λ` by (B2).

Hence

  `|Ω Δ B_L| ≤ λ + Asym(Ω̃) s + λ = Asym(Ω̃) · s + 2λ`.               (C′)

*Step D: `B_L` is admissible for `Asym(Ω)`.* The ball `B_L` has
`|B_L| = L = |Ω|`, so it is one of the competitors in the minimum (Asym)
defining `Asym(Ω)`. Therefore

  `Asym(Ω) ≤ |Ω Δ B_L| / |Ω|
           ≤ (Asym(Ω̃) · s + 2λ)/L
           = Asym(Ω̃) · (s/L) + 2λ/L.`

Since `0 < s/L = 1 − λ/L ≤ 1` and `Asym(Ω̃) ≥ 0`, we get
`Asym(Ω̃)·(s/L) ≤ Asym(Ω̃)`, whence

  `Asym(Ω) ≤ Asym(Ω̃) + 2λ/L = Asym(Ω̃) + 2 λ/|Ω|`.

This is (8.3) with `C(n) = 2`. ∎

**Remarks on the constant.**
1. **`C(n) = 2` is exact and dimension-free.** It is `1 + 1`: one `λ`
   from the collar `|Ω ∖ Ω̃|`, one `λ` from `|B_L ∖ B_s|` (matching the
   volume of the comparison ball up from `s` to `L`). It is the literal
   `2 η/L` of the file's Lemma 8.3 with `η = λ`. No dimension enters
   because (8.3) is purely measure-theoretic (Step A–D never touch the
   PDE, the perimeter, or `n`). It is of exactly the advertised form
   `C(n)|Ω∖Ω̃|/|Ω|` (a "`2/L`-type constant", with the file's `L=|Ω|`).
2. **Sharpness of the linear `λ/|Ω|`.** Taking `Ω` a ball and
   `Ω̃ = Ω ∖ (thin spherical shell at the boundary)` of measure `λ`
   shows `Asym(Ω̃) = Θ(λ/|Ω|)` while `Asym(Ω)=0`; the bound is linear in
   `λ/|Ω|` and cannot be improved to a higher power in general. (Not
   needed below — there the squared form is used — but it certifies that
   `C(n)=2`, linear, is the right shape, not an artifact of slack.)
3. **Tightening (optional).** One may keep the `s/L = 1−λ/L` factor:
   `Asym(Ω) ≤ (1−λ/L) Asym(Ω̃) + 2λ/L ≤ Asym(Ω̃) + 2λ/L`. The factor
   `(1−λ/L) ≤ 1` only *helps*; discarding it (as above) is the safe
   direction and is what we use. No sign error: the discarded term is
   `−(λ/L)Asym(Ω̃) ≤ 0`, so dropping it *enlarges* the right side, i.e.
   keeps the inequality valid.

**Hypothesis check (regularity-freeness).** The proof used only:
measurability and finite measure of `Ω, Ω̃`; `Ω̃ ⊂ Ω`; `0<|Ω̃|<|Ω|`;
existence of volume-prescribed balls and attainment of the min in
(Asym). A superlevel set `Ω̃ = E_{t̂} = {u>t̂}` is **open** (preimage of
an open set under the continuous `u`), hence Lebesgue measurable;
`E_{t̂} ⊂ Ω` for `t̂ ≥ 0`; and `|E_{t̂}| < |Ω|` for `t̂ > 0` (the collar
`{0<u≤t̂}` has positive measure since `u>0` in `Ω`, `u→0` at `∂Ω`).
**No `C^{1,γ}` free boundary, no nondegeneracy, no `|∇u|` bound, no
graph property, no Sard, no isoperimetric inequality is invoked.** This
is the precise content of the spec's requirement that Lemma 8.3's *only*
hypothesis is `Ω̃ ⊂ Ω` measurable and that a superlevel set qualifies.

---

## 2. Volume normalization: how `Asym` and the deficit chain compose

Here `|Ω̃| = L − λ`. After the unit-volume convention `|Ω| = ω_n` of the
route this is `|Ω̃| = ω_n − λ ≠ ω_n`. We must say *precisely* how
`Asym(Ω̃)` and the deficit chain compose under the rescaling of `Ω̃` to
unit volume, **consistently with Step 3's rescaling**, and verify the
`O(λ)` mismatch is absorbed with a tracked constant.

### 2.1 Scaling laws (the crux computation)

Let `ρ>0`, `F_ρ := ρ F = {ρx : x∈F}`. The torsion function obeys

  `u_{F_ρ}(x) = ρ² · u_F(x/ρ)`   (both solve `−Δw=1`, zero boundary),

so `∫_{F_ρ} u_{F_ρ} = ρ^{n+2} ∫_F u_F`, hence

  `E(F_ρ) = ρ^{n+2} E(F)`,   `|F_ρ| = ρ^n |F|`,
  `δ_T(F_ρ) = E(F_ρ) − E(B^{(|F_ρ|)}) = ρ^{n+2}(E(F)−E(B^{(|F|)})) = ρ^{n+2} δ_T(F)`.   (S1)

(The ball term scales the same: `B^{(ρ^n|F|)} = ρ B^{(|F|)}`.) Therefore

- **`δ_T` is NOT scale-invariant**: `δ_T(F_ρ) = ρ^{n+2} δ_T(F)`.        (S2)
- **`δ̄_T := δ_T/|F|^{(n+2)/n}` IS scale-invariant**:
  `δ̄_T(F_ρ) = ρ^{n+2}δ_T(F) / (ρ^n|F|)^{(n+2)/n} = δ_T(F)/|F|^{(n+2)/n} = δ̄_T(F)`.   (S3)
- **`Asym` IS scale-invariant**: `B↦ρB` is a bijection of admissible
  balls, `|F_ρ Δ ρB| = ρ^n|F Δ B|`, `|F_ρ| = ρ^n|F|`, so the ratio in
  (Asym) is unchanged, `Asym(F_ρ) = Asym(F)`.                          (S4)

(S2) versus (S4) is *the* incompatibility flagged in the brief: an
inequality `Asym(·)² ≤ c δ_T(·)` with **unnormalized** `δ_T` has a
scale-invariant left side and a `ρ^{n+2}`-homogeneous right side, so it
is *false at some scale* unless a volume normalization is fixed. (S3)
versus (S4) is the *consistent* pairing: both sides scale-invariant.
**We therefore run the entire chain in `δ̄_T`.** This is the single
substantive normalization decision; everything below is consequence.

### 2.2 The rescaling of `Ω̃`, consistent with Step 3

Let the route's normalization be `|Ω| = ω_n` (so `Ω`'s equal-volume ball
is the unit ball `B_1`; this is the standard FK normalization and is what
Step 3 uses when it states `δ_T(Ω̃) ≤ C_n δ_T(Ω)`). Then
`|Ω̃| = ω_n − λ`. Define the **unit-volume rescaling of `Ω̃`**

  `ρ := (ω_n / |Ω̃|)^{1/n} = (1 − λ/ω_n)^{-1/n} ≥ 1`,
  `Ω̃^♯ := ρ Ω̃`,   so `|Ω̃^♯| = ρ^n |Ω̃| = ω_n`.                       (R)

This is *exactly* the rescaling Step 3 / Step 4 use to put `Ω̃` into the
"`|·| = ω_n`" perturbative class. By scale-invariance (S3),(S4):

  `Asym(Ω̃) = Asym(Ω̃^♯)`,   `δ̄_T(Ω̃) = δ̄_T(Ω̃^♯)`.                    (R-inv)

So **(H4) is invariant under (R)**: `Asym(Ω̃)² = Asym(Ω̃^♯)² ≤ c(n)
δ̄_T(Ω̃^♯) = c(n) δ̄_T(Ω̃)`, and likewise **(H3) is invariant**:
`δ̄_T(Ω̃) = δ̄_T(Ω̃^♯) ≤ C_n δ̄_T(Ω) = C_n δ̄_T(Ω^♯)` with `Ω^♯ = Ω`
already at unit volume. **No `λ`-dependent factor appears in (H3) or
(H4)** precisely because they are stated in the scale-invariant
quantities `Asym`, `δ̄_T`. This is the resolution of the user's flagged
risk: the volume mismatch `|Ω̃|=ω_n−λ≠ω_n` is *invisible* to (H3),(H4)
when (and only when) they are read in `δ̄_T` — which §2.1 shows is the
only consistent reading.

> **Where the `O(λ)` mismatch actually lives.** It does *not* live in
> (H3),(H4) (scale-invariant). It lives entirely in **Lemma 8.3′'s
> additive term `2λ/|Ω|`** and, if one insisted on the unnormalized
> reading, in the conversion factor between `δ_T(Ω̃)` and
> `δ̄_T(Ω̃)·|Ω̃|^{(n+2)/n}`. We handle the former in §3 (it squares to
> `O(λ²)=O(δ̄_T²)`, lower order — §5). The latter is dispatched next.

### 2.3 Dictionary to the file's unnormalized §8 statements

The file §8 states (H1)-type facts with unnormalized `δ_T` and a factor
`R² = (|Ω|/ω_n)^{2/n}`. With the route normalization `|Ω| = ω_n` we have
`R = 1`, so `R²=1`, and by (δ̄_T) with `|Ω|=ω_n`:

  `δ̄_T(Ω) = δ_T(Ω)/ω_n^{(n+2)/n}`,   i.e. `δ_T(Ω) = ω_n^{(n+2)/n} δ̄_T(Ω)`.

Thus the §8 collar bound (Lemma 8.1/8.2, "`η ≤ A_1' δ_T(Ω)/R²`" at unit
volume `R²=1`) reads `λ = η ≤ A_1' δ_T(Ω) = A_1' ω_n^{(n+2)/n}
δ̄_T(Ω) =: A_1(n) ω_n δ̄_T(Ω)`, with
`A_1(n) := A_1' ω_n^{2/n}`. This is exactly **(H1)** with
`|Ω| = ω_n`. No scale ambiguity remains: at the fixed normalization
`|Ω|=ω_n` the unnormalized and normalized statements are related by the
*fixed* constant `ω_n^{(n+2)/n}`, absorbed into `A_1(n)`. (Off the
normalization, only `δ̄_T` is meaningful; we never need that here since
we fix `|Ω|=ω_n` once, in §3.)

### 2.4 Equivalence of "fixed-volume reading" and "`δ̄_T` reading"

For completeness, the two admissible readings of (H3),(H4) coincide:

- *Fixed-volume reading.* Replace `Ω̃` by `Ω̃^♯` (volume exactly `ω_n`)
  and use the *unnormalized* `δ_T` on `Ω̃^♯`. Since `|Ω̃^♯|=ω_n`,
  `δ_T(Ω̃^♯) = ω_n^{(n+2)/n} δ̄_T(Ω̃^♯) = ω_n^{(n+2)/n} δ̄_T(Ω̃)` by
  (R-inv). So `Asym(Ω̃)² = Asym(Ω̃^♯)² ≤ c(n) δ_T(Ω̃^♯)
  = c(n) ω_n^{(n+2)/n} δ̄_T(Ω̃)`.
- *`δ̄_T` reading.* `Asym(Ω̃)² ≤ c(n) δ̄_T(Ω̃)` directly (H4).

These differ only by the **fixed** factor `ω_n^{(n+2)/n}`, which we keep
explicit and fold into the final constant (§3). There is **no
`λ`-dependent discrepancy** between the two readings: the rescaling (R)
acts trivially on every scale-invariant quantity by (R-inv), and the
*only* `λ` that survives anywhere is the additive `2λ/|Ω|` of
Lemma 8.3′. This is the precise sense in which "the `O(λ)=O(δ_T)`
mismatch is absorbed", with the tracked constant being `ω_n^{(n+2)/n}`
(volume conversion) and `2` (Lemma 8.3′).

---

## 3. Assembly: the final inequality with explicit `C_*(n)`

Fix the route normalization `|Ω| = ω_n` (legitimate: `Asym(Ω)²` and
`δ̄_T(Ω)` are scale-invariant by (S3),(S4), so the target
`Asym(Ω)² ≤ C_*(n) δ̄_T(Ω)` is scale-invariant; proving it at `|Ω|=ω_n`
proves it at every scale). Abbreviate `δ := δ̄_T(Ω) ≥ 0`.

**Inputs.**
- **(8.3)** (Lemma 8.3′, proved in §1; hypothesis verified — `Ω̃=E_{t̂}`
  measurable, `Ω̃⊂Ω`, `|Ω̃|<ω_n`):
  `Asym(Ω) ≤ Asym(Ω̃) + 2λ/|Ω| = Asym(Ω̃) + 2λ/ω_n`.
- **(H1)**: `λ ≤ A_1(n) · ω_n · δ`, i.e. `λ/ω_n ≤ A_1(n) δ`.
- **(H3)** in `δ̄_T` (invariant under (R), §2.2): `δ̄_T(Ω̃) ≤ C_n δ`.
- **(H4)** in `δ̄_T` (invariant under (R), §2.2):
  `Asym(Ω̃)² ≤ c(n) δ̄_T(Ω̃)`.

**Step (i): square (8.3) with the elementary `(a+b)² ≤ 2a²+2b²`.**
(Valid for all real `a,b`; here `a=Asym(Ω̃)≥0`, `b=2λ/ω_n≥0`.)

  `Asym(Ω)² ≤ 2 Asym(Ω̃)² + 2 (2λ/ω_n)² = 2 Asym(Ω̃)² + 8 (λ/ω_n)².`   (i)

**Step (ii): bound `Asym(Ω̃)²` via (H4) then (H3).**

  `Asym(Ω̃)² ≤ c(n) δ̄_T(Ω̃) ≤ c(n) · C_n · δ.`                        (ii)

**Step (iii): bound the squared collar term via (H1).**

  `8 (λ/ω_n)² ≤ 8 (A_1(n) δ)² = 8 A_1(n)² · δ².`                       (iii)

**Step (iv): combine (i)–(iii).**

  `Asym(Ω)² ≤ 2 c(n) C_n · δ  +  8 A_1(n)² · δ².`                      (iv)

This is exactly the spec's
`Asym(Ω)² ≤ 2 c(n) C_n δ_T(Ω) + C'(n) δ_T(Ω)²` with the **explicit**

  `C'(n) := 8 · A_1(n)²`,                                              (C′)

where `A_1(n)` is the Step-1 collar constant (here `A_1(n)=A_1'
ω_n^{2/n}` from §2.3, `A_1'` the file's §8 constant; `A_1(n)` is
dimensional, with **no `δ`-dependence** — it comes from Chebyshev applied
to a fixed identity, §0/(H1)).

**Step (v): absorb the quadratic term (room to spare).** For
`δ = δ̄_T(Ω) ≤ δ_0(n)` with the **explicit dimensional threshold**

  `δ_0(n) := (c(n) C_n) / (4 A_1(n)²)`,                                (δ0)

we have `8 A_1(n)² δ² = 8 A_1(n)² δ · δ ≤ 8 A_1(n)² · δ_0(n) · δ
= 2 c(n) C_n · δ`. Substituting into (iv):

  `Asym(Ω)² ≤ 2 c(n) C_n δ + 2 c(n) C_n δ = 4 c(n) C_n · δ.`           (v)

**Conclusion (Step 5, final inequality).** For every `Ω` with
`δ̄_T(Ω) ≤ δ_0(n)`,

  ┌─────────────────────────────────────────────────────────────────┐
  │  `Asym(Ω)²  ≤  C_*(n) · δ̄_T(Ω)`,    `C_*(n) := 4 · c(n) · C_n`.  │
  └─────────────────────────────────────────────────────────────────┘
                                                                     (★)

Equivalently, in the file's unnormalized §8 deficit at `|Ω|=ω_n`
(dictionary §2.3, `δ̄_T(Ω) = δ_T(Ω)/ω_n^{(n+2)/n}`):

  `Asym(Ω)² ≤ C_*(n) · ω_n^{-(n+2)/n} · δ_T(Ω) =: C_**(n) · δ_T(Ω)`,
  `C_**(n) := 4 c(n) C_n ω_n^{-(n+2)/n}`,    (at the fixed `|Ω|=ω_n`).  (★′)

`C_*(n)` is **explicit** in the three imported dimensional constants:

| symbol | source | role |
|---|---|---|
| `c(n)` | **(H4)**, Step 4 | sharp FK-for-graph constant `Asym(Ω̃)²≤c(n)δ̄_T(Ω̃)` |
| `C_n`  | **(H3)**, Step 3 | deficit transfer `δ̄_T(Ω̃)≤C_n δ̄_T(Ω)` |
| `2`    | **Lemma 8.3′**, §1 | the dimension-free transfer constant `C(n)=2` |
| `A_1(n)` | **(H1)**, Step 1 | collar bound `λ≤A_1(n)ω_n δ̄_T(Ω)` |

The transfer constant `2` enters only through `δ_0(n)` and `C'(n)`
(via the `8=2·2²` in (i),(iii)); the headline constant is
`C_*(n)=4 c(n) C_n`, with the `4 = 2·2` coming from step (i)'s
`(a+b)²≤2a²+2b²` and step (v)'s absorption (each contributes a factor
`2`). Threshold `δ_0(n)=c(n)C_n/(4A_1(n)²)` is purely dimensional.

---

## 4. The "δ_T of room to spare", made rigorous and sharp-linear

The route's slogan is that the transfer has "`δ_T` of room to spare".
Here is the precise, audited statement.

**Claim.** In (iv), `Asym(Ω)² ≤ 2c(n)C_n · δ + 8A_1(n)² · δ²`:
the leading term is `Θ(δ)` (sharp-linear in `δ = δ̄_T(Ω)`) and the
collar term is `Θ(δ²)`, **genuinely lower order**, with a *dimensional*
constant `8A_1(n)²` that contains **no hidden `δ`-dependence**.

**Proof of the claim.**

1. *The collar term is exactly quadratic, not merely `o(δ)`.* By
   Lemma 8.3′ the transfer error is the additive `2λ/ω_n`, **linear in
   the collar volume `λ`**. Squaring (step (i)) makes it
   `8(λ/ω_n)²`. By (H1), `λ/ω_n ≤ A_1(n) δ`, an **honest linear**
   bound (Chebyshev/Markov on the *fixed* exact identity of §1–§3 of
   `level-set-deficit-identity.md`; the constant `A_1(n)` is the
   Chebyshev constant `C_n/θ` of Step 1 with `θ` a *fixed absolute*
   number — by the spec, `θ` is **not** `δ_T`-small and **not**
   `1/C`-small). Hence the collar term is `≤ 8A_1(n)² δ²`,
   `Θ(δ²)`. The exponent is `2`, strictly above the leading `1`.

2. *`A_1(n)` carries no hidden `δ`.* `A_1(n) = A_1' ω_n^{2/n}` with
   `A_1'` the §8/Step-1 constant `= (Chebyshev const)/(profile const)`;
   both are evaluated on the *exact* deficit identity (which is an
   equality, `Γ(Ω)=2δ_T(Ω)/|Ω|`, file §3 line 206) and on the ball
   profile `b(s)` — neither depends on `Ω` or on `δ_T`. In particular
   there is **no** `δ_T^{-1/2}`-window, **no** depth parameter `C`, **no**
   `√δ_T`-collar (all explicitly struck in the spec): the collar is
   `O(δ_T)` *linearly*, with a clean dimensional constant. The squared
   term is `O(δ_T²)` honestly.

3. *Lower-orderness is quantitative, with explicit room.* For
   `δ ≤ δ_0(n) = c(n)C_n/(4A_1(n)²)`,
   `(collar term)/(leading term) = 8A_1(n)²δ² / (2c(n)C_n δ)
   = (4A_1(n)²/(c(n)C_n)) · δ = δ/δ_0(n) ≤ 1`.
   So on `[0,δ_0(n)]` the collar term is *at most equal to* the leading
   term, and `→ 0` *relative* to it as `δ→0` (ratio `= δ/δ_0(n) → 0`).
   The "room to spare" is exactly the factor `δ/δ_0(n)`: there is a full
   linear factor of `δ` between the two terms. This is the rigorous
   meaning of "`δ_T` of room to spare".

4. *Sharp-linearity of the final bound.* (★), `Asym²≤C_*(n)δ`, is
   linear in `δ=δ̄_T(Ω)` with a *dimensional* `C_*(n)=4c(n)C_n`. The
   exponent `1` on `δ` is the sharp Faber–Krahn stability exponent
   (`Asym²∼δ_T`, not `Asym²∼δ_T^{1+ε}`); Lemma 8.3′'s linearity (Remark
   2 of §1) is what *preserves* the sharp exponent through the transfer
   — a superlinear transfer error (e.g. `λ^{1/2}`) would have *destroyed*
   it. The collar contributes only at order `δ²`, so it cannot degrade
   the exponent. ∎

---

## 5. Adversarial audit of the volume-normalization composition

The brief specifically asks whether the rescaling introduces a term that
is **not** `O(δ_T)` or **not** lower order, and to report any sign error.
Full audit:

**(A) Sign of the discarded factor in Lemma 8.3′.** Step D drops
`−(λ/L)Asym(Ω̃) ≤ 0`. Dropping a *nonpositive* term from the right side
*enlarges* it, so `Asym(Ω) ≤ Asym(Ω̃) + 2λ/L` is *valid*. ✔ (A
sign slip would have *kept* `(1−λ/L)` on the wrong side or dropped a
positive term — neither occurs.) The constant is exactly `2`, matching
the file's `2η/L` verbatim. ✔

**(B) Does the rescaling (R) inject a non-`O(δ_T)` term?** No. By
(S3),(S4) every quantity entering (H3),(H4) — `Asym(Ω̃)`, `δ̄_T(Ω̃)`,
`δ̄_T(Ω)` — is **invariant** under `Ω̃ ↦ Ω̃^♯ = ρΩ̃`. The Jacobian
`ρ = (1−λ/ω_n)^{-1/n} = 1 + λ/(nω_n) + O(λ²)` is `≠1`, but it acts
**trivially** on scale-invariant quantities by (R-inv); it never
multiplies `Asym(Ω̃)` or `δ̄_T`. So no `ρ`-factor (hence no `(1+O(λ))`
factor) leaks into the chain. ✔ The *only* place `ρ` could have done
damage is if the chain were run in **unnormalized** `δ_T`: then
`δ_T(Ω̃^♯) = ρ^{n+2} δ_T(Ω̃) = (1+O(λ)) δ_T(Ω̃)` would inject a
`(1+O(λ))=(1+O(δ_T))` *multiplicative* factor on the right of (H4). That
factor is `1+O(δ_T)`, i.e. *bounded* (≤ 2 for `δ_T` small) and
multiplies a term already `O(δ_T)`; it would change `C_*(n)` by at most
a factor `2` and is *not* a new lower-order-violating term. We avoid it
entirely by using `δ̄_T` (§2.1). **Reported precisely:** the *worst* the
rescaling can do, even under the inferior unnormalized reading, is a
bounded `(1+O(δ_T))` prefactor on an already-`O(δ_T)` term — never an
additive non-`O(δ_T)` term, never a term that fails to be lower order.
✔

**(C) The genuine `λ` term and its order.** The single surviving `λ`
is the additive `2λ/ω_n` of Lemma 8.3′. Its order: `2λ/ω_n ≤
2A_1(n)δ = O(δ)` by (H1) (linear, not `√δ`). After squaring,
`8(λ/ω_n)² ≤ 8A_1(n)²δ² = O(δ²)`, strictly lower order than the
leading `O(δ)`. ✔ No term of order `δ^{<1}` (e.g. `√δ`, `δ^{3/4}`)
appears anywhere; in particular the struck `√δ_T`-collar does **not**
re-enter. ✔

**(D) Dimensional purity of `C_*(n)`, `C'(n)`, `δ_0(n)`.** Each is
built from `c(n)` (H4), `C_n` (H3), `A_1(n)` (H1), and absolute numbers
(`2,4,8`). None of `c(n),C_n,A_1(n)` depends on `δ_T` or on `Ω`:
`c(n),C_n` are the Step-3/4 dimensional constants by hypothesis;
`A_1(n)` is the Chebyshev constant of Step 1 with a *fixed absolute*
`θ` on a *fixed exact* identity. Hence `C_*(n)=4c(n)C_n`,
`C'(n)=8A_1(n)²`, `δ_0(n)=c(n)C_n/(4A_1(n)²)` are **purely
dimensional**, with **no hidden `δ_T`-dependence**. ✔ This is exactly
the brief's requirement.

**(E) Consistency of the normalization choice across Steps 3/4/5.**
Step 3 outputs (H3) and Step 4 outputs (H4); the spec writes them with
`δ_T`, but as proved in §2.1 the only dimensionally consistent reading
(left side `Asym²` scale-invariant) is the `δ̄_T` reading, equivalently
the fixed-`ω_n`-volume reading (§2.4), and these are **identical** up to
the *fixed* factor `ω_n^{(n+2)/n}` (no `λ`). Step 5's rescaling (R) is
*the same* rescaling Steps 3/4 implicitly use to land `Ω̃` in the
unit-volume perturbative class, so the three steps compose with **no
double-counting and no normalization clash**. ✔

**Residual / caveat (reported honestly).** One genuine
interpretive dependency, *not* a gap in Step 5 itself: the spec states
(H3),(H4) with the *unnormalized* `δ_T`. Step 5 is rigorous **provided
(H3),(H4) are read in the scale-invariant `δ̄_T`** (equivalently, are
proved at the fixed normalization `|Ω̃^♯|=|Ω|=ω_n`). §2.1 shows this is
the *only* reading under which `Asym²≤c δ_T` is dimensionally possible at
all, so this is not a defect but a *consistency requirement on Steps 3/4*:
*they must be the scale-invariant statements (or fixed-volume
statements), which the standard FK-stability literature always is.* Under
that (necessary, and standard) reading there is **no residual term that
is not `O(δ_T)` and no residual term that is not lower order**: the
composition is clean, the constant is `C_*(n)=4c(n)C_n`, dimensional,
and the bound is sharp-linear. If, contrary to the literature, Steps 3/4
were genuinely meant with unnormalized `δ_T` at variable volume, the
*only* effect is the bounded `(1+O(δ_T))` prefactor of audit (B) — still
`O(δ_T)`, still lower-order-safe, changing `C_*(n)` by at most a fixed
factor `2`. **No sign error, no order violation, was found.**

---

## 6. Summary statement (the proved Step-5 lemma)

> **Lemma (Step 5, transfer + assembly).** Let `Ω̃ = E_{t̂} ⊂ Ω` be the
> Step-1 superlevel set, `λ := |Ω∖Ω̃|`. Then *unconditionally*
> (Lemma 8.3′, §1; only hypothesis `Ω̃⊂Ω` measurable, satisfied by any
> superlevel set):
>
>   `Asym(Ω) ≤ Asym(Ω̃) + 2 λ/|Ω|`   (dimension-free constant `2`).
>
> Assume further the Step-1/3/4 outputs **(H1)**, **(H3)**, **(H4)** of
> §0 (in the scale-invariant deficit `δ̄_T`, the only consistent
> normalization, §2.1). Then for `δ̄_T(Ω) ≤ δ_0(n) :=
> c(n)C_n/(4A_1(n)²)`,
>
>   `Asym(Ω)² ≤ 2 c(n) C_n δ̄_T(Ω) + 8 A_1(n)² δ̄_T(Ω)²
>            ≤ C_*(n) δ̄_T(Ω)`,    `C_*(n) := 4 c(n) C_n`,
>
> with `c(n)` from (H4) [Step 4], `C_n` from (H3) [Step 3], `A_1(n)`
> from (H1) [Step 1], all dimensional and `δ_T`-independent. The squared
> collar term is `Θ(δ̄_T²)`, genuinely lower order, with dimensional
> constant `8A_1(n)²` and no hidden `δ_T`-dependence; the final bound is
> sharp-linear in `δ̄_T(Ω)`. ∎
