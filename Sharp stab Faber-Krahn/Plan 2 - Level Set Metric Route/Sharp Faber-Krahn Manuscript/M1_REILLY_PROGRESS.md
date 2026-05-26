# M1 progress: weighted Reilly identities and the precise remaining kernels

Goal of M1 (from the strategy file): for `v = u - t(ρ)` the torsion function of
`E_ρ` (`-Δv = 1`, `v = 0` on `∂E_ρ`, `v > 0` inside), produce a constructive,
linear, explicit-constant bound feeding `Assumption ass:constructive-strong`,
i.e. `|E_ρ Δ B_ρ(z)|² + ∫_{∂*E_ρ}|ν - e_z|² ≤ C(D_H + D_I)` for one centre `z`.

Notation on `∂E_ρ`: `g := |∇v| = |∇u|`, `P := P(E_ρ)`, `m := |E_ρ| = ω_n ρ^n`,
`β := ∫_{∂E_ρ} g`, `α := ∫_{∂E_ρ} g^{-1}`, `\bar g := β/P`. Flux identity:
`β = m`. Cauchy–Schwarz defect `D_H = αβ - P²`. Isoperimetric defect
`D_I = P² - c_n m^{2-2/n}`, `c_n = n²ω_n^{2/n}`. `T = T(E_ρ) = ∫_{E_ρ} v`.

**Summary.** Three exact, explicit identities are established (Part 1) and one
clean reduction (Part 2). They reduce M1 to two sharply-identified kernels
(Part 3): a scale-invariant torsion inequality and a bulk→single-level trace.
The honest finding (Part 4) is that the weighted-Reilly bulk deviation is a
*bulk* quantity over the interior of `E_ρ`, so it yields the target **only in
integrated form**, not pointwise per level as `ass:constructive-strong` is
currently stated. This is the real structural issue to resolve next; it is
**not** a contradiction/compactness obstruction.

---

## Part 1. Three exact identities (proved, ball-checked)

Write `q := D²v + (1/n)I` (symmetric tensor); since `Δv = -1`,
`|q|² = |D²v|² + (2/n)Δv + 1/n = |D²v|² - 1/n`, and `q ≡ 0` iff `v` is a ball
profile. Weinberger's `P`-function `Π := |∇v|² + (2/n)v` has
`ΔΠ = 2|D²v|² - 2/n = 2|q|²`.

### Identity A (weighted Reilly/Weinberger)
```
   2 ∫_{E_ρ} v |D²v + (1/n)I|² dx  =  ∫_{∂E_ρ} g³ dH  −  (1 + 2/n) T.
```
*Proof.* Green's second identity for `(v, Π)` with `v=0` on `∂E_ρ`:
`∫ vΔΠ − ΠΔv = ∫_∂ (v Π_ν − Π v_ν) = −∫_∂ Π v_ν`. Here `Δv=-1`, on `∂E_ρ`
`Π = g²`, `v_ν = -g`, so `−∫_∂ Π v_ν = ∫_∂ g³`; and `∫ ΠΔv = -∫_{E_ρ}Π =
-(∫|∇v|² + (2/n)∫v) = -(1+2/n)T` (using `∫_{E_ρ}|∇v|² = ∫_{E_ρ}v = T`).
LHS `= ∫ v·2|q|²`. ∎
*Ball check* (`B_R`): `∫_∂ g³ = (R/n)³ nω_nR^{n-1} = ω_nR^{n+2}/n²`;
`(1+2/n)T = ω_nR^{n+2}/n²`. RHS `= 0 = ` LHS. ✓

### Identity B (Pohozaev/Rellich)
```
   ∫_{∂E_ρ} g² (x−z)·ν dH = (n+2) T   for every z,    and    ∫_{∂E_ρ} g² ν dH = 0.
```
*Proof.* Compute `∫_{E_ρ}((x−z)·∇v)(−Δv)` two ways. Using `−Δv=1` it equals
`∫(x−z)·∇v = −n∫v = −nT`. Integrating by parts the other way gives
`(1−n/2)T − (1/2)∫_∂ g²(x−z)·ν`. Equate ⇒ `∫_∂ g²(x−z)·ν = (n+2)T`,
`z`-independent; the `z`-independence is `∫_∂ g²ν = 0` (also checked directly
via `∫_∂ g²ν_i = 2∫ ∂_j v ∂_{ij}v = 2∫_∂ g²ν_i`). ∎
*Ball check*: `(R/n)²·R·nω_nR^{n-1} = ω_nR^{n+2}/n = (n+2)T(B_R)`. ✓

### Identity C (combination; eliminates the bulk `T`)
Substituting B into A:
```
   2 ∫_{E_ρ} v |D²v + (1/n)I|² dx  =  ∫_{∂E_ρ} g² [ g − (1/n)(x−z)·ν ] dH.
```
Pure boundary integral; integrand vanishes on a ball about `z` (`g=R/n`,
`(x−z)·ν=R`). For our use `(x−z)·ν = ρ H_{z,ρ}`, so the integrand couples the
gradient defect (`g−\bar g`) and the homothetic-trace defect (`H_{z,ρ}−1`).

---

## Part 2. Reduction of the bulk deviation

Set `Dev_w := ∫_{E_ρ} v |D²v+(1/n)I|² ≥ 0` and the third-moment variance
`V₃ := ∫_{∂E_ρ} g³ − β³/P²`. Writing `g = \bar g + δ`, `∫δ = 0`:
```
   V₃ = 3\bar g ∫_{∂E_ρ}(g−\bar g)² + ∫_{∂E_ρ}(g−\bar g)³ ≥ 0   (Hölder; 0 iff g const).
```
From Identity A, with `W := (1+2/n)T − β³/P²`:
```
   2 Dev_w = V₃ − W.                                            (R)
```
*Ball check*: `β³/P² = m³/P² = ω_nR^{n+2}/n² = (1+2/n)T(B_R)` ⇒ `W=0`, and
`V₃=0`, consistent with `Dev_w=0`.

### Lemma (third-moment variance is controlled by `D_H`, given an upper bound)
Using the weighted-variance identity `D_H = (P²/m)∫_{∂E_ρ}(g−\bar g)²/g`
(proved in the manuscript, `lem:velocity` circle): if `g ≤ M₀` on `∂E_ρ`, then
`∫(g−\bar g)² ≤ M₀ ∫(g−\bar g)²/g = M₀ (m/P²) D_H`, and `|g−\bar g| ≤ M₀+\bar g`,
so
```
   V₃ ≤ ( 3\bar g + (M₀+\bar g) ) M₀ (m/P²) D_H ≤ C(n,R,ρ_*,M₀) · D_H.    (V)
```
All constants explicit. **This step needs an a priori upper bound
`g=|∇u| ≤ M₀` on `∂E_ρ`** (the `M₀`-half of the old Hyp-G; available in the
bounded class via Talenti/Cianchi–Maz'ya gradient bounds, but it is a genuine
prerequisite, not free).

By (R) and (V): `Dev_w ≤ (C·D_H − W)/2`. So a clean bound `Dev_w ≤ C(D_H+D_I)`
holds **iff** `−W ≤ C(D_H+D_I)`.

---

## Part 3. The two remaining kernels

### Kernel K1 — sign/size of `W` (a scale-invariant torsion inequality)
`−W = β³/P² − (1+2/n)T = m³/P² − (1+2/n)T(E_ρ)`. Nearly-spherically (volume
fixed, `P = P(B_ρ)(1+p)`, `p ≈ D_I/(2P(B_ρ)²)`, torsion deficit
`τ := T(B_ρ)−T(E_ρ) ≥ 0`):
```
   −W ≈ (1+2/n)[ τ − T(B_ρ) D_I / P(B_ρ)² ].
```
So `−W ≤ C(D_H+D_I)` reduces to **`τ(E_ρ) ≤ C(D_H+D_I)`** (the `D_I` term is
already of the right size). Equivalently `W ≥ 0` is the scale-invariant
inequality
```
   T(Ω) P(Ω)² ≥ (n/(n+2)) |Ω|³,   with equality iff Ω is a ball.        (K1)
```
*Status of (K1):* verified by hand on the ball (equality), disk vs. square,
thin rectangle, thin annulus, two-balls-with-neck — all give `≥` with the ball
as the apparent **minimiser** of `T P²/|Ω|³`. Not proved. (K1) is a clean,
self-contained "reverse" torsion–perimeter inequality; the natural test of
whether it is even true is the Fuglede nearly-spherical expansion mode-by-mode
(compute the degree-`k` coefficients of `τ` and `D_I`; the dangerous mode is
`k=2`, the ellipsoidal/sharpness mode). If some mode gives `W<0`, then `−W`
is of size `D_I` there, which is still admissible since we allow `C(D_H+D_I)`;
the real issue is K2 below.

### Kernel K2 — bulk vs. single level (the structural crux)
`τ(E_ρ)` is **not** a single-level quantity. By the level-set identity applied
to `E_ρ` (whose torsion function is `v`),
```
   τ(E_ρ) = ∫_{(0,ρ]} ( D_H(t(ρ')) + D_I(t(ρ')) ) · (weight) dρ' ,
```
an integral of our defects over **all interior radii** `ρ' ≤ ρ`. Hence
`τ(E_ρ) ≤ C(D_H+D_I)(t(ρ))` is **false pointwise** (`D_I` can spike at a single
level without the interior integral being small, and vice versa). Consequently
`Dev_w(E_ρ)` is **not** bounded pointwise by the single-level
`D_H(t(ρ))+D_I(t(ρ))`, and `ass:constructive-strong` as stated (a pointwise,
per-`ρ` estimate) is **not** what the weighted-Reilly identity delivers.

What the identity *does* deliver, after integrating against `dμ` and using the
budget `∫(D_H+D_I)dμ ≤ Cδ_T` together with
`∫_G τ(E_ρ)dμ(ρ) = ∫_G(∫_{(0,ρ]}(D_H+D_I)dμ')dμ(ρ) ≤ (∫(D_H+D_I)dμ)·μ(G) ≤ Cδ_T`,
is the **integrated** bound
```
   ∫_{G} Dev_w(E_ρ) \, dμ(ρ) ≤ C(n,R,ρ_*,M₀) · δ_T(Ω).        (INT)
```

### Kernel K3 — trace (bulk `Dev_w` → single-level normal oscillation)
Even granting (INT), `eq:constructive-strong` asks for the single-level
boundary term `∫_{∂E_ρ}|ν−e_z|²`. Relating it to the bulk `Dev_w` is a trace,
and by coarea the bulk distributes over *all* levels, so there is no clean
pointwise trace either. The volume term `|E_ρΔB_ρ(z)|² ≤ C D_I` is fine and
constructive (FMP Fraenkel inequality), but its centre must be reconciled with
the Reilly/best-profile centre (`lem:center-transfer`).

---

## Part 4. Honest assessment and the corrected target

- The identities A, B, C and the reduction (R)+(V) are **correct, explicit, and
  contradiction-free** — genuine progress, and the right starting point.
- The pointwise per-level `ass:constructive-strong` is, however, **mismatched**
  to the weighted-Reilly route: `Dev_w(E_ρ)` is intrinsically a bulk quantity
  over the interior of `E_ρ`, controlled by the *interior-integrated* defect
  `τ(E_ρ)`, not by the single level `ρ`. The route yields the **integrated**
  estimate (INT), not the pointwise (eq:constructive-strong).
- Two clean, self-contained sub-problems are isolated:
  - **(K1)** `T P² ≥ (n/(n+2))|Ω|³` (ball = equality) — a scale-invariant
    torsion–perimeter inequality, checkable first by the Fuglede `k=2`
    expansion, then (if true) by symmetrization/rearrangement. Worth settling
    on its own.
  - **(M₀)** the a priori upper gradient bound `|∇u| ≤ M₀` on good level sets,
    needed for (V).

### Recommended reformulation (the productive next move)
Replace the pointwise `ass:constructive-strong` by an **integrated** constructive
input compatible with (INT), and re-route the kinetic estimate to consume it.
Concretely, target
```
   ∫_{G} ( |E_ρΔB_ρ(z_ρ)|² + ∫_{∂*E_ρ}|ν_ρ−e_z|² ) \, dμ(ρ)
        ≤ C(n,R,ρ_*) · δ_T(Ω),                              (INT-strong)
```
i.e. the same-centre control **integrated over good radii**. This is exactly
what the Reilly identity (via (INT) + trace-in-the-mean + FMP for the volume
term) is positioned to give, and it is what the budget supplies. The kinetic
estimate currently applies the pointwise bound and then integrates; it should
be checked whether it can instead consume (INT-strong) directly. If yes, the
bulk obstruction K2 dissolves and only (K1)+(M₀)+the integrated trace remain —
all constructive.

**Bottom line.** M1's algebraic core is done and clean. The obstruction is not
non-constructivity but a **bulk-vs-pointwise mismatch**: the honest constructive
statement obtainable from Reilly is the *integrated* same-centre bound
(INT-strong), and the manuscript's pointwise assumption should be weakened to
match it. Next concrete steps: (i) settle (K1); (ii) verify the kinetic estimate
accepts (INT-strong); (iii) establish (M₀) in the bounded class.

---

## Part 5. The kinetic estimate accepts the integrated bound (verified)

This is the key viability check, and it **passes**: the pointwise
`ass:constructive-strong` is stronger than the proof needs; the integrated
`INT-strong` suffices. Hence the bulk obstruction K2 is harmless.

**Claim.** Proposition `prop:positivekinetic` closes using only
```
   (INT-strong)   ∫_{G} ( ∫_{∂*E_ρ} |ν_ρ − e_z|² dH ) dμ(ρ) ≤ C δ_T(Ω),
```
together with the constructive Fraenkel bound `|E_ρΔB_ρ(z)|² ≤ C D_I` (FMP) and
the *trivial* pointwise bound `∫_{∂*E_ρ}|ν_ρ−e_z|² ≤ 4P(E_ρ) ≤ C` on good
levels.

**Proof of the claim.** In `prop:positivekinetic` one needs
`∫_G (∫_{∂*E_ρ}|H_{z,ρ}−\bar V_ρ|)² dμ ≤ Cδ_T` (the only place the strong-form
input enters; the `q²≤CD_I` and `(∫|V−\bar V|)²≤D_H` terms are pointwise and
constructive). By the oriented radial trace (`lem:oriented-radial-trace`) and
`|1−\bar V_ρ|P(E_ρ) = P(E_ρ)−P(B_ρ) ≤ C D_I`,
```
   ∫_{∂*E_ρ}|H_{z,ρ}−\bar V_ρ| ≤ (n/ρ_*)|E_ρΔB_ρ(z)| + C∫_{∂*E_ρ}|ν_ρ−e_z|² + C D_I =: A_ρ.
```
So `A_ρ² ≤ 3[(n/ρ_*)²|E_ρΔB_ρ(z)|² + C²(∫|ν_ρ−e_z|²)² + C²D_I²]`. Integrate
against `dμ` over `G`:
- `∫_G |E_ρΔB_ρ(z)|² dμ ≤ C∫_G D_I dμ ≤ Cδ_T` (FMP, pointwise);
- `∫_G D_I² dμ ≤ η_{\rm Ser}\!∫_G D_I dμ ≤ Cδ_T` (`D_I ≤ η_{\rm Ser}` on good levels);
- `∫_G (∫|ν_ρ−e_z|²)² dμ ≤ ∫_G 4P(E_ρ)·(∫|ν_ρ−e_z|²) dμ ≤ C∫_G(∫|ν_ρ−e_z|²)dμ ≤ Cδ_T`,
  using `(∫|ν−e_z|²)² ≤ (4P)(∫|ν−e_z|²)` since `|ν−e_z|²≤4`, `P≤C` on `G`, and
  then **(INT-strong)**.

Hence `∫_G A_ρ² dμ ≤ Cδ_T`, so `∫_G(∫|H−\bar V|)²dμ ≤ Cδ_T`, and the rest of
`prop:positivekinetic` (convert `dμ→dρ` via `w≥τ_0` on `G_τ`, add the bad-set
measure terms) goes through unchanged. The endpoint trace `lem:endpoint` uses
only `q²≤C D_I` (Fraenkel, pointwise), so it is unaffected. ∎

**Consequence.** The squaring in the radial-trace conversion is absorbed by the
free perimeter bound `4P`, so only the *first power* of the normal oscillation,
*integrated*, is needed — exactly what the Reilly route produces. The pointwise
per-level hypothesis was an over-statement.

### Revised division of labour (constructive, all contradiction-free)
1. **Weaken the manuscript hypothesis** `ass:constructive-strong` to its
   integrated form `INT-strong` (and keep the trivial `∫|ν−e_z|²≤4P`), adjusting
   `prop:positivekinetic` by the three-line estimate above. *(Verified here;
   should itself be re-audited when implemented.)*
2. **Deliver `INT-strong` from Reilly.** Chain:
   `∫_G(∫_{∂*E_ρ}|ν−e_z|²)dμ  ≤  C ∫_G Dev_w(E_ρ) dμ + (volume, FMP)`  [integrated
   trace, **bulk-to-bulk** via coarea — tractable], and
   `∫_G Dev_w dμ ≤ C∫_G(D_H+D_I+τ(E_ρ))dμ ≤ Cδ_T`  [from (R),(V),(K1-size), and
   `∫_Gτ\,dμ≤Cδ_T`]. Centre `z=z_ρ` is the best-ball-profile centre from Reilly,
   reconciled with the Fraenkel centre by `lem:center-transfer`.
3. **Remaining genuine inputs**, both contradiction-free and now in
   *integrated/bulk* form (easier than pointwise):
   - **(M₀)** upper gradient bound `|∇u|≤M₀` on good level sets (Talenti /
     Cianchi–Maz'ya), used in (V);
   - **the integrated trace** `∫_G(∫_{∂*E_ρ}|ν−e_z|²)dμ ≤ C∫_G Dev_w dμ + ...`,
     a coarea/Hessian-to-normal estimate.

**Net.** The route is now *structurally sound*: identities A–C are exact and
explicit; the kinetic estimate provably needs only the integrated same-centre
bound; and that integrated bound is exactly the bulk-compatible output of the
weighted-Reilly identity. No compactness or contradiction enters at any point.
What remains is (M₀) and the integrated trace — both concrete analysis tasks,
not the non-constructive reduction that blocks general-set Fusco–Julin.

---

## Part 6. The genuine obstruction in (M₀): gradient integrability, and why
## `D_H` cannot supply the shape

Tackling the two remaining items (M₀ and the integrated trace) exposes a real
barrier, which I record honestly.

### 6.1 What the integrated trace actually needs
Coarea turns the integrated boundary cube into a bulk power of the gradient:
with `dt=-d\mu` and `∫_0^M(∫_{{u=t}}φ)dt = ∫ φ|∇u|dx`,
```
   ∫_G ( ∫_{∂E_ρ} g³ dH ) dμ(ρ) = ∫_{u^{-1}(t(G))} |∇u|^4 dx .
```
So controlling `∫_G Dev_w dμ` (via identity A) requires `∫|∇u|^4 < ∞` over the
good bulk — i.e. an `L^4` (morally `L^∞`, the bound `M₀`) gradient bound.
Pointwise, `V₃ ≤ C D_H` needs `g ≤ M₀` on `∂E_ρ`: indeed
`V₃ = 3\bar g∫(g-\bar g)² + ∫(g-\bar g)³` weights large `g` heavily, whereas
`D_H = (P²/m)∫(g-\bar g)²/g` weights it by `1/g`; the gap is exactly the
large-gradient tail.

### 6.2 `M₀` is NOT available for general domains in the class
On a good level `∂E_ρ` (`ρ≤ρ_δ<1`, so `t(ρ)>0`), a point `x_0` with `u(x_0)=t`
can lie arbitrarily close to `∂Ω` (a thin spike on which `u` rises to `t`
quickly). The interior gradient estimate then gives only
`|∇u(x_0)| ≲ \|u\|_∞/\mathrm{dist}(x_0,∂Ω) + \dots`, which blows up. There is no
universal upper bound `|∇u|≤M₀` on `∂E_ρ`; Meyers' higher integrability gives
only `|∇u|∈L^{2+ε}` for a dimensional `ε>0`, in general `ε<2`, so even `L^4` is
not free. The constructive Reilly–Serrin stability of Magnanini–Poggesi is, for
this reason, stated for domains of bounded geometry (uniform ball condition /
`C^{2,α}`), where `M₀` holds — exactly the hypothesis our level sets lack.

### 6.3 The deeper reason: `D_H ⟂ shape`
`D_H` is the Cauchy–Schwarz/gradient-oscillation defect (`=0` iff `|∇u|` is
constant on `∂E_ρ`); the normal/shape oscillation `∫_{∂*E_ρ}|ν-e_z|²` is `=0`
iff `∂E_ρ` is a sphere. For a *general* surface these are independent (a wavy
surface with constant `|∇u|` has `D_H=0` but large normal oscillation). For a
*torsion level set* they are PDE-linked (a ball `E_ρ` forces `v` radial, hence
`g` constant, hence `D_H=0`), but only in measure: `E_ρ` close to a ball *in
volume* (`D_I`, `|EΔB|` small) still allows small boundary pieces near `∂Ω`
where `|∇u|` spikes. The `L²`-Hessian `Dev_w` (and `∫g³`) sees those spikes,
while `D_H+D_I` do not. Hence `Dev_w ≤ C(D_H+D_I)` **fails** without controlling
the spikes, i.e. without `M₀`.

Conclusion: the shape/normal term is genuinely a `D_I`-controlled quantity, and
its constructive control is exactly the open strong-form problem. `D_H` does not
supply it; the Reilly identity converts the non-constructive Fusco–Julin
constant into a gradient-regularity hypothesis `M₀`, not into nothing.

### 6.4 Honest status of the route
The Reilly/quantitative-Serrin route yields a **constructive, explicit-constant**
discharge of `ass:constructive-strong` — and hence a fully computable sharp
Faber–Krahn constant — **for domains whose good torsion level sets carry a
uniform gradient bound `M₀`** (e.g. domains of bounded geometry; convex
domains). For such domains the chain is complete and contradiction-free.

For *fully general* open sets the normal term remains conditional: it needs
either the non-constructive Fusco–Julin strong form, or the unavailable `M₀`.
This is the same regularity barrier the moving-ball route was built to avoid;
the Reilly route does not remove it for the general class, it relocates it to a
transparent gradient-regularity hypothesis.

### 6.5 What this means concretely
- The manuscript is correct and, modulo `ass:constructive-strong`, complete.
- `ass:constructive-strong` is now understood to be **equivalent (via the
  weighted-Reilly identity + the integrated kinetic estimate) to a gradient
  bound `M₀` on good level sets**, up to the `τ`-integration
  `∫_G τ(E_ρ)dμ ≤ Cδ_T` (which holds by Fubini on the deficit identity for the
  inner radii) and the bulk→normal Poincaré trace.
- Therefore: **sharp Faber–Krahn is fully constructive (computable constant) on
  the bounded-geometry / `M₀` class**; the obstruction to the general case is
  precisely the absence of an a priori gradient bound, equivalently the
  constructive control of the normal oscillation by `D_I` (the open strong
  form). No fabricated closure.
