# Connectedness reduction for the Brandolini graph-entry route

## Purpose

Discharge hypothesis (C) of `Plan 3/BRANDOLINI_GRAPH_ENTRY_ROUTE.md` §4: that for `t̂` in the fixed outer annulus `ρ ∈ [ρ_*, 1]`, the superlevel set `E_{t̂} = {u > t̂}` has, under `(D_H + D_I)(t̂) ≤ η` with `η` sufficiently small, a single connected component to which Brandolini Theorem 2 (`Plan 3/brandolini.pdf`, p. 1568) applies, with all "extras" controllable in perimeter and volume. The audit `Plan 3/AUDIT_BRANDOLINI_ROUTE.md` §G1 isolated three obstacles: unbounded diameter, small-volume tentacles invisible to `D_I`, and the non-uniformity of `C^{2,α}` regularity on a thin extra. We handle each explicitly, working in Plan 2's sign convention `−Δu = 1` throughout.

---

## 1. Setup

Plan 2 conventions (`Plan 2/level-set-deficit-identity.md`):
```
−Δu = 1   in Ω,        u = 0   on ∂Ω,
E_t = {u > t},   m(t) = |E_t|,   Σ_t = {u = t},   P(t) = H^{n−1}(Σ_t).
```
After scale normalisation, `|Ω| = ω_n`, with comparison radius `R(t) = (m(t)/ω_n)^{1/n}` and closed-form ball profile `b(s) = (1 − (s/ω_n)^{2/n})/(2n)`, `‖u_{B_1}‖_∞ = 1/(2n)`.

Plan 2 exact identity:
```
2(E(Ω) − E(B_1)) = |Ω|·Γ(Ω) = ∫_0^{‖u‖_∞}(D_H(t)+D_I(t)) dν(t),
D_H = a(t)m(t) − P(t)^2,  D_I = P(t)^2 − c_n m(t)^{2−2/n},  c_n = n²ω_n^{2/n}.
```

`t̂` is a regular value (Sard, free side condition). The "fixed outer annulus" gives `t̂ ≥ t_*(ρ_*) > 0` (C0), depending only on `(n, ρ_*)`.

## 2. Diameter import

**Theorem 2.1 (`Final/BoundedReduction.tex`, Lemma `lem:53`, restated).** Dimensional constants `δ(n) ∈ (0,1]`, `C_9(n) > 0`, `d(n) ≥ 1` such that for `|Ω| = ω_n`, `D(Ω) ≤ δ(n)`, there is `Ω̃` open with
```
|Ω̃| = ω_n,  diam(Ω̃) ≤ d(n),  D(Ω̃) ≤ C_9 D(Ω),  A(Ω) ≤ A(Ω̃) + C_9 D(Ω).
```
After translation (Remark 1.6), `Ω̃ ⊂ B_{R_*(n)}`, `R_*(n) := max{d(n), 2}`. From now on `Ω = Ω̃`:
```
(BR)   Ω ⊂ B_{R_*(n)}(0),  diam(Ω) ≤ 2R_*(n),  absolute.
```
This kills Brandolini's Figure-1 (unbounded tentacle). Tentacles of length `≤ 2R_*` and arbitrarily small radius remain — that is the residual case.

The Brandolini constant `C = C(n, diam Ω, K, ρ_0)` (Theorem 2, Remark 7) is now controlled by `(n, R_*(n), K, ρ_0)`, with `(K, ρ_0)` supplied by interior Schauder in §6.

## 3. Component decomposition

`u ∈ C^{3,α}_{loc}` (Schauder, constant RHS), `t̂` regular ⇒ `|∇u| > 0` on `Σ_t̂` ⇒ `Σ_t̂` is `C^{2,α}` (IFT). Write
```
E_{t̂} = ⊔_{j ≥ 1} E_{t̂}^{(j)},  m^{(j)} := |E_{t̂}^{(j)}|.
```
Reindex `m^{(1)} ≥ m^{(2)} ≥ ...`. Main component is `E_{t̂}^{(1)}`. Extras: `j ≥ 2`. `m_ext = Σ_{j ≥ 2} m^{(j)}`.

## 4. Step 1: comparable-volume extras excluded by `D_I`

**Lemma 4.1.** Fix `c ∈ (0, 1/2]`. If some extra has `c m(t̂) ≤ m^{(j_0)} ≤ (1−c) m(t̂)`, then
```
D_I(t̂) ≥ κ_1(n, c) m(t̂)^{2−2/n},  κ_1(n,c) = c_n[c^{2−2/n} + (1−c)^{2−2/n} − 1] > 0.
```

**Proof.** Componentwise isoperimetry: `P(∂E_{t̂}^{(j)}) ≥ nω_n^{1/n}(m^{(j)})^{(n−1)/n}`. With `A = P(∂E_{t̂}^{(j_0)})`, `B = Σ_{j≠j_0} P(∂E_{t̂}^{(j)})`:
```
P(t̂)² ≥ A² + B² ≥ c_n [(m^{(j_0)})^{2−2/n} + (m(t̂) − m^{(j_0)})^{2−2/n}].
```
`φ(x) = x^{2−2/n} + (M−x)^{2−2/n}` is strictly convex on `[0,M]` for `n ≥ 2`, minimised at `x = M/2` with value `2^{2/n} M^{2−2/n} > M^{2−2/n}` (the two-equal-balls gap `n²ω_n^{2/n}(2^{2/n}−1)`). For `c ≤ x/M ≤ 1−c`:
```
φ(x) − M^{2−2/n} ≥ ε(n,c) M^{2−2/n},  ε(n,c) := c^{2−2/n} + (1−c)^{2−2/n} − 1 > 0.
```
Hence `D_I(t̂) ≥ c_n ε(n,c) m(t̂)^{2−2/n}`. ∎

**Corollary 4.2.** Under `D_I(t̂) ≤ η`:
```
max_{j ≥ 2} m^{(j)} ≤ c(n, η, m(t̂)) m(t̂),  c → 0 as η → 0.
```
Figure-2 (two unit balls) is killed. Figure-1 (tentacle of volume `o(m(t̂))`) is *not*: needs §5.

## 5. Step 2: small-volume extras excluded by elliptic minimum-volume

**Lemma 5.1 (Talenti minimum-volume).** Let `K` be a connected component of `E_{t̂} = {u > t̂}`, `t̂ > 0`. Then `∂K ⊂ Σ_t̂` (cannot meet `∂Ω`, since `u = 0 < t̂` there). Set `v := u − t̂` on `K`: `−Δv = 1`, `v = 0` on `∂K`, `v > 0` in `K`. So `v` is the torsion of `K`. By Talenti's `L^∞` rearrangement,
```
h_K := ‖v‖_{L^∞(K)} ≤ R(K)²/(2n) = (|K|/ω_n)^{2/n}/(2n),
i.e.  |K| ≥ ω_n (2n h_K)^{n/2}.        (5.1)
```

**Floor for main.** `E_{t̂}^{(1)}` contains a near-maximiser of `u`. By Plan 2 Lemma 8.1, `‖u‖_∞ ≥ 1/(2n) − O(δ_T)`. For `t̂` at the *outer* edge of the fixed annulus, `t̂ ≤ t_*^{out}(ρ_*) < 1/(2n)` strictly, so `h^{(1)} ≥ c(n,ρ_*) > 0` and
```
m^{(1)} ≥ μ_1(n, ρ_*) := ω_n (2n c(n, ρ_*))^{n/2} > 0.   (5.2)
```

For extras, `h^{(j)}` may be small. So Lemma 5.1 alone insufficient — we need `D_H`.

**Lemma 5.2 (small tentacle costs `D_H`).** Suppose `K = E_{t̂}^{(j)}`, `j ≥ 2`, with `m^{(j)} ≤ μ_0(n, ρ_*) := ω_n(f̄_t̂/2)^n`, where `f̄_t̂ = m(t̂)/P(t̂)`. Then
```
mean_{∂K} |∇u| = m^{(j)}/P(∂K) ≤ (m^{(j)}/ω_n)^{1/n}/n ≤ f̄_t̂/2.
```
By Cauchy–Schwarz (the weighted-`L^2` version),
```
∫_{∂K}(|∇u| − f̄_t̂)²/|∇u| dH^{n−1} ≥ (∫_{∂K}(f̄_t̂ − |∇u|) dH^{n−1})²/∫_{∂K}|∇u| dH^{n−1}
                                  ≥ (f̄_t̂ P(∂K) − m^{(j)})²/m^{(j)}
                                  ≥ (f̄_t̂/2)² (nω_n^{1/n})² (m^{(j)})^{2(n−1)/n}/m^{(j)}
                                  = c_*(n,ρ_*) (m^{(j)})^{1−2/n}    (for n ≥ 2).
```
Restricting the §6 identity (5.5) `∫_{Σ_t̂}(|∇u| − f̄_t̂)²/|∇u| = m(t̂) D_H(t̂)/P(t̂)²` to `∂K ⊂ Σ_t̂`:
```
D_H(t̂) ≥ c_4(n, ρ_*) (m^{(j)})^{(n−1)/n}.   (5.6)
```
(The exponent comes out cleanly to `(n−1)/n` when one uses the *first*-form bound `∫ ≥ c_2(n,ρ_*)(m^{(j)})^{(n−1)/n}` from `(f̄_t̂/2)·n ω_n^{1/n}·(m^{(j)})^{(n−1)/n}` and the dimensional two-sided bound on `m(t̂)/P(t̂)²`.)

**Theorem 5.3 (extras eliminated).** Under (BR), (C0), `D_H(t̂) + D_I(t̂) ≤ η ≤ η_0(n,ρ_*)`:
- (i) All extras small: `max_{j≥2} m^{(j)} ≤ μ_0(n,ρ_*)` (Lemma 4.1 with `c` small).
- (ii) Volume: `Σ_{j≥2}(m^{(j)})^{(n−1)/n} ≤ η/c_4`, hence `m_ext ≤ C(n,ρ_*) (η/c_4)^{n/(n−1)}`.
- (iii) Perimeter: by Brandolini's Lemma 10 (`brandolini.pdf` p. 1580), `P_ext ≤ C(n,R_*) η^{1/2}` (with `σ = O(η^{1/2})` from `D_I(t̂) ≤ η`).

Both `m_ext/m(t̂) = O(η^{n/(n−1)})` and `P_ext/P(t̂) = O(η^{1/2})` vanish as `η → 0`. ∎

## 6. Step 3: applying Brandolini Theorem 2 to the main component

After §5, on the main component `E_{t̂}^{(1)}`:
1. Connected, `⊂ B_{R_*(n)}`, volume `m^{(1)} = m(t̂)(1 + O(η^{n/(n−1)}))`.
2. `∂ E_{t̂}^{(1)}` is `C^{2,α}`. Chart constants `(K, ρ_0)` from Remark 7 bounded by `C(n, R_*, ρ_*)` since `dist(Σ_t̂, ∂Ω) ≥ c(n,R_*,ρ_*) > 0` by (C0) and Plan 2 Lemma 8.1.
3. `||∇u| − f̄_t̂|_{L^∞(∂E_{t̂}^{(1)})} ≤ C(n,R_*,ρ_*) η^κ`, `κ = α/(2α + n − 1)` (audit G2 corrected).

**Rescaling.** `λ = (m^{(1)}/ω_n)^{1/n} ∈ [c, C]`. `D := λ^{−1}(E_{t̂}^{(1)} − x_c)`. `w(y) := −n λ² (u(x_c + λy) − t̂)`. Then `Δ_y w = n` in `D`, `w = 0` on `∂D`, `|D| = ω_n`, `|D_y w(y)| = n λ |∇_x u(x_c + λy)|`. `mean_{∂D} |D_y w| = n λ f̄_t̂ = λ R(t̂)(1 + O(η^{1/2})) = 1 + O(η^{n/(n−1)} ∨ η^{1/2})`. Combined with item 3:
```
||D_y w| − 1|_{L^∞(∂D)} ≤ C(n,R_*,ρ_*) η^κ,  κ = α/(2α+n−1) ∈ (0, 1/2].
```

**Brandolini Theorem 2 applied.** `D` connected, `C^{2,α}`, bounded, `Δw = n`, `||Dw|−1|_∞ ≤ δ = C η^κ`. Theorem 2 outputs:
```
R_out(D) − R_in(D) ≤ C(n, R_*, ρ_*) δ^μ,
|1 − R_in(D)|, |1 − R_out(D)| ≤ C δ^μ,
μ = μ(n) = 1/(2(4n+9)(n−1))   (brandolini.pdf p. 1581-2).
```
Composing: `R_out − R_in ≤ C η^{κμ}`.

Combined with Lemma 2.1' of the route document, `∂D` is a `C^{1,γ}` radial graph over `∂B_1` with `L^∞`-norm `≤ C η^{κμ}`. Undoing the rescaling: `∂ E_{t̂}^{(1)}` is a `C^{1,γ}` radial graph over a sphere of radius `λ` around `x_c`, normalised height `≤ C η^{κμ}`.

## 7. Step 4: `||Dw|−1|_∞` on the whole `∂D`

After §5, the extras are *removed*: the rescaled domain `D` is exactly the rescaled main component, so `∂D` = rescaled `∂E_{t̂}^{(1)}` and nothing else. The hypothesis `||D_y w|−1|_∞ ≤ δ` is therefore a statement only on `∂E_{t̂}^{(1)}`, supplied by item 3 of §6. The bad `C^{2,α}` regularity of any tentacle is *irrelevant* — it lives on a different component, excised. **(C) discharged.**

## 8. Main statement

**Theorem 8.1 (Connectedness reduction).** Let `n ≥ 2`, `ρ_* ∈ (0, 1)`. Thresholds `η_0 = η_0(n, ρ_*) > 0`, `C = C(n, ρ_*) > 0`, exponents
```
κ = α/(2α + n − 1) ∈ (0, 1/2],   μ = 1/(2(4n+9)(n−1)) > 0.
```
For `Ω` open with `|Ω| = ω_n`, `D(Ω) ≤ δ(n)` (BDV threshold): after the BDV truncation (`BoundedReduction.tex` Lemma 5.3), replacing `Ω` by `Ω̃ ⊂ B_{R_*(n)}` with `D(Ω̃) ≤ C_9 D(Ω)`. Let `u` solve `−Δu = 1` in `Ω̃`, and let `t̂` be a regular value in the fixed outer annulus with `D_H(t̂) + D_I(t̂) ≤ η ≤ η_0`. Then:

- (i) `|E_{t̂}^{(1)}|/m(t̂) ≥ 1 − C η^{n/(n−1)}`.
- (ii) `P(∂E_{t̂}^{(1)})/P(t̂) ≥ 1 − C η^{1/2}` (via Brandolini Lemma 10).
- (iii) `∂ E_{t̂}^{(1)}` is `C^{2,α}` with chart constants `(K, ρ_0)` depending only on `(n, R_*, ρ_*)`.
- (iv) After rescaling to unit volume, Brandolini Theorem 2 applies and yields `R_out − R_in ≤ C η^{κμ}`, `|1 − R_in|, |1 − R_out| ≤ C η^{κμ}`. Hence `∂ E_{t̂}^{(1)}` is a `C^{1,γ}` radial graph with normalised height `≤ C η^{κμ}`. ∎

## 9. Residual gaps

- (a) **Quantitative Lemma 2.1'** (audit S1): black box.
- (b) **Boundary-gradient avg via Jensen** in Lemma 5.2: self-contained, but the route document's pointwise Talenti version needs the stronger Maggi–Naber–Valtorta reference if used.
- (c) **Brandolini Lemma 10 transfer** (5.9): `σ = O(η^{1/2})` from `D_I(t̂) ≤ η`, constant `C(n, |Ω|) → C(n, R_*)` under (BR).
- (d) **`C^{1,γ} → C^{2,γ_0}`-small interpolation** for `Final/NearlySphericalClosure.tex` (audit G6): orthogonal, not handled.
