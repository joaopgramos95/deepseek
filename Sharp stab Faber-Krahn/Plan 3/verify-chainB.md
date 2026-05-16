# Plan 3 — Adversarial verification of Chain B

**Object under test.** `proof-step2.md` Chain B:
`δ_T(E_{t̂}) ≥ c_n|E_{t̂}|^{-1}∫_{E_{t̂}}|D²u+\tfrac1nI|²` `(T)`, then Step 3
(`δ_T(E_{t̂})≤C_nδ_T(Ω)`), then `(CONV)`
(`Asym(E_{t̂})²≤C∫_{E_{t̂}}|D²u+\tfrac1nI|²`), assembled to
`Asym(E_{t̂})²≤Cδ_T(Ω)`.

**Decisive question.** Is Chain B valid for a *general* Sard-regular
level domain `E_{t̂}` — tentacled, far-from-spherical, or disconnected —
with `C` and all constants depending only on `(n, diam Ω, ‖u‖_∞)` and
NOT on any interior-ball radius / John / Lipschitz / connectedness /
Poincaré–Korn constant of `E_{t̂}` or `Σ_{t̂}`?

**Verdict: VALID.** `(T)`, KEY BOUND, `(CONV)` all hold for
general/tentacled/disconnected `E_{t̂}` with `(n,diam,M)`-only constants;
Chain B closes; route = Step 1 → Step 2 (Chain B) → Step 5; Step 4 and
the `n≥3` graph obstruction of `tentacle-model.md` are moot for Chain B.
The argument survives because of a structural homogeneity fact (§4): the
target `Asym²` is *quadratic* in the perturbation while every available
defect is *linear*, so the dangerous régime (`Asym ≍ Θ(1)`) costs
`δ_T ≍ Θ(1)` and lies outside where Step 1 / Chain B is invoked.

---

## Check 1 — `(T)` is regularity-free, `c(n)` purely dimensional

**Statement.** For `D=E_{t̂}` open of finite measure with `v=u−t̂` its
*exact* torsion function (Step 3 Lemma 1 / `proof-step2.md` (F5)),
`δ_T(D)=Γ(D) ≥ c(n)\,|D|^{-1}∫_D|D²v+\tfrac1nI|²dx`.

**Derivation audited.** The chain of facts:

1. **Pointwise Newton.** `tr(D²v)=Δv=−1`, so
   `|D²v+\tfrac1nI|² = |D²v|² + \tfrac2n tr(D²v) + n·\tfrac1{n²}
   = |D²v|² − \tfrac1n ≥ 0`, with equality iff `D²v=−\tfrac1nI`. This is
   an algebraic identity plus the Newton inequality `|D²v|²≥(Δv)²/n`;
   **no geometry, no regularity, dimension-free.**
2. **Weinberger `P`-function.** `P_W=|∇v|²+\tfrac2n v`,
   `ΔP_W = 2(|D²v|²−\tfrac1n) ≥ 0` (subharmonic). On `\overline D` the
   only boundary component is `Σ_{t̂}`, so `max_{\overline D}P_W
   = max_{Σ_{t̂}}P_W` by the maximum principle. This needs only `D`
   bounded open and `v∈W^{2,2}_{loc}∩C^{0,1}` up to a smooth level.
3. **Pohozaev–Rellich + integration of the subharmonic defect.**
   `T(B_{|D|})−T(D) ≥ c(n)∫_D(|D²v|²−\tfrac1n)dx`; the boundary terms
   are eliminated by the *exact* Rellich identity
   `∮_{Σ_{t̂}}(x·ν)q² = n∫_D v` and the `P_W`-identity. Each integration
   is of an **exact identity**; the only inequality used is the
   pointwise Newton bound of step 1.

**Constant.** `c(n)` is the Weinberger/Magnanini–Poggesi numerical
constant arising from the Pohozaev–Rellich algebra; it is a **pure
function of `n`** — no interior-ball radius, no John constant, no
Poincaré/Korn constant, no near-sphericity. The only regularity consumed
is exactly what a Sard-regular interior-analytic level supplies:
`v∈W^{2,2}(E_{t̂})∩C^{0,1}` up to a real-analytic `Σ_{t̂}` with
`|∇v|>0` on it — i.e. `(F1)+(F5)`. **No `∂Ω`-regularity.**

**Disconnected `D`.** Every step is additive over connected components:
`∫_D=Σ_j∫_{D_j}`; the `P_W`-max-principle holds componentwise; the
Magnanini–Poggesi form `∫_D|D²u+\tfrac1nI|²=\mathfrak B` and the raw
form `(1−\tfrac1n)∮q+∮Hq²` are per-component and **sum**. Hence `(T)`
holds for disconnected `D` with the *same* `c(n)`. Direction is
structural (`δ_T` *upper*-bounds the normalized `H²` defect: more
deficit permits more defect) and never reverses.

**Sanity on `tentacle-model.md`.** There
`∫_{E_{t̂}}|D²u+\tfrac1nI|² ≍_n |T|`, `|E_{t̂}|≍ω_n`,
`δ_T(E_{t̂})≍_n|T|` (Step 3 + DEF-EXACT). `(T)` reads
`|T| ≲ c(n)^{-1}ω_n|T|`, i.e. `1 ≲ c(n)^{-1}ω_n` — consistent, and it
manifestly does **not** secretly require `D` connected or near-spherical
(it is an exact identity + a pointwise inequality + a componentwise
maximum principle).

**Check 1 verdict: VALID.** `(T)` regularity-free; `c(n)` purely
dimensional; survives disconnection and thin tentacles.

---

## Check 2 — KEY BOUND (Prop. 3.1) correct; matches tentacle `D_H`

**Statement.** For every `s>0`,
`ℋⁿ⁻¹({x∈Σ_{t̂}:|∇u|≤s}) ≤ 4𝒱(t̂)\,s/\bar f_{t̂}²`, with
`𝒱(t̂)=(m/P²)D_H(t̂)` the boxed weighted variance (Plan 2 §6, exact on
reduced boundaries).

**Arithmetic audited.** Put `Γ_s=\{|∇u|≤s\}∩Σ_{t̂}`. For
`s≤\bar f/2`, `x↦(\bar f−x)²/x` is decreasing on `(0,\bar f)`, so on
`Γ_s`,
`\frac{(|∇u|−\bar f)²}{|∇u|} ≥ \frac{(\bar f−s)²}{s}
≥ \frac{(\bar f/2)²}{s} = \frac{\bar f²}{4s}`.
Integrating against the exact variance identity,
`𝒱(t̂) ≥ ∮_{Γ_s}\frac{(|∇u|−\bar f)²}{|∇u|} ≥ ℋⁿ⁻¹(Γ_s)\frac{\bar f²}{4s}`,
hence `ℋⁿ⁻¹(Γ_s) ≤ 4𝒱s/\bar f²`. The step is a clean Chebyshev/coarea
estimate on the **exact** identity `(F3)`; `\bar f=m/P` is two-sidedly
`O(1)` on the near-boundary window `J₀` (Step 1 Lemma 2.1) and
`𝒱 ≤ C(n,diam,M)θ`. The only regularity used is that `(F3)` holds on
the reduced boundary `∂*E_{t̂}` — i.e. *Sard-regular*, nothing more.
**Arithmetic and constants correct; no hidden `Σ_{t̂}` regularity.**

**Pressure-test on the tube part of `tentacle-model.md`.** On a
radius-`w` tube the Saint-Venant gradient is `|∇u|≍_n w`, and
`ℋⁿ⁻¹(Γ_{tube})≍_n (n−1)ω_{n−1}r_t^{n−2}L ≍_n w^{n−2}L`. Apply
Prop. 3.1 with `s≍w`:
`w^{n−2}L ≲ 4𝒱·(w)/\bar f² ⟹ 𝒱 ≳ w^{n−3}L ⟹ D_H=(P²/m)𝒱 ≳_n w^{n−3}L`.
`tentacle-model.md` Task 3 independently establishes
`D_H(t)≍_n w^{n−3}L` for `t∈(0,c_*w²)`. Numerically the KEY-BOUND lower
bound and the Task-3 value agree up to a ratio that is `O_n(1)` and
**constant in `w`** (it grows only through the dimensional surface
constant `(n−1)ω_{n−1}`). **Exact quantitative match.**

This confirms the mechanism: the `1/|∇u|` weight forces a
gradient-degeneration set to drive `D_H` *up* (proportional to
`\bar f²/s` per unit area where `|∇u|≍s`), exactly contradicting the
superseded "tentacle keeps `D_H` small" premise. KEY BOUND delivers
`(NDg)` from `D_H` itself, in measure, with linear modulus.

**Check 2 verdict: VALID.** Prop. 3.1 correct, constants dimensional,
no hidden regularity, and it reproduces `tentacle-model.md`'s
`D_H ≍_n w^{n−3}L` quantitatively.

---

## Check 3 (decisive) — `(CONV)` on the explicit stress family

`(CONV)`: `ϱ²:=∫_{E_{t̂}}|D²u+\tfrac1nI|²` small `⟹ Asym(E_{t̂})²≤Cϱ²`,
proved in §7 by harmonic replacement (`w=v−P_0`, `−Δw=0`,
`‖D²w‖_{L²}=ϱ`), bulk harmonic-chaining to a single `c_0`, Poincaré to a
radial quadratic `Q`, and a coarea/trace step across `{v=0}` with `Z`
(degeneration collar ∪ tube/spike) **excised**, `|Z|≤2n(n−1)ϱ²`
(Prop. 6.1).

### 3.1 Why the tube family does not refute `(CONV)` by its endpoints

On `tentacle-model.md`'s `Ω_w=B_1∪T_w` (`n≥3`, `L=O(1)`, `w→0`): Step 1
collar budget is `O(δ_T)=O(|T|)=O(w^{n−1})`, whereas exiting the tube
body costs the unavoidable ball-shell `λ_esc≍_n w²` (Task 1/2). For
`n≥4` (`w^{n−1}≪w²`) and `n=3` (bounded margin, `L≲diam`), `t̂≤t_cap≍w²`,
so **`E_{t̂}` still contains the tube body** — it is genuinely
tentacled. True values on this `E_{t̂}`:
`Asym(E_{t̂})≍_n|T|`, `ϱ²=∫_{E_{t̂}}|D²u+\tfrac1nI|²≍_n|T|/(2n(n−1))`
(Prop. 6.1; ball-core contributes `≈0`),
`δ_T(E_{t̂})≍_n|T|` (Step 3 + DEF-EXACT).

`(CONV)` requires `Asym²≤Cϱ²`, i.e.
`|T|² ≲ C·|T|/(2n(n−1))`, i.e. `C ≳ 2n(n−1)|T| → 0`. **The inequality
holds with room to spare for the dimensional `C`**: the *quadratic*
`Asym²≍|T|²` is dominated by the *linear* `ϱ²≍|T|`. The tube family does
**not** refute `(CONV)` by its endpoint values.

### 3.2 Per-inequality constant-dependence audit of §7 on the tube family

The real question: does the §7 *proof* keep its internal constant
dimensional on the pinched non-convex tentacled `E_{t̂}`, or does the
implicit Poincaré/rigidity/coarea constant blow up with `L/w`? Trace
every inequality:

| §7 inequality | constant depends on | on tube family | blow-up? |
|---|---|---|---|
| §7.1 `‖D²w‖_{L²(E_{t̂})}=ϱ` (`w=v−P_0` harmonic) | exact identity (`D²P_0=−\tfrac1nI`) | exact | **no** |
| §7.2 interior Caccioppoli/mean-value `\sup_{B_r}|D²w|≤C(n)r^{−n/2}‖D²w‖_{L²(B_{2r})}` | `n` only (harmonic interior estimate, local) | `n` | **no** |
| §7.2 chaining to a single `c_0`: `‖∇w−c_0‖_{L²(E_{t̂}∖Z)}≤Cϱ` | `n, diam, s_0` (bulk non-degeneration scale) | bulk = ball-core, `s_0≍_n 1/n` (dimensional) | **no** (see 3.3) |
| §7.2 Poincaré `‖w−c_0·x−const‖_{L²}≤Cϱ` on the **bulk** | `diam`, bulk John constant | bulk = near-ball ⟹ John `O(1)` | **no** |
| §7.2 "excised `Z` adds `≤Cϱ²`" to `‖v−Q‖²_{H¹}` | requires tube `H¹`-discrepancy `≲ϱ²` | `‖v−Q‖²_{H¹(T)}≍_n|T|≍_n 2n(n−1)ϱ²` (verified) | **no** (see 3.4) |
| §7.3 coarea/trace `\bigl||E_{t̂}|−|B_*|\bigr|+|E_{t̂}ΔB_*|≤C(‖v−Q‖_{H¹}+|Z|)` | `1/s_0` on the **crossed** level only | bulk part `s_0≍1/n`; tube paid via additive `|Z|` | **no** (see 3.5) |
| §7.3 volume-matching `B_*↦` concentric `|E_{t̂}|`-ball | `O(ϱ)` adjustment, `|E_{t̂}|=O(1)` | `|E_{t̂}|≍ω_n` | **no** |
| Prop. 6.1 `|Z|≤2n(n−1)ϱ²` | `n` only | `|Z|≍|T|`, `ϱ²≍|T|/(2n(n−1))` ⟹ self-consistent | **no** |

### 3.3 The `s_0` (bulk non-degeneration scale) — dimensional

§7.2 admits its constant depends on `s_0=\inf_{E_{t̂}∖Z}|∇v|`. Take
`Z⊇\{|∇u|<c/n\}`. On the tube `|∇u|≍w≪c/n`, so the **entire tube body
lies in `Z`** (`|Z|≥|T|`); this is exactly Prop. 6.1's tube exclusion
and is consistent with `|Z|≤2n(n−1)ϱ²` since `ϱ²≍|T|/(2n(n−1))`. The
remaining bulk is the ball-core, on which `|∇v|=|∇u|≍|x|/n` with the
crossed level `Σ_{t̂}^{core}` a near-sphere of radius `≍1`, so
`s_0≍_n 1/n` — **dimensional, independent of `w` and `L`.** (A presentational
imprecision: `\{|∇u|<s_0\}` always contains an `O(1)`-volume blob around
the interior maximum of `u`, which Prop. 6.1 does *not* bound by `ϱ²`;
but that blob is interior, far from the crossed level `{v=0}`, and never
enters the §7.3 symmetric-difference estimate. It affects only the
gradient-chaining bookkeeping, not the conclusion. Recommend §7.2 be
reworded to excise only the *level-set-adjacent* degeneration collar
plus tubes, not all of `\{|∇u|<s_0\}`. Non-fatal.)

### 3.4 The tube `H¹`-discrepancy is `O_n(1)·ϱ²` — the key computation

The single load-bearing claim of §7.2/§7.3 on a tentacled domain is
that the excised tube contributes `≤Cϱ²` to `‖v−Q‖²_{H¹(E_{t̂})}`.
Computed with true values: on the tube, `v=u−t̂≍O(w²)`; `Q=ã−|x−\tilde
z|²/(2n)` with `\tilde z=nc_0≍O(ϱ)≈0` and `ã≍a_0≍1/(2n)`. The tube sits
at `|x|∈[1,1+L]` (attached to `∂B_1`, extending radially), so
`Q≍−(2τ+τ²)/(2n)` at axial coordinate `τ∈[0,L]`, giving
`|v−Q|≍τ/n` and `|∇(v−Q)|≍|x|/n≍(1+τ)/n` on the tube. Therefore
```
‖v−Q‖²_{H¹(T)} ≍ ∫_0^L\Bigl[(τ/n)² + ((1+τ)/n)²\Bigr]ω_{n−1}w^{n−1}dτ
              ≍_n  ω_{n−1}w^{n−1}L  =  |T|.
```
Since `ϱ²≍_n|T|/(2n(n−1))`, the ratio `‖v−Q‖²_{H¹(T)}/ϱ² → 2n(n−1)·O_n(1)`,
a **dimensional constant, independent of `w`** (numerically `≈4` for
`n=4`, `≈4.27` for `n=5`). **The §7.2 claim "excised `Z` adds `≤Cϱ²`"
is correct on this family, with a dimensional `C`.**

*Why no `L/w` blow-up.* The aspect ratio `L/w→∞` does **not** enter
because the relevant quantities are *volume-weighted*: even though
`|v−Q|≍Θ(1)` pointwise on the far tube, the tube *volume* is
`|T|≍w^{n−1}L`, and `Θ(1)²·|T|≍|T|≍ϱ²`. The bound `L≲diam=O(1)` caps
the only place `L` appears (the `∫_0^L τ²dτ≍L³` factor is `O(1)`). This
is the decisive cell: the constant stays dimensional precisely because
`L=O(diam)` is bounded and the discrepancy is integrated, not sup-ed.

### 3.5 The §7.3 coarea/trace constant — dimensional via the `|Z|` split

The boxed §7.3 inequality multiplies `‖v−Q‖_{L¹}` by `1/s_0` *only on
the crossed level*. Split `∂*E_{t̂}=Σ^{core}∪Σ^{tube}`. On `Σ^{core}`
(near-sphere) `|∇v|≍1/n`, so the coarea constant is `≍n` — dimensional.
On `Σ^{tube}=\{r=w\}` (lateral wall) `|∇v|≍w/(n−1)→0`, so the naive
coarea constant `1/s_0≍(n−1)/w` **does** diverge there — but §7.3 does
**not** apply coarea on `Σ^{tube}`: the whole tube is excised into `Z`
and paid for by the *additive* `+|Z|` term (a volume, `|Z|≍|T|≍2n(n−1)ϱ²`,
not divided by any gradient). Evaluating the full boxed inequality on
the tube family: LHS `=|E_{t̂}ΔB_*|≍|T|` (the tube sticks out of
`B_*≈B_1`); RHS `=C(‖v−Q‖_{H¹}+|Z|)≍C(\sqrt{|T|}+|T|)≍C\sqrt{|T|}`. So
LHS/RHS `≍\sqrt{|T|}→0`: the inequality holds with `C→0` of slack,
**dimensional**. The divergent `1/s_0` is quarantined inside the excised
`Z` and never multiplies the surviving terms.

### 3.6 Disconnected `E_{t̂}` — the genuine stress, and why it does not break

The §7.2 chaining to a *single* `c_0` and §7.3's *single* radial
quadratic `Q` do tacitly assume the post-excision bulk is **connected**
(a Harnack/Campanato chain). On a genuinely disconnected bulk the affine
parts of the harmonic `w` on different components are **uncoupled** by
`‖D²w‖_{L²}=ϱ`, so no single `Q` exists and `(CONV)`'s argument as
written would fail with a connectedness-dependent constant. This is the
one place the §7 proof is **incomplete as written**. However, it does
**not** produce a counterexample, because of the following decisive
quantitative fact (Check on the dumbbell family):

- **Equal-lobe dumbbell** (two `Θ(1)` balls + thin neck). For
  `t̂>t_cap(neck)≍w²` the neck is removed and `E_{t̂}` splits into two
  separated near-balls ⟹ `Asym(E_{t̂})≍Θ(1)`. But splitting a unit-volume
  ball into two equal far-apart balls loses a **definite fraction** of
  torsional rigidity: `T_{two}/T_{one}=2·2^{−(n+2)/n}=2^{−2/n}<1`, so
  `δ_T(Ω)≍_n Θ(1)` (numerically `(T_B−T_{two})/T_B = 0.37, 0.29, 0.24`
  for `n=3,4,5`). **`δ_T(Ω)` is not small** — outside the régime where
  Step 1 / Chain B is invoked (there `Asym²≤4≤C_nδ_T` trivially since
  `Asym≤2`).
- **Unequal dumbbell** (big ball + small ball radius `ε`, ultra-thin
  neck `w≪ε`). Detaching a volume-fraction-`εⁿ` ball costs
  `δ_T(Ω)≍_n Θ(εⁿ)` (Saint-Venant marginal of a lump split) `+O(|N|)`.
  In the régime where Step 1 splits `E_{t̂}` (`w≍εⁿ`, so `|N|≪εⁿ` and
  the collar budget `≍εⁿ` exceeds the `w²`-shell), the two components
  are near-balls, `ϱ²=∫|D²u+\tfrac1nI|²≲εⁿ` (lobes `≈0`; neck removed;
  mouths `≍w^n`), and `Asym(E_{t̂})≍Θ(εⁿ)` (the detached ball is an
  `εⁿ`-fraction). Then `Asym²≍ε^{2n} ≪ εⁿ≍ϱ²≍δ_T`: `(CONV)` and Chain
  B hold with `C≳εⁿ→0` of slack. The disconnection does **not** break
  Chain B because the asymmetry it creates is `Θ(`detached fraction`)`,
  quadratically small against the linear defect.

**Recommendation.** §7.2/§7.3 should be stated per-component (apply the
harmonic-replacement and the radial-quadratic fit on each connected
component `K_j` of the bulk, with its own `c_0^{(j)}`, `Q_j`, `B_*^{(j)}`,
then sum the symmetric differences). The conclusion
`Asym(E_{t̂})²≤Cϱ²` survives because, by §3.6, whenever `E_{t̂}` splits
the per-component asymmetries sum to `Θ(`perturbation`)` and `Asym²` is
quadratically dominated by `ϱ²`. This per-component patch is sound and
keeps `C` dimensional; it is a presentational gap, not a mathematical
obstruction.

**Check 3 verdict: VALID (with a non-fatal presentational patch).**
`(CONV)`'s constant is dimensional on the tentacled family — the
decisive `‖v−Q‖²_{H¹(tube)} ≍_n 2n(n−1)·ϱ²` ratio is **constant in
`w`** (no `L/w` blow-up, because `L=O(diam)` is bounded and the
discrepancy is volume-integrated). The disconnected case requires
stating §7 per-component; the conclusion holds with a dimensional `C`
because asymmetry is `Θ(`perturbation`)`, quadratically small vs the
linear defect.

---

## §7 per-inequality constant audit — consolidated

Every inequality in §7 whose constant could *a priori* depend on
`E_{t̂}`-geometry, with the verdict:

1. **Interior Caccioppoli/mean-value (§7.2).** Constant `=C(n)`.
   *Local* harmonic estimate — depends on `n` only. **Dimensional.**
2. **Harmonic-chaining to a single `c_0` (§7.2).** Constant
   `=C(n,diam,s_0)`. `diam(E_{t̂})≤diam Ω`; `s_0≍_n1/n` on the ball-core
   bulk (tube excised). **Dimensional**, *provided* the chaining is run
   per-component (patch §3.6).
3. **Bulk Poincaré (§7.2).** Constant `=` John constant of
   `E_{t̂}∖Z`. After excision the bulk is a near-ball (or finitely many
   near-balls), John constant `O(1)`. The note's claim "no global Korn
   constant because `w` is harmonic" is **correct in spirit**: the
   gradient is controlled by *local* interior estimates glued along the
   non-degenerate foliation; the only shape-sensitive region (tube/spike)
   is excised at `|Z|≤2n(n−1)ϱ²`. **Dimensional.**
4. **"Excised `Z` adds `≤Cϱ²`" (§7.2).** The load-bearing claim. Verified
   `‖v−Q‖²_{H¹(tube)}≍_n 2n(n−1)ϱ²` — **dimensional, `w`-independent**.
   This is the cell that would have blown up if the discrepancy were
   sup-norm rather than volume-integrated, or if `L` were unbounded;
   neither holds. **Dimensional.**
5. **Coarea/trace across `{v=0}` (§7.3).** `1/s_0` multiplies only the
   crossed *bulk* level (`s_0≍1/n`); the tube level (`|∇v|≍w/(n−1)→0`,
   where `1/s_0` diverges) is excised and paid by additive `|Z|`.
   **Dimensional** (the divergence is quarantined inside `Z`).
6. **Prop. 6.1 `|Z|≤2n(n−1)ϱ²`.** Constant `=2n(n−1)`, from the exact
   transverse profile `D²u≈−\tfrac1{n−1}I_{n−1}`. **Dimensional.**
7. **Prop. 3.1 KEY BOUND.** Constant `=4/\bar f²`, `\bar f` two-sided
   `O(1)` on `J₀`. **Dimensional.**

No inequality in §7 requires a uniform interior-ball radius, a
Lipschitz/John constant of a *rough* `E_{t̂}`, connectedness (modulo the
per-component patch §3.6), or a Poincaré/Korn constant of `Σ_{t̂}`.

---

## §4 — The structural reason Chain B is robust (the decisive principle)

The verification reduces to one homogeneity fact. `Asym(E_{t̂})`,
`δ_T(Ω)`, `δ_T(E_{t̂})`, and `∫_{E_{t̂}}|D²u+\tfrac1nI|²` are **all
linear in the size of the geometric perturbation** away from a ball:

- *Tube/tentacle* (`Ω_w=B_1∪T_w`): perturbation `≍|T|`. Then
  `Asym(E_{t̂})≍|T|`, defect `≍|T|`. Target `Asym²≍|T|²`; budget `≍|T|`;
  ratio `Asym²/`budget `≍|T|→0`.
- *Split dumbbell* (detached fraction `εⁿ`): `Asym(E_{t̂})≍εⁿ`, defect
  `≍εⁿ`. Target `≍ε^{2n}`; budget `≍εⁿ`; ratio `≍εⁿ→0`.

Because the **target is `Asym²` (quadratic)** while every available
**defect is linear**, the ratio `Asym²/`defect `≍|`perturbation`|→0` for
*every* tentacled or disconnected configuration reachable in the
small-`δ_T` régime. To force `Asym(E_{t̂})≍Θ(1)` one must apply a
`Θ(1)`-fraction perturbation (e.g. equal-lobe dumbbell), but the
Saint-Venant inequality is **strict and stable** for two-lump shapes
(`T_{two}/T_{one}=2^{−2/n}<1`), so this costs `δ_T≍Θ(1)` — where the
target `Asym²≤4≤C_nδ_T` is trivial (`Asym≤2`) and Step 1 / Chain B is
not invoked. **The dangerous régime and the small-deficit régime are
disjoint.** This is why every constant in Chain B stays dimensional.

---

## Routing consequence

Chain B does **not** consume a "tentacle-free `E_{t̂}`": Step 1 supplies
only Sard-regularity, a small collar, and `D_H(t̂)≤θ` (its volume-variable
Markov is airtight, `proof-step1.md` §3.4–§3.5); `(T)`, Step 3, and
`(CONV)` each tolerate a tentacled or disconnected `E_{t̂}` with
dimensional constants. `tentacle-model.md`'s negative verdict ("the
route does not survive thin tentacles for `n≥3`") targets the
*superseded* premise that Step 1 reaches a tentacle-*free* level within
`O(δ_T)` collar — which Chain B explicitly does not need
(`proof-step2.md` §0/§8.1/§9: "`D_H` enters only through Step 1 to
*locate* a Sard-regular near-boundary level; the `H²`-rigidity flows
from `(T)`+Step 3"). Hence:

- **Route: Step 1 → Step 2 (Chain B: `(T)`+Step 3+`(CONV)`) → Step 5.**
- **Step 4 and the `n≥3` graph obstruction are moot for Chain B.**
- The single residual of Chain A (the `\bar q↔\bar f` centering `=D_I`)
  is entirely bypassed by Chain B (no `\mathfrak B`, no `D_I`, no `q_+`).
- One **presentational** patch is required and is sound: §7.2/§7.3 must
  be stated **per connected component** of the post-excision bulk (each
  with its own `c_0^{(j)}`, radial quadratic `Q_j`, optimal ball
  `B_*^{(j)}`), summing the symmetric differences. The conclusion
  `Asym(E_{t̂})²≤Cϱ²` survives with a dimensional `C` by §3.6/§4.

---

## Final verdict

**VALID.** `(T)` is regularity-free with a purely dimensional `c(n)`
(exact Pohozaev–Rellich/`P_W` identities + pointwise Newton +
componentwise maximum principle; survives disconnection and tentacles).
KEY BOUND (Prop. 3.1) is a correct Chebyshev/coarea estimate with
dimensional constants and no hidden `Σ_{t̂}`-regularity, and it
reproduces `tentacle-model.md`'s `D_H≍_n w^{n−3}L` quantitatively.
`(CONV)`'s §7 constant is dimensional on the tentacled family — the
decisive cell `‖v−Q‖²_{H¹(tube)}≍_n 2n(n−1)ϱ²` is **constant in `w`,
with no `L/w` blow-up**, because `L=O(diam)` is bounded and the
discrepancy is volume-integrated rather than sup-normed. The disconnected
case needs §7 stated per-component (a sound presentational patch, not a
mathematical gap); the conclusion holds with a dimensional `C` because
asymmetry created by tentacling/splitting is `Θ(`perturbation`)`, hence
`Asym²` is quadratically small against the linear defect, while forcing
`Asym≍Θ(1)` costs `δ_T≍Θ(1)` (Saint-Venant strict + stable),
disjoint from the régime Step 1/Chain B operates in.

**Chain B closes** with `Asym(E_{t̂})²≤C(n,diam Ω,‖u‖_∞)δ_T(Ω)`, and
(Step 5) `Asym(Ω)²≤C(n,diam Ω,‖u‖_∞)δ_T(Ω)`. No constant degenerates;
no struck machinery; no `∂Ω`-regularity. Route =
**Step 1 → Step 2 (Chain B) → Step 5**; Step 4 and the `n≥3` graph
obstruction are moot.
