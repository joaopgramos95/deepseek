# Lemma 2.1 (quantitative): annulus + bounded C^{1,γ} ⇒ radial graph

**Purpose.** Provide a rigorous, quantitative replacement for Lemma 2.1 of `BRANDOLINI_GRAPH_ENTRY_ROUTE.md`. The original statement is false (audit §S1): a `C^{1,γ}` connected closed hypersurface in a thin annulus can fold an odd (≥3) number of times across radial rays. The repair imposes a `C^{1,γ}`-norm bound `M` and a smallness threshold `ε ≤ ε₀(M,γ,n,r₀)`. After the lemma, we verify that the `M` emerging from interior Schauder on the rescaled torsion superlevel set is `M(n,R,ρ_*,γ)`, independent of the deficit `δ`, so for `δ` small Brandolini's `Cδ^μ` falls below `ε₀`.

**Sign convention.** `u` is the Plan 2 torsion function `−Δu=1` on `Ω`, `u=0` on `∂Ω`. Brandolini uses `Δũ=n`, reconciled in §3.1.

## 1. Norm conventions

### 1.1 Local-chart C^{1,γ} norm

For a closed `C^{1,γ}` hypersurface `S ⊂ ℝⁿ` and `p ∈ S`, fix the unit normal `ν(p)` (outward to `E` if `S=∂E`). In the affine frame `(T_p S, ℝν(p))` there exist `r_p>0` and `f_p : B^{n−1}_{r_p}(0)→ℝ` of class `C^{1,γ}` with `f_p(0)=0`, `∇f_p(0)=0`, and
\[ S ∩ (B^{n−1}_{r_p}(0)×(−r_p,r_p)_{ν(p)}) = \{p+ξ+f_p(ξ)ν(p) : ξ∈B^{n−1}_{r_p}(0)\}. \]
Define
\[ ‖S‖_{C^{1,γ},r_0} := \sup_{p∈S}(\sup_{B^{n−1}_{r_0}}|∇f_p| + [∇f_p]_{C^{0,γ}(B^{n−1}_{r_0})}). \]
We require `r_p ≥ r_0` for all `p ∈ S`.

### 1.2 Consequences of ‖S‖_{C^{1,γ},r₀} ≤ M

**(N1) Hölder normals.** `|p−q|≤r₀/4 ⇒ |ν(p)−ν(q)| ≤ C₁(M,n)|p−q|^γ`, `C₁ := M(1+M²)^{1/2}`.

**(N2) Quadratic slab.** `|ξ| ≤ r₀ ⇒ |f_p(ξ)| ≤ M|ξ|^{1+γ}/(1+γ)`.

**(N3) Arc-length tangent control.** Unit-speed `C^{1,γ}` arc `σ:[0,L]→S`, `L≤r₀`: `|σ̇(t)−σ̇(0)| ≤ C₂(M,n)t^γ`, `C₂=C(n)M`.

### 1.3 Annulus hypothesis

`S ⊂ A_{R_in,R_out}(x_*)`, `R_in,R_out ∈ [1/2,3/2]`, `S=∂E`, `B_{R_in}(x_*) ⊂ E ⊂ B_{R_out}(x_*)`, WLOG `x_*=0`.

## 2. Statement of Lemma 2.1′

**Lemma 2.1′ (quantitative annulus-to-graph).** Fix `n≥2, γ∈(0,1], M≥1, r₀∈(0,1/4]`. Define
\[ \boxed{ε_0(M,γ,n,r_0) := \frac{1}{64(M+4)^2}.} \]
A sharper threshold `ε₀ ∼ M^{−(1+γ)/γ}` is attainable by full Hölder-exponent optimization in the slab estimate; the form above suffices for the route.

Let `S ⊂ ℝⁿ` be closed, connected, `C^{1,γ}`, with `‖S‖_{C^{1,γ},r₀} ≤ M`, satisfying §1.3 with `ε ≤ ε₀`. Then there is a unique `h ∈ C^{1,γ}(∂B₁)` with
\[ S = \{(1+h(θ))θ : θ∈∂B_1\}, \quad ‖h‖_{L^∞} ≤ \max(|1−R_in|,|R_out−1|), \]
\[ ‖h‖_{C^{1,γ}(∂B_1)} ≤ C_4(n,γ)(1+M). \]

## 3. Proof

The proof rests on the quantitative claim: at every `p∈S`, `ν(p)` is close to `p̂`. Once shown, the radial-graph property and regularity follow from the implicit function theorem.

### 3.1 Radial-tangent geodesic estimate

**Lemma 3.2 (slab).** Let `p₀ ∈ S` with `p̂₀ · ν(p₀)=0`, `r:=|p₀|∈[1/2,3/2]`. Let `σ:[−T,T]→S` be unit-speed `C^{1,γ}`, `σ(0)=p₀`, `σ̇(0) ⊥ p̂₀`, `T≤r₀/2`. Then
\[ ||σ(t)|−r| ≤ \frac{4+C_2}{1+γ}|t|^{1+γ}, \quad t∈[−T,T]. \]
*Proof.* `β(t):=d|σ(t)|/dt = σ̇(t)·σ̂(t)`, `β(0)=0`. Decompose `σ̇=βσ̂+w`, `w⊥σ̂`, `|w|²=1−β²`, so `σ̂̇=w/|σ|`. By (N3), `σ̇(t)=σ̇(0)+r_σ(t)` with `|r_σ(t)|≤C₂|t|^γ`. Then `β(t)=σ̇(0)·(σ̂(t)−σ̂(0))+r_σ(t)·σ̂(t)`. The first term is `≤|σ̇(0)|·4t·(|σ|≥1/4)=4t` (using `|σ̂(t)−σ̂(0)|≤|σ(t)−σ(0)|/|σ_min|≤t/(1/4)=4t`); the second is `≤C₂|t|^γ`. So `|β(t)|≤(4+C₂)|t|^γ`. Integrate. ∎

### 3.2 Nearly-radial normals

**Lemma 3.3 (nearly-radial normals).** Under Lemma 2.1′ hypotheses, every `p∈S`:
\[ |\sin α(p)| := \sqrt{1−(ν(p)·p̂)²} ≤ 4C_3(M,n)\sqrt{ε}, \quad C_3 := M+4. \]
*Proof.* Fix `p₀∈S`, `α₀:=α(p₀)`, `δ₀:=|\sinα₀|`. If `δ₀=0`, done. Else let `e := Π_{T_{p₀}S}(p̂₀)/δ₀` (unit in `T_{p₀}S`); set `ξ(t):=te`, `q(t):=p₀+ξ(t)+f_{p₀}(ξ(t))ν(p₀)`. By (N2), `|f_{p₀}(te)|≤M|t|^{1+γ}/(1+γ)`. Compute:
\[ |q(t)|² = |p_0|² + 2p_0·ξ(t) + 2f_{p_0}(te)\,p_0·ν(p_0) + t² + f_{p_0}(te)². \]
`p₀·ξ(t)=|p₀|tδ₀`; `p₀·ν(p₀)=s_0|p_0|\cos α_0` with `s_0∈\{±1\}`. For `|t|≤t_*:=δ₀/(4M)`:
\[ |q(t)|²−|p_0|² = 2t|p_0|δ_0 + R(t), \quad |R(t)| ≤ t|p_0|δ_0 + 2t². \]
Hence `|q(t)|²−|q(−t)|² ≥ t|p_0|δ_0`. With `|q(±t)|∈[R_in,R_out]`, `|q(t)|²−|q(−t)|²≤(R_out+R_in)ε≤3ε`. Take `t=t_1:=δ_0/(4(M+1))∈[t_*,δ_0/(4M)]∩[0,|p_0|δ_0/4]`:
\[ t_1|p_0|δ_0 ≤ 3ε ⟹ δ_0²/(4(M+1)) ≤ 6ε ⟹ δ_0 ≤ 5\sqrt{(M+1)ε} ≤ 4C_3\sqrt{ε}. \] ∎

### 3.3 No radial-tangent points; ray-crossing = 1

With `ε ≤ ε₀ = 1/(64C₃²)`, `|\sinα(p)|≤1/2`, so `|ν(p)·p̂|≥√3/2≥4/5`. By connectedness of `S`, the sign of `p̂·ν(p)` is constant on `S`; by `B_{R_in}⊂E` with outward normal, the sign is `+1`:
\[ p̂·ν(p) ≥ 4/5, \quad ∀p∈S. \]
Each ray `ℝ_+θ` meets `S` in a finite set (transversal), every crossing has `p̂·ν=θ·ν>0`. The signed intersection number with `∂E` is `1` (ray enters then exits `E`); the algebraic count equals the unsigned count since all signs are `+1`. So each ray crosses `S` exactly once. Hence `r(θ)` is well-defined.

### 3.4 C^{1,γ} regularity of h

`F(r,ξ;θ):=r·θ−p_0−ξ−f_{p_0}(ξ)ν(p_0)=0` defines `(r,ξ)` near `(r(θ_0),0)`. Jacobian determinant `±r(θ_0)^{n−1}·(p̂_0·ν(p_0))≥(4/5)·(1/2)^{n−1}>0`. IFT in `C^{1,γ}` gives `r∈C^{1,γ}(∂B_1)`, `‖r‖_{C^{1,γ}}≤C_4(n,γ)(1+‖f_{p_0}‖_{C^{1,γ}})≤C_4(n,γ)(1+M)`. Set `h(θ):=r(θ)−1`. ∎

## 4. Sharpness

In `n=2`, fold profile `r(θ)=1−h·η(θ/Φ)` with `η:[−1,1]→[0,1]` a `C^{1,γ}` bump. Slope `|r'|∼h/Φ`, `[r']_{C^{0,γ}}∼h/Φ^{1+γ}=M`. So `h=MΦ^{1+γ}`. Geometric permissibility: `h≤ε`. Hence the fold has angular extent `Φ=(h/M)^{1/(1+γ)}≤(ε/M)^{1/(1+γ)}`. For `ε∼M^{−(1+γ)/γ}`, the fold reaches `C^{1,γ}`-saturation. For `ε<ε₀∼M^{−(1+γ)/γ}`, no compatible fold exists; rigorous version is Lemma 3.3.

## 5. Verification: Brandolini's Cδ^μ ≤ ε₀ for δ small

### 5.1 Sign convention

Plan 2: `−Δu=1`. Brandolini: `Δũ=n`. Set `ũ:=−nu`: `Δũ=n`, `ũ|_{∂Ω}=0`, `|Dũ|=n|Du|`. Rescale `u→nu` to align gradient normalization with Brandolini's `||Dũ|−1|≤δ`.

### 5.2 Rescaling

`λ:=(|E_{t̂}|/ω_n)^{1/n}`, `Ê:=λ^{−1}E_{t̂}`, `û(x):=λ^{−2}(u(λx)−t̂)`. `−Δû=1` on `Ê`, `|û|≤C(n,R)`. In fixed-collar regime `λ∈[c_*,C_*]`, depending on `(n,R,ρ_*)`.

### 5.3 Interior Schauder

GT Thm 6.2: `‖û‖_{C^{3,α}(K)} ≤ C_S(n,α,d_0)‖û‖_{L^∞}` on `K` with `dist(K,∂Ω̂)≥d_0>0`. In fixed collar `t̂∈[ρ_*,1]`, `dist(Σ_{t̂},∂Ω̂)≥c(n,R,ρ_*)>0`, so `‖û‖_{C^{3,α}(N(Σ_{t̂}))} ≤ C_S(n,α,R,ρ_*)`.

### 5.4 IFT at regular level

Sard + Agent 1 ⇒ regular `t̂`. `mean_{∂Ê}|∇û| = ω_n/P(Ê) = 1+O(√D_I)`. `C^α`-interpolation (G2-corrected, `κ=α/(2α+n−1)`): `|∇û|(p)≥1−C(√D_I+D_H^κ)≥1/2`. IFT: `Σ_{t̂}` is `C^{3,α}` graph, chart radius `r_0(n,R,ρ_*)>0`, norm `C_{IFT}(n,α,R,ρ_*)`.

### 5.5 C^{1,γ} bound M

Take `α=γ` in 5.3-5.4: `M:=‖Σ_{t̂}‖_{C^{1,γ},r_0} ≤ M(n,R,ρ_*,γ)`. Rescaling adjusts by `λ^γ∈[c_*^γ,C_*^γ]`, absorbed.

### 5.6 Brandolini Theorem 2 with concentric balls

Brandolini ⇒ `B_{R_in}(x_*)⊂Ê⊂B_{R_out}(x_*)`, `R_out−R_in≤C_B(n,R,ρ_*)δ^μ`, `|1−R_*|≤C_Bδ^μ`, `μ=1/(2(4n+9)(n−1))`. **Concentric:** the center `x_*` is the inscribed-ball center from Corollary 9; the proof of Theorem 2 (brandolini.pdf p.1581: "smallest ball containing Ω and concentric with `B_R`") takes the circumscribed ball concentric with the inscribed, so both balls share `x_*`. `δ` here = `C(n,R)(D_H+D_I)^κ`.

### 5.7 Application of Lemma 2.1′

`‖∂Ê‖_{C^{1,γ},r_0}≤M(n,R,ρ_*,γ)`; `r_0>0` indep. of `δ`. `ε₀=1/(64(M+4)²)>0` indep. of `δ`. Apply Lemma 2.1′ provided
\[ C_Bδ^μ ≤ ε_0 ⟺ δ ≤ δ_0(n,R,ρ_*,γ) := (ε_0/C_B)^{1/μ}. \]
Equivalently `(D_H+D_I)(t̂) ≤ η_0(n,R,ρ_*,γ) := (δ_0/C)^{1/κ}`. For `(D_H+D_I)(t̂)≤η_0`,
\[ ∂Ê = \{x_*+(1+h(θ))θ\}, \quad ‖h‖_{L^∞}≤2C_Bδ^μ, \quad ‖h‖_{C^{1,γ}}≤C_4(n,γ)(1+M)=:M'(n,R,ρ_*,γ). \]

## 6. Residual gaps not closed by this note

**(a) Connectedness of `∂Ê` (audit G1).** Lemma 2.1′ requires `S` connected. `E_{t̂}` may have multiple components if `Ω` has tentacles. One-dominant-component reduction (Brandolini Theorem 1 multi-ball + `D_I`-smallness) is not closed here.

**(b) `C^{1,γ} → small C^{2,γ_0}` for `thm:NS` (audit G6).** Lemma 2.1′ outputs `‖h‖_{C^{1,γ}}≤M'` (bounded, not small) and `‖h‖_{L^∞}≤2C_Bδ^μ` (small). Schauder interpolation between small `L^∞` and bounded `C^{3,α}` gives `‖h‖_{C^{2,γ_0}}≤CM'^{1−σ}(2C_Bδ^μ)^σ` for `σ=σ(γ_0,α)∈(0,1)`. Small for `δ` small but costs a fractional power of `δ^μ`.

**(c) Audit G2 exponent.** The `κ` used in 5.4, 5.7 is the audit-corrected `α/(2α+n−1)`, not the route's `α/(2(n−1+α))`.

**(d) First-mode neutralization (audit C7).** Translation by `O(δ^μ)` from inscribed-ball center `x_*` to barycenter to feed Agent 3's (G0). Trivial, but should be performed explicitly.
