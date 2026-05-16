# The partial-hodograph bootstrap for the D_H-near-Serrin level set

One decidable question: does the Kinderlehrer–Nirenberg partial-hodograph
equation bootstrap a weak (H^{1/2}/H^1/H^0) seed up to C^{2,γ} with
equation-intrinsic constants — no interior ‖u‖_{C^{2,α}}, no dist(Σ,∂Ω)?

## 1. The hodograph equation
Near a regular point with ∂_n u ≠ 0, solve u(x',φ(x',s))=s. The level
{u=t̂} is x_n=φ(x'). Rewriting −Δu=1:

    a_{αβ}(∇'φ) φ_{αβ} = b(∇'φ; |∇u|),
    a_{αβ}(p)=δ_{αβ}+p_α p_β   (eigenvalues in [1, 1+|p|²]),
    b ≍ (1+|∇'φ|²)^{3/2}·(1/|∇u|) − (tangential-curvature terms).

- (E) Ellipticity is UNCONDITIONAL from the graph structure; needs no
  info on |∇u|.
- (F) The only PDE source is the bare constant −Δu=1; the sole
  non-elementary input is the POINTWISE quantity ‖1/|∇u|‖_{L^∞(Σ)}.
- |∇u| enters only (i) for existence of the transform (pointwise
  inf_Σ|∇u|>0) and (ii) in the forcing (F). Both pointwise. The
  near-Serrin/small-gradient data are integral and give neither.

## 2. Sub-Q1 — Schauder upper range: HOLDS, equation-intrinsic
Granted a C^{1,α} seed (‖·‖≤M₁) and a pointwise floor |∇u|≥c>0:
frozen-coefficient Schauder (Gilbarg–Trudinger 6.2/6.6) bootstraps
C^{1,α}→C^{2,γ}→C^∞→analytic with constant

    ‖φ‖_{C^{2,α}} ≤ C_S(n,α)·(1+M₁²)^{N(n)}·c^{-K(n)}·(M₁+1).

Verified: |∇u| on Σ is slaved to φ and the source 1 via the level-set
curvature identity H_Σ|∇u| = −1−∂_ν|∇u|, so ‖1/|∇u|‖_{C^α(Σ)} ≤
1/c + Ψ(M₁)/c² — NO ‖u‖_{C^{2,α}(Ω)}, NO dist(Σ,∂Ω). The φ-equation
route genuinely avoids interior estimates for u. Conditional ONLY on
the pointwise floor c=inf_Σ|∇u|>0 and the C^{1,α} seed.

## 3. Sub-Q2 — De Giorgi entry: OBSTRUCTED, explicit n=2 counterexample
Seed is at best H^{1/2} (sharp Steklov, δ_T≍‖φ‖²_{H^{1/2}}); lifting to
C^{1,α} is De Giorgi–Nash–Moser, not Schauder. Forcing b ≍ 1/|∇u|; the
small-gradient lemma gives EXACTLY

    1/|∇u| ∈ L^{1,∞}(Σ)  (weak-L¹),  and nothing better.

n=2 (Σ a curve): GT 8.22 needs b∈L^q, q>1, for a C^{0,α} gain.
L^{1,∞} fails by the endpoint. The bad set is excisable for an
INTEGRAL conclusion (Strategy-B's Z, paid additively) but NOT for a
pointwise C^{1,α} graph statement.

Adversarial family Σ_{a,λ} (n=2): localized analytic bump, height
a=θ^{1/2}/√log(1/λ), width λ→0, Serrin defect ≡ θ (fixed), small-
gradient lemma SATURATED by the width-λ foot, ‖g‖_{C¹},κ_max→∞,
‖1/|∇u|‖_{L^∞}≍1/a→∞. It satisfies every hypothesis, evades the
D_H-blow-up that prices out n=2 tentacles (tuned so the defect stays
θ), and is provably NOT C^{1,α} with a λ-uniform constant. Explicit
counterexample to any regularity-free entry estimate.

## 4. Where the forbidden constant re-enters
Exactly one node: the pointwise gradient floor inf_Σ|∇u|. The integral
hypotheses give only weak-L¹; the only regularity-free lower bound on
inf_Σ|∇u| is a dist(Σ,∂Ω)^{-β} interior/Hopf estimate (GT 3.7/6.3) —
the boundary the route is built to avoid. This is Checkpoint A2 /
(R-collar), now pinned to its exact cause: the entry is a De Giorgi
statement failing at the weak-L¹ endpoint the small-gradient lemma
supplies.

## 5. Verdict
Sub-Q1 (Schauder C^{1,α}→C^∞): HOLDS, equation-intrinsic, conditional
on the pointwise floor + C^{1,α} seed. Sub-Q2 (De Giorgi entry): FAILS
regularity-free; explicit n=2 counterexample. A positive on (1) does
NOT close (2). Regularity-free weak→C^{2,γ} does NOT close via the
hodograph graph route. The interior Weinberger/Strategy-B route (which
needs only the integral excision, never a pointwise floor) is
unaffected.

References: Kinderlehrer–Nirenberg (Ann. SNS Pisa 1977);
Gilbarg–Trudinger Ch. 6, 8 (Thm 8.22/8.24/8.32, 3.7, 6.3);
Brasco–De Philippis–Velichkov (Duke 2015).
