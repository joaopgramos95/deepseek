# Handoff index — sharp quantitative Saint–Venant / Faber–Krahn stability

Organised by **attempt/method**, with honest status and the precise
open point of each, so a fresh solver can engage. The underlying
theorem (`Asym(Ω)² ≤ C(n)·δ_T(Ω)`, sharp exponent) is **true** —
Brasco–De Philippis–Velichkov (BDV) proved it for all `n` via a
selection principle. This program seeks a **selection-principle-free
and/or regularity-free** proof, and has mapped exactly where each
method succeeds and fails.

Conventions: `−Δu=1` in `Ω`, `u=0` on `∂Ω`, `u>0` inside;
`δ_T` = scale-invariant Saint–Venant deficit; `Asym` = Fraenkel
asymmetry; `E_t=\{u>t\}`; `D_H` = Cauchy–Schwarz/Serrin boundary-gradient
defect (`= 1/|∇u|`-weighted variance of `|∇u|`); `D_I` = isoperimetric
defect; `δ_T ≍ ∫(D_H+D_I)w\,dt`.

Status tags: **PROVED** (in-program, dimensional) · **CLOSED-cond**
(closes modulo a named, non-circular import) · **OPEN** · **OBSTRUCTED**
(explicit counterexample / provable wall) · **SUPERSEDED**.

---

## The one-paragraph map

Every *regularity-free* "make the boundary a graph" method (Plan 3
Strategy A and all its variants; Plan 2 GGRT profile) reduces to the
**same single wall**, pinned from three independent directions: the
deficit controls only `H^{1/2}` of the boundary / the pointwise gradient
floor `inf_Σ|∇u|` is available only in weak-`L¹` / the per-level FMP
ball centres drift (the Plan-2 moving-centre `(F)` obstruction).

Two methods escape it, by opposite moves. **Plan 1 (Method 1)** does
*not* try to be regularity-free: it *imports* the BDV Alt–Caffarelli
regularity package and a single-set penalised selection. Its former
showstopper (BDV's compactness, Lemma 4.13, "moved not removed") is now
**dissolved** — 4.13 is source-verified to be BDV's lone `j→∞` step and
is replaced by the quantitative `α→d_H` modulus `lem:alphaH` (written
out), with `prop:flatness`'s nondegeneracy constant exhibited; status
**CLOSED-cond** modulo classical cited imports (BDV 4.2; per-set
density; BDV 4.18 higher clause / uniform Schauder `M_m`). **Route B
(interior Weinberger)** instead never forms a graph: trace-free Hessian,
excise (not transport) the bad set; Half 1 **PROVED**, **closes for
`n≥4`** modulo one external geometric import; **`n=2,3` open**. Plan 1
is the more advanced route to a (regularity-consuming) proof; Route B is
the candidate for a regularity-free one.

---

## Method 1 — Plan 1: quantify the BDV selection principle
Dir: `Plan 1/` · Start: `Plan 1/WHAT_PLAN1_DOES.md`, then
`Plan 1/AUDIT_PLAN1_STRUCTURAL.md`.

Replace BDV's sequential-selection-plus-compactness *contradiction* by a
single-set penalised selection, then run BDV graph entry + nearly-spherical
second variation + Kohler–Jobin, with tracked constants.

- **Status: CLOSED-cond (modulo two classical, source-verified imports).**
  The single-set selection (deficit/asymmetry preservation) is **sound and
  sequence-free** (BDV Lemma 4.7(i),(iii), a one-line minimality comparison;
  `C_sel` is a real estimate). The former **showstopper F2** ("BDV's
  compactness, Lemma 4.13, was moved not removed") is now **dissolved**:
  verified against the BDV source that 4.13 (Kuratowski `∂Ω_j→∂B_1`) is
  BDV's *only* `j→∞` ingredient and is used solely to put a free-boundary
  point near every `x̄∈∂B_1`; the deterministic chain replaces *exactly*
  that with the quantitative `α→d_H` modulus. `lem:alphaH` is now **written
  out** (`route-A-summary.tex`: two-inclusion proof, explicit exponent
  `α^{1/2N}`, fixed `(N,R)` threshold, no limit), and `prop:flatness` now
  **exhibits** the per-set nondegeneracy/density constant `c_d(N,R)` with
  the positive phase made deterministic via the inner annular sandwich
  (the "non-vacuous normalization … BDV nondegeneracy" punt is removed).
  F4 (normalization) and F3's core circularity (collar-localized bracket,
  graph-independent `C^k`) were already patched by codex.
  **Honest residual (why CLOSED-*cond*, not PROVED):** the written proof
  rests on two genuinely classical *cited* imports — (a) BDV Lemma 4.2,
  asymmetry ⇒ `|Ω∆B_1|≤C_α α^{1/2}` (standard quantitative-isoperimetry
  type, dimension-only constant); (b) the per-set density constants
  `c_d,r_d`, now **source-verified non-sequential** (BDV proofs of
  Lemmas 4.9–4.12 open *"being j fixed we drop the subscript"*, constants
  `(N,R)`, derived from the single-set first variation 4.2/(4.19)). These
  are imports to *cite*, not walls to break; F2 is no longer a structural
  obstruction. Still genuinely asserted-not-reproved downstream: the
  uniform Schauder constant `M_m(N,R)` (F3 endpoint — codex's collar
  argument supplies the `q_U` side; BDV 4.18's higher-regularity clause is
  classical per-set).
- Key files: `route-A-summary.{tex,pdf}` (the worked route; see
  §"Notation" per-set remark, `lem:alphaH`, `prop:flatness`),
  `audit-patch-normalization-schauder.md` (codex's F3/F4 patch),
  `AUDIT_PLAN1_STRUCTURAL.md` (the original F1–F6 audit),
  `plan1.md`, `quantitative-selection-principle.md`,
  `corrections-needed.md`, `1306.0392v1.pdf` (BDV).

## Method 2 — Plan 2: level-set identity / foliation / GGRT profile
Dir: `Plan 2/` · Start: `Plan 2/level-set-deficit-identity.md`,
`Plan 2/global-foliation-trace.md`, `Plan 2/nicola-tilli-stability-import.md`,
`Plan 2/ggrt-transport-pushback.md`.

- The **exact level-set deficit identity** `δ_T≍∫(D_H+D_I)w\,dt` is
  clean and PROVED-level (Plan 2's solid core).
- The **foliation/action-bound `(F)`** `∫_{ρ_*}^1(ρ^{n+1}‖∂_ρh‖²+ρ^{n-1}Q(h))dρ
  ≤ C_nδ_T` — **OPEN**; this is Plan 2's central conjecture (`(F) ⇒`
  sharp stability in a few lines, but `(F)` itself is unproved; its
  remainder estimates are the open obligation).
- **GGRT/STFT profile import** (`ggrt-transport-pushback.md`): genuinely
  orthogonal in formulation, dictionary built (`δ_T` = profile-area
  between `v(s)=u^*` and ball profile `b(s)`), **but REDUCES TO `(F)`**:
  per-level FMP gives a moving centre `x_s`; assembling needs exactly
  `(F)`. GGRT escape only via a fixed global holomorphic cancellation
  (`Re G(0)=0`, Bargmann–Fock) that has **no torsion analogue** — the
  precise reason recorded in `ggrt-transport-pushback.md`.

## Method 3 — Plan 3 / route specifications (authoritative)
Dir: `Plan 3/00-route-specs/`.

- `PLAN3_INTENDED_ROUTE.md` — the corrected single-level route (v3),
  authoritative; its Status section records what the investigation
  established.
- `STRATEGY_A_PLAN.md` — the user's laid-out graph-route plan.
- `MY_UNDERSTANDING.md` — **the user's own red-pen** of the route
  (ALL-CAPS comments are the user's corrections; treat as ground truth
  for intent).

## Method 4 — Plan 3 / Strategy A: single-level graph route
Dir: `Plan 3/A-strategyA-graph/`.

Extract a near-Serrin level, show it is a small-norm graph, close
perturbatively (Fuglede/BDV), transfer back.

- **Status: OBSTRUCTED regularity-free, at one precisely-pinned node.**
  Every variant collapses to: the pointwise gradient floor `inf_Σ|∇u|`
  is delivered by the integral defects only in **weak-`L¹`**
  (`1/|∇u|∈L^{1,∞}`), the exact De Giorgi–Nash–Moser endpoint where the
  bootstrap gives no `C^{0,α}` gain; the forbidden `dist(Σ,∂Ω)^{-β}`
  re-enters there. Explicit analytic `n=2` counterexample.
- Files (each a variant, all OBSTRUCTED/RELOCATE):
  `expA-step1-regularizer.md` (selection-as-regulariser: smoother *given*
  `α≤α_graph`, not generator), `expA-anygraph-monotonicity.md`
  (monotonicity relocates smallness; independently re-derives Route B),
  `expA-bootstrap.md` (`H^{1/2}→C^{2,γ_0}` interpolation is clean &
  non-circular, but inherits Step-B's gap), `expA-selfquantify-propagate.md`
  (Poisson smoothing fails: elliptic, no smoothing at the `δ_T`-shell),
  `dh-hodograph-bootstrap.md` (Schauder upper range OK equation-intrinsic;
  De Giorgi entry obstructed — the cleanest statement of the wall),
  `n2-graph-route-OBSTRUCTED.md` (explicit 2D counterexample; the "Fuglede
  closes" claim is unsound — do not trust it).

## Method 5 — Plan 3 / Route B: single-level interior Weinberger
Dir: `Plan 3/B-routeB-weinberger/` · Start: `two-strategies.pdf` (the
main exposition), then `route-B-clarified.pdf`.

Never forms a graph. `P=|∇u|²+\tfrac2nu`, `ΔP=2|D²u+\tfrac1nI|²`;
the trace-free Hessian rigidity, made quantitative.

- **Half 1 — PROVED, dimensional, regularity-free** (`routeB-half1.md`):
  `δ_T(D) ≥ c(n)|D|^{-(n+2)/n}∫_D v|D²v+\tfrac1nI|²` (the **`v`-weighted**
  Hessian defect `R_v`; the clean unweighted form is *not* what the
  identity gives — this is a real correction).
- **Half 2 — CLOSED-cond for `n≥4`; OPEN for `n=2,3`.** `R_v` small ⇒
  `Asym²≲R_v` via Korn rigidity on the bulk `D∖Z` (`Z=\{|∇v|≤s_0\}`
  excised). For `n≥4` the tentacle passes (`Asym²/R_v≍w^{n-3}L→0`); for
  `n=2` it **fails** (`→∞`), `n=3` borderline (the seam). The `n≥4`
  closure rests on one external import (below). Constant dimensional but
  `≍n^{-n}` (acceptable for the stability theorem).
- Files: `routeB-half1.md`, `routeB-half2-adversarial.md` (the dumbbell
  break attempt — its `δ_T=Θ(ρ^{n-2})` is an ERROR; correct value
  `1-2^{-2/n}=Θ(1)`), `dk-nge4.md` (DK holds `n≥4`), `dk-thirdclass.md`
  (final break attempt: no third class; exhaustive dichotomy),
  `verify-chainB.md`, `tentacle-model.md`, `ROUTE_B_CLARIFIED.md`,
  `route-B-clarified.{tex,pdf}`, `two-strategies.{tex,pdf}`.

### The single `n≥4` import (the referee-target)
Route B `n≥4` reduces to **one** external, deficit-independent,
non-circular geometric fact — a quantitative John/uniform-domain
structural dichotomy:

> If a bounded `D⊂ℝⁿ` fails the `c`-John condition with constant `J`,
> then `D` contains **either** (i) a *channel* of length-to-width aspect
> `≳ J`, **or** (ii) a *separating bottleneck* — a cross-section of
> relative diameter `≲ 1/J` splitting `D` into two `Θ(1)`-volume pieces.

Attributed to **Martio–Sarvas** (Ann. Acad. Sci. Fenn., 1979) and
**Väisälä**, *Uniform domains* (Tôhoku Math. J. 40, 1988). Used in
exactly one place (convert "bulk not John" into channel ∨ bottleneck;
then Half 1 kills channels, strict stability kills bottlenecks).
**Honest status:** standard *in spirit* (uniform/`(ε,δ)`/John theory),
but the exact *exhaustive quantitative dimensional* form is **not a
verbatim cited theorem** — this is the load-bearing thing a referee must
establish for the `n≥4` proof.

## Method 6 — Plan 3 / assembled proof steps (earlier max-effort)
Dir: `Plan 3/C-assembled-proof-steps/`.

`proof-step1..5.md`: the earlier end-to-end attempt. **Steps 1
(Chebyshev extraction), 3 (exact deficit transfer via `v=u-\hat t`),
5 (superlevel asymmetry transfer) are rigorous and reusable as lemmas.**
Step 2 (graph entry) and Step 4 (perturbative) are SUPERSEDED by the
Strategy-A-OBSTRUCTED / Route-B understanding. Use Steps 1/3/5 as solid
building blocks for any route.

## Building blocks (BDV-derived, taken as imports)
`Final/` : `BoundedReduction`, `NearlySphericalClosure`,
`KohlerJobinTransfer`, `SchauderInterpolation`, `SelectionPrinciple`,
`SaintVenantAssembly` — classical/BDV components, cited not reproved.
`Manuscript/` : assembly digests (`ROUTE_STATUS_DIGEST`, COMPANION_*).

---

## Frontier for the next solver (where to actually push)

1. **Complete Route B for `n≥4`**: verify or directly prove the single
   import — *failure of the John condition with constant `J` ⇒ a `≳J`-aspect
   channel or a `≲1/J`-relative separating bottleneck*, with
   dimension-tracked constants. Everything else `n≥4` is in-program-proved
   (Half 1) or classical (Saint–Venant superadditivity, FMP). This is the
   single cleanest, most isolated open lemma; it is purely geometric and
   non-circular.
2. **`n=2,3` are genuinely open.** The graph route is OBSTRUCTED
   regularity-free (Method 4; explicit `n=2` counterexample); Route B's
   `v`-weighted Half 2 provably fails the tentacle test for `n=2` and is
   borderline at the `n=3` seam. A genuinely new idea is needed for low
   dimension — do not re-run the graph route (the wall is dimension-
   independent and pinned).
3. **Plan 1 (Method 1) is now the most advanced route: CLOSED-cond.** Its
   former showstopper F2 is dissolved (`lem:alphaH` written out;
   `prop:flatness` nondegeneracy constant exhibited; 4.13 source-verified
   to be BDV's lone sequential step and replaced, not relocated). What
   remains are *citations*, not walls: BDV Lemma 4.2 (classical
   asymmetry⇒`L¹`), the per-set density constants (source-verified
   non-sequential), and BDV Thm 4.18's higher-regularity clause feeding
   the uniform Schauder `M_m(N,R)` (classical per-set Schauder; F3's
   circularity itself is broken by codex's collar-localized bracket).
   Plan 1 is *not* regularity-free — it consumes the BDV package — but it
   is a coherent conditional proof of the sharp inequality and the next
   verification target is finishing/citing those classical imports
   precisely, not breaking a wall. Plan 2's action bound `(F)` remains the
   *regularity-free* recurring wall (moving centre); the graph-route wall
   (Method 4) is the regularity-free obstruction Plan 1 sidesteps by
   *using* regularity.

**Do not** relay any single agent's "it closes" without the skeptical
check: the recurring failure mode in this project was agents concluding
closure via an internally-coherent route that an adversarial pass then
broke. Every "closed" claim here has been stress-tested; the honest
residuals are stated above and must be carried forward, not dropped.
