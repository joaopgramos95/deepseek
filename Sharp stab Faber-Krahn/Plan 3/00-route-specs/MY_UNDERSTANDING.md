# What I (Claude) currently believe the Plan 3 route is

This is my plain statement of the route, written for you to red-pen.
It is NOT an authoritative spec and NOT a result claim. Where I am
unsure or suspect I introduced confusion, I say so explicitly.

## The route, as I understand it from your own words

Setup: `−Δu = 1` in `Ω`, `u = 0` on `∂Ω`. `E_t = {u > t}` are the
superlevel sets; the "zero level" is `∂Ω`. `δ_T(Ω)` = Saint–Venant
deficit. `Asym` = Fraenkel asymmetry. Goal: `Asym(Ω)² ≤ C(n) δ_T(Ω)`.

1. **One near-boundary level, found by averaging.** Use the exact
   level-set identity `δ_T(Ω) ≃ ∫ (D_H+D_I) w dt` as an *average*:
   restrict it to the collar of levels within `O(δ_T)` of the boundary
   and Chebyshev out a single level `t̂` there at which `E_{t̂}` is a
   **near-Serrin domain** (`D_H(t̂)`, `D_I(t̂)` small (COMMENT: SMALL IN ABSOLUTE TERMS, NOT IN TERMS OF \delta_T. THAT IS, THEY ARE SMALL ABSOLUTE CONSTANTS). The averaging
   is essential — it is how the near-Serrin level is produced.

2. **Near-Serrin ⇒ the level set is a graph.** By Serrin-type
   stability, `∂E_{t̂}` is (close to) a graph over a sphere. The graph
   need not be small a priori, but pushing the level deeper (the
   implicit constant in `O(δ_T)` large) together with `D_H` makes the
   graph norm `≪ 1`. (COMMENT: NOT CLOSE TO A GRAPH; THERE SHOULD BE A WAY TO SAY THAT IT IS A GRAPH: IF |\nabla u| IS CLOSE TO CONSTANT - WHICH IT IS DUE TO D_H - IN AN INTEGRATED SENSE, THEN MAYBE A REGULARITY ARGUMENT, OR PERHAPS A INTERPOLATION-OF-HARMONIC-FUNCTIONS-BOUND HARNACK-STYLE (SINCE \nabla u IS A VECTOR OF HARMONIC FUNCTIONS) SHOULD PROVIDE THE REQUIRED L^{\infty} INEQUALITY).  

3. **A graph subdomain with controlled deficit.** `Ω̃ := E_{t̂} ⊂ Ω`
   is a level set of `u`, now a small graph, with
   `δ_T(Ω̃) ≲ δ_T(Ω)`.

4. **Reduce to the perturbative case.** It then suffices to prove the
   sharp inequality for domains whose boundary is a small graph
   (nearly-spherical / perturbative), applied to `Ω̃`.

5. **Transfer back with room to spare.** The discarded collar
   `|Ω∖Ω̃|` is `O(δ_T)`, so the transfer error from `Ω̃` back to `Ω`
   squares to `≪ δ_T`. Hence `Asym(Ω)² ≲ δ_T(Ω)`.

## What is NOT in the route (my understanding)

- No Plan 2 foliation, no action bound `(F)`, no `∂_ρ`
  derivative/variation, no `t`-family / cohesion. Single level, static.

## Where I think I may have confused things (please confirm/deny)

These came from sub-agents I deployed; I am unsure which, if any, you
intend as part of the route, and I suspect some are my confusion:

- **(a) `(BReg)` / "assume `∂Ω` is `C^{2,α}`".** A sub-agent argued
  Step 2's procurement needs regularity *uniform as the level
  approaches `∂Ω`*, and I let that become an assumed hypothesis
  `(BReg)` discharged by a "weak selection principle". You then said:
  the interior level sets are real-analytic for free, so we should not
  need regularity of `Ω`. **I now think (BReg) was my confusion, not
  your route.** Please confirm. (COMMENT: SEE THE COMMENT IN STEP 2 ABOVE. IT IS EVIDENT THAT AS SOON AS WE GO A BIT INSIDE THE DOMAIN, THE LEVEL SETS OF u ARE ALMOST ALL SMOOTH, SO THE REGULARISATION STEP IS IDIOTIC: WE ARE NOT USING THE SERRIN STABILITY IN \partial \Omega ANYWAY, ONLY ON AN INNER LEVEL) 

- **(b) Brandolini vs. `D_H`-integral-Serrin for Step 2.** I am unsure
  whether your Step 2 "Serrin stability" is meant to be Brandolini's
  `L^∞` theorem (which is what dragged in regularity), or an
  integral-identity (Weinberger/Magnanini–Poggesi) stability that
  consumes `D_H` directly. Your last instruction ("consumes `D_H`")
  suggests the latter. I do not know if you regard these as the same
  step described two ways, or one right and one wrong. (COMMENT: SEE COMMENTS ABOVE. YOU MENTIONED YOURSELF IN A PREVIOUS GUIDELINE/MESSAGE THAT THERE SHOULD BE A WAY TO TAKE THE D_H INPUT AND TRANSFORM IT INTO A L^{\infty} OUTPUT. THIS IS THE SENSE). 

- **(c) `D_I`-Fuglede vs `D_H`.** Step 4 ("sharp FK for graph
  domains") I have realized two ways: a `D_I`/isoperimetric Fuglede
  argument, and a `D_H`/Serrin one. I am not sure which you intend, or
  whether both are meant to be used (the identity supplies both). (COMMENT: `D_I` IS LIKELY NOT THE RIGHT ROUTE. INSTEAD, WE ONLY USE `D_H`; THIS EXTRACTS A GOOD LEVEL SET, WHICH IS A GRAPH, AND WHOSE DEFICIT IS O(\delta_T)). 

- **(d) The "depth" mechanism in Step 2.** I am not confident I
  correctly understand *why* a deeper level (larger implicit constant)
  gives a smaller graph norm — I have stated it as "regularisation +
  `D_H`" but cannot cleanly justify the quantitative dependence, and
  may have mis-stated it. (COMMENT: JUST USE CHEBYSHEV: THERE IS NO DEEPER LEVEL IMPLIES SMALLER GRAPH NORM, YOU HALLUCINATED THIS. THE IDEA IS THAT IF WE USE CHEBYSHEV, THEN THE MEASURE OF THE PARAMETERS t SUCH THAT THE D_H INTEGRAND IS GREATER THAN \theta IS AT MOST A CONSTANT DEPENDING ON THETA TIMES \delta_T. THIS IS THE INTENDED MECHANISM: THERE IS A LEVEL SET FOR WHICH D_H IS SMALL WHICH LURKS AT A DISTANCE O_\theta(\delta_T) FROM THE BOUNDARY). 

## My single biggest uncertainty

Whether Step 2's "near-Serrin ⇒ graph, small norm" is supposed to be
**regularity-free** (using only interior analyticity of `u`, which is
free, plus `D_H`) — in which case (BReg) and the whole
selection-principle detour are my error — or whether you do intend some
regularity input there. Everything else in the route I am fairly
confident I have right; this is the node where I think I screwed up.

(COMMENT: SEE ABOVE). 

---

Please correct any step or strike anything that is my confusion. I will
rewrite `PLAN3_INTENDED_ROUTE.md` to match your corrections and stop
spawning analysis until the route is fixed.
