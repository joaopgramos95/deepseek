# Raw Moving-Ball Closure Audit Execution Report

Date: 2026-05-25 (post-patch re-audit)

Source audited:

```text
Blocks/Raw Moving Ball Closure/faber_krahn_raw_moving_ball_closure.tex
```

Guideline used:

```text
Blocks/Raw Moving Ball Closure/raw_moving_ball_audit_guideline.md
```

Six disjoint scopes (A–F) were deployed as adversarial manuscript-grade
verifiers. Each read the TeX source first and produced a report only; no source
files were edited. The adjudicator independently traced the patched
coarea/shell core before and after deployment.

## Run History

```text
Run 1 (earlier today, pre-patch file):  BLOCKED
  Three defects in the affine shell / coarea block:
    B1  admissible-radius family depended on the tested radius (not countable);
    B2  Borel coarea approximation error measured against P(E_rho), not
        dH/|grad u|;
    B3  compact-exhaustion / no-escape step in Lemma shell incomplete.

Run 2 (this report, post-patch file):   PASS
  B1, B2, B3 are all genuinely resolved (see "Resolution of prior blockers").
  No scope returned a BLOCKING or MAJOR finding.
```

## Consolidated Verdict

```text
PASS
```

The route is internally complete and the sharp squared rate
`A(Omega)^2 <= C delta_T(Omega)` is preserved, with all constants depending
only on `(n,R,rho_*)` and the two explicitly imported constants. The closure
is conditional on a single external import (below), which is out of scope for
this manuscript.

## Scope Verdicts

```text
Scope A: End-to-End Dependency Audit                  PASS
Scope B: Level-Set Import and Bad-Density Audit       PASS
Scope C: Fusco--Julin and Radial Trace Audit          PASS
Scope D: Velocity Defect and Coarea/Shell Audit       PASS
Scope E: Moving-Ball First Variation / Kinetic        PASS
Scope F: Endpoint Trace and Final Transfer            PASS
```

## Resolution of Prior Blockers (Scope D)

```text
B1  RESOLVED.  Admissibility now registers a fixed countable family of bounded
    Borel endpoint pairs over rational (c,p,q,lambda,r,z,a) and U in the
    countable class of finite unions of rational balls compactly contained in
    Omega.  The family is independent of the tested radius.  Real (rho,z,a) are
    reached in Lemma shell by: fix a registered rational pair and buffer r>0;
    send h->0 (the uniform o(h) Taylor error on the compact closure of U
    satisfies o(h)/h < r for small h, so the real slab lies inside the rational
    slab and varcoarea applies); then send rational -> real (1-Lipschitzness of
    min/max) and r -> 0.  The outward buffer absorbs both the parameter
    mismatch and the o(h) error.

B2  RESOLVED.  The varcoarea Borel-approximation error is now
    2 eta * int_{partial* {u>s}} 1/|grad u|, which vanishes as eta -> 0 because
    the weighted boundary measure is finite at the admissible levels.  The old
    perimeter-measure error (a hidden lower-gradient move) is gone.

B3  RESOLVED.  The symmetric difference is split into an interior part on U
    (sharp, via localized varcoarea) and a complement.  The complement is paid
    crudely but made arbitrarily small by inner regularity:
      - level-set tail: |(E_{rho+h} Delta E)\U|/h <= w int_{partial*E\U}
        1/|grad u|, obtained as the EXACT total volume derivative
        |E_{rho+h}\E| = omega_n((rho+h)^n - rho^n) minus the U-localized coarea
        rate (no 1_{U^c} pair is needed);
      - deformation tail: |(E Delta T_h(E))\U|/h <= int_{partial*E\K} |W|, via
        the new Local BV deformation-tail lemma (Lemma BV-tail).
    Both tails are <= 2 epsilon because K is chosen with measure of
    partial*E \ K below epsilon for the finite Radon measure carrying all three
    tail integrands.  No graph parametrisation, smooth foliation, normal
    transport theorem, or pointwise lower bound on |grad u| is used.
```

## Findings

No BLOCKING or MAJOR findings in any scope. The items below are MINOR or NOTE.

### MINOR

```text
M1 (Scope D)  Status section, item 2 (line ~1170): the sentence
   "No Reshetnyak or lower-semicontinuity passage is used" is inaccurate.
   The Lemma BV-tail proof (lines ~757-763) uses strict BV_loc convergence of
   the mollifications to pass int eta|W| |grad u_eps| -> int eta|W| d|D 1_E|;
   that is exactly scalar Reshetnyak continuity against the continuous weight
   eta|W|.  The mathematics is correct and standard (AFP Thm 2.39 / Maggi) and
   is used only for a tail forced <= 2 epsilon, but the self-description is
   false as written.  Fix: soften the clause and cite the strict-convergence/
   Reshetnyak fact in Lemma BV-tail.

M2 (Scopes A, D, E)  Ball-ball lower bound (line ~984):
   |B_rho(z_1) Delta B_rho(z_2)| >= c(n) rho^{n-1} min{d,rho}, used in
   Lemma center-transfer, is asserted with no in-file proof or citation.
   True, standard; add a one-line slab cross-section proof or a reference.

M3 (Scope D, prior audit)  Theorem qplus (line ~882) is stated for
   rho in (0,1], but D^+q and shell-admissibility require rho in (0,1).
   Restrict to (0,1).

M4 (Scopes A, B)  Import provenance overstated.  Lines ~179-183 describe the
   imported identity as using "only BV coarea, the flux identity, and the
   De Giorgi isoperimetric inequality," and line ~207 says the block "proves"
   the profile-gap identity.  In fact the profile-gap identity is reconstructed
   internally here (verified correct), and the imported identity's
   finite-perimeter form is not established in the source block (see Residual
   Dependency).  Reword to "we derive from the imported identity ..." and state
   the finite-perimeter import explicitly.

M5 (Scope C)  Radial-trace Gauss--Green write-up (lines ~393-401) leaves the
   cutoff-gradient term implicit.  Add one sentence:
   int_E grad(chi_eps) . X = O(eps^{n-1}) -> 0 (annulus volume ~ eps^n,
   |grad chi_eps| ~ 1/eps, |X| bounded).

M6 (Scope D)  Lemma shell cutoff inclusion (lines ~848-852): the claim
   "(E Delta T_h(E)) \ U subset {eta=1} for small h" needs the eta=0
   neighbourhood of K shrunk inside U and eta=1 on the outer shell reached by
   T_h(E); spell out, or use the weaker bound int eta|W| <= int_{partial*E\K}
   |W| directly.

M7 (Scope A)  Dead bibliography entries: CL2012, FMP2008, AFP2000, Maggi2012,
   Talenti1976 are uncited in the body (only FJ2014 is cited).  Prune or cite.
   Note CL2012 (selection principle) being unused confirms the route avoids a
   selection principle.
```

### NOTE

```text
N1 (Scope E)  center-transfer line ~1005 "Combine with eq:sc-input" is terse;
   the triangle inequality + squaring is correct but left implicit.
N2 (Scope F)  Two asymmetry normalizations coexist: the manuscript's Fraenkel
   A(E) normalizes |E Delta B|/|E|, while the Fusco--Julin display normalizes
   by r_E^n.  Never conflated in the audited steps; q(rho_delta)/(omega_n
   rho_delta^n) = A(E_{rho_delta}) is exact under the manuscript convention.
N3 (Scope E)  Existence-of-minimiser argument (lines ~901-904) compresses
   "inf over R^n = min over the compact ball {|z| <= R+rho}."
```

## Load-Bearing Checks That Passed

```text
- Dependency graph is acyclic; all \ref targets resolve; rate-preserving.
- Level-set budget eq:budget with C_L = 2 n^2 omega_n; profile-gap identity and
  D_H + D_I = omega_n rho^n (alpha - alpha_B); 0 <= w <= rho/n <= 1/n;
  bad-density |B_tau| <= C_tau delta_T with C_tau = 4n/(omega_n rho_*^{n+1}).
- Fusco--Julin is the genuine single-min-of-sum form (verified against
  arXiv:1111.4866): one common centre controls both the symmetric-difference
  and the normal-oscillation term.  Scaling to rho in [rho_*,1] and reduction
  to D_I are correct.
- Radial-trace finite-perimeter Gauss--Green is sound: divergence formulas,
  1/|x-z| integrability for n>=2, the identity W_z = X.nu + (W_z/2)|nu-e_z|^2,
  centre localization |z| <= R+1 established before the lemma is invoked.
- Velocity defect: (int |V-Vbar|)^2 <= D_H via the Cauchy--Schwarz identity
  int (f-fbar)^2/f = (P*/P^2) D_H and P* <= P.
- varcoarea two-sided differentiation, corrected error measure, critical-set
  discard via real-analyticity, level->radius pullback on G_tau.
- Lemma BV-tail upper bound (by |W|, harmless), used only in the vanishing tail.
- Affine first variation: T_h(B_rho(z_rho)) = B_{rho+h}(z_rho+ha), Jacobian
  (1+h/rho)^n, the (n/rho) q term, inf over a; D^+q -> q'_+ transition valid;
  unconditional nestedness Lipschitz bound q'_+ <= 2 n omega_n.
- Positive kinetic bound: (q'_+)^2 <= C(D_H + D_I) on G; drho <= tau_0^{-1}
  dmu on G_tau; bad set paid by measure; output genuinely in unweighted drho.
- Endpoint trace and final transfer: averaging to rho_0, propagation by
  Cauchy--Schwarz, boundary-layer |Omega \ E_{rho_delta}| <= n omega_n kappa
  delta_T^{1/2}, final squaring preserves A(Omega)^2 <= C delta_T; large-deficit
  fallback valid.
```

## Residual Dependency (Now Closed)

```text
The entire route rests on eq:imported-levelset-identity (the "Exact deficit
identity on reduced-boundary level sets" from the LevelSetIdentity block).

STATUS: RESOLVED (2026-05-25, post-audit).
The finite-perimeter form is genuinely proved in
  Blocks/Level Set Identity/LevelSetIdentity.tex
as Theorem "Exact deficit identity on reduced-boundary level sets", for every
open Omega of finite measure -- no smoothness of dOmega, no pointwise lower
bound on |grad u|, all integrals on reduced boundaries, a.e. level.  Key
ingredients: BV coarea; the flux identity int_{d*E_t}|grad u| = m(t) proved by
Lipschitz truncation of the weak equation (not a boundary trace of grad u);
the De Giorgi isoperimetric inequality; and the rearranged primitive with the
corrected I'' = -1/alpha (alpha = int 1/|grad u|), NOT -1/beta, which would
silently delete D_H.

An independent adversarial verification of that proof returned PASS: lem:flux,
lem:noatoms (Stampacchia), lem:I3c (inverse-AC, alpha>0 a.e.), lem:cov/gap,
lem:profile-gap, and Hyp-G-independence all hold.  One self-cancelling
factor-of-2 arithmetic slip in lem:endpoint (the file wrote 1/(2n(n+2)) where
1/(n(n+2)) is correct, in two compensating places; the boxed identity was
nonetheless true) has been corrected.  The smooth-only note
level-set-deficit-identity.tex (lines 28-30) had merely conjectured the
finite-perimeter extension; its caveat now points to the proved theorem.

The manuscript's import wording (lines ~179-186) was updated to cite the
identity as proved (finite-perimeter, a.e. level, reduced boundaries), not
imported-on-faith.  All three files recompile cleanly.  The route is now
self-contained modulo standard cited theorems (BV coarea, De Giorgi
isoperimetry, Fusco-Julin, Reshetnyak/Gauss-Green from AFP/Maggi).
```

## Bottom Line

```text
The patched coarea / admissibility / BV-tail / shell block survives
line-by-line scrutiny.  The three previously blocking defects are genuinely
fixed.  The remaining items are MINOR (one is a false self-description sentence
that should be corrected for honesty; the rest are exposition/citation
tightenings) and do not affect the route, the final theorem, or the sharp
A(Omega)^2 <= C delta_T(Omega) rate.

POST-AUDIT (2026-05-25): all MINOR items above have been applied to the
manuscript (Reshetnyak self-description corrected; ball-ball lower bound now
proved in-file; import provenance reworded; radial-trace cutoff term spelled
out; shell cutoff inclusion tightened; center-transfer triangle inequality
made explicit; dead bib entries pruned), and the one external open item -- the
finite-perimeter form of the imported level-set identity -- has been CLOSED
(see "Residual Dependency (Now Closed)").  Manuscript compiles to 14pp.
```
