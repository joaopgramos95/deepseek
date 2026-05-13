# Plan 2 Internal Audit (Agent 16)

**Scope.** Audit of the Plan 2 section drafts against the Plan 2 source
blocks and the Non-Negotiable Standards of `MANUSCRIPT_ASSEMBLY_AGENTS.md`.

Drafts audited:

- `Manuscript/plan2_levelset_identity.tex`        (Agent 9)
- `Manuscript/plan2_metric_framework.tex`         (Agent 10)
- `Manuscript/plan2_fj_center_radial_trace.tex`   (Agent 11)
- `Manuscript/plan2_weighted_metric_trace.tex`    (Agent 12)
- `Manuscript/plan2_boundary_layer_assembly.tex`  (Agent 13)
- `Manuscript/plan2_aux_centroid_note.tex`        (Agent 14, auxiliary)

Verdict ordering: BLOCKING / MAJOR / MINOR / NOTE.

---

## **VERDICT: BLOCKED on 1 finding.**

One BLOCKING finding (B1) prevents the repaired Plan 2 chain from closing
as drafted: Agent 12's metric-trace window does not place \(\widehat\rho\)
within a \(\sqrt{\delta_T}\)-neighbourhood of \(1\), so Agent 13's
boundary-layer estimate fails on the stated hypotheses. Two MAJOR issues
require coordination edits before integration. Remaining MINOR/NOTE items
are local clarifications.

---

## BLOCKING

### B1. Metric-trace window in Agent 12 does not produce an \(O(\sqrt{\delta_T})\) boundary layer; Agent 13's input mismatches Agent 12's output.

**Location.**
- Agent 12: `plan2_weighted_metric_trace.tex`, Theorem `thm:wmt:trace`
  (§4.4.5), lines 660–728, with the choice
  \(L^*:=(\rho_\delta-\rho_*)/4\) and
  \(\widehat\rho\in J^*=[\rho_\delta-L^*,\rho_\delta-L^*/2]\)
  (lines 665–666).
- Closing remark, lines 825–830: "the boundary layer
  \(\Omega\setminus E_{\widehat\rho}\) has volume \(O(\sqrt{\delta})\)".
- Agent 13: `plan2_boundary_layer_assembly.tex`, Theorem
  `thm:metric-trace-input` (lines 93–119), states
  \(\widehat\rho\in[\rho_\delta-C_*\delta_T(\Omega),\rho_\delta]\).
- Source map `source_map.md` item **E4.6**: ``ρ̂ ∈ [ρ_δ − C_* δ_T, ρ_δ]''.

**Issue.**
Agent 12 instantiates the abstract weighted-trace lemma with
\([a,b]=[\rho_*,\rho_\delta]\) and \(L^*=(b-a)/4=(\rho_\delta-\rho_*)/4\),
so \(\widehat\rho\le\rho_\delta-L^*/2\) and
\(1-\widehat\rho\ge\kappa\sqrt{\delta_T}+L^*/2\). With \(\rho_*=1/2\) and
\(\delta_T\to 0\), \(L^*/2\to(1-\rho_*)/8=1/16\), so
\(1-\widehat\rho\ge 1/16+\kappa\sqrt{\delta_T}\). Consequently
\(|\Omega\setminus E_{\widehat\rho}|=\omega_n(1-\widehat\rho^{\,n})\) is
bounded **below** by a fixed positive constant depending on
\((n,\rho_*)\), **not** by \(O(\sqrt{\delta_T})\). Agent 12's claim in
the closing remark and Agent 13's stated window
\([\rho_\delta-C_*\delta_T,\rho_\delta]\) are inconsistent with the
proof. Agent 13's boundary-layer estimate Lemma~`plan2-layer-vol`
\(|\Omega\setminus E_{\widehat\rho}|\le C_n\sqrt{\delta_T}\)
(lines 158–202) therefore fails: it derives from
\(\widehat\rho\ge 1-\kappa\sqrt{\delta_T}-C_*\delta_T\), an inequality
that is **not** provided by Agent 12's actual construction.

**Stop-condition match.** This is exactly the rate-loss /
normalization-inconsistency stop condition: the sharp \(\delta_T\) chain
collapses unless \(\widehat\rho\) lives in a
\(\sqrt{\delta_T}\)-neighbourhood of \(\rho_\delta\).

**Recommended fix.**
Tighten Agent 12's instantiation of the abstract weighted-trace lemma.
Two equivalent options:

1. Apply Theorem `thm:wmt:abstract-trace` to
   \([a,b]=[\rho_\delta-c_0\sqrt{\delta_T},\rho_\delta]\) for an explicit
   \(c_0=c_0(n,\rho_*,\kappa)\), absorbing the integrated action and
   kinetic bounds restricted to this small interval (both bounds are
   subadditive in the integration window, so they still hold over
   \([\rho_\delta-c_0\sqrt{\delta_T},\rho_\delta]\) with the same
   \(C_*^{\mathrm{act}},C_*^{\mathrm{kin}}\)). This yields
   \(L^*=c_0\sqrt{\delta_T}/4\) and \(\widehat\rho\in
   [\rho_\delta-c_0\sqrt{\delta_T},\rho_\delta-c_0\sqrt{\delta_T}/8]\),
   so \(1-\widehat\rho=O(\sqrt{\delta_T})\) and Agent 13's
   \(O(\sqrt{\delta_T})\) layer estimate is recovered. The trade-off is
   that the kinetic transport step contributes
   \(L^*\,C_K\,\delta_T=O(\sqrt{\delta_T})\cdot\delta_T=
   O(\delta_T^{3/2})\le C\delta_T\), preserving the sharp rate.
2. Alternatively, after the Markov step in `thm:wmt:abstract-trace`,
   transport from \(\rho_0\in J^*\) directly to \(\rho_\delta\) (or to
   any point at scale \(\sqrt{\delta_T}\) below \(\rho_\delta\)) using
   the kinetic bound (K). Then \(\widehat\rho\) is the *transported*
   endpoint, lying in
   \([\rho_\delta-O(\sqrt{\delta_T}),\rho_\delta]\), and the
   distance bound at \(\widehat\rho\) inherits the same \(O(\delta_T)\)
   rate up to the kinetic-transport correction
   \(\le L^*\,C_K\,\delta_T\), which we then have to bound by
   \(C\,\delta_T\) using \(L^*=O(1)\). This is fine because the
   contribution is \(O(\delta_T)\), but **the bound at**
   \(\widehat\rho\) is what is needed, not at \(\rho_0\). This
   restructuring is closer to the WIP block design.

Either fix realigns Agent 12 with the source-map statement E4.6 and
with Agent 13's Theorem `thm:metric-trace-input`. Agent 12 must also
correct its closing remark (lines 825–830) to state explicitly that
\(\widehat\rho\) lies in
\([\rho_\delta-C_*\sqrt{\delta_T},\rho_\delta]\) (with the appropriate
constant), not in a fixed-size window.

---

## MAJOR

### M1. Centre-field identification across Agents 11 and 12.

**Location.**
- Agent 11: `plan2_fj_center_radial_trace.tex`, Remark
  `rmk:centre-selection` (lines 164–176) fixes
  \(z_\rho:=\bar z_\rho\) (centroid) throughout §4.3.
- Agent 12: `plan2_weighted_metric_trace.tex`, Lemma
  `lem:fj-center-package` (lines 171–198) defines the centre via the
  FJ centre package, setting \(|z_\rho|\le 2R\) on \(G_I\) and
  \(z_\rho=0\) on \(B_I\), with measurable-selection citation, **not**
  identified with the centroid.

**Issue.**
Agent 11's radial-trace lemma (Theorem `thm:radial-trace`) is proved at
the **centroid** \(\bar z_\rho\), using the explicit containment
\(B(\bar z_\rho,\rho/4)\subset E_\rho\subset B(\bar z_\rho,3\rho)\) of
Lemma `lem:centroid-borel`. Agent 12 then invokes this lemma in
`lem:wmt:radial-trace` for a centre \(z_\rho\) that may be a generic
FJ centre, not the centroid. The proof of `lem:wmt:good-htrace` and the
proof of Theorem `thm:wmt:52int` use this \(z_\rho\) without verifying
the containment hypothesis on which Agent 11's truncation step rests.

This is not a Π-route violation (the centroid is allowed as a centre
choice; only signed-radial-moment Π identities are off-limits, see N1),
but it is a structural ambiguity that must be resolved before
integration.

**Recommended fix.**
Agent 12 should fix \(z_\rho:=\bar z_\rho\) on \(G_I\), identical to
Agent 11. Lemma `lem:fj-center-package` should be restated with
\(z_\rho:=\bar z_\rho\) and the absorption argument of Agent 11's
Remark `rmk:centre-selection`
(\(|\bar z_\rho-z^{\mathrm{Fr}}_\rho|\le C\sqrt{\delta_T}\le\rho/4\) for
\(\delta_T\le\delta_0\)) used to justify that \(\bar z_\rho\) satisfies
the FJ bound at the centroid with the same constant up to enlargement.
This is already half-done in Agent 11 Remark `rmk:centre-selection`;
Agent 12 should cite it explicitly and drop the abstract
measurable-selection wording.

### M2. Constant dependence on \(\kappa\) is inconsistent between Agents 12 and 13.

**Location.**
- Agent 12: \(C_*^{\mathrm{act}},C_*^{\mathrm{kin}},C_*\) all carry
  \(\kappa\) (cf. lines 277–283, 498–505, 668–728, and constants table
  lines 798–819).
- Agent 13: Theorem `thm:metric-trace-input` (lines 93–119) declares
  \(C_*=C_*(n,R,\rho_*)\) without \(\kappa\), and propagates this
  signature into Lemma `plan2-layer-vol`, Theorem `thm:plan2-bdd-SV`,
  and the constants formula `eq:plan2-C-final`.

**Issue.**
Agent 12 explicitly says (lines 372–375 and 821–825) that the
\(\kappa\)-dependence enters only through the smallness threshold
\(\delta_0(n,R,\rho_*,\kappa)\). Once \(\kappa\) is fixed by the
notation register as a function of \((n,R,\rho_*)\), \(C_*\) becomes
\(C_*(n,R,\rho_*)\). Agent 13 silently assumes this fixing, but the
fixing is not yet recorded in the manuscript.

**Recommended fix.**
Either (a) Agent 12 fixes \(\kappa=\kappa(n,R,\rho_*)\) explicitly at
the start of §4.4 (with the canonical choice deferred to a
"choice-of-\(\kappa\)" remark) and propagates the signature
\(C_*(n,R,\rho_*)\) to its outputs; or (b) Agent 13 carries the
\(\kappa\) argument through, and the notation-unification agent
(Agent 17) collapses it. Option (a) is preferable and matches the
notation register §12.

---

## MINOR

### m1. Lemma 8.3 (superlevel transfer): constant discrepancy.

**Location.**
- Agent 9: `plan2_levelset_identity.tex`, Lemma
  `lem:superlevel-transfer` (lines 897–926) states
  \(\mathcal A(\Omega)\le\mathcal A(E_t)+4\eta/L\).
- Agent 13: `plan2_boundary_layer_assembly.tex`, Lemma
  `plan2-superlevel` (lines 225–280) states the same lemma with
  constant \(2\eta/L\).

**Issue.**
Both are valid (Agent 13's is tighter). Agent 9's "enlarging the
constant from 2 to 4" parenthetical is conservative; Agent 13's
explicit triangle-inequality bookkeeping gives \(2\eta/L\) without
slack. This duplicate lemma should appear only once.

**Recommended fix.**
Keep Agent 13's version with the \(2\eta/L\) constant. Agent 9 should
either delete its Lemma 8.3 (consequence subsection) and forward-ref
Agent 13, or update its constant to \(2\eta/L\) and remove the "enlarge
to 4" wording. The chain in Agent 13 then uses \(C_n':=n(\kappa+C_*)\)
without the conservative factor of 2 that the 4 would introduce.

### m2. Agent 10 Theorem T constant dependence stated as \(C(n,\rho_*)\), then as \(C(n,R,\rho_*)\).

**Location.**
- Agent 10: Theorem `thm:mf-T` (line 339) writes \(C(n,\rho_*)=\rho_*^{-n}\).
- Agent 10: Eq. `eq:mf-int-cond` (line 605) writes \(C(n,R,\rho_*)\).
- Agent 10: Theorem `thm:mf-main` (item (iv), line 638) writes
  \(\rho_*^{-n}\), no \(R\).

**Issue.**
The pure metric first-variation bound (T) has constant
\(\rho_*^{-n}\) (no \(R\)). The downstream integrated form
\(\int|\dot F_\rho|^2 d\mu\le C\delta_T\) acquires an \(R\) through
Fusco--Julin scaling and centre containment, which is correct. The
draft is consistent if read carefully, but the constants table at the
end (line 644) mixes \(C(n,R,\rho_*)\) in a confusing way.

**Recommended fix.**
Insert a one-line remark at the end of §4.2 noting that Theorem T's
constant is \(\rho_*^{-n}\) without \(R\); the \(R\)-dependence enters
only when combining with FJ in §4.4. Adjust the constants paragraph
(line 644) accordingly.

### m3. Agent 11's Theorem `thm:radial-trace` constant inconsistency.

**Location.**
Lines 276–278 and 419–425 of `plan2_fj_center_radial_trace.tex`.

**Issue.**
The theorem statement (line 277) gives
\(C_4(n,R,\rho_*)=\max\{n/\rho_*,1/2\}\); the proof's final line
(eq.~`T-trace-explicit`, line 419) gives
\(C_4=\max\{n/\rho_*,3R/(2\rho_*)\}\). These differ in the
tangential-term constant: \(3R/(2\rho_*)\) (proof) vs.\ \(1/2\) (stated).
The proof's constant is correct (the bound \(w\le 3R/\rho_*\) was used
in eq.~`T-tan-bound`). The summary at line 553 also writes
\(\max\{n/\rho_*,3R/(2\rho_*)\}\). The discrepancy is in the theorem
statement at line 277.

**Recommended fix.**
Correct the explicit form in the theorem statement at line 277 to
\(C_4=\max\{n/\rho_*,3R/(2\rho_*)\}\), polynomial in \(n,R,1/\rho_*\).

### m4. Agent 11 Remark `rmk:FJ-equiv` uses a Π-flavoured identity.

**Location.**
`plan2_fj_center_radial_trace.tex`, eq.~`eq:beta-div` (line 105) and
surrounding text writes the divergence identity
\(2\beta(E,z)^2=\int|\nu-(x-z)/|x-z||^2\,d\mathcal H^{n-1}
=2(P(E)-P(B_\rho))+2\Pi(E,z)\) with
\(\Pi(E,z):=(n-1)\int(\mathbf 1_{B_\rho}-\mathbf 1_E)|x-z|^{-1}\,dx\).

**Issue.**
The use of the symbol \(\Pi\) here is purely a bookkeeping shorthand
inside the divergence identity used to convert
\(\beta(E,z)^2\) into the normal-oscillation integral. Agent 11
explicitly says (line 117) "we use only the inequality" — no
\(\Pi\)-control hypothesis is invoked. This is **not** the centroid
\(\Pi\)-route. To avoid confusion with Agent 14's conditional
\(\Pi\)-control, this remark should be flagged.

**Recommended fix.**
Add a one-line note at the end of Remark `rmk:FJ-equiv` stating
"The quantity \(\Pi(E,z)\) is recorded here only as a name for the
divergence-identity term; no integrated \(\Pi\)-control is invoked."
This anchors the audit check (4.1) explicitly.

---

## NOTE

### N1. No load-bearing use of the centroid Π-route. **PASS.**

Agents 9–13 do not invoke the conditional integrated \(\Pi\)-control
estimate of `WIP_SpaceTimeIdentity.tex` / `WIP_CentroidBound.tex`.
Agent 11 uses the centroid \(\bar z_\rho\) as a centre choice; this is
permitted by the notation register §10 and is **not** the
\(\Pi\)-route. The divergence-identity term named \(\Pi(E,z)\) in
Agent 11 Remark `rmk:FJ-equiv` is a notational artefact (see m4).
Agent 14 is correctly flagged AUXILIARY/CONDITIONAL at the top of its
file (lines 23, 37–49).

### N2. Finite-perimeter first variation: smooth-flow + passage both present. **PASS.**

Agent 10 §4.2.7 (smooth-flow proof, `prop:mf-T-smooth`) and §4.2.8
(BV/coarea approximation `lem:mf-approx`) and §4.2.9 (closure via
Reshetnyak `lem:mf-reshetnyak` and AGS `lem:mf-AGS`) both appear, with
explicit citations. The standing-hypotheses (§4.2.1) clearly state no
global Lipschitz boundary regularity is assumed. No hidden smoothness
remains in the final Theorem T statement.

### N3. Fusco--Julin scaled correctly. **PASS.**

Agent 11 Theorem `thm:FJ-scaled` carries constants \(C_1(n,\rho_*)
=4 C_{\mathrm{FJ}}(n)\max(1,\rho_*^{-(n+1)})\), matching the
preliminaries item C3. Constants \(C_2,C_3,C_4,C_5,C_6\) depend on
\((n,R,\rho_*)\) and are tracked. Agent 4's preliminaries (C2, C3, C4)
are consumed correctly.

### N4. Oriented radial trace is proved, not handwaved. **PASS.**

Agent 11 Theorem `thm:radial-trace` (§4.3.3, lines 246–426) gives the
full proof using the named vector field
\(X(x)=||x-\bar z_\rho|/\rho-1|(x-\bar z_\rho)/|x-\bar z_\rho|\)
(eq. `X-def`, line 251), the truncation \(\eta_\eps\) (eq. `Xeps-def`,
line 319), and the finite-perimeter divergence theorem (Maggi 16.3,
cited via preliminaries A4). The truncation is justified
(Remark `rmk:truncation`, lines 428–445) by the centroid containment
\(B(\bar z_\rho,\rho/4)\subset E_\rho\) of
Lemma `lem:centroid-borel`. No ray-slicing shortcut is used; the
slicing route is explicitly demoted to Remark `rmk:slicing-route` as
an alternative.

### N5. Good/bad level split preserves \(\delta_T\) rate. **PASS.**

Agent 12 Markov bound `lem:wmt:markov-BI` gives \(\mu(B_I)\le
\eta_I^{-1}C_1\delta_T\), linear in \(\delta_T\); on the bad set the
trivial bound \(\le(2\omega_n)^2\mu(B_I)\) contributes
\(O(\delta_T)\), not \(O(\sqrt{\delta_T})\). The pointwise good-set
estimates (FJ asymmetry, FJ normal, radial trace) involve a
\(\sqrt{\mathcal I}\) only **inside** \(T_\rho\), which is **squared**
before integration in `lem:wmt:good-htrace` (line 264). The integrated
action `eq:wmt:52int` is therefore \(O(\delta_T)\). Remark
`rem:wmt:rate-good-bad` (lines 158–169) and the closing remark on
sharp rate (lines 377–387) document this correctly.

### N6. Weighted metric trace uses both weighted action and Lebesgue kinetic bounds. **PASS.**

Agent 12 Theorem `thm:wmt:abstract-trace` (lines 558–638) declares
four hypotheses (H1) integrated weighted action, (H2) interval lower
bound on \(\mu\), (H3) matching upper bound on \(\mu\), and (K)
integrated Lebesgue kinetic. The proof uses (H1) for Markov in Step 1
and (K) for kinetic transport in Step 2; neither is redundant.
Remark `rem:wmt:H1-alone` (lines 640–655) explicitly explains why (H1)
alone loses a \(\sqrt{\delta}\). The good-\(-t'\) decomposition
(Lemma `lem:wmt:badtprime`, §4.4.3) provides (K) from (H1) and the
Talenti profile gap; both pieces are present.

### N7. Boundary-layer transfer squares AFTER transfer. **PASS** (modulo B1).

Agent 13 §4.5.4 (`sssec:plan2-squaring`, lines 316–399) explicitly
proves \(\mathcal A(\Omega)\le\mathcal A(E_{\widehat\rho})+
2C_n'\sqrt{\delta_T}\) first (Corollary `cor:plan2-transfer-rhat`,
line 294), then squares via \((a+b)^2\le 2a^2+2b^2\) to obtain
\(\mathcal A(\Omega)^2\le 2\mathcal A(E_{\widehat\rho})^2
+8(C_n')^2\delta_T\). Remark `rem:plan2-square-before` (lines 429–444)
explains why squaring before would fail. The sharp exponent 2 is
preserved.

**Caveat.** Pending the resolution of B1, the input
\(|\Omega\setminus E_{\widehat\rho}|\le C_n\sqrt{\delta_T}\) is not
actually delivered; under the current Agent 12 draft, the layer is
\(O(1)\). N7 is **conditionally PASS** assuming B1 is fixed.

### N8. Final theorem matches Plan 1 normalisation. **PASS.**

Agent 13 Theorem `thm:plan2-FK` (line 557) and the explicit constant
formula `eq:plan2-cFKdef` (line 528) match Plan 1 Agent 8's
D4.6 / `Final/master.tex` `(eq:cFKdef)` verbatim. Remark
`rem:plan2-vs-plan1-normalisation` (lines 592–606) confirms identical
statement and constant. The source-map header in Agent 13
(lines 44–57) records this normalisation check.

### N9. No \(N\) dimension symbols, no hidden smoothness. **PASS.**

All six drafts use \(n\). The `n` vs `N` conversion is needed only in
the Plan 1 drafts at unification time. Hypothesis-tracking sections
appear in Agent 9 (§ failure modes, lines 928–964), Agent 10
(§4.2.1 standing hypotheses, lines 54–89, and `rem:no-graph`,
lines 504–510), Agent 11 (Remark `rmk:hypothesis-tracking`,
lines 527–540). No section silently assumes \(C^1\) boundary.

### N10. Agent 14 correctly flagged as auxiliary. **PASS.**

`plan2_aux_centroid_note.tex` carries the header (line 23):
``STATUS: AUXILIARY — NOT LOAD-BEARING. CONDITIONAL ON INTEGRATED
Π-CONTROL.'' The opening quote block (lines 37–49) re-states the
auxiliary status. The (Π-int) hypothesis is listed as
``MISSING / CONDITIONAL'' in the source-map header.

---

## Summary of action items before integration

1. **(BLOCKING)** Agent 12 must rewrite Theorem `thm:wmt:trace` so that
   \(\widehat\rho\in[\rho_\delta-c_0\sqrt{\delta_T},\rho_\delta]\) for
   an explicit \(c_0=c_0(n,\rho_*,\kappa)\), restoring the source-map
   E4.6 statement and Agent 13's input. (See B1 for two fix options.)
2. **(MAJOR)** Identify the Agent 12 centre field with Agent 11's
   centroid \(\bar z_\rho\) on \(G_I\) (M1).
3. **(MAJOR)** Fix \(\kappa=\kappa(n,R,\rho_*)\) explicitly in Agent 12
   and reduce \(C_*\) to a function of \((n,R,\rho_*)\) (M2).
4. **(MINOR)** Reconcile the \(2\eta/L\) vs \(4\eta/L\) constant in
   Lemma 8.3 (m1); fix the Agent 11 theorem-statement constant (m3);
   tighten Agent 10's constants paragraph (m2); annotate Agent 11
   Remark `rmk:FJ-equiv` (m4).

Once B1 is fixed, the chain (LevelSetIdentity → MetricFramework →
FJ+RadialTrace → WeightedMetricTrace → BoundaryLayerTransfer →
GlobalAssembly) closes at the sharp rate \(\mathcal A(\Omega)^2\le
C(n,R,\rho_*)\delta_T(\Omega)\), and the final theorem agrees with
Plan 1's at the explicit dimensional constant \(c_{\mathrm{FK}}(n)\).

---

## Repair Status (2026-05-13)

**B1, M1, M2 are resolved.** See
`Manuscript/audit_plan2_repair_report.md` for the exact edits.

- **B1 (BLOCKING) — RESOLVED.** Agent 12's Theorem `thm:wmt:trace`
  now instantiates the abstract weighted-trace lemma on the window
  `[ρ_δ − c_0√δ_T, ρ_δ]` with `L* = c_0√δ_T`, placing
  `widehat-ρ ∈ [ρ_δ − c_0√δ_T, ρ_δ − c_0√δ_T/2]` and yielding
  `|Ω ∖ E_widehat-ρ| ≤ C_lay(n,R,ρ_*)√δ_T`. The sharp `δ_T`-rate
  `d_𝓧(F_widehat-ρ, B_1)² ≤ C_*(n,R,ρ_*) δ_T` is preserved via the
  explicit smallness threshold `δ_T ≤ δ_0(n,R,ρ_*)` (stated in the
  hypotheses and unwound in the proof). Agent 13's
  Theorem `thm:metric-trace-input` and Lemma `lem:plan2-layer-vol`
  are updated to consume the new window scale; the boundary-layer
  estimate now closes directly without absorbing a `δ_T`-term into
  `√δ_T`.

- **M1 (MAJOR) — RESOLVED.** Agent 12's Lemma
  `lem:fj-center-package` now sets `z_ρ := z̄_ρ` (bulk centroid) on
  `G_I` explicitly, citing Agent 11's
  Lemma `lem:centroid-borel` (containment) and
  Remark `rmk:centre-selection` (offset absorption). The downstream
  applications of Agent 11's Theorem `thm:radial-trace` in Agent 12
  now satisfy the centroid containment hypothesis. The abstract
  measurable-selection wording is removed.

- **M2 (MAJOR) — RESOLVED.** Agent 12 pins
  `κ = κ(n, R, ρ_*) := 1` (canonical, per notation register §12)
  at the start of §4.4. All constants
  `C_*^act, C_*^kin, C_*, δ_0` now have signature `(n, R, ρ_*)`
  with no residual `κ`-argument; Agent 13's Theorem
  `thm:metric-trace-input` consistency is restored without silent
  assumptions.

The chain Agent 9 → 10 → 11 → 12 → 13 now closes with the sharp
`δ_T`-rate, and the final Plan 2 theorem matches Plan 1's at the
explicit dimensional constant `c_FK(n)`. The MINOR findings m1–m4
remain to be addressed at the notation-unification stage (Agent 17)
or by a separate minor-fix pass; they are not blocking.
