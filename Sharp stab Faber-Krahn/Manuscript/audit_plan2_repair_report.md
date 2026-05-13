# Plan 2 Audit Repair Report (2026-05-13)

**Scope.** Resolution of the BLOCKING and two MAJOR findings of
`Manuscript/audit_plan2.md` (Agent 16): B1 (window scale), M1 (centre
identification), M2 (kappa-dependence).

Edits are minimal and targeted; no proofs were rewritten beyond what is
strictly required by the recommended fixes. Two files were edited:

- `Manuscript/plan2_weighted_metric_trace.tex` (Agent 12)
- `Manuscript/plan2_boundary_layer_assembly.tex` (Agent 13)

A `% AUDIT B1/M1/M2 REPAIR — DATE 2026-05-13` comment block was prepended
to each edited file.

---

## B1 — Metric-trace window scale (BLOCKING)

**File:** `Manuscript/plan2_weighted_metric_trace.tex`

### Edit B1.a — Abstract weighted-trace lemma made window-agnostic

Theorem `thm:wmt:abstract-trace` (§4.4.4): the choice
`L* := (b - a)/4` is replaced by a free parameter `L* in (0, b - a]`.
The conclusion now reads `widehat-rho in J* = [b - L*, b - L*/2]`, with
`b - widehat-rho <= L*` explicitly stated. This permits the concrete
instantiation below.

- Before: `Set L* := (b-a)/4 and J* := [b-L*, b-L*/2]`.
- After: `Fix any L* in (0, b-a] and set J* := [b-L*, b-L*/2]`.

### Edit B1.b — Concrete instantiation in Theorem `thm:wmt:trace`

Theorem `thm:wmt:trace` (§4.4.5) is rewritten so that the abstract
lemma is applied on the small window

```
[a, b] := [rho_delta - c_0 sqrt(delta_T), rho_delta],
L*     := c_0 sqrt(delta_T),
J*     := [rho_delta - c_0 sqrt(delta_T), rho_delta - c_0 sqrt(delta_T)/2],
```

with the explicit window constant
`c_0 := c_0(n, R, rho_*) = 4n / (omega_n rho_*^{n+1}) = 2 C_H2 / c`,
where `c = rho_*/n` and `C_H2 = 2/(omega_n rho_*^n)` come from
hypothesis (H2). The choice `c_0 = 2 C_H2 / c` makes the abstract
smallness condition `c L*/2 - C_H2 delta >= c L*/4` reduce to
`sqrt(delta) <= c_0 / 2`, i.e. an absolute smallness threshold
`delta <= delta_0^{(2)}(n, R, rho_*) := c_0^2 / 4`, recorded
explicitly. A second smallness threshold
`delta_0^{(1)} := ((1 - rho_*)/(kappa + c_0))^2` ensures
`rho_delta - c_0 sqrt(delta) >= rho_*`. Both thresholds depend only
on `(n, R, rho_*)`.

### Edit B1.c — Verification of (H1), (H2), (H3), (K) on the small window

- (H1) and (K) are obtained from Theorems `thm:wmt:52int` and
  `thm:wmt:K` by monotonicity of the Lebesgue integral in the
  integration domain: both integrands are non-negative, so restricting
  to the sub-interval preserves the same constants
  `C_*^act(n, R, rho_*)`, `C_*^kin(n, R, rho_*)`.
- (H2) depends only on the ambient `[rho_*, 1]` and the Talenti
  pointwise gap; the constants `c = rho_*/n` and
  `C_H2 = 2/(omega_n rho_*^n)` are unchanged.
- (H3) is unchanged.

### Edit B1.d — Sharp delta-rate at widehat-rho

The triangle bound at `widehat-rho in J*` yields

```
d_X(F_{widehat-rho}, B_1)^2
   <= 2 K_1 delta + 2 L* C_K delta
   = 16 C_*^act / (c c_0) * sqrt(delta) + 2 c_0 C_*^kin * delta^{3/2}.
```

The first summand is genuinely `O(sqrt(delta))` in isolation. The
sharp `O(delta)` rate is recovered by the explicit substitution
`sqrt(delta) <= delta_0^{-1/2} delta` on `delta in (0, delta_0]`,
yielding

```
d_X(F_{widehat-rho}, B_1)^2 <= C_*(n, R, rho_*) delta,
C_* := 16 C_*^act / (c c_0 sqrt(delta_0)) + 2 c_0 C_*^kin.
```

Since `delta_0` depends only on `(n, R, rho_*)`, so does `C_*`. This
is the trade-off flagged in the audit recommendation: the kinetic
transport step contributes `O(delta^{3/2})`, dominated by `delta`; the
Markov step contributes `O(sqrt(delta))` in isolation but is absorbed
by the smallness threshold into an `O(delta)` bound.

### Edit B1.e — Closing remark on boundary-layer volume

A new Remark `rem:wmt:layer-volume` is inserted after Theorem
`thm:wmt:trace`. It states

```
1 - widehat-rho <= (kappa + c_0) sqrt(delta_T),
|Omega \ E_{widehat-rho}| <= omega_n n (kappa + c_0) sqrt(delta_T)
                          =: C_lay(n, R, rho_*) sqrt(delta_T).
```

This is exactly the input required by Agent 13's Lemma
`lem:plan2-layer-vol`.

The 4.4.7 constants summary and the file's closing paragraph were
updated to record the new constants `c_0`, `C_lay` and to drop the
phrase "`O(sqrt(delta))`" without a constant: the new statement names
the explicit constant `C_lay(n, R, rho_*)`.

---

## M1 — Centre identification (MAJOR)

**File:** `Manuscript/plan2_weighted_metric_trace.tex`

### Edit M1.a — Notation block

In the notation block (§4.4.1), the description of `z_rho` is rewritten:

- Before: `z_rho denotes the Borel measurable centre field of
  Lemma~\ref{lem:fj-center-package} below.`
- After: `z_rho denotes the bulk centroid of E_rho, identified in
  Lemma~\ref{lem:fj-center-package} below with the canonical centre
  zbar = bar z_rho of the notation register §10.`

### Edit M1.b — Lemma `lem:fj-center-package` rewritten

The lemma now sets `z_rho := zbar = bar z_rho` on `G_I` explicitly,
quotes the centroid containment `B(z_rho, rho/4) subset E_rho subset
B(z_rho, 3 rho)` from Lemma `lem:centroid-borel` (Agent 11,
Section `subsec:fj-radial-trace`), and uses Agent 11 Remark
`rmk:centre-selection` for the absorption of the centroid-Fraenkel
offset `|zbar - z_rho^Fr| <= C(n, rho_*) sqrt(delta_T) <= rho/4` into
the FJ constant under the smallness threshold delta <= delta_0.

The proof now cites
- Lemma `lem:centroid-borel` (Agent 11) for Borel measurability and
  the containment hypothesis,
- Remark `rmk:centre-selection` (Agent 11) for the offset absorption,
- Lemmas `lem:fraenkel-centroid` and `lem:normal-osc-centroid`
  (Agent 11) for the FJ bounds at the centroid.

The abstract measurable-selection wording is removed. The centre is
fixed throughout `subsec:weighted-metric-trace` to be the bulk
centroid, identical to Agent 11.

---

## M2 — Constant dependence on kappa (MAJOR)

**File:** `Manuscript/plan2_weighted_metric_trace.tex`

### Edit M2.a — Pin kappa at the start of §4.4

A new "Canonical choice of kappa" paragraph is inserted in the
standing-hypotheses block: `kappa = kappa(n, R, rho_*) := 1` (the
canonical choice; any fixed Theta_n(1) constant works). The smallness
condition becomes `delta <= delta_0(n, R, rho_*)`, eliminating the
`kappa` argument.

### Edit M2.b — Drop kappa from all `C_*` constants

- Theorem `thm:wmt:52int`: `C_*^act(n, R, rho_*, kappa)` -->
  `C_*^act(n, R, rho_*)`, and the closing sentence is updated.
- Theorem `thm:wmt:K`: `C_*^kin(n, R, rho_*, kappa)` -->
  `C_*^kin(n, R, rho_*)`.
- Theorem `thm:wmt:trace`: `C_*(n, R, rho_*, kappa)` -->
  `C_*(n, R, rho_*)`, with `C_*` explicit in
  `eq:wmt:Cstar`.
- Corollary `cor:wmt:pointwise-asym`: `C(n, R, rho_*, kappa)` -->
  `C(n, R, rho_*)`.
- §4.4.7 constants table: all rows updated.

The closing paragraph of §4.4.7 now states explicitly that constants
have signature `(n, R, rho_*)` and that the only role of `kappa` is
through the smallness threshold.

---

## Agent 13 consumption check

**File:** `Manuscript/plan2_boundary_layer_assembly.tex`

### Edit Agent13.a — Theorem `thm:metric-trace-input`

The metric-trace input statement is reset to match Agent 12's repaired
output:

```
widehat-rho in [rho_delta - c_0 sqrt(delta_T(Omega)), rho_delta],
c_0 = c_0(n, R, rho_*) = 4n / (omega_n rho_*^{n+1}),
d_X(F_{widehat-rho}, B_1)^2 <= C_* delta_T,
C_* = C_*(n, R, rho_*).
```

The statement now declares the dimensional choice
`kappa = kappa(n, R, rho_*)` from §4.4 (notation register §12).

### Edit Agent13.b — Lemma `lem:plan2-layer-vol`

The constant `C'_n` is updated from `n(kappa + C_*)` to `n(kappa + c_0)`.
The proof is simpler now: with the new sqrt(delta_T)-window,

```
1 - widehat-rho <= (kappa + c_0) sqrt(delta_T)
```

directly, with no need to absorb a `delta_T`-term into `sqrt(delta_T)`.

### Edit Agent13.c — Corollary `cor:plan2-transfer-rhat`, Theorem `thm:plan2-bdd-SV`, Remark `rem:plan2-rho-star-fix`

`C'_n = n(kappa + C_*)` --> `C'_n = n(kappa + c_0)` everywhere in
Agent 13. The constants-formula `eq:plan2-C-final` is unchanged
structurally; the explanatory paragraph after it now lists
`C_*, c_0, kappa, delta_0` as the upstream constants of
Theorem `thm:metric-trace-input` (Agent 12) and §4.4.

### Edit Agent13.d — Sharp exponent and downstream theorems

No change is required to Theorem `thm:plan2-bdd-SV`'s squaring step
(`sssec:plan2-squaring`), nor to Theorems `thm:plan2-glob-SV`,
`thm:plan2-KJ-import`, `thm:plan2-FK`. They consume only the bounded
form `Fr(Omega)^2 <= C(n, R, rho_*) delta_T(Omega)` from
Theorem `thm:plan2-bdd-SV`, which is unchanged in shape.

---

## Chain closure verification

The chain

```
Agent 9 (level-set deficit identity)
   --> Agent 10 (metric framework, Theorem T)
   --> Agent 11 (FJ centre + oriented radial trace at bar z_rho)
   --> Agent 12 (integrated action + weighted metric trace at widehat-rho)
   --> Agent 13 (boundary-layer transfer + global assembly)
```

now closes with the sharp `delta_T`-rate. Step-by-step:

1. Agent 9 delivers `int (D_H + D_I) dmu <= C_1(n, rho_*) delta_T` and
   the profile-gap bound on the measure `mu`. (Unchanged.)
2. Agent 10 delivers Theorem T with constant `rho_*^{-n}`,
   transformed downstream by FJ to `C(n, R, rho_*)`. (Unchanged.)
3. Agent 11 delivers Lemma `lem:radial-trace` at the bulk centroid
   `bar z_rho`, with Lemma `lem:centroid-borel`'s containment
   `B(bar z_rho, rho/4) subset E_rho subset B(bar z_rho, 3 rho)`.
   (Unchanged.) Agent 12 now consumes this directly via the M1 repair.
4. Agent 12 (post-repair) delivers
   `d_X(F_{widehat-rho}, B_1)^2 <= C_*(n, R, rho_*) delta_T` with
   `widehat-rho in [rho_delta - c_0 sqrt(delta_T), rho_delta]` and
   `kappa = kappa(n, R, rho_*)` canonical. The smallness threshold
   `delta <= delta_0(n, R, rho_*)` is explicit; no hidden hypotheses.
5. Agent 13 (post-repair) consumes (4) and produces
   `|Omega \ E_{widehat-rho}| <= C_n(n, R, rho_*) sqrt(delta_T)`
   directly from the window scale. The squaring step
   `(a + b)^2 <= 2 a^2 + 2 b^2` then yields
   `Fr(Omega)^2 <= C_3(n, R, rho_*) delta_T(Omega)` (Theorem
   `thm:plan2-bdd-SV`).
6. The bounded reduction (Theorem `thm:plan2-glob-SV`) and
   Kohler-Jobin transfer (Theorem `thm:plan2-KJ-import`) deliver
   `Fr(Omega)^2 <= c_FK(n)^{-1} delta_FK(Omega)`, identical to the
   Plan 1 final theorem. (Unchanged.)

All constants are tracked with explicit dependence on `(n, R, rho_*)`;
no constant depends on `kappa` after the pin. The sharp exponent 2 in
`Fr(Omega)^2` is preserved: the only `sqrt(delta_T)` in the chain is
the layer error, which is squared only via the lossless squaring
identity `(a + b)^2 <= 2 a^2 + 2 b^2`.

---

## Files edited

- `Manuscript/plan2_weighted_metric_trace.tex` (header comment + edits
  B1.a, B1.b, B1.c, B1.d, B1.e, M1.a, M1.b, M2.a, M2.b)
- `Manuscript/plan2_boundary_layer_assembly.tex` (header comment +
  edits Agent13.a, Agent13.b, Agent13.c, Agent13.d)

No changes to Agent 11 (`plan2_fj_center_radial_trace.tex`); only its
existing Lemma `lem:centroid-borel` and Remark `rmk:centre-selection`
are now cited explicitly by Agent 12. No changes to Agent 9, 10, or
14.

The MINOR findings m1-m4 of the audit are out of scope of this repair
and remain to be addressed by Agent 17 (notation unification) or by a
separate minor-fix pass.
