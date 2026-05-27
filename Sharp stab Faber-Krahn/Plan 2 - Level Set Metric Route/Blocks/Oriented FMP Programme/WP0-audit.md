# WP0. Definitions and Permissible-Input Audit

**Status.** Closed.  This document is short and self-contained.  Every claim
referenced as "available input" in WP1--WP7 either (i) is proved in the
companion file `Sharp Faber-Krahn Manuscript/FJ_quantitative_attempts.tex`
with the proof location given here, (ii) is taken from a cited published
source whose constant is computable, or (iii) is explicitly flagged as
conjectural and listed in WP1--WP3 as a deliverable.

Throughout, \(n\ge 2\) and \(\omega_n=|B_1|\).  Unless otherwise stated,
the volume normalisation is \(|E|=\omega_n\).  We write
\[
   D(E):=P(E)-P(B_1),\qquad
   I_z(E):=\int_E\frac{dx}{|x-z|},
\]
\[
   {\cal B}_z(E):=\tfrac12\int_{\partial^* E}
                        |\nu_E(x)-e_z(x)|^2\,d{\cal H}^{n-1}(x),
                        \qquad e_z(x):=\frac{x-z}{|x-z|},
\]
and \(\beta(E)^2:=\inf_{z\in\R^n}{\cal B}_z(E)\).

The plan-internal display numbers `(2.1)`, `(2.2)`, ... refer to FJ-attack.md
(this directory's parent file).  Manuscript display numbers refer to
`FJ_quantitative_attempts.tex`.  These two numbering schemes occasionally
collide; we always write `(plan 2.X)` or `(ms 2.X)` to disambiguate when
context is not immediate.

## 1. Verification of the radial identities

**Plan (2.1).**  \(  {\cal B}_z(E)=P(E)-(n-1)I_z(E)  \).

This is proved in the manuscript as Proposition `prop:radial-GG`
(line 238) and is its display `(2.3)` `eq:osc-potential`.  It is valid
for every bounded finite-perimeter set, every \(z\in\R^n\), and every
dimension \(n\ge2\); the proof goes via a cut-off Gauss--Green argument
that handles the singularity of \(e_z\) at \(z\) and uses no
smoothness on \(\partial E\).  No volume normalisation is invoked.

**Plan (2.2).**  For \(|E|=\omega_n\),
\[
   {\cal B}_z(E)
     = D(E)+(n-1)\{I_z(B_1(z))-I_z(E)\}.
\]
This is proved in the manuscript on line 3701, display
`eq:B-def-plus-potential`, by combining Plan (2.1) with the identity
\((n-1)I_z(B_1(z))=P(B_1)\) (which is the case \(E=B_1(z)\) of
Plan (2.1), since \(\nu=e_z\) on \(\partial B_1(z)\) gives
\({\cal B}_z(B_1(z))=0\)).

Both terms on the right are nonnegative: \(D(E)\ge0\) is the ordinary
isoperimetric inequality; \(I_z(B_1(z))-I_z(E)\ge0\) is the
rearrangement statement that, among sets of equal volume, the unit
ball about \(z\) maximises the integral of the decreasing kernel
\(|x-z|^{-1}\) (bathtub/Hardy--Littlewood; reproved as the elementary
shell exchange in WP1 below).

**Plan (2.3).**  For \(|E|=\omega_n\),
\[
   |E\,\triangle\,B_1(z)|^2
   \le c_n\{I_z(B_1(z))-I_z(E)\}
   \le \frac{c_n}{n-1}{\cal B}_z(E).
\tag{plan 2.3}
\]
The second inequality is immediate from (plan 2.2) and \(D(E)\ge0\).
The first inequality is the same-centre bathtub comparison and is
**not** in the manuscript; it is the deliverable of WP1 (lemma C1).
A computable value of \(c_n\) is supplied there.

**Important.**  (plan 2.3) is much weaker than (FJ).  It controls
\(|E\,\triangle\,B_1(z)|\) at the same centre \(z\), not the
boundary-normal oscillation about \(z\).  It is used in WP1--WP3 only
as the bridge between \({\cal B}_z\) and the symmetric difference at
the same point.

## 2. Verification of scaling

For \(\lambda>0\) and \(a\in\R^n\), the substitution \(x=a+\lambda y\)
yields, on any finite-perimeter \(E\subset\R^n\):

| quantity | scaling under \(F=a+\lambda E\) |
|---|---|
| \(|F|\) | \(\lambda^n|E|\) |
| \(P(F)\) | \(\lambda^{n-1}P(E)\) |
| \(D(F)=P(F)-P(B_{\lambda\rho})\) when \(|E|=\omega_n\rho^n\) | \(\lambda^{n-1}D(E)\) |
| \(I_z(F)\) for \(z=a+\lambda w\) | \(\lambda^{n-1}I_w(E)\) |
| \({\cal B}_z(F)\) for \(z=a+\lambda w\) | \(\lambda^{n-1}{\cal B}_w(E)\) |
| \(\beta(F)^2\) | \(\lambda^{n-1}\beta(E)^2\) |
| \(|F\,\triangle\,B_{\lambda\rho}(z)|\) for \(z=a+\lambda w\) | \(\lambda^n|E\,\triangle\,B_\rho(w)|\) |

This is the manuscript's `lem:scaling` (line 313, displays
`eq:scale-D` and `eq:scale-beta`).  The remaining rows are direct
applications of the same change of variable.

**Consequence for WP0/WP1.**  At general unit volume normalisation
\(|E|=|B_\rho|\) (so \(\rho^n=|E|/\omega_n\)), (plan 2.3) reads
\[
   \rho^{-(n+1)}|E\,\triangle\,B_\rho(z)|^2
   \le c_n\{I_z(B_\rho(z))-I_z(E)\}
   \le \frac{c_n}{n-1}{\cal B}_z(E),
\]
which is what WP1.C1 calls its display \((C1)\).  The dimensional
constant \(c_n\) is unchanged: it is the same one that appears at
\(\rho=1\), because the relation
\[
   |F\triangle B_\rho(a+\lambda w)|^2 = \lambda^{2n}\,|E\triangle B_1(w)|^2,
   \qquad
   I_z(B_\rho(z))-I_z(F) = \lambda^{n-1}\{I_w(B_1(w))-I_w(E)\}
\]
forces the relative power \(\lambda^{2n-(n-1)}=\lambda^{n+1}\)
exactly.  Therefore no scaling error is hidden in the unit-volume
statement.

## 3. Large-deficit branch

The bound
\[
   D(E)\ge\eta\,P(B_\rho)\;\Longrightarrow\;\beta(E)^2\le2(1+\eta^{-1})D(E)
\]
is the manuscript's `lem:large` (line 337).  It is elementary
(\({\cal B}_z\le 2P\) since \(|\nu-e_z|^2\le4\)).  Throughout WP1--WP7
the symbol \(\delta_n\) denotes a dimensional small-deficit threshold;
the value of \(\delta_n\) becomes relevant only in WP3 and WP4 (lemmas
C3--C5) where C2's "explicit dimensional threshold" enters.  Outside
\(D(E)\le\delta_n P(B_1)\) the inequality (FJ) is automatic.

## 4. Permissible-input audit

The following inputs are permitted in WP1--WP7 without further
justification beyond a citation.

1. **The radial Gauss--Green identity (plan 2.1).**
   Manuscript `prop:radial-GG`.  Proof reproduced there is by cut-off.

2. **The radial-potential rearrangement inequality
   \(I_z(B_1(z))\ge I_z(E)\) for \(|E|=|B_1|\).**
   This is the layer-cake/bathtub identity for the decreasing radial
   kernel \(|x-z|^{-1}\).  Plan rule 5 explicitly permits it
   ("the elementary radial-potential rearrangement comparison may be
   reproved and used. It is not circular").  WP1 reproves it as the
   shell-exchange estimate (it is not stated as a lemma in the
   manuscript but its proof is one line; see WP1).

3. **The ordinary sharp quantitative isoperimetric inequality.**
   We use the **mass-transport effective form** of
   Figalli--Maggi--Pratelli (2010):
   \[
      \alpha(E)^2\le C_n^{\rm FMP}D(E),
      \qquad
      \alpha(E):=\inf_z\frac{|E\,\triangle\,B_1(z)|}{|B_1|}.
   \tag{8.3}\label{eq:fmp}
   \]
   Computability of \(C_n^{\rm FMP}\):  the constant arising in
   Figalli--Maggi--Pratelli, *Invent. Math.* 182 (2010), 167--211,
   Theorem 1.1, is given by an explicit finite composition of
   dimensional constants from
   - the Brenier-map existence and trace estimate
     (their Lemma 2.5 and Proposition 2.1),
   - the integration-by-parts argument leading to their (2.2),
   - the Sobolev/Poincar\'e constant used to deduce the
     symmetric-difference bound from the boundary integral.
   For \(n=2\) the constant in their proof is
   \(C_2^{\rm FMP}\le 331\); a generic dimensional formula
   \(C_n^{\rm FMP}\le C\sqrt n\,(2(n-1))^{n/2}\) is recorded in their
   Theorem 1.1 remark.  WP1--WP4 only use *existence and
   computability* of \(C_n^{\rm FMP}\); the explicit value is not
   exploited.

4. **Manuscript Section "The radial identity and elementary
   reductions" (lines 193--361).**  Provides Plan (2.1)--(2.2),
   scaling, and the large-deficit branch.

5. **Manuscript Section "Attempt IV", parts up through
   `cor:oriented-reduction-plane` (lines 3658--4236).**  Provides:
   - the fixed-centre identity (plan 2.1) restated as the working
     form `eq:fixed-centre-B`;
   - transverse Schwarz symmetrisation and its potential and
     perimeter monotonicity, with the discrepancy identity
     `eq:B-symmetrisation-direction` (plan 3.7);
   - meridian action of an axially symmetric set,
     `lem:meridian-action` (plan 3.8);
   - the centred one-bisection identity
     `lem:one-centred-bisection` (plan 3.1, 3.2);
   - the \((n-1)\) centred transverse reduction
     `thm:transverse-oriented-reduction` (plan 3.3, 3.4);
   - the planar orthogonal quadrisection
     `lem:orthogonal-quadrisection` and its consequence
     `cor:oriented-reduction-plane` (plan 3.5).

6. **The recent Figalli--van Hintum--Tiba work.**  Used only as
   structural motivation for the overlap-compatibility argument in
   WP3.C4; not as a black-box input.  All concrete estimates used in
   C4 must be re-proved here (see WP3).

7. **The Maldonado--Rold\'an-Pensado obstruction
   (arXiv:2404.01504).**  Used as a negative result: for \(n\ge 3\)
   the planar orthogonal-equipartition shortcut cannot be the route
   to full symmetry.

## 5. Non-circularity verification

Plan rule 3 forbids invoking the Fusco--Julin inequality, even for
reflected children or slices.  We verify:

- **No item of input list (1)--(7) above invokes (FJ).**  Items
  (1)--(2) are integration identities or rearrangement; (3) is the
  ordinary quantitative isoperimetric inequality, which is strictly
  weaker than (FJ); (4) reduces to (1)--(2); (5) is built only from
  the centred reflection identity (which uses Plan (2.1) and nothing
  about ball comparison); (6) and (7) are not used as proofs of
  oriented estimates.

- **Plan rule 4 is satisfied** by item (3).

- **Plan rule 5 is satisfied** by item (2).

- **The shell-exchange lemma** (WP1, C1) is independent of (FJ) and
  has its own self-contained derivation.

- **In WP3.C2 / C3**, the assumed input "\(G\) is close in measure to
  \(B_1(z)\)" is provided in our use by (plan 2.3), which is C1, not
  by any FJ statement.

We therefore confirm: no proposed input chain in WP1--WP7 transits
through Fusco--Julin.

## 6. Cross-reference of established results

The dependency graph for the manuscript inputs used in the new
programme is the following.

```
prop:radial-GG  ──┐
                  ├──► eq:fixed-centre-B  (plan 2.1 working form)
lem:scaling     ──┘
                                                          ▲
                                                          │
prop:radial-GG  ──► eq:B-def-plus-potential  (plan 2.2)   │
                                                          │
prop:radial-GG  ──► lem:potential-transverse  (plan 3.6 part 1)
                                                          │
lem:graph-geometry ──► lem:meridian-action  (plan 3.8)    │
                                                          │
prop:radial-GG  ──► lem:one-centred-bisection (plan 3.1)──┴► thm:transverse-oriented-reduction  (plan 3.3, 3.4)
                                                          │
                                                          ├► prop:orthant-oriented-reduction  (plan 3.5 hyp.)
                                                          │
                                                          └► cor:oriented-reduction-plane     (plan 3.5)
```

The new programme adds the following nodes:

```
   C1  (WP1)                                     [bathtub]
   C2  (WP1)                                     [centre near sym. flat]
   C3  (WP2)        ── go/no-go for high-dim
   C4  (WP3)
   C5  (WP4)
   OFR (WP4)
   TERM(WP4)
  (5.2)(WP4)
   SM  (WP6)
   MA  (WP7)
   SC  = SM + MA + induction over dimension
   (FJ)= OFR + TERM + SC
```

with arrows:
- WP1.C1 depends only on bathtub (and (plan 2.2)).
- WP1.C2 depends on C1, the unit-ball translation length bound,
  and the symmetry hypothesis from `thm:transverse-oriented-reduction`.
- WP2.C3 depends on C1, C2, and a quadratic expansion of \(I_z\).
- WP3.C4 depends on C1, C2 (one cut), and the
  two-orthogonal-cut comparison whose volumetric model is FMP Lemma 2.4.
- WP4.C5 combines C2--C4 with `lem:one-centred-bisection`.
- WP4.TERM combines C2--C3 with `lem:one-centred-bisection` and the
  last median (no second direction needed).
- WP4 then iterates and uses `lem:large` for the large-deficit branch.
- WP6.SM uses `lem:potential-transverse` and an inductive
  lower-dimensional SC.
- WP7.MA uses `lem:meridian-action` and the volume/translation modes.

## 7. Open items to be resolved by WP1--WP7

| symbol | statement | status before WP | location |
|---|---|---|---|
| C1 | bathtub (plan 2.3) | folklore, not yet displayed in ms | WP1 |
| C2 | centre near symmetry flat | folklore for one ball but not at the present sharp order | WP1 |
| C3 | quadratic recentering | open | WP2 |
| C4 | two-plane coherent centres | open | WP3 |
| C5 | common-centre oriented gluing | open | WP4 |
| OFR | oriented FMP reflection | open | WP4 |
| TERM | terminal one-plane reflection | open | WP4 (subsidiary to C2--C3) |
| (5.2) | iterated reduction to fully symmetric | follows from OFR+TERM | WP4 |
| SM | oriented slice-motion | open | WP6 |
| MA | meridian action closure | open | WP7 |
| TR | transport radialisation | open | WP-T (parallel) |
| P2 | planar symmetric closure | open | WP5 |

Computability is required of every constant.  We say a constant is
*computable* if it is a finite composition of:
- dimensional constants from the radial Gauss--Green identity (item
  (1) above; trivially explicit),
- the constant \(c_n\) in the bathtub estimate C1 (WP1),
- the explicit FMP transport constant \(C_n^{\rm FMP}\) of item (3),
- the geometric constants produced by the WP3 overlap argument
  (which is a finite computation in WP3),
- finite ratios of \(2^n\) and \(\binom{n}{k}\) introduced by the
  reflection iteration.

WP0 audit complete.
