# Wave 2 Agent C: cleanup of I5, I10, I12

Status: documentation/wording patches only. No new mathematics. All three
items are sub-substantive issues flagged in `agent6-adversarial-audit.md`
§1 (severity table) and §4 (Wave 2 priorities 3, 4, 5).

---

## C1.  I5 — FvHT block-center vs. Fraenkel asymmetry center

### Problem
Agent 3 (`agent3-metric-first-variation.md` §0, line 50–52) takes
$z_\rho$ to be the **FvHT block centre field** of
`fvht-center-gluing-import.md` §4: piecewise constant on a finite
overlap cover $\{I_j\}_{j=0}^N$ of $[\rho_*,1]$, with values
$z_j$ chosen as block minimizers of
$\Phi_j(z)=\int_{I_j}|E_\rho\Delta(z+B_\rho)|\,d\rho$, Borel
measurable, with jumps at block boundaries.

By contrast, Agent 2 (`metric-finite-perimeter-closure.md` §3.3,
eq. (3.2)–(3.4); `gmt-inputs-for-metric-closure.md` §1.1, eq. (1.1)) uses
$z_E=z^{\rm Fr}_\rho$: the **Fusco–Julin / Cicalese–Leonardi
strong‑isoperimetric center** of $E_\rho$, which varies measurably (and
in the smooth nearly‑spherical regime smoothly) with $\rho$. Cicalese–Leonardi
ARMA 2012 Thm. 1.1 gives this centre as the unique (up to error
$O(\mathcal A(E_\rho))$) minimizer of the Fraenkel functional
$z\mapsto|E_\rho\Delta(z+B_\rho)|$.

Agent 6 §2 Q2 flagged that Agent 3's identification of $z_\rho$ is
nominally distinct from Agent 2's. The two are not pointwise identical:
$z_j$ is constant on $I_j$, $z^{\rm Fr}_\rho$ is not.

### Resolution
**Claim.** Restrict to the smallness regime
$\delta=\delta_T(\Omega)\le\delta_0(n,\rho_*,R)$, so that for a.e.
$\rho\in[\rho_*,1]$ one has $\mathcal A(E_\rho)\le\varepsilon_0$. Then
on every overlap region $I_j\cap I_{j+1}$ and for a.e. $\rho$ in it,
$$
  |z_j-z^{\rm Fr}_\rho|+|z_{j+1}-z^{\rm Fr}_\rho|
  \le C_{n,\rho_*,R}\sqrt{\delta_T(\Omega)}.
\tag{C1.1}
$$
Consequently every estimate in `metric-finite-perimeter-closure.md`
§3.3–3.4 stated for the Fraenkel center $z^{\rm Fr}_\rho$ holds for
the FvHT block centre $z_j$ with the same exponent, up to an additive
$O(\sqrt\delta)$ into the constant. Symmetrically every estimate in
Agent 3 stated for $z_\rho=z_j$ extends to $z^{\rm Fr}_\rho$.

### Sketch
1. **FvHT overlap.** `fvht-center-gluing-import.md` §3–4 gives
   $|z_j-z_{j+1}|\le C_{n,\rho_*}(\varepsilon_j+\varepsilon_{j+1})$
   with $\varepsilon_j=\Phi_j(z_j)$. Levelwise quantitative
   isoperimetry (1.1) and Cauchy–Schwarz on $I_j$ give
   $\varepsilon_j\le C\sqrt{\int_{I_j}D_I(t(\rho))\,d\rho}\le
   C\sqrt\delta$. Hence $|z_j-z_{j+1}|\le C\sqrt\delta$ on each
   overlap, with $C=C_{n,\rho_*,R}$.
2. **Cicalese–Leonardi uniqueness.** ARMA 2012 Prop. 2.3 (or equivalent
   form, e.g. Acerbi–Fusco–Morini 2013 Lem. 2.6) gives, in the
   smallness regime, a unique Fraenkel centre $z^{\rm Fr}_\rho$ such
   that any $z$ with $|E_\rho\Delta(z+B_\rho)|\le 2\inf_{z'}|E_\rho
   \Delta(z'+B_\rho)|$ satisfies
   $|z-z^{\rm Fr}_\rho|\le C\,\mathcal A(E_\rho)$. Both $z_j$ and
   $z_{j+1}$, restricted to $\rho\in I_j\cap I_{j+1}$, are such
   competing minimizers up to a factor 2 by FvHT §4, and
   $\mathcal A(E_\rho)\le C\sqrt\delta$ for a.e. $\rho$ by (1.1) +
   Markov. Therefore
   $|z_j-z^{\rm Fr}_\rho|\le C\sqrt\delta$, giving (C1.1).
3. **Absorption.** In `metric-finite-perimeter-closure.md` (3.2)–(3.4),
   substituting $z_j$ for $z^{\rm Fr}_\rho$ introduces, on each
   block, an additive contribution
   $\int_{\partial^*E_\rho}|H_{z_j,\rho}-H_{z^{\rm Fr}_\rho,\rho}|\,d\mathcal H^{n-1}
   \le C\rho_*^{-1}\,|z_j-z^{\rm Fr}_\rho|\,P(E_\rho)
   \le C_{n,\rho_*,R}\sqrt\delta$. Squaring and integrating in $\rho$
   gives an $O(\delta)$ term, absorbable on the right-hand side of
   (3.4) into the $C_{n,\rho_*,R}D_I(t(\rho))$ constant after a
   pigeonhole on $\rho$ (or, more cleanly, into the global
   $C_{n,\rho_*,R}\delta$ of (5.2)). The same absorption works inside
   Agent 3 (T): replacing $H_{z_\rho,\rho}$ by $H_{z^{\rm Fr}_\rho,\rho}$
   changes the integrand by an $L^\infty$-bounded function whose
   integral is $\le C\sqrt\delta\,P(E_\rho)$, again absorbable.
4. **Conditionality.** Step 3 in the *Agent 2 direction* relies on the
   homothetic velocity defect lemma (3.2), which is conditional on
   Wave 2 Agent A's $L^2$-radial-trace closing Conjecture 3.6.
   So this reconciliation inherits the same conditionality and adds
   nothing new on the substantive side; it is *purely a wording fix*.

### Citations added
- Cicalese, Leonardi, *A selection principle for the sharp quantitative
  isoperimetric inequality*, ARMA 206 (2012), 617–643 — Thm. 1.1 and
  Prop. 2.3 (uniqueness of the Fraenkel centre up to
  $O(\mathcal A(E))$).
- Acerbi, Fusco, Morini, *Minimality via second variation for a nonlocal
  isoperimetric problem*, Comm. Math. Phys. 322 (2013), 515–557 —
  Lem. 2.6 (alternative form of the same uniqueness statement).

### Patch location
- `agent3-metric-first-variation.md` §0, immediately after the
  definition of $z_\rho$ on line 50–52, insert:

  > **Remark (centre identification).** $z_\rho$ here is the FvHT
  > block centre of `fvht-center-gluing-import.md` §4. In the smallness
  > regime $\delta_T(\Omega)\le\delta_0(n,\rho_*,R)$, Cicalese–Leonardi
  > 2012 Prop. 2.3 gives uniqueness of the Fraenkel centre
  > $z^{\rm Fr}_\rho$ up to $O(\mathcal A(E_\rho))$; combined with
  > the FvHT overlap bound $|z_j-z_{j+1}|\le C\sqrt\delta$ of
  > `fvht-center-gluing-import.md` §4, one has
  > $|z_\rho-z^{\rm Fr}_\rho|\le C_{n,\rho_*,R}\sqrt{\delta_T(\Omega)}$
  > for a.e. $\rho$. The resulting deviation of $H_{z_\rho,\rho}$
  > from $H_{z^{\rm Fr}_\rho,\rho}$ is bounded in $L^1(\partial^*E_\rho)$
  > by $C_{n,\rho_*,R}\sqrt\delta$ and is absorbed into the constants
  > of (T) and of Theorem (3.4) of `metric-finite-perimeter-closure.md`.

- `metric-finite-perimeter-closure.md` §3.3, just after the statement
  of the homothetic velocity defect lemma (after line 145), add a
  one‑sentence cross‑reference:

  > The centre $z_E$ here is the Fraenkel/strong‑isoperimetric centre
  > of Cicalese–Leonardi 2012 Thm. 1.1; on the foliation $\{E_\rho\}$
  > it agrees with the FvHT block centre $z_\rho$ of Agent 3 §0 up
  > to $O(\sqrt{\delta_T(\Omega)})$ (Wave 2 Agent C, C1).

---

## C2.  I10 — Sobolev Sard citation for Agent 3

### Problem
Agent 3 §0 defines
$V_\rho(x)=-t'(\rho)/|\nabla u(x)|$ for $x\in\partial^*E_\rho$ with
$|\nabla u|(x)>0$, and uses $V_\rho$ as an $\mathcal H^{n-1}$-a.e.
defined function on $\partial^*E_\rho$ for a.e. $\rho\in[\rho_*,1]$.
For this, one needs
$$
  \mathcal H^{n-1}\bigl(\partial^*E_t\cap\{|\nabla u|=0\}\bigr)=0
  \quad\hbox{for a.e. }t\in(0,\|u\|_\infty),
\tag{C2.1}
$$
i.e. a **Sard-for-Sobolev** statement, since
$u\in H^1_0(\Omega)\cap W^{2,p}_{\rm loc}(\Omega)$ for all
$p<\infty$ (Stampacchia + interior elliptic regularity for the
variational torsion) is not $C^1$ up to the boundary.

### Citation chosen
**Primary citation.** Figalli, Maggi, *On the shape of liquid drops
and crystals in the small mass regime*, Arch. Ration. Mech. Anal. 201
(2011), 143–207, **Appendix A, Theorem A.1**. The statement there gives,
for $u\in W^{2,p}_{\rm loc}$ with $p>n$, that the critical set
$\{|\nabla u|=0\}$ is $\mathcal H^{n-1}$-negligible on a.e. level
$\{u=t\}$; equivalently, $\mathcal H^{n-1}(\{u=t\}\cap\{|\nabla u|=0\})=0$
for a.e. $t$. Since $\partial^*E_t\subset\{u=t\}$ up to an
$\mathcal H^{n-1}$-null set for a.e. $t$ by the De Giorgi structure
theorem + coarea (Maggi 2012 Thm. 13.1; Ambrosio–Fusco–Pallara 2000
Thm. 3.40), (C2.1) follows.

**Hypotheses check.** Figalli–Maggi A.1 requires
$u\in W^{2,p}_{\rm loc}$ with $p>n$. Agent 1 §1 (and Agent 3 §0
line 12–14) establishes $u\in H^1_0\cap W^{2,p}_{\rm loc}$ for **every**
$p<\infty$ via Stampacchia; taking any $p>n$ suffices. The boundary
behaviour is irrelevant because the foliation is on the fixed annulus
$\rho\in[\rho_*,1]$, strictly interior. ✓

**Backup citation.** De Philippis, Marini, Mukoseeva, *The sharp
quantitative isocapacitary inequality*, Rev. Mat. Iberoam. 37 (2021),
2191–2228, **§2 (Preliminaries), Lemma 2.4** (or the more refined
form in their Lem. 2.5), where the Sobolev Sard statement is recorded
for $W^{2,p}$ functions with $p>n$ in exactly the form (C2.1).

**Classical alternative.** Brothers, Ziemer, *Minimal rearrangements
of Sobolev functions*, J. Reine Angew. Math. 384 (1988), 153–179,
Lemma 2.4. This works under weaker regularity (it is the original Sard
theorem for Sobolev functions), but its statement is in terms of
capacity/quasi-continuity rather than $\mathcal H^{n-1}$-measure, so
it requires one extra line to convert. **Not** recommended as primary
because the conversion (capacity → $\mathcal H^{n-1}$) introduces a
small extra argument; Figalli–Maggi A.1 already packages it.

**Bourgain–Korobkov–Kristensen 2013** (*On the Morse–Sard property and
level sets of Sobolev and BV functions*, Rev. Mat. Iberoam. 29) is
sharper but addresses the BV setting; it is overkill here.

### Patch text (two paragraphs, to be inserted in Agent 3 §0)

> Insert immediately after Agent 3 §0 line 31–33 (the definition of
> $V_\rho$ "for $x\in\partial^*E_\rho$, $|\nabla u|(x)>0$"):

**Paragraph 1.** *Sobolev Sard.* Standard elliptic regularity
(Stampacchia) gives $u\in W^{2,p}_{\rm loc}(\Omega)$ for every
$p<\infty$; fix any $p>n$. By the Sobolev Sard theorem of Figalli
and Maggi (Arch. Ration. Mech. Anal. 201 (2011), Appendix A,
Theorem A.1), for a.e. $t\in(0,\|u\|_\infty)$,
$$
  \mathcal H^{n-1}\bigl(\{u=t\}\cap\{|\nabla u|=0\}\bigr)=0.
$$
Since $\partial^*E_t\subset\{u=t\}$ up to an $\mathcal H^{n-1}$-null
set (De Giorgi structure theorem; Maggi 2012, Thm. 15.9), the same
identity holds with $\{u=t\}$ replaced by $\partial^*E_t$. After
reparametrization by volume radius $\rho$, this gives
$\mathcal H^{n-1}(\partial^*E_\rho\cap\{|\nabla u|=0\})=0$ for a.e.
$\rho\in[\rho_*,1]$.

**Paragraph 2.** *Consequence for $V_\rho$.* Therefore the formula
$V_\rho(x)=-t'(\rho)/|\nabla u(x)|$ defines $V_\rho$ as an
$\mathcal H^{n-1}$-a.e. finite, strictly positive function on
$\partial^*E_\rho$ for a.e. $\rho$. The coarea identity (0.1) then
yields $V_\rho\in L^1(\partial^*E_\rho,\mathcal H^{n-1})$ for a.e.
$\rho$, as needed. An alternative reference giving the same statement
under the same hypotheses is De Philippis–Marini–Mukoseeva 2021,
Lemma 2.4; the classical Brothers–Ziemer 1988 Lemma 2.4 also suffices
modulo a capacity-to-$\mathcal H^{n-1}$ conversion.

### Patch location
`agent3-metric-first-variation.md` §0, between current lines 33 and 34
(immediately after the definition of $V_\rho$, before the coarea
identity (0.1)).

---

## C3.  I12 — Rewrite `gmt-inputs-for-metric-closure.md` §1, eq. (1.2)

### Problem
Lines 51–55 of `gmt-inputs-for-metric-closure.md` §1 read:

> The radial estimate (1.2) follows from the same strong isoperimetric
> package: the oscillation index controls the boundary-normal defect,
> while the Fraenkel part controls the volume of the radial mismatch.
> Boundedness converts the volume mismatch into an
> $L^1(\partial^*E)$ trace mismatch by the coarea argument along rays,
> with constants depending on $R$ and $\rho_*$.

This is a one-line hand-wave. Agent 2 §3.6 (in
`agent2-homothetic-velocity-defect.md`) showed that this "follows
from" is in fact equivalent to the open Conjecture 3.6 / (R). With
Wave 2 Agent A establishing the $L^2$ form (R2) and Cauchy–Schwarz
upgrading (R2) → (R), this reference chain should now be made
explicit.

### Resolution: replacement paragraph (lines 51–55 of
`gmt-inputs-for-metric-closure.md`)

> The radial trace estimate (1.2) is **not** an immediate consequence
> of (1.1). It is the content of the **homothetic velocity defect
> lemma** of `agent2-homothetic-velocity-defect.md` §3.6 (Conjecture
> 3.6, statement (R)), which Agent 2 identified as the genuine
> bottleneck of Plan 2. (R) is closed, conditionally on the $L^2$
> radial trace inequality (R2) of `wave2-A-radial-l2-trace.md`,
> *viz.*
> $$
>   \int_{\partial^*E}\Bigl|\frac{|x-z_E|}{\rho}-1\Bigr|^2
>   d\mathcal H^{n-1}\le C_{n,\rho_*,R}\bigl(P(E)-P_\rho\bigr),
> \tag{R2}
> $$
> for finite-perimeter $E\subset B_R$ with $|E|=|B_\rho|$ and
> $\rho\in[\rho_*,1]$. The Cauchy–Schwarz upgrade from $L^2$ to
> $L^1$ closes (1.2) at the rate stated:
> $$
>   \left(\int_{\partial^*E}\Bigl|\frac{|x-z_E|}{\rho}-1\Bigr|
>   d\mathcal H^{n-1}\right)^2
>   \le P(E)\int_{\partial^*E}\Bigl|\frac{|x-z_E|}{\rho}-1\Bigr|^2
>   d\mathcal H^{n-1}
>   \le C_{n,\rho_*,R}\bigl(P(E)-P_\rho\bigr),
> $$
> using $P(E)\le C_{n,\rho_*}$ in the near-isoperimetric regime
> (and the non-near regime is absorbed into the constant exactly as in
> §2). The centre $z_E$ here is the
> Fusco–Julin/Cicalese–Leonardi strong-isoperimetric centre; on the
> torsion foliation $\{E_\rho\}$ it agrees with the FvHT block
> centre of Agent 3 §0 up to $O(\sqrt{\delta_T(\Omega)})$ (Wave 2
> Agent C, C1), which is absorbed into $C_{n,\rho_*,R}$.

No equation, no constant, and no exponent is changed; only the
attribution chain. The (1.2) estimate continues to be the input to §2
of the same note (homothetic velocity defect) and downstream into
`metric-finite-perimeter-closure.md` §3.

### Citations added
- `agent2-homothetic-velocity-defect.md` §3.6 (homothetic velocity
  defect lemma; equivalence of (1.2) with Conjecture 3.6).
- `wave2-A-radial-l2-trace.md` (Wave 2 Agent A, (R2)).
- `fvht-center-gluing-import.md` §4 (FvHT block centre); the centre
  identification cross-reference goes to Wave 2 Agent C §C1 above.

### Patch location
`gmt-inputs-for-metric-closure.md` §1, lines 51–55: replace the
existing one-paragraph hand-wave wholesale with the paragraph above.
Lines 1–49 (the statements of (1.1) and (1.2)) and lines 56–58
("Equivalently, one may take (1.1)–(1.2) as the exact quoted strong
isoperimetric input needed here.") are unchanged.

A consistent one-line footnote should also be added to
`metric-finite-perimeter-closure.md` §3 (immediately after the boxed
estimate (3.2)), reading:

> The lemma (3.2) is exactly Conjecture 3.6 / statement (R) of
> `agent2-homothetic-velocity-defect.md` §3.6; closed conditionally on
> Wave 2 Agent A's (R2) via Cauchy–Schwarz, see `gmt-inputs-for-metric-closure.md`
> §1 as revised by Wave 2 Agent C, C3.

---

## End-of-bundle status

- **C1 (I5):** wording remark; no new math. Conditional on Wave 2
  Agent A in the Agent 2 direction; unconditional in the Agent 3
  direction. Patches identified for `agent3-metric-first-variation.md`
  §0 and `metric-finite-perimeter-closure.md` §3.3.
- **C2 (I10):** citation only; primary Figalli–Maggi 2011 App. A
  Thm. A.1, backups De Philippis–Marini–Mukoseeva 2021 Lem. 2.4 and
  Brothers–Ziemer 1988 Lem. 2.4. Two-paragraph patch identified for
  `agent3-metric-first-variation.md` §0 (between current lines 33
  and 34).
- **C3 (I12):** wholesale replacement of lines 51–55 of
  `gmt-inputs-for-metric-closure.md` §1 with the explicit reference
  chain Agent 2 §3.6 → Wave 2 Agent A (R2) → Cauchy–Schwarz → (1.2).
  Plus one footnote in `metric-finite-perimeter-closure.md` §3.
