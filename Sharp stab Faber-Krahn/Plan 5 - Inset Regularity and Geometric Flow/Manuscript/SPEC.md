# Manuscript build spec — shared contract for all section agents

You are writing **one section** of a single research paper proving the sharp
planar quantitative Saint–Venant inequality
$$\mathcal A(\Omega)^2 \le C\,\delta_T(\Omega)$$
(absolute constant $C$, no regularity on $\Omega$), selection-free,
transport-free, symmetry-method-free. The reduction uses only the two
level deficits $D_H,D_I$; the finish is perturbative stability of nearly
spherical sets.

Read this entire file before writing. Then read the source files listed for
your section, **reconstruct and verify every step yourself**, and write a
fully self-contained section.

## Absolute rules

1. **Self-contained.** Every nonstandard claim must be proved in full, in
   this paper, with all constants explicit or explicitly absolute. It is
   **forbidden** to write "this is an adaptation of [X]", "as in [X]",
   "one can show", "it is well known that" for any step that is not a
   *verbatim* classical theorem. If you lean on a result, either (a) it is a
   classical published theorem, which you **state precisely** (full
   hypotheses + conclusion) and cite from `refs.bib`, or (b) you **prove it
   here, minutely**.
2. **Citation policy.** External inputs allowed only as precise quoted
   theorems with a `refs.bib` cite: GMT structure (De Giorgi/Federer —
   `AFP2000`,`Maggi2012`,`EvansGariepy2015`,`Federer1969`), the coarea
   formula, the (relative) isoperimetric inequality, the sharp quantitative
   isoperimetric inequality (`FMP2008`), elliptic regularity
   (`GilbargTrudinger2001`), Talenti's comparison (`Talenti1976`), Sard's
   theorem. Everything specific to this paper (level identity, annulus,
   fold content, cutting lemma, the assembly, and — per the no-adaptation
   rule — the nearly-spherical/Fuglede computation) must be **proved here**.
   Do **not** cite `BDV2015` for any *step we reprove*; you may cite it in
   prose for context/history only.
3. **Veracity.** Make at least **three passes**: (i) reconstruct the proof
   from scratch and check it line by line; (ii) hunt for hidden hypotheses,
   sign errors, constants that blow up, measure-zero/regular-value caveats,
   connectivity/orientation assumptions, and edge cases ($\delta_T\to0$
   asymptotics, degenerate slices); (iii) read your final LaTeX as an
   adversarial referee. If you find a genuine gap you cannot close, do
   **not** paper over it: mark it in the text with
   `\begin{remark}[Gap]...\end{remark}` and report it. Correctness over
   completeness.
4. **No preamble in section files.** Write only `\section{...}\label{...}`
   plus body. All macros/environments are in `_preamble.tex` (read it).
   Use the macros there; do not redefine them.
5. **Cross-references.** Use exactly the labels in the "Label interface"
   below for results other sections rely on, so that `\cref{...}` resolves.
   Refer to results in other sections by those labels with `\cref`.
6. **Style.** 11pt amsart, formal manuscript register, complete sentences,
   theorem–proof. Define every symbol at first use within your section
   (even if also global). Equations that are referenced get `\label`.

## Files

- Your output: `sections/<NN-name>.tex` (path given in your task). Overwrite.
- Shared (already created, do not edit): `main.tex`, `_preamble.tex`,
  `refs.bib`. If you need a classical reference not in `refs.bib`, put the
  `\cite{key}` in your text and list the full BibTeX entry in your final
  report; the orchestrator will add it. Do **not** edit `refs.bib`.
- Self-test before finishing (from the `Manuscript/` directory):
  ```
  printf '%s\n' '\documentclass[11pt,reqno]{amsart}' '\input{_preamble}' \
    '\begin{document}' '\input{sections/<NN-name>}' '\end{document}' > _t<NN>.tex
  pdflatex -interaction=nonstopmode -halt-on-error _t<NN>.tex
  ```
  Cross-refs to *other* sections will be undefined (`??`) — that is fine.
  There must be **no** `!`-errors. Then delete `_t<NN>.*` artifacts. Report
  the page count of your section.

## Canonical notation (use verbatim)

- $\Omega\subset\R^2$ open, $|\Omega|=\pi$ (normalisation fixed throughout).
- $u\in H^1_0(\Omega)$ torsion function: $-\Delta u=1$ in $\Omega$, $u=0$ on
  $\partial\Omega$; $T(\Omega)=\int_\Omega u=\int_\Omega|\nabla u|^2$;
  $m:=\max u$. Unit disc $B_1$, $T(B_1)=\pi/8$, $u_{B_1}=(1-|x|^2)/4$.
- **Saint–Venant deficit** (absolute, area-normalised):
  $\dT:=\dT(\Omega):=\tfrac\pi8-T(\Omega)\ge0$.
- **Scale-invariant relative deficit** of a finite-measure set $E$:
  $\dstar(E):=\dfrac{T(B_E)-T(E)}{T(B_E)}\in[0,1)$, $B_E$ any equal-area
  ball, $T(B_E)=|E|^2/(8\pi)$. Note $\dstar(\Omega)=\tfrac8\pi\dT$.
- **Fraenkel asymmetry** $\AF(E):=\min_{x_0}\dfrac{|E\triangle
  B(x_0,r_E)|}{|E|}$, $r_E=\sqrt{|E|/\pi}$.
- $\mu(v):=|\{u>v\}|$, $\Per(v):=P(\{u>v\})$ (perimeter), for $v\in(0,m)$.
- **Two level deficits:** $D_H(v):=\mu(v)(-\mu'(v))-\Per(v)^2$ and
  $D_I(v):=\Per(v)^2-4\pi\mu(v)$.
- Disc profile $\mu_B(v):=\pi(1-4v)_+$ (distribution function of $u_{B_1}$).
- Flux/coarea: $\int_{\{u=v\}}|\nabla u|\,d\HH^1=\mu(v)$,
  $-\mu'(v)=\int_{\{u=v\}}|\nabla u|^{-1}\,d\HH^1$ (a.e. regular $v$).
- **Inset:** $\hat v\in(\tau,2\tau)$ a good regular level, $\tau:=\sqrt\dT$;
  $\Etil$ = the connected component of $\{u>\hat v\}$ of largest measure;
  $\mu_E:=|\Etil|$, $\hat r:=\sqrt{\mu_E/\pi}$,
  $\diso:=\diso(\Etil)=\Per(\Etil)/(2\sqrt{\pi\mu_E})-1$,
  $\Exc:=\Per(\Etil)-2\pi\hat r=2\pi\hat r\,\diso$,
  $a:=|\Etil\triangle B_{\hat r}(z)|$ (optimal/annulus centre $z$).
- **Annulus:** $B_{\rho_i}(z)\subset\Etil\subset B_{\rho_e}(z)$,
  $\eta:=\rho_e-\rho_i$, $\rho_i\le\hat r\le\rho_e$.
- **Crossings:** for $\theta\in S^1$, $M(\theta)=\HH^0(\partial\Etil\cap
  \{z+\rho e^{i\theta}:\rho>0\})$ (ray); $N(\rho)=\HH^0(\partial\Etil\cap
  \partial B_\rho(z))$ (circle).
- **Graph defect** $\gd(E):=\inf_{\rho:S^1\to(0,\infty)}|E\triangle\{z+r\omega:
  r<\rho(\omega)\}|$.
- $\nu$ outward unit normal on the reduced boundary, $e_r=(x-z)/|x-z|$,
  $\nu_r=\nu\cdot e_r$.
- Absolute constants are denoted $C$ (value may change line to line) or
  named ($C_G,\eta_G,C_{\mathrm F},A_0,\delta_\star$). State dependence
  explicitly; "absolute" means independent of $\Omega$.

## Label interface (fixed — produce these exactly)

- §2: `thm:fmp` (FMP), `thm:coarea`, `thm:isoperimetric`,
  `thm:rel-isoperimetric`, `lem:dist-deriv` (differentiation of $\mu$),
  `thm:torsion-reg` (smoothness/analyticity of $u$),
  `thm:interior-est` (interior gradient/Hessian),
  `thm:sard`, `lem:regular-values`.
- §3: `def:deficits`, `lem:nonneg`, `thm:level-identity`
  (eq:`eq:level-identity`), `thm:talenti` (eq:`eq:talenti`),
  `lem:profile` (eq:`eq:profile`), `lem:muprime` ($-\mu'\ge4\pi$).
- §4: `lem:noholes`, `lem:transfer` (eq:`eq:transfer`), `lem:level`
  (eq:`eq:goodlevel`), `lem:close` (eq:`eq:close`), `lem:spill`
  (eq:`eq:spill`); define $\Etil$ here (`def:inset`).
- §5: `lem:angular-coarea` (eq:`eq:angular-coarea`), `lem:Ncross`,
  `thm:annulus` (eq:`eq:annulus`).
- §6: `lem:two-flux` (eq:`eq:two-flux`), `prop:fold`
  (eq:`eq:foldsharp`), `cor:gd` (eq:`eq:gd`), `prop:realization`
  (continuous graph $G$; eq:`eq:realization`).
- §7: `lem:torsion-stab` (eq:`eq:torsion-stab`), `lem:cutdeficit`.
- §8: `thm:graphG` (eq:`eq:graphG`) with constants $\eta_G,C_G$; supporting
  `lem:fuglede`, `lem:harmonic-coercivity` as needed.
- §9: `thm:reduction`, `thm:main` (eq:`eq:main`).

## The argument in one paragraph (so each agent sees the whole)

Pick the inset level $\hat v\sim\sqrt\dT$ low (near $\partial\Omega$):
closeness $|\Omega\triangle\Etil|=\pi-\mu(\hat v)\sim\sqrt\dT$ is carried by
the *level* (Talenti + the profile identity $\int_0^{1/4}(\mu_B-\mu)=\dT$),
while the torsion deficit transfers, $\dstar(\Etil)\lesssim\dT$, as a tail
of the level identity $\int_0^m(D_H+D_I)=4\pi\dT$. At a good level
(averaging the identity) $D_I(\hat v)\lesssim\dT/\tau$, so the inset is
trapped in an annulus of width $\eta\lesssim\dT^{1/8}$ — an *absolute*
small amplitude, all the graph theorem needs. The fold content (obstruction
to being a graph about $z$) is bounded with **no FMP square-root loss** via
the point-source flux identities and the cancellation
$|I_\Etil-2\pi\hat r|\le Ca\eta$ (subtract the constant $1/\hat r$; the
symmetric difference lives in the $\eta$-annulus), giving
$\gd(\Etil)\lesssim\dT/\tau$. Cutting the (low-torsion) caps to make a
genuine radial graph $G$ **lowers** $\dstar$ (the equal-area ball shrinks
faster than torsion is lost). Thus $G$ has amplitude $\le\eta_G$,
$\dstar(G)\lesssim\dT$, $|\Omega\triangle G|\lesssim\sqrt\dT$; the
perturbative nearly-spherical bound gives $\AF(G)^2\le C_G\dstar(G)$, and the
triangle inequality transfers it to $\AF(\Omega)^2\lesssim\dT$. Optimum
$\tau=\sqrt\dT$ balances closeness against graph defect.

## Per-section mandates and sources

Source root S = `/home/joao-pedro-ramos/Math projects/Sharp stab Faber-Krahn/Plan 5 - Inset Regularity and Geometric Flow`.

### 01-intro  (§1 Introduction)
No theorems to prove. Write: the problem (torsion, Saint–Venant/Faber–Krahn,
$\AF^2\lesssim\dT$ sharp), brief history (Saint–Venant conjecture &
Pólya–Szegő `PolyaSzego1951`; Talenti `Talenti1976`; sharp quantitative
isoperimetry `FMP2008`; quantitative Faber–Krahn/Saint–Venant `BDV2015`,
`BrascoPratelli2012`, survey `BrascoDePhilippis2017`), the **main theorem**
(stated as `thm:main` will appear in §9 — here state it as the headline
result, referencing `\cref{thm:main}`), what is new (selection-free,
transport-free, only $D_H,D_I$; the two sharp ingredients), and an
"Organization of the paper" paragraph mapping sections. Be accurate about
prior art; do not overclaim. ~1.5–2.5 pages.

### 02-prelim  (§2 Preliminaries)
The *imported toolbox*, each as a precisely stated, cited classical theorem
(no proofs except trivial corollaries): sets of finite perimeter, reduced
& essential boundary, De Giorgi/Federer structure (`AFP2000`,`Maggi2012`);
the coarea formula `thm:coarea`; differentiation of the distribution
function `lem:dist-deriv`; planar isoperimetric `thm:isoperimetric` and
relative isoperimetric in a disc `thm:rel-isoperimetric`; the sharp
quantitative isoperimetric inequality `thm:fmp` (state `FMP2008` in the
planar additive form $\AF(E)\le C_{\mathrm F}\diso(E)^{1/2}$, give the
constant's status); interior smoothness/analyticity of $u$ `thm:torsion-reg`
and interior gradient/Hessian estimates `thm:interior-est`
(`GilbargTrudinger2001`); Sard `thm:sard` and "a.e. level is regular"
`lem:regular-values`. Mine: `S/Blocks/Inset Sections/sec_preliminaries.tex`.
Keep tight but complete. ~3–4 pages.

### 03-identity  (§3 The level deficits and the volume profile)
Prove in full: `def:deficits`; non-negativity `lem:nonneg` ($D_H\ge0$ by
Cauchy–Schwarz with the flux/coarea identities; $D_I\ge0$ isoperimetric);
the **level-set deficit identity** `thm:level-identity`:
$\int_0^m(D_H+D_I)\,dv=4\pi\dT$ (eq:`eq:level-identity`); its
scale-invariance (degree-4 homogeneity), used later for the inset.
`thm:talenti` (Talenti comparison $\mu\le\mu_B$, cite `Talenti1976` for the
comparison principle but prove the consequence we use); the **profile
identity** `lem:profile`: $\int_0^{1/4}(\mu_B-\mu)\,dv=\dT$ with $\mu_B-\mu\ge0$,
hence $m\le\tfrac14$; and `lem:muprime`: $-\mu'(v)\ge4\pi$ a.e. Mine:
`S/Blocks/Inset Sections/sec_core.tex` (`thm:identity`,`thm:talenti`,
`cor:profile`). Verify the constant $4\pi$ and the identity derivation
independently (coarea + integration by parts). ~3–4 pages.

### 04-inset  (§4 The inset: regularity, deficit transfer, level selection)
Prove: for regular $v$, $\{u>v\}$ is a finite-perimeter set with the flux
identities, and a connected component has **no interior holes** `lem:noholes`
(superharmonicity + minimum principle). **Deficit transfer** `lem:transfer`:
$\dstar(\{u>v\})\le(\pi^2/\mu(v)^2)\dstar(\Omega)$ (the torsion function of
$\{u>v\}$ is $u-v$; tail of `thm:level-identity` in scale-invariant form).
**Good level** `lem:level`: $\exists$ regular $\hat v\in(\tau,2\tau)$ with
$D_H(\hat v)+D_I(\hat v)\le A_0\dT/\tau$ and $\mu_B(\hat v)-\mu(\hat v)\le
A_0\dT/\tau$ (Chebyshev on `thm:level-identity` and `lem:profile` + Sard).
**Closeness** `lem:close`: $|\Omega\triangle\{u>\hat v\}|=\pi-\mu(\hat v)\le
8\pi\tau+A_0\dT/\tau$. **Spillover** `lem:spill`: the non-largest components
of $\{u>\hat v\}$ have total measure $\le D_I(\hat v)^2/(16\pi^3)$
(multi-component isoperimetric: $D_I\ge8\pi\sum_{i<j}\sqrt{A_iA_j}$); define
$\Etil$ = largest component (`def:inset`), record
$\diso(\Etil)\le D_I(\hat v)/(8\pi\mu_E)\le C\dT/\tau$ and that $\Etil$ is
connected, hole-free, $|\Omega\triangle\Etil|\le C\sqrt\dT$ (once
$\tau=\sqrt\dT$; but keep $\tau$ symbolic, optimise in §9). Mine:
`S/Blocks/Inset Sections/sec_core.tex` (`prop:noholes`,`prop:goodlevel`),
`S/Core/sharp_via_graph_inset.tex` (§3: `lem:transfer`,`lem:level`,
`lem:close`,`lem:spill`). Check the spillover constant and the $A_1\ge\pi/4$
step. ~3–4 pages.

### 05-annulus  (§5 The trapping annulus)
Prove `thm:annulus`: a connected hole-free finite-perimeter set $E$ with
isoperimetric deficit $\diso$, excess $\Exc=2\pi\hat r\diso$, and ball-distance
$a=|E\triangle B_{\hat r}(z)|$ is trapped, $B_{\rho_i}(z)\subset E\subset
B_{\rho_e}(z)$ with $\eta=\rho_e-\rho_i\le C(\Exc+a)^{1/2}$, $C$ absolute,
no $C^2$/regularity. Route (mine, `S/Blocks/Inset Sections/sec_density_annulus.tex`,
`lem:Ptheta`,`lem:Ncross`,`thm:perim-annulus`): the angular-perimeter coarea
identity `lem:angular-coarea` $\int_{\partial E}|\nu_\theta|=\int_0^\infty
N(\rho)\,d\rho$; $N(\rho)\ge2$ for $\rho\in(\rho_i,\rho_e)$ `lem:Ncross`
(connectedness + no holes ⇒ the boundary meets every intermediate circle at
least twice); Cauchy–Schwarz $P_\theta^2\le2P(P-P_r)$ and the radial-profile
bound $P-P_r\le\Exc+Ca$. **This is original to this project — scrutinise it
hardest** (the definitions of $\rho_i,\rho_e$, why $N\ge2$, the
Cauchy–Schwarz step, and the constant). If a step needs $E$ open / a good
representative, say so. ~4–5 pages.

### 06-fold  (§6 Fold content and the radial graph)
Prove `lem:two-flux` (point-source identities, eq:`eq:two-flux`):
$\int_{\partial E}|\nu_r|/|x-z|=\int_{S^1}M\,d\theta$,
$\int_{\partial E}\nu_r/|x-z|=2\pi$,
$\int_{\partial E}\nu_r=\int_E|x-z|^{-1}=:I_E$ (coarea on the angle for the
first; divergence theorem for the field $e_r$ resp. $(x-z)/|x-z|^2$ — handle
the singularity at $z$ by excising $B_\eps(z)$). **Sharp fold content**
`prop:fold` (eq:`eq:foldsharp`):
$\int_{S^1}(M-1)\,d\theta\le(\Exc+a\eta/(\rho_i\hat r))/\rho_i\le C(\Exc+a\eta)$,
where the crux is $|I_E-2\pi\hat r|\le a\eta/(\rho_i\hat r)$ obtained by
subtracting the constant $1/\hat r$ (legitimate since $|E|=|B_{\hat r}(z)|$)
and confining $E\triangle B_{\hat r}(z)$ to the $\eta$-annulus. **Graph
defect** `cor:gd` (eq:`eq:gd`): $\gd(E)\le\rho_e\eta\int m\,d\theta\le
C\eta(\Exc+a\eta)$ (cut the caps; per-ray cap mass $\le\rho_e\eta$).
**Realization** `prop:realization`: a continuous (indeed Lipschitz) radial
profile $\rho$ with $|E\triangle\{r<\rho\}|\le\gd(E)+C\sigma$ and amplitude
$\|\rho-\hat r\|_\infty\le\eta$ (mollify the BV core profile at angular scale
$\sigma$; $\mathrm{TV}\le P(E)/\rho_i$). Mine:
`S/Blocks/Inset Sections/sec_graph.tex` and `S/Core/sharp_via_graph_inset.tex`
(§4–5). Verify the singularity handling in `lem:two-flux` and the constant
subtraction in `prop:fold`. ~4–5 pages.

### 07-cut  (§7 Cutting the caps lowers the deficit)
Prove `lem:torsion-stab` (eq:`eq:torsion-stab`): if $B_{\rho_i}(z)\subset
E\cap F$, $E\cup F\subset B_{\rho_e}(z)$, $|E\triangle F|=m$, then
$|T(E)-T(F)|\le3\tilde\eta\,m$, $\tilde\eta=\tfrac14(\rho_e^2-\rho_i^2)$
(Green-function double integral $T(D)=\iint G_D$, monotonicity
$G_{E\cap F}\le G_{E\cup F}$, barrier $u_{E\cup F}\le\tilde\eta$ on the
collar). **Cutting lowers $\dstar$** `lem:cutdeficit`: if $B_{\rho_i}(z)
\subset G\subset E\subset B_{\rho_e}(z)$, $E\setminus G$ in the collar, and
$3\tilde\eta\le T(E)/|E|$, then $\dstar(G)\le\dstar(E)$. **Get the sign
right**: expand $T(1-g/V)^2=T-2Tg/V+Tg^2/V^2$ and use $g\le V$ so
$2T/V-Tg/V^2\ge T/V\ge3\tilde\eta$. Mine:
`S/Core/selection_free_route.tex` (`lem:torsion-stab`),
`S/Core/sharp_via_graph_inset.tex` (`lem:cutdeficit`). Double-check the
Green-function representation $T(D)=\iint_{D\times D}G_D$ and the barrier
constant. ~2–3 pages.

### 08-nearly  (§8 Perturbative stability of nearly spherical sets)
Prove, **fully and self-containedly** (Fuglede-type for the torsion
functional — do NOT invoke `BDV2015`), `thm:graphG` (eq:`eq:graphG`): there
are absolute $\eta_G>0$ and $C_G$ such that any radial graph
$G=\{z+r\omega:r<\hat r_G(1+\varphi(\omega))\}$, $\varphi\in
\mathrm{Lip}(S^1)$ (or $W^{1,2}$), $\|\varphi\|_\infty\le\eta_G$, $|G|$
fixed, satisfies $\AF(G)^2\le C_G\,\dstar(G)$. Plan: (a) reduce to
$\hat r_G=1$, $|G|=\pi$ by scaling ($\dstar,\AF$ invariant); (b) absorb the
volume constraint $\int(2\varphi+\varphi^2)=0$ and translate so the
barycentre kills the first Fourier mode (or carry the mode-1 term and use
that asymmetry is the mode-1 amplitude); (c) compute the torsion deficit to
second order in $\varphi$ via the Dirichlet/Pólya–Szegő variational
characterisation $T(G)=\max\{2\int_G\phi-\int_G|\nabla\phi|^2\}$ and a
harmonic/explicit comparison field, obtaining a lower bound
$\dstar(G)\ge c\sum_{k\ge2}(\text{coercive})|\hat\varphi_k|^2-(\text{h.o.t.})$;
(d) bound $\AF(G)^2\le C\|\varphi\|_{L^2}^2$ and conclude by coercivity of
the quadratic form on the mean-zero, mode-1-free part, with $\eta_G$ chosen
so the cubic remainder is absorbed. Provide explicit (or explicitly
absolute) $\eta_G,C_G$. Mine for orientation only:
`S/Core/selection_free_route.tex` (Module (G)),
`S/../Plan 2 - Level Set Metric Route/Core/Assembled Manuscript/plan1_nearly_spherical.tex`,
`Fuglede1989`, `BrascoPratelli2012`. **This is the hardest section; budget
the most verification.** If the cleanest honest route is to quote a single
published *perturbative* (non-selection) theorem verbatim, you may do so as
a clearly-stated cited theorem — but the no-adaptation rule means you must
still verify our $G$ meets its hypotheses exactly and reprove any gap. ~5–7
pages.

### 09-main  (§9 Proof of the main theorem)
Assemble. `thm:reduction`: for $\dT\le\delta_\star$ and $\tau=\sqrt\dT$
there is a continuous radial graph $G$ with (i) amplitude $\le C\dT^{1/8}\le
\eta_G$, (ii) $\dstar(G)\le C\dstar(\Omega)$, (iii) $|\Omega\triangle G|\le
C\sqrt\dT$ — chaining §§4–7 with the scales $\diso\sim\dT/\tau$,
$a\sim(\dT/\tau)^{1/2}$, $\eta\sim(\dT/\tau)^{1/4}$, $\gd\sim\dT/\tau$, and
the optimisation $\tau=\sqrt\dT$. Then `thm:main`: $\AF(\Omega)^2\le C\dT$
via `thm:graphG` and the triangle inequality (handle area/barycentre
normalisation and the $\dT\ge\delta_\star$ regime trivially). Close with a
remark on what was and was not used (no selection/transport/symmetry
method) and the role of the two sharp ingredients. Mine:
`S/Core/sharp_via_graph_inset.tex` (`thm:reduction`,`thm:main`). Re-derive
every scale and check the optimisation. ~2–3 pages.

## Final report (every agent)

End with: section page count; the list of results you proved (by label);
external theorems you cited (keys) and any new BibTeX entries needed;
**every gap/concern you found and how you resolved it (or that it remains)**;
and any change you'd request of an adjacent section's interface.
