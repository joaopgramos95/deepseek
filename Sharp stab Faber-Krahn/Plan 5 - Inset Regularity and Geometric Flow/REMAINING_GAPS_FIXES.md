# Suggested Fixes for Remaining Manuscript Gaps

This note records concrete repair strategies for the explicit `Gap` remarks
currently left in `Manuscript/sections`.  The goal is to turn each gap into a
bounded section task without changing the overall route more than necessary.

## 1. Global exterior connectedness of the inset

Location: `Manuscript/sections/05-annulus.tex`, `gap:global-noholes`.

Problem: `lem:noholes` in Section 4 excludes complementary components compactly
contained in `\Omega`, but the annulus proof needs the stronger statement that
`\mathbb R^2\setminus\overline{\widetilde E}` is connected.  A bounded
complementary component may touch `\partial\Omega` and evade the current
minimum-principle proof.

Recommended fix: fill the holes before applying the annulus theorem.

Define `E^h` as the union of `\widetilde E` with all bounded connected
components of `\mathbb R^2\setminus\overline{\widetilde E}`.  Then prove:

1. `E^h` is bounded, connected, and has connected exterior.
2. `|E^h|=|\widetilde E|+H`, where `H` is the filled area, and
   `P(E^h)\le P(\widetilde E)`.
3. The filled area `H` is controlled by the level spill/deficit or by
   `|\Omega\triangle\widetilde E|`, at the required `O(\sqrt{\delta_T})`
   scale.
4. The torsion deficit transfer survives replacing `\widetilde E` by `E^h`.
   Since `E^h\supset\widetilde E`, torsion increases, but the comparison ball
   also grows.  Prove a direct estimate
   `\delta_*(E^h)\le C\delta_*(\widetilde E)+C H`.
5. Run the annulus and fold arguments on `E^h`, then transfer the final graph
   back to `\widetilde E` with an extra `H` error.

Fallback fix: if hole filling creates too much bookkeeping, strengthen
`lem:noholes` by proving that any bounded exterior component touching
`\partial\Omega` is polar/capacity-zero for the torsion representative.  This
would use fine topology and is likely less elementary than filling.

## 2. BV-to-continuous graph realisation

Location: `Manuscript/sections/06-fold.tex`, `gap:realization`.

Problem: the current proof tries to show the innermost crossing profile
`\rho_0=r_1` has bounded variation by comparing
`\{\rho_0>\rho\}` to circular slices.  That comparison is false on rays with
caps: a cap may contain radius `\rho` even when `\rho_0<\rho`.

Recommended fix: avoid proving `BV` regularity of the innermost profile.

Use a measurable graph first, and do not mollify it.  The nearly-spherical
theorem in Section 8 only needs a radial graph with small amplitude and no
slope control; it can be stated for measurable profiles with
`L^\infty` amplitude and proved by approximation from inside/outside.

Concrete steps:

1. Define the measurable core graph
   `G_0={z+r\omega:0<r<\rho_0(\omega)}` using the slice profile.
2. Prove `G_0` is measurable, star-shaped, contains `B_{\rho_i}(z)`, lies in
   `B_{\rho_e}(z)`, and satisfies
   `|\widetilde E\triangle G_0|\le C\eta(\mathrm{Exc}+a\eta)`.
3. Replace `prop:realization` by a lower-semicontinuous/open approximation
   lemma: for every `\epsilon>0`, there is an open radial graph `G_\epsilon`
   with measurable profile in `[\rho_i,\rho_e]` such that
   `|G_\epsilon\triangle G_0|\le\epsilon`.
4. Extend `thm:graphG` from Lipschitz profiles to measurable profiles by
   approximating the profile in `L^2` and using Mosco convergence/domain
   monotonicity for torsion.  This is natural because the Section 8 proof is
   slope-free.

Alternative fix: define a different profile from the circular slices, for
example a monotone rearranged star-shaped core whose level sets are the
essential angular interiors of `E\cap\partial B_\rho`; this may give a genuine
BV profile, but it is more invasive.

## 3. Boundary-layer torsion stability and cap cutting

Location: `Manuscript/sections/07-cut.tex`, `gap:torsion-stab`.

Problem: `|E\triangle F|` alone cannot control torsion on arbitrary open sets:
removing a zero-area positive-capacity slit can change `H^1_0` and torsion.
The current Green-kernel argument is also too weak for rough domains.

Recommended fix: restrict the cutting lemma to radial graph cuts and prove it
variationally, not through rough-domain Green kernels.

For `G_0\subset E` where `E\setminus G_0` is a union of radial caps in the
annulus, prove directly that the torsion loss is bounded by the torsion
function of `E` on the cap set:

1. Use the variational characterization
   `T(D)=max_{v\in H^1_0(D)}(2\int_D v-\int_D|\nabla v|^2)`.
2. Construct an admissible competitor on `G_0` by truncating the torsion
   function `u_E` with a radial cutoff that vanishes on the newly exposed
   radial cap boundaries.
3. Since all cap material lies in
   `\{\rho_i<|x-z|<\rho_e\}`, use the disc barrier
   `u_E(x)\le(\rho_e^2-|x-z|^2)/4\le\tilde\eta`.
4. Estimate the gradient cost of the cutoff in terms of cap geometry.  The
   fold-content bound gives the total angular size of cap rays; this should
   replace the false pure-measure bound.
5. Prove the needed conclusion directly:
   `T(E)-T(G_0)\le C\tilde\eta |E\setminus G_0|`
   for these cap cuts, possibly with an additional
   `C\eta\,\mathrm{fold}` term still `O(\delta_T)`.
6. Then repeat the sign-critical algebra in `lem:cutdeficit`.

If a general lemma is desired, add a capacitary hypothesis such as
`H^1_0(E\cap F)=H^1_0(E)\cap H^1_0(F)` and no positive-capacity cracks in the
collar.  But the radial-cap-specific lemma is the safer route.

## 4. Barycentre normalization for the graph theorem

Location: `Manuscript/sections/09-main.tex`, `gap:barycentre`.

Problem: `thm:graphG` assumes the graph centre is the barycentre.  The graph
constructed in Section 6 is centred at the annulus/FMP centre `z`.  Recentring
at the barycentre may destroy single-valued radiality without a slope bound.

Recommended fix: modify Section 8 to handle the translation mode directly.

Do not require the graph centre to be the barycentre.  Instead:

1. Keep the mode-1 Fourier coefficients in the perturbative computation.
2. Use Fraenkel asymmetry modulo translations:
   choose a comparison disc centre shifted by the first Fourier mode.
3. Prove an estimate of the form
   `\mathcal A(G)^2\le C(\|P_{\ge2}\varphi\|_2^2 + \text{higher order})`.
   The `P_1` component corresponds to translating the disc and should not need
   coercivity from the torsion deficit.
4. In the energy lower bound, only coerce modes `k\ge2`, exactly as the
   current Steklov argument already does.
5. Replace `lem:modes` by:
   - the volume constraint controls `P_0\varphi=O(\|\varphi\|_2^2)`;
   - `P_1\varphi` is left free;
   - asymmetry after optimizing the disc centre is controlled by
     `\|P_{\ge2}\varphi\|_2 + O(\|\varphi\|_2^2)`.

This avoids proving star-shapedness under recentering and matches the
selection-free/no-slope philosophy of the paper.

Fallback fix: prove a star-centre stability lemma.  If a graph satisfies
`B_{\rho_i}(z)\subset G\subset B_{\rho_e}(z)` with
`\rho_e-\rho_i=\eta\ll\rho_i`, and if `|b-z|\le c\rho_i`, then `G` is
star-shaped with respect to `b` and has amplitude `O(\eta+|b-z|)`.  This is
plausible for genuinely star-shaped sets containing a large ball, but proving
single crossing from the shifted centre without slope control is delicate.
The mode-1 route is cleaner.

## Suggested repair order

1. Fix Section 8 by removing the barycentre hypothesis and handling mode 1.
   This is self-contained and likely the cleanest win.
2. Replace `prop:realization` by a measurable/open approximation version and
   extend `thm:graphG` to measurable profiles.
3. Replace the general cap-cutting lemma with a radial-cap-specific variational
   lemma.
4. Decide whether to fill holes or prove global exterior connectedness.  Hole
   filling is probably the most robust route.

After each repair, rerun:

```bash
cd Manuscript
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Then rerun a mathematical audit specifically on the repaired section and its
two adjacent dependencies.
