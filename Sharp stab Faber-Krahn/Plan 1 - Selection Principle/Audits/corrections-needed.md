# Corrections Needed for the Claimed Theorem

This note records the places where the current Plan 1 writeup overstates what is actually proved.

## 1. Tone down the global claim

The following wording is too strong:

- `README.md`: the route is described as “end-to-end and rigorous”.
- `fixed-domain-bernoulli-expansion.md/.tex`: the Bernoulli spectral closure is presented as unconditional.
- `faber-krahn-transfer.md`: the final Faber--Krahn theorem is stated as proved for every open set in the small-quotient regime.

The safer status is:

- the selection step is quantitative;
- graph entry is reduced to a regularity threshold;
- the Bernoulli spectral closure is still conditional unless the missing tame expansion is fully justified;
- the BDV nearly spherical second variation remains the reliable closure route.

## 2. Do not treat the normalized selected set as automatically admissible for the Bernoulli law

The selection proof constructs a minimizer `U_*` and then volume-normalizes it to `\widetilde\Omega`.

What needs to be fixed:

- either prove that the Bernoulli/Euler--Lagrange law survives the normalization in the form used later;
- or apply the spectral closure only before normalization, with a separate argument that transfers the conclusion back.

Right now the normalization step is asserted to be harmless, but the proof does not write out the transformed law.

## 3. Separate `C^{1,\gamma}` graph entry from the `C^{2,\gamma}` input needed later

`graph-entry-closure.md` gives a global graph with small `C^{1,\gamma}` norm.

The later spectral argument assumes a small `C^{2,\gamma}` graph regime.

Correction needed:

- add a real bootstrap argument that upgrades the graph regularity to `C^{2,\gamma}`;
- or weaken the spectral closure so it only uses the regularity actually proved.

The current text jumps from local flatness to `C^{2,\gamma}` smallness without writing the quantitative upgrade.

## 4. Finish the tame boundary-gradient remainder carefully

The key analytic step in `fixed-domain-bernoulli-expansion.tex` is the `C^{2,\gamma} \times H^1 \to L^2` remainder bound.

What needs to be made explicit:

- enumerate the second-variation source terms instead of describing them schematically;
- justify the integration-by-parts step on the sphere for the highest-derivative products;
- show the resulting source estimate with constants that are uniform in the small graph regime.

Until that is written out cleanly, the Bernoulli spectral closure remains conditional.

## 5. Keep the final theorem in the correct regime

The final statement should be restricted to the regime actually covered by the proof:

- small asymmetry;
- selected minimizers;
- graph entry plus the chosen closure mechanism.

If the Bernoulli route is not fully closed, the theorem should explicitly say that the last step uses the BDV nearly spherical second variation instead.

## 6. Fix the sign typo in the Bernoulli expansion

In `fixed-domain-bernoulli-expansion.tex`, the text near the square-root argument says `\partial_r\widetilde u_g \ge 1/(2N)`.

That sign is inconsistent with the torsion solution near the unit ball, where the radial derivative is negative.

This should be rewritten in terms of `|\partial_r\widetilde u_g|` or with the correct negative sign.

## 7. Recommended status wording

Use this instead of “proved end-to-end”:

> The selection principle and graph-entry steps are quantitative. The Bernoulli spectral closure is a promising conditional route, but the fully rigorous closure still requires either a completed tame remainder proof or the BDV nearly spherical second variation as the final step.

