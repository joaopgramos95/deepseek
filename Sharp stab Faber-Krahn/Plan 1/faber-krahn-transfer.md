# Sharp Faber-Krahn stability via the Kohler-Jobin transfer

The spectral closure of `fixed-domain-bernoulli-expansion.md` gives sharp
**Saint-Venant** stability. This note records the Kohler-Jobin transfer
step that converts it into sharp **Faber-Krahn** stability for the first
Dirichlet eigenvalue:

\[
\lambda_1(\Omega)-\lambda_1(B^*)\ge c_{\rm FK}(N,R)\,\mathcal A(\Omega)^2,
\]

where $B^*$ is the ball with $|B^*|=|\Omega|$.

See `faber-krahn-transfer.tex/.pdf` for the full proof.

## 1. Kohler-Jobin inequality (1978)

For every open bounded set $\Omega\subset\R^N$ with finite $\lambda_1$, the
scale-invariant product

\[
\Psi(\Omega):=T(\Omega)\cdot\lambda_1(\Omega)^{(N+2)/2}
\]

satisfies $\Psi(\Omega)\ge \Psi(B)$ for every ball $B$, with equality iff
$\Omega$ is a ball. (Brasco's "On torsional rigidity and principal
frequencies," ESAIM:COCV 2014, gives the modern proof.)

## 2. Pointwise transfer at fixed volume

Setting $L=\lambda_1(B^*)$, $T_0=T(B^*)$, $\beta=(N+2)/2$, the Kohler-Jobin
inequality at fixed volume gives

\[
\lambda_1(\Omega)\ge L\cdot\bigl(T_0/T(\Omega)\bigr)^{1/\beta}.
\]

For small Saint-Venant deficit $\delta_{\rm SV}=T_0-T(\Omega)$, linearization
yields

\[
\lambda_1(\Omega)-L\ge\frac{2L}{(N+2)T_0}\,\delta_{\rm SV},
\quad\hbox{valid for }\delta_{\rm SV}\le T_0/2.
\]

This is the universal "Kohler-Jobin multiplier" $2L/((N+2)T_0)$ — a fixed
dimensional constant (using $T_N=|B_1|/(N(N+2))$ and $L_N$ the first
Dirichlet eigenvalue of $-\Delta$ on $B_1$).

## 3. Sharp Faber-Krahn theorem

Combining

- our sharp Saint-Venant stability
  $T_0-T(\Omega)\ge c_{\rm SV}(N,R)\mathcal A(\Omega)^2$ for $\mathcal A\le\mathcal A_*$,
- the Kohler-Jobin linearization above,
- and the trivial large-asymmetry bound $\lambda_1(\Omega)\ge L+\delta_*>L$
  away from the ball,

we obtain

\[
\boxed{
\lambda_1(\Omega)-\lambda_1(B^*)\ge c_{\rm FK}(N,R)\,\mathcal A(\Omega)^2
\quad\hbox{for every open }\Omega\subset B_R\hbox{ with }|\Omega|=|B^*|.
}
\]

The exponent $2$ on $\mathcal A$ is sharp (saturated by ellipsoidal
perturbations of the ball).

## 4. Quantitative constants

The constant $c_{\rm FK}(N,R)$ is

\[
c_{\rm FK}(N,R)=\min\bigl(c_1(N,R),\,c_2(N,R)\bigr),
\]

with

\[
c_1(N,R)=\frac{2L_N\,c_{\rm SV}(N,R)}{(N+2)T_N}
\ge\frac{2L_N\,\sigma_*(N,R)^4}{(N+2)T_N\,C_{\rm sel}(N,R)},
\]

(small-asymmetry, traced back through the selection chain), and
$c_2(N,R)>0$ a qualitative compactness constant (large-asymmetry). The
chain of constants:

| stage | constant | source |
|-------|----------|--------|
| selection | $C_{\rm sel}(N,R)$ | `quantitative-selection-principle.md` |
| graph entry | $\alpha_{\rm graph}(N,R)$ | `graph-entry-closure.md` |
| spectral closure | $\sigma_*(N,R), \delta_*(N,R)$ | `fixed-domain-bernoulli-expansion.md` |
| Saint-Venant threshold | $q_*\sim\sigma_*^4$ | combined |
| Kohler-Jobin multiplier | $2L_N/((N+2)T_N)$ | universal |
| small-asymmetry FK | $c_1$ | this note, §3 |
| large-asymmetry FK | $c_2$ | compactness |

## 5. Comparison with BDV

This is exactly the chain BDV use to prove sharp Faber-Krahn (their Theorem
1.1). The Kohler-Jobin transfer step is shared with BDV and uses no new
input.

**The new content of Plan 1** is that the Saint-Venant constant
$c_{\rm SV}(N,R)$ is now derived from the Bernoulli spectral closure
(`fixed-domain-bernoulli-expansion.md`) rather than from BDV's nearly
spherical second variation. The Kohler-Jobin step is unchanged.

## 6. End-to-end status

The full chain for **sharp quantitative Faber-Krahn stability** is now:

1. Selection (`quantitative-selection-principle.md`) — preserves $Q_\alpha$.
2. Graph entry (`graph-entry-closure.md`) — places the selected minimizer
   in the $C^{2,\gamma}$ graph class.
3. Bernoulli spectral closure (`fixed-domain-bernoulli-expansion.md`) —
   forces the selected minimizer to be the ball in the smallness regime,
   yielding sharp Saint-Venant stability.
4. Kohler-Jobin transfer (this note) — converts to sharp Faber-Krahn.

Each step is now individually rigorous (modulo standard references and
constant bookkeeping). The end result is

\[
\lambda_1(\Omega)-\lambda_1(B^*)\ge c_{\rm FK}(N,R)\,\mathcal A(\Omega)^2,
\]

with sharp exponent $2$, for every open $\Omega\subset B_R$ with
$|\Omega|=|B^*|$.
