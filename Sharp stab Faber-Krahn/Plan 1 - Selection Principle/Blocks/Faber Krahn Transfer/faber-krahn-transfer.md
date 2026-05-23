# Sharp Faber-Krahn stability via the Kohler-Jobin transfer

Route A gives sharp **Saint-Venant** stability through the single-set
selection map, graph entry, interpolation into the nearly spherical class,
and BDV Theorem 3.3. This note records the Kohler-Jobin transfer step that
converts that energy estimate into sharp **Faber-Krahn** stability for the
first Dirichlet eigenvalue:

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
  \(E(\Omega)-E(B^*)\ge c_{\rm SV}(N,R)\mathcal A(\Omega)^2\), equivalently
  \(T_0-T(\Omega)\ge2c_{\rm SV}(N,R)\mathcal A(\Omega)^2\),
- the Kohler-Jobin linearization above,
- and the pointwise Kohler-Jobin lower bound when
  \(T_0-T(\Omega)>T_0/2\),

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

where the small-deficit branch has

\[
c_1(N,R)=\frac{4L_N\,c_{\rm SV}(N,R)}{(N+2)T_N},
\]

and the large-deficit branch has

\[
c_2(N)=\frac{L_N(2^{2/(N+2)}-1)}{4}.
\]

The chain of constants:

| stage | constant | source |
|-------|----------|--------|
| selection | $C_{\rm sel}(N,R)$ | `quantitative-selection-principle.md` |
| graph entry | $\alpha_{\rm graph}(N,R)$ | `graph-entry-closure.md` |
| Route A closure | $c_{\rm sph}(N),\delta_{\rm sph}(N,\gamma_0)$ | BDV Theorem 3.3 |
| Saint-Venant threshold | $q_*=c_*/(2C_{\rm sel})$ | combined |
| Kohler-Jobin multiplier | $2L_N/((N+2)T_N)$ | universal |
| small-deficit FK | $c_1$ | this note, §3 |
| large-deficit FK | $c_2$ | pointwise Kohler-Jobin |

## 5. Comparison with BDV

This is exactly the chain BDV use to prove sharp Faber-Krahn (their Theorem
1.1). The Kohler-Jobin transfer step is shared with BDV and uses no new
input.

**The reliable Route A content of Plan 1** is that the selection and
graph-entry parts are made single-set and quantitative, while the final
Saint-Venant closure still uses BDV's nearly spherical theorem. The
Kohler-Jobin step is unchanged. The Bernoulli spectral closure remains Route B.

## 6. End-to-end status

The full chain for **sharp quantitative Faber-Krahn stability** is now:

1. Selection (`quantitative-selection-principle.md`) — preserves $Q_\alpha$.
2. Graph entry (`graph-entry-closure.md`) — places the selected minimizer
   in the small $C^{2,\gamma_0}$ graph class via interpolation.
3. BDV nearly spherical theorem (Route A) — gives the pointwise lower bound
   for selected small graphs. Route B may replace this with the Bernoulli
   spectral closure once its source enumeration is fully finalized.
4. Kohler-Jobin transfer (this note) — converts to sharp Faber-Krahn.

Each step is structurally complete. The final closure (step 3) is either
**Route A** (BDV's nearly spherical second variation — unconditional) or
**Route B** (Bernoulli spectral closure — conditional on
`corrections-response.md`, §3). The end result, in either route, is

\[
\lambda_1(\Omega)-\lambda_1(B^*)\ge c_{\rm FK}(N,R)\,\mathcal A(\Omega)^2,
\]

with sharp exponent $2$, for every open $\Omega\subset B_R$ with
$|\Omega|=|B^*|$.
