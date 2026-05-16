# Route B, clarified against your near-Serrin picture

You described a natural mechanism for the *graph* route (Strategy A):
near-Serrin `L²` + Markov ⇒ "most of the boundary has controlled norm"
⇒ go `O(δ_T)` inside ⇒ the control "propagates to the whole boundary"
like a dispersive smoothing ⇒ small `C³` graph. The single most
useful thing I can say about Route B is what it does with the *same
input* (`|∇u|` close to a constant on a level set, in `L²`), because it
is exactly the opposite design choice — and that contrast is the
clearest way to understand Route B.

## The shared starting point

Both routes start from one fact, produced by the level-set identity +
Markov: at a good level `\hat t`, the boundary-gradient defect
`∫_{Σ}(|∇u|−\bar f)²/|∇u|` is a small absolute constant. Equivalently,
`|∇u|` is close to a constant on `Σ=Σ_{\hat t}` *in `L²`*. Nothing
more is given for free — in particular, no pointwise/graph control.

## What Strategy A must then do (and where your picture lives)

Strategy A wants the *geometric* conclusion "`Σ` is a small graph over
a sphere". `L²`-closeness of `|∇u|` does not give that pointwise, so it
needs your two-step upgrade: (1) self-quantify — `L²` + Markov ⇒
controlled geometry off a small-measure bad set; (2) propagate —
go `O(δ_T)` deeper so the equation smooths the bad set away and the
control becomes uniform. That propagation is a genuine (and delicate)
PDE statement; it is exactly what the Strategy-A agents are testing.

## What Route B does instead: never leave `L²`, never form a graph

Route B refuses the geometric conclusion entirely. It keeps everything
**integral and interior**, and it is precisely Serrin's theorem used
the way Weinberger proved it.

Recall Weinberger's identity: with `P=|∇u|²+\tfrac2n u`,
`ΔP = 2\,|D²u+\tfrac1n I|² ≥ 0`, and equality holds exactly on the
ball quadratic. So the *interior* quantity `\R=∫|D²u+\tfrac1n I|²`
(the trace-free Hessian, integrated) measures non-roundness, and
Serrin/Weinberger rigidity is "`\R=0 ⟹ ball`". Route B is its
quantitative form:

1. The Saint–Venant deficit dominates `\R` (a quantitative Weinberger
   inequality, interior, no boundary regularity).
2. `\R` small ⇒ `D²u ≈ −\tfrac1n I` in `L²` ⇒ `u` is `H²`-close to a
   ball quadratic ⇒ the level set is Fraenkel-close to a ball.

The boundary-gradient defect (`|∇u|−\bar f` in `L²`, i.e. your
near-Serrin input) enters Route B in **one place only**: it bounds the
*measure* of the set where `|∇u|` is small (the small-gradient set),
which is the only place the `H²`-rigidity constant could degrade. That
bad set is then **excised and paid for additively** — its measure is
controlled, so removing it costs little.

## The precise contrast (this is the clarification)

- Strategy A needs the bad set to be *smoothed away* — pushed to zero
  and the good control made *uniform/pointwise on the whole boundary*.
  That is the "propagate `O(δ_T)` inside, dispersive-style" step you
  described, and it is the hard, open part.
- Route B never needs the bad set to vanish or the control to become
  pointwise. It only needs the bad set to have **small measure** (true,
  by Markov, with no propagation), and then it **deletes it** and works
  on the rest. There is no graph, no boundary norm, no propagation, no
  dispersive smoothing — because the conclusion is extracted from the
  *interior `L²` Hessian*, not from the *boundary geometry*.

So: your dispersive-propagation idea is the right tool *for Strategy A*
(making the boundary a uniform graph). Route B's whole point is that if
you are willing to give up the graph and argue in the interior via
Weinberger, you do not need that propagation at all — the same `L²`
near-Serrin input is enough, consumed by excision instead of smoothing.

## The honest caveat (so this clarification is not overselling)

Route B's two steps are not yet human-refereed. Step 1 (deficit
dominates `\R`, regularity-free, dimensional constant) and Step 2
(the `H²`-rigidity / Korn–Poincaré constant staying dimensional after
excising the small-gradient set, even for pinched or multi-component
level domains) are the two load-bearing analytic statements. The
clarification above explains the *design* — why Route B avoids the
propagation problem — not a claim that it is proved. Strategy A and
Route B are being pursued in parallel precisely because each has a
distinct hard point: A's is the propagation you described; B's is the
excised-Korn-constant.
