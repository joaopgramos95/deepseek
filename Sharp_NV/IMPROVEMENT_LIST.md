# Improvement List — Sharp_NV/main.tex

A curated punch list, by category, of items to fix in the rewritten / reassembled paper. The original `main.tex` is **not** to be edited; the changes land in `Final/`.

The file ends at line 2970 and the broad structure is

- Lines 1–731: preamble (packages, macros, theorem styles, author info).
- Lines 738–979: §1 Introduction (1.1 main results, 1.2 overview, 1.3 acks).
- Lines 981–2280: §2 Preliminaries (tree formalism, normal form derivation, modified normal form / gauged equation).
- Lines 2281–2704: §3 Functional setting and multilinear estimates (FRE lemmas + proof of `prop:bourgL2`).
- Lines 2706–2858: §4 Proof of the main theorem (LWP for gauged NV, gauge mapping, equivalence/density).
- Lines 2862–2921: Appendix on $s>-\tfrac34$.

The four coauthor structural items (Resumir a prova da densidade, Limpar a construção da GNV, Limpar as FRE, Terminar a introdução) are dispatched to four parallel agents, whose outputs are
`density.tex`, `gauge.tex`, `fre.tex`, `intro.tex` (each preceded by a WIP file with ≥ 4 passes).

---

## (A) Typos / LaTeX / grammar

### Macros & author notes
- The author-note macros `\simao{}`, `\joao{}`, `\andreia{}` still emit margin notes throughout the file (lines 1291, 1303, 2248, 2372, 2791, 2944, 2953 …). For the Final version all of these should be silenced (redefine the macros to swallow their argument, or remove the notes outright after they have been acted upon).
- Line 679: `\newcommand{\joao}[1]{\marginpar{\color{brown} …}{\smallskip \noi\color{red}JOAO: #1}\smallskip}` — text colour is `red`, contradicting the `brown` marker. Cosmetic.
- Line 55: `\newcommand{\jp}{\color{orange}}` is defined but never used.
- Line 95: `\mathtoolsset{showonlyrefs=true}` is convenient but masks unreferenced equations during proof reading. Keep, but be aware some `\eqref` failures are silent until that flag is removed.

### Placeholders / broken refs
- Line 1097: `\pb(\star)\neq \emptyser` → `\emptyset`. (Compile error / undefined control sequence in some setups.)
- Line 1285: `\eqref{psi-tree}` — there is no label `psi-tree`; the two relevant labels are `psi0-tree` (1207) and `psiE-tree` (1226). Fix or merge.
- Line 1232: `\label{psi-circ}` duplicates the earlier `\label{psi-circ}` at line 1216 — drop the second copy (or rename to `psi-circ-E`).
- Lines 1409, 1420, 1597: `\eqref{dtv}` — no label `dtv`. The intended target is the Duhamel form of (NV) for $v$ derived at the top of §2.2.
- Line 1597: also `\eqref{kdv}` (should be `eq:NV`) and `\eqref{inter}` (no such label).
- Line 1403: "We refer the reader to the companion paper CITE" — replace `CITE` with `\cite{chcora}` (Lemma 2.7 there).
- Line 1465: `\label{NFE001}` collides with `\label{NFE001}` on line 1324. Rename one (e.g. `NFE001b`).
- Line 2370: `[CITE]` (Strichartz reference) — fill the actual reference.
- Line 2434: "Morse's lemma with parameters [CITE]" — add a precise reference (e.g. Hörmander vol. I §C.6, or Duistermaat).

### Grammar & punctuation
- Line 877: "(but is yet to be achieved for quadratic cases)" — slightly ambiguous; rephrase.
- Line 1180: "after **an** differentiation-by-parts step" → "after **a** differentiation-by-parts step".
- Line 1204: "zero-energy phase function**}**associated" — missing space after `}`.
- Line 1273: "differentiation-by-parts" wording is consistent but verbose; once the phrase is introduced, abbreviate to "DBP" or simply "the procedure".
- Line 2336: "Suppose that **there exists** $B\subset \dots$ **be** a proper non-empty subset" — agreement issue: "let $B\subset\dots$ be a proper non-empty subset" or "Suppose that there exists $B\subset\dots$, a proper non-empty subset".
- Line 2502: `for $\xi_{\star1}. \xi_{\star2}$ fixed` — full stop where a comma is meant.
- Line 2702: `is similar to\eqref{eq:IVinterp2}` — missing space.
- Line 2792: "which **is is** a consequence of" — duplicate.
- Line 2846: "is well-posed **in for** initial data" — drop "in".
- Line 2891: "as already been shown" → "**has** already been shown".
- Line 2812: `u_0 \in H^{s'}(\R)` should be `\R^2`.
- Line 2917: index mismatch `d\xi_{\l}` vs the running variable `k`.

### Notation drift / mathy nits
- Line 1217 vs 1209: define `\Psi_0(\star)` with the same sign convention as `\Psi_0(\TT)` (the version in 1217 already does, but cross-check against 1207). Same for `\Psi_E(\star)`.
- Lines 2249-2269: $w$ is defined twice — once via $v = w + \Ical(\<1>, -i\mulB(\<1>); w)$ (the change of variables), and a few lines later "we set $w$ to be the interaction representation variable of a new unknown $z$". Either rename the second $w$ or rephrase to "Setting $z(t) := U(-t)w(t)$" without the misleading sentence about a new unknown $w$.
- Line 2426: "$c = \sum_{j=2}^k p_k = p - p_1$" — should be $\sum_{j=2}^k p_j$.
- Line 2684: "$\xi_{31}$" — should be `$\xi_{21}$`.
- Line 2879: the second proposition (in the appendix) is unlabelled — give it a `\label{prop:bilin_s-34}`.
- Line 2820 / 2843: keep direction of the gauge consistent — the lemma defines $\Gc^{-1}$ (the bilinear bump) and $\Gc$ is its inverse, but the body uses $\Gc[u]$ as the *gauged* variable. Either state in words "$\Gc_\delta$ is the inverse of the map $\Gc_\delta^{-1}$ defined in \eqref{eq:gauge}", or rename to avoid the inverse-direction confusion.

### Commented-out blocks that need a decision
- Lines 2274-2278 (commented Strichartz/standard fact remark) — either restore in a polished form or remove.
- Lines 2558-2581 (long commented Morse-with-parameters reasoning in Case B2 of Type IV) — either delete or replace the current short paragraph with a cleaned-up version of it (recommended: keep the short version).
- Lines 2925-2961 (long commented draft Proof of Theorem 1.1 / equiv) — delete.

---

## (B) Exposition

- **Introduction is the structural item D-(iv)** — handled by `intro.tex`. Key gaps in the current draft:
  - There is no "Organization of the paper" / "Notation" paragraph at the end of the introduction (the KdV companion paper has one).
  - The "Overview of the method" stops abruptly after the gauged equation is introduced; it does not preview the LWP statement for $(\mathcal{G}_\delta\text{-NV})$ (Proposition 4.1), the equivalence proposition, the density argument, or the role of frequency-restricted estimates.
  - The historical paragraph could explicitly compare the gap closed here (Theorem 1.1) with the gaps closed in the analogous KdV paper.
  - The remark after Theorem 1.1 mentions our KdV paper and the analogous critical results, but does not pin down what the present paper inherits vs. what is genuinely new (the *Sobolev* gain rather than $\FL^{s,p}$ gain).

- **Tree formalism subsection (§2.1):** the Definitions are mathematically clean but read very encyclopedically. A motivating sentence after each definition (one line, "we use this concept to track…") would help.

- **Normal form derivation (§2.2):** the first DBP step is written out longhand (lines 1303-1396), then Lemma 2.7 generalises it. A reader can lose the forest in the trees — add one short paragraph between the bare-hand calculation and Lemma 2.7 explaining what to expect next ("the same manipulation applied to a general tree produces …").

- **Modified normal form / gauge construction:** this is structural item D-(ii) — handled by `gauge.tex`. Specifically:
  - The transition from "boundary terms vanish" (Lemma `LEM:wbd`) to "only five tree shapes contribute" (Lemma `LEM:wint`) deserves a one-paragraph summary; the five types should be named/illustrated *before* the long combinatorial proof.
  - The proof of `LEM:wint` (lines 1928-2240) is a near-verbatim transposition of [chcora, Lemma 2.10]. It should be **shortened** to "the algebra is identical up to inserting the energy-phase contribution; we record the new step and refer to *loc. cit.* for the inclusion-exclusion bookkeeping", retaining the steps that involve $\Psi_E$ (which are genuinely new).
  - Figure 1 (the three subfigures of tree shapes) lacks an introductory caption explaining what "Type I, II/III, IV" mean.

- **Multilinear estimates (§3):** structural item D-(iii) — handled by `fre.tex`. The reader currently sees Proposition 3.1, then three black-box lemmas (Lem. 3.2–3.4), then the geometry lemma, then seven steps of case analysis. A one-paragraph road-map at the start of §3, plus a sentence at the start of each step linking it to the appropriate type of tree, would make the section navigable.

- **Density / equivalence argument (§4 from line 2806 on):** structural item D-(i) — handled by `density.tex`. The current text is two paragraphs ("Sketch of the proof"). Mirror the KdV companion (which has Lemmas `lem:estimativas_brutas`, `lem:zn`, `lem:equiv_n` + Proposition `PRO:equiv`), but **summarised** — three short lemmas plus one short proof of the equivalence, all flagged as parallel to the KdV proof.

- **Appendix:** state the proposition's number/label and add a single sentence saying *why* this appendix exists (it improves the smoothness of the data-to-solution map in the previously known range, complementing Theorem 1.1).

---

## (C) Theorems & proofs

- **Lemma 2.7 (Differentiation-by-parts on trees, line 1406):** cite [chcora, Lemma 2.7] (or its arXiv version) — currently the placeholder `CITE` is in the body of the lemma.

- **Proposition 2.8 (line 1595):** the hypothesis names equations `\eqref{kdv}`, `\eqref{inter}`, `\eqref{dtv}`, none of which are labels in this file. Fix targets to `\eqref{eq:NV}` and the appropriate normal-form equation introduced in §2.2.

- **Lemma `LEM:wbd` (line 1744):** the lemma is stated but the proof is omitted with the reference "identical to [chcora, Lemma 2.8]". A 5-line proof sketch (the cancellation $\BB(\TT) + \BB(\TT\overset{\star}{\ominus}\<1>)\circ\D = 0$ comes from the time-derivative of $\mathcal{G}_\delta$ applied to the boundary of the previous step) should be included so a PhD student is not forced to open the KdV manuscript.

- **Lemma `LEM:wint` (line 1882):** the proof is too long for what it adds beyond the KdV version. Trim aggressively, keeping only the inclusion-exclusion step that handles the $\Psi_E$ contribution. (See `gauge.tex` agent task.)

- **Lemma 3.6 (resonance geometry, line 2374):** the proof relies on Morse's lemma with parameters; cite a precise statement (Duistermaat *Fourier Integral Operators*, or Hörmander vol. I, §C.6). Also, the typo "$c = \sum_{j=2}^k p_k$" (should be $p_j$) appears mid-proof.

- **Proposition `prop:bourgL2` (line 2294):** the bound $\delta^{(2s+2)(j-3)-1}$ on the right-hand side has an off-by-one feel. Verify: in Step 2 the bound is $\delta^{(2s+2)(j-2)}$, in Step 4 it is $\delta^{(2s+2)(j-3)}M$. The summability used in Proposition 4.1 needs $\sum_j C^j \delta^{(2s+2)(j-3)-1} R^{j+1}$ to converge for some choice of $\delta$ depending on $R$ — sanity-check the geometric series there. (See `fre.tex` agent task.)

- **Step 6 (line 2684):** "$\xi_{11}\not\simeq -\xi_{31}$" — the index `31` makes no sense for the tree $\<33>$; presumably this should be `\xi_{21}`. Verify and correct.

- **Step 7 (Type V, $j\ge 4$, line 2691):** the argument is "proceed as in Step 4". One sentence saying *what extra step makes the larger weight $|\xi_{\star11}|^2$ work* (and where the $j-3$ factor of $\delta$ comes from) is needed for the reader to verify the geometric-series argument that closes Proposition 4.1.

- **Proposition `prop:lwp_rnv` (line 2713):** the chain of inequalities ending in "$\le R + T^{0+}C\delta^{-4s-5}R^2 \le 2R$" hides the geometric-series sum. Add one display showing $\sum_{j=1}^\infty C^j \delta^{(2s+2)(j-3)-1}R^{j-1} \le C\delta^{-4s-5}$ valid under the smallness condition \eqref{eq:escolhadelta}.

- **Lemma `LEM:D` (line 2755):** statement uses $B^{s',s}_{\delta}$ but the definition (line 2766) writes $B^{s',s}_\delta$ with subscript $\delta$ on the LHS but uses $R$ on the RHS; harmonise. Also the inclusion arrow in (i) should be $\Gc_\dl^{-1}:B^{s',s}_R \to B^{s',s}_{(1+\eps)R}$ with the same superscripts — the current statement reverses $s$ and $s'$ in one occurrence.

- **Proposition `PRO:equiv` (line 2808):** the "Sketch of the proof" is too sketchy. (See `density.tex` agent task.)

- **Appendix proposition (line 2879):** statement should be labelled. The proof writes $(\Phi - \alpha)$ with $\alpha \in \R$, $|\alpha| \lesssim M > 1$ — this should be $1 < M$, $|\alpha| \lesssim M$, otherwise the case $\alpha \approx 0$ is suspect.

---

## (D) Structural — coauthor punch list

| Item | Source file (WIP → final) | Owner |
|---|---|---|
| (D1) Resumir a prova da densidade (mirror the KdV folder) | `WIP_density.tex` → `density.tex` | density-agent |
| (D2) Limpar a construção da GNV (gauge): clearer, slightly less repetitive than KdV | `WIP_gauge.tex` → `gauge.tex` | gauge-agent |
| (D3) Limpar as FRE (Frequency Restricted Estimates) | `WIP_fre.tex` → `fre.tex` | fre-agent |
| (D4) Terminar a introdução — genuinely great | `WIP_intro.tex` → `intro.tex` | intro-agent |

After all four files exist, the parent assembles them in `Final/` with the rest of the article and the (A)/(B)/(C) fixes folded in.

Page-budget guidance: the article currently produces ~50 printed pages. Total expansion budget: **+5 pages comfortable, +10 still OK, +15 borderline, more not desired**. The density argument *gains* a few pages (from "two-paragraph sketch" to "three small lemmas + proof"); the gauge construction should *shed* a few pages (LEM:wint proof contraction). Net: roughly zero, possibly a small expansion.
