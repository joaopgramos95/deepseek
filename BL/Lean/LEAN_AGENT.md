You are part of an agent swarm working on a providing a counterexample to L^2 stability of the Brascamp-Lieb inequality in Lean. 

This is our workspace, there are many agents working together here, almost one per file. Every file "filename.lean" in this folder should have two versions, the "WIP_filename.lean" version and the original wersion. The "WIP..." version is editable, the other one is not. This is to not step on other agents'work. 

If there is no WIP file, create it before the following instructions. 

Relevant to our work:

- Blueprint: This is the blueprint with the mathematical content that you have been told to translate. You read the analog to your .lean file for mathematical insight, and refer to other documents therein as you need them. 



Editing rules and etiquette
===========================

There are multiple agents working and compiling Lean files. You should be mindful of everyone else. In order to do so, every agent is working on a WIP_.. file, but importing the non-wip versions of the files.

1. You can only edit the WIP_ versinon, never the non WIP_ version. Once you are done, and your document compiles without sorries (other than the sorries coming from imports which are fine) you can 

2. You may not change the signature of any of the theorems without asking for perimssion. If you think the signature is wrong, you should stop and ask. There are three reasons to flag an issue
2.a  One of the theorems in your file is stronger than what the blueprint indicates, and this extra strenght makes the proof significantly harder.
2.b One of the theorems in your imports is too weak and that makes the proof significantly harder. 
2.c One of the theorems in your file is weaker than what the blueprint indicates, and this extra weakness will make the downstream proof too hard.

3. If you encounter any issue with the mathematical content of the WIP, you can flag that. 


Axioms and dependencies
=======================

Because of the way we are working, you are importing files with axioms and sorries. This is completely fine. You must bring your file to a sorry-free state by using the theorems in the dependecies as axioms. In particular do not leave unproven results in your files "because they have dependencies". You can use the sorried dependencies it's fine!

Once every agent is done with a sorry-free proof, we will replace the files not starting with WIP by their WIP counterparts and there will be no dependencies. 

Best Practices
==============

1. Build incrementally and test often. The magic of having a verifier is that you can do lots of cool things! Do not build the whole project, instead test your file only.

2. If you are proving something elementary and think "this should be in mathlib.." 
2.a  Search. It most likely is
2.b If you are 100% convinced it is not on mathlib (it, or a similar enough result) make it as a private lemma/theorem and tag it as :"-- to_mathlib: target/mathlib/file/path".

3. The final version of your code should be "mathlib ready". That does not mean you cannot build incrementally with "uglier" code of course.

3.a In particular (as an example), once you are done, you should use your lean_code_actions mcp to upgrade your simp to simp only using simp?, and expand aesop usage using aesop?

3.b The previous code sufferted from a lot of MAX_HEARTBEATS problems, this is not ideal and your code should be refactored around it.

4. Keep intermediate lemma statements as concrete and finitary as possible. If a bound holds exactly for a finite truncation parameter J, state it as `∀ J, exact_bound(J)` rather than as a limit or an ε-δ approximation. Avoid introducing infinite objects (`tsum`, integrals over unbounded domains, `Filter.Tendsto`) in intermediate lemma *statements* when a finite formulation suffices — the convergence/measurability obligations they create are disproportionately expensive in Lean. When infinite objects are unavoidable (e.g., because the goal involves an integral over ℝ or ℂ), isolate the finite-to-infinite bridge in a single dedicated lemma and keep the rest of the proof chain finitary.

5. More generally: a statement that is mathematically equivalent may be much harder or easier to prove in Lean. Prefer formulations that stay close to Lean's native strengths (finite sums, decidable arithmetic, algebraic manipulation) and minimize reliance on heavy analytic infrastructure (measure theory, dominated convergence, Fubini on non-compact domains). When in doubt, check whether the key Mathlib lemma you plan to invoke actually exists and has the signature you expect before committing to a proof strategy.

Once you're done
================

1. Congratulations! 

2. If you are now in a sorry-free state, you must look at all at the files you edited and check for simplicity and quality: Are they Mathlib-ready? are there proofs that contain stuff   that "should be in mathlib"? (If there is stuff  that "should be in mathlib, make it self-contained lemmas and annotate them as such, as per CLAUDE.md) This does not only apply to self-standing lemmas, but to intermediate steps in proofs.

3. Now that you have isolated plenty of Mathlib-ready lemmas, toroughly check mathlib in case they are not already there. If they genuinely are not there (and there isn't something sematically equivalent), tag them with "-- to_mathlib: target/mathlib/file/path".

4. Do a last pass, are there any linter warnings? any MAX_HEARBEATS? go sort them out!
