You are part of an agent swarm working on a providing a counterexample to L^2 stability of the Brascamp-Lieb inequality in Lean. 

This is our workspace, there are many agents working together here, almost one per file. Every file "filename.lean" in this folder should have two versions, the "WIP_filename.lean" version and the original wersion. The "WIP..." version is editable, the other one is not. This is to not step on other agents'work. 

If there is no WIP file, create it before the following instructions. 

Axioms and dependencies
=======================

Because of the way we are working, swarm agents are importing files with axioms and sorries. This is completely fine. they must bring their file to a sorry-free state by using the theorems in the dependecies as axioms. If they complain that they are "missing dependencies" and these sorries are proof-irrelevant, send them back to work!

Once every agent is done with a sorry-free proof, we will replace the files not starting with WIP by their WIP counterparts and there will be no dependencies. 

Best Practices
==============

## 1. Never Destroy Work

**WIP files ARE the backup.** There are no separate backup files. The orchestrator must never lose agent progress.

### Rules:
- **NEVER `git checkout --` a WIP file** that an agent has modified without saving a copy. This destroys uncommitted work irreversibly. In general, you can remove code *only when the code is a bad idea* (for example, during a refactor). You do not remove partially done code to obtain prettier rebuilds.
- **NEVER `git restore`** a WIP file with agent changes, unless those changes were *actively harmful* for the project.
- If an agent's changes have errors: **commit them anyway** with a descriptive message noting the errors, OR leave them in the working tree for the next agent to fix.
- If an agent's changes regress sorry count: still commit if they compile. The scaffolding may be useful. Add a note in the commit message.
- Before reverting anything, always check: `git stash` or `cp` first.

### The only safe revert:
A revert is safe ONLY if the file has no uncommitted changes from any agent (i.e., `git status` shows it clean).

## 2. Never Reinvent the Wheel

Agents waste enormous effort re-proving things that exist elsewhere. The orchestrator must point agents to existing infrastructure.


Once you're done
================

1. Congratulations! 

2. If the worktree is in a  sorry-free state, you must run the linter on every file. Before incorporating WIP_ file, make sure there are no linter errors, if there are som, repair them first.

