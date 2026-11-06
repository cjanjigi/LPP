/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

/-!
# The audit library

This library holds the check of the project's main statements against the papers, in the form used
by the Lean comparator tool.

* `Challenge/<Project>.lean` states the project's main results as theorems whose proofs are left
  open (`by sorry`). It imports only Mathlib and defines exactly the notions the statements mention,
  so a reader can check the statements against the paper in one short file. Nothing in it is
  private.
* `Solution/<Project>.lean` repeats the definitions and the theorem statements character for
  character and proves the theorems from the project library. It does not import the challenge file.
* `comparator/<Project>/comparator.json`, in the repository root, names the two modules, the
  theorems to compare and the only axioms allowed (`propext`, `Classical.choice`, `Quot.sound`).
  The script `scripts/check-challenges.mjs` checks that the two files correspond; the external
  comparator tool, once pinned, replays the solution in an independent kernel.

The deliberate `sorry` in each challenge file is the only `sorry` in the project. The root library
does not import this library, so the project's axiom check is unaffected. So far the library covers
Liggett (1985), Theorem 1.10.
-/
