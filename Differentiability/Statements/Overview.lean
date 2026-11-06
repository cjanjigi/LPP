/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

/-!
# Statements of the main results

Two versions of every main result, with a proved equivalence between them:

- version A, `literal_X`: the source statement copied verbatim from its corresponding library
  theorem;
- version B, `plain_X`: the same statement written with the named definitions of
  `ShapeDefinitions.lean` and `ProbabilityDefinitions.lean`; the theorem with the descriptive name
  states it, its docstring gives the exact label, and an alias is named by the label;
- `plain_X_iff_literal : plain_X ↔ literal_X`.

The shape statements take the paper's form: the shape function exists and is unique, and it has the
property in question. The uniqueness facts that make this equivalent to the literal form are in
`ShapeFacts.lean`.

Files: `Differentiability.lean` (the differentiability preprint, Theorem 2.1), `Martin2004.lean`
(Martin (2004)), `BK.lean` (van den Berg and Kesten (1985), Theorem 3.3 and its extensions),
`Liggett.lean` (Liggett (1985), Theorem 1.10), `Concentration.lean` (Martin (2004), Lemma 3.1).
-/
