/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import Martin2004.Statements.ShapeFacts
public import Martin2004.Frozen.Martin.Proposition21
public import Martin2004.Frozen.Martin.ShapeContinuous
public import Martin2004.Frozen.Martin.Shape
public import Martin2004.Frozen.Martin.BoundaryAsymptotics
public import Martin2004.Frozen.Martin.FirstPassage
public import Martin2004.Frozen.Martin.FirstPassageBoundaryAsymptotics
public import Martin2004.Frozen.Martin.GrowthShape
public import Martin2004.Frozen.Martin.FirstPassageGrowthShape
public import Martin2004.Frozen.Martin.Remark51

public import Martin2004.Statements.LimitShape
public import Martin2004.Statements.BoundaryAsymptotics
public import Martin2004.Statements.GrowthSets

/-!
# The main results of Martin (2004), in two versions

The main results of Martin (2004) on the limit shape of last-passage and first-passage percolation,
in the planar case `d = 2`. For each of the nine results there are

* version A, `literal_<name>`: the source statement copied verbatim as a proposition (the only
  change is a leading underscore on the names of hypotheses that the statement does not use, to keep
  the unused-variable linter quiet), with `literal_<name>_holds` proved from the corresponding
  library theorem;
* version B, `plain_<name>`: the same statement written with the named definitions of
  `ShapeDefinitions`, with `plain_<name>_iff_literal` showing that it is equivalent to version A.
  Where the statement is about the shape function and a property of it, version B has the form of
  the paper: there is exactly one shape function, and it has the property (`ShapeFacts` proves that
  shape functions are unique);
* the theorem `<name>` stating version B with ordinary binders, whose docstring starts with the
  precise label, and an alias named by the label.

- `extendedShape_limits_of_finite_mean` — Proposition 2.1; alias `proposition_2_1`.
- `shape_continuous_of_finite_mean` — Propositions 2.1-2.2, Theorem 2.3; alias
  `propositions_2_1_2_2_theorem_2_3`.
- `shape_function_exists_unique` — Section 5.3 (uniform shape statement); alias
  `section_5_3_uniform_shape`.
- `shape_boundary_asymptotics` — Theorem 2.4; alias `theorem_2_4`.
- `firstPassageShape_continuous` — Corollary 2.5(i); alias `corollary_2_5_i`.
- `firstPassageShape_boundary_asymptotics` — Corollary 2.5(ii); alias
  `corollary_2_5_ii`.
- `lastPassage_growthSets_converge` — Theorem 5.1(i); alias `theorem_5_1_i`.
- `firstPassage_growthSets_converge` — Theorem 5.1(ii); alias `theorem_5_1_ii`.
- `taxicab_lower_bound_of_subadditive` — Remark 5.1(i); alias `remark_5_1_i`.

## References

* J. B. Martin, Limiting shape for directed percolation models, Ann. Probab. 32 (2004), Propositions
  2.1 and 2.2, Theorems 2.3, 2.4 and 5.1, Corollary 2.5, Remark 5.1 and Section 5.3.
-/

