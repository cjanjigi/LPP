import Lake

open Lake DSL

package «lppdifferentiability» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- ProbabilityBasics project. -/
@[default_target]
lean_lib «ProbabilityBasics» where
  globs := #[.andSubmodules `ProbabilityBasics]
  leanOptions := projectLeanOptions

/-- LPP_Foundations project. -/
@[default_target]
lean_lib «LPP_Foundations» where
  globs := #[.andSubmodules `LPP_Foundations]
  leanOptions := projectLeanOptions

/-- Martin2004 project. -/
@[default_target]
lean_lib «Martin2004» where
  globs := #[.andSubmodules `Martin2004]
  leanOptions := projectLeanOptions

/-- Differentiability project. -/
@[default_target]
lean_lib «Differentiability» where
  globs := #[.andSubmodules `Differentiability]
  leanOptions := projectLeanOptions
