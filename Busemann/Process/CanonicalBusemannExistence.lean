/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Process
public import Busemann.Process.TiltIndexedBusemannProcess
public import LPP_Foundations.Statements.WeightMoments

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- The canonical tilt-indexed Busemann process exists under the hypotheses of
Theorem 3.11 of the Strong Existence manuscript. Its characterization
includes the Skorokhod realization and almost sure uniqueness. -/
theorem exists_canonical_busemann_process
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2) :
    ∃ Bm Bp : StrongField μ, IsCanonicalBusemannProcess μ Bm Bp := by
  obtain ⟨Bm, Bp, hProcess⟩ :=
    exists_unique_strong_busemann_process μ hμ hmoment
  exact ⟨Bm, Bp, (is_canonical_busemann_process_iff μ Bm Bp).mpr hProcess⟩

end LPP.Busemann
