/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.JointCompactness
public import Busemann.Process.StationaryLimit
public import Busemann.Process.ClosedConstraints
public import Busemann.Process.WeakMeanBound

/-! Native one-law consequences of the shared-horizon weak limit. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- Native moment and support inputs give one joint edge law with its canonical
marginal, shift invariance, one-sided coordinate means, square identities, and
recovery, as in JR1810.03580v3, proof of Theorem 4.8 after (4.17)--(4.20). -/
theorem exists_native_countable_edge_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (h : ℕ → SupportTilt g) :
    let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
      (show ProbabilityMeasure (Environment × Fin (n + 1)) from
        ⟨finiteBusemannSharedHorizonLaw μ n, by
          change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
          infer_instance⟩).map
        (fun p => (p.1,
          finiteBusemannArrayAtSharedHorizon n (fun j => (h j).val) p))
    ∃ P : ProbabilityMeasure ProcessSample, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (ν ∘ φ) atTop (𝓝 P) ∧
      (P : Measure ProcessSample).fst = environmentLaw μ ∧
      (∀ z : Lattice,
        MeasurePreserving (processShift z) (P : Measure ProcessSample)
          (P : Measure ProcessSample)) ∧
      (∀ j x i,
        Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) ∧
        (∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) ≤
          -finiteTiltCoordinate (h j).val i) ∧
      (∀ᵐ s ∂(P : Measure ProcessSample),
        (∀ j x i k, s.2 j x i + s.2 j (x + finiteEdgeStep i) k =
          s.2 j x k + s.2 j (x + finiteEdgeStep k) i) ∧
        (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x)) := by
  classical
  obtain ⟨P, φ, hφ, hweak, hmarginal⟩ :=
    exists_finiteBusemann_joint_probabilityMeasure_subseq μ hmoment g hg h
  let hvalues : ℕ → ℝ × ℝ := fun j => (h j).val
  refine ⟨P, φ, hφ, hweak, hmarginal, ?_, ?_, ?_⟩
  · intro z
    exact measurePreserving_processShift_of_finiteBusemann_weak_limit
      μ hvalues P φ hφ hweak z
  · exact integral_edge_le_neg_tilt_of_finiteBusemann_weak_limit
      μ hmoment g hg h P φ hφ hweak
  · exact ae_square_and_recovery_of_finiteBusemann_weak_limit
      μ hvalues P φ hφ hweak

end LPP.Busemann
