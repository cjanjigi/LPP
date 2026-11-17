/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CountableEdgeLaw
public import Busemann.Process.CountableCocycle
import Mathlib.Tactic

/-! Native countable cocycles from one shared-horizon limit law. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- One native weak-limit law carries all countable shift-covariant cocycles.

This assembles the native edge law and the literal signed path sums from the
proof of Theorem 4.8 after (4.19)-(4.20) in JR arXiv:1810.03580v3. -/
theorem exists_native_countable_cocycles
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
      let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
        if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
        else -(∑ k ∈ Finset.Ico b a, f k)
      let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
        S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
          S (fun k => s.2 j (y.1, k) 1) x.2 y.2
      Measurable (fun q : ℕ × Lattice × Lattice × ProcessSample =>
        R q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      (∀ j x y, Integrable (R j x y) (P : Measure ProcessSample)) ∧
      (∀ s j x, R j x (x + (1, 0)) s = s.2 j x 0 ∧
        R j x (x + (0, 1)) s = s.2 j x 1) ∧
      (∀ j x i,
        Integrable (R j x (x + finiteEdgeStep i)) (P : Measure ProcessSample) ∧
        (∫ s : ProcessSample, R j x (x + finiteEdgeStep i) s
          ∂(P : Measure ProcessSample)) ≤ -finiteTiltCoordinate (h j).val i) ∧
      ∃ C : Set ProcessSample,
        C = {s | (∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
            s.2 j x 1 + s.2 j (x + (0, 1)) 0) ∧
          (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x)} ∧
        MeasurableSet C ∧
        (P : Measure ProcessSample) C = 1 ∧
        (∀ z s, processShift z s ∈ C ↔ s ∈ C) ∧
        (∀ s ∈ C, ∀ j,
          (∀ x y z, R j (x + z) (y + z) s = R j x y (processShift z s)) ∧
          (∀ x y z, R j x y s + R j y z s = R j x z s) ∧
          recovers_environment s.1 (fun x y => R j x y s)) ∧
        (∀ j, is_shift_covariant_cocycle (P : Measure ProcessSample) processShift (R j)) := by
  classical
  obtain ⟨P, φ, hφ, hweak, hMarginal, hShiftInvariant, hMeans, hSquareRecovery⟩ :=
    exists_native_countable_edge_law μ hmoment g hg h

  let hInt : ∀ j x i,
      Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) := by
    intro j x i
    exact (hMeans j x i).1

  -- Specialize every native square to the elementary unit square.
  have hElementary : ∀ᵐ s ∂(P : Measure ProcessSample),
      (∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
        s.2 j x 1 + s.2 j (x + (0, 1)) 0) ∧
      (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x) := by
    filter_upwards [hSquareRecovery] with s hs
    constructor
    · intro j x
      simpa [finiteEdgeStep] using hs.1 j x 0 1
    · exact hs.2

  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2

  obtain ⟨hRMeasurable, hRIntegrable, hUnit, C, hCDef, hCMeasurable, hCProb,
    hCInvariant, hCAll, hCocycle⟩ :=
    countable_coordinate_cocycles (P : Measure ProcessSample) hInt hElementary

  have hUnitValue (j : ℕ) (x : Lattice) (i : Fin 2) (s : ProcessSample) :
      R j x (x + finiteEdgeStep i) s = s.2 j x i := by
    fin_cases i
    · simpa [R, S, finiteEdgeStep] using (hUnit s j x).1
    · simpa [R, S, finiteEdgeStep] using (hUnit s j x).2

  have hREdgeMean : ∀ j x i,
      Integrable (R j x (x + finiteEdgeStep i)) (P : Measure ProcessSample) ∧
      (∫ s : ProcessSample, R j x (x + finiteEdgeStep i) s
        ∂(P : Measure ProcessSample)) ≤ -finiteTiltCoordinate (h j).val i := by
    intro j x i
    have hUnitAE : ∀ᵐ s ∂(P : Measure ProcessSample),
        R j x (x + finiteEdgeStep i) s = s.2 j x i :=
      ae_of_all _ (hUnitValue j x i)
    constructor
    · exact hRIntegrable j x (x + finiteEdgeStep i)
    · calc
        (∫ s : ProcessSample, R j x (x + finiteEdgeStep i) s
            ∂(P : Measure ProcessSample)) =
          ∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample) :=
            integral_congr_ae hUnitAE
        _ ≤ -finiteTiltCoordinate (h j).val i := (hMeans j x i).2

  exact ⟨P, φ, hφ, hweak, hMarginal, hShiftInvariant, hMeans,
    hRMeasurable, hRIntegrable, hUnit, hREdgeMean, C, hCDef, hCMeasurable,
    hCProb, hCInvariant, hCAll, hCocycle⟩

end LPP.Busemann
