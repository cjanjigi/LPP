/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeExactSeed
import Busemann.Process.CountableFutureIndependence

@[expose] public section

open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- The same native countable seed also carries independence of all indexed
path-sum future observations from the strict past. This is the countable-field
step in JR arXiv:1810.03580v3, Theorem 4.8(b), after (4.19). -/
theorem exists_native_countable_future_seed
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
      (P : Measure ProcessSample).map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice,
        MeasurePreserving (processShift z) (P : Measure ProcessSample)
          (P : Measure ProcessSample)) ∧
      (∀ j x i,
        Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) ∧
        (∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) =
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
          ∂(P : Measure ProcessSample)) = -finiteTiltCoordinate (h j).val i) ∧
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
        (∀ j, is_shift_covariant_cocycle (P : Measure ProcessSample) processShift (R j)) ∧
        (∀ I : Set Lattice,
          let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
          let U : ProcessSample →
              (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
            fun s a => match a with
              | .inl x => s.1 x.1
              | .inr (j, x, i) => s.2 j x.1 i
          IndepFun U (pastVariables I) (P : Measure ProcessSample)) ∧
        ∀ I : Set Lattice,
          let W : ProcessSample →
              (Sum {x : Lattice // x ∈ I}
                (ℕ × {p : Lattice × Lattice // p.1 ∈ I ∧ p.1 ≤ p.2}) → ℝ) :=
            fun s a => match a with
              | .inl x => s.1 x.1
              | .inr (j, p) => R j p.1.1 p.1.2 s
          IndepFun W (pastVariables I) (P : Measure ProcessSample) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2

  obtain ⟨P, φ, hφ, hweak, hMarginalFst, hMarginal, hShiftPreserving,
    hRawMeans, hRMeasurable, hRIntegrable, hUnit, hREdgeExact, C, hCDef,
    hCMeasurable, hCProbability, hCInvariant, hCAll, hCocycle,
    hRawIndependence⟩ := exists_native_exact_countable_seed μ hmoment g hg h

  have hInt : ∀ j x i,
      Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) := by
    intro j x i
    exact (hRawMeans j x i).1

  have hCountableFuture := countable_coordinate_future_indep_past
    (P : Measure ProcessSample) hInt hRawIndependence

  exact ⟨P, φ, hφ, hweak, hMarginalFst, hMarginal, hShiftPreserving, hRawMeans,
    hRMeasurable, hRIntegrable, hUnit, hREdgeExact, C, hCDef, hCMeasurable,
    hCProbability, hCInvariant, hCAll, hCocycle, hRawIndependence,
    hCountableFuture⟩

end LPP.Busemann
