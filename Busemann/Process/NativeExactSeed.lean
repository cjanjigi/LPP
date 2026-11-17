/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeCocycles
public import Busemann.Process.CoupledMeans
public import Busemann.Process.RawFutureIndependence

@[expose] public section

open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- The native countable seed has exact unit means and raw future independence
from the strict past, on the same weak-limit law and cocycle event. This is the
countable-seed step in JR arXiv:1810.03580v3, proof of Theorem 4.8 after
(4.19)-(4.21). -/
theorem exists_native_exact_countable_seed
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
      ∀ I : Set Lattice,
        let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
        let U : ProcessSample →
            (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
          fun s a => match a with
            | .inl x => s.1 x.1
            | .inr (j, x, i) => s.2 j x.1 i
        IndepFun U (pastVariables I) (P : Measure ProcessSample) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2

  obtain ⟨P, φ, hφ, hweak, hMarginalFst, hShiftPreserving, hRawMeans,
    hRMeasurable, hRIntegrable, hUnit, hREdgeMeans, C, hCDef, hCMeasurable,
    hCProbability, hCInvariant, hCAll, hCocycle⟩ :=
    exists_native_countable_cocycles μ hmoment g hg h

  have hMarginal :
      (P : Measure ProcessSample).map processEnvironment = environmentLaw μ := by
    change (P : Measure ProcessSample).map Prod.fst = environmentLaw μ
    exact hMarginalFst

  have hShift : ∀ z : Lattice,
      (P : Measure ProcessSample).map (processShift z) = P := by
    intro z
    exact (hShiftPreserving z).map_eq

  have hCAE : ∀ᵐ s ∂(P : Measure ProcessSample), s ∈ C :=
    (mem_ae_iff_prob_eq_one hCMeasurable).mpr hCProbability

  have hOriginRecovery (j : ℕ) : ∀ᵐ s ∂(P : Measure ProcessSample),
      min (R j (0, 0) ((1 : ℤ), (0 : ℤ)) s)
          (R j (0, 0) ((0 : ℤ), (1 : ℤ)) s) = processEnvironment s 0 := by
    filter_upwards [hCAE] with s hs
    have hrec := (hCAll s hs j).2.2
    simpa [R, S, processEnvironment] using hrec 0

  have hUpper₁ (j : ℕ) :
      (∫ s, R j (0, 0) ((1 : ℤ), (0 : ℤ)) s ∂(P : Measure ProcessSample)) ≤
        -((h j).val.1) := by
    simpa [R, S, finiteEdgeStep, finiteTiltCoordinate] using
      (hREdgeMeans j (0, 0) 0).2

  have hUpper₂ (j : ℕ) :
      (∫ s, R j (0, 0) ((0 : ℤ), (1 : ℤ)) s ∂(P : Measure ProcessSample)) ≤
        -((h j).val.2) := by
    simpa [R, S, finiteEdgeStep, finiteTiltCoordinate] using
      (hREdgeMeans j (0, 0) 1).2

  have hExactMeans (j : ℕ) :=
    coupled_cocycle_edge_means μ hmoment g hg (h j) (P : Measure ProcessSample)
      hMarginal hShift (R j) (hCocycle j) (fun x y => hRIntegrable j x y)
      (hOriginRecovery j) (hUpper₁ j) (hUpper₂ j)

  have hREdgeExact : ∀ j x i,
      Integrable (R j x (x + finiteEdgeStep i)) (P : Measure ProcessSample) ∧
      (∫ s : ProcessSample, R j x (x + finiteEdgeStep i) s
        ∂(P : Measure ProcessSample)) = -finiteTiltCoordinate (h j).val i := by
    intro j x i
    have hmeans := hExactMeans j x
    fin_cases i
    · exact ⟨(hREdgeMeans j x 0).1, by
        simpa [R, S, finiteEdgeStep, finiteTiltCoordinate] using hmeans.1⟩
    · exact ⟨(hREdgeMeans j x 1).1, by
        simpa [R, S, finiteEdgeStep, finiteTiltCoordinate] using hmeans.2⟩

  have hUnitValue (j : ℕ) (x : Lattice) (i : Fin 2) (s : ProcessSample) :
      R j x (x + finiteEdgeStep i) s = s.2 j x i := by
    fin_cases i
    · simpa [R, S, finiteEdgeStep] using (hUnit s j x).1
    · simpa [R, S, finiteEdgeStep] using (hUnit s j x).2

  have hRawExact : ∀ j x i,
      Integrable (fun s : ProcessSample => s.2 j x i) (P : Measure ProcessSample) ∧
      (∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) =
        -finiteTiltCoordinate (h j).val i := by
    intro j x i
    have hUnitAE : ∀ᵐ s ∂(P : Measure ProcessSample),
        R j x (x + finiteEdgeStep i) s = s.2 j x i :=
      ae_of_all _ (hUnitValue j x i)
    refine ⟨(hRawMeans j x i).1, ?_⟩
    calc
      (∫ s : ProcessSample, s.2 j x i ∂(P : Measure ProcessSample)) =
          ∫ s : ProcessSample, R j x (x + finiteEdgeStep i) s
            ∂(P : Measure ProcessSample) :=
              integral_congr_ae (hUnitAE.mono fun s hUnit => hUnit.symm)
      _ = -finiteTiltCoordinate (h j).val i := (hREdgeExact j x i).2

  have hRawIndependence :=
    rawFutureIndepPast_of_actualWeakLimit μ (fun j => (h j).val) P φ hweak

  exact ⟨P, φ, hφ, hweak, hMarginalFst, hMarginal, hShiftPreserving, hRawExact,
    hRMeasurable, hRIntegrable, hUnit, hREdgeExact, C, hCDef, hCMeasurable,
    hCProbability, hCInvariant, hCAll, hCocycle, hRawIndependence⟩

end LPP.Busemann
