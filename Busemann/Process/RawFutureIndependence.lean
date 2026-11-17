/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Finite.FutureIndependence
public import Busemann.Frozen.Definitions.FiniteBusemannArrayAtSharedHorizon
public import Busemann.Frozen.Definitions.PastVariables
public import ProbabilityBasics.Probability.WeakIndependence
import Busemann.Finite.Measurability
import LPP_Foundations.Probability.EnvironmentLaw

@[expose] public section

open MeasureTheory ProbabilityTheory LPPDifferentiability
open Filter
open scoped Topology

namespace LPP.Busemann

/-- The raw countable future remains independent of the strict past under the
actual shared-horizon weak limit; this is the countable-coordinate statement
in JR1810.03580v3, Theorem 4.8(b), lines 654–668. -/
theorem rawFutureIndepPast_of_actualWeakLimit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℕ → ℝ × ℝ)
    (P : ProbabilityMeasure ProcessSample) (φ : ℕ → ℕ)
    (hweak :
      let ν : ℕ → ProbabilityMeasure ProcessSample := fun n =>
        (show ProbabilityMeasure (Environment × Fin (n + 1)) from
          ⟨finiteBusemannSharedHorizonLaw μ n, by
            change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
            infer_instance⟩).map
          (fun p => (p.1, finiteBusemannArrayAtSharedHorizon n h p))
      Tendsto (ν ∘ φ) atTop (𝓝 P)) :
    ∀ I : Set Lattice,
      let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
      let U : ProcessSample →
          (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
        fun s a => match a with
          | .inl x => s.1 x.1
          | .inr (j, x, i) => s.2 j x.1 i
      IndepFun U (pastVariables I) (P : Measure ProcessSample) := by
  classical
  let q (n : ℕ) : ProbabilityMeasure (Environment × Fin (n + 1)) :=
    ⟨finiteBusemannSharedHorizonLaw μ n, by
      change IsProbabilityMeasure (uniformOriginProduct (environmentLaw μ) n)
      infer_instance⟩
  let S (n : ℕ) (p : Environment × Fin (n + 1)) : ProcessSample :=
    (p.1, finiteBusemannArrayAtSharedHorizon n h p)
  let ν : ℕ → ProbabilityMeasure ProcessSample := fun n => (q n).map (S n)
  change Tendsto (ν ∘ φ) atTop (𝓝 P) at hweak
  intro I
  let J : Set Lattice := {y | ∃ x ∈ I, x ≤ y}
  let U : ProcessSample →
      (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
    fun s a => match a with
      | .inl x => s.1 x.1
      | .inr (j, x, i) => s.2 j x.1 i
  let PastIndex := {x : Lattice // ∀ z ∈ I, ¬ z ≤ x}
  let : Countable Lattice := inferInstance
  let : Countable {x : Lattice // x ∈ I} := Subtype.countable
  let : Countable {x : Lattice // x ∈ J} := Subtype.countable
  let : Countable PastIndex := Subtype.countable

  -- These observations are continuous because each output coordinate reads
  -- one coordinate of the environment or of the sampled edge array.
  have hUcont : Continuous U := by
    apply continuous_pi
    intro a
    cases a with
    | inl x => exact (continuous_apply x.1).comp continuous_fst
    | inr q =>
      rcases q with ⟨j, x, i⟩
      exact (continuous_apply i).comp ((continuous_apply x.1).comp
        ((continuous_apply j).comp continuous_snd))
  have hPastcont : Continuous (pastVariables I) := by
    change Continuous (fun s : ProcessSample => fun x : PastIndex => s.1 x.1)
    apply continuous_pi
    intro x
    exact (continuous_apply x.1).comp continuous_fst
  have hUmeas : Measurable U := hUcont.measurable
  have hPastmeas : Measurable (pastVariables I) := hPastcont.measurable

  -- The finite theorem uses the same local future index and the actual
  -- one-based shared horizon selected by the sampler.
  let F (n : ℕ) : Environment × Fin (n + 1) →
      (Sum {x : Lattice // x ∈ I} (ℕ × {x : Lattice // x ∈ J} × Fin 2) → ℝ) :=
    fun p a => match a with
      | .inl x => p.1 x.1
      | .inr (j, x, i) =>
          finiteBusemannEdge p.1 (h j) x.1 ((p.2.val + 1 : ℕ) : ℤ) i
  let G (n : ℕ) : Environment × Fin (n + 1) → (PastIndex → ℝ) :=
    fun p x => p.1 x.1
  have hS (n : ℕ) : Measurable (S n) :=
    measurable_fst.prodMk (measurable_finiteBusemannArrayAtSharedHorizon n h)
  have hUS (n : ℕ) : U ∘ S n = F n := by
    funext p a
    cases a with
    | inl x => rfl
    | inr q => rcases q with ⟨j, x, i⟩; rfl
  have hPastS (n : ℕ) : pastVariables I ∘ S n = G n := by
    funext p x
    rfl
  have hFmeas (n : ℕ) : Measurable (F n) := by
    rw [← hUS n]
    exact hUmeas.comp (hS n)
  have hGmeas (n : ℕ) : Measurable (G n) := by
    rw [← hPastS n]
    exact hPastmeas.comp (hS n)

  -- Transport the finite independence through the genuine sampler map.
  have hfinite (n : ℕ) :
      IndepFun (F n) (G n) (finiteBusemannSharedHorizonLaw μ n) := by
    convert finiteBusemann_raw_future_indep_past μ h n I using 1
  have hjoint (n : ℕ) :
      (ν n : Measure ProcessSample).map (fun s => (U s, pastVariables I s)) =
        ((ν n : Measure ProcessSample).map U).prod
          ((ν n : Measure ProcessSample).map (pastVariables I)) := by
    change ((q n : Measure (Environment × Fin (n + 1))).map (S n)).map
        (fun s => (U s, pastVariables I s)) =
      (((q n : Measure (Environment × Fin (n + 1))).map (S n)).map U).prod
        (((q n : Measure (Environment × Fin (n + 1))).map (S n)).map
          (pastVariables I))
    rw [Measure.map_map (hUmeas.prodMk hPastmeas) (hS n)]
    rw [Measure.map_map hUmeas (hS n), Measure.map_map hPastmeas (hS n)]
    change (q n : Measure (Environment × Fin (n + 1))).map
        (fun p => (U (S n p), pastVariables I (S n p))) =
      (((q n : Measure (Environment × Fin (n + 1))).map (U ∘ S n)).prod
        ((q n : Measure (Environment × Fin (n + 1))).map
          (pastVariables I ∘ S n)))
    have hpair : (fun p => (U (S n p), pastVariables I (S n p))) =
        fun p => (F n p, G n p) := by
      funext p
      exact Prod.ext (congrFun (hUS n) p) (congrFun (hPastS n) p)
    rw [hpair, hUS n, hPastS n]
    exact (hfinite n).map_prod_eq_prod_map_map
      (hFmeas n).aemeasurable (hGmeas n).aemeasurable
  have hfiniteActual (n : ℕ) :
      IndepFun U (pastVariables I) (ν n : Measure ProcessSample) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hUmeas.aemeasurable hPastmeas.aemeasurable).2 (hjoint n)

  -- The observations are continuous, so the general weak-limit result applies.
  exact ProbabilityBasics.indepFun_of_weakLimit (ν ∘ φ) P hweak U
    (pastVariables I) hUcont hPastcont (fun n => hfiniteActual (φ n))

end LPP.Busemann
