/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Model.Animals.PathSets
import Differentiability.Probability.GlobalMaskFamilyWeights
import LPP_Foundations.Model.Paths.Fintype
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Weights of paths selected after observing very bad vertices

A varying finite family can collect sites anywhere in the lattice. The finite-region bound
applies to the subfamily whose collected sites lie in each finite region. The failure event for
the full family is the increasing union of these events.
-/

public section

open MeasureTheory LPPStatements
open scoped BigOperators ENNReal

namespace LPPDifferentiability.Paper

/-- Appendix B, `lem:weights`. A family of at most `N` paths, each of length at most `n`, is
selected measurably from the mask of weights below `-T`. If the paths avoid collected sites in
the mask, the probability that any path weight is too low is bounded by the binomial and
Bernstein estimates. The starts and collected sites can vary over the entire lattice. -/
theorem path_family_weight_failure_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hpos : HasSqrtUpperTail μ) (p T b t : ℝ) (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (n N K : ℕ) (hK : 1 ≤ K)
    (paths : (Lattice → Bool) → Finset (Σ u : Lattice, Σ d : ℕ × ℕ, Path u d))
    (hmeas : ∀ P, MeasurableSet {a | paths a = P})
    (hcard : ∀ a, (paths a).card ≤ N)
    (hlen : ∀ a q, q ∈ paths a → q.2.1.1 + q.2.1.2 ≤ n)
    (hgood : ∀ a q, q ∈ paths a → ∀ z ∈ q.2.2.collectedSites, a z = false) :
    let mask := fun ω : Environment => fun z : Lattice => if ω z < -T then true else false
    let E := {ω : Environment | ∃ q ∈ paths (mask ω),
      pathWeight ω q.2.2 <
        -2 * (∫ y, max (-y) 0 ∂μ) * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - (K - 1 : ℕ) * T - t}
    MeasurableSet E ∧ (environmentLaw μ).real E ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
  classical
  intro mask E
  let PathFamily := Finset (Σ u : Lattice, Σ d : ℕ × ℕ, Path u d)
  let _ : Countable PathFamily := by
    dsimp [PathFamily]
    infer_instance
  let _ : MeasurableSpace PathFamily := ⊤
  have hpaths : Measurable paths := measurable_to_countable' hmeas
  let sites (F : PathFamily) (j : Fin N) : Finset Lattice :=
    if h : j.val < F.card then (F.equivFin.symm ⟨j.val, h⟩).val.2.2.collectedSites else ∅
  let active (Q : Finset Lattice) (F : PathFamily) (j : Fin N) : Bool :=
    decide (j.val < F.card ∧ sites F j ⊆ Q)
  have hslot (F : PathFamily) (j : Fin N) (h : j.val < F.card) :
      sites F j = (F.equivFin.symm ⟨j.val, h⟩).val.2.2.collectedSites := dite_eq_left h
  let small (ω : Environment) (q : Σ u : Lattice, Σ d : ℕ × ℕ, Path u d) : Prop :=
    pathWeight ω q.2.2 <
      -2 * (∫ y, max (-y) 0 ∂μ) * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - (K - 1 : ℕ) * T - t
  let E₀ (Q : Finset Lattice) := {ω : Environment | ∃ q ∈ paths (mask ω),
    q.2.2.collectedSites ⊆ Q ∧ small ω q}
  have hlocal (Q : Finset Lattice) : MeasurableSet (E₀ Q) ∧ (environmentLaw μ).real (E₀ Q) ≤
      N * ((2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3)))) := by
    have hslots (a : Lattice → Bool) (j : Fin N) (h : active Q (paths a) j = true) :
        ∃ q ∈ paths a, sites (paths a) j = q.2.2.collectedSites := by
      have hindex : j.val < (paths a).card := (of_decide_eq_true h).1
      let q := (paths a).equivFin.symm ⟨j.val, hindex⟩
      exact ⟨q.val, q.property, hslot _ _ _⟩
    have hcore := global_mask_family_weight_failure_le μ T p b t hp hT hthreshold hb ht
      hmoment Q n N K hK (Fintype.card_fin N).le
      (fun a j => active Q (paths a) j) (fun a j => sites (paths a) j)
      (fun a j h => by
        obtain ⟨q, hq, hqsites⟩ := hslots a j h
        rw [hqsites, Path.collectedSites_card]
        exact hlen a q hq)
      (fun a j h => (of_decide_eq_true h).2)
      (fun a j h => by
        obtain ⟨q, hq, hqsites⟩ := hslots a j h
        rw [hqsites]
        exact hgood a q hq)
      (fun j s => hpaths (t := {F | active Q F j = true ∧ sites F j = s}) trivial)
    have hevent : E₀ Q = {ω : Environment | ∃ j : Fin N, active Q (paths (mask ω)) j = true ∧
        ∑ z ∈ sites (paths (mask ω)) j, ω z <
          -2 * (∫ y, max (-y) 0 ∂μ) * (sites (paths (mask ω)) j).card - (K - 1 : ℕ) * T - t} := by
      ext ω
      constructor
      · rintro ⟨q, hq, hsub, hw⟩
        let i := (paths (mask ω)).equivFin ⟨q, hq⟩
        let j : Fin N := ⟨i.val, i.isLt.trans_le (hcard (mask ω))⟩
        have hj : sites (paths (mask ω)) j = q.2.2.collectedSites := by
          rw [hslot _ _ i.isLt]
          exact congrArg (fun r => r.val.2.2.collectedSites)
            ((paths (mask ω)).equivFin.symm_apply_apply ⟨q, hq⟩)
        have hjs : sites (paths (mask ω)) j ⊆ Q := by rwa [hj]
        refine ⟨j, decide_eq_true ⟨i.isLt, hjs⟩, ?_⟩
        rw [hj, Path.collectedSites_card, ← Path.pathWeight_eq_sum_collectedSites]
        exact hw
      · rintro ⟨j, h, hw⟩
        obtain ⟨q, hq, hqsites⟩ := hslots (mask ω) j h
        have hsub : sites (paths (mask ω)) j ⊆ Q := (of_decide_eq_true h).2
        rw [hqsites, Path.collectedSites_card, ← Path.pathWeight_eq_sum_collectedSites] at hw
        rw [hqsites] at hsub
        exact ⟨q, hq, hsub, hw⟩
    rw [hevent]
    exact hcore
  have heq : E = ⋃ Q : Finset Lattice, E₀ Q := by
    ext ω
    constructor
    · rintro ⟨q, hq, hw⟩
      exact Set.mem_iUnion.mpr ⟨q.2.2.collectedSites, q, hq, fun _ hz => hz, hw⟩
    · intro h
      obtain ⟨Q, q, hq, _, hw⟩ := Set.mem_iUnion.mp h
      exact ⟨q, hq, hw⟩
  have hmono : Monotone E₀ := by
    intro Q R hQR ω hω
    obtain ⟨q, hq, hsub, hw⟩ := hω
    exact ⟨q, hq, hsub.trans hQR, hw⟩
  have hnonneg := measureReal_nonneg.trans (hlocal ∅).2
  rw [heq]
  refine ⟨MeasurableSet.iUnion fun Q => (hlocal Q).1, ?_⟩
  rw [measureReal_def, hmono.directed_le.measure_iUnion]
  exact ENNReal.toReal_le_of_le_ofReal hnonneg <| iSup_le fun Q =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnonneg).2 (hlocal Q).2

end LPPDifferentiability.Paper
