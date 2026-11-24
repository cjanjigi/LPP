/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.StairGeometry.Reach
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Differentiability.FinalDraft.Contour.Count
import Differentiability.FinalDraft.Contour.Existence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! The finite-reach bound from the final draft's square contours. The cycle's label set
is computed directly on the unrooted cycle, so each event in the union uses fixed sites. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability.StairGeometry

private abbrev Edge := Lattice × Lattice

private def cycleCells (p : Edge → Prop) [DecidablePred p] (label : Edge → Lattice)
    (c : Cycle Edge) : Finset Lattice :=
  (c.toFinset.filter p).image label

private theorem mem_cycleCells {p : Edge → Prop} [DecidablePred p] {label : Edge → Lattice}
    {m : ℕ} {v : Fin (m + 1) → Lattice} {w : Lattice} :
    w ∈ cycleCells p label (squareCircuitCycle v) ↔
      ∃ i : Fin m, p (squareCircuitEdge v i) ∧ label (squareCircuitEdge v i) = w := by
  simp only [cycleCells, squareCircuitCycle, Cycle.coe_toFinset, Finset.mem_image,
    Finset.mem_filter, List.mem_toFinset, List.mem_ofFn]
  aesop

private def forwardCells (c : Cycle Edge) : Finset Lattice :=
  cycleCells (fun e => e.2 - e.1 = (0, 1) ∨ e.2 - e.1 = (-1, 0)) dualEdgeLeftCellCode c

private def backwardCells (c : Cycle Edge) : Finset Lattice :=
  cycleCells (fun e => e.2 - e.1 = (0, -1) ∨ e.2 - e.1 = (1, 0)) dualEdgeRightCellCode c

private theorem forwardCells_eq {m : ℕ} {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v) :
    forwardCells (squareCircuitCycle v) = squareCircuitForwardCells hc := by
  ext w
  rw [forwardCells, mem_cycleCells]
  simp only [squareCircuitForwardCells, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, squareCircuitEdge, dualEdgeLeftCell]

private theorem backwardCells_eq {m : ℕ} {v : Fin (m + 1) → Lattice} (hc : IsSquareCircuit v) :
    backwardCells (squareCircuitCycle v) = squareCircuitBackwardCells hc := by
  ext w
  rw [backwardCells, mem_cycleCells]
  simp only [squareCircuitBackwardCells, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, squareCircuitEdge, dualEdgeRightCell]

private theorem four_mul_le_of_area {K m n : ℕ} (hcard : K ^ 2 ≤ n) (harea : 16 * n ≤ m ^ 2) :
    4 * K ≤ m := by
  by_contra! h
  have hsq := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
  rw [mul_pow] at hsq
  omega

private theorem forward_bad_contour {K : ℕ} {ω : Environment} {T : ℝ} {z : Lattice}
    (hcard : K ^ 2 ≤ (reachSet ω T z).ncard) (hfin : (reachSet ω T z).Finite) :
    ∃ (m : ℕ) (v : Fin (m + 1) → Lattice), 4 * K ≤ m ∧ IsSquareCircuit v ∧
      SquareCircuitHitsRay z v ∧ m ≤ 4 * (forwardCells (squareCircuitCycle v)).card ∧
      ∀ w ∈ forwardCells (squareCircuitCycle v), ω w < -T := by
  obtain ⟨S, hS⟩ := hfin.exists_finset_coe
  have hz : z ∈ S := Finset.mem_coe.mp (hS.symm ▸ mem_reach_self ω T z)
  obtain ⟨m, v, hc, _, _, ⟨hcount, hlabels⟩, _, harea, hray⟩ :=
    (exists_square_contour S (reach_connected hS) z hz).1
  rw [← hS, Set.ncard_coe_finset] at hcard
  refine ⟨m, v, four_mul_le_of_area hcard harea, hc, hray, ?_, ?_⟩
  · rwa [forwardCells_eq hc]
  · intro w hw
    rw [forwardCells_eq hc] at hw
    obtain ⟨hwS, hstep⟩ := hlabels w hw
    have hreach : w ∈ reachSet ω T z := hS ▸ Finset.mem_coe.mpr hwS
    by_contra! hgood
    rcases hstep with h | h
    · exact h (Finset.mem_coe.mp (hS.symm ▸ reach_step hreach hgood (1, 0) (Or.inl rfl)))
    · exact h (Finset.mem_coe.mp (hS.symm ▸ reach_step hreach hgood (0, 1) (Or.inr rfl)))

private theorem backward_bad_contour {K : ℕ} {ω : Environment} {T : ℝ} {z : Lattice}
    (hcard : K ^ 2 ≤ (reachBackSet ω T z).ncard) (hfin : (reachBackSet ω T z).Finite) :
    ∃ (m : ℕ) (v : Fin (m + 1) → Lattice), 4 * K ≤ m ∧ IsSquareCircuit v ∧
      SquareCircuitHitsRay z v ∧ m ≤ 4 * (backwardCells (squareCircuitCycle v)).card ∧
      ∀ w ∈ backwardCells (squareCircuitCycle v), ω w < -T := by
  obtain ⟨S, hS⟩ := hfin.exists_finset_coe
  have hz : z ∈ S := Finset.mem_coe.mp (hS.symm ▸ mem_reachBack_self ω T z)
  obtain ⟨m, v, hc, _, _, _, ⟨hcount, hlabels⟩, harea, hray⟩ :=
    (exists_square_contour S (reachBack_connected hS) z hz).1
  rw [← hS, Set.ncard_coe_finset] at hcard
  refine ⟨m, v, four_mul_le_of_area hcard harea, hc, hray, ?_, ?_⟩
  · rwa [backwardCells_eq hc]
  · intro w hw
    rw [backwardCells_eq hc] at hw
    obtain ⟨hwS, hstep⟩ := hlabels w hw
    by_contra! hgood
    apply hwS
    apply Finset.mem_coe.mp
    rw [hS]
    rcases hstep with h | h
    · exact reachBack_step (1, 0) (Or.inl rfl) (hS ▸ Finset.mem_coe.mpr h) hgood
    · exact reachBack_step (0, 1) (Or.inr rfl) (hS ▸ Finset.mem_coe.mpr h) hgood

private theorem all_bad_measureReal (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (S : Finset Lattice) :
    (environmentLaw μ).real {ω : Environment | ∀ w ∈ S, ω w < -T} =
      (μ.real (Iio (-T))) ^ S.card := by
  classical
  let I := {w : Lattice // w ∈ S}
  let coords : Environment → I → ℝ := fun ω i => ω i.1
  let box : Set (I → ℝ) := Set.univ.pi fun _ => Iio (-T)
  have hcoords : Measurable coords := measurable_finite_environment_coordinates Subtype.val
  have hbox : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Iio
  have hpre : coords ⁻¹' box = {ω : Environment | ∀ w ∈ S, ω w < -T} := by
    ext ω
    simp only [coords, box, mem_preimage, mem_pi, mem_univ, true_implies, mem_Iio, mem_ofPred_eq]
    exact ⟨fun h w hw => h ⟨w, hw⟩, fun h i => h i.1 i.2⟩
  rw [← hpre, ← map_measureReal_apply hcoords hbox]
  have hlaw : (environmentLaw μ).map coords = Measure.pi (fun _ : I => μ) :=
    environmentLaw_map_finite_coordinates μ Subtype.val Subtype.val_injective
  rw [hlaw, measureReal_def, show box = Set.univ.pi (fun _ : I => Iio (-T)) from rfl,
    Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rfl

private theorem measureReal_iUnion_le_tsum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : ℕ → Set Ω) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (hs : Summable t)
    (hE : ∀ n, P.real (E n) ≤ t n) : P.real (⋃ n, E n) ≤ ∑' n, t n := by
  have hEach (n : ℕ) : P (E n) ≤ ENNReal.ofReal (t n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E n))]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have hUnion : P (⋃ n, E n) ≤ ENNReal.ofReal (∑' n, t n) :=
    calc _ ≤ ∑' n, P (E n) := measure_iUnion_le E
      _ ≤ ∑' n, ENNReal.ofReal (t n) := ENNReal.tsum_le_tsum hEach
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg ht hs).symm
  simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg ht)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hUnion

private theorem contour_term_le (K j : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ (1 / 12 : ℝ) ^ 4) :
    let m := 4 * K + j
    (m : ℝ) * 3 ^ (m - 1) * p ^ ((m : ℝ) / 4) ≤
      (6 : ℝ) ^ (4 * K) * p ^ K * (1 / 2 : ℝ) ^ j := by
  intro m
  have hcount : (m : ℝ) * 3 ^ (m - 1) ≤ (6 : ℝ) ^ m := by
    have h₁ : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
    have h₂ : (3 : ℝ) ^ (m - 1) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    calc _ ≤ (2 : ℝ) ^ m * 3 ^ m := mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hquarter : p ^ (1 / 4 : ℝ) ≤ 1 / 12 :=
    (Real.rpow_le_rpow hp0 hp (by norm_num)).trans_eq (by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num)
  have hexp : (m : ℝ) / 4 = (K : ℝ) + (1 / 4 : ℝ) * j := by
    dsimp [m]; push_cast; ring
  calc
    _ ≤ (6 : ℝ) ^ m * p ^ ((m : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hp0 _)
    _ = (6 : ℝ) ^ (4 * K) * p ^ K * (6 * p ^ (1 / 4 : ℝ)) ^ j := by
      rw [hexp, Real.rpow_add_of_nonneg hp0 (by positivity) (by positivity), Real.rpow_natCast,
        Real.rpow_mul_natCast hp0, mul_pow]
      dsimp [m]
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) j) (by positivity)

/-- Use the union bound over cycles of each length, then over lengths. Filtering on the
number of distinct labels preserves the contour count and never uses the environment. -/
private theorem measureReal_bad_contours_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (z : Lattice) (K : ℕ) (labels : Cycle Edge → Finset Lattice)
    (hp : μ.real (Iio (-T)) ≤ (1 / 12 : ℝ) ^ 4) :
    (environmentLaw μ).real {ω : Environment |
      ∃ (m : ℕ) (v : Fin (m + 1) → Lattice), 4 * K ≤ m ∧ IsSquareCircuit v ∧
        SquareCircuitHitsRay z v ∧ m ≤ 4 * (labels (squareCircuitCycle v)).card ∧
        ∀ w ∈ labels (squareCircuitCycle v), ω w < -T} ≤
      (2 * (6 : ℝ) ^ (4 * K)) * (μ.real (Iio (-T))) ^ K := by
  classical
  choose C hC hcard using exists_finset_square_circuits_hitting_ray z
  let p := μ.real (Iio (-T))
  let m (j : ℕ) := 4 * K + j
  let D (j : ℕ) := (C (m j)).filter fun c => m j ≤ 4 * (labels c).card
  let bad (c : Cycle Edge) : Set Environment := {ω | ∀ w ∈ labels c, ω w < -T}
  let E (j : ℕ) : Set Environment := ⋃ c ∈ D j, bad c
  let t (j : ℕ) := (6 : ℝ) ^ (4 * K) * p ^ K * (1 / 2 : ℝ) ^ j
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := hp.trans (by norm_num)
  have hsub : {ω : Environment | ∃ (l : ℕ) (v : Fin (l + 1) → Lattice),
      4 * K ≤ l ∧ IsSquareCircuit v ∧ SquareCircuitHitsRay z v ∧
      l ≤ 4 * (labels (squareCircuitCycle v)).card ∧
      ∀ w ∈ labels (squareCircuitCycle v), ω w < -T} ⊆ ⋃ j, E j := by
    rintro ω ⟨l, v, hk, hc, hhit, hl, hb⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    apply mem_iUnion.mpr
    refine ⟨j, mem_iUnion.mpr ⟨squareCircuitCycle v, mem_iUnion.mpr ⟨?_, hb⟩⟩⟩
    exact Finset.mem_filter.mpr ⟨(hC _ _).mpr ⟨v, hc, hhit, rfl⟩, hl⟩
  have hE (j : ℕ) : (environmentLaw μ).real (E j) ≤ t j := by
    have hprob (c : Cycle Edge) (hc : c ∈ D j) :
        (environmentLaw μ).real (bad c) ≤ p ^ ((m j : ℝ) / 4) := by
      have hcount : (m j : ℝ) ≤ 4 * ((labels c).card : ℝ) :=
        by exact_mod_cast (Finset.mem_filter.mp hc).2
      change (environmentLaw μ).real {ω : Environment | ∀ w ∈ labels c, ω w < -T} ≤ _
      rw [all_bad_measureReal μ T, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hp0 hp1 (by positivity) (by linarith)
    have hD : ((D j).card : ℝ) ≤ (m j : ℝ) * 3 ^ (m j - 1) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (hcard (m j))
    calc
      _ ≤ ∑ c ∈ D j, (environmentLaw μ).real (bad c) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ D j, p ^ ((m j : ℝ) / 4) := Finset.sum_le_sum hprob
      _ = ((D j).card : ℝ) * p ^ ((m j : ℝ) / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m j : ℝ) * 3 ^ (m j - 1) * p ^ ((m j : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hp0 _)
      _ ≤ t j := contour_term_le K j p hp0 hp
  calc
    _ ≤ (environmentLaw μ).real (⋃ j, E j) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑' j, t j := measureReal_iUnion_le_tsum _ _ _ (fun j => by dsimp [t]; positivity)
      (summable_geometric_two.mul_left _) hE
    _ = _ := by simp only [t]; rw [tsum_mul_left, tsum_geometric_two]; ring

/-- The forward and backward finite-reach events with at least `K₃²` vertices have probability
at most a constant times `p_T ^ K₃`, uniformly in the site. Final draft, Lemma `lem:stair-geometry`. -/
theorem finite_reach_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (z : Lattice) (K₃ : ℕ) (hp : μ.real (Iio (-T)) ≤ (1 / 12 : ℝ) ^ 4) :
    (environmentLaw μ).real {ω : Environment |
      K₃ ^ 2 ≤ (reachSet ω T z).ncard ∧ (reachSet ω T z).Finite} ≤
        (2 * (6 : ℝ) ^ (4 * K₃)) * (μ.real (Iio (-T))) ^ K₃ ∧
    (environmentLaw μ).real {ω : Environment |
      K₃ ^ 2 ≤ (reachBackSet ω T z).ncard ∧ (reachBackSet ω T z).Finite} ≤
        (2 * (6 : ℝ) ^ (4 * K₃)) * (μ.real (Iio (-T))) ^ K₃ := by
  exact ⟨(measureReal_mono (fun _ h => forward_bad_contour h.1 h.2) (measure_ne_top _ _)).trans
      (measureReal_bad_contours_le μ T z K₃ forwardCells hp),
    (measureReal_mono (fun _ h => backward_bad_contour h.1 h.2) (measure_ne_top _ _)).trans
      (measureReal_bad_contours_le μ T z K₃ backwardCells hp)⟩

end LPPDifferentiability.StairGeometry
