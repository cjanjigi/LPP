/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathCoordinateEscape
public import Busemann.Process.RightmostPathVerticalOrder
public import Busemann.Process.RightmostPathMeasurability
public import LPP_Foundations.Model.Paths.BoundaryHits
import Mathlib.Tactic

/-! Positive measurable selection of actual three-ray boundary hits. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- On a positive three-ray event, select one deterministic horizontal
coordinate and a positive measurable subevent carrying all actual north and
east boundary hits on the same sample. The height is fixed before the
coordinate is selected. This is the geometric selection in GRS
arXiv:1510.00860v1, Appendix A, lines 1556–1580. -/
theorem exists_positive_three_ray_boundary_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → Environment)
    (hzero : ∀ ω, T 0 ω = ω)
    (hadd : ∀ z w ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x ω, weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P)
    (m ell M2 : ℕ) (hm : 0 < m) (hmell : m < ell) (hTop : ell < M2)
    (E : Set Ω) (hEmeas : MeasurableSet E) (hEpos : 0 < P E)
    (hGeometry : ∀ ω ∈ E,
      (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
      (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) s) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) (0, (ell : ℤ)) =
        (1, (ell : ℤ))) :
    ∃ M1 : ℕ, 0 < M1 ∧ ∃ A : Set Ω, MeasurableSet A ∧ 0 < P A ∧ A ⊆ E ∧
      ∀ ω ∈ A,
        rightmostCocyclePath (fun x y => B x y ω) 0 (M1 + M2) =
          ((M1 : ℤ), (M2 : ℤ)) ∧
        rightmostCocyclePath (fun x y => B x y ω) 0 (M1 + M2 - 1) =
          ((M1 : ℤ), ((M2 : ℤ) - 1)) ∧
        ∃ (a1 a2 H : ℤ) (nM nU nEast : ℕ),
          0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) nM =
            (a2, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) nU =
            (a1, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) nEast =
            ((M1 : ℤ), H) := by
  classical
  let ray (ω : Ω) (x : Lattice) (n : ℕ) :=
    rightmostCocyclePath (fun y z => B y z ω) x n
  have hBmeas (x y : Lattice) : Measurable (B x y) := by
    have hmap : Measurable (fun ω : Ω => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hmap
  have hRayMeas (x : Lattice) (n : ℕ) : Measurable (fun ω => ray ω x n) := by
    exact measurable_rightmostCocyclePath B hBmeas x n
  -- Each candidate event records every hit on the same sample.
  let A (M1 : ℕ) : Set Ω := E ∩ {ω |
    0 < M1 ∧
    ray ω 0 (M1 + M2) = ((M1 : ℤ), (M2 : ℤ)) ∧
    ray ω 0 (M1 + M2 - 1) = ((M1 : ℤ), ((M2 : ℤ) - 1)) ∧
    ∃ (a1 a2 H : ℤ) (nM nU nEast : ℕ),
      0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
      ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) ∧
      ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) ∧
      ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)}
  have hWitnessMeas (M1 : ℕ) (a1 a2 H : ℤ) (nM nU nEast : ℕ) :
      MeasurableSet {ω : Ω |
        0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
        ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)} := by
    by_cases hc : 0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H
    · have h1 : MeasurableSet {ω : Ω | ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ))} :=
        measurableSet_eq_fun (hRayMeas (0, (m : ℤ)) nM) measurable_const
      have h2 : MeasurableSet {ω : Ω | ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ))} :=
        measurableSet_eq_fun (hRayMeas (0, (ell : ℤ)) nU) measurable_const
      have h3 : MeasurableSet {ω : Ω | ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)} :=
        measurableSet_eq_fun (hRayMeas (0, (ell : ℤ)) nEast) measurable_const
      simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, true_and, Set.ofPred_and] using h1.inter (h2.inter h3)
    · have he : {ω : Ω |
        0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
        ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hh
        exact hc ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
      rw [he]
      exact MeasurableSet.empty
  have hAmeas (M1 : ℕ) : MeasurableSet (A M1) := by
    have hw : MeasurableSet {ω : Ω | ∃ (a1 a2 H : ℤ) (nM nU nEast : ℕ),
        0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
        ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) ∧
        ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun a1 => MeasurableSet.iUnion fun a2 =>
        MeasurableSet.iUnion fun H => MeasurableSet.iUnion fun nM =>
        MeasurableSet.iUnion fun nU => MeasurableSet.iUnion fun nEast =>
          hWitnessMeas M1 a1 a2 H nM nU nEast
    by_cases hM : 0 < M1
    · have h1 : MeasurableSet {ω : Ω | ray ω 0 (M1 + M2) = ((M1 : ℤ), (M2 : ℤ))} :=
        measurableSet_eq_fun (hRayMeas 0 (M1 + M2)) measurable_const
      have h2 : MeasurableSet {ω : Ω | ray ω 0 (M1 + M2 - 1) = ((M1 : ℤ), ((M2 : ℤ) - 1))} :=
        measurableSet_eq_fun (hRayMeas 0 (M1 + M2 - 1)) measurable_const
      have h : MeasurableSet {ω : Ω |
          0 < M1 ∧ ray ω 0 (M1 + M2) = ((M1 : ℤ), (M2 : ℤ)) ∧
          ray ω 0 (M1 + M2 - 1) = ((M1 : ℤ), ((M2 : ℤ) - 1)) ∧
          ∃ (a1 a2 H : ℤ) (nM nU nEast : ℕ),
            0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
            ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) ∧
            ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) ∧
            ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H)} := by
        simpa only [hM, true_and, Set.ofPred_and] using h1.inter (h2.inter hw)
      exact hEmeas.inter h
    · have he : A M1 = ∅ := by
        ext ω
        simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hω
        exact hM hω.2.1
      rw [he]
      exact MeasurableSet.empty
  -- The all-start escape event is fixed before all later choices.
  have hEscape := ae_rightmostCocyclePath_tendsto_coordinates_of_action
    μ hμ hmoment P T weights hzero hadd hShift hWeightsMeas hMarginal
    hWeightsShift B hB hRec hInt₁ hInt₂
  have hCover : {ω : Ω | ∀ x : Lattice,
      Tendsto (fun n => (ray ω x n).1) atTop atTop ∧
      Tendsto (fun n => (ray ω x n).2) atTop atTop} ∩ E ⊆ ⋃ M1 : ℕ, A M1 := by
    intro ω hω
    obtain ⟨hEsc, hωE⟩ := hω
    obtain ⟨hLM, hMU, hEastL, hEastU⟩ := hGeometry ω hωE
    let C : Lattice → Lattice → ℝ := fun x y => B x y ω
    have hStep (x : Lattice) (n : ℕ) : ray ω x (n + 1) = ray ω x n + (1, 0) ∨
        ray ω x (n + 1) = ray ω x n + (0, 1) := by
      simpa only [ray, rightmostCocyclePath, Function.iterate_succ_apply'] using
        rightmostCocycleSuccessor_step C (ray ω x n)
    have hLevel (x : Lattice) (n : ℕ) :
        (ray ω x n).1 + (ray ω x n).2 = x.1 + x.2 + (n : ℤ) := by
      induction n with
      | zero => simp [ray, rightmostCocyclePath]
      | succ n ih =>
        rcases hStep x n with h | h <;>
          simp only [h, Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
    have hXmono (x : Lattice) : Monotone (fun n => (ray ω x n).1) := by
      apply monotone_nat_of_le_succ
      intro n
      rcases hStep x n with h | h <;> simp only [h, Prod.fst_add] <;> omega
    have hYmono (x : Lattice) : Monotone (fun n => (ray ω x n).2) := by
      apply monotone_nat_of_le_succ
      intro n
      rcases hStep x n with h | h <;> simp only [h, Prod.snd_add] <;> omega
    have hTopZ : (ell : ℤ) < (M2 : ℤ) := by exact_mod_cast hTop
    have hmZ : (m : ℤ) < (ell : ℤ) := by exact_mod_cast hmell
    -- The first north hit of each actual ray has the prescribed height.
    obtain ⟨nL, hnL, hnLY, hnLStep, _⟩ :=
      up_right_path_first_north_arrival (ray ω 0) (hStep 0) (hEsc 0).2 (M2 : ℤ) (by
        simp [ray, rightmostCocyclePath]; omega)
    obtain ⟨nM, hnM, hnMY, _, _⟩ :=
      up_right_path_first_north_arrival (ray ω (0, (m : ℤ))) (hStep _) (hEsc _).2 (M2 : ℤ) (by
        simp [ray, rightmostCocyclePath]; omega)
    obtain ⟨nU, hnU, hnUY, _, _⟩ :=
      up_right_path_first_north_arrival (ray ω (0, (ell : ℤ))) (hStep _) (hEsc _).2 (M2 : ℤ) (by
        simp [ray, rightmostCocyclePath]; omega)
    let a1 : ℤ := (ray ω (0, (ell : ℤ)) nU).1
    let a2 : ℤ := (ray ω (0, (m : ℤ)) nM).1
    let M1 : ℕ := (ray ω 0 nL).1.toNat
    have hLfirst : ray ω 0 1 = (1, 0) := by
      simpa [ray, rightmostCocyclePath] using hEastL
    have hUfirst : ray ω (0, (ell : ℤ)) 1 = (1, (ell : ℤ)) := by
      simpa [ray, rightmostCocyclePath] using hEastU
    have hLpos : 0 < (ray ω 0 nL).1 := by
      have hh := hXmono 0 (show 1 ≤ nL by omega)
      dsimp only at hh
      rw [hLfirst] at hh
      simp only at hh
      omega
    have hUpos : 0 < a1 := by
      have hh := hXmono (0, (ell : ℤ)) (show 1 ≤ nU by omega)
      dsimp only at hh
      rw [hUfirst] at hh
      simp only at hh
      dsimp only [a1]
      omega
    have hM1cast : (M1 : ℤ) = (ray ω 0 nL).1 := Int.toNat_of_nonneg (by omega)
    have hM1pos : 0 < M1 := by omega
    have hLHit : ray ω 0 nL = ((M1 : ℤ), (M2 : ℤ)) := by
      apply Prod.ext
      · exact hM1cast.symm
      · exact hnLY
    have hMHit : ray ω (0, (m : ℤ)) nM = (a2, (M2 : ℤ)) := by
      apply Prod.ext
      · rfl
      · exact hnMY
    have hUHit : ray ω (0, (ell : ℤ)) nU = (a1, (M2 : ℤ)) := by
      apply Prod.ext
      · rfl
      · exact hnUY
    have hOrder := rightmostCocyclePath_height_order_and_north_hit_order
      C m ell hm hmell (M1 : ℤ) (M2 : ℤ) a1 a2 hTopZ nL nM nU
      hLHit hMHit hUHit hLM hMU
    have hIndex : nL = M1 + M2 := by
      have hh := hLevel 0 nL
      rw [hLHit] at hh
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hh
      omega
    have hPred : ray ω 0 (M1 + M2 - 1) = ((M1 : ℤ), ((M2 : ℤ) - 1)) := by
      have hh := hnLStep
      rw [hLHit, hIndex] at hh
      apply Prod.ext
      · have hx := congrArg Prod.fst hh
        simp only [Prod.fst_add] at hx
        omega
      · have hy := congrArg Prod.snd hh
        simp only [Prod.snd_add] at hy
        omega
    -- Actual horizontal escape supplies the upper ray's east hit.
    obtain ⟨nEast, hEastX, _, _, _⟩ :=
      up_right_path_last_east_departure (ray ω (0, (ell : ℤ))) (hStep _) (hEsc _).1
        (M1 : ℤ) (by simp [ray, rightmostCocyclePath])
    let H : ℤ := (ray ω (0, (ell : ℤ)) nEast).2
    have hH : (ell : ℤ) ≤ H := by
      have hh := hYmono (0, (ell : ℤ)) (Nat.zero_le nEast)
      simpa [H, ray, rightmostCocyclePath] using hh
    have hEastHit : ray ω (0, (ell : ℤ)) nEast = ((M1 : ℤ), H) := by
      apply Prod.ext
      · exact hEastX
      · rfl
    apply Set.mem_iUnion.mpr
    refine ⟨M1, hωE, hM1pos, ?_, hPred, a1, a2, H, nM, nU, nEast,
      hUpos, hOrder.2.2.2.1, hOrder.2.2.2.2, hH, hMHit, hUHit, hEastHit⟩
    simpa only [hIndex] using hLHit
  have hInter : P ({ω : Ω | ∀ x : Lattice,
      Tendsto (fun n => (ray ω x n).1) atTop atTop ∧
      Tendsto (fun n => (ray ω x n).2) atTop atTop} ∩ E) = P E := by
    apply Measure.measure_inter_eq_of_ae
    exact hEscape
  have hUnionPos : 0 < P (⋃ M1 : ℕ, A M1) := by
    rw [← hInter] at hEpos
    exact lt_of_lt_of_le hEpos (measure_mono hCover)
  obtain ⟨M1, hPositive⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero (ne_of_gt hPositive)
  refine ⟨M1, hω.2.1, A M1, hAmeas M1, hPositive, ?_, ?_⟩
  · exact Set.inter_subset_left
  · intro ω hω
    exact hω.2.2

end LPP.Busemann
