/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPairNormalization
public import Busemann.Process.RightmostThreeRayEvent
public import Busemann.Process.RightmostThreeRayBoundaryEvent
public import ProbabilityBasics.Probability.FiniteBoundaryThreshold
import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! A single positive three-ray event with the old west and north weight bounds. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology BigOperators

namespace LPP.Busemann

private theorem strict_west_boundary_sum
    (w : LPPDifferentiability.Environment) (K : ℝ) (ell M2 : ℕ)
    (hTop : ell < M2)
    (hLower : ∀ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), K ≤ w (0, j))
    (hStrict : ∃ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), K < w (0, j)) :
    (((M2 : ℤ) - (ell : ℤ) : ℤ) : ℝ) * K <
      ∑ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), w (0, j) := by
  have hcardZ : ((Finset.Ico (ell : ℤ) (M2 : ℤ)).card : ℤ) =
      (M2 : ℤ) - (ell : ℤ) :=
    Int.card_Ico_of_le _ _ (by exact_mod_cast hTop.le)
  have hcardR : ((Finset.Ico (ell : ℤ) (M2 : ℤ)).card : ℝ) =
      ((M2 : ℤ) - (ell : ℤ) : ℤ) := by exact_mod_cast hcardZ
  have hSum := Finset.sum_lt_sum hLower hStrict
  simpa only [Finset.sum_const, nsmul_eq_mul, hcardR] using hSum

/-- From a positive nonintersection event for arbitrary two actual rays, select
one positive event with all three-ray boundary geometry and weight inequalities.
The two attained-essential-infimum cases are handled internally. This is the
old-event selection of GRS, arXiv:1510.00860v1, Appendix A, A.8/A.9 and Case 2. -/
theorem exists_positive_three_ray_boundary_weight_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → LPPDifferentiability.Environment)
    (hzero : ∀ ω : Ω, T 0 ω = ω)
    (hadd : ∀ z w : Lattice, ∀ ω : Ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x : Lattice, ∀ ω : Ω,
      weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P)
    (a b : Lattice)
    (hPositive : 0 < P {ω : Ω | ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) a r ≠
        rightmostCocyclePath (fun x y => B x y ω) b s})
    :
    ∃ (m ell M1 M2 : ℕ) (K : ℝ) (A : Set Ω),
      0 < m ∧ m < ell ∧ 0 < M1 ∧ ell < M2 ∧
      0 < μ (Set.Iic K) ∧ MeasurableSet A ∧ 0 < P A ∧
      ∀ ω ∈ A,
        (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
          rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) r ≠
          rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (ell : ℤ)) =
          (1, (ell : ℤ)) ∧
        rightmostCocyclePath (fun x y => B x y ω) 0 (M1 + M2) =
          ((M1 : ℤ), (M2 : ℤ)) ∧
        rightmostCocyclePath (fun x y => B x y ω) 0 (M1 + M2 - 1) =
          ((M1 : ℤ), ((M2 : ℤ) - 1)) ∧
        (∃ (a1 a2 H : ℤ) (nM nU nEast : ℕ),
          0 < a1 ∧ a1 < a2 ∧ a2 < (M1 : ℤ) ∧ (ell : ℤ) ≤ H ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) nM =
            (a2, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) nU =
            (a1, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y ω) (0, (ell : ℤ)) nEast =
            ((M1 : ℤ), H)) ∧
        (∀ j : ℤ, 0 ≤ j → j < (ell : ℤ) → K ≤ weights ω (0, j)) ∧
        (((M2 : ℤ) - (ell : ℤ) : ℤ) : ℝ) * K <
          ∑ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), weights ω (0, j) ∧
        (∀ i : ℤ, 0 ≤ i → i ≤ (M1 : ℤ) → K ≤ weights ω (i, (M2 : ℤ))) := by
  classical
  -- The original environment marginal gives every scalar coordinate law.
  have hCoordMeas (z : Lattice) : Measurable (fun ω => weights ω z) :=
    (measurable_environment_eval z).comp hWeightsMeas
  have hCoordLaw (z : Lattice) : P.map (fun ω => weights ω z) = μ := by
    calc
      P.map (fun ω => weights ω z) =
          (P.map weights).map (fun w : LPPDifferentiability.Environment => w z) :=
        (Measure.map_map (measurable_environment_eval z) hWeightsMeas).symm
      _ = μ := by rw [hMarginal, environmentLaw_map_eval]
  by_cases hAtom : ∃ K : ℝ, (∀ᵐ t ∂μ, K ≤ t) ∧ 0 < μ {K}
  · obtain ⟨K, hLower, hAtomPos⟩ := hAtom
    -- Nondegeneracy supplies the strict upper tail above the attained minimum.
    have hHigh : 0 < μ (Set.Ioi K) := by
      apply pos_iff_ne_zero.mpr
      intro hZero
      have hUpper : ∀ᵐ (t : ℝ) ∂μ, t ≤ K := by
        apply ae_iff.mpr
        have hSet : {t : ℝ | ¬ t ≤ K} = Set.Ioi K := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_Ioi, not_le]
        rw [hSet]
        exact hZero
      have hConstant : ({K} : Set ℝ) =ᵐ[μ] Set.univ := by
        filter_upwards [hLower, hUpper] with t ht₁ ht₂
        apply propext
        exact ⟨fun _ => Set.mem_univ t, fun _ => le_antisymm ht₂ ht₁⟩
      have hMass : μ {K} = 1 := by
        rw [measure_congr hConstant, measure_univ]
      exact (ne_of_lt (hμ K)) hMass
    have hCutPos : 0 < μ (Set.Iic K) :=
      lt_of_lt_of_le hAtomPos (measure_mono (Set.singleton_subset_iff.mpr (by simp)))
    obtain ⟨m, hm, hDMeas, hDPos⟩ :=
      exists_positive_normalized_rightmost_pair_with_high_weight μ hμ hmoment P T weights
        hzero hadd hShift hWeightsMeas hMarginal hWeightsShift B hB hRec hInt₁ hInt₂
        a b hPositive K hHigh
    let D : Set Ω := {ω |
      (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
        (0, (m : ℤ)) + (1, 0) ∧
      ∃ r : ℕ, m < r ∧ K < weights ω (0, (r : ℤ))}
    obtain ⟨i, hmi, E, hEMeas, hEPos, hSub, hGeometry⟩ :=
      exists_positive_three_ray_event_of_recurrence P T hzero hadd hShift B hB m hm
        D hDMeas hDPos (fun _ hω => hω.1) (fun _ hω => hω.2.1)
        (fun _ hω => by simpa only [Prod.mk_add_mk, zero_add, add_zero] using hω.2.2.1)
    let ell := i + m
    have hmell : m < ell := by dsimp only [ell]; omega
    -- The shifted occurrence retained by recurrence gives a high point above ell.
    have hHighPoint : ∀ ω ∈ E, ∃ r : ℕ, ell < r ∧ K < weights ω (0, (r : ℤ)) := by
      intro ω hω
      obtain ⟨r, hmr, hr⟩ := (hSub hω).2.2.2.2
      refine ⟨i + r, by dsimp only [ell]; omega, ?_⟩
      simpa only [hWeightsShift, Prod.mk_add_mk, zero_add, ← Nat.cast_add] using hr
    let F (r : ℕ) : Set Ω := E ∩ {ω | ell < r ∧ K < weights ω (0, (r : ℤ))}
    have hFMeas (r : ℕ) : MeasurableSet (F r) := by
      by_cases hr : ell < r
      · have hh : MeasurableSet {ω : Ω | K < weights ω (0, (r : ℤ))} :=
          measurableSet_lt measurable_const (hCoordMeas (0, (r : ℤ)))
        exact hEMeas.inter (by simpa only [hr, true_and] using hh)
      · have hEmpty : F r = ∅ := by ext ω; simp only [F, hr, false_and, Set.ofPred_false, Set.inter_empty]
        rw [hEmpty]
        exact MeasurableSet.empty
    have hCover : E ⊆ ⋃ r : ℕ, F r := by
      intro ω hω
      obtain ⟨r, hr, hHighR⟩ := hHighPoint ω hω
      exact Set.mem_iUnion.mpr ⟨r, hω, hr, hHighR⟩
    have hUnionPos : 0 < P (⋃ r : ℕ, F r) :=
      lt_of_lt_of_le hEPos (measure_mono hCover)
    obtain ⟨r, hrPos⟩ := exists_measure_pos_of_not_measure_iUnion_null hUnionPos.ne'
    obtain ⟨ω₀, hω₀⟩ := nonempty_of_measure_ne_zero hrPos.ne'
    have hr : ell < r := hω₀.2.1
    let M2 := r + 1
    have hTop : ell < M2 := by dsimp only [M2]; omega
    -- Intersect with one measurable all-lattice lower-bound event.
    let G : Set Ω := {ω | ∀ z : Lattice, K ≤ weights ω z}
    have hGMeas : MeasurableSet G := by
      simp only [G, Set.ofPred_forall]
      exact MeasurableSet.iInter fun z => measurableSet_le measurable_const (hCoordMeas z)
    have hGAE : ∀ᵐ ω ∂P, ω ∈ G := by
      apply ae_all_iff.mpr
      intro z
      have hMapped : ∀ᵐ t ∂P.map (fun ω => weights ω z), K ≤ t := by
        rw [hCoordLaw z]
        exact hLower
      exact (Measure.tendsto_ae_map (hCoordMeas z).aemeasurable).eventually hMapped
    let E' := G ∩ F r
    have hE'Meas : MeasurableSet E' := hGMeas.inter (hFMeas r)
    have hE'Pos : 0 < P E' := by
      have hMass : P E' = P (F r) := Measure.measure_inter_eq_of_ae hGAE
      rw [hMass]
      exact hrPos
    obtain ⟨M1, hM1, A, hAMeas, hAPos, hASub, hHits⟩ :=
      exists_positive_three_ray_boundary_event μ hμ hmoment P T weights hzero hadd hShift
        hWeightsMeas hMarginal hWeightsShift B hB hRec hInt₁ hInt₂ m ell M2 hm hmell
        hTop E' hE'Meas hE'Pos (fun ω hω => hGeometry ω hω.2.1)
    refine ⟨m, ell, M1, M2, K, A, hm, hmell, hM1, hTop, hCutPos, hAMeas, hAPos, ?_⟩
    intro ω hω
    have hOld := hASub hω
    obtain ⟨hLM, hMU, hEL, hEU⟩ := hGeometry ω hOld.2.1
    obtain ⟨hNorth, hPred, hWitness⟩ := hHits ω hω
    have hTail := strict_west_boundary_sum (weights ω) K ell M2 hTop
      (fun j _ => hOld.1 (0, j))
      ⟨(r : ℤ), Finset.mem_Ico.mpr ⟨by exact_mod_cast hr.le, by dsimp only [M2]; omega⟩,
        hOld.2.2.2⟩
    exact ⟨hLM, hMU, hEL, hEU, hNorth, hPred, hWitness,
      fun j _ _ => hOld.1 (0, j), hTail, fun j _ _ => hOld.1 (j, (M2 : ℤ))⟩
  · -- Without an attained minimum, choose the whole geometry before the cut.
    obtain ⟨m, hm, hDMeas, hDPos⟩ :=
      exists_positive_normalized_rightmost_pair μ hμ hmoment P T weights hzero hadd hShift
        hWeightsMeas hMarginal hWeightsShift B hB hRec hInt₁ hInt₂ a b hPositive
    let D : Set Ω := {ω |
      (∀ r s : ℕ, rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
      rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
        (0, (m : ℤ)) + (1, 0)}
    obtain ⟨i, hmi, E, hEMeas, hEPos, _, hGeometry⟩ :=
      exists_positive_three_ray_event_of_recurrence P T hzero hadd hShift B hB m hm
        D hDMeas hDPos (fun _ hω => hω.1) (fun _ hω => hω.2.1)
        (fun _ hω => by simpa only [Prod.mk_add_mk, zero_add, add_zero] using hω.2.2)
    let ell := i + m
    have hmell : m < ell := by dsimp only [ell]; omega
    let M2 := ell + 1
    have hTop : ell < M2 := by dsimp only [M2]; omega
    obtain ⟨M1, hM1, A, hAMeas, hAPos, hASub, hHits⟩ :=
      exists_positive_three_ray_boundary_event μ hμ hmoment P T weights hzero hadd hShift
        hWeightsMeas hMarginal hWeightsShift B hB hRec hInt₁ hInt₂ m ell M2 hm hmell
        hTop E hEMeas hEPos hGeometry
    let F : Finset Lattice :=
      (Finset.Icc (0 : ℤ) (M2 : ℤ)).image (fun j => (0, j)) ∪
        (Finset.Icc (0 : ℤ) (M1 : ℤ)).image (fun j => (j, (M2 : ℤ)))
    rcases ProbabilityBasics.exists_lower_bound_atom_or_positive_finite_boundary_cut μ P
      (fun z ω => weights ω z) hCoordMeas hCoordLaw A hAMeas hAPos F with
      hAttained | ⟨K, hCutPos, hCutEventPos⟩
    · exact (hAtom hAttained).elim
    · let A' := A ∩ {ω | ∀ z ∈ F, K < weights ω z}
      have hA'Meas : MeasurableSet A' := by
        apply hAMeas.inter
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_const (hCoordMeas z)
      refine ⟨m, ell, M1, M2, K, A', hm, hmell, hM1, hTop, hCutPos,
        hA'Meas, hCutEventPos, ?_⟩
      intro ω hω
      obtain ⟨hLM, hMU, hEL, hEU⟩ := hGeometry ω (hASub hω.1)
      obtain ⟨hNorth, hPred, hWitness⟩ := hHits ω hω.1
      have hWest (j : ℤ) (hj : 0 ≤ j) (hjTop : j ≤ (M2 : ℤ)) :
          K < weights ω (0, j) := by
        apply hω.2 (0, j)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj, hjTop⟩, rfl⟩)
      have hNorthWeight (j : ℤ) (hj : 0 ≤ j) (hjTop : j ≤ (M1 : ℤ)) :
          K < weights ω (j, (M2 : ℤ)) := by
        apply hω.2 (j, (M2 : ℤ))
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj, hjTop⟩, rfl⟩)
      have hTail := strict_west_boundary_sum (weights ω) K ell M2 hTop
        (fun j hj => (hWest j (by have hh := Finset.mem_Ico.mp hj; omega)
          (Finset.mem_Ico.mp hj).2.le).le)
        ⟨(ell : ℤ), Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hTop⟩,
          hWest (ell : ℤ) (by omega) (by exact_mod_cast hTop.le)⟩
      exact ⟨hLM, hMU, hEL, hEU, hNorth, hPred, hWitness,
        fun j hj hje => (hWest j hj (by dsimp only [M2]; omega)).le,
        hTail, fun j hj hjM => (hNorthWeight j hj hjM).le⟩

end LPP.Busemann
