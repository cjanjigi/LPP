/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.CoalescingRightmostPaths
public import Busemann.Frozen.Definitions.OutsideSigma
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Process.RightmostBoundaryWeightEvent
import Busemann.Process.RightmostPathCorridorModification
import Busemann.Process.RightmostShieldedEventNull
import LPP_Foundations.Model.Path.ArrowOrder
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! Coalescence from the source finite-block conditional positivity criterion. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal BigOperators

namespace LPP.Busemann

/-- The original stationary recovering-cocycle model and its positive-cut
finite-block conditional probabilities give one almost-sure event of coalescence
for every signed starting pair, at aligned absolute levels and all future times.
This assembles GRS arXiv:1510.00860v1, Appendix A, Theorem A.1, Lemma A.2/A.4
and the stationary counting closure, reading lines 1406–1489 and 1517–1687. -/
theorem hasCoalescingRightmostPaths_of_finite_block_condExp
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → LPPDifferentiability.Environment)
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
    (hFiniteBlock : ∀ K : ℝ, 0 < μ (Set.Iic K) →
      ∀ V : Finset Lattice, ∀ᵐ s ∂P,
        0 < (MeasureTheory.condExp (outsideSigma weights B V) P
          (Set.indicator {s : Ω | ∀ z ∈ V, weights s z ≤ K}
            (fun _ => (1 : ℝ)))) s) :
    HasCoalescingRightmostPaths P B := by
  classical
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hSection : Measurable (fun s : Ω => ((x, y), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hSection
  let E (a b : Lattice) : Set Ω := {s | ∀ r t : ℕ,
    rightmostCocyclePath (fun x y => B x y s) a r ≠
      rightmostCocyclePath (fun x y => B x y s) b t}
  have hEMeas (a b : Lattice) : MeasurableSet (E a b) := by
    simp only [E, Set.ofPred_forall]
    exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun t =>
      (measurableSet_eq_fun (measurable_rightmostCocyclePath B hBMeas a r)
        (measurable_rightmostCocyclePath B hBMeas b t)).compl
  -- Positive nonintersection would produce a positive stationary shield event.
  have hPairNull (a b : Lattice) : P (E a b) = 0 := by
    by_contra hNonzero
    have hPositive : 0 < P (E a b) := pos_iff_ne_zero.mpr hNonzero
    obtain ⟨m, ell, M1, M2, K, A, hm, hmell, hM1, hTop,
      hCut, hAMeas, hAPos, hOld⟩ :=
      exists_positive_three_ray_boundary_weight_event μ hμ hmoment P T weights
        hzero hadd hShift hWeightsMeas hMarginal hWeightsShift
        B hB hRec hInt₁ hInt₂ a b hPositive
    have hGeometry : ∀ s ∈ A,
        (∀ r t : ℕ, rightmostCocyclePath (fun x y => B x y s) 0 r ≠
          rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) t) ∧
        (∀ r t : ℕ, rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) r ≠
          rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) t) ∧
        rightmostCocyclePath (fun x y => B x y s) 0 (M1 + M2) =
          ((M1 : ℤ), (M2 : ℤ)) ∧
        ∃ (a1 a2 H : ℤ) (nM nU nE : ℕ),
          rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) nM =
            (a2, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) nU =
            (a1, (M2 : ℤ)) ∧
          rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) nE =
            ((M1 : ℤ), H) := by
      intro s hs
      obtain ⟨hLM, hMU, _hEL, _hEU, hNorth, _hPred, hHits, _hWeights⟩ := hOld s hs
      obtain ⟨a1, a2, H, nM, nU, nE, _ha1, _ha12, _ha2, _hH,
        hNorthM, hNorthU, hEastU⟩ := hHits
      exact ⟨hLM, hMU, hNorth, a1, a2, H, nM, nU, nE,
        hNorthM, hNorthU, hEastU⟩
    have hWeights : ∀ s ∈ A,
        (∀ j : ℤ, 0 ≤ j → j < (ell : ℤ) → K ≤ weights s (0, j)) ∧
        ((((M2 : ℤ) - (ell : ℤ) : ℤ) : ℝ) * K <
          ∑ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), weights s (0, j)) ∧
        (∀ i : ℤ, 0 ≤ i → i ≤ (M1 : ℤ) → K ≤ weights s (i, (M2 : ℤ))) := by
      intro s hs
      exact (hOld s hs).2.2.2.2.2.2.2
    -- The weight-event producer's SAME K and positive cut discharge finite energy.
    obtain ⟨V, D, hDMeas, hDPos, _hOldAssociated, hNew⟩ :=
      exists_positive_shielded_ray_event_of_finite_block_condExp
        P weights hWeightsMeas B hBMeas hB.2.2 hRec K (hFiniteBlock K hCut)
        m ell M1 M2 hm hmell hM1 hTop A hAMeas hAPos hGeometry hWeights
    have hDZero : P D = 0 :=
      measure_shielded_rightmost_event_eq_zero P T hzero hadd hShift B hB.2.1
        M1 M2 D hDMeas (fun s hs => (hNew s hs).2.2.2)
    exact hDPos.ne' hDZero
  -- Countability gives ONE full event for all signed pairs before meeting choices.
  have hPairMeet (a b : Lattice) : ∀ᵐ s ∂P, ∃ r t : ℕ,
      rightmostCocyclePath (fun x y => B x y s) a r =
        rightmostCocyclePath (fun x y => B x y s) b t := by
    have hComplement : P (E a b)ᶜ = 1 := by
      rw [measure_compl (hEMeas a b) (by rw [hPairNull]; exact ENNReal.zero_ne_top),
        measure_univ, hPairNull, tsub_zero]
    have hNotAvoid : ∀ᵐ s ∂P, s ∈ (E a b)ᶜ :=
      (mem_ae_iff_prob_eq_one (hEMeas a b).compl).2 hComplement
    filter_upwards [hNotAvoid] with s hs
    change ¬ (∀ r t : ℕ,
      rightmostCocyclePath (fun x y => B x y s) a r ≠
        rightmostCocyclePath (fun x y => B x y s) b t) at hs
    push Not at hs
    exact hs
  have hCommon : ∀ᵐ s ∂P, ∀ a b : Lattice, ∃ r t : ℕ,
      rightmostCocyclePath (fun x y => B x y s) a r =
        rightmostCocyclePath (fun x y => B x y s) b t :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => hPairMeet a b
  change ∀ᵐ s ∂P, ∀ u v : Lattice, ∃ m n : ℕ,
    u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
    ∀ k : ℕ, rightmostCocyclePath (fun x y => B x y s) u (m + k) =
      rightmostCocyclePath (fun x y => B x y s) v (n + k)
  filter_upwards [hCommon] with s hs
  let C : Lattice → Lattice → ℝ := fun x y => B x y s
  let f := rightmostCocycleSuccessor C
  -- The finite iterate trace and Path.level give signed absolute levels.
  have hLevel (x : Lattice) (N : ℕ) :
      (rightmostCocyclePath C x N).1 + (rightmostCocyclePath C x N).2 =
        x.1 + x.2 + (N : ℤ) := by
    obtain ⟨q, hTrace⟩ := exists_arrow_iterate_path_trace f
      (rightmostCocycleSuccessor_step C) x N
    have hLength : q.1.val + (N - q.1.val) = N :=
      Nat.add_sub_of_le (Nat.le_of_lt_succ q.1.isLt)
    have hLev := q.2.level ⟨N, by omega⟩
    rw [hTrace N (by omega)] at hLev
    exact hLev
  intro u v
  obtain ⟨m, n, hMeet⟩ := hs u v
  have hAligned : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) := by
    have hu := hLevel u m
    have hv := hLevel v n
    rw [hMeet] at hu
    exact hu.symm.trans hv
  refine ⟨m, n, hAligned, ?_⟩
  intro k
  -- Identical successors at the meeting vertex preserve the ENTIRE future.
  calc
    rightmostCocyclePath C u (m + k) = f^[k] (rightmostCocyclePath C u m) := by
      change f^[m + k] u = f^[k] (f^[m] u)
      rw [Nat.add_comm m k, Function.iterate_add_apply]
    _ = f^[k] (rightmostCocyclePath C v n) := congrArg (fun z => f^[k] z) hMeet
    _ = rightmostCocyclePath C v (n + k) := by
      change f^[k] (f^[n] v) = f^[n + k] v
      rw [Nat.add_comm n k, Function.iterate_add_apply]

end LPP.Busemann
