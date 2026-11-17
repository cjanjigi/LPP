/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathMeasurability
public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Logic.Equiv.List

/-! Positive finite partitions by high sites in the clipped corridor. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- A positive measurable event contains a positive measurable subevent on
which the clipped corridor's high sites form one fixed finite set. This is
the finite partition step in GRS, arXiv:1510.00860v1, Appendix A.4,
lines 1581–1587. -/
theorem exists_positive_fixed_corridor_high_sites
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (weights : Ω → Environment)
    (hWeightsMeas : Measurable weights)
    (B : Lattice → Lattice → Ω → ℝ)
    (hBMeas : ∀ x y : Lattice, Measurable (B x y))
    (F : Finset Lattice) (ell : ℕ) (M2 : ℤ) (K : ℝ)
    (A : Set Ω) (hAMeas : MeasurableSet A) (hAPos : 0 < P A) :
    ∃ V : Finset Lattice,
      let E := A ∩ {s : Ω | ∀ z : Lattice,
        z ∈ V ↔ z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
          (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
            (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
            (n < ell ∨ z.2 <
              (rightmostCocyclePath (fun x y => B x y s)
                (0, (ell : ℤ)) (n - ell)).2)) ∧
          K < weights s z}
      MeasurableSet E ∧ 0 < P E := by
  classical
  -- Each finite-time path coordinate is measurable from the producer.
  have hPathCoordinate (x : Lattice) (n : ℕ) :
      Measurable (fun s : Ω =>
        (rightmostCocyclePath (fun x y => B x y s) x n).2) := by
    exact measurable_snd.comp (measurable_rightmostCocyclePath B hBMeas x n)

  -- Each fixed-site corridor witness is a countable union of measurable tests.
  have hWitnessTermMeas (z : Lattice) (n : ℕ) :
      MeasurableSet {s : Ω |
        (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)} := by
    have hLevel : MeasurableSet {s : Ω | (n : ℤ) = z.1 + z.2} := by
      by_cases h : (n : ℤ) = z.1 + z.2 <;> simp [h]
    have hBelow : MeasurableSet {s : Ω |
        (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2} :=
      measurableSet_lt (hPathCoordinate 0 n) measurable_const
    have hAbove : MeasurableSet {s : Ω |
        n < ell ∨ z.2 <
          (rightmostCocyclePath (fun x y => B x y s)
            (0, (ell : ℤ)) (n - ell)).2} := by
      by_cases hn : n < ell
      · simp [hn]
      · simpa [hn] using
          (measurableSet_lt measurable_const
            (hPathCoordinate (0, (ell : ℤ)) (n - ell)))
    change MeasurableSet
      ({s : Ω | (n : ℤ) = z.1 + z.2} ∩
        ({s : Ω | (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2} ∩
          {s : Ω | n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2}))
    exact hLevel.inter (hBelow.inter hAbove)

  have hWitnessMeas (z : Lattice) :
      MeasurableSet {s : Ω | ∃ n : ℕ,
        (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => hWitnessTermMeas z n

  -- Membership in the finite clip and its two coordinate bounds are fixed tests.
  have hInClipMeas (z : Lattice) : MeasurableSet {s : Ω | z ∈ F} := by
    by_cases hz : z ∈ F <;> simp [hz]
  have hFirstBoundMeas (z : Lattice) : MeasurableSet {s : Ω | 0 < z.1} := by
    by_cases hz : 0 < z.1 <;> simp [hz]
  have hSecondBoundMeas (z : Lattice) : MeasurableSet {s : Ω | z.2 < M2} := by
    by_cases hz : z.2 < M2 <;> simp [hz]
  have hWeightMeasAt (z : Lattice) :
      Measurable (fun s : Ω => weights s z) :=
    (measurable_pi_apply z).comp hWeightsMeas

  have hHighSiteMeas (z : Lattice) :
      MeasurableSet {s : Ω | z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
        (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)) ∧
        K < weights s z} := by
    change MeasurableSet
      ({s : Ω | z ∈ F} ∩
        ({s : Ω | 0 < z.1} ∩
          ({s : Ω | z.2 < M2} ∩
            ({s : Ω | ∃ n : ℕ,
                (n : ℤ) = z.1 + z.2 ∧
                  (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
                  (n < ell ∨ z.2 <
                    (rightmostCocyclePath (fun x y => B x y s)
                      (0, (ell : ℤ)) (n - ell)).2)} ∩
              {s : Ω | K < weights s z}))))
    exact (hInClipMeas z).inter
      ((hFirstBoundMeas z).inter
        ((hSecondBoundMeas z).inter
          ((hWitnessMeas z).inter
            (measurableSet_lt measurable_const (hWeightMeasAt z)))))

  -- The complete characteristic event is a countable intersection of site tests.
  have hCharacteristicCoordinateMeas (V : Finset Lattice) (z : Lattice) :
      MeasurableSet {s : Ω | z ∈ V ↔
        z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
          (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
            (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
            (n < ell ∨ z.2 <
              (rightmostCocyclePath (fun x y => B x y s)
                (0, (ell : ℤ)) (n - ell)).2)) ∧
          K < weights s z} := by
    by_cases hz : z ∈ V
    · simpa [hz] using hHighSiteMeas z
    · simp only [hz, false_iff]
      exact (hHighSiteMeas z).compl
  have hCharacteristicMeas (V : Finset Lattice) :
      MeasurableSet {s : Ω | ∀ z : Lattice, z ∈ V ↔
        z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
          (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
            (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
            (n < ell ∨ z.2 <
              (rightmostCocyclePath (fun x y => B x y s)
                (0, (ell : ℤ)) (n - ell)).2)) ∧
          K < weights s z} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun z => hCharacteristicCoordinateMeas V z

  let E (V : Finset Lattice) : Set Ω :=
    A ∩ {s : Ω | ∀ z : Lattice, z ∈ V ↔
      z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
        (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)) ∧
        K < weights s z}
  have hEMeas (V : Finset Lattice) : MeasurableSet (E V) := by
    dsimp only [E]
    exact hAMeas.inter (hCharacteristicMeas V)

  -- Every outcome's high sites in the finite clip form one of the fibers.
  let W (s : Ω) : Finset Lattice := F.filter fun z =>
    0 < z.1 ∧ z.2 < M2 ∧
      (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 <
          (rightmostCocyclePath (fun x y => B x y s)
            (0, (ell : ℤ)) (n - ell)).2)) ∧
      K < weights s z
  have hWCharacteristic (s : Ω) (z : Lattice) :
      z ∈ W s ↔ z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
        (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)) ∧
        K < weights s z := by
    simp only [W, Finset.mem_filter]
  have hCover : A ⊆ ⋃ V : Finset Lattice, E V := by
    intro s hsA
    refine Set.mem_iUnion.mpr ⟨W s, ?_⟩
    change s ∈ A ∧ ∀ z : Lattice, z ∈ W s ↔
      z ∈ F ∧ 0 < z.1 ∧ z.2 < M2 ∧
        (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
          (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
          (n < ell ∨ z.2 <
            (rightmostCocyclePath (fun x y => B x y s)
              (0, (ell : ℤ)) (n - ell)).2)) ∧
        K < weights s z
    exact ⟨hsA, fun z => hWCharacteristic s z⟩

  -- A positive countable union has a positive member, with no assumption on P.
  have hUnionPositive : 0 < P (⋃ V : Finset Lattice, E V) :=
    lt_of_lt_of_le hAPos (measure_mono hCover)
  obtain ⟨V, hVPositive⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPositive)

  refine ⟨V, ?_⟩
  change MeasurableSet (E V) ∧ 0 < P (E V)
  exact ⟨hEMeas V, hVPositive⟩

end LPP.Busemann
