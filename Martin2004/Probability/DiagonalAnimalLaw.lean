/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.DiagonalCovariance
public import Martin2004.Probability.DiagonalAnimalMaximum
public import LPP_Foundations.Probability.TranslationErgodic
public import ProbabilityBasics.Probability.CesaroLaw
public import Mathlib.Probability.IdentDistrib

/-! Whole-process laws for Martin's actual proper-interval diagonal maxima.
Positive columns and positive-size tail blocks never evaluate an off-domain Q. -/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Every family of actual proper-interval maxima is jointly measurable. -/
theorem measurable_diagonalAnimalMaximum_process {ι : Type*}
    (m n : ι → ℤ) (hmn : ∀ i, m i < n i) :
    Measurable (fun ω : Environment => fun i : ι =>
      diagonalAnimalMaximum (m i) (n i) (hmn i) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_diagonalAnimalMaximum (Ω := Environment)
    (fun (v : Lattice) (ω : Environment) => ω v)
    (fun v => measurable_pi_apply v) (m i) (n i) (hmn i)

/-- All proper-interval maxima have a jointly translation-invariant law.
Taking the index set to be all pairs m<n gives equation (3.2) of Martin (2002). -/
theorem environmentLaw_map_diagonalAnimalMaximum_process {ι : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m n : ι → ℤ) (hmn : ∀ i, m i < n i) (k : ℤ) :
    (environmentLaw μ).map (fun ω : Environment => fun i : ι =>
      diagonalAnimalMaximum (m i + k) (n i + k)
        (by have hi := hmn i; omega) ω) =
    (environmentLaw μ).map (fun ω : Environment => fun i : ι =>
      diagonalAnimalMaximum (m i) (n i) (hmn i) ω) := by
  have htrans : Measurable (fun ω : Environment => fun z => ω ((k, k) + z)) :=
    Measurable.of_eval (fun z => measurable_pi_apply ((k, k) + z))
  calc
    _ = (environmentLaw μ).map
        ((fun ω : Environment => fun i : ι =>
          diagonalAnimalMaximum (m i) (n i) (hmn i) ω) ∘
          (fun ω : Environment => fun z => ω ((k, k) + z))) := by
      congr 1
      funext ω i
      exact (diagonalAnimalMaximum_translate (m i) (n i) k (hmn i) ω).symm
    _ = ((environmentLaw μ).map
        (fun ω : Environment => fun z => ω ((k, k) + z))).map
        (fun ω : Environment => fun i : ι =>
          diagonalAnimalMaximum (m i) (n i) (hmn i) ω) :=
      (Measure.map_map (measurable_diagonalAnimalMaximum_process m n hmn) htrans).symm
    _ = _ := by rw [environmentLaw_map_translation]

/-- The whole column indexed by positive length j+1 is measurable. -/
theorem measurable_diagonalAnimalMaximum_column (m : ℤ) :
    Measurable (fun ω : Environment => fun j : ℕ =>
      diagonalAnimalMaximum m (m + ((j + 1 : ℕ) : ℤ)) (by omega) ω) :=
  measurable_diagonalAnimalMaximum_process (fun _ : ℕ => m)
    (fun j => m + ((j + 1 : ℕ) : ℤ)) (by intro j; omega)

/-- Adjacent whole positive-length columns are identically distributed. -/
theorem diagonalAnimalMaximum_column_identDistrib (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (m : ℤ) :
    IdentDistrib
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (m + 1) (m + 1 + ((j + 1 : ℕ) : ℤ)) (by omega) ω)
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum m (m + ((j + 1 : ℕ) : ℤ)) (by omega) ω)
      (environmentLaw μ) (environmentLaw μ) := by
  refine ⟨(measurable_diagonalAnimalMaximum_column (m + 1)).aemeasurable,
    (measurable_diagonalAnimalMaximum_column m).aemeasurable, ?_⟩
  simpa only [add_right_comm m 1] using
    environmentLaw_map_diagonalAnimalMaximum_process μ (fun _ : ℕ => m)
      (fun j => m + ((j + 1 : ℕ) : ℤ)) (by intro j; omega) 1

/-- Positive block size makes each literal source-tail interval proper. -/
theorem diagonalAnimal_tailBlock_lt (j k : ℕ) (hk : 0 < k) :
    (((j + 1) * k : ℕ) : ℤ) < (((j + 2) * k : ℕ) : ℤ) := by
  exact_mod_cast Nat.mul_lt_mul_of_pos_right (by omega : j + 1 < j + 2) hk

/-- The whole tail block process starts with Q(k,2k) and is measurable. -/
theorem measurable_diagonalAnimalMaximum_tailBlocks (k : ℕ) (hk : 0 < k) :
    Measurable (fun ω : Environment => fun j : ℕ =>
      diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
        (diagonalAnimal_tailBlock_lt j k hk) ω) :=
  measurable_diagonalAnimalMaximum_process
    (fun j : ℕ => (((j + 1) * k : ℕ) : ℤ))
    (fun j : ℕ => (((j + 2) * k : ℕ) : ℤ))
    (fun j => diagonalAnimal_tailBlock_lt j k hk)

/-- Actual translation by (k,k) advances the entire proper tail block process. -/
theorem diagonalAnimalMaximum_tailBlocks_semiconj (k : ℕ) (hk : 0 < k) :
    Function.Semiconj
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)
      (fun ω : Environment => fun z => ω (((k : ℤ), (k : ℤ)) + z))
      sequenceShift := by
  intro ω
  funext j
  change diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
      (diagonalAnimal_tailBlock_lt j k hk) (fun z => ω (((k : ℤ), (k : ℤ)) + z)) =
    diagonalAnimalMaximum ((((j + 1) + 1) * k : ℕ) : ℤ)
      ((((j + 1) + 2) * k : ℕ) : ℤ) (diagonalAnimal_tailBlock_lt (j + 1) k hk) ω
  rw [diagonalAnimalMaximum_translate]
  have hstart : (((j + 1) * k : ℕ) : ℤ) + (k : ℤ) =
      ((((j + 1) + 1) * k : ℕ) : ℤ) := by push_cast; ring
  have hfinish : (((j + 2) * k : ℕ) : ℤ) + (k : ℤ) =
      ((((j + 1) + 2) * k : ℕ) : ℤ) := by push_cast; ring
  simp only [hstart, hfinish]

/-- Literal left shift preserves the actual pushed whole tail-block law. -/
theorem measurePreserving_diagonalAnimalMaximum_tailBlocks_shift
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k) :
    MeasurePreserving sequenceShift
      ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω))
      ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)) := by
  have hmap : MeasurePreserving
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)
      (environmentLaw μ) _ :=
    ⟨measurable_diagonalAnimalMaximum_tailBlocks k hk, rfl⟩
  exact hmap.of_semiconj
    (measurePreserving_environment_translation μ ((k : ℤ), (k : ℤ)))
    (diagonalAnimalMaximum_tailBlocks_semiconj k hk) measurable_sequenceShift

/-- The whole positive-size tail block process is stationary in joint law. -/
theorem diagonalAnimalMaximum_tailBlocks_identDistrib
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k) :
    IdentDistrib
      (fun ω : Environment => sequenceShift (fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω))
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)
      (environmentLaw μ) (environmentLaw μ) := by
  have hmeas := measurable_diagonalAnimalMaximum_tailBlocks k hk
  refine ⟨(measurable_sequenceShift.comp hmeas).aemeasurable, hmeas.aemeasurable, ?_⟩
  rw [← (measurePreserving_diagonalAnimalMaximum_tailBlocks_shift μ k hk).map_eq]
  exact (Measure.map_map measurable_sequenceShift hmeas).symm

/-- The actual pushed tail-block law is ergodic under left shift for every
positive k, by the nonzero environment translation (k,k) itself. -/
theorem ergodic_diagonalAnimalMaximum_tailBlocks_shift
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k) :
    Ergodic sequenceShift
      ((environmentLaw μ).map (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)) := by
  have hmap : MeasurePreserving
      (fun ω : Environment => fun j : ℕ =>
        diagonalAnimalMaximum (((j + 1) * k : ℕ) : ℤ) (((j + 2) * k : ℕ) : ℤ)
          (diagonalAnimal_tailBlock_lt j k hk) ω)
      (environmentLaw μ) _ :=
    ⟨measurable_diagonalAnimalMaximum_tailBlocks k hk, rfl⟩
  have hnonzero : ((k : ℤ), (k : ℤ)) ≠ (0 : Lattice) := by
    intro h
    have hfst : (k : ℤ) = 0 := congrArg Prod.fst h
    have : k = 0 := Int.natCast_inj.mp hfst
    omega
  exact hmap.ergodic_of_ergodic_semiconj
    (ergodic_environment_translation μ ((k : ℤ), (k : ℤ)) hnonzero)
    measurable_sequenceShift (diagonalAnimalMaximum_tailBlocks_semiconj k hk)

/-- A measurable site transform preserves the interval translation law under
the original iid environment measure. This includes positive-part weights. -/
theorem diagonalAnimalMaximum_comp_identDistrib (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (m n k : ℤ) (hmn : m < n) :
    IdentDistrib
      (fun ω : Environment => diagonalAnimalMaximum (m + k) (n + k) (by omega)
        (fun v => f (ω v)))
      (fun ω : Environment => diagonalAnimalMaximum m n hmn (fun v => f (ω v)))
      (environmentLaw μ) (environmentLaw μ) := by
  have hmeas : Measurable (fun ω : Environment =>
      diagonalAnimalMaximum m n hmn (fun v => f (ω v))) :=
    measurable_diagonalAnimalMaximum (Ω := Environment)
      (fun (v : Lattice) (ω : Environment) => f (ω v))
      (fun v => hf.comp (measurable_pi_apply v)) m n hmn
  have htrans : Measurable (fun ω : Environment => fun z => ω ((k, k) + z)) :=
    Measurable.of_eval (fun z => measurable_pi_apply ((k, k) + z))
  refine ⟨(measurable_diagonalAnimalMaximum (Ω := Environment)
    (fun (v : Lattice) (ω : Environment) => f (ω v))
    (fun v => hf.comp (measurable_pi_apply v)) (m + k) (n + k) (by omega)).aemeasurable,
    hmeas.aemeasurable, ?_⟩
  calc
    _ = (environmentLaw μ).map
        ((fun ω : Environment => diagonalAnimalMaximum m n hmn (fun v => f (ω v))) ∘
          (fun ω : Environment => fun z => ω ((k, k) + z))) := by
      congr 1
      funext ω
      exact (diagonalAnimalMaximum_translate m n k hmn (fun v => f (ω v))).symm
    _ = ((environmentLaw μ).map
        (fun ω : Environment => fun z => ω ((k, k) + z))).map
        (fun ω : Environment => diagonalAnimalMaximum m n hmn (fun v => f (ω v))) :=
      (Measure.map_map hmeas htrans).symm
    _ = _ := by rw [environmentLaw_map_translation]

/-- Translating a single actual interval preserves its distribution. -/
theorem diagonalAnimalMaximum_identDistrib (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (m n k : ℤ) (hmn : m < n) :
    IdentDistrib
      (fun ω : Environment => diagonalAnimalMaximum (m + k) (n + k) (by omega) ω)
      (fun ω : Environment => diagonalAnimalMaximum m n hmn ω)
      (environmentLaw μ) (environmentLaw μ) :=
  diagonalAnimalMaximum_comp_identDistrib μ (fun x => x) measurable_id m n k hmn

end LPPDifferentiability
