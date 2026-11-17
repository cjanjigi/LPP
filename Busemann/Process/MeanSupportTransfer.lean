/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.QuadrantSuperdifferentialIdentities
public import Busemann.Frozen.Definitions.InteriorDirection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mean support transfer for the quadrant superdifferential

An integrable random vector with an interior support almost surely has any
fixed support that contains its mean almost surely as well.
-/

public section

open MeasureTheory LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- Transfer a fixed support of the mean to the random vector from an
almost-sure interior support. The interior contact event is an explicit input. -/
theorem ae_mem_quadrantSuperdifferential_of_integral_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Quadrant → ℝ) (X : Ω → ℝ × ℝ) (ξ : Quadrant)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (hX : Integrable X P)
    (hcontact : ∀ᵐ ω ∂P, ∃ η : InteriorDirection,
      X ω ∈ quadrantSuperdifferential g η.val)
    (hmean : (∫ ω, X ω ∂P) ∈ quadrantSuperdifferential g ξ) :
    ∀ᵐ ω ∂P, X ω ∈ quadrantSuperdifferential g ξ := by
  let ξ₁ : ℝ := (ξ.1 : ℝ)
  let ξ₂ : ℝ := (ξ.2 : ℝ)
  let gap : Ω → ℝ := fun ω =>
    ξ₁ * (X ω).1 + ξ₂ * (X ω).2 - g ξ
  have hmeanContact :
      g ξ = (∫ ω, X ω ∂P).1 * ξ₁ + (∫ ω, X ω ∂P).2 * ξ₂ :=
    ((mem_quadrantSuperdifferential_iff_majorant_and_contact
      g ξ (∫ ω, X ω ∂P) hhom).mp hmean).2
  have hmajorantAE : ∀ᵐ ω ∂P, ∀ z : Quadrant,
      g z ≤ (X ω).1 * (z.1 : ℝ) + (X ω).2 * (z.2 : ℝ) := by
    filter_upwards [hcontact] with ω hω
    obtain ⟨η, hη⟩ := hω
    exact ((mem_quadrantSuperdifferential_iff_majorant_and_contact
      g η.val (X ω) hhom).mp hη).1
  have hlinearInt : Integrable (fun ω =>
      ξ₁ * (X ω).1 + ξ₂ * (X ω).2) P :=
    (hX.fst.const_mul ξ₁).add (hX.snd.const_mul ξ₂)
  have hgapInt : Integrable gap P := by
    change Integrable (fun ω =>
      ξ₁ * (X ω).1 + ξ₂ * (X ω).2 - g ξ) P
    exact hlinearInt.sub (integrable_const _)
  have hgapNonneg : 0 ≤ᵐ[P] gap := by
    filter_upwards [hmajorantAE] with ω hmajorant
    have hξ := hmajorant ξ
    dsimp [gap, ξ₁, ξ₂]
    nlinarith [hξ]
  have hgapIntegral : (∫ ω, gap ω ∂P) = 0 := by
    calc
      (∫ ω, gap ω ∂P) =
          (∫ ω, ξ₁ * (X ω).1 + ξ₂ * (X ω).2 ∂P) -
            ∫ ω, (fun _ : Ω => g ξ) ω ∂P := by
              rw [show gap = fun ω =>
                ξ₁ * (X ω).1 + ξ₂ * (X ω).2 - g ξ by funext ω; rfl]
              exact integral_sub hlinearInt (integrable_const _)
      _ = ξ₁ * (∫ ω, (X ω).1 ∂P) +
            ξ₂ * (∫ ω, (X ω).2 ∂P) - g ξ := by
              rw [integral_add (hX.fst.const_mul ξ₁) (hX.snd.const_mul ξ₂),
                integral_const_mul, integral_const_mul]
              simp
      _ = ξ₁ * (∫ ω, X ω ∂P).1 +
            ξ₂ * (∫ ω, X ω ∂P).2 - g ξ := by
              rw [← fst_integral hX, ← snd_integral hX]
      _ = 0 := by
              rw [hmeanContact]
              ring
  have hgapZero : gap =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hgapNonneg hgapInt).mp hgapIntegral
  filter_upwards [hmajorantAE, hgapZero] with ω hmajorant hzero
  have hcontactAtXi :
      g ξ = (X ω).1 * (ξ.1 : ℝ) + (X ω).2 * (ξ.2 : ℝ) := by
    have hgapEq : ξ₁ * (X ω).1 + ξ₂ * (X ω).2 - g ξ = 0 := by
      simpa [gap, ξ₁, ξ₂] using hzero
    nlinarith [hgapEq]
  exact (mem_quadrantSuperdifferential_iff_majorant_and_contact
    g ξ (X ω) hhom).mpr ⟨hmajorant, hcontactAtXi⟩

end LPP.Busemann
