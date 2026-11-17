/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Finite.Integrability
public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
import Busemann.Finite.Translations
import Busemann.Finite.Measurability
import ProbabilityBasics.Analysis.ShiftedHorizonTelescoping

/-! The finite signed-level expectation under one shared uniform horizon. -/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem integral_finiteTiltedPotential_translate (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (h : ℝ × ℝ) (x : Lattice) (N : ℤ) :
    (∫ ω : Environment, (finiteTiltedPotential ω h x N).toReal ∂environmentLaw μ) =
      ∫ ω : Environment,
        (finiteTiltedPotential ω h 0 (N - (x.1 + x.2))).toReal ∂environmentLaw μ := by
  have hpoint (ω : Environment) :
      (finiteTiltedPotential ω h x N).toReal =
        (finiteTiltedPotential (environmentTranslationEquiv x ω) h 0
          (N - (x.1 + x.2))).toReal := by
    have ht := finiteTiltedPotential_translate ω h 0 x (N - (x.1 + x.2))
    have hN : N - (x.1 + x.2) + x.1 + x.2 = N := by omega
    simpa only [add_zero, hN] using congrArg EReal.toReal ht.symm
  calc
    (∫ ω : Environment, (finiteTiltedPotential ω h x N).toReal ∂environmentLaw μ) =
        ∫ ω : Environment, (finiteTiltedPotential (environmentTranslationEquiv x ω) h 0
          (N - (x.1 + x.2))).toReal ∂environmentLaw μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∫ ω : Environment,
        (finiteTiltedPotential ω h 0 (N - (x.1 + x.2))).toReal ∂environmentLaw μ :=
      (measurePreserving_environmentTranslationEquiv μ x).integral_comp'
        (fun ω : Environment => (finiteTiltedPotential ω h 0 (N - (x.1 + x.2))).toReal)

/-- The actual finite edge averaged over the shared one-based horizon has the
corrected signed-level expectation of JR arXiv:1810.03580v3, equation (4.17),
with the boundary term and active tilt count from the correction. -/
theorem integral_finiteBusemannEdge_sharedHorizon
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (h : ℝ × ℝ)
    (x : Lattice) (i : Fin 2) (n : ℕ)
    (hwindow : max (x.1 + x.2) 0 < (n : ℤ) + 1) :
    let f : ℕ → ℝ := fun k =>
      ∫ ω : Environment, (finiteTiltedPotential ω h 0 (k : ℤ)).toReal ∂environmentLaw μ
    (∫ p : Environment × Fin (n + 1),
      finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i
        ∂finiteBusemannSharedHorizonLaw μ n) =
      (f (((n : ℤ) + 1 - (x.1 + x.2)).toNat) -
        f ((max (-(x.1 + x.2)) 0).toNat) -
        ((n : ℝ) + 1 - ((max (x.1 + x.2) 0 : ℤ) : ℝ)) *
          finiteTiltCoordinate h i) / ((n : ℝ) + 1) := by
  classical
  let f : ℕ → ℝ := fun k =>
    ∫ ω : Environment, (finiteTiltedPotential ω h 0 (k : ℤ)).toReal ∂environmentLaw μ
  let m : ℤ := x.1 + x.2
  have hstep : (x + finiteEdgeStep i).1 + (x + finiteEdgeStep i).2 = m + 1 := by
    fin_cases i <;> simp [finiteEdgeStep, m] <;> omega
  have hedge (k : Fin (n + 1)) :
      (∫ ω : Environment, finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i
        ∂environmentLaw μ) =
      if m < (k.val : ℤ) + 1 then
        f (((k.val : ℤ) + 1 - m).toNat) - f (((k.val : ℤ) - m).toNat) -
          finiteTiltCoordinate h i
      else 0 := by
    by_cases ha : m < (k.val : ℤ) + 1
    · have hactive : x.1 + x.2 < ((k.val + 1 : ℕ) : ℤ) := by
        dsimp [m] at ha
        exact_mod_cast ha
      have hcurrent := integrable_finiteTiltedPotential_toReal μ hμ h x
        ((k.val + 1 : ℕ) : ℤ)
      have hnext := integrable_finiteTiltedPotential_toReal μ hμ h
        (x + finiteEdgeStep i) ((k.val + 1 : ℕ) : ℤ)
      have hrepresentation : (fun ω : Environment =>
          finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i) =
          fun ω => (finiteTiltedPotential ω h x ((k.val + 1 : ℕ) : ℤ)).toReal -
            (finiteTiltedPotential ω h (x + finiteEdgeStep i)
              ((k.val + 1 : ℕ) : ℤ)).toReal - finiteTiltCoordinate h i := by
        funext ω
        simp only [finiteBusemannEdge, dite_eq_left hactive]
      have hsub := integral_sub (hcurrent.sub hnext)
        (integrable_const (finiteTiltCoordinate h i))
      simp only [Pi.sub_apply] at hsub
      have hsub' := integral_sub hcurrent hnext
      rw [ite_eq_left ha, hrepresentation, hsub, hsub', integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      rw [integral_finiteTiltedPotential_translate μ h x,
        integral_finiteTiltedPotential_translate μ h (x + finiteEdgeStep i), hstep]
      have hfirst : (↑(((k.val : ℤ) + 1 - m).toNat) : ℤ) =
          ((k.val + 1 : ℕ) : ℤ) - (x.1 + x.2) := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ (k.val : ℤ) + 1 - m)]
        dsimp [m]
      have hsecond : (↑(((k.val : ℤ) - m).toNat) : ℤ) =
          ((k.val + 1 : ℕ) : ℤ) - (m + 1) := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ (k.val : ℤ) - m)]
        push_cast
        omega
      simp only [f, hfirst, hsecond]
    · have hinactive : ¬ x.1 + x.2 < ((k.val + 1 : ℕ) : ℤ) := by
        dsimp [m] at ha
        exact_mod_cast ha
      simp only [ite_eq_right ha, finiteBusemannEdge, dite_eq_right hinactive, integral_zero]
  have hfamily := integral_uniformOrigin_family (environmentLaw μ) n
    (fun k ω => finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i)
    (fun k => measurable_finiteBusemannEdge h x ((k.val + 1 : ℕ) : ℤ) i)
    (fun k => integrable_finiteBusemannEdge μ hμ h x ((k.val + 1 : ℕ) : ℤ) i)
  change (∫ p : Environment × Fin (n + 1),
      finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i
        ∂finiteBusemannSharedHorizonLaw μ n) = _
  rw [finiteBusemannSharedHorizonLaw, hfamily]
  simp_rw [hedge]
  have hw : max m 0 < ((n + 1 : ℕ) : ℤ) := by
    dsimp [m]
    exact_mod_cast hwindow
  have hsum := ProbabilityBasics.average_finite_shifted_increments f m
    (finiteTiltCoordinate h i) (n + 1) hw
  simpa only [m, f, Nat.cast_add, Nat.cast_one, Int.cast_max, Int.cast_zero] using hsum

end LPP.Busemann
