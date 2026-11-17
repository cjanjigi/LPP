/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.SupportIdentities
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate
public import Busemann.Frozen.Definitions.ProcessSample
public import Busemann.Frozen.Definitions.SupportTilt
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Conditional contact and extreme-support pinning of a random drift. -/

public section

open MeasureTheory Filter LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- A supporting drift with an extreme first coordinate is pinned by its mean.
This is the conditional coordinate step in JR1810.03580v3, Lemma 4.5(b,c).
The global random majorant is incoming data and is not produced here. -/
theorem ae_drift_eq_of_extreme_support_mean
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (u : Fin 2 → ProcessSample → ℝ)
    (hInt : ∀ i : Fin 2, Integrable (u i) P)
    (eta : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g eta h.1)
    (hext : (∀ k : SupportTilt g, SupportsAt g eta k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g, SupportsAt g eta k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2, (∫ s, u i s ∂P) = -finiteTiltCoordinate h.1 i)
    (hMajorant : ∀ᵐ s ∂P, ∀ z : Quadrant,
      g z ≤ u 0 s * (z.1 : ℝ) + u 1 s * (z.2 : ℝ)) :
    ∀ᵐ s ∂P, SupportsAt g eta (-u 0 s, -u 1 s) ∧
      ∀ i : Fin 2, u i s = -finiteTiltCoordinate h.1 i := by
  classical
  let eta₁ : ℝ := (eta.1.1 : ℝ)
  let eta₂ : ℝ := (eta.1.2 : ℝ)
  let gap : ProcessSample → ℝ := fun s =>
    eta₁ * u 0 s + eta₂ * u 1 s - g eta.1

  have hlinearInt : Integrable (fun s => eta₁ * u 0 s + eta₂ * u 1 s) P :=
    (hInt 0).const_mul eta₁ |>.add ((hInt 1).const_mul eta₂)
  have hgapInt : Integrable gap P := by
    change Integrable (fun s => eta₁ * u 0 s + eta₂ * u 1 s - g eta.1) P
    exact hlinearInt.sub (integrable_const _)
  have hgapNonneg : 0 ≤ᵐ[P] gap := by
    filter_upwards [hMajorant] with s hs
    have hsη := hs eta.1
    dsimp [gap]
    nlinarith [hsη]
  have hhh :=
    (supportsAt_iff_through_origin_majorant_and_contact g eta h.1 hhom).mp hh
  have hgapIntegral : (∫ s, gap s ∂P) = 0 := by
    calc
      (∫ s, gap s ∂P) =
          (∫ s, eta₁ * u 0 s + eta₂ * u 1 s ∂P) -
            ∫ s, (fun _ : ProcessSample => g eta.1) s ∂P := by
              rw [show gap =
                fun s => eta₁ * u 0 s + eta₂ * u 1 s - g eta.1 by
                  funext s
                  rfl]
              exact integral_sub hlinearInt (integrable_const _)
      _ = eta₁ * (∫ s, u 0 s ∂P) + eta₂ * (∫ s, u 1 s ∂P) - g eta.1 := by
            rw [integral_add ((hInt 0).const_mul eta₁) ((hInt 1).const_mul eta₂),
              integral_const_mul, integral_const_mul]
            simp
      _ = 0 := by
            rw [hMean 0, hMean 1]
            simp [finiteTiltCoordinate]
            rw [hhh.2]
            dsimp [eta₁, eta₂]
            ring
  have hgapZero : gap =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hgapNonneg hgapInt).mp hgapIntegral

  have hsupportAE : ∀ᵐ s ∂P, SupportsAt g eta (-u 0 s, -u 1 s) := by
    filter_upwards [hMajorant, hgapZero] with s hs hz
    have hcontact :
        g eta.1 = eta₁ * u 0 s + eta₂ * u 1 s := by
      have hz' : eta₁ * u 0 s + eta₂ * u 1 s - g eta.1 = 0 := by
        simpa [gap] using hz
      linarith
    apply (supportsAt_iff_through_origin_majorant_and_contact g eta
      (-u 0 s, -u 1 s) hhom).2
    refine ⟨?_, ?_⟩
    · intro z
      simpa only [neg_neg] using hs z
    · change g eta.1 =
        -(-u 0 s) * (eta.1.1 : ℝ) + -(-u 1 s) * (eta.1.2 : ℝ)
      simpa only [neg_neg, eta₁, eta₂, mul_comm] using hcontact

  have hconstInt : Integrable (fun _ : ProcessSample => -h.1.1) P :=
    integrable_const _
  have hfirstMean :
      (∫ s, u 0 s ∂P) = ∫ s, (fun _ : ProcessSample => -h.1.1) s ∂P := by
    rw [hMean 0]
    simp [finiteTiltCoordinate]
  have hfirstPinned : u 0 =ᵐ[P] fun _ => -h.1.1 := by
    rcases hext with hmin | hmax
    · have horder : u 0 ≤ᵐ[P] fun _ => -h.1.1 := by
        filter_upwards [hsupportAE] with s hs
        let k : SupportTilt g := ⟨(-u 0 s, -u 1 s), ⟨eta, hs⟩⟩
        have hkSupport : SupportsAt g eta k.1 := by simpa [k] using hs
        have hk := hmin k hkSupport
        dsimp [k] at hk
        linarith
      exact (integral_eq_iff_of_ae_le (hInt 0) hconstInt horder).mp hfirstMean
    · have horder : (fun _ => -h.1.1) ≤ᵐ[P] u 0 := by
        filter_upwards [hsupportAE] with s hs
        let k : SupportTilt g := ⟨(-u 0 s, -u 1 s), ⟨eta, hs⟩⟩
        have hkSupport : SupportsAt g eta k.1 := by simpa [k] using hs
        have hk := hmax k hkSupport
        dsimp [k] at hk
        linarith
      exact ((integral_eq_iff_of_ae_le hconstInt (hInt 0) horder).mp
        hfirstMean.symm).symm

  filter_upwards [hsupportAE, hfirstPinned] with s hsupp hpin
  have hpin' : u 0 s = -h.1.1 := by simpa using hpin
  let k : SupportTilt g := ⟨(-u 0 s, -u 1 s), ⟨eta, hsupp⟩⟩
  have hkSupport : SupportsAt g eta k.1 := by simpa [k] using hsupp
  have hfirst : k.1.1 = h.1.1 := by
    dsimp [k]
    linarith
  have hpair := supporting_tilts_eq_of_first_coord_eq g eta k.1 h.1 hhom
    hkSupport hh hfirst
  refine ⟨hsupp, ?_⟩
  intro i
  fin_cases i
  · simpa [finiteTiltCoordinate] using hpin'
  · have hsecond : -u 1 s = h.1.2 := congrArg Prod.snd hpair
    have hu1 : u 1 s = -h.1.2 := by linarith
    simpa [finiteTiltCoordinate] using hu1

end LPP.Busemann
