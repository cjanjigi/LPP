/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import ProbabilityBasics.Analysis.ConcaveProfileSlopes

/-!
# Supporting lines and contact for a concave profile

A finite concave real function on an interval containing zero has two
canonical one-sided derivatives there. Both affine functions with these
slopes support the whole interval, and each has first-order contact on its
own side of zero.
-/

public section

open Set
open Filter
open scoped Topology

namespace ConcaveOn

theorem supporting_lines_and_one_sided_contact
    {l r : ℝ} {f : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc l r) f) (hl : l < 0) (hr : 0 < r) :
    (∀ h ∈ Icc l r, f h ≤ f 0 + derivWithin f (Iio 0) 0 * h) ∧
      (∀ h ∈ Icc l r, f h ≤ f 0 + derivWithin f (Ioi 0) 0 * h) ∧
      ((fun h : ℝ => f 0 + derivWithin f (Iio 0) 0 * h - f h)
        =o[𝓝[<] (0 : ℝ)] (fun h => |h|)) ∧
      ((fun h : ℝ => f 0 + derivWithin f (Ioi 0) 0 * h - f h)
        =o[𝓝[>] (0 : ℝ)] (fun h => |h|)) := by
  let dleft : ℝ := derivWithin f (Iio 0) 0
  let dright : ℝ := derivWithin f (Ioi 0) 0
  have hzeroInterior : (0 : ℝ) ∈ interior (Icc l r) := by
    rw [interior_Icc]
    exact ⟨hl, hr⟩
  have hzeroMem : (0 : ℝ) ∈ Icc l r := ⟨le_of_lt hl, le_of_lt hr⟩
  have hleftDeriv : HasDerivWithinAt f dleft (Iio 0) 0 :=
    hconc.hasDerivWithinAt_leftDeriv_of_mem_interior hzeroInterior
  have hrightDeriv : HasDerivWithinAt f dright (Ioi 0) 0 :=
    hconc.hasDerivWithinAt_rightDeriv_of_mem_interior hzeroInterior
  have hderivOrder : dright ≤ dleft :=
    hconc.rightDeriv_le_leftDeriv_of_mem_interior hzeroInterior
  have hsupportRight : ∀ h ∈ Icc l r, f h ≤ f 0 + dright * h := by
    intro h hh
    rcases lt_trichotomy h 0 with hneg | heq | hpos
    · have hsec : dleft ≤ slope f h 0 :=
        hconc.le_slope_of_hasDerivWithinAt_Iio hh hzeroMem hneg hleftDeriv
      have hsec' : dleft ≤ (f h - f 0) / h := by
        rw [slope_comm f h 0, slope_def_field, sub_zero] at hsec
        exact hsec
      have hmul := mul_le_mul_of_nonpos_right hsec' (le_of_lt hneg)
      have hcancel : (f h - f 0) / h * h = f h - f 0 :=
        div_mul_cancel₀ _ (ne_of_lt hneg)
      have hleft : f h ≤ f 0 + dleft * h := by
        linarith [hmul, hcancel]
      have hcross : f 0 + dleft * h ≤ f 0 + dright * h := by
        have hmulD : dleft * h ≤ dright * h :=
          mul_le_mul_of_nonpos_right hderivOrder (le_of_lt hneg)
        linarith
      exact le_trans hleft hcross
    · subst h
      simp
    · have hsec : slope f 0 h ≤ dright :=
        hconc.slope_le_of_hasDerivWithinAt_Ioi hzeroMem hh hpos hrightDeriv
      have hsec' : (f h - f 0) / h ≤ dright := by
        rw [slope_def_field, sub_zero] at hsec
        exact hsec
      have hmul : f h - f 0 ≤ dright * h :=
        (div_le_iff₀ hpos).mp hsec'
      linarith
  have hsupportLeft : ∀ h ∈ Icc l r, f h ≤ f 0 + dleft * h := by
    intro h hh
    rcases lt_trichotomy h 0 with hneg | heq | hpos
    · have hsec : dleft ≤ slope f h 0 :=
        hconc.le_slope_of_hasDerivWithinAt_Iio hh hzeroMem hneg hleftDeriv
      have hsec' : dleft ≤ (f h - f 0) / h := by
        rw [slope_comm f h 0, slope_def_field, sub_zero] at hsec
        exact hsec
      have hmul := mul_le_mul_of_nonpos_right hsec' (le_of_lt hneg)
      have hcancel : (f h - f 0) / h * h = f h - f 0 :=
        div_mul_cancel₀ _ (ne_of_lt hneg)
      linarith [hmul, hcancel]
    · subst h
      simp
    · have hsec : slope f 0 h ≤ dright :=
        hconc.slope_le_of_hasDerivWithinAt_Ioi hzeroMem hh hpos hrightDeriv
      have hsec' : (f h - f 0) / h ≤ dright := by
        rw [slope_def_field, sub_zero] at hsec
        exact hsec
      have hmul : f h - f 0 ≤ dright * h :=
        (div_le_iff₀ hpos).mp hsec'
      have hcross : f 0 + dright * h ≤ f 0 + dleft * h := by
        have hmulD : dright * h ≤ dleft * h :=
          mul_le_mul_of_nonneg_right hderivOrder (le_of_lt hpos)
        linarith
      exact le_trans (by linarith) hcross
  have hleftContactId :
      (fun h : ℝ => f 0 + dleft * h - f h) =o[𝓝[<] (0 : ℝ)] fun h => h := by
    have hrem := hleftDeriv.isLittleO.neg_left
    exact hrem.congr (fun h => by ring) (fun _ => by simp)
  have hleftAbs :
      (fun h : ℝ => -h) =ᶠ[𝓝[<] (0 : ℝ)] fun h => |h| := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [abs_of_neg hh]
  have hleftContact :
      (fun h : ℝ => f 0 + dleft * h - f h)
        =o[𝓝[<] (0 : ℝ)] fun h => |h| :=
    hleftContactId.neg_right.congr' EventuallyEq.rfl hleftAbs
  have hrightContactId :
      (fun h : ℝ => f 0 + dright * h - f h) =o[𝓝[>] (0 : ℝ)] fun h => h := by
    have hrem := hrightDeriv.isLittleO.neg_left
    exact hrem.congr (fun h => by ring) (fun _ => by simp)
  have hrightAbs :
      (fun h : ℝ => h) =ᶠ[𝓝[>] (0 : ℝ)] fun h => |h| := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [abs_of_pos hh]
  have hrightContact :
      (fun h : ℝ => f 0 + dright * h - f h)
        =o[𝓝[>] (0 : ℝ)] fun h => |h| :=
    hrightContactId.congr' EventuallyEq.rfl hrightAbs
  exact ⟨hsupportLeft, hsupportRight, hleftContact, hrightContact⟩

end ConcaveOn
