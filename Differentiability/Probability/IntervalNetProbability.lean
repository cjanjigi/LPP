/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.Travel
public import Differentiability.Probability.BoundedAttachmentProbability
public import Martin2004.Probability.BoundedMarginalTails
import Mathlib.Tactic

/-!
# Union bounds for interval connections

Finite union bounds and one common success function for interval connections.
-/
public section
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology BigOperators
namespace LPPDifferentiability

/-- A finite family of measurable success events needs no independence. -/
theorem finite_family_success_probability {Ω J : Type*} [MeasurableSpace Ω]
    [Fintype J] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : J → Set Ω) (hE : ∀ j, MeasurableSet (E j))
    (p C : ℝ) (hp : p ≤ 1) (hcard : (Fintype.card J : ℝ) ≤ C)
    (hprob : ∀ j, p ≤ P.real (E j)) :
    MeasurableSet (⋂ j, E j) ∧ 1-C*(1-p) ≤ P.real (⋂ j, E j) := by
  have hm : MeasurableSet (⋂ j, E j) := MeasurableSet.iInter hE
  refine ⟨hm,?_⟩
  have hb : P.real (⋂ j, E j)ᶜ ≤ C*(1-p) := by
    rw [compl_iInter]
    calc
      _ ≤ ∑ j : J, P.real (E j)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : J, (1-p) := Finset.sum_le_sum fun j _ => by
        rw [probReal_compl_eq_one_sub (hE j)]
        linarith only [hprob j]
      _ = (Fintype.card J:ℝ)*(1-p) := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ C*(1-p) := mul_le_mul_of_nonneg_right hcard (by linarith)
  rw [probReal_compl_eq_one_sub hm] at hb
  linarith only [hb]

/-- Two measurable good events lose at most the sum of their failure bounds. -/
theorem intersection_success_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (x y : ℝ)
    (hx : 1-x ≤ P.real A) (hy : 1-y ≤ P.real B) :
    max 0 (1-x-y) ≤ P.real (A ∩ B) := by
  have hb : P.real (A∩B)ᶜ ≤ x+y := by
    rw [compl_inter]
    calc
      _ ≤ P.real Aᶜ + P.real Bᶜ := measureReal_union_le _ _
      _ ≤ x+y := by
        rw [probReal_compl_eq_one_sub hA,probReal_compl_eq_one_sub hB]
        linarith only [hx,hy]
  rw [probReal_compl_eq_one_sub (hA.inter hB)] at hb
  exact max_le measureReal_nonneg (by linarith only [hb])

/-- The single globally clamped probability function has limit one. -/
theorem interval_success_function (D C : ℝ) {M η : ℝ}
    (hM : 0<M) (hη : 0<η) (p : ℝ → ℝ)
    (ht : Tendsto p atTop (𝓝 1)) :
    (∀ s : ℝ, 0 ≤ max 0 (min 1 (1-
      (2*D*s+2)*exp (-η^2*s/(32*M^2))-C^2*(1-p (s/2)))) ∧
      max 0 (min 1 (1-(2*D*s+2)*exp (-η^2*s/(32*M^2))-
        C^2*(1-p (s/2)))) ≤ 1) ∧
    Tendsto (fun s : ℝ => max 0 (min 1 (1-
      (2*D*s+2)*exp (-η^2*s/(32*M^2))-C^2*(1-p (s/2))))) atTop (𝓝 1) := by
  constructor
  · intro s
    exact ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  · let c : ℝ := η^2/(32*M^2)
    have hc : 0<c := by dsimp [c]; positivity
    have h0 : Tendsto (fun s : ℝ => exp (-c*s)) atTop (𝓝 0) := by
      simpa only [rpow_zero,one_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
    have h1 : Tendsto (fun s : ℝ => s*exp (-c*s)) atTop (𝓝 0) := by
      simpa only [rpow_one] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    have hdecay : Tendsto (fun s : ℝ => (2*D*s+2)*exp (-η^2*s/(32*M^2)))
        atTop (𝓝 0) := by
      have hh := (h1.const_mul (2*D)).add (h0.const_mul 2)
      simp only [mul_zero,add_zero] at hh
      apply hh.congr
      intro s
      have he : -η^2*s/(32*M^2) = -c*s := by dsimp [c]; ring
      rw [he]
      ring
    have hhalf : Tendsto (fun s : ℝ => s/2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    have hmiddle : Tendsto (fun s : ℝ => C^2*(1-p (s/2))) atTop (𝓝 (C^2*(1-1))) :=
      (tendsto_const_nhds.sub (ht.comp hhalf)).const_mul (C^2)
    have hfull : Tendsto (fun s : ℝ => 1-(2*D*s+2)*exp (-η^2*s/(32*M^2))-
        C^2*(1-p (s/2))) atTop (𝓝 (1-0-C^2*(1-1))) :=
      (tendsto_const_nhds.sub hdecay).sub hmiddle
    have hh := (tendsto_const_nhds (x := (0:ℝ))).max
      ((tendsto_const_nhds (x := (1:ℝ))).min hfull)
    simpa only [sub_self,mul_zero,sub_zero,min_self,max_eq_right zero_le_one] using hh

end LPPDifferentiability
