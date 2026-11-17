/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CalibratedPaths
public import Busemann.Frozen.Definitions.InteriorDirection
public import Busemann.Frozen.Definitions.SupportTilt
public import Mathlib.Topology.Order.Compact

/-! Conditional confinement of calibrated endpoints to a contact interval. -/
@[expose] public section
open Filter LPPDifferentiability LPP.Busemann
open scoped NNReal Topology

namespace LPP.Busemann

/-- GRS 1510.00860v2, Theorem 4.3: supplied shape and centered-cocycle limits confine
calibrated endpoints to the interval where the limiting tilted gap vanishes. -/
theorem calibrated_endpoints_confined_to_contact_interval
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (g : Quadrant → ℝ) (h : SupportTilt g)
    (left right : InteriorDirection) (x : Lattice)
    (d : ℕ → ℕ × ℕ) (hlen : ∀ n, (d n).1 + (d n).2 = n)
    (p : ∀ n, LPPDifferentiability.Path x (d n))
    (hcal : ∀ n, ∀ k : Fin ((d n).1 + (d n).2),
      C ((p n).vertex k.castSucc) ((p n).vertex k.succ) =
        ω ((p n).vertex k.castSucc)) :
    let q : ℝ → Quadrant := fun t =>
      (Real.toNNReal t, Real.toNNReal (1 - t))
    let ρ : ℕ → ℝ := fun n => ((d n).1 : ℝ) / (n : ℝ)
    ContinuousOn (fun t : ℝ => g (q t)) (Set.Icc 0 1) →
    (∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (g (q t) + h.1.1 * t + h.1.2 * (1 - t) = 0 ↔
        (left.1.1 : ℝ) ≤ t ∧ t ≤ (right.1.1 : ℝ))) →
    Tendsto (fun n => lastPassage ω x (d n) / (n : ℝ) - g (q (ρ n)))
      atTop (𝓝 0) →
    Tendsto (fun n =>
      (C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) +
        h.1.1 * ((d n).1 : ℝ) + h.1.2 * ((d n).2 : ℝ)) / (n : ℝ))
      atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (left.1.1 : ℝ) - ε < ρ n ∧ ρ n < (right.1.1 : ℝ) + ε := by
  intro q ρ hcontinuous hcontact hpassage hendpoint
  let q₀ : ℝ → Quadrant := q
  let ρ₀ : ℕ → ℝ := ρ
  let gap : ℝ → ℝ := fun t =>
    g (q₀ t) + h.1.1 * t + h.1.2 * (1 - t)
  let passageError : ℕ → ℝ := fun n =>
    lastPassage ω x (d n) / (n : ℝ) - g (q₀ (ρ₀ n))
  let endpointError : ℕ → ℝ := fun n =>
    (C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) +
      h.1.1 * ((d n).1 : ℝ) + h.1.2 * ((d n).2 : ℝ)) / (n : ℝ)
  have hcalibrated (n : ℕ) :
      lastPassage ω x (d n) = C x (x + (((d n).1 : ℤ), ((d n).2 : ℤ))) := by
    have hpath := calibrated_path_weight_eq_and_maximizing
      ω C hC hrec x (d n) (p n) (hcal n)
    exact hpath.2.symm.trans hpath.1
  have hpassageError : Tendsto passageError atTop (𝓝 0) := hpassage
  have hendpointError : Tendsto endpointError atTop (𝓝 0) := hendpoint
  have hgap_formula (n : ℕ) (hn : 0 < n) :
      gap (ρ₀ n) = endpointError n - passageError n := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hlengthR : ((d n).1 : ℝ) + ((d n).2 : ℝ) = (n : ℝ) := by
      exact_mod_cast hlen n
    have hsumRatio :
        ((d n).1 : ℝ) / (n : ℝ) + ((d n).2 : ℝ) / (n : ℝ) = 1 := by
      rw [← add_div, hlengthR, div_self hnR]
    have hsecondRatio : ((d n).2 : ℝ) / (n : ℝ) = 1 - ρ₀ n := by
      dsimp [ρ₀]
      linarith
    dsimp only [gap, endpointError, passageError]
    rw [hcalibrated n]
    rw [add_div, add_div, mul_div_assoc, mul_div_assoc, hsecondRatio]
    dsimp [ρ₀]
    ring
  have herrorDifference :
      Tendsto (fun n => endpointError n - passageError n) atTop (𝓝 0) := by
    simpa using hendpointError.sub hpassageError
  have hgapEventuallyEq :
      (fun n => gap (ρ₀ n)) =ᶠ[atTop]
        (fun n => endpointError n - passageError n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hgap_formula n hn
  have hgapLimit : Tendsto (fun n => gap (ρ₀ n)) atTop (𝓝 0) := by
    exact Filter.Tendsto.congr' hgapEventuallyEq.symm herrorDifference
  have hgapAbsLimit : Tendsto (fun n => |gap (ρ₀ n)|) atTop (𝓝 0) := by
    simpa [Function.comp_def, abs_zero] using
      (_root_.continuous_abs.tendsto (0 : ℝ)).comp hgapLimit
  have hrho_mem (n : ℕ) (hn : 0 < n) : ρ₀ n ∈ Set.Icc 0 1 := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have haNat : (d n).1 ≤ n := by
      have hlength := hlen n
      omega
    have haR : ((d n).1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast haNat
    have hlow : 0 ≤ ρ₀ n := by
      dsimp [ρ₀]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hupp : ρ₀ n ≤ 1 := by
      dsimp [ρ₀]
      rw [div_le_iff₀ hnR]
      nlinarith
    exact ⟨hlow, hupp⟩
  have hgapContinuous : ContinuousOn gap (Set.Icc 0 1) := by
    have hlinearFirst : ContinuousOn (fun t : ℝ => h.1.1 * t) (Set.Icc 0 1) := by
      fun_prop
    have hlinearSecond :
        ContinuousOn (fun t : ℝ => h.1.2 * (1 - t)) (Set.Icc 0 1) := by
      fun_prop
    have hcontinuousQ : ContinuousOn (fun t : ℝ => g (q₀ t)) (Set.Icc 0 1) := by
      simpa [q₀] using hcontinuous
    change ContinuousOn
      (fun t : ℝ => (g (q₀ t) + h.1.1 * t) + h.1.2 * (1 - t)) (Set.Icc 0 1)
    exact (hcontinuousQ.add hlinearFirst).add hlinearSecond
  intro ε hε
  let bad : Set ℝ :=
    Set.Icc 0 1 ∩ (Set.Iic ((left.1.1 : ℝ) - ε) ∪ Set.Ici ((right.1.1 : ℝ) + ε))
  have hbadClosed :
      IsClosed (Set.Iic ((left.1.1 : ℝ) - ε) ∪ Set.Ici ((right.1.1 : ℝ) + ε)) :=
    isClosed_Iic.union isClosed_Ici
  have hbadCompact : IsCompact bad := by
    dsimp [bad]
    exact isCompact_Icc.inter_right hbadClosed
  have hbadAbsContinuous : ContinuousOn (fun t : ℝ => |gap t|) bad := by
    exact _root_.continuous_abs.comp_continuousOn
      (hgapContinuous.mono (Set.inter_subset_left))
  by_cases hbadEmpty : bad = ∅
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hrho := hrho_mem n hn
    have hrhoNotBad : ρ₀ n ∉ bad := by rw [hbadEmpty]; simp
    have hrhoNotExterior :
        ρ₀ n ∉ Set.Iic ((left.1.1 : ℝ) - ε) ∪ Set.Ici ((right.1.1 : ℝ) + ε) := by
      intro hext
      exact hrhoNotBad ⟨hrho, hext⟩
    simpa only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] using hrhoNotExterior
  · have hbadNonempty : bad.Nonempty := Set.nonempty_iff_ne_empty.mpr hbadEmpty
    obtain ⟨t, htbad, hminimum⟩ := hbadCompact.exists_isMinOn hbadNonempty hbadAbsContinuous
    have hgapNe : gap t ≠ 0 := by
      intro hzero
      have hcontactAtT := (hcontact t htbad.1).mp hzero
      have hbadExterior :
          t ≤ (left.1.1 : ℝ) - ε ∨ (right.1.1 : ℝ) + ε ≤ t := by
        simpa only [Set.mem_union, Set.mem_Iic, Set.mem_Ici] using htbad.2
      rcases hbadExterior with hleft | hright
      · have hlt : t < (left.1.1 : ℝ) :=
          lt_of_le_of_lt hleft (sub_lt_self _ hε)
        exact (not_lt_of_ge hcontactAtT.1) hlt
      · have hlt : (right.1.1 : ℝ) < t :=
          lt_of_lt_of_le (lt_add_of_pos_right _ hε) hright
        exact (not_lt_of_ge hcontactAtT.2) hlt
    have hminimumPositive : 0 < |gap t| := abs_pos.mpr hgapNe
    have hgapSmall : ∀ᶠ n : ℕ in atTop, |gap (ρ₀ n)| < |gap t| := by
      exact hgapAbsLimit.eventually (Iio_mem_nhds hminimumPositive)
    filter_upwards [hgapSmall, eventually_gt_atTop (0 : ℕ)] with n hsmall hn
    have hrho := hrho_mem n hn
    by_contra hband
    have hrhoBad : ρ₀ n ∈ bad := by
      change ρ₀ n ∈ Set.Icc 0 1 ∩
        (Set.Iic ((left.1.1 : ℝ) - ε) ∪ Set.Ici ((right.1.1 : ℝ) + ε))
      refine ⟨hrho, ?_⟩
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici]
      rcases not_and_or.mp hband with hleft | hright
      · exact Or.inl (le_of_not_gt hleft)
      · exact Or.inr (le_of_not_gt hright)
    have hmin := hminimum hrhoBad
    change |gap t| ≤ |gap (ρ₀ n)| at hmin
    linarith

end LPP.Busemann
