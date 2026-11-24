/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatBlockSource.Confinement
public import Differentiability.FinalDraft.FlatBlockSource.Events
import Mathlib.Tactic

/-! The probability of both full confined crossings tends to one,
as in Durrett (1984), Section 9, property (iii). -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace LPPDifferentiability.FinalDraft.FlatBlockSource

private theorem exponential_summable (A B : ℝ) (hB : 0 < B) :
    Summable (fun n : ℕ => A * Real.exp (-(B * (n : ℝ)))) := by
  have hq := summable_geometric_of_lt_one (Real.exp_pos (-B)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hB))
  convert hq.mul_left A using 1
  funext n
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- Summing the actual translated overspeed events gives the left-side
crossing estimate of Durrett, p. 1025. -/
theorem leftExcursion_failure_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α A B : ℝ} (hB : 0 < B)
    (hdev : ∀ n : ℕ, (environmentLaw ν).real
      {ω | (α + α / 44) * (n : ℝ) ≤ rotatedEdge ω n} ≤ A * Real.exp (-(B * n)))
    {N M : ℕ} (hN : 0 < N) (hw100 : (100 : ℤ) ≤ roundedWidth α N)
    (hMW : (M : ℤ) ≤ roundedWidth α N) :
    (environmentLaw ν).real (LeftExcursion N (roundedWidth α N)) ≤
      ∑' i : ℕ, A * Real.exp (-(B * ((i + M : ℕ) : ℝ))) := by
  let D (n : ℕ) : Set Environment := {ω | (α + α / 44) * (n : ℝ) ≤ rotatedEdge ω n}
  let a (n : ℕ) := traceSite 0 (22 * N - n) (lowerBoundary N (roundedWidth α N) (22 * N - n))
  let E (n : ℕ) := environmentTranslationEquiv (a n) ⁻¹' D n
  have hDm (n : ℕ) : MeasurableSet (D n) :=
    measurableSet_le measurable_const (measurable_rotatedEdge n)
  calc
    _ ≤ (environmentLaw ν).real (⋃ n ∈ Finset.Icc M (22 * N), E n) :=
      measureReal_mono (leftExcursion_subset_deviation hN hw100 hMW) (measure_ne_top _ _)
    _ ≤ ∑ n ∈ Finset.Icc M (22 * N), (environmentLaw ν).real (E n) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.Icc M (22 * N), A * Real.exp (-(B * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro n _
      rw [show E n = environmentTranslationEquiv (a n) ⁻¹' D n from rfl,
        (measurePreserving_environmentTranslationEquiv ν (a n)).measureReal_preimage
          (hDm n).nullMeasurableSet]
      exact hdev n
    _ ≤ _ := by
      have hA : 0 ≤ A := by simpa using (measureReal_nonneg.trans (hdev 0))
      have hI : Finset.Icc M (22 * N) = Finset.Ico M (22 * N + 1) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hI, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_comm M]
      exact ((summable_nat_add_iff M).2 (exponential_summable A B hB)).sum_le_tsum _
        (fun i _ => mul_nonneg hA (Real.exp_pos _).le)

/-- A positive centered speed makes the two confined crossings jointly
likely. The block geometry keeps the fixed one-dependence range. -/
theorem exists_goodBlock_small_failure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : 0 < ν {1}) {β : ℝ} (hβ : 1 / 2 < β)
    (hglb : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N : ℕ, ∃ w : ℤ, 0 < N ∧ 0 < w ∧ (environmentLaw ν).real ((GoodBlock N w 0)ᶜ) < ζ := by
  let α := 2 * β - 1
  have hα : 0 < α := by dsimp [α]; linarith
  obtain ⟨b, hb, hlim⟩ := exists_constant_halfLineEdge_speed_of_bddBelow ν hν ⟨β, hglb.1⟩
  rw [hb.unique hglb] at hlim
  obtain ⟨A, B, -, hB, hdev⟩ := exponential_rotatedEdge_upper ν hν
    (b := α + α / 44) (by change α < α + α / 44; linarith) hglb
  have hsumlim := tendsto_sum_nat_add (fun n : ℕ => A * Real.exp (-(B * (n : ℝ))))
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hsumlim).2 (ζ / 8) (by positivity))
  let F (N : ℕ) : Set Environment := {ω | ¬ ∀ n ≤ 22 * N,
    |rotatedEdge ω n - α * (n : ℝ)| ≤ (roundedWidth α N : ℝ) / 5}
  have hF := rotatedEdge_uniform_failure_tendsto ν hβ hlim
  obtain ⟨L, hL⟩ := eventually_atTop.mp ((tendsto_order.mp hF).2 (ζ / 8) (by positivity))
  obtain ⟨L', hL'⟩ := exists_nat_gt (((M : ℝ) + 101) / α)
  let N := max (max L L') 1
  let w := roundedWidth α N
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hL'N : L' ≤ N := (le_max_right L L').trans (le_max_left _ 1)
  have hs : (M : ℝ) + 101 < α * (N : ℝ) := by
    have hcast : (L' : ℝ) ≤ N := by exact_mod_cast hL'N
    simpa only [mul_comm (N : ℝ) α] using (div_lt_iff₀ hα).mp (hL'.trans_le hcast)
  have hwLo : (100 : ℤ) ≤ w := by
    apply Int.le_floor.mpr
    change (100 : ℝ) ≤ α * (N : ℝ)
    linarith only [hs, show (M : ℝ) ≥ 0 by positivity]
  have hMw : (M : ℤ) ≤ w := by
    apply Int.le_floor.mpr
    push_cast
    linarith only [hs]
  have hUpper : (environmentLaw ν).real (F N) < ζ / 8 :=
    hL N ((le_max_left L L').trans (le_max_left _ 1))
  let a := traceSite 0 0 (initialBoundary w)
  have hFm : MeasurableSet (F N) := measurableSet_box_failure α N
  have hUp : (environmentLaw ν).real (environmentTranslationEquiv a ⁻¹' F N) < ζ / 8 := by
    rw [(measurePreserving_environmentTranslationEquiv ν a).measureReal_preimage
      hFm.nullMeasurableSet]
    exact hUpper
  have hLeft : (environmentLaw ν).real (LeftExcursion N w) < ζ / 8 :=
    (leftExcursion_failure_le ν hB hdev hN hwLo hMw).trans_lt (hM M le_rfl)
  have hsub : (RightBlock N w 0)ᶜ ⊆
      (environmentTranslationEquiv a ⁻¹' F N) ∪ LeftExcursion N w := by
    intro ω hω
    by_contra h
    have hupper : ω ∉ environmentTranslationEquiv a ⁻¹' F N := fun he => h (Or.inl he)
    have hleft : ω ∉ LeftExcursion N w := fun he => h (Or.inr he)
    have hcap : ∀ n ≤ 22 * N,
        |rotatedEdge (environmentTranslationEquiv a ω) n - α * (n : ℝ)| ≤ (w : ℝ) / 5 := by
      simpa only [F, mem_preimage, mem_ofPred_eq, not_not] using hupper
    exact hω (rightBlock_of_edges hN hwLo hcap hleft)
  have hRight : (environmentLaw ν).real ((RightBlock N w 0)ᶜ) ≤
      (environmentLaw ν).real (environmentTranslationEquiv a ⁻¹' F N) +
      (environmentLaw ν).real (LeftExcursion N w) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hw : 0 < w := by omega
  obtain ⟨S, hS⟩ := exists_finset_blockSupport N w hw.le 0
  have hmeas : MeasurableSet (RightBlock N w 0) :=
    measurableSet_of_open_sites S _ (fun ω ω' h => rightBlock_local hN hw.le _ ω ω'
      (fun z hz => h z ((hS z).2 hz)))
  have hswap : (environmentLaw ν).real (environmentSwap ⁻¹' ((RightBlock N w 0)ᶜ)) =
      (environmentLaw ν).real ((RightBlock N w 0)ᶜ) :=
    (measurePreserving_environmentSwap ν).measureReal_preimage hmeas.compl.nullMeasurableSet
  refine ⟨N, w, hN, hw, ?_⟩
  rw [goodBlock_eq_inter_swap, compl_inter, ← preimage_compl]
  have hUnion := measureReal_union_le (μ := environmentLaw ν) ((RightBlock N w 0)ᶜ)
    (environmentSwap ⁻¹' ((RightBlock N w 0)ᶜ))
  linarith only [hUp, hLeft, hRight, hswap, hUnion, hζ]

end LPPDifferentiability.FinalDraft.FlatBlockSource
