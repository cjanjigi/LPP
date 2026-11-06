/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Probability.HalfLineEdge
import LPP_Foundations.Probability.TranslationEquiv
import Lean.Elab.Tactic.Omega
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The gain from adding the right block to a start set

Adding the `m` sites just to the right of the antidiagonal half-line `Z̃₋` to a start set
can only move the edge of the open cluster to the right, and it does so by at least as
much for a smaller start set. For the whole half-line, the expected gain is exactly `m`.

This is the gain inequality of Liggett type used at the end of the flat-edge argument.

## Main results

* `openEdge_union_gain_antitone`: the pathwise comparison.
* `integral_halfLine_rightBlock_gain`: the exact expected gain for `Z̃₋`, from
  translation invariance of the weight law.
* `lintegral_rightBlock_gain_ge`: the expected gain for an infinite subset of `Z̃₋`,
  as a lower integral, because for a sparse subset the edge need not be integrable.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the oriented-percolation
  gain lemma.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory Set
open scoped ENNReal

/-! ## Auxiliary lemmas -/

private theorem bddAbove_fst_reach (O : Set Lattice) (n : ℕ) {S : Set Lattice}
    (hS : BddAbove (Prod.fst '' S)) : BddAbove (Prod.fst '' openReachSet O S n) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨b + n, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact bddAbove_fst_openReachSet O S n b
    (fun u hu => hb (Set.mem_image_of_mem Prod.fst hu)) x hx

private theorem bddAbove_fst_union {S F : Set Lattice} (hS : BddAbove (Prod.fst '' S))
    (hF : BddAbove (Prod.fst '' F)) : BddAbove (Prod.fst '' (S ∪ F)) := by
  rw [Set.image_union]
  exact hS.union hF

/-- The edge of a union of two nonempty bounded sets is the larger of the two edges. -/
private theorem maxFirst_union_of_nonempty {X Y : Set Lattice} (hX : X.Nonempty)
    (hY : Y.Nonempty) (hbX : BddAbove (Prod.fst '' X)) (hbY : BddAbove (Prod.fst '' Y)) :
    maxFirst (X ∪ Y) = max (maxFirst X) (maxFirst Y) := by
  have hbXY := bddAbove_fst_union hbX hbY
  apply le_antisymm
  · obtain ⟨v, hv, hvv⟩ := maxFirst_mem (X ∪ Y) (hX.mono Set.subset_union_left) hbXY
    rw [← hvv]
    rcases hv with hv | hv
    · exact le_max_of_le_left (le_maxFirst X hbX hv)
    · exact le_max_of_le_right (le_maxFirst Y hbY hv)
  · refine max_le ?_ ?_
    · obtain ⟨v, hv, hvv⟩ := maxFirst_mem X hX hbX
      rw [← hvv]
      exact le_maxFirst (X ∪ Y) hbXY (Or.inl hv)
    · obtain ⟨v, hv, hvv⟩ := maxFirst_mem Y hY hbY
      rw [← hvv]
      exact le_maxFirst (X ∪ Y) hbXY (Or.inr hv)

/-- Adding sites to a start set does not decrease the edge, when the reached set is
nonempty and bounded. -/
private theorem openEdge_le_union (O A F : Set Lattice) (n : ℕ)
    (hA : (openReachSet O A n).Nonempty) (hbA : BddAbove (Prod.fst '' A))
    (hbF : BddAbove (Prod.fst '' F)) :
    openEdge O A n ≤ openEdge O (A ∪ F) n := by
  unfold openEdge
  obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ hA (bddAbove_fst_reach O n hbA)
  rw [← hvv]
  exact le_maxFirst _ (bddAbove_fst_reach O n (bddAbove_fst_union hbA hbF))
    (openReachSet_mono subset_rfl Set.subset_union_left n hv)

/-- The edge of `Z̃₋ ∪ F_m` is `m` plus the half-line edge of the shifted weights, once
the half-line reaches somewhere. -/
private theorem openEdge_halfLine_rightBlock_eq (ω : Environment) (m n : ℕ)
    (hne : (openReachSet (topSites ω) antidiagHalfLine n).Nonempty) :
    openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n =
      (m : ℤ) + halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n := by
  have hsub : antidiagHalfLine ⊆
      (fun z => ((m : ℤ), -(m : ℤ)) + z) '' antidiagHalfLine := by
    rw [← antidiagHalfLine_union_rightBlock]
    exact Set.subset_union_left
  rw [antidiagHalfLine_union_rightBlock]
  exact openEdge_translate ω antidiagHalfLine ((m : ℤ), -(m : ℤ)) n
    (hne.mono (openReachSet_mono subset_rfl hsub n)) bddAbove_fst_antidiagHalfLine

/-- Almost surely, the gain for the half-line is `m` plus the difference between the
half-line edge of the shifted weights and of the weights. -/
private theorem gain_ae_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (m n : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν,
      ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) -
        halfLineEdge ω n) =
      (m : ℝ) + (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ) -
        halfLineEdge ω n := by
  filter_upwards [ae_openReachSet_halfLine_infinite ν hp₀] with ω hω
  rw [openEdge_halfLine_rightBlock_eq ω m n (hω n).nonempty]
  push_cast
  ring

private theorem integrable_shifted_halfLineEdge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (m n : ℕ) :
    Integrable (fun ω => (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ))
      (environmentLaw ν) := by
  have hmp := measurePreserving_environmentTranslationEquiv ν ((m : ℤ), -(m : ℤ))
  have hint := integrable_halfLineEdge ν hp₀ n
  exact (hmp.integrable_comp hint.aestronglyMeasurable).2 hint

private theorem integrable_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (m n : ℕ) :
    Integrable (fun ω => ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) -
      halfLineEdge ω n)) (environmentLaw ν) := by
  have h := ((integrable_const (m : ℝ)).add
    (integrable_shifted_halfLineEdge ν hp₀ m n)).sub (integrable_halfLineEdge ν hp₀ n)
  exact h.congr ((gain_ae_eq ν hp₀ m n).mono fun ω hω => hω.symm)

private theorem gain_nonneg_ae (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (m n : ℕ) :
    0 ≤ᵐ[environmentLaw ν] fun ω =>
      ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) -
        halfLineEdge ω n) := by
  filter_upwards [ae_openReachSet_halfLine_infinite ν hp₀] with ω hω
  have h := openEdge_le_union (topSites ω) antidiagHalfLine (antidiagRightBlock m) n
    (hω n).nonempty bddAbove_fst_antidiagHalfLine (bddAbove_fst_antidiagRightBlock m)
  have h' : (halfLineEdge ω n : ℝ) ≤
      (openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) :=
    Int.cast_le.2 h
  simp only [Pi.zero_apply]
  linarith

/-! ## The gain from adding the right block -/

/-- Adding the sites of `F` to a smaller start set `A ⊆ B` raises the edge at least as much as
adding them to `B`. -/
theorem openEdge_union_gain_antitone (O A B F : Set Lattice) (n : ℕ) (hAB : A ⊆ B)
    (hA : (openReachSet O A n).Nonempty) (hB : BddAbove (Prod.fst '' B))
    (hF : BddAbove (Prod.fst '' F)) :
    openEdge O (B ∪ F) n - openEdge O B n ≤ openEdge O (A ∪ F) n - openEdge O A n := by
  have hbA : BddAbove (Prod.fst '' A) := hB.mono (Set.image_mono hAB)
  have hRAB : openReachSet O A n ⊆ openReachSet O B n :=
    openReachSet_mono subset_rfl hAB n
  unfold openEdge
  rw [openReachSet_union, openReachSet_union]
  by_cases hF' : (openReachSet O F n).Nonempty
  · have hRB : (openReachSet O B n).Nonempty := hA.mono hRAB
    rw [maxFirst_union_of_nonempty hRB hF' (bddAbove_fst_reach O n hB)
        (bddAbove_fst_reach O n hF),
      maxFirst_union_of_nonempty hA hF' (bddAbove_fst_reach O n hbA)
        (bddAbove_fst_reach O n hF)]
    have hle : maxFirst (openReachSet O A n) ≤ maxFirst (openReachSet O B n) := by
      obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ hA (bddAbove_fst_reach O n hbA)
      rw [← hvv]
      exact le_maxFirst _ (bddAbove_fst_reach O n hB) (hRAB hv)
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hF'
    rw [hF', Set.union_empty, Set.union_empty]
    omega

/-- The expected gain from adding the `m` sites of the right block to the half-line is exactly
`m`. -/
theorem integral_halfLine_rightBlock_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (m n : ℕ) :
    ∫ ω, ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) -
      halfLineEdge ω n) ∂environmentLaw ν = m := by
  have hmp := measurePreserving_environmentTranslationEquiv ν ((m : ℤ), -(m : ℤ))
  have hint := integrable_halfLineEdge ν hp₀ n
  have hint' := integrable_shifted_halfLineEdge ν hp₀ m n
  have hshift : ∫ ω, (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ)
      ∂environmentLaw ν = ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw ν :=
    hmp.integral_comp' (fun ω => (halfLineEdge ω n : ℝ))
  have h1 : ∫ ω, ((m : ℝ) + (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ) -
      halfLineEdge ω n) ∂environmentLaw ν =
      (m : ℝ) + ∫ ω, (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ)
        ∂environmentLaw ν - ∫ ω, (halfLineEdge ω n : ℝ) ∂environmentLaw ν := by
    have hI : Integrable (fun ω => (m : ℝ) +
        (halfLineEdge (fun z => ω (((m : ℤ), -(m : ℤ)) + z)) n : ℝ)) (environmentLaw ν) :=
      (integrable_const (m : ℝ)).add hint'
    rw [integral_sub hI hint, integral_add (integrable_const (m : ℝ)) hint']
    simp
  rw [integral_congr_ae (gain_ae_eq ν hp₀ m n), h1, hshift]
  ring

/-- For an infinite subset `A` of the half-line, the lower integral of the gain from adding the
right block is at least `m`. -/
theorem lintegral_rightBlock_gain_ge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine) (hinf : A.Infinite)
    (m n : ℕ) :
    (m : ℝ≥0∞) ≤ ∫⁻ ω, ENNReal.ofReal
      ((openEdge (topSites ω) (A ∪ antidiagRightBlock m) n : ℝ) -
        openEdge (topSites ω) A n) ∂environmentLaw ν := by
  calc (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) := (ENNReal.ofReal_natCast m).symm
    _ = ENNReal.ofReal (∫ ω, ((openEdge (topSites ω)
          (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) - halfLineEdge ω n)
          ∂environmentLaw ν) := by rw [integral_halfLine_rightBlock_gain ν hp₀ m n]
    _ = ∫⁻ ω, ENNReal.ofReal ((openEdge (topSites ω)
          (antidiagHalfLine ∪ antidiagRightBlock m) n : ℝ) - halfLineEdge ω n)
          ∂environmentLaw ν :=
        ofReal_integral_eq_lintegral_ofReal (integrable_gain ν hp₀ m n)
          (gain_nonneg_ae ν hp₀ m n)
    _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_openReachSet_nonempty_of_infinite ν hp₀ A hA hinf] with ω hω
        refine ENNReal.ofReal_le_ofReal ?_
        have h := openEdge_union_gain_antitone (topSites ω) A antidiagHalfLine
          (antidiagRightBlock m) n hA (hω n) bddAbove_fst_antidiagHalfLine
          (bddAbove_fst_antidiagRightBlock m)
        have h' : ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock m) n -
            openEdge (topSites ω) antidiagHalfLine n : ℤ) : ℝ) ≤
            ((openEdge (topSites ω) (A ∪ antidiagRightBlock m) n -
              openEdge (topSites ω) A n : ℤ) : ℝ) := Int.cast_le.2 h
        have e : halfLineEdge ω n = openEdge (topSites ω) antidiagHalfLine n := rfl
        rw [e]
        push_cast at h'
        exact h'

end LPPDifferentiability
