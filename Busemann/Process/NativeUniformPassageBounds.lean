/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeLeftPassageBounds
public import Busemann.Process.NativeRightPassageBounds
import ProbabilityBasics.Analysis.GradedSequences
import Mathlib.Tactic

/-! Uniform neighboring-start passage bounds over endpoint displacements. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability LPP.Busemann
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- The native left sequence bounds hold at all sufficiently large endpoint displacements
from each fixed start; see GRS arXiv:1510.00859v2, Theorem 6.1, Step 1. -/
theorem ae_native_uniform_passage_difference_bounds_left_of_support_face
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g,
      SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g,
        SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) =
        -finiteTiltCoordinate h.1 i)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hθface : ∀ ζ ∈ supportFace g h, θ < (ζ.1.1 : ℝ)) :
    ∀ᵐ s ∂P, ∀ x : Lattice, ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 → ((d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ θ) →
      0 < d.1 + d.2 ∧
        (0 < d.1 → B x (x + (1, 0)) s ≤
            lastPassage (processEnvironment s) x d -
              lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2)) ∧
        (0 < d.2 → lastPassage (processEnvironment s) x d -
              lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1) ≤
            B x (x + (0, 1)) s) := by
  classical
  have hNative := ae_native_passage_difference_bounds_left_of_support_face
    μ hmoment hnonconstant P hMarginal hShift B hB hInt hRec
    g hg η h hh hext hMean θ hθ0 hθ1 hθface
  filter_upwards [hNative] with s hs
  intro x
  let grade : ℕ × ℕ → ℕ := fun d => d.1 + d.2
  let Q : ℕ × ℕ → Prop := fun d =>
    (d.1 : ℝ) / ((grade d : ℕ) : ℝ) ≤ θ
  let R : ℕ × ℕ → Prop := fun d =>
    0 < grade d ∧
      (0 < d.1 → B x (x + (1, 0)) s ≤
        lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2)) ∧
      (0 < d.2 → lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1) ≤
        B x (x + (0, 1)) s)
  have hfill : ∀ n, grade (0, n) = n := by
    intro n
    simp only [grade, Nat.zero_add]
  have hfillQ : ∀ᶠ n : ℕ in atTop, Q (0, n) := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [Q, grade, Nat.zero_add, Nat.cast_zero, zero_div] using hθ0
  have hseq : ∀ D : ℕ → ℕ × ℕ,
      (∀ n, grade (D n) = n) →
      (∀ᶠ n : ℕ in atTop, Q (D n)) →
      ∀ᶠ n : ℕ in atTop, R (D n) := by
    intro D hlen hQ
    have hratio : ∀ᶠ n : ℕ in atTop,
        ((D n).1 : ℝ) / (n : ℝ) ≤ θ := by
      filter_upwards [hQ] with n hn
      simpa only [Q, hlen n] using hn
    have hresult := hs x D hlen hratio
    simpa only [R, grade, hlen] using hresult
  have hUniform := ProbabilityBasics.eventually_uniform_of_graded_sequences
    grade Q R (fun n => (0, n)) hfill hfillQ hseq
  obtain ⟨N, hN⟩ := eventually_atTop.mp hUniform
  refine ⟨N, ?_⟩
  intro d hd hQ
  exact hN (grade d) hd d rfl hQ

/-- The native right sequence bounds hold at all sufficiently large endpoint displacements
from each fixed start; see GRS arXiv:1510.00859v2, Theorem 6.1, Step 1. -/
theorem ae_native_uniform_passage_difference_bounds_right_of_support_face
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, MeasurePreserving (processShift z) P P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : is_shift_covariant_cocycle P processShift B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (hRec : recovers_weight_map_ae P processEnvironment B)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g)
    (η : InteriorDirection) (h : SupportTilt g)
    (hh : SupportsAt g η h.1)
    (hext : (∀ k : SupportTilt g,
      SupportsAt g η k.1 → h.1.1 ≤ k.1.1) ∨
      (∀ k : SupportTilt g,
        SupportsAt g η k.1 → k.1.1 ≤ h.1.1))
    (hMean : ∀ i : Fin 2,
      (∫ s, B 0 (finiteEdgeStep i) s ∂P) =
        -finiteTiltCoordinate h.1 i)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθface : ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) < θ) :
    ∀ᵐ s ∂P, ∀ x : Lattice, ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 → (θ ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ)) →
      0 < d.1 + d.2 ∧
        (0 < d.1 → lastPassage (processEnvironment s) x d -
              lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2) ≤
            B x (x + (1, 0)) s) ∧
        (0 < d.2 → B x (x + (0, 1)) s ≤
            lastPassage (processEnvironment s) x d -
              lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1)) := by
  classical
  have hNative := ae_native_passage_difference_bounds_right_of_support_face
    μ hmoment hnonconstant P hMarginal hShift B hB hInt hRec
    g hg η h hh hext hMean θ hθ0 hθ1 hθface
  filter_upwards [hNative] with s hs
  intro x
  let grade : ℕ × ℕ → ℕ := fun d => d.1 + d.2
  let Q : ℕ × ℕ → Prop := fun d =>
    θ ≤ (d.1 : ℝ) / ((grade d : ℕ) : ℝ)
  let R : ℕ × ℕ → Prop := fun d =>
    0 < grade d ∧
      (0 < d.1 → lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2) ≤
        B x (x + (1, 0)) s) ∧
      (0 < d.2 → B x (x + (0, 1)) s ≤
        lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1))
  have hfill : ∀ n, grade (n, 0) = n := by intro n; rfl
  have hfillQ : ∀ᶠ n : ℕ in atTop, Q (n, 0) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
    simpa only [Q, grade, Nat.add_zero, div_self hnR] using hθ1
  have hseq : ∀ D : ℕ → ℕ × ℕ,
      (∀ n, grade (D n) = n) →
      (∀ᶠ n : ℕ in atTop, Q (D n)) →
      ∀ᶠ n : ℕ in atTop, R (D n) := by
    intro D hlen hQ
    have hratio : ∀ᶠ n : ℕ in atTop,
        θ ≤ ((D n).1 : ℝ) / (n : ℝ) := by
      filter_upwards [hQ] with n hn
      simpa only [Q, hlen n] using hn
    have hresult := hs x D hlen hratio
    simpa only [R, grade, hlen] using hresult
  have hUniform := ProbabilityBasics.eventually_uniform_of_graded_sequences
    grade Q R (fun n => (n, 0)) hfill hfillQ hseq
  obtain ⟨N, hN⟩ := eventually_atTop.mp hUniform
  refine ⟨N, ?_⟩
  intro d hd hQ
  exact hN (grade d) hd d rfl hQ

end LPP.Busemann

end
