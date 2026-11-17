/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Geometry.ExtremeEndpointContinuity
import Busemann.Geometry.StrictDirectionSequences
import Busemann.Geometry.SupportOrder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped NNReal Topology
namespace LPP.Busemann

/-- If β lies on a right extreme face, it lies on the left extreme face at
that face's right endpoint. This is the endpoint reciprocity in the reflected
liminf argument of GRS arXiv:1510.00860v1, Theorem 2.1(i). -/
theorem support_left_at_right_endpoint_of_extreme_face
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hL hR : InteriorDirection → SupportTilt g)
    (leftEndpoint rightEndpoint : InteriorDirection → InteriorDirection)
    (hExtreme : ∀ ξ : InteriorDirection,
      SupportsAt g ξ (hL ξ).1 ∧ SupportsAt g ξ (hR ξ).1 ∧
      ∀ h : SupportTilt g, SupportsAt g ξ h.1 →
        (hL ξ).1.1 ≤ h.1.1 ∧ h.1.1 ≤ (hR ξ).1.1)
    (hInterval : ∀ ξ η : InteriorDirection,
      η ∈ supportFacesUnion g (hL ξ) (hR ξ) ↔
        (leftEndpoint ξ).1.1 ≤ η.1.1 ∧
          η.1.1 ≤ (rightEndpoint ξ).1.1)
    (β : InteriorDirection) :
    SupportsAt g β (hL (rightEndpoint β)).1 := by
  let ξ := rightEndpoint β
  have hβB : (leftEndpoint β).1.1 ≤ β.1.1 ∧
      β.1.1 ≤ ξ.1.1 :=
    (hInterval β β).mp (Or.inl (hExtreme β).1)
  have hξMem : ξ ∈ supportFacesUnion g (hL β) (hR β) :=
    (hInterval β ξ).mpr ⟨hβB.1.trans hβB.2, le_rfl⟩
  by_cases heq : β = ξ
  · change SupportsAt g β (hL ξ).1
    rw [← heq]
    exact (hExtreme β).1
  have hStrict : (β.1.1 : ℝ) < (ξ.1.1 : ℝ) := by
    have hle : (β.1.1 : ℝ) ≤ (ξ.1.1 : ℝ) := by exact_mod_cast hβB.2
    apply lt_of_le_of_ne hle
    intro hcoord
    apply heq
    apply Subtype.ext
    apply Prod.ext
    · exact NNReal.coe_injective hcoord
    · apply NNReal.coe_injective
      linarith only [β.2.2.2, ξ.2.2.2, hcoord]
  have hRξ : SupportsAt g ξ (hR β).1 := by
    rcases hξMem with hLeft | hRight
    · have hRle := support_first_coord_le_of_direction_lt g hhom β ξ
        (hR β) (hL β) hStrict (hExtreme β).2.1 hLeft
      have hLle := ((hExtreme β).2.2 (hR β) (hExtreme β).2.1).1
      have hTilt : hL β = hR β :=
        (supportTilt_coordinate_order g hhom (hL β) (hR β)).2
          (le_antisymm hLle hRle)
      rw [← hTilt]
      exact hLeft
    · exact hRight
  have hRleL := support_first_coord_le_of_direction_lt g hhom β ξ
    (hR β) (hL ξ) hStrict (hExtreme β).2.1 (hExtreme ξ).1
  have hLleR := ((hExtreme ξ).2.2 (hR β) hRξ).1
  have hTilt : hL ξ = hR β :=
    (supportTilt_coordinate_order g hhom (hL ξ) (hR β)).2
      (le_antisymm hLleR hRleL)
  rw [hTilt]
  exact (hExtreme β).2.1

/-- A dense countable direction family has a subsequence strictly to the
right of any interior direction and converging to it. This is the outward
selection in GRS arXiv:1510.00860v1, Theorem 2.1(i). -/
theorem exists_dense_directions_from_right
    (D : ℕ → InteriorDirection) (hDense : DenseRange D)
    (ξ : InteriorDirection) :
    ∃ i : ℕ → ℕ,
      (∀ n, ξ.1.1 < (D (i n)).1.1) ∧
      Tendsto (fun n => D (i n)) atTop (𝓝 ξ) := by
  obtain ⟨_, r, hside, _, hr⟩ := exists_strict_left_right_direction_sequences ξ
  let radius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hRadiusPos (n : ℕ) : 0 < radius n := by
    dsimp only [radius]
    positivity
  have hRadiusZero : Tendsto radius atTop (𝓝 0) := by
    simpa only [radius] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let U (n : ℕ) : Set InteriorDirection :=
    {ζ | ξ.1.1 < ζ.1.1} ∩ Metric.ball (r n) (radius n)
  have hcoord : Continuous (fun ζ : InteriorDirection => ζ.1.1) := by fun_prop
  have hOpen (n : ℕ) : IsOpen (U n) :=
    (isOpen_Ioi.preimage hcoord).inter Metric.isOpen_ball
  have hNonempty (n : ℕ) : (U n).Nonempty := by
    refine ⟨r n, (hside n).2, ?_⟩
    simpa only [Metric.mem_ball, dist_self] using hRadiusPos n
  choose i hi using fun n => hDense.exists_mem_open (hOpen n) (hNonempty n)
  have hDist : Tendsto (fun n => dist (r n) (D (i n))) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => (dist_nonneg : 0 ≤ dist (r n) (D (i n))))
      (fun n => ?_) hRadiusZero
    rw [dist_comm]
    exact (Metric.mem_ball.mp (hi n).2).le
  refine ⟨i, fun n => (hi n).1, ?_⟩
  exact hr.congr_dist hDist

end LPP.Busemann
