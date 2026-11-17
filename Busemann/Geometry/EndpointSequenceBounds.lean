/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ApproachesFaceInterval
public import Busemann.Frozen.Definitions.LatticeEndpoint
public import Busemann.Frozen.Definitions.FiniteEdgeStep
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic

/-! Coordinate escape and signed-start reachability for face-approaching endpoints. -/

@[expose] public section

open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

/-- Both endpoint coordinates tend to infinity when the normalized horizontal
coordinate approaches an interval contained in the interior of the unit-sum
segment (GRS 1510.00860v2, (3.8)). -/
theorem approachesFaceInterval_tendsto_coordinates
    (v : ℕ → ℕ × ℕ) (left right : InteriorDirection)
    (hv : approachesFaceInterval v left right) :
    Tendsto (fun n => (v n).1) atTop atTop ∧
      Tendsto (fun n => (v n).2) atTop atTop := by
  let level : ℕ → ℕ := fun n => (v n).1 + (v n).2
  let ρ : ℕ → ℝ := fun n => ((v n).1 : ℝ) / (level n : ℝ)
  have hlevel : Tendsto level atTop atTop := hv.1
  have hleft : (left.1.1 : ℝ) ≤ liminf ρ atTop := hv.2.1
  have hright : limsup ρ atTop ≤ (right.1.1 : ℝ) := hv.2.2
  -- The ratio is bounded even at the finitely many possible zero levels.
  have hρbounds (n : ℕ) : 0 ≤ ρ n ∧ ρ n ≤ 1 := by
    by_cases hz : level n = 0
    · simp [ρ, hz]
    · have hpos : (0 : ℝ) < (level n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hpos.le
      · apply (div_le_iff₀ hpos).2
        dsimp [level]
        simpa only [one_mul] using
          (show ((v n).1 : ℝ) ≤ (((v n).1 + (v n).2 : ℕ) : ℝ) by
            exact_mod_cast Nat.le_add_right (v n).1 (v n).2)
  have hboundedBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) ρ :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hρbounds n).1)
  have hboundedAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) ρ :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hρbounds n).2)
  have hleftPos : (0 : ℝ) < (left.1.1 : ℝ) := by exact_mod_cast left.2.1
  have hrightLt : (right.1.1 : ℝ) < 1 := by
    have hsum := right.2.2.2
    have hsecond : (0 : ℝ) < (right.1.2 : ℝ) := by exact_mod_cast right.2.2.1
    linarith
  let a : ℝ := (left.1.1 : ℝ) / 2
  let b : ℝ := ((right.1.1 : ℝ) + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  have hbetweenLeft : a < liminf ρ atTop := lt_of_lt_of_le (by dsimp [a]; linarith) hleft
  have hbetweenRight : limsup ρ atTop < b := lt_of_le_of_lt hright (by dsimp [b]; linarith)
  have hρleft : ∀ᶠ n : ℕ in atTop, a < ρ n :=
    eventually_lt_of_lt_liminf hbetweenLeft hboundedBelow
  have hρright : ∀ᶠ n : ℕ in atTop, ρ n < b :=
    eventually_lt_of_limsup_lt hbetweenRight hboundedAbove
  -- On one tail, each coordinate dominates a fixed positive fraction of level.
  constructor
  · apply tendsto_atTop.2
    intro K
    obtain ⟨M, hM⟩ := exists_nat_gt (max 1 ((K : ℝ) / a))
    have hMpos : 0 < M := by
      have hm : (1 : ℝ) < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
      exact_mod_cast (show (0 : ℝ) < (M : ℝ) by linarith)
    have hKbound : (K : ℝ) < a * (M : ℝ) := by
      have hdiv : (K : ℝ) / a < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
      simpa only [mul_comm] using (div_lt_iff₀ ha).mp hdiv
    filter_upwards [hρleft, (tendsto_atTop.1 hlevel M)] with n hn hMn
    have hlevelPos : (0 : ℝ) < (level n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hMpos hMn
    have hMnR : (M : ℝ) ≤ (level n : ℝ) := by exact_mod_cast hMn
    have hcoordinate : a * (level n : ℝ) < ((v n).1 : ℝ) :=
      (lt_div_iff₀ hlevelPos).mp hn
    have hKR : (K : ℝ) ≤ ((v n).1 : ℝ) :=
      le_of_lt (lt_of_lt_of_le hKbound (mul_le_mul_of_nonneg_left hMnR ha.le) |>.trans hcoordinate)
    exact_mod_cast hKR
  · apply tendsto_atTop.2
    intro K
    have hc : 0 < 1 - b := sub_pos.mpr hb
    obtain ⟨M, hM⟩ := exists_nat_gt (max 1 ((K : ℝ) / (1 - b)))
    have hMpos : 0 < M := by
      have hm : (1 : ℝ) < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
      exact_mod_cast (show (0 : ℝ) < (M : ℝ) by linarith)
    have hKbound : (K : ℝ) < (1 - b) * (M : ℝ) := by
      have hdiv : (K : ℝ) / (1 - b) < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp hdiv
    filter_upwards [hρright, (tendsto_atTop.1 hlevel M)] with n hn hMn
    have hlevelPos : (0 : ℝ) < (level n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hMpos hMn
    have hMnR : (M : ℝ) ≤ (level n : ℝ) := by exact_mod_cast hMn
    have hfirst : ((v n).1 : ℝ) < b * (level n : ℝ) :=
      (div_lt_iff₀ hlevelPos).mp hn
    have hsum : ((v n).1 : ℝ) + ((v n).2 : ℝ) = (level n : ℝ) := by
      dsimp [level]
      push_cast
      ring
    have hsecond : (1 - b) * (level n : ℝ) < ((v n).2 : ℝ) := by
      nlinarith only [hfirst, hsum]
    have hKR : (K : ℝ) ≤ ((v n).2 : ℝ) :=
      le_of_lt (lt_of_lt_of_le hKbound (mul_le_mul_of_nonneg_left hMnR hc.le) |>.trans hsecond)
    exact_mod_cast hKR

/-- A face-approaching endpoint eventually lies above any signed start and
both of its unit-step neighbors (GRS 1510.00860v2, (3.8)). -/
theorem approachesFaceInterval_eventually_reaches
    (v : ℕ → ℕ × ℕ) (left right : InteriorDirection)
    (hv : approachesFaceInterval v left right) (x : Lattice) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      x ≤ latticeEndpoint (v n) ∧
        ∀ i : Fin 2, x + finiteEdgeStep i ≤ latticeEndpoint (v n) := by
  have hcoordinates := approachesFaceInterval_tendsto_coordinates v left right hv
  obtain ⟨K, hK⟩ := exists_nat_gt (max (x.1 : ℝ) (x.2 : ℝ) + 1)
  have hx1 : x.1 + 1 ≤ (K : ℤ) := by
    have hmax : (x.1 : ℝ) ≤ max (x.1 : ℝ) (x.2 : ℝ) := le_max_left _ _
    exact_mod_cast (show (x.1 : ℝ) + 1 ≤ (K : ℝ) by linarith [hK, hmax])
  have hx2 : x.2 + 1 ≤ (K : ℤ) := by
    have hmax : (x.2 : ℝ) ≤ max (x.1 : ℝ) (x.2 : ℝ) := le_max_right _ _
    exact_mod_cast (show (x.2 : ℝ) + 1 ≤ (K : ℝ) by linarith [hK, hmax])
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_atTop.1 hcoordinates.1 K).and (tendsto_atTop.1 hcoordinates.2 K))
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : (K : ℤ) ≤ ((v n).1 : ℤ) := by exact_mod_cast (hN n hn).1
  have hn2 : (K : ℤ) ≤ ((v n).2 : ℤ) := by exact_mod_cast (hN n hn).2
  constructor
  · change x.1 ≤ ((v n).1 : ℤ) ∧ x.2 ≤ ((v n).2 : ℤ)
    exact ⟨by omega, by omega⟩
  · intro i
    fin_cases i
    · simpa [finiteEdgeStep, latticeEndpoint, Prod.le_def] using
        (show x.1 + 1 ≤ ((v n).1 : ℤ) ∧ x.2 ≤ ((v n).2 : ℤ) from
          ⟨by omega, by omega⟩)
    · simpa [finiteEdgeStep, latticeEndpoint, Prod.le_def] using
        (show x.1 ≤ ((v n).1 : ℤ) ∧ x.2 + 1 ≤ ((v n).2 : ℤ) from
          ⟨by omega, by omega⟩)

end LPP.Busemann
