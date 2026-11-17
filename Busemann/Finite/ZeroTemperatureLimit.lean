/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteBusemannEdge
public import LPP_Foundations.Model.Paths.Fintype
public import LPP_Foundations.Model.Paths.Nonempty
public import ProbabilityBasics.Analysis.FiniteLogSumExpLimit
import Busemann.Finite.PotentialOrder
import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

/-! Actual finite path sums converge to the last-passage potential and edges. -/

@[expose] public section

open Filter LPPDifferentiability
open scoped BigOperators Topology

namespace LPP.Busemann

/-- The actual normalized finite log partition tends to the finite
last-passage potential, and its normalized edge differences tend to the exact
finite Busemann edges. This is the finite zero-temperature passage in
JR1810.03580v3, Appendix A.1, proof of Lemma 4.11. -/
theorem finite_partition_and_edge_zero_temperature_limits
    (ω : Environment) (h : ℝ × ℝ) :
    let Z : ℝ → ℕ → Lattice → ℝ := fun β n y =>
      ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    let F : ℝ → ℕ → Lattice → ℝ := fun β n y => Real.log (Z β n y) / β
    (∀ (N : ℕ) (x : Lattice),
      Tendsto (fun β : ℝ => F β N x) atTop
        (𝓝 ((finiteTiltedPotential ω h x (x.1 + x.2 + (N : ℤ))).toReal))) ∧
    (∀ (N : ℕ) (x : Lattice) (i : Fin 2),
      Tendsto (fun β : ℝ => F β (N + 1) x - F β N (x + finiteEdgeStep i) -
        finiteTiltCoordinate h i) atTop
        (𝓝 (finiteBusemannEdge ω h x (x.1 + x.2 + ((N + 1 : ℕ) : ℤ)) i))) := by
  classical
  let Z : ℝ → ℕ → Lattice → ℝ := fun β n y =>
    ∑ k : Fin (n + 1), ∑ p : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω p + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))
  let F : ℝ → ℕ → Lattice → ℝ := fun β n y => Real.log (Z β n y) / β
  change (∀ (N : ℕ) (x : Lattice), Tendsto (fun β : ℝ => F β N x) atTop
      (𝓝 ((finiteTiltedPotential ω h x (x.1 + x.2 + (N : ℤ))).toReal))) ∧ _

  have hpressure (N : ℕ) (x : Lattice) :
      Tendsto (fun β : ℝ => F β N x) atTop
        (𝓝 ((finiteTiltedPotential ω h x (x.1 + x.2 + (N : ℤ))).toReal)) := by
    let n : ℤ := x.1 + x.2 + (N : ℤ)
    let m : ℕ := (n - (x.1 + x.2)).toNat
    have hactive : x.1 + x.2 ≤ n := by dsimp only [n]; omega
    have hlen : m = N := by dsimp only [m, n]; omega
    have htop := finiteTiltedPotential_ne_top ω h x n hactive
    have hbot := finiteTiltedPotential_ne_bot ω h x n hactive
    let I := Σ k : Fin (N + 1), LPPDifferentiability.Path x (k.val, N - k.val)
    let k0 : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    let : Nonempty I := ⟨⟨k0, Classical.choice (inferInstance :
      Nonempty (LPPDifferentiability.Path x (k0.val, N - k0.val)))⟩⟩
    let E : I → ℝ := fun a => pathWeight ω a.2 + h.1 * (a.1.val : ℝ) +
      h.2 * ((N - a.1.val : ℕ) : ℝ)
    let M : ℝ := Finset.univ.sup' Finset.univ_nonempty E

    -- Every actual path energy is bounded by its endpoint passage maximum and the potential.
    have hMle : M ≤ (finiteTiltedPotential ω h x n).toReal := by
      apply Finset.sup'_le
      intro a _
      let k : Fin (m + 1) := ⟨a.1.val, by rw [hlen]; exact a.1.isLt⟩
      have hcandidate := finiteTiltedPotential_candidate_le ω h x n hactive k
      have hreal := EReal.toReal_le_toReal hcandidate (EReal.coe_ne_bot _) htop
      simp only [EReal.toReal_coe] at hreal
      change lastPassage ω x (k.val, m - k.val) + h.1 * (k.val : ℝ) +
        h.2 * ((m - k.val : ℕ) : ℝ) ≤ (finiteTiltedPotential ω h x n).toReal at hreal
      dsimp only [k] at hreal
      have hreal' : lastPassage ω x (a.1.val, N - a.1.val) + h.1 * (a.1.val : ℝ) +
          h.2 * ((N - a.1.val : ℕ) : ℝ) ≤ (finiteTiltedPotential ω h x n).toReal := by
        simpa only [hlen] using hreal
      have hweight := pathWeight_le_lastPassage ω a.2
      change pathWeight ω a.2 + h.1 * (a.1.val : ℝ) +
        h.2 * ((N - a.1.val : ℕ) : ℝ) ≤ (finiteTiltedPotential ω h x n).toReal
      linarith only [hweight, hreal']

    -- Each endpoint maximum is attained by an actual path in the same Sigma ensemble.
    have hPupper : finiteTiltedPotential ω h x n ≤ (M : EReal) := by
      apply (finiteTiltedPotential_le_coe_iff ω h x n hactive M).mpr
      intro k
      let v : ℕ := k.val
      let kN : Fin (N + 1) := ⟨v, by
        have hk : v < m + 1 := k.isLt
        rw [hlen] at hk
        exact hk⟩
      obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω x (kN.val, N - kN.val)
      have hle : E ⟨kN, p⟩ ≤ M := Finset.le_sup' E (Finset.mem_univ _)
      change pathWeight ω p + h.1 * (v : ℝ) + h.2 * ((N - v : ℕ) : ℝ) ≤ M at hle
      rw [hp] at hle
      change lastPassage ω x (v, m - v) + h.1 * (v : ℝ) +
        h.2 * ((m - v : ℕ) : ℝ) ≤ M
      rw [hlen]
      exact hle
    have hPle : (finiteTiltedPotential ω h x n).toReal ≤ M := by
      simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal hPupper hbot (EReal.coe_ne_top _)
    have hmaximum : M = (finiteTiltedPotential ω h x n).toReal :=
      le_antisymm hMle hPle

    -- The finite log-sum-exp theorem now has the actual maximum as limit.
    have hZ (β : ℝ) : (∑ a : I, Real.exp (β * E a)) = Z β N x := by
      rw [Fintype.sum_sigma]
    have hfun : (fun β : ℝ => β⁻¹ * Real.log (∑ a : I, Real.exp (β * E a))) =
        (fun β : ℝ => F β N x) := by
      funext β
      rw [hZ]
      dsimp only [F]
      rw [div_eq_mul_inv, mul_comm]
    have hlimit := ProbabilityBasics.tendsto_log_sum_exp_div_atTop E
    change Tendsto (fun β : ℝ => β⁻¹ * Real.log (∑ a : I, Real.exp (β * E a)))
      atTop (𝓝 M) at hlimit
    rw [hfun, hmaximum] at hlimit
    exact hlimit

  constructor
  · exact hpressure
  · intro N x i
    have hstep : (finiteEdgeStep i).1 + (finiteEdgeStep i).2 = 1 := by
      fin_cases i <;> norm_num [finiteEdgeStep]
    have hchildLevel : (x + finiteEdgeStep i).1 + (x + finiteEdgeStep i).2 + (N : ℤ) =
        x.1 + x.2 + ((N + 1 : ℕ) : ℤ) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hparent := hpressure (N + 1) x
    have hchild := hpressure N (x + finiteEdgeStep i)
    rw [hchildLevel] at hchild
    have hconstant : Tendsto (fun _ : ℝ => finiteTiltCoordinate h i) atTop
        (𝓝 (finiteTiltCoordinate h i)) := tendsto_const_nhds
    have hlimits := (hparent.sub hchild).sub hconstant
    have hactive : x.1 + x.2 < x.1 + x.2 + ((N + 1 : ℕ) : ℤ) := by omega
    simpa only [finiteBusemannEdge, dite_eq_left hactive] using hlimits

end LPP.Busemann
