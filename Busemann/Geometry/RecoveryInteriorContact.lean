/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.Recovery
public import Busemann.Frozen.Definitions.InteriorDirection
public import LPP_Foundations.Analysis.ClosedUnitDirections
public import LPP_Foundations.Analysis.QuadrantSuperdifferentialIdentities
public import LPP_Foundations.Model.RecoveryAntidiagonal
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! A deterministic contact point from finite recovery and uniform estimates. -/

public section

open Set LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- Finite recovery and the two uniform endpoint estimates force the given
majorant to touch the shape at an interior direction. This is the deterministic
contact step in JR arXiv:1810.03580v3, lines 814–829. -/
theorem exists_interior_contact_of_uniform_recovery_bounds
    (weights : Environment) (C : Lattice → Lattice → ℝ)
    (g : Quadrant → ℝ) (u : ℝ × ℝ)
    (hC : is_additive C) (hrec : recovers_environment weights C)
    (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (hmajor : ∀ z : Quadrant, g z ≤ u.1 * (z.1 : ℝ) + u.2 * (z.2 : ℝ))
    (haxes : quadrantSuperdifferential g (1, 0) = ∅ ∧
      quadrantSuperdifferential g (0, 1) = ∅)
    (hw : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 →
        |lastPassage weights 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ × ℕ,
      N ≤ d.1 + d.2 →
        |C 0 ((d.1 : ℤ), (d.2 : ℤ)) -
          (u.1 * (d.1 : ℝ) + u.2 * (d.2 : ℝ))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    ∃ ξ : InteriorDirection, u ∈ quadrantSuperdifferential g ξ.val := by
  let D : Quadrant → ℝ := fun z => u.1 * (z.1 : ℝ) + u.2 * (z.2 : ℝ) - g z
  have hfirst : Continuous (fun z : Quadrant => (z.1 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_fst
  have hsecond : Continuous (fun z : Quadrant => (z.2 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_snd
  have hD : Continuous D :=
    ((continuous_const.mul hfirst).add (continuous_const.mul hsecond)).sub hg
  have hclosed : IsClosed closedUnitDirections :=
    isClosed_eq (hfirst.add hsecond) continuous_const
  have hbound : closedUnitDirections ⊆ Icc (0 : Quadrant) (1, 1) := by
    intro z hz
    have hsum : (z.1 : ℝ) + (z.2 : ℝ) = 1 := hz
    have h₁ : 0 ≤ (z.1 : ℝ) := NNReal.coe_nonneg _
    have h₂ : 0 ≤ (z.2 : ℝ) := NNReal.coe_nonneg _
    constructor
    · exact ⟨zero_le, zero_le⟩
    · constructor
      · have hle : (z.1 : ℝ) ≤ 1 := by linarith only [hsum, h₂]
        exact_mod_cast hle
      · have hle : (z.2 : ℝ) ≤ 1 := by linarith only [hsum, h₁]
        exact_mod_cast hle
  have hcompact : IsCompact closedUnitDirections :=
    (isCompact_Icc : IsCompact (Icc (0 : Quadrant) (1, 1))).of_isClosed_subset hclosed hbound
  have hnonempty : closedUnitDirections.Nonempty := by
    refine ⟨(1, 0), ?_⟩
    norm_num [closedUnitDirections]
  -- Minimize the nonnegative deficit on the whole closed segment.
  obtain ⟨ξ, hξ, hmin⟩ := hcompact.exists_isMinOn hnonempty hD.continuousOn
  have hnonneg : 0 ≤ D ξ := by
    dsimp [D]
    linarith only [hmajor ξ]
  have hzero : D ξ = 0 := by
    by_contra hne
    have ha : 0 < D ξ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨Nw, hNw⟩ := hw (D ξ / 4) (by linarith)
    obtain ⟨Nc, hNc⟩ := hc (D ξ / 4) (by linarith)
    let n : ℕ := max 1 (max Nw Nc)
    have hn : 0 < n := by dsimp [n]; omega
    have hnw : Nw ≤ n := by dsimp [n]; omega
    have hnc : Nc ≤ n := by dsimp [n]; omega
    -- Recovery gives an actually attained endpoint on this antidiagonal.
    obtain ⟨d, hd, hatt⟩ :=
      (LPP.lastPassage_antidiagonal_comparison_and_attainment weights C hC hrec 0 n).2
    have hatt' : lastPassage weights 0 d = C 0 ((d.1 : ℤ), (d.2 : ℤ)) := by
      simpa only [zero_add] using hatt
    have hw' := hNw d (by omega)
    have hc' := hNc d (by omega)
    rw [hd] at hw' hc'
    let r : Quadrant := ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
    let q : Quadrant := (1 / (n : ℝ≥0)) • r
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsum : (d.1 : ℝ) + (d.2 : ℝ) = (n : ℝ) := by exact_mod_cast hd
    have hq : q ∈ closedUnitDirections := by
      change ((q.1 : ℝ) + (q.2 : ℝ)) = 1
      dsimp [q, r]
      simp only [NNReal.coe_natCast]
      field_simp
      nlinarith [hsum]
    have hscale : D q = (1 / (n : ℝ)) *
        (u.1 * (d.1 : ℝ) + u.2 * (d.2 : ℝ) - g r) := by
      dsimp [D, q]
      rw [hhom]
      dsimp [r]
      simp only [NNReal.coe_natCast]
      ring
    have herror : u.1 * (d.1 : ℝ) + u.2 * (d.2 : ℝ) - g r ≤
        2 * (D ξ / 4) * (n : ℝ) := by
      have hwupper := (abs_le.mp hw').2
      have hclower := (abs_le.mp hc').1
      dsimp [r] at ⊢
      rw [hatt'] at hwupper
      linarith only [hwupper, hclower]
    have hsmall : D q ≤ D ξ / 2 := by
      rw [hscale]
      have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_left herror hinv
      have heq : (1 / (n : ℝ)) * (2 * (D ξ / 4) * (n : ℝ)) = D ξ / 2 := by
        field_simp
        ring
      linarith only [hm, heq]
    have hminimal : D ξ ≤ D q := hmin hq
    linarith only [hminimal, hsmall, ha]
  have hcontact : g ξ = u.1 * (ξ.1 : ℝ) + u.2 * (ξ.2 : ℝ) := by
    dsimp [D] at hzero
    linarith only [hzero]
  have hsupp : u ∈ quadrantSuperdifferential g ξ :=
    (mem_quadrantSuperdifferential_iff_majorant_and_contact g ξ u hhom).2
      ⟨hmajor, hcontact⟩
  have hsum : (ξ.1 : ℝ) + (ξ.2 : ℝ) = 1 := hξ
  -- Axis emptiness makes this contact point strictly interior.
  have hnonzero₁ : ξ.1 ≠ 0 := by
    intro hz₁
    have hz₂ : ξ.2 = 1 := by
      rw [hz₁, NNReal.coe_zero, zero_add] at hsum
      exact_mod_cast hsum
    have hzaxis : ξ = (0, 1) := Prod.ext hz₁ hz₂
    rw [hzaxis, haxes.2] at hsupp
    exact hsupp
  have hnonzero₂ : ξ.2 ≠ 0 := by
    intro hz₂
    have hz₁ : ξ.1 = 1 := by
      rw [hz₂, NNReal.coe_zero, add_zero] at hsum
      exact_mod_cast hsum
    have hzaxis : ξ = (1, 0) := Prod.ext hz₁ hz₂
    rw [hzaxis, haxes.1] at hsupp
    exact hsupp
  exact ⟨⟨ξ, lt_of_le_of_ne zero_le (Ne.symm hnonzero₁),
    lt_of_le_of_ne zero_le (Ne.symm hnonzero₂), hsum⟩, hsupp⟩

end LPP.Busemann
