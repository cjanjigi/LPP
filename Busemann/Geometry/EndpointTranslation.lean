/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.EndpointSequenceBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Fixed signed-start translation of escaping endpoints and their direction ratios. -/

@[expose] public section

open LPPDifferentiability Filter
open scoped Topology

namespace LPP.Busemann

/-- Translating a face-approaching endpoint by one fixed signed start preserves
escape and changes its horizontal ratio by a vanishing amount. This is the
endpoint-translation detail for GRS arXiv:1510.00860v2, (3.8). -/
theorem approachesFaceInterval_translated_displacement_asymptotics
    (v : ℕ → ℕ × ℕ) (left right : InteriorDirection)
    (hv : approachesFaceInterval v left right) (x : Lattice) :
    let d : ℕ → ℕ × ℕ := fun n =>
      ((((v n).1 : ℤ) - x.1).toNat, (((v n).2 : ℤ) - x.2).toNat)
    Tendsto (fun n => (d n).1 + (d n).2) atTop atTop ∧
      Tendsto (fun n =>
        ((d n).1 : ℝ) / (((d n).1 + (d n).2 : ℕ) : ℝ) -
          ((v n).1 : ℝ) / (((v n).1 + (v n).2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  intro d
  let D : ℕ → ℕ := fun n => (d n).1 + (d n).2
  let A : ℕ → ℝ := fun n => ((v n).1 : ℝ)
  let S : ℕ → ℝ := fun n => (((v n).1 + (v n).2 : ℕ) : ℝ)
  let c : ℝ := (x.1 : ℝ)
  let e : ℝ := ((x.1 + x.2 : ℤ) : ℝ)
  let ρ : ℕ → ℝ := fun n => A n / S n
  have hcoordinates := approachesFaceInterval_tendsto_coordinates v left right hv
  obtain ⟨Nreach, hNreach⟩ := approachesFaceInterval_eventually_reaches v left right hv x
  have hreach : ∀ᶠ n : ℕ in atTop, x ≤ latticeEndpoint (v n) :=
    eventually_atTop.2 ⟨Nreach, fun n hn => (hNreach n hn).1⟩
  have hcast (n : ℕ) (hn : x ≤ latticeEndpoint (v n)) :
      ((d n).1 : ℝ) = A n - c ∧ (D n : ℝ) = S n - e := by
    have hfirst : ((d n).1 : ℤ) = ((v n).1 : ℤ) - x.1 := by
      dsimp [d]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hn.1)
    have hsecond : ((d n).2 : ℤ) = ((v n).2 : ℤ) - x.2 := by
      dsimp [d]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hn.2)
    have hfirstR : ((d n).1 : ℝ) = A n - c := by
      dsimp [A, c]
      exact_mod_cast hfirst
    have hsecondR : ((d n).2 : ℝ) = ((v n).2 : ℝ) - (x.2 : ℝ) := by
      exact_mod_cast hsecond
    constructor
    · exact hfirstR
    · dsimp [D, S, e]
      push_cast
      rw [hfirstR, hsecondR]
      dsimp [A, c] at hfirstR ⊢
      ring

  -- One coordinate already forces the translated natural size to escape.
  have hsize : Tendsto D atTop atTop := by
    apply tendsto_atTop.2
    intro K
    obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) + c)
    filter_upwards [hreach, (tendsto_atTop.1 hcoordinates.1 M)] with n hn hMn
    have hMnR : (M : ℝ) ≤ A n := by
      dsimp [A]
      exact_mod_cast hMn
    have hD1 := (hcast n hn).1
    have hK1 : (K : ℝ) ≤ ((d n).1 : ℝ) := by linarith
    have hKNat : K ≤ (d n).1 := by exact_mod_cast hK1
    exact hKNat.trans (Nat.le_add_right _ _)
  have hsizeR : Tendsto (fun n => (D n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsize
  have hS : Tendsto (fun n => (v n).1 + (v n).2) atTop atTop := hv.1
  have hSpositive : ∀ᶠ n : ℕ in atTop, 0 < S n := by
    filter_upwards [tendsto_atTop.1 hS 1] with n hn
    have hpos : 0 < (v n).1 + (v n).2 := lt_of_lt_of_le Nat.zero_lt_one hn
    dsimp [S]
    exact_mod_cast hpos
  have hDpositive : ∀ᶠ n : ℕ in atTop, 0 < (D n : ℝ) := by
    filter_upwards [tendsto_atTop.1 hsize 1] with n hn
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hρbounds (n : ℕ) : 0 ≤ ρ n ∧ ρ n ≤ 1 := by
    by_cases hz : (v n).1 + (v n).2 = 0
    · have hfirst : (v n).1 = 0 := by omega
      have hsecond : (v n).2 = 0 := by omega
      simp [ρ, A, S, hfirst, hsecond]
    · have hSpos : 0 < S n := by
        dsimp [S]
        exact_mod_cast Nat.pos_of_ne_zero hz
      constructor
      · exact div_nonneg (by dsimp [A]; exact Nat.cast_nonneg _) hSpos.le
      · apply (div_le_iff₀ hSpos).2
        dsimp [ρ, A, S]
        simpa only [one_mul] using
          (show ((v n).1 : ℝ) ≤ (((v n).1 + (v n).2 : ℕ) : ℝ) by
            exact_mod_cast Nat.le_add_right (v n).1 (v n).2)
  let C : ℝ := |e| + |c|
  have hCdiv : Tendsto (fun n => C / (D n : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (D n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsizeR
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := C)).mul hinv
  have herror : ∀ᶠ n : ℕ in atTop,
      |((d n).1 : ℝ) / (D n : ℝ) - ρ n| ≤ C / (D n : ℝ) := by
    filter_upwards [hreach, hSpositive, hDpositive] with n hn hSpos hDpos
    have hD1 := (hcast n hn).1
    have hDeq := (hcast n hn).2
    have hdiffpos : 0 < S n - e := by rw [← hDeq]; exact hDpos
    have hidentity : ((d n).1 : ℝ) / (D n : ℝ) - ρ n =
        (ρ n * e - c) / (D n : ℝ) := by
      rw [hD1, hDeq]
      dsimp [ρ]
      field_simp [ne_of_gt hSpos, ne_of_gt hdiffpos]
      ring
    have hnum : |ρ n * e - c| ≤ C := by
      calc
        |ρ n * e - c| ≤ |ρ n * e| + |c| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (ρ n * e) 0 c
        _ = |ρ n| * |e| + |c| := by rw [abs_mul]
        _ ≤ C := by
          rw [abs_of_nonneg (hρbounds n).1]
          have hmul := mul_le_mul_of_nonneg_right (hρbounds n).2 (abs_nonneg e)
          dsimp [C]
          linarith
    rw [hidentity, abs_div, abs_of_pos hDpos]
    exact div_le_div_of_nonneg_right hnum hDpos.le
  refine ⟨hsize, ?_⟩
  change Tendsto (fun n => ((d n).1 : ℝ) / (D n : ℝ) - ρ n) atTop (𝓝 0)
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => abs_nonneg _)
    herror hCdiv

end LPP.Busemann
