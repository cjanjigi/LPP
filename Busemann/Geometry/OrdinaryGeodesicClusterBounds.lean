/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import Busemann.Frozen.Definitions.ApproachesFaceInterval
public import Mathlib.Topology.ClusterPt
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- The horizontal displacement ratio of an ordinary up-right ray lies in
the unit interval. All cluster points of the signed-root normalized ray have
unit coordinate sum and horizontal coordinate between this ratio's liminf
and limsup. GRS arXiv:1510.00860v1, Theorem 2.1(i), normalization step. -/
theorem ordinary_ray_normalized_cluster_bounds
    (u : Lattice) (γ : ℕ → Lattice)
    (hstart : γ 0 = u)
    (hsteps : ∀ n : ℕ,
      γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
        γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) :
    let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
    (∀ n, 0 ≤ a n ∧ a n ≤ 1) ∧
    0 ≤ liminf a atTop ∧ limsup a atTop ≤ 1 ∧
    ∀ η : ℝ × ℝ,
      MapClusterPt η atTop
        (fun n => (((γ n).1 : ℝ) / (n : ℝ), ((γ n).2 : ℝ) / (n : ℝ))) →
      liminf a atTop ≤ η.1 ∧ η.1 ≤ limsup a atTop ∧ η.1 + η.2 = 1 := by
  let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
  let v : ℕ → ℝ × ℝ := fun n =>
    (((γ n).1 : ℝ) / (n : ℝ), ((γ n).2 : ℝ) / (n : ℝ))
  have hDisplacement (n : ℕ) :
      0 ≤ (γ n).1 - u.1 ∧ (γ n).1 - u.1 ≤ (n : ℤ) ∧
      (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    induction n with
    | zero => simp [hstart]
    | succ n ih =>
      rcases hsteps n with hEast | hNorth
      · rw [hEast]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] at *
        omega
      · rw [hNorth]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] at *
        omega
  have hBounds (n : ℕ) : 0 ≤ a n ∧ a n ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp [a, hstart]
    have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    constructor
    · exact div_nonneg (by exact_mod_cast (hDisplacement n).1) hnReal.le
    · apply (div_le_iff₀ hnReal).mpr
      have hd : (((γ n).1 - u.1 : ℤ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (hDisplacement n).2.1
      simpa only [one_mul] using hd
  have hBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) a :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hBounds n).1)
  have hAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) a :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hBounds n).2)
  have hLiminfNonneg : 0 ≤ liminf a atTop :=
    le_liminf_of_le hAbove.isCoboundedUnder_ge
      (Filter.Eventually.of_forall fun n => (hBounds n).1)
  have hLimsupOne : limsup a atTop ≤ 1 :=
    limsup_le_of_le hBelow.isCoboundedUnder_le
      (Filter.Eventually.of_forall fun n => (hBounds n).2)
  have hRootFirst : Tendsto (fun n : ℕ => (u.1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat (u.1 : ℝ)
  have hRootSum : Tendsto (fun n : ℕ => ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat ((u.1 + u.2 : ℤ) : ℝ)
  have hFirst (n : ℕ) : (v n).1 = a n + (u.1 : ℝ) / (n : ℝ) := by
    change ((γ n).1 : ℝ) / (n : ℝ) =
      (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ) + (u.1 : ℝ) / (n : ℝ)
    rw [Int.cast_sub, sub_div, sub_add_cancel]
  have hSum : Tendsto (fun n => (v n).1 + (v n).2) atTop (𝓝 1) := by
    have hFormula : ∀ᶠ n : ℕ in atTop,
        (v n).1 + (v n).2 = 1 + ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      change ((γ n).1 : ℝ) / (n : ℝ) + ((γ n).2 : ℝ) / (n : ℝ) = _
      rw [← add_div]
      have hs : ((γ n).1 : ℝ) + ((γ n).2 : ℝ) =
          ((u.1 + u.2 : ℤ) : ℝ) + (n : ℝ) := by
        exact_mod_cast (hDisplacement n).2.2
      rw [hs]
      field_simp [hnReal]
      ring
    have hLimit : Tendsto (fun n : ℕ =>
        1 + ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hRootSum
    exact hLimit.congr' (hFormula.mono fun _ h => h.symm)
  refine ⟨hBounds, hLiminfNonneg, hLimsupOne, ?_⟩
  intro η hCluster
  obtain ⟨φ, hφ, hConverges⟩ := MapClusterPt.tendsto_subseq hCluster
  have hφTop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hFirstConv : Tendsto (fun k => (v (φ k)).1) atTop (𝓝 η.1) :=
    by simpa only [Function.comp_def] using hConverges.fst_nhds
  have hAConv : Tendsto (fun k => a (φ k)) atTop (𝓝 η.1) := by
    have h := hFirstConv.sub (hRootFirst.comp hφTop)
    have hEq (k : ℕ) : a (φ k) = (v (φ k)).1 - (u.1 : ℝ) / (φ k : ℝ) := by
      rw [hFirst]
      ring
    simpa only [hEq, Function.comp_def, sub_zero] using h
  have hACluster : MapClusterPt η.1 atTop a :=
    MapClusterPt.of_comp hφTop hAConv.mapClusterPt
  have hSumConv : Tendsto (fun k => (v (φ k)).1 + (v (φ k)).2)
      atTop (𝓝 (η.1 + η.2)) := by
    simpa only [Function.comp_def] using
      hConverges.fst_nhds.add hConverges.snd_nhds
  have hUnit : η.1 + η.2 = 1 :=
    tendsto_nhds_unique hSumConv (hSum.comp hφTop)
  exact ⟨MapClusterPt.liminf_le hACluster hBelow,
    MapClusterPt.le_limsup hACluster hAbove, hUnit⟩

/-- A calibrated barrier whose left face lies strictly right of the ordinary
ray's horizontal liminf is frequently strictly east of that ray. This is the
strict comparison trigger in GRS arXiv:1510.00860v1, Theorem 2.1(i). -/
theorem ordinary_ray_frequently_west_of_barrier
    (u : Lattice) (γ ρ : ℕ → Lattice)
    (a : ℕ → ℝ)
    (hA : ∀ n, a n = (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ))
    (hABounds : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (d : ℕ → ℕ × ℕ)
    (hEnd : ∀ n : ℕ,
      (d n).1 + (d n).2 = n ∧
      ρ n = u + (((d n).1 : ℤ), ((d n).2 : ℤ)))
    (left right : InteriorDirection)
    (hFace : approachesFaceInterval d left right)
    (hGap : liminf a atTop < (left.1.1 : ℝ)) :
    ∃ᶠ n : ℕ in atTop, (γ n).1 < (ρ n).1 := by
  let ratio (n : ℕ) : ℝ := ((d n).1 : ℝ) / (n : ℝ)
  let θ : ℝ := (liminf a atTop + (left.1.1 : ℝ)) / 2
  have hbθ : liminf a atTop < θ := by dsimp only [θ]; linarith only [hGap]
  have hθleft : θ < (left.1.1 : ℝ) := by dsimp only [θ]; linarith only [hGap]
  have hABelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) a :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hABounds n).1)
  have hAAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) a :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hABounds n).2)
  have hAFrequent : ∃ᶠ n : ℕ in atTop, a n < θ :=
    frequently_lt_of_liminf_lt hAAbove.isCoboundedUnder_ge hbθ
  have hRatioNonneg (n : ℕ) : 0 ≤ ratio n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hRatioBounded : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) ratio :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hRatioNonneg)
  have hLen (n : ℕ) : (d n).1 + (d n).2 = n := (hEnd n).1
  have hRatioLiminf : (left.1.1 : ℝ) ≤ liminf ratio atTop := by
    simpa only [ratio, hLen] using hFace.2.1
  have hBarrier : ∀ᶠ n : ℕ in atTop, θ < ratio n :=
    eventually_lt_of_lt_liminf (hθleft.trans_le hRatioLiminf) hRatioBounded
  apply (hAFrequent.and_eventually (hBarrier.and (eventually_gt_atTop (0 : ℕ)))).mono
  intro n hn
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2.2
  have hDiv : (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ) <
      ((d n).1 : ℝ) / (n : ℝ) := by
    rw [← hA n]
    exact hn.1.trans hn.2.1
  have hReal : (((γ n).1 - u.1 : ℤ) : ℝ) < ((d n).1 : ℝ) :=
    (div_lt_div_iff_of_pos_right hnReal).mp hDiv
  have hInt : (γ n).1 - u.1 < ((d n).1 : ℤ) := by exact_mod_cast hReal
  have hρ := (hEnd n).2
  rw [hρ]
  simp only [Prod.fst_add]
  omega

end LPP.Busemann
