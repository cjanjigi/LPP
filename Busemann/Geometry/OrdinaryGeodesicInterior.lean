/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicCocycleConfinement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

/-- A unique normalized cluster direction of an ordinary up-right ray is its
actual normalized limit. The signed root vanishes under normalization. -/
theorem ordinary_ray_normalized_tendsto_of_unique_cluster
    (u : Lattice) (γ : ℕ → Lattice) (hstart : γ 0 = u)
    (hsteps : ∀ n, γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
      γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ)))
    (z : ℝ)
    (hcluster : ∀ η : ℝ × ℝ,
      MapClusterPt η atTop
        (fun n : ℕ => (((γ n).1 : ℝ) / (n : ℝ),
          ((γ n).2 : ℝ) / (n : ℝ))) → η = (z, 1 - z)) :
    Tendsto (fun n : ℕ => (((γ n).1 : ℝ) / (n : ℝ),
        ((γ n).2 : ℝ) / (n : ℝ))) atTop (𝓝 (z, 1 - z)) := by
  let a : ℕ → ℝ := fun n => (((γ n).1 - u.1 : ℤ) : ℝ) / (n : ℝ)
  have hData := ordinary_ray_normalized_cluster_bounds u γ hstart hsteps
  have hBounds : ∀ n, 0 ≤ a n ∧ a n ≤ 1 := hData.1
  have hBelow : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) a :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n => (hBounds n).1)
  have hAbove : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) a :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => (hBounds n).2)
  have hInfCluster : MapClusterPt (liminf a atTop) atTop a :=
    MapClusterPt.liminf hAbove.isCoboundedUnder_ge hBelow
  have hSupCluster : MapClusterPt (limsup a atTop) atTop a :=
    MapClusterPt.limsup hBelow.isCoboundedUnder_le hAbove
  have hInf : liminf a atTop = z := by
    have h := hcluster _
      (normalized_ray_cluster_of_horizontal_ratio_cluster u γ hstart hsteps _ hInfCluster)
    exact congrArg Prod.fst h
  have hSup : limsup a atTop = z := by
    have h := hcluster _
      (normalized_ray_cluster_of_horizontal_ratio_cluster u γ hstart hsteps _ hSupCluster)
    exact congrArg Prod.fst h
  have ha : Tendsto a atTop (𝓝 z) :=
    tendsto_of_liminf_eq_limsup hInf hSup hAbove hBelow
  have hroot₁ : Tendsto (fun n : ℕ => (u.1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hrootSum : Tendsto
      (fun n : ℕ => ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hFirst : Tendsto (fun n : ℕ => ((γ n).1 : ℝ) / (n : ℝ)) atTop (𝓝 z) := by
    have h := ha.add hroot₁
    have heq (n : ℕ) : ((γ n).1 : ℝ) / (n : ℝ) =
        a n + (u.1 : ℝ) / (n : ℝ) := by
      dsimp only [a]
      rw [Int.cast_sub, sub_div, sub_add_cancel]
    simpa only [heq, add_zero] using h
  have hsum : ∀ n, (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
    intro n
    induction n with
    | zero => simp [hstart]
    | succ n ih =>
      rcases hsteps n with he | hn
      · simp only [he, Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
      · simp only [hn, Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
  have hSecondBase : Tendsto (fun n : ℕ =>
      1 - a n + ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ) -
        (u.1 : ℝ) / (n : ℝ)) atTop (𝓝 (1 - z)) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub ha).add hrootSum).sub hroot₁
    simpa only [sub_zero, add_zero] using h
  have hSecond : Tendsto (fun n : ℕ => ((γ n).2 : ℝ) / (n : ℝ))
      atTop (𝓝 (1 - z)) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        ((γ n).2 : ℝ) / (n : ℝ) =
          1 - a n + ((u.1 + u.2 : ℤ) : ℝ) / (n : ℝ) -
            (u.1 : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have hs : ((γ n).1 : ℝ) + ((γ n).2 : ℝ) =
          ((u.1 + u.2 : ℤ) : ℝ) + (n : ℝ) := by
        exact_mod_cast hsum n
      dsimp only [a]
      rw [Int.cast_sub]
      field_simp [hn0]
      linarith only [hs]
    exact hSecondBase.congr' (heq.mono fun _ h => h.symm)
  exact hFirst.prodMk_nhds hSecond

end LPP.Busemann
