/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RealQuantileJointLaw
public import Busemann.Process.CoalescingBarrierCDF
public import LPP_Foundations.Model.Paths.Coalescence
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Busemann.Geometry.CoalescingMateMeasurability
import Busemann.Process.RightmostPathGeodesic
import Busemann.Process.RightmostPathMeasurability
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- One original conditional-CDF quantile family coalesces across all signed
root pairs for product-almost every environment and common uniform parameter.
Strong Existence, lm:coal, public source lines 931–968. -/
theorem ae_coalescing_real_rightmost_quantile_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B)
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (hqMeas : ∀ u : Lattice, Measurable
      (fun a : Environment × unitInterval => q u a.1 a.2))
    (hqCDF : ∀ᵐ ω ∂environmentLaw μ,
      ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (condDistrib
                (fun a : ProcessSample =>
                  rightmostCocyclePath (fun x y => B x y a) u)
                processEnvironment P) ω
                  {η : ℕ → Lattice | pathSoutheastLE η γ})) :
    ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
      ∀ u v : Lattice, paths_coalesce u v (q u a.1 a.2) (q v a.1 a.2) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  let ν := (environmentLaw μ).prod (volume : Measure unitInterval)
  let ray (u : Lattice) (a : ProcessSample) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y a) u
  let E (u v : Lattice) : Set (Environment × (ℕ → Lattice)) :=
    {a | ∃ π : ℕ → Lattice,
      IsLocallyRightmostGeodesic a.1 v π ∧
      ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, a.2 (m + k) = π (n + k)}
  have hE (u v : Lattice) : MeasurableSet (E u v) :=
    measurableSet_exists_coalescing_locallyRightmost_mate u v
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun a : ProcessSample => ((x, y), a)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  have hRayMeas (u : Lattice) : Measurable (ray u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath B hBMeas u n
  have hActualGeo : ∀ᵐ a ∂P, ∀ u : Lattice,
      IsLocallyRightmostGeodesic (processEnvironment a) u (ray u a) := by
    filter_upwards [hB.1.2.2, hB.2.1] with a hadd hrec
    intro u
    exact isLocallyRightmostGeodesic_rightmostCocyclePath
      (processEnvironment a) (fun x y => B x y a) hadd hrec u
  have hActualMate (u v : Lattice) :
      ∀ᵐ a ∂P, (processEnvironment a, ray u a) ∈ E u v := by
    filter_upwards [hActualGeo, hCoal] with a hgeo hcoal
    obtain ⟨m, n, halign, htail⟩ := hcoal u v
    exact ⟨ray v a, hgeo v, m, n, halign, htail⟩
  have hQMate (u v : Lattice) : ∀ᵐ a ∂ν,
      (a.1, q u a.1 a.2) ∈ E u v := by
    have hLaw := real_rightmost_quantile_joint_law
      μ P hMarginal B hB q hqMeas hqCDF u
    have hPairQ : Measurable
        (fun a : Environment × unitInterval => (a.1, q u a.1 a.2)) :=
      measurable_fst.prodMk (hqMeas u)
    have hPairP : Measurable
        (fun a : ProcessSample => (processEnvironment a, ray u a)) :=
      measurable_fst.prodMk (hRayMeas u)
    have hP : ∀ᵐ b ∂P.map
        (fun a : ProcessSample => (processEnvironment a, ray u a)),
        b ∈ E u v := by
      exact (ae_map_iff hPairP.aemeasurable (hE u v)).mpr
        (hActualMate u v)
    rw [← hLaw] at hP
    exact (ae_map_iff hPairQ.aemeasurable (hE u v)).mp hP
  have hQMateAll : ∀ᵐ a ∂ν, ∀ u v : Lattice,
      (a.1, q u a.1 a.2) ∈ E u v := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    exact hQMate u v
  have hCDFProd : ∀ᵐ a ∂ν,
      ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic a.1 u (q u a.1 s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic a.1 u γ →
          (pathSoutheastLE (q u a.1 s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η γ}) := by
    exact (Measure.quasiMeasurePreserving_fst.ae hqCDF)
  have hCutProd : ∀ᵐ a ∂ν, ∀ u v : Lattice,
      ∀ π γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic a.1 u π →
        IsLocallyRightmostGeodesic a.1 v γ →
        (∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, π (m + k) = γ (n + k)) →
        (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η π} =
          (κ v) a.1 {η : ℕ → Lattice | pathSoutheastLE η γ} := by
    exact Measure.quasiMeasurePreserving_fst.ae
      (conditional_rightmost_lower_cut_eq_of_coalescing_barriers
        μ P hMarginal B hB hCoal)
  filter_upwards [hQMateAll, hCDFProd, hCutProd] with a hmates hcdf hcuts
  intro u v
  change ∃ m n : ℕ,
    u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
    ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k)
  obtain ⟨πv, hπv, m₁, n₁, halign₁, htail₁⟩ := hmates u v
  obtain ⟨πu, hπu, m₂, n₂, halign₂, htail₂⟩ := hmates v u
  have hqu := (hcdf u a.2)
  have hqv := (hcdf v a.2)
  have hSelfU : pathSoutheastLE (q u a.1 a.2) (q u a.1 a.2) := by
    intro i j hlevel
    have hij : i = j := by omega
    subst j
    exact ⟨le_refl _, le_refl _⟩
  have hSelfV : pathSoutheastLE (q v a.1 a.2) (q v a.1 a.2) := by
    intro i j hlevel
    have hij : i = j := by omega
    subst j
    exact ⟨le_refl _, le_refl _⟩
  have hQvLeπv : pathSoutheastLE (q v a.1 a.2) πv := by
    apply (hqv.2 πv hπv).mpr
    rw [← hcuts u v (q u a.1 a.2) πv hqu.1 hπv
      ⟨m₁, n₁, halign₁, htail₁⟩]
    exact (hqu.2 (q u a.1 a.2) hqu.1).mp hSelfU
  have hQuLeπu : pathSoutheastLE (q u a.1 a.2) πu := by
    apply (hqu.2 πu hπu).mpr
    rw [← hcuts v u (q v a.1 a.2) πu hqv.1 hπu
      ⟨m₂, n₂, halign₂, htail₂⟩]
    exact (hqv.2 (q v a.1 a.2) hqv.1).mp hSelfV
  let m : ℕ := m₁ + m₂
  let n : ℕ := n₁ + m₂
  have halign : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) := by
    dsimp [m, n]
    omega
  refine ⟨m, n, halign, ?_⟩
  intro k
  have hindex : m₁ + m₂ = n₁ + n₂ := by omega
  have hfirst : q u a.1 a.2 (m + k) = πv (n + k) := by
    simpa only [m, n, ← add_assoc] using htail₁ (m₂ + k)
  have hsecond : q v a.1 a.2 (n + k) = πu (m + k) := by
    have h := htail₂ (n₁ + k)
    simpa only [m, n, hindex, add_comm, add_left_comm, add_assoc] using h
  have hlevel :
      (q u a.1 a.2 0).1 + (q u a.1 a.2 0).2 + ((m + k : ℕ) : ℤ) =
      (πu 0).1 + (πu 0).2 + ((m + k : ℕ) : ℤ) := by
    rw [hqu.1.1, hπu.1]
  have hlevelv :
      (q v a.1 a.2 0).1 + (q v a.1 a.2 0).2 + ((n + k : ℕ) : ℤ) =
      (πv 0).1 + (πv 0).2 + ((n + k : ℕ) : ℤ) := by
    rw [hqv.1.1, hπv.1]
  have hu := hQuLeπu (m + k) (m + k) hlevel
  have hv := hQvLeπv (n + k) (n + k) hlevelv
  rw [← hsecond] at hu
  rw [← hfirst] at hv
  exact Prod.ext (le_antisymm hu.1 hv.1)
    (le_antisymm hv.2 hu.2)

end LPP.Busemann
