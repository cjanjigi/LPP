/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.ArbitraryGeodesicBarrier
public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Topology.Instances.Real.Lemmas
import Busemann.Process.NorthAxisGeodesics
import LPP_Foundations.Probability.EnvironmentSwap
import LPP_Foundations.Model.LastPassage.Swap

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- One measurable full event under the original real iid law makes every
ordinary maximizing north- or east-directed ray from every signed root the
corresponding canonical axis. The shared ray hypotheses occur once; both
coordinate limits use local time. JSP (2025), Lemma 5.1 and coordinate
reflection; GRS arXiv:1510.00860v1, Lemma 5.1; accepted Strong Existence,
g400(b), line 1662. Coordinate reindexing requires no symmetry of site values. -/
theorem exists_full_event_axis_directed_geodesic_eq_axis
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ A : Set LPPDifferentiability.Environment,
      MeasurableSet A ∧ environmentLaw μ A = 1 ∧
      ∀ ω ∈ A, ∀ u : Lattice, ∀ γ : ℕ → Lattice,
        γ 0 = u →
        (∀ n : ℕ,
          γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
            γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) →
        LPPDifferentiability.has_maximizing_segments ω γ →
        (Tendsto (fun n : ℕ => ((γ n).1 : ℝ) / (n : ℝ)) atTop (𝓝 0) →
          ∀ n : ℕ, γ n = u + ((0 : ℤ), (n : ℤ))) ∧
        (Tendsto (fun n : ℕ => ((γ n).2 : ℝ) / (n : ℝ)) atTop (𝓝 0) →
          ∀ n : ℕ, γ n = u + ((n : ℤ), (0 : ℤ))) := by
  classical
  -- Source step 1: choose the north event once under the original law.
  obtain ⟨A_N, hA_N_meas, hA_N_full, hNorth⟩ :=
    exists_full_event_north_directed_geodesic_eq_axis μ hμ hmoment

  -- Source steps 2 and 3: intersect with the swap preimage before any rays.
  have hSwap : MeasurePreserving environmentSwap
      (environmentLaw μ) (environmentLaw μ) :=
    LPPDifferentiability.measurePreserving_environmentSwap μ
  let A : Set LPPDifferentiability.Environment :=
    A_N ∩ environmentSwap ⁻¹' A_N
  have hSwapPreimageMeas : MeasurableSet (environmentSwap ⁻¹' A_N) :=
    hSwap.measurable hA_N_meas
  have hAMeas : MeasurableSet A := hA_N_meas.inter hSwapPreimageMeas
  have hSwapPreimageFull : environmentLaw μ (environmentSwap ⁻¹' A_N) = 1 := by
    exact (hSwap.measure_preimage hA_N_meas.nullMeasurableSet).trans hA_N_full

  have hA_N_compl_null : environmentLaw μ A_Nᶜ = 0 := by
    calc
      environmentLaw μ A_Nᶜ = environmentLaw μ Set.univ - environmentLaw μ A_N :=
        measure_compl hA_N_meas (measure_ne_top _ _)
      _ = 0 := by rw [measure_univ, hA_N_full]; simp
  have hSwapPreimage_compl_null :
      environmentLaw μ (environmentSwap ⁻¹' A_N)ᶜ = 0 := by
    calc
      environmentLaw μ (environmentSwap ⁻¹' A_N)ᶜ =
          environmentLaw μ Set.univ - environmentLaw μ (environmentSwap ⁻¹' A_N) :=
        measure_compl hSwapPreimageMeas (measure_ne_top _ _)
      _ = 0 := by rw [measure_univ, hSwapPreimageFull]; simp
  have hBadUnionNull :
      environmentLaw μ (A_Nᶜ ∪ (environmentSwap ⁻¹' A_N)ᶜ) = 0 :=
    measure_union_null hA_N_compl_null hSwapPreimage_compl_null
  have hA_compl_subset : Aᶜ ⊆ A_Nᶜ ∪ (environmentSwap ⁻¹' A_N)ᶜ := by
    intro ω hω
    simp only [A, Set.mem_compl_iff, Set.mem_inter_iff] at hω
    simp only [Set.mem_union, Set.mem_compl_iff]
    exact not_and_or.mp hω
  have hA_compl_null : environmentLaw μ Aᶜ = 0 :=
    measure_mono_null hA_compl_subset hBadUnionNull
  have hA_full : environmentLaw μ A = 1 := by
    calc
      environmentLaw μ A = environmentLaw μ Set.univ :=
        measure_of_measure_compl_eq_zero hA_compl_null
      _ = 1 := measure_univ

  -- The environment involution identifies both transported site fields.
  have hSwapField (ω : LPPDifferentiability.Environment) :
      (fun z => environmentSwap ω z.swap) = ω := by
    change environmentSwap (environmentSwap ω) = ω
    exact LPPDifferentiability.environmentSwap_involutive ω

  refine ⟨A, hAMeas, hA_full, ?_⟩
  intro ω hω u γ hstart hsteps hsegments
  have hωNorth : ω ∈ A_N := hω.1
  have hSwapωNorth : environmentSwap ω ∈ A_N := hω.2
  change environmentSwap ω ∈ A_N at hSwapωNorth

  constructor
  · -- Source step 6: the north implication uses the original ray directly.
    intro hNorthDir
    exact hNorth ω hωNorth u γ hstart hsteps hsegments hNorthDir
  · -- Source steps 4 and 5: prove the east implication by transposing the ray.
    intro hEastDir
    let γSwap : ℕ → Lattice := fun n => (γ n).swap
    have hstartSwap : γSwap 0 = u.swap := by
      change (γ 0).swap = u.swap
      rw [hstart]
    have hstepsSwap : ∀ n : ℕ,
        γSwap (n + 1) = γSwap n + ((1 : ℤ), (0 : ℤ)) ∨
          γSwap (n + 1) = γSwap n + ((0 : ℤ), (1 : ℤ)) := by
      intro n
      rcases hsteps n with hEast | hNorth
      · right
        change (γ (n + 1)).swap = (γ n).swap + ((0 : ℤ), (1 : ℤ))
        rw [hEast]
        ext <;> simp [Prod.swap]
      · left
        change (γ (n + 1)).swap = (γ n).swap + ((1 : ℤ), (0 : ℤ))
        rw [hNorth]
        ext <;> simp [Prod.swap]

    have hsegmentsSwap : LPPDifferentiability.has_maximizing_segments
        (environmentSwap ω) γSwap := by
      intro m N hN
      obtain ⟨d, p, hd, hvertices, hweight⟩ := hsegments m N hN
      refine ⟨d.swap, p.swap, ?_, ?_, ?_⟩
      · change d.2 + d.1 = N
        calc
          d.2 + d.1 = d.1 + d.2 := Nat.add_comm _ _
          _ = N := hd
      · intro i
        change (p.swap).vertex i = (γ (m + i.val)).swap
        rw [LPPDifferentiability.Path.swap_vertex]
        rw [hvertices
          (Fin.cast (congrArg Nat.succ (Nat.add_comm d.2 d.1)) i)]
        simp only [Fin.val_cast]
      · have hweightSwap :
            pathWeight (environmentSwap ω) p.swap = pathWeight ω p := by
          calc
            pathWeight (environmentSwap ω) p.swap =
                pathWeight (fun z => environmentSwap ω z.swap) p :=
              LPPDifferentiability.pathWeight_swap (environmentSwap ω) p
            _ = pathWeight ω p := by rw [hSwapField ω]
        have hlastSwap :
            lastPassage (environmentSwap ω) (γ m).swap d.swap =
              lastPassage ω (γ m) d := by
          calc
            lastPassage (environmentSwap ω) (γ m).swap d.swap =
                lastPassage (fun z => environmentSwap ω z.swap) (γ m) d :=
              LPPDifferentiability.lastPassage_swap (environmentSwap ω) (γ m) d
            _ = lastPassage ω (γ m) d := by rw [hSwapField ω]
        calc
          pathWeight (environmentSwap ω) p.swap = pathWeight ω p := hweightSwap
          _ = lastPassage ω (γ m) d := hweight
          _ = lastPassage (environmentSwap ω) (γSwap m) d.swap := hlastSwap.symm

    have hEastDirSwap :
        Tendsto (fun n : ℕ => ((γSwap n).1 : ℝ) / (n : ℝ))
          atTop (𝓝 0) := by
      simpa only [γSwap, Prod.swap] using hEastDir
    have hNorthAxisSwap :=
      hNorth (environmentSwap ω) hSwapωNorth u.swap γSwap hstartSwap
        hstepsSwap hsegmentsSwap hEastDirSwap
    intro n
    have hTransposed := congrArg Prod.swap (hNorthAxisSwap n)
    have hCoordinates : γ n = (u.1 + (n : ℤ), u.2) := by
      simpa [γSwap, Prod.swap] using hTransposed
    have hAxisPair : (u.1 + (n : ℤ), u.2) = u + ((n : ℤ), (0 : ℤ)) := by
      ext <;> simp
    exact hCoordinates.trans hAxisPair

end LPP.Busemann
