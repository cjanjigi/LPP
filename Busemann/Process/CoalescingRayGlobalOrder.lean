/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicOrder
public import Busemann.Geometry.GeodesicMeasurability
public import Busemann.Process.RightmostPathCovariance
public import Busemann.Process.CoalescingCocycleRepresentation
public import Busemann.Probability.CanonicalCocycleMeans
public import LPP_Foundations.Probability.TranslationErgodic
import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Geometry.CrossedGeodesicCoalescenceAtRoots
import Busemann.Process.RightmostPathGeodesic
import Busemann.Process.RightmostPathMeasurability
import Mathlib.Dynamics.Ergodic.Ergodic
import Lean.Elab.Tactic.Omega

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

private theorem pathSoutheastLE_self (γ : ℕ → Lattice) :
    pathSoutheastLE γ γ := by
  intro m n hlevel
  have hmn : m = n := by omega
  subst n
  exact ⟨le_refl _, le_refl _⟩

private theorem pathSoutheastLE_translate_iff
    (γ δ : ℕ → Lattice) (z : Lattice) :
    pathSoutheastLE (fun n => γ n + z) (fun n => δ n + z) ↔
      pathSoutheastLE γ δ := by
  constructor
  · intro h m n hlevel
    have hshiftlevel :
        ((γ 0 + z).1 + (γ 0 + z).2 + (m : ℤ)) =
          ((δ 0 + z).1 + (δ 0 + z).2 + (n : ℤ)) := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    have hmn := h m n hshiftlevel
    simp only [Prod.fst_add, Prod.snd_add] at hmn
    constructor <;> omega
  · intro h m n hlevel
    have hbaselevel :
        (γ 0).1 + (γ 0).2 + (m : ℤ) =
          (δ 0).1 + (δ 0).2 + (n : ℤ) := by
      simp only [Prod.fst_add, Prod.snd_add] at hlevel
      omega
    have hmn := h m n hbaselevel
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> omega

private theorem rightmost_families_order_at_all_roots
    (ω : Environment)
    (π ρ : Lattice → ℕ → Lattice)
    (hπ : ∀ u, IsLocallyRightmostGeodesic ω u (π u))
    (hρ : ∀ u, IsLocallyRightmostGeodesic ω u (ρ u))
    (hcoalπ : ∀ u v : Lattice, paths_coalesce u v (π u) (π v))
    (hcoalρ : ∀ u v : Lattice, paths_coalesce u v (ρ u) (ρ v))
    (u v : Lattice) (hu : pathSoutheastLE (π u) (ρ u)) :
    pathSoutheastLE (π v) (ρ v) := by
  by_cases hSame : π u = ρ u
  · obtain ⟨a, b, hab, hTailπ⟩ := hcoalπ u v
    obtain ⟨c, d, hcd, hTailρ⟩ := hcoalρ u v
    have hindex : b + c = d + a := by omega
    have hmeet : π v (b + c) = ρ v (b + c) := by
      calc
        π v (b + c) = π u (a + c) := (hTailπ c).symm
        _ = ρ u (c + a) := by rw [hSame]; congr 1; omega
        _ = ρ v (d + a) := hTailρ a
        _ = ρ v (b + c) := by rw [hindex]
    have hprefix := locallyRightmostGeodesic_eq_prefix_of_meet
      ω v (π v) (ρ v) (hπ v) (hρ v) (b + c) hmeet
    have hsamev : π v = ρ v := by
      funext n
      by_cases hn : n ≤ b + c
      · exact hprefix n hn
      · let k := n - (b + c)
        have hπindex : n = b + (c + k) := by dsimp [k]; omega
        have hρindex : n = d + (a + k) := by dsimp [k]; omega
        calc
          π v n = π u (a + (c + k)) := by
            rw [hπindex]
            exact (hTailπ (c + k)).symm
          _ = ρ u (c + (a + k)) := by rw [hSame]; congr 1; omega
          _ = ρ v n := by rw [hρindex]; exact hTailρ (a + k)
    rw [hsamev]
    exact pathSoutheastLE_self (ρ v)
  · by_contra hnot
    obtain hforward | hreverse :=
      pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω v (π v) (ρ v) (hπ v) (hρ v)
    · exact hnot hforward
    · have hneq : ρ v ≠ π v := by
        intro heq
        apply hnot
        rw [heq]
        exact pathSoutheastLE_self (π v)
      have hcross :=
        no_outer_coalescence_of_crossed_locallyRightmost_rays_at_roots
          ω u v (π u) (ρ u) (ρ v) (π v)
          (hπ u) (hρ u) (hρ v) (hπ v)
          ⟨hu, hSame⟩ ⟨hreverse, hneq⟩ (hcoalρ u v)
      exact hcross (hcoalπ u v)

/-- Two canonical coalescing rightmost ray families have one global order
orientation on a common full event, including all signed roots. -/
theorem ae_rightmostCocyclePaths_globally_comparable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B C : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hCoalB : HasCoalescingRightmostPaths (environmentLaw μ) B)
    (hCoalC : HasCoalescingRightmostPaths (environmentLaw μ) C) :
    (∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      pathSoutheastLE
        (rightmostCocyclePath (fun x y => B x y ω) u)
        (rightmostCocyclePath (fun x y => C x y ω) u)) ∨
    (∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      pathSoutheastLE
        (rightmostCocyclePath (fun x y => C x y ω) u)
        (rightmostCocyclePath (fun x y => B x y ω) u)) := by
  let P := environmentLaw μ
  let z : Lattice := (1, 0)
  let T : Environment → Environment := environmentTranslationEquiv z
  let πB (ω : Environment) (u : Lattice) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y ω) u
  let πC (ω : Environment) (u : Lattice) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => C x y ω) u
  let E : Set Environment := {ω | pathSoutheastLE (πB ω 0) (πC ω 0)}

  have hBmeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun ω : Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hB.1.1.comp hArg
  have hCmeas (x y : Lattice) : Measurable (C x y) := by
    have hArg : Measurable (fun ω : Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hC.1.1.comp hArg
  have hRayB (u : Lattice) : Measurable (fun ω => πB ω u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath B hBmeas u n
  have hRayC (u : Lattice) : Measurable (fun ω => πC ω u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath C hCmeas u n
  have hE : MeasurableSet E := by
    exact measurableSet_pathSoutheastLE.preimage
      ((hRayB 0).prodMk (hRayC 0))

  have hGood : ∀ᵐ ω ∂P,
      (∀ u v, pathSoutheastLE (πB ω u) (πC ω u) →
        pathSoutheastLE (πB ω v) (πC ω v)) ∧
      (∀ u v, pathSoutheastLE (πC ω u) (πB ω u) →
        pathSoutheastLE (πC ω v) (πB ω v)) ∧
      (pathSoutheastLE (πB ω 0) (πC ω 0) ∨
        pathSoutheastLE (πC ω 0) (πB ω 0)) := by
    filter_upwards [hCoalB, hCoalC, hB.1.2.2, hC.1.2.2,
      hB.2.1, hC.2.1] with ω hCoB hCoC hAddB hAddC hRecB hRecC
    have hGeoB (u : Lattice) : IsLocallyRightmostGeodesic ω u (πB ω u) :=
      isLocallyRightmostGeodesic_rightmostCocyclePath ω _ hAddB hRecB u
    have hGeoC (u : Lattice) : IsLocallyRightmostGeodesic ω u (πC ω u) :=
      isLocallyRightmostGeodesic_rightmostCocyclePath ω _ hAddC hRecC u
    have hTransferBC (u v : Lattice) :=
      rightmost_families_order_at_all_roots ω (πB ω) (πC ω)
        hGeoB hGeoC hCoB hCoC u v
    have hTransferCB (u v : Lattice) :=
      rightmost_families_order_at_all_roots ω (πC ω) (πB ω)
        hGeoC hGeoB hCoC hCoB u v
    exact ⟨hTransferBC, hTransferCB,
      pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω 0 (πB ω 0) (πC ω 0) (hGeoB 0) (hGeoC 0)⟩

  have hCovB : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      B (x + z) (y + z) ω = B x y (T ω) := by
    exact ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => hB.1.2.1 x y z
  have hCovC : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      C (x + z) (y + z) ω = C x y (T ω) := by
    exact ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => hC.1.2.1 x y z
  have hInv : T ⁻¹' E =ᵐ[P] E := by
    filter_upwards [hGood, hCovB, hCovC] with ω hω hbc hcc
    have hPathB (n : ℕ) : πB (T ω) 0 n + z = πB ω z n := by
      exact rightmostCocyclePath_translate
        (fun x y => B x y ω) (fun x y => B x y (T ω)) z
        (fun x y => (hbc x y).symm) 0 n
    have hPathC (n : ℕ) : πC (T ω) 0 n + z = πC ω z n := by
      exact rightmostCocyclePath_translate
        (fun x y => C x y ω) (fun x y => C x y (T ω)) z
        (fun x y => (hcc x y).symm) 0 n
    have hShift : pathSoutheastLE (πB (T ω) 0) (πC (T ω) 0) ↔
        pathSoutheastLE (πB ω z) (πC ω z) := by
      have ht := pathSoutheastLE_translate_iff
        (πB (T ω) 0) (πC (T ω) 0) z
      have hBEq : (fun n => πB (T ω) 0 n + z) = πB ω z := funext hPathB
      have hCEq : (fun n => πC (T ω) 0 n + z) = πC ω z := funext hPathC
      rw [hBEq, hCEq] at ht
      exact ht.symm
    apply propext
    change pathSoutheastLE (πB (T ω) 0) (πC (T ω) 0) ↔
      pathSoutheastLE (πB ω 0) (πC ω 0)
    exact hShift.trans ⟨hω.1 z 0, hω.1 0 z⟩

  have hz : z ≠ 0 := by decide
  have hZeroOne :=
    ((ergodic_environment_translation μ z hz).quasiErgodic).ae_mem_or_ae_notMem₀
      hE.nullMeasurableSet hInv
  rcases hZeroOne with hAE | hNotAE
  · left
    filter_upwards [hGood, hAE] with ω hω hMem
    intro u
    exact hω.1 0 u hMem
  · right
    filter_upwards [hGood, hNotAE] with ω hω hNotMem
    intro u
    have hReverse : pathSoutheastLE (πC ω 0) (πB ω 0) := by
      rcases hω.2.2 with hForward | hBackward
      · exact (hNotMem hForward).elim
      · exact hBackward
    exact hω.2.1 0 u hReverse

end LPP.Busemann
