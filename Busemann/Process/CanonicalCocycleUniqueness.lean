/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits
public import Busemann.Frozen.Definitions.InvariantCocycleTilt

import Busemann.Process.CoalescingRayGlobalOrder
import Busemann.Process.CoalescingRayCocycleOrder
import Busemann.Frozen.Definitions.FiniteEdgeStep
import Busemann.Probability.CanonicalCocycleMeans
import LPP_Foundations.Model.LatticeEdgeIntegration
import LPP_Foundations.Probability.TranslationEquiv

/-! Same deterministic tilts identify coalescing canonical cocycles. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- Coalescing rightmost cocycles with the same deterministic invariant tilt
agree on every signed lattice pair almost surely. This is the uniqueness step
in Strong Existence, lines 1155–1166. -/
theorem ae_eq_of_coalescing_canonical_cocycles_same_tilt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B C : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hCoalB : HasCoalescingRightmostPaths (environmentLaw μ) B)
    (hCoalC : HasCoalescingRightmostPaths (environmentLaw μ) C)
    (h : ℝ × ℝ)
    (hTiltB : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B hB ω = h)
    (hTiltC : ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C hC ω = h) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice, B x y ω = C x y ω := by
  classical
  let eEast : Lattice := ((1 : ℤ), (0 : ℤ))
  let eNorth : Lattice := ((0 : ℤ), (1 : ℤ))

  -- The published deterministic tilt identity gives each origin edge mean.
  have hOriginMeansB :=
    canonical_origin_means_of_deterministic_invariant_tilt
      μ B hB h hTiltB
  have hOriginMeansC :=
    canonical_origin_means_of_deterministic_invariant_tilt
      μ C hC h hTiltC

  -- Covariance and preservation of the environment law transport an origin
  -- edge's integrability and mean to the same oriented edge at every site.
  have hTranslatedMean
      (D : Lattice → Lattice → Environment → ℝ)
      (hD : is_shift_covariant_cocycle (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) D)
      (x e : Lattice)
      (hInt : Integrable (D 0 e) (environmentLaw μ)) :
      Integrable (D x (x + e)) (environmentLaw μ) ∧
        (∫ ω, D x (x + e) ω ∂environmentLaw μ) =
          ∫ ω, D 0 e ω ∂environmentLaw μ := by
    have hShift := measurePreserving_environmentTranslationEquiv μ x
    have hCov : (fun ω => D x (x + e) ω) =ᵐ[environmentLaw μ]
        (fun ω => D 0 e (environmentTranslationEquiv x ω)) := by
      filter_upwards [hD.2.1 0 e x] with ω hω
      simpa only [zero_add, add_comm e x] using hω
    have hComp : Integrable
        (fun ω => D 0 e (environmentTranslationEquiv x ω))
        (environmentLaw μ) := by
      change Integrable ((D 0 e) ∘ environmentTranslationEquiv x)
        (environmentLaw μ)
      exact hShift.integrable_comp_of_integrable hInt
    refine ⟨hComp.congr hCov.symm, ?_⟩
    calc
      (∫ ω, D x (x + e) ω ∂environmentLaw μ) =
          ∫ ω, D 0 e (environmentTranslationEquiv x ω) ∂environmentLaw μ :=
        integral_congr_ae hCov
      _ = ∫ ω, D 0 e ω ∂environmentLaw μ :=
        hShift.integral_comp' (D 0 e)

  have hMeansAtB (x : Lattice) :
      (∫ ω, B x (x + eEast) ω ∂environmentLaw μ) = -h.1 ∧
        (∫ ω, B x (x + eNorth) ω ∂environmentLaw μ) = -h.2 := by
    have hEast := hTranslatedMean B hB.1 x eEast (hB.2.2 0 eEast)
    have hNorth := hTranslatedMean B hB.1 x eNorth (hB.2.2 0 eNorth)
    exact ⟨hEast.2.trans hOriginMeansB.1, hNorth.2.trans hOriginMeansB.2⟩

  have hMeansAtC (x : Lattice) :
      (∫ ω, C x (x + eEast) ω ∂environmentLaw μ) = -h.1 ∧
        (∫ ω, C x (x + eNorth) ω ∂environmentLaw μ) = -h.2 := by
    have hEast := hTranslatedMean C hC.1 x eEast (hC.2.2 0 eEast)
    have hNorth := hTranslatedMean C hC.1 x eNorth (hC.2.2 0 eNorth)
    exact ⟨hEast.2.trans hOriginMeansC.1, hNorth.2.trans hOriginMeansC.2⟩

  -- Equal integrals and an almost-sure order identify each ordered edge pair.
  have hOrderedEqualities
      (f g : Lattice → Environment → ℝ)
      (hf : ∀ x, Integrable (f x) (environmentLaw μ))
      (hg : ∀ x, Integrable (g x) (environmentLaw μ))
      (hMean : ∀ x, (∫ ω, f x ω ∂environmentLaw μ) =
        ∫ ω, g x ω ∂environmentLaw μ)
      (hOrder : ∀ x, f x ≤ᵐ[environmentLaw μ] g x) :
      ∀ᵐ ω ∂environmentLaw μ, ∀ x, f x ω = g x ω := by
    apply ae_all_iff.mpr
    intro x
    exact (integral_eq_iff_of_ae_le (hf x) (hg x) (hOrder x)).mp (hMean x)

  -- Once all signed unit edges agree, additive uniqueness extends agreement
  -- to every ordered pair of lattice points.
  have hExtendFromEdges
      (hEdges : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
        B x (x + eEast) ω = C x (x + eEast) ω ∧
        B x (x + eNorth) ω = C x (x + eNorth) ω) :
      ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice, B x y ω = C x y ω := by
    filter_upwards [hEdges, hB.1.2.2, hC.1.2.2] with ω hEdge haddB haddC
    change ∀ x y z : Lattice, B x y ω + B y z ω = B x z ω at haddB
    change ∀ x y z : Lattice, C x y ω + C y z ω = C x z ω at haddC
    let E : Lattice → Fin 2 → ℝ := fun x i =>
      B x (x + finiteEdgeStep i) ω

    -- Additivity makes the two routes around each unit square agree.
    have hCurl : ∀ x, E x 0 + E (x + (1, 0)) 1 =
        E x 1 + E (x + (0, 1)) 0 := by
      intro x
      have hEastSquare :
          B x (x + (1, 0)) ω + B (x + (1, 0)) (x + (1, 1)) ω =
            B x (x + (1, 1)) ω :=
        haddB x (x + (1, 0)) (x + (1, 1))
      have hNorthSquare :
          B x (x + (0, 1)) ω + B (x + (0, 1)) (x + (1, 1)) ω =
            B x (x + (1, 1)) ω :=
        haddB x (x + (0, 1)) (x + (1, 1))
      have hEastStep : (x + (1, 0)) + (0, 1) = x + (1, 1) := by
        ext <;> simp [Prod.mk_add_mk, add_assoc]
      have hNorthStep : (x + (0, 1)) + (1, 0) = x + (1, 1) := by
        ext <;> simp [Prod.mk_add_mk, add_assoc]
      dsimp [E, finiteEdgeStep]
      rw [hEastStep, hNorthStep]
      linarith only [hEastSquare, hNorthSquare]

    obtain ⟨F, _, hFEdges, _, hUnique⟩ :=
      exists_unique_lattice_edge_extension E hCurl
    have hBEdges (x : Lattice) :
        B x (x + (1, 0)) ω = E x 0 ∧ B x (x + (0, 1)) ω = E x 1 := by
      constructor <;> simp [E, finiteEdgeStep]
    have hCEdges (x : Lattice) :
        C x (x + (1, 0)) ω = E x 0 ∧ C x (x + (0, 1)) ω = E x 1 := by
      constructor
      · simpa [E, finiteEdgeStep] using (hEdge x).1.symm
      · simpa [E, finiteEdgeStep] using (hEdge x).2.symm
    have hBAdditive : ∀ x y z : Lattice,
        (fun a b => B a b ω) x y + (fun a b => B a b ω) y z =
          (fun a b => B a b ω) x z := haddB
    have hCAdditive : ∀ x y z : Lattice,
        (fun a b => C a b ω) x y + (fun a b => C a b ω) y z =
          (fun a b => C a b ω) x z := haddC
    have hBExtension : (fun x y => B x y ω) = F :=
      hUnique (fun x y => B x y ω) hBAdditive hBEdges
    have hCExtension : (fun x y => C x y ω) = F :=
      hUnique (fun x y => C x y ω) hCAdditive hCEdges
    have hBC : (fun x y => B x y ω) = fun x y => C x y ω :=
      hBExtension.trans hCExtension.symm
    intro x y
    exact congrFun (congrFun hBC x) y

  -- The coalescing ray families have one global orientation.
  rcases ae_rightmostCocyclePaths_globally_comparable
      μ B C hB hC hCoalB hCoalC with hPathsBC | hPathsCB
  · have hEdgeOrder := ae_cocycle_opposite_edge_order_of_rightmostPath_order
      μ B C hB hC hCoalB hCoalC hPathsBC
    have hEastOrder (x : Lattice) :
        (fun ω => C x (x + eEast) ω) ≤ᵐ[environmentLaw μ]
          (fun ω => B x (x + eEast) ω) := by
      filter_upwards [hEdgeOrder] with ω hω
      exact (hω x).1
    have hNorthOrder (x : Lattice) :
        (fun ω => B x (x + eNorth) ω) ≤ᵐ[environmentLaw μ]
          (fun ω => C x (x + eNorth) ω) := by
      filter_upwards [hEdgeOrder] with ω hω
      exact (hω x).2
    have hEastEq := hOrderedEqualities
      (fun x ω => C x (x + eEast) ω) (fun x ω => B x (x + eEast) ω)
      (fun x => hC.2.2 x (x + eEast)) (fun x => hB.2.2 x (x + eEast))
      (fun x => (hMeansAtC x).1.trans (hMeansAtB x).1.symm) hEastOrder
    have hNorthEq := hOrderedEqualities
      (fun x ω => B x (x + eNorth) ω) (fun x ω => C x (x + eNorth) ω)
      (fun x => hB.2.2 x (x + eNorth)) (fun x => hC.2.2 x (x + eNorth))
      (fun x => (hMeansAtB x).2.trans (hMeansAtC x).2.symm) hNorthOrder
    have hEdges : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
        B x (x + eEast) ω = C x (x + eEast) ω ∧
        B x (x + eNorth) ω = C x (x + eNorth) ω := by
      filter_upwards [hEastEq, hNorthEq] with ω hE hN
      exact fun x => ⟨(hE x).symm, hN x⟩
    exact hExtendFromEdges hEdges
  · have hEdgeOrder := ae_cocycle_opposite_edge_order_of_rightmostPath_order
      μ C B hC hB hCoalC hCoalB hPathsCB
    have hEastOrder (x : Lattice) :
        (fun ω => B x (x + eEast) ω) ≤ᵐ[environmentLaw μ]
          (fun ω => C x (x + eEast) ω) := by
      filter_upwards [hEdgeOrder] with ω hω
      exact (hω x).1
    have hNorthOrder (x : Lattice) :
        (fun ω => C x (x + eNorth) ω) ≤ᵐ[environmentLaw μ]
          (fun ω => B x (x + eNorth) ω) := by
      filter_upwards [hEdgeOrder] with ω hω
      exact (hω x).2
    have hEastEq := hOrderedEqualities
      (fun x ω => B x (x + eEast) ω) (fun x ω => C x (x + eEast) ω)
      (fun x => hB.2.2 x (x + eEast)) (fun x => hC.2.2 x (x + eEast))
      (fun x => (hMeansAtB x).1.trans (hMeansAtC x).1.symm) hEastOrder
    have hNorthEq := hOrderedEqualities
      (fun x ω => C x (x + eNorth) ω) (fun x ω => B x (x + eNorth) ω)
      (fun x => hC.2.2 x (x + eNorth)) (fun x => hB.2.2 x (x + eNorth))
      (fun x => (hMeansAtC x).2.trans (hMeansAtB x).2.symm) hNorthOrder
    have hEdges : ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
        B x (x + eEast) ω = C x (x + eEast) ω ∧
        B x (x + eNorth) ω = C x (x + eNorth) ω := by
      filter_upwards [hEastEq, hNorthEq] with ω hE hN
      exact fun x => ⟨hE x, (hN x).symm⟩
    exact hExtendFromEdges hEdges

end LPP.Busemann
