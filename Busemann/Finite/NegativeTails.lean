/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.Integrability
public import Busemann.Frozen.Definitions.FiniteBusemannSharedHorizonLaw
import Busemann.Finite.Measurability
import Busemann.Finite.Recovery
import LPP_Foundations.Probability.CoordinateLaw

/-!
# Negative excess tails of finite Busemann edges

The actual finite edge has a negative excess tail bounded by the starting-site tail.
The same bound holds after averaging over the literal shared environment and horizon law.

## Main results

- finite_busemann_edge_negative_excess_le_site_negative_excess: pointwise domination.
- integral_finite_busemann_edge_negative_excess_shared_horizon_le: actual finite-law domination.

## References

- JR arXiv:1810.03580v3, proof of Lemma 4.8 after equation (4.17).
- The deterministic finite recovery theorem and the actual finite shared-horizon law.
- The uniform-origin family integral and the fixed-coordinate law of the environment.
-/

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- At every signed horizon, an edge negative excess tail is bounded by the
starting weight tail. This is the finite pointwise step in JR arXiv:1810.03580v3,
proof of Lemma 4.8 after equation (4.17). -/
theorem finite_busemann_edge_negative_excess_le_site_negative_excess
    (ω : Environment) (h : ℝ × ℝ) (x : Lattice) (n : ℤ)
    (i : Fin 2) (R : ℝ) (hR : 0 ≤ R) :
    max (-finiteBusemannEdge ω h x n i - R) 0 ≤ max (-ω x - R) 0 := by
  by_cases hactive : x.1 + x.2 < n
  · -- The active recovery identity bounds both outgoing edges below by the site weight.
    have hrecover := finiteBusemannEdge_min_of_active ω h x n hactive
    have hedge : ω x ≤ finiteBusemannEdge ω h x n i := by
      fin_cases i
      · rw [← hrecover]
        exact min_le_left _ _
      · rw [← hrecover]
        exact min_le_right _ _
    have hexcess : -finiteBusemannEdge ω h x n i - R ≤ -ω x - R := by
      linarith
    exact max_le_max hexcess le_rfl
  · -- The literal inactive edge is zero, so its tail vanishes for R >= 0.
    have hzero : finiteBusemannEdge ω h x n i = 0 := by
      simp [finiteBusemannEdge, hactive]
    have hleft : max (-finiteBusemannEdge ω h x n i - R) 0 = 0 := by
      rw [hzero, neg_zero, zero_sub]
      exact max_eq_right (neg_nonpos.mpr hR)
    rw [hleft]
    exact le_max_right _ _

/-- The actual finite edge negative excess tail, averaged over one shared
uniform horizon, is bounded by the fixed one-site tail. This is the finite
negative-part domination step in JR arXiv:1810.03580v3, proof of Lemma 4.8
after equation (4.17). -/
theorem integral_finite_busemann_edge_negative_excess_shared_horizon_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (h : ℝ × ℝ) (x : Lattice) (i : Fin 2) (n : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ p : Environment × Fin (n + 1),
      max (-finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i - R) 0
        ∂finiteBusemannSharedHorizonLaw μ n) ≤
      ∫ t : ℝ, max (-t - R) 0 ∂μ := by
  classical
  let tailFamily : Fin (n + 1) → Environment → ℝ := fun k ω =>
    max (-finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i - R) 0

  -- Each fixed-horizon section inherits measurability from the edge map.
  have hmeas (k : Fin (n + 1)) : Measurable (tailFamily k) := by
    dsimp only [tailFamily]
    have hedge := measurable_finiteBusemannEdge h x ((k.val + 1 : ℕ) : ℤ) i
    have hexcess : Measurable
        (fun ω : Environment =>
          -finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i - R) :=
      hedge.neg.sub measurable_const
    exact Measurable.max hexcess measurable_const

  -- Each section is integrable by finite-edge integrability and positive-part closure.
  have hint (k : Fin (n + 1)) : Integrable (tailFamily k) (environmentLaw μ) := by
    dsimp only [tailFamily]
    have hedge := integrable_finiteBusemannEdge μ hμ h x
      ((k.val + 1 : ℕ) : ℤ) i
    have hexcess : Integrable
        (fun ω : Environment =>
          -finiteBusemannEdge ω h x ((k.val + 1 : ℕ) : ℤ) i - R) (environmentLaw μ) :=
      hedge.neg.sub (integrable_const R)
    exact hexcess.pos_part

  -- The finite family is integrable under the actual product with one shared horizon.
  have hfamily :
      Integrable (fun p : Environment × Fin (n + 1) => tailFamily p.2 p.1)
        (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    exact integrable_uniformOrigin_family (environmentLaw μ) n tailFamily hmeas hint

  -- The fixed-site tail is integrable from the actual coordinate marginal law.
  have hsiteMap :
      (environmentLaw μ).map (fun ω : Environment => ω x) = μ :=
    environmentLaw_map_eval μ x
  have hidIntegrable :
      Integrable (fun t : ℝ => t)
        ((environmentLaw μ).map (fun ω : Environment => ω x)) := by
    rw [hsiteMap]
    exact hμ
  have hsiteIntegrable :
      Integrable (fun ω : Environment => ω x) (environmentLaw μ) := by
    have hcomp :=
      (integrable_map_measure
        (μ := environmentLaw μ)
        (f := fun ω : Environment => ω x)
        (g := fun t : ℝ => t)
        measurable_id.aestronglyMeasurable
        (measurable_environment_eval x).aemeasurable).mp hidIntegrable
    convert hcomp using 1
    ext ω
    rfl
  have hsiteExcess :
      Integrable (fun ω : Environment => -ω x - R) (environmentLaw μ) :=
    hsiteIntegrable.neg.sub (integrable_const R)
  have hsiteTail :
      Integrable (fun ω : Environment => max (-ω x - R) 0) (environmentLaw μ) :=
    hsiteExcess.pos_part

  -- The comparison tail stays integrable after the first projection.
  have hright :
      Integrable
        (fun p : Environment × Fin (n + 1) => max (-p.1 x - R) 0)
        (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    have hcomp :=
      (uniformOriginProduct_fst (environmentLaw μ) n).integrable_comp_of_integrable
        (g := fun ω : Environment => max (-ω x - R) 0) hsiteTail
    convert hcomp using 1
    ext p
    rfl

  -- Each pair uses its environment and the same one-based horizon coordinate as the law.
  have hpointwise (p : Environment × Fin (n + 1)) :
      max (-finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i - R) 0 ≤
        max (-p.1 x - R) 0 :=
    finite_busemann_edge_negative_excess_le_site_negative_excess
      p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i R hR
  have hleft :
      Integrable
        (fun p : Environment × Fin (n + 1) =>
          max (-finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i - R) 0)
        (finiteBusemannSharedHorizonLaw μ n) := by
    simpa only [tailFamily] using hfamily
  have hmono :
      (∫ p : Environment × Fin (n + 1),
        max (-finiteBusemannEdge p.1 h x ((p.2.val + 1 : ℕ) : ℤ) i - R) 0
          ∂finiteBusemannSharedHorizonLaw μ n) ≤
        ∫ p : Environment × Fin (n + 1), max (-p.1 x - R) 0
          ∂finiteBusemannSharedHorizonLaw μ n :=
    integral_mono hleft hright (fun p => hpointwise p)

  -- The first projection and fixed-site map recover the original one-site law.
  have htailMeas : Measurable (fun t : ℝ => max (-t - R) 0) := by
    have hexcess : Measurable (fun t : ℝ => -t - R) :=
      measurable_id.neg.sub measurable_const
    exact Measurable.max hexcess measurable_const
  have hsiteTailMeas : Measurable
      (fun ω : Environment => max (-ω x - R) 0) := by
    have heval : Measurable (fun ω : Environment => ω x) :=
      measurable_environment_eval x
    exact htailMeas.comp heval
  have hprojectionIntegral :
      (∫ p : Environment × Fin (n + 1), max (-p.1 x - R) 0
        ∂uniformOriginProduct (environmentLaw μ) n) =
        ∫ ω : Environment, max (-ω x - R) 0 ∂environmentLaw μ := by
    have hprojection := uniformOriginProduct_fst (environmentLaw μ) n
    calc
      (∫ p : Environment × Fin (n + 1), max (-p.1 x - R) 0
        ∂uniformOriginProduct (environmentLaw μ) n) =
          ∫ ω : Environment, max (-ω x - R) 0
            ∂Measure.map Prod.fst (uniformOriginProduct (environmentLaw μ) n) := by
              exact (integral_map measurable_fst.aemeasurable
                hsiteTailMeas.aestronglyMeasurable).symm
      _ = ∫ ω : Environment, max (-ω x - R) 0 ∂environmentLaw μ := by
        rw [hprojection.map_eq]

  have hsiteIntegral :
      (∫ ω : Environment, max (-ω x - R) 0 ∂environmentLaw μ) =
        ∫ t : ℝ, max (-t - R) 0 ∂μ := by
    calc
      (∫ ω : Environment, max (-ω x - R) 0 ∂environmentLaw μ) =
          ∫ t : ℝ, max (-t - R) 0
            ∂Measure.map (fun ω : Environment => ω x) (environmentLaw μ) := by
              exact (integral_map (measurable_environment_eval x).aemeasurable
                htailMeas.aestronglyMeasurable).symm
      _ = ∫ t : ℝ, max (-t - R) 0 ∂μ := by
        rw [hsiteMap]

  have hcomparison :
      (∫ p : Environment × Fin (n + 1), max (-p.1 x - R) 0
        ∂finiteBusemannSharedHorizonLaw μ n) =
        ∫ t : ℝ, max (-t - R) 0 ∂μ := by
    rw [finiteBusemannSharedHorizonLaw]
    exact hprojectionIntegral.trans hsiteIntegral

  exact hmono.trans_eq hcomparison

end LPP.Busemann
