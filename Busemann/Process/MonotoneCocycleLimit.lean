/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RightmostPathCoalescenceApplications
public import Busemann.Probability.CanonicalCocycleMeans
public import Busemann.Probability.CanonicalInvariantConditionalMean
public import Busemann.Probability.CocycleIntegrability
public import Busemann.Process.LatticeCocycleEdgeLimits
public import Busemann.Process.MonotoneCocycleLimitAux
public import Busemann.Frozen.Definitions.InvariantCocycleTilt
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

-- Covariance and preservation of the environment law transport each origin
-- edge's integrability and mean to the corresponding edge at any signed site.
private theorem monotone_limit_translated_edge_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D : Lattice → Lattice → LPPDifferentiability.Environment → ℝ)
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
    change Integrable ((D 0 e) ∘ environmentTranslationEquiv x) (environmentLaw μ)
    exact hShift.integrable_comp_of_integrable hInt
  refine ⟨hComp.congr hCov.symm, ?_⟩
  calc
    (∫ ω, D x (x + e) ω ∂environmentLaw μ) =
        ∫ ω, D 0 e (environmentTranslationEquiv x ω) ∂environmentLaw μ :=
      integral_congr_ae hCov
    _ = ∫ ω, D 0 e ω ∂environmentLaw μ :=
      hShift.integral_comp' (D 0 e)

/-- A countable globally ordered family of canonical forward cocycles has a
forward, coalescing, integrable limit with its limiting deterministic tilt. -/
theorem exists_forward_coalescing_monotone_cocycle_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (B : ℕ → Lattice → Lattice → LPPDifferentiability.Environment → ℝ)
    (hB : ∀ n, IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) (B n))
    (hForward : ∀ n, IsForwardMeasurable (B n))
    (hs : ℕ → ℝ × ℝ) (h : ℝ × ℝ)
    (hTilt : ∀ n, ∀ᵐ ω ∂environmentLaw μ,
      invariantCocycleTilt (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
        (B n) (hB n) ω = hs n)
    (hConverges : Tendsto hs atTop (𝓝 h))
    (hOrder :
      (∀ᵐ ω ∂environmentLaw μ, ∀ (n : ℕ) (x : Lattice),
        B (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          B n x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        B n x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          B (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
      (∀ᵐ ω ∂environmentLaw μ, ∀ (n : ℕ) (x : Lattice),
        B n x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          B (n + 1) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        B (n + 1) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          B n x (x + ((0 : ℤ), (1 : ℤ))) ω)) :
    ∃ (C : Lattice → Lattice → LPPDifferentiability.Environment → ℝ),
      ∃ hC : IsGeneralizedBusemann (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C,
        IsForwardMeasurable C ∧
        HasCoalescingRightmostPaths (environmentLaw μ) C ∧
        (∀ᵐ ω ∂environmentLaw μ,
          invariantCocycleTilt (environmentLaw μ)
            (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω)
            C hC ω = h) ∧
        (∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice,
          Tendsto (fun n => B n x y ω) atTop (𝓝 (C x y ω))) ∧
        (∀ x y : Lattice,
          Tendsto (fun n => ∫ ω,
            |B n x y ω - C x y ω| ∂environmentLaw μ) atTop (𝓝 0)) ∧
        (∫ ω, C 0 ((1 : ℤ), (0 : ℤ)) ω ∂environmentLaw μ) = -h.1 ∧
        (∫ ω, C 0 ((0 : ℤ), (1 : ℤ)) ω ∂environmentLaw μ) = -h.2
    := by
  classical
  let P : Measure LPPDifferentiability.Environment := environmentLaw μ
  let T : Lattice → LPPDifferentiability.Environment → LPPDifferentiability.Environment :=
    fun z ω => environmentTranslationEquiv z ω
  let e₁ : Lattice := (1, 0)
  let e₂ : Lattice := (0, 1)
  have hMeans (n : ℕ) :=
    canonical_origin_means_of_deterministic_invariant_tilt
      μ (B n) (hB n) (hs n) (hTilt n)
  have hMeasB (n : ℕ) (x y : Lattice) : Measurable (B n x y) := by
    have hp : Measurable
        (fun ω : LPPDifferentiability.Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    exact (hB n).1.1.comp hp
  have hTranslated (n : ℕ) (x : Lattice) (i : Fin 2) :
      Integrable (B n x (x + finiteEdgeStep i)) P ∧
      (∫ ω, B n x (x + finiteEdgeStep i) ω ∂P) =
        if i = 0 then -(hs n).1 else -(hs n).2 := by
    have hOrigin₁ : Integrable (B n 0 e₁) P := (hB n).2.2 0 e₁
    have hOrigin₂ : Integrable (B n 0 e₂) P := (hB n).2.2 0 e₂
    fin_cases i
    · have ht := monotone_limit_translated_edge_mean μ (B n) (hB n).1
        x e₁ hOrigin₁
      simpa [P, e₁, finiteEdgeStep] using
        ⟨ht.1, ht.2.trans (hMeans n).1⟩
    · have ht := monotone_limit_translated_edge_mean μ (B n) (hB n).1
        x e₂ hOrigin₂
      simpa [P, e₂, finiteEdgeStep] using
        ⟨ht.1, ht.2.trans (hMeans n).2⟩
  have hMeanEast : Tendsto (fun n => -(hs n).1) atTop (𝓝 (-h.1)) :=
    hConverges.fst_nhds.neg
  have hMeanNorth : Tendsto (fun n => -(hs n).2) atTop (𝓝 (-h.2)) :=
    hConverges.snd_nhds.neg
  have hEdgeOrder (x : Lattice) (i : Fin 2) :
      (∀ᵐ ω ∂P, Monotone
        (fun n => B n x (x + finiteEdgeStep i) ω)) ∨
      (∀ᵐ ω ∂P, Antitone
        (fun n => B n x (x + finiteEdgeStep i) ω)) := by
    fin_cases i
    · rcases hOrder with ho | ho
      · right
        filter_upwards [ho] with ω hw
        exact antitone_nat_of_succ_le (fun n => by
          simpa [finiteEdgeStep] using (hw n x).1)
      · left
        filter_upwards [ho] with ω hw
        exact monotone_nat_of_le_succ (fun n => by
          simpa [finiteEdgeStep] using (hw n x).1)
    · rcases hOrder with ho | ho
      · left
        filter_upwards [ho] with ω hw
        exact monotone_nat_of_le_succ (fun n => by
          simpa [finiteEdgeStep] using (hw n x).2)
      · right
        filter_upwards [ho] with ω hw
        exact antitone_nat_of_succ_le (fun n => by
          simpa [finiteEdgeStep] using (hw n x).2)
  -- Each of the two signed edges uses its own translated deterministic mean.
  have hEdgeData (x : Lattice) (i : Fin 2) :
      ∃ L : LPPDifferentiability.Environment → ℝ,
        Measurable L ∧ Integrable L P ∧
        (∀ᵐ ω ∂P, Tendsto
          (fun n => B n x (x + finiteEdgeStep i) ω) atTop (𝓝 (L ω))) ∧
        Tendsto (fun n => ∫ ω,
          |B n x (x + finiteEdgeStep i) ω - L ω| ∂P) atTop (𝓝 0) := by
    have hm (n : ℕ) : Measurable (B n x (x + finiteEdgeStep i)) :=
      hMeasB n x (x + finiteEdgeStep i)
    have hi (n : ℕ) : Integrable (B n x (x + finiteEdgeStep i)) P :=
      (hTranslated n x i).1
    have hmean : Tendsto
        (fun n => ∫ ω, B n x (x + finiteEdgeStep i) ω ∂P) atTop
        (𝓝 (if i = 0 then -h.1 else -h.2)) := by
      have heq : (fun n => ∫ ω, B n x (x + finiteEdgeStep i) ω ∂P) =
          (fun n => if i = 0 then -(hs n).1 else -(hs n).2) := by
        funext n
        exact (hTranslated n x i).2
      rw [heq]
      by_cases he : i = 0
      · simpa [he] using hMeanEast
      · simpa [he] using hMeanNorth
    exact exists_integrable_limit_of_ordered_convergent_means P
      (fun n => B n x (x + finiteEdgeStep i)) hm hi (hEdgeOrder x i) hmean
  choose L hLm hLi hLc hLl1 using hEdgeData
  have hPairExists := ae_all_pair_limits_of_unit_edge_limits P B
    (fun n => (hB n).1.2.2) (fun x i => (hLc x i).mono fun ω hw => ⟨L x i ω, hw⟩)
  let C : Lattice → Lattice → LPPDifferentiability.Environment → ℝ :=
    fun x y ω => limUnder atTop (fun n => B n x y ω)
  have hPair : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      Tendsto (fun n => B n x y ω) atTop (𝓝 (C x y ω)) := by
    filter_upwards [hPairExists] with ω hw
    intro x y
    exact tendsto_nhds_limUnder (hw x y)
  have hEqEdge (x : Lattice) (i : Fin 2) :
      C x (x + finiteEdgeStep i) =ᵐ[P] L x i := by
    filter_upwards [hPair, hLc x i] with ω hp he
    exact tendsto_nhds_unique (hp x (x + finiteEdgeStep i)) he
  have hIntCEdge (x : Lattice) (i : Fin 2) :
      Integrable (C x (x + finiteEdgeStep i)) P :=
    (hLi x i).congr (hEqEdge x i).symm
  have hL1Edge (x : Lattice) (i : Fin 2) :
      Tendsto (fun n => ∫ ω,
        |B n x (x + finiteEdgeStep i) ω - C x (x + finiteEdgeStep i) ω| ∂P)
        atTop (𝓝 0) := by
    have heq : (fun n => ∫ ω,
        |B n x (x + finiteEdgeStep i) ω - C x (x + finiteEdgeStep i) ω| ∂P) =
        (fun n => ∫ ω,
          |B n x (x + finiteEdgeStep i) ω - L x i ω| ∂P) := by
      funext n
      apply integral_congr_ae
      filter_upwards [hEqEdge x i] with ω he
      rw [he]
    rw [heq]
    exact hLl1 x i
  have hMeasC : Measurable
      (fun p : (Lattice × Lattice) × LPPDifferentiability.Environment =>
        C p.1.1 p.1.2 p.2) := by
    exact (StronglyMeasurable.limUnder
      (fun n => ((hB n).1.1).stronglyMeasurable)).measurable
  have hAddAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
      is_additive (fun x y => B n x y ω) :=
    ae_all_iff.mpr (fun n => (hB n).1.2.2)
  have hAddC : ∀ᵐ ω ∂P, is_additive (fun x y => C x y ω) := by
    filter_upwards [hPair, hAddAll] with ω hp ha
    intro x y z
    have hsum := (hp x y).add (hp y z)
    have heq : (fun n => B n x y ω + B n y z ω) =
        (fun n => B n x z ω) := by
      funext n
      exact ha n x y z
    rw [heq] at hsum
    exact tendsto_nhds_unique hsum (hp x z)
  have hTranslatedPair (z : Lattice) : ∀ᵐ ω ∂P,
      ∀ x y : Lattice,
        Tendsto (fun n => B n x y (T z ω)) atTop (𝓝 (C x y (T z ω))) := by
    exact (measurePreserving_environmentTranslationEquiv μ z).quasiMeasurePreserving.tendsto_ae
      hPair
  have hCovC (x y z : Lattice) : ∀ᵐ ω ∂P,
      C (x + z) (y + z) ω = C x y (T z ω) := by
    have hc : ∀ᵐ ω ∂P, ∀ n : ℕ,
        B n (x + z) (y + z) ω = B n x y (T z ω) :=
      ae_all_iff.mpr (fun n => (hB n).1.2.1 x y z)
    filter_upwards [hPair, hTranslatedPair z, hc] with ω hp ht he
    have hl := hp (x + z) (y + z)
    have hr := ht x y
    have heq : (fun n => B n (x + z) (y + z) ω) =
        (fun n => B n x y (T z ω)) := by
      funext n
      exact he n
    rw [heq] at hl
    exact tendsto_nhds_unique hl hr
  have hRecAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
      recovers_environment ω (fun x y => B n x y ω) :=
    ae_all_iff.mpr (fun n => (hB n).2.1)
  have hRecC : recovers_weight_map_ae P (fun ω => ω) C := by
    filter_upwards [hPair, hRecAll] with ω hp hr
    intro x
    have hm := (hp x (x + e₁)).min (hp x (x + e₂))
    have heq : (fun n => min (B n x (x + e₁) ω) (B n x (x + e₂) ω)) =
        (fun _ => ω x) := by
      funext n
      exact hr n x
    rw [heq] at hm
    exact tendsto_nhds_unique hm tendsto_const_nhds
  have hCocycle : is_shift_covariant_cocycle P T C :=
    ⟨hMeasC, hCovC, hAddC⟩
  have hIntOrigin₁ : Integrable (C 0 e₁) P := by
    simpa [e₁, finiteEdgeStep] using hIntCEdge 0 0
  have hIntOrigin₂ : Integrable (C 0 e₂) P := by
    simpa [e₂, finiteEdgeStep] using hIntCEdge 0 1
  have hIntC : ∀ x y : Lattice, Integrable (C x y) P :=
    integrable_cocycle_of_integrable_origin_edges P T C
      (fun z => measurePreserving_environmentTranslationEquiv μ z)
      hCocycle hIntOrigin₁ hIntOrigin₂
  have hC : IsGeneralizedBusemann P T (fun ω => ω) C :=
    ⟨hCocycle, hRecC, hIntC⟩
  have hL1Pair : ∀ x y : Lattice,
      Tendsto (fun n => ∫ ω, |B n x y ω - C x y ω| ∂P) atTop (𝓝 0) :=
    all_pair_integral_abs_sub_tendsto_of_unit_edges P B C
      (fun n => (hB n).1.2.2) hAddC
      (fun n x i => (hTranslated n x i).1) hIntCEdge hL1Edge
  have hMeanC (i : Fin 2) :
      (∫ ω, C 0 (finiteEdgeStep i) ω ∂P) =
        if i = 0 then -h.1 else -h.2 := by
    have ht : Tendsto (fun n => ∫ ω, B n 0 (finiteEdgeStep i) ω ∂P)
        atTop (𝓝 (∫ ω, C 0 (finiteEdgeStep i) ω ∂P)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      have hbound (n : ℕ) :
          |(∫ ω, B n 0 (finiteEdgeStep i) ω ∂P) -
            (∫ ω, C 0 (finiteEdgeStep i) ω ∂P)| ≤
          ∫ ω, |B n 0 (finiteEdgeStep i) ω - C 0 (finiteEdgeStep i) ω| ∂P := by
        have hIntBn : Integrable (B n 0 (finiteEdgeStep i)) P := by
          simpa only [zero_add] using (hTranslated n 0 i).1
        have hIntCn : Integrable (C 0 (finiteEdgeStep i)) P := by
          simpa only [zero_add] using hIntCEdge 0 i
        rw [← integral_sub hIntBn hIntCn]
        exact abs_integral_le_integral_abs
      have hl := squeeze_zero (fun n => abs_nonneg _) hbound (by
        simpa only [zero_add] using hL1Edge 0 i)
      simpa only [Real.dist_eq] using hl
    have hm : Tendsto (fun n => ∫ ω, B n 0 (finiteEdgeStep i) ω ∂P)
        atTop (𝓝 (if i = 0 then -h.1 else -h.2)) := by
      have heq : (fun n => ∫ ω, B n 0 (finiteEdgeStep i) ω ∂P) =
          (fun n => if i = 0 then -(hs n).1 else -(hs n).2) := by
        funext n
        simpa only [zero_add] using (hTranslated n 0 i).2
      rw [heq]
      by_cases hi : i = 0
      · simpa [hi] using hMeanEast
      · simpa [hi] using hMeanNorth
    exact tendsto_nhds_unique ht hm
  have hMeanC₁ : (∫ ω, C 0 e₁ ω ∂P) = -h.1 := by
    simpa [e₁, finiteEdgeStep] using hMeanC 0
  have hMeanC₂ : (∫ ω, C 0 e₂ ω ∂P) = -h.2 := by
    simpa [e₂, finiteEdgeStep] using hMeanC 1
  have hCond₁ := canonical_condExp_full_invariants_eq_mean μ (C 0 e₁) hIntOrigin₁
  have hCond₂ := canonical_condExp_full_invariants_eq_mean μ (C 0 e₂) hIntOrigin₂
  have hTiltC : ∀ᵐ ω ∂P,
      invariantCocycleTilt P T (fun ω => ω) C hC ω = h := by
    filter_upwards [hCond₁, hCond₂] with ω hc₁ hc₂
    change (-(P[C 0 e₁ | latticeInvariantSigma T] ω),
      -(P[C 0 e₂ | latticeInvariantSigma T] ω)) = h
    rw [hc₁, hc₂, hMeanC₁, hMeanC₂]
    simp
  have hForwardC : IsForwardMeasurable C :=
    isForwardMeasurable_limUnder B hForward
  have hCoal : HasCoalescingRightmostPaths P C :=
    hasCoalescingRightmostPaths_environmentLaw_of_isForwardMeasurable
      μ hμ hmoment C hCocycle hRecC hIntOrigin₁ hIntOrigin₂ hForwardC
  exact ⟨C, hC, hForwardC, hCoal, hTiltC, hPair, hL1Pair,
    hMeanC₁, hMeanC₂⟩

end LPP.Busemann
