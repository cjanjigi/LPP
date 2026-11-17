/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.ForwardMeasurable
public import ProbabilityBasics.Probability.Scheffe
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Measurability of pointwise limits of canonical forward cocycles. -/

public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology ENNReal

namespace LPP.Busemann

/-- A pointwise `limUnder` of forward fields is forward measurable. The limit
operator uses its fixed default only where that particular pair does not
converge. This is the measurable-limit step of the unpublished H lemma. -/
theorem isForwardMeasurable_limUnder
    (B : ℕ → Lattice → Lattice → Environment → ℝ)
    (hForward : ∀ n, IsForwardMeasurable (B n)) :
    IsForwardMeasurable
      (fun x y ω => limUnder atTop (fun n => B n x y ω)) := by
  intro u x y hux huy
  let : MeasurableSpace Environment := forwardWeightSigma u
  have hm (n : ℕ) :
      @Measurable Environment ℝ (forwardWeightSigma u) inferInstance
        (B n x y) := hForward n u x y hux huy
  exact (StronglyMeasurable.limUnder
    (fun n => (hm n).stronglyMeasurable)).measurable

end LPP.Busemann

namespace LPP.Busemann

/-- Nonnegative increasing real random variables with bounded means have a
finite integrable limit, and converge to it in integral absolute difference.
This is the signed-difference monotone-convergence step of the unpublished H lemma. -/
theorem exists_integrable_limit_of_monotone_bounded_means
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (Y n))
    (hInt : ∀ n, Integrable (Y n) P)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun n => Y n ω))
    (hBound : ∃ K : ℝ, ∀ n, (∫ ω, Y n ω ∂P) ≤ K) :
    ∃ L : Ω → ℝ, Measurable L ∧ Integrable L P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (L ω))) ∧
      Tendsto (fun n => ∫ ω, |Y n ω - L ω| ∂P) atTop (𝓝 0) := by
  let F : Ω → ℝ≥0∞ := fun ω => ⨆ n, ENNReal.ofReal (Y n ω)
  let L : Ω → ℝ := fun ω => (F ω).toReal
  have hFm : Measurable F := Measurable.iSup (fun n => (hMeas n).ennreal_ofReal)
  have hYm (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (Y n ω)) P :=
    ((hMeas n).ennreal_ofReal).aemeasurable
  have hYmono : ∀ᵐ ω ∂P, Monotone (fun n => ENNReal.ofReal (Y n ω)) := by
    filter_upwards [hMono] with ω hω
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (hω hij)
  obtain ⟨K, hK⟩ := hBound
  have hFbound : (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal K := by
    rw [lintegral_iSup' hYm hYmono]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt n) (hNonneg n)]
    exact ENNReal.ofReal_le_ofReal (hK n)
  have hFfinite : (∫⁻ ω, F ω ∂P) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFbound
  have hLae : ∀ᵐ ω ∂P, F ω < ∞ := ae_lt_top hFm hFfinite
  have hLm : Measurable L := hFm.ennreal_toReal
  have hLi : Integrable L P :=
    integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hFfinite
  have hConv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hLae, hYmono, ae_all_iff.mpr hNonneg] with ω hω hmon hnon
    have hExt : Tendsto (fun n => ENNReal.ofReal (Y n ω)) atTop (𝓝 (F ω)) :=
      tendsto_atTop_iSup hmon
    have hReal := (ENNReal.tendsto_toReal hω.ne).comp hExt
    have hfun : (ENNReal.toReal ∘ fun n => ENNReal.ofReal (Y n ω)) =
        (fun n => Y n ω) := by
      funext n
      exact ENNReal.toReal_ofReal (hnon n)
    rw [hfun] at hReal
    exact hReal
  have hLnonneg : ∀ᵐ ω ∂P, 0 ≤ L ω :=
    Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
  have hMean := integral_tendsto_of_tendsto_of_monotone hInt hLi hMono hConv
  exact ⟨L, hLm, hLi, hConv,
    LPPDifferentiability.tendsto_integral_abs_sub_of_ae_tendsto
      hInt hLi hNonneg hLnonneg hConv hMean⟩

/-- An almost-sure increasing integrable real sequence with bounded means has
an integrable almost-sure and L1 limit. This applies the nonnegative lemma to
the difference from the initial value. -/
theorem exists_integrable_limit_of_increasing_bounded_means
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hInt : ∀ n, Integrable (X n) P)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun n => X n ω))
    (hBound : ∃ K : ℝ, ∀ n, (∫ ω, X n ω ∂P) ≤ K) :
    ∃ L : Ω → ℝ, Measurable L ∧ Integrable L P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (L ω))) ∧
      Tendsto (fun n => ∫ ω, |X n ω - L ω| ∂P) atTop (𝓝 0) := by
  let Y : ℕ → Ω → ℝ := fun n ω => max (X n ω - X 0 ω) 0
  have hYeq (n : ℕ) : Y n =ᵐ[P] (fun ω => X n ω - X 0 ω) := by
    filter_upwards [hMono] with ω hm
    have hle : X 0 ω ≤ X n ω := hm (Nat.zero_le n)
    simp [Y, max_eq_left (sub_nonneg.mpr hle)]
  have hYm (n : ℕ) : Measurable (Y n) :=
    ((hMeas n).sub (hMeas 0)).max measurable_const
  have hYi (n : ℕ) : Integrable (Y n) P :=
    ((hInt n).sub (hInt 0)).sup (integrable_zero _ _ P)
  have hYn (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ Y n ω :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hYmono : ∀ᵐ ω ∂P, Monotone (fun n => Y n ω) := by
    filter_upwards [hMono] with ω hm
    intro i j hij
    exact max_le_max (sub_le_sub_right (hm hij) _) le_rfl
  obtain ⟨K, hK⟩ := hBound
  have hYBound : ∃ K' : ℝ, ∀ n, (∫ ω, Y n ω ∂P) ≤ K' := by
    refine ⟨K - ∫ ω, X 0 ω ∂P, ?_⟩
    intro n
    rw [integral_congr_ae (hYeq n), integral_sub (hInt n) (hInt 0)]
    exact sub_le_sub_right (hK n) _
  obtain ⟨M, hMm, hMi, hMc, hMl1⟩ :=
    exists_integrable_limit_of_monotone_bounded_means P Y hYm hYi hYn hYmono hYBound
  refine ⟨fun ω => M ω + X 0 ω, hMm.add (hMeas 0), hMi.add (hInt 0), ?_, ?_⟩
  · filter_upwards [hMc, ae_all_iff.mpr hYeq] with ω hc heq
    have hc' := hc.add (tendsto_const_nhds (x := X 0 ω))
    convert hc' using 1
    ext n
    have hn := heq n
    dsimp [Y] at hn
    linarith
  · have heq : ∀ n, (fun ω => |X n ω - (M ω + X 0 ω)|) =ᵐ[P]
        (fun ω => |Y n ω - M ω|) := by
      intro n
      filter_upwards [hYeq n] with ω hn
      rw [hn]
      ring
    have hf : (fun n => ∫ ω, |X n ω - (M ω + X 0 ω)| ∂P) =
        (fun n => ∫ ω, |Y n ω - M ω| ∂P) := by
      funext n
      exact integral_congr_ae (heq n)
    rw [hf]
    exact hMl1

/-- An almost-sure decreasing integrable real sequence with bounded means
below has an integrable almost-sure and L1 limit. -/
theorem exists_integrable_limit_of_decreasing_bounded_means
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hInt : ∀ n, Integrable (X n) P)
    (hAnti : ∀ᵐ ω ∂P, Antitone (fun n => X n ω))
    (hBound : ∃ K : ℝ, ∀ n, K ≤ (∫ ω, X n ω ∂P)) :
    ∃ L : Ω → ℝ, Measurable L ∧ Integrable L P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (L ω))) ∧
      Tendsto (fun n => ∫ ω, |X n ω - L ω| ∂P) atTop (𝓝 0) := by
  have hBoundNeg : ∃ K' : ℝ, ∀ n,
      (∫ ω, -X n ω ∂P) ≤ K' := by
    obtain ⟨K, hK⟩ := hBound
    refine ⟨-K, ?_⟩
    intro n
    rw [integral_neg]
    exact neg_le_neg (hK n)
  obtain ⟨M, hMm, hMi, hMc, hMl1⟩ :=
    exists_integrable_limit_of_increasing_bounded_means P
      (fun n ω => -X n ω) (fun n => (hMeas n).neg)
      (fun n => (hInt n).neg) (by
        filter_upwards [hAnti] with ω ha
        intro i j hij
        exact neg_le_neg (ha hij)) hBoundNeg
  refine ⟨fun ω => -M ω, hMm.neg, hMi.neg, ?_, ?_⟩
  · filter_upwards [hMc] with ω hc
    have hc' := hc.neg
    simpa only [neg_neg] using hc'
  · convert hMl1 using 1
    ext n
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      calc
        |X n ω - -M ω| = |-(-X n ω - M ω)| := by congr 1; ring
        _ = |-X n ω - M ω| := abs_neg _)

/-- Either monotone direction admits a finite integrable L1 limit when the
means themselves converge. The two orientations use separate signed MCT
differences from the initial value. -/
theorem exists_integrable_limit_of_ordered_convergent_means
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hInt : ∀ n, Integrable (X n) P)
    (hOrder : (∀ᵐ ω ∂P, Monotone (fun n => X n ω)) ∨
      (∀ᵐ ω ∂P, Antitone (fun n => X n ω)))
    {m : ℝ}
    (hMean : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) :
    ∃ L : Ω → ℝ, Measurable L ∧ Integrable L P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (L ω))) ∧
      Tendsto (fun n => ∫ ω, |X n ω - L ω| ∂P) atTop (𝓝 0) := by
  have hb := Metric.isBounded_range_of_tendsto _ hMean
  rcases hOrder with hMono | hAnti
  · obtain ⟨K, hK⟩ := hb.bddAbove
    exact exists_integrable_limit_of_increasing_bounded_means P X hMeas hInt
      hMono ⟨K, fun n => hK (Set.mem_range_self n)⟩
  · obtain ⟨K, hK⟩ := hb.bddBelow
    exact exists_integrable_limit_of_decreasing_bounded_means P X hMeas hInt
      hAnti ⟨K, fun n => hK (Set.mem_range_self n)⟩

end LPP.Busemann
