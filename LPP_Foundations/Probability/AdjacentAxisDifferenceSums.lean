/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.EnvironmentLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LPP_Foundations.Probability.CoordinateLaw
import ProbabilityBasics.Probability.SymmetricIidWalkOscillation
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import ProbabilityBasics.Probability.SqrtTailMoments
import ProbabilityBasics.Probability.NonconstantVariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic

/-! The adjacent-axis difference walks on a common event, using the limited
symmetric iid walk argument separately for the two orientations. -/

@[expose] public section
open MeasureTheory LPPDifferentiability ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace LPP.Busemann

private def rowSites (x : Lattice) (a : ℕ × Fin 2) : Lattice :=
  if a.2 = 0 then x + (((a.1 : ℤ) + 1), (0 : ℤ))
  else x + ((a.1 : ℤ), (1 : ℤ))

private def columnSites (x : Lattice) (a : ℕ × Fin 2) : Lattice :=
  if a.2 = 0 then x + ((0 : ℤ), ((a.1 : ℤ) + 1))
  else x + ((1 : ℤ), (a.1 : ℤ))

-- Independence is within each orientation; the two families can share sites.
private theorem row_sites_injective (x : Lattice) : Function.Injective (rowSites x) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ h
  fin_cases i <;> fin_cases l
  · have hx : x.1 + ((j : ℤ) + 1) = x.1 + ((k : ℤ) + 1) := by
      simpa [rowSites] using congrArg Prod.fst h
    have hjk : j = k := by omega
    subst k
    rfl
  · have hy : x.2 = x.2 + 1 := by
      simpa [rowSites] using congrArg Prod.snd h
    omega
  · have hy : x.2 + 1 = x.2 := by
      simpa [rowSites] using congrArg Prod.snd h
    omega
  · have hx : x.1 + (j : ℤ) = x.1 + (k : ℤ) := by
      simpa [rowSites] using congrArg Prod.fst h
    have hjk : j = k := by omega
    subst k
    rfl

private theorem column_sites_injective (x : Lattice) :
    Function.Injective (columnSites x) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ h
  fin_cases i <;> fin_cases l
  · have hy : x.2 + ((j : ℤ) + 1) = x.2 + ((k : ℤ) + 1) := by
      simpa [columnSites] using congrArg Prod.snd h
    have hjk : j = k := by omega
    subst k
    rfl
  · have hx : x.1 = x.1 + 1 := by
      simpa [columnSites] using congrArg Prod.fst h
    omega
  · have hx : x.1 + 1 = x.1 := by
      simpa [columnSites] using congrArg Prod.fst h
    omega
  · have hy : x.2 + (j : ℤ) = x.2 + (k : ℤ) := by
      simpa [columnSites] using congrArg Prod.snd h
    have hjk : j = k := by omega
    subst k
    rfl

private theorem measurable_row_sum (x : Lattice) (n : ℕ) :
    Measurable (fun ω : LPPDifferentiability.Environment =>
      ∑ j ∈ Finset.range n,
        (ω (x + (((j : ℤ) + 1), (0 : ℤ))) - ω (x + ((j : ℤ), (1 : ℤ))))) := by
  exact (Finset.range n).measurable_fun_sum fun j _ =>
    (measurable_environment_eval (x + (((j : ℤ) + 1), (0 : ℤ)))).sub
      (measurable_environment_eval (x + ((j : ℤ), (1 : ℤ))))

private theorem measurable_column_sum (x : Lattice) (n : ℕ) :
    Measurable (fun ω : LPPDifferentiability.Environment =>
      ∑ j ∈ Finset.range n,
        (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) - ω (x + ((1 : ℤ), (j : ℤ))))) := by
  exact (Finset.range n).measurable_fun_sum fun j _ =>
    (measurable_environment_eval (x + ((0 : ℤ), ((j : ℤ) + 1)))).sub
      (measurable_environment_eval (x + ((1 : ℤ), (j : ℤ))))

private theorem measurableSet_all_nat_thresholds :
    MeasurableSet {ω : LPPDifferentiability.Environment |
      ∀ x : Lattice, ∀ M : ℕ,
        (∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
          (ω (x + (((j : ℤ) + 1), (0 : ℤ))) - ω (x + ((j : ℤ), (1 : ℤ))))) ∧
        (∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
          (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) - ω (x + ((1 : ℤ), (j : ℤ)))))} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro M
  have hRow : MeasurableSet {ω : LPPDifferentiability.Environment |
      ∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
        (ω (x + (((j : ℤ) + 1), (0 : ℤ))) - ω (x + ((j : ℤ), (1 : ℤ))))} := by
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (measurable_row_sum x n)
  have hColumn : MeasurableSet {ω : LPPDifferentiability.Environment |
      ∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
        (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) - ω (x + ((1 : ℤ), (j : ℤ))))} := by
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_column_sum x n)
  exact hRow.inter hColumn

private theorem real_thresholds_of_nat (S : ℕ → ℝ)
    (h : ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < S n) :
    ∀ K : ℝ, ∃ n : ℕ, K < S n := by
  intro K
  obtain ⟨M, hM⟩ := exists_nat_gt K
  obtain ⟨n, hn⟩ := h M
  exact ⟨n, lt_trans hM hn⟩

-- The original moment hypothesis supplies the finite, strictly positive
-- variance of the marginal; no moment or nondegeneracy premise is added.
private theorem marginal_memLp_and_variance_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    MemLp (fun t : ℝ => t) 2 μ ∧
      0 < variance (fun t : ℝ => t) μ := by
  obtain ⟨p, hp, hmoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hmoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hmoment
  have h2 := sqrt_tail_integrable_sq μ hneg hpos
  have hNonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c := by
    rintro ⟨c, hc⟩
    have hOne : μ ({c} : Set ℝ) = 1 :=
      (mem_ae_iff_prob_eq_one (measurableSet_singleton c)).mp hc
    exact (ne_of_lt (hμ c)) hOne
  refine ⟨(memLp_two_iff_integrable_sq (by fun_prop)).mpr h2, ?_⟩
  rw [variance_eq_integral (X := fun t : ℝ => t) (μ := μ) measurable_id.aemeasurable]
  exact ProbabilityBasics.integral_centered_sq_pos_of_not_ae_const μ h2 hNonconstant

-- A common proof for either orientation. The injective site map guarantees
-- independence within that orientation, without a claim across orientations.
private theorem ae_unbounded_site_pair_differences
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (site : ℕ × Fin 2 → Lattice) (hsite : Function.Injective site) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n, (ω (site (j, 0)) - ω (site (j, 1))) := by
  let P := environmentLaw μ
  let Q : Measure (Fin 2 → ℝ) := Measure.infinitePi (fun _ : Fin 2 => μ)
  let D (v : Fin 2 → ℝ) : ℝ := v 0 - v 1
  let ν : Measure ℝ := Q.map D
  let F (ω : LPPDifferentiability.Environment) (n : ℕ) (i : Fin 2) := ω (site (n, i))
  let X (n : ℕ) (ω : LPPDifferentiability.Environment) := D (F ω n)
  have hD : Measurable D := (measurable_pi_apply 0).sub (measurable_pi_apply 1)
  have hF : Measurable F := by
    exact measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun i =>
      measurable_environment_eval (site (n, i))
  have hX (n : ℕ) : Measurable (X n) := by
    exact hD.comp ((measurable_pi_apply n).comp hF)
  have hPath : Measurable (fun ω n => X n ω) := measurable_pi_iff.mpr hX
  -- Reindex the independent site field, then group consecutive pairs by curry.
  have hPairLaw : P.map F = Measure.infinitePi (fun _ : ℕ => Q) := by
    let A (ω : LPPDifferentiability.Environment) (p : ℕ × Fin 2) := ω (site p)
    have hA : Measurable A := measurable_pi_iff.mpr fun p =>
      measurable_environment_eval (site p)
    have hALaw : P.map A = Measure.infinitePi (fun _ : ℕ × Fin 2 => μ) :=
      Measure.map_infinitePi_infinitePi_of_inj hsite
    calc
      P.map F = (P.map A).map (MeasurableEquiv.curry ℕ (Fin 2) ℝ) :=
        (Measure.map_map (MeasurableEquiv.curry ℕ (Fin 2) ℝ).measurable hA).symm
      _ = Measure.infinitePi (fun _ : ℕ => Q) := by
        rw [hALaw]
        exact Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) => μ)
  have hLaw : P.map (fun ω n => X n ω) = Measure.infinitePi (fun _ : ℕ => ν) := by
    have hApplyD : Measurable (fun f : ℕ → Fin 2 → ℝ => fun n => D (f n)) :=
      measurable_pi_iff.mpr fun n => hD.comp (measurable_pi_apply n)
    calc
      P.map (fun ω n => X n ω) =
          (P.map F).map (fun f n => D (f n)) :=
        (Measure.map_map hApplyD hF).symm
      _ = Measure.infinitePi (fun _ : ℕ => ν) := by
        rw [hPairLaw]
        exact Measure.infinitePi_map_pi _ (fun _ => hD)
  have hMarginal (n : ℕ) : P.map (X n) = ν := by
    calc
      P.map (X n) = (P.map (fun ω n => X n ω)).map (fun f => f n) :=
        (Measure.map_map (measurable_pi_apply n) hPath).symm
      _ = ν := by rw [hLaw, Measure.infinitePi_map_eval]
  have hIndep : iIndepFun X P := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hX).mpr
    rw [hLaw]
    congr 1
    funext n
    exact (hMarginal n).symm
  have hIdent (n : ℕ) : IdentDistrib (X n) (X 0) P P :=
    ⟨(hX n).aemeasurable, (hX 0).aemeasurable,
      (hMarginal n).trans (hMarginal 0).symm⟩
  have hToD : IdentDistrib (X 0) D P Q :=
    ⟨(hX 0).aemeasurable, hD.aemeasurable, hMarginal 0⟩
  -- Swapping the two iid coordinates reflects the difference law.
  let swap (v : Fin 2 → ℝ) (i : Fin 2) := v (Equiv.swap (0 : Fin 2) 1 i)
  have hSwapMeas : Measurable swap := by fun_prop
  have hSwapLaw : Q.map swap = Q :=
    Measure.map_infinitePi_infinitePi_of_inj (Equiv.swap (0 : Fin 2) 1).injective
  have hSwapIdent : IdentDistrib (fun v : Fin 2 → ℝ => v) swap Q Q :=
    ⟨measurable_id.aemeasurable, hSwapMeas.aemeasurable, by
      change Q.map id = Q.map swap
      rw [Measure.map_id, hSwapLaw]⟩
  have hDSymm : IdentDistrib D (fun v => -(D v)) Q Q := by
    have h := hSwapIdent.comp hD
    have heq : D ∘ swap = fun v => -(D v) := by
      funext v
      simp only [Function.comp_apply, D, swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    rw [heq] at h
    exact h
  have hSymm : IdentDistrib (X 0) (fun ω => -(X 0 ω)) P P :=
    hToD.trans (hDSymm.trans (hToD.comp measurable_neg).symm)
  -- Finite positive marginal variance gives a nonzero difference walk.
  obtain ⟨hMem, hVarPos⟩ := marginal_memLp_and_variance_pos μ hμ hmoment
  have hCoordinate (i : Fin 2) : IdentDistrib (fun v : Fin 2 → ℝ => v i)
      (fun t : ℝ => t) Q μ :=
    ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, by
      dsimp [Q]
      rw [Measure.infinitePi_map_eval]
      change μ = μ.map id
      rw [Measure.map_id]⟩
  have hCoordIndep : IndepFun (fun v : Fin 2 → ℝ => v 0)
      (fun v : Fin 2 → ℝ => v 1) Q :=
    (iIndepFun_infinitePi (P := fun _ : Fin 2 => μ)
      (X := fun _ (t : ℝ) => t) (fun _ => measurable_id)).indepFun (by decide)
  have hDiffVariance : variance D Q =
      variance (fun t : ℝ => t) μ + variance (fun t : ℝ => t) μ := by
    calc
      variance D Q = variance (fun v : Fin 2 → ℝ => v 0 + -(v 1)) Q := by
        simp only [D, sub_eq_add_neg]
      _ = variance (fun v : Fin 2 → ℝ => v 0) Q +
          variance (fun v : Fin 2 → ℝ => -(v 1)) Q :=
        (hCoordIndep.comp measurable_id measurable_neg).variance_fun_add
          ((hCoordinate 0).symm.memLp_snd hMem) ((hCoordinate 1).symm.memLp_snd hMem).neg
      _ = variance (fun t : ℝ => t) μ + variance (fun t : ℝ => t) μ := by
        rw [variance_fun_neg, (hCoordinate 0).variance_eq, (hCoordinate 1).variance_eq]
  have hNonzero : ¬ ∀ᵐ ω ∂P, X 0 ω = 0 := by
    intro hzero
    have hVZero : variance (X 0) P = 0 :=
      (variance_congr hzero).trans (variance_zero P)
    rw [hToD.variance_eq, hDiffVariance] at hVZero
    linarith
  exact ProbabilityBasics.ae_unbounded_above_sum_of_symmetric_iid P X hX
    hIndep hIdent hSymm hNonzero

/-- On one common environment event, both adjacent-axis difference walks have
arbitrarily large positive partial sums from every signed site. This is the
isolated symmetric iid walk input of GRS, arXiv:1510.00860v1, Lemma 5.1;
the real-law moment assumption supplies finite positive variance internally. -/
theorem exists_full_event_unbounded_adjacent_axis_difference_sums
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ E : Set Environment,
      MeasurableSet E ∧ environmentLaw μ E = 1 ∧
      ∀ ω ∈ E, ∀ x : Lattice, ∀ K : ℝ,
        (∃ n : ℕ, K < ∑ j ∈ Finset.range n,
          (ω (x + (((j : ℤ) + 1), (0 : ℤ))) -
            ω (x + ((j : ℤ), (1 : ℤ))))) ∧
        (∃ n : ℕ, K < ∑ j ∈ Finset.range n,
          (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) -
            ω (x + ((1 : ℤ), (j : ℤ))))) := by
  have hRow (x : Lattice) : ∀ᵐ ω ∂environmentLaw μ, ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n,
        (ω (x + (((j : ℤ) + 1), (0 : ℤ))) - ω (x + ((j : ℤ), (1 : ℤ)))) := by
    simpa [rowSites] using
      ae_unbounded_site_pair_differences μ hμ hmoment (rowSites x) (row_sites_injective x)
  have hColumn (x : Lattice) : ∀ᵐ ω ∂environmentLaw μ, ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n,
        (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) - ω (x + ((1 : ℤ), (j : ℤ)))) := by
    simpa [columnSites] using
      ae_unbounded_site_pair_differences μ hμ hmoment (columnSites x) (column_sites_injective x)
  let E : Set LPPDifferentiability.Environment := {ω | ∀ x : Lattice, ∀ M : ℕ,
    (∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
      (ω (x + (((j : ℤ) + 1), (0 : ℤ))) - ω (x + ((j : ℤ), (1 : ℤ))))) ∧
    (∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n,
      (ω (x + ((0 : ℤ), ((j : ℤ) + 1))) - ω (x + ((1 : ℤ), (j : ℤ)))))}
  have hMeas : MeasurableSet E := measurableSet_all_nat_thresholds
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ω ∈ E := by
    apply ae_all_iff.mpr
    intro x
    filter_upwards [hRow x, hColumn x] with ω hR hC
    exact fun M => ⟨hR M, hC M⟩
  refine ⟨E, hMeas, (mem_ae_iff_prob_eq_one hMeas).mp hAE, ?_⟩
  intro ω hω x K
  exact ⟨real_thresholds_of_nat _ (fun M => (hω x M).1) K,
    real_thresholds_of_nat _ (fun M => (hω x M).2) K⟩

end LPP.Busemann
