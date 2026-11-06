/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentResample
public import Martin2004.Probability.PassageMaximizerSelection
public import LPP_Foundations.Probability.PassageIntegrable
public import LPP_Foundations.Probability.TruncationLaw
public import ProbabilityBasics.Probability.ProductOppositeMonotoneIntegral
import Martin2004.Probability.SparseMinimumLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Negative remainder along a selected path

Finite selected-path negative clipping estimates under an integrable marginal.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- Measurable fibers of an actual finite-path selector give measurable site membership. -/
theorem measurableSet_selected_path_membership {u : Lattice} {d : ℕ × ℕ}
    (σ : Environment → Path u d)
    (hσ : ∀ p, MeasurableSet {ω | σ ω = p}) (v : Lattice) :
    MeasurableSet {ω | v ∈ (σ ω).collectedSites} := by
  classical
  have heq : {ω | v ∈ (σ ω).collectedSites} =
      ⋃ p : Path u d, ⋃ (_ : v ∈ p.collectedSites), {ω | σ ω = p} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hv
      exact ⟨σ ω, hv, rfl⟩
    · rintro ⟨p, hv, hp⟩
      simpa only [hp] using hv
  rw [heq]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => hσ p

/-- The same selected-path membership indicator is measurable as a function of the
fresh coordinate and the remaining environment together. -/
theorem measurable_selected_path_update_indicator {u : Lattice} {d : ℕ × ℕ}
    (σ : Environment → Path u d)
    (hσ : ∀ p, MeasurableSet {ω | σ ω = p}) (v : Lattice) :
    Measurable (fun p : ℝ × Environment =>
      if v ∈ (σ (Function.update p.2 v p.1)).collectedSites then (1 : ℝ) else 0) := by
  classical
  exact (Measurable.ite (measurableSet_selected_path_membership σ hσ v)
    measurable_const measurable_const).comp (measurable_environment_update v)

/-- Every collected site lies in the actual finite endpoint rectangle. -/
theorem Path.collectedSites_subset_endpoint_rectangle {d : ℕ × ℕ} (p : Path 0 d) :
    p.collectedSites ⊆ (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ
      (Finset.Icc (0 : ℤ) (d.2 : ℤ)) := by
  intro v hv
  obtain ⟨i, rfl⟩ := (p.mem_collectedSites_iff v).mp hv
  have h := p.vertex_mem_Icc i.castSucc
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨h.1.1, by simpa only [Prod.fst_add, Prod.fst_zero, zero_add] using h.2.1⟩,
      Finset.mem_Icc.mpr ⟨h.1.2, by simpa only [Prod.snd_add, Prod.snd_zero, zero_add] using h.2.2⟩⟩

/-- A sum over the endpoint rectangle of a selected-site indicator is exactly
the corresponding sum over the terminal-excluded, unrepeated path sites. -/
theorem Path.sum_endpoint_rectangle_indicator {d : ℕ × ℕ} (p : Path 0 d)
    (f : Lattice → ℝ) :
    (∑ v ∈ (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (d.2 : ℤ)),
      if v ∈ p.collectedSites then f v else 0) = ∑ v ∈ p.collectedSites, f v := by
  classical
  calc
    _ = ∑ v ∈ p.collectedSites, if v ∈ p.collectedSites then f v else 0 :=
      (Finset.sum_subset p.collectedSites_subset_endpoint_rectangle
        (fun v _ hv => ite_eq_right hv)).symm
    _ = _ := Finset.sum_congr rfl fun v hv => ite_eq_left hv

/-- The sum of the selected-path membership indicators counts exactly its length. -/
theorem Path.sum_endpoint_rectangle_membership {d : ℕ × ℕ} (p : Path 0 d) :
    (∑ v ∈ (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (d.2 : ℤ)),
      if v ∈ p.collectedSites then (1 : ℝ) else 0) = (d.1 + d.2 : ℕ) := by
  classical
  rw [p.sum_endpoint_rectangle_indicator]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, p.collectedSites_card]

/-- Literal clipping can exceed the original weight only by its negative remainder. -/
theorem clipped_sub_le_negative_remainder (L x : ℝ) :
    max (-L) (min L x) - x ≤ max (-L - x) 0 := by
  have h₁ := le_max_left (-L - x) 0
  have h₂ := le_max_right (-L - x) 0
  have h₃ := min_le_right L x
  apply sub_le_iff_le_add.mpr
  exact max_le (by linarith only [h₁]) (by linarith only [h₂, h₃])

/-- The same actual clipped maximizer gives the pointwise negative residual bound. -/
theorem lastPassage_clipped_sub_le_selected_negative_remainder
    (ω : Environment) (d : ℕ × ℕ) (L : ℝ) (p : Path 0 d)
    (hp : pathWeight (fun v => max (-L) (min L (ω v))) p =
      lastPassage (fun v => max (-L) (min L (ω v))) 0 d) :
    lastPassage (fun v => max (-L) (min L (ω v))) 0 d - lastPassage ω 0 d ≤
      ∑ v ∈ p.collectedSites, max (-L - ω v) 0 := by
  classical
  rw [← hp]
  calc
    _ ≤ pathWeight (fun v => max (-L) (min L (ω v))) p - pathWeight ω p :=
      sub_le_sub_left (pathWeight_le_lastPassage ω p) _
    _ = ∑ v ∈ p.collectedSites, (max (-L) (min L (ω v)) - ω v) := by
      rw [p.pathWeight_eq_sum_collectedSites, p.pathWeight_eq_sum_collectedSites,
        Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun v _ => clipped_sub_le_negative_remainder L (ω v)

/-- Earlier name of `integrable_sparseMinimum_residual` (same statement). -/
alias integrable_negative_remainder := integrable_sparseMinimum_residual

/-- Clipped finite passage times are integrable without an additional moment premise. -/
theorem integrable_clipped_lastPassage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) (u : Lattice) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment =>
      lastPassage (fun v => max (-L) (min L (ω v))) u d) (environmentLaw μ) := by
  have hclip : Integrable (fun x : ℝ => max (-L) (min L x)) μ :=
    (integrable_const (-L)).sup ((integrable_const L).inf hμ)
  have hm : Measurable (fun x : ℝ => max (-L) (min L x)) := by fun_prop
  have hi : Integrable (fun x : ℝ => x) (μ.map (fun x : ℝ => max (-L) (min L x))) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hm.aemeasurable).mpr hclip
  have hp : Integrable (fun ω : Environment => lastPassage ω u d)
      ((environmentLaw μ).map (fun ω : Environment => fun v => max (-L) (min L (ω v)))) := by
    rw [environmentLaw_map_clipped]
    exact integrable_lastPassage _ hi u d
  exact hp.comp_measurable (Measurable.of_eval fun v =>
    measurable_const.max (measurable_const.min (measurable_environment_eval v)))

/-- Selected residuals are genuinely integrable because the membership indicator
is measurable and bounded and the actual coordinate residual is integrable. -/
theorem integrable_selected_negative_remainder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {u : Lattice} {d : ℕ × ℕ}
    (σ : Environment → Path u d)
    (hσ : ∀ p, MeasurableSet {ω | σ ω = p}) (L : ℝ) (v : Lattice) :
    Integrable (fun ω : Environment =>
      (if v ∈ (σ ω).collectedSites then (1 : ℝ) else 0) * max (-L - ω v) 0)
      (environmentLaw μ) := by
  classical
  have hW : Integrable (fun ω : Environment => max (-L - ω v) 0)
      (environmentLaw μ) :=
    ((integrable_const (-L)).sub (integrable_environment_eval μ hμ v)).sup
      (integrable_zero _ _ _)
  have hI : Measurable (fun ω : Environment =>
      if v ∈ (σ ω).collectedSites then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_selected_path_membership σ hσ v)
      measurable_const measurable_const
  exact hW.bdd_mul (c := 1) hI.aestronglyMeasurable (ae_of_all _ fun ω => by
    split_ifs <;> norm_num)

/-- Integrating the actual selected-path comparison is legitimate with only a
first marginal moment. Every term is produced from the same selector. -/
theorem integral_clipped_sub_le_sum_selected_negative_remainder
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) (d : ℕ × ℕ)
    (σ : Environment → Path 0 d)
    (hfiber : ∀ p, MeasurableSet {ω | σ ω = p})
    (hmax : ∀ ω, pathWeight (fun v => max (-L) (min L (ω v))) (σ ω) =
      lastPassage (fun v => max (-L) (min L (ω v))) 0 d) :
    (∫ ω : Environment, lastPassage (fun v => max (-L) (min L (ω v))) 0 d
      ∂environmentLaw μ) -
      (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
      ∑ v ∈ (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (d.2 : ℤ)),
        ∫ ω : Environment,
          (if v ∈ (σ ω).collectedSites then (1 : ℝ) else 0) * max (-L - ω v) 0
          ∂environmentLaw μ := by
  classical
  let s := (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (d.2 : ℤ))
  let R : Lattice → Environment → ℝ := fun v ω =>
    (if v ∈ (σ ω).collectedSites then 1 else 0) * max (-L - ω v) 0
  have hR (v : Lattice) : Integrable (R v) (environmentLaw μ) :=
    integrable_selected_negative_remainder μ hμ σ hfiber L v
  have hsum : Integrable (fun ω => ∑ v ∈ s, R v ω) (environmentLaw μ) :=
    integrable_finsetSum s (fun v _ => hR v)
  have hpoint (ω : Environment) :
      lastPassage (fun v => max (-L) (min L (ω v))) 0 d - lastPassage ω 0 d ≤
        ∑ v ∈ s, R v ω := by
    have heq : (∑ v ∈ s, R v ω) = ∑ v ∈ (σ ω).collectedSites, max (-L - ω v) 0 := by
      simpa only [s, R, ite_mul, one_mul, zero_mul] using
        (σ ω).sum_endpoint_rectangle_indicator (fun v => max (-L - ω v) 0)
    rw [heq]
    exact lastPassage_clipped_sub_le_selected_negative_remainder ω d L (σ ω) (hmax ω)
  calc
    _ = ∫ ω : Environment,
        lastPassage (fun v => max (-L) (min L (ω v))) 0 d - lastPassage ω 0 d
        ∂environmentLaw μ :=
      (integral_sub (integrable_clipped_lastPassage μ hμ L 0 d)
        (integrable_lastPassage μ hμ 0 d)).symm
    _ ≤ ∫ ω : Environment, ∑ v ∈ s, R v ω ∂environmentLaw μ :=
      integral_mono ((integrable_clipped_lastPassage μ hμ L 0 d).sub
        (integrable_lastPassage μ hμ 0 d)) hsum hpoint
    _ = _ := integral_finsetSum s (fun v _ => hR v)

/-- The canonical fresh-coordinate coupling turns the product covariance inequality into the
selected-site residual estimate. -/
theorem integral_selected_negative_remainder_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {d : ℕ × ℕ}
    (σ : Environment → Path 0 d)
    (hfiber : ∀ p, MeasurableSet {ω | σ ω = p})
    (hmono : ∀ v ω, Monotone (fun t : ℝ =>
      if v ∈ (σ (Function.update ω v t)).collectedSites then (1 : ℝ) else 0))
    (L : ℝ) (v : Lattice) :
    (∫ ω : Environment,
      (if v ∈ (σ ω).collectedSites then (1 : ℝ) else 0) * max (-L - ω v) 0
      ∂environmentLaw μ) ≤
      (∫ ω : Environment,
        (if v ∈ (σ ω).collectedSites then (1 : ℝ) else 0) ∂environmentLaw μ) *
        (∫ x : ℝ, max (-L - x) 0 ∂μ) := by
  classical
  let I : Environment → ℝ := fun ω => if v ∈ (σ ω).collectedSites then 1 else 0
  let f : ℝ × Environment → ℝ := fun p => I (Function.update p.2 v p.1)
  let W : ℝ → ℝ := fun x => max (-L - x) 0
  have hI : Measurable I :=
    Measurable.ite (measurableSet_selected_path_membership σ hfiber v)
      measurable_const measurable_const
  have hW : Antitone W := by
    intro x y hxy
    exact max_le_max (sub_le_sub_left hxy (-L)) le_rfl
  have hcov := integrable_and_integral_mul_le_mul_integrals_of_monotone_antitone_prod
    (μ := μ) (ν := environmentLaw μ) (f := f) (W := W)
    (measurable_selected_path_update_indicator σ hfiber v)
    (fun x ω => by dsimp only [f, I]; split_ifs <;> norm_num)
    (fun x ω => by dsimp only [f, I]; split_ifs <;> norm_num)
    (fun ω => hmono v ω) hW (integrable_sparseMinimum_residual μ hμ L)
  have hWmeas : Measurable (fun ω : Environment => W (ω v)) := by
    dsimp only [W]
    exact (measurable_const.sub (measurable_environment_eval v)).max measurable_const
  have htransport :
      (∫ p : ℝ × Environment, f p * W p.1 ∂μ.prod (environmentLaw μ)) =
        ∫ ω : Environment, I ω * W (ω v) ∂environmentLaw μ := by
    simpa only [f, Function.update_self] using
      integral_environment_update μ v (fun ω => I ω * W (ω v)) (hI.mul hWmeas)
  have htransportI : (∫ p : ℝ × Environment, f p ∂μ.prod (environmentLaw μ)) =
      ∫ ω : Environment, I ω ∂environmentLaw μ :=
    integral_environment_update μ v I hI
  simpa only [htransport, htransportI, I, W] using hcov.2.2

/-- The finite expected negative clipping error needs only a genuine first
marginal moment. One actual clipped maximizing selector is produced internally
and used for every site; no selector or covariance estimate is a premise. -/
theorem integrable_and_integral_clipped_sub_lastPassage_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (L : ℝ) (_hL : 0 ≤ L) (d : ℕ × ℕ) :
    Integrable (fun ω : Environment => lastPassage ω 0 d) (environmentLaw μ) ∧
    Integrable (fun ω : Environment =>
      lastPassage (fun v => max (-L) (min L (ω v))) 0 d) (environmentLaw μ) ∧
    Integrable (fun x : ℝ => max (-L - x) 0) μ ∧
    (∫ ω : Environment, lastPassage (fun v => max (-L) (min L (ω v))) 0 d
      ∂environmentLaw μ) -
      (∫ ω : Environment, lastPassage ω 0 d ∂environmentLaw μ) ≤
      (d.1 + d.2 : ℕ) * (∫ x : ℝ, max (-L - x) 0 ∂μ) := by
  classical
  refine ⟨integrable_lastPassage μ hμ 0 d, integrable_clipped_lastPassage μ hμ L 0 d,
    integrable_sparseMinimum_residual μ hμ L, ?_⟩
  obtain ⟨σ, hfiber, hmax, hmono, _⟩ :=
    exists_measurable_clipped_maximizing_path_selector 0 d L
  let s := (Finset.Icc (0 : ℤ) (d.1 : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (d.2 : ℤ))
  let I : Lattice → Environment → ℝ := fun v ω =>
    if v ∈ (σ ω).collectedSites then 1 else 0
  have hI (v : Lattice) : Integrable (I v) (environmentLaw μ) := by
    have hm : Measurable (I v) :=
      Measurable.ite (measurableSet_selected_path_membership σ hfiber v)
        measurable_const measurable_const
    exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      dsimp only [I]
      split_ifs <;> norm_num)
  have hcount : (∑ v ∈ s, ∫ ω : Environment, I v ω ∂environmentLaw μ) =
      (d.1 + d.2 : ℕ) := by
    calc
      _ = ∫ ω : Environment, ∑ v ∈ s, I v ω ∂environmentLaw μ :=
        (integral_finsetSum s (fun v _ => hI v)).symm
      _ = ∫ _ω : Environment, ((d.1 + d.2 : ℕ) : ℝ) ∂environmentLaw μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => (σ ω).sum_endpoint_rectangle_membership
      _ = _ := by simp only [integral_const, probReal_univ, one_smul]
  calc
    _ ≤ ∑ v ∈ s, ∫ ω : Environment, I v ω * max (-L - ω v) 0 ∂environmentLaw μ :=
      integral_clipped_sub_le_sum_selected_negative_remainder μ hμ L d σ hfiber hmax
    _ ≤ ∑ v ∈ s, (∫ ω : Environment, I v ω ∂environmentLaw μ) *
        (∫ x : ℝ, max (-L - x) 0 ∂μ) :=
      Finset.sum_le_sum fun v _ =>
        integral_selected_negative_remainder_le μ hμ σ hfiber hmono L v
    _ = (∑ v ∈ s, ∫ ω : Environment, I v ω ∂environmentLaw μ) *
        (∫ x : ℝ, max (-L - x) 0 ∂μ) := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hcount]

end LPPDifferentiability
