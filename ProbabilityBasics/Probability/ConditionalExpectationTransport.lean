/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Conditional expectation transport by an invariant measurable equivalence. -/

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics

/-- A measure-preserving equivalence which preserves the conditioning sigma algebra
commutes with conditional expectation. This is the transport step used for the
conditional projection in JR arXiv:1810.03580v3, (4.20)-(4.21). -/
theorem condExp_comp_measurePreserving {α : Type*} [m₀ : MeasurableSpace α]
    {m : MeasurableSpace α} (hm : m ≤ m₀) (μ : Measure[m₀] α) [IsFiniteMeasure μ]
    (e : @MeasurableEquiv α α m₀ m₀) (he : @MeasurePreserving α α m₀ m₀ (@MeasurableEquiv.toEquiv α α m₀ m₀ e) μ μ)
    (he_m : MeasurableSpace.comap (@MeasurableEquiv.toEquiv α α m₀ m₀ e) m = m) (f : α → ℝ) (hf : Integrable f μ) :
    μ[f ∘ (@MeasurableEquiv.toEquiv α α m₀ m₀ e) | m] =ᵐ[μ] (μ[f | m]) ∘ (@MeasurableEquiv.toEquiv α α m₀ m₀ e) := by
  let : MeasurableSpace α := m₀
  have he_meas : @Measurable α α m m (@MeasurableEquiv.toEquiv α α m₀ m₀ e) :=
    measurable_iff_comap_le.mpr (le_of_eq he_m)
  have he_symm_m : @Measurable α α m m (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm := by
    apply measurable_iff_comap_le.mpr
    apply le_of_eq
    calc
      MeasurableSpace.comap (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm m =
          MeasurableSpace.comap (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm (MeasurableSpace.comap (@MeasurableEquiv.toEquiv α α m₀ m₀ e) m) := congrArg (MeasurableSpace.comap (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm) he_m.symm
      _ = m := by
        rw [MeasurableSpace.comap_comp]
        have hfun : (@MeasurableEquiv.toEquiv α α m₀ m₀ e) ∘ (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm = id := by
          funext x
          exact (@MeasurableEquiv.toEquiv α α m₀ m₀ e).apply_symm_apply x
        rw [hfun, MeasurableSpace.comap_id]
  have hcomp_int : Integrable (f ∘ (@MeasurableEquiv.toEquiv α α m₀ m₀ e)) μ := he.integrable_comp_of_integrable hf
  have hcond_int : Integrable ((μ[f | m]) ∘ (@MeasurableEquiv.toEquiv α α m₀ m₀ e)) μ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hcomp_int
    (fun _ _ _ => hcond_int.integrableOn) ?_ ?_).symm
  · intro s hs _
    let t : Set α := (@MeasurableEquiv.toEquiv α α m₀ m₀ e).symm ⁻¹' s
    have ht : MeasurableSet[m] t := he_symm_m hs
    have hpre : (@MeasurableEquiv.toEquiv α α m₀ m₀ e) ⁻¹' t = s := by
      ext x
      simp only [t, Set.mem_preimage, Equiv.symm_apply_apply]
    calc
      ∫ x in s, (μ[f | m]) ((@MeasurableEquiv.toEquiv α α m₀ m₀ e) x) ∂μ = ∫ x in t, (μ[f | m]) x ∂μ := by
        simpa only [hpre] using he.setIntegral_preimage_emb e.measurableEmbedding (μ[f | m]) t
      _ = ∫ x in t, f x ∂μ := setIntegral_condExp hm hf ht
      _ = ∫ x in s, f ((@MeasurableEquiv.toEquiv α α m₀ m₀ e) x) ∂μ := by
        simpa only [hpre] using (he.setIntegral_preimage_emb e.measurableEmbedding f t).symm
  · exact (stronglyMeasurable_condExp.comp_measurable he_meas).aestronglyMeasurable

end ProbabilityBasics
