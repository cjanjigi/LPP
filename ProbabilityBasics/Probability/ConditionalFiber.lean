/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Conditional fiber witnesses

This module turns positive conditional mass on a set into an actual point of that set on the same
fiber, for almost every observed value.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityBasics

/-- For almost every modified sample, positive conditional mass of `A` gives an actual sample in
`A` with the same value of `phi`. This is the conditional-law witness step in GRS,
arXiv:1510.00860v1, Appendix A, Lemma A.2, lines 1455–1456. -/
theorem ae_exists_mem_eq_of_condDistrib_pos
    {Ω E : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace E] [MeasurableEq E]
    (P : Measure Ω) [IsFiniteMeasure P]
    {phi : Ω → E} (hphi : Measurable phi) (A : Set Ω) :
    ∀ᵐ ω' ∂P,
      0 < ProbabilityTheory.condDistrib id phi P (phi ω') A →
      ∃ ω, ω ∈ A ∧ phi ω = phi ω' := by
  let pair : Ω → E × Ω := fun ω => (phi ω, ω)

  -- The regular conditional law can only charge samples on the measurable graph of `phi`.
  have hgraph_measurable :
      MeasurableSet {z : E × Ω | phi z.2 = z.1} := by
    exact measurableSet_eq_fun (hphi.comp measurable_snd) measurable_fst

  have hpair_measurable : Measurable pair := by
    change Measurable (fun ω : Ω => (phi ω, ω))
    exact hphi.prodMk measurable_id

  -- The actual joint sample law is concentrated on that graph.
  have hgraph_ae :
      ∀ᵐ z ∂P.map pair, phi z.2 = z.1 := by
    exact (MeasureTheory.ae_map_iff hpair_measurable.aemeasurable hgraph_measurable).2
      (Filter.Eventually.of_forall fun ω => rfl)

  -- Identify the graph law with the composition product of the observed law and its conditional law.
  have hjoint_law :
      P.map pair = (P.map phi) ⊗ₘ ProbabilityTheory.condDistrib id phi P := by
    symm
    exact ProbabilityTheory.compProd_map_condDistrib hphi.aemeasurable aemeasurable_id

  -- Disintegration gives conditional concentration on the exact fiber.
  have hfiber :
      ∀ᵐ b ∂P.map phi,
        ∀ᵐ ω ∂ProbabilityTheory.condDistrib id phi P b, phi ω = b := by
    have hjoint :
        ∀ᵐ z ∂(P.map phi ⊗ₘ ProbabilityTheory.condDistrib id phi P),
          phi z.2 = z.1 := by
      rw [← hjoint_law]
      exact hgraph_ae
    exact MeasureTheory.Measure.ae_ae_of_ae_compProd hjoint

  -- Pull the conditional fiber statement back to almost every modified sample.
  have hfiber_pullback :
      ∀ᵐ ω' ∂P,
        ∀ᵐ ω ∂ProbabilityTheory.condDistrib id phi P (phi ω'), phi ω = phi ω' :=
    MeasureTheory.ae_of_ae_map hphi.aemeasurable hfiber

  filter_upwards [hfiber_pullback] with ω' hω'
  intro hpositive
  have hmass_ne_zero :
      ProbabilityTheory.condDistrib id phi P (phi ω') A ≠ 0 := ne_of_gt hpositive
  obtain ⟨ω, hωA, hωfiber⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hmass_ne_zero
      (MeasureTheory.ae_restrict_of_ae hω')
  exact ⟨ω, hωA, hωfiber⟩

end ProbabilityBasics
