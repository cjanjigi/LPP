/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.DisjointSupport
public import LPP_Foundations.Probability.TranslationEquiv
import Mathlib.Tactic

/-!
# Events determined by the weights on disjoint finite sets of sites

An event is determined by the weights on a finite set `S` when two
environments that agree on `S` lie in the event together. Measurable events of
this kind, attached to pairwise disjoint finite sets, form an independent
family under the canonical iid law. The second result applies this to
translated copies of one such event.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- Extension by zero of a weight vector on a finite set of sites. -/
private def extendZero (S : Finset Lattice) (x : {z : Lattice // z ∈ S} → ℝ) :
    Environment := fun z => if h : z ∈ S then x ⟨z, h⟩ else 0

private theorem measurable_extendZero (S : Finset Lattice) :
    Measurable (extendZero S) := by
  refine Measurable.of_eval fun z => ?_
  by_cases h : z ∈ S
  · simp only [extendZero, dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [extendZero, dite_eq_right h]
    exact measurable_const

/-- An event determined by the weights on `S` is a preimage under the
restriction to `S`. -/
private theorem eq_preimage_restrict_of_local (S : Finset Lattice)
    (A : Set Environment)
    (hloc : ∀ ω ω' : Environment, (∀ z ∈ S, ω z = ω' z) → (ω ∈ A ↔ ω' ∈ A)) :
    A = (fun ω : Environment => fun s : {z : Lattice // z ∈ S} => ω s.val) ⁻¹'
      (extendZero S ⁻¹' A) := by
  ext ω
  show ω ∈ A ↔ extendZero S (fun s : {z : Lattice // z ∈ S} => ω s.val) ∈ A
  refine hloc ω _ fun z hz => ?_
  simp [extendZero, hz]

/-- Measurable events determined by the weights on pairwise disjoint finite
sets of sites are independent under the canonical iid law. -/
theorem iIndepSet_environment_of_disjoint_supports
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ι : Type*}
    (A : ι → Set Environment) (S : ι → Finset Lattice)
    (hA : ∀ i, MeasurableSet (A i))
    (hloc : ∀ i (ω ω' : Environment), (∀ z ∈ S i, ω z = ω' z) →
      (ω ∈ A i ↔ ω' ∈ A i))
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet A (environmentLaw μ) := by
  classical
  rw [iIndepSet_iff_meas_biInter hA]
  intro J
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    rw [Finset.prod_insert hj, ← ih, Finset.set_biInter_insert]
    have hdisj : Disjoint (S j) (J.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      refine hS ?_
      rintro rfl
      exact hj hi
    have hlocB : ∀ ω ω' : Environment, (∀ z ∈ J.biUnion S, ω z = ω' z) →
        (ω ∈ ⋂ i ∈ J, A i ↔ ω' ∈ ⋂ i ∈ J, A i) := by
      intro ω ω' h
      simp only [Set.mem_iInter]
      refine forall_congr' fun i => forall_congr' fun hi => hloc i ω ω' fun z hz => ?_
      exact h z (Finset.mem_biUnion.mpr ⟨i, hi, hz⟩)
    have hBm : MeasurableSet (⋂ i ∈ J, A i) :=
      Finset.measurableSet_biInter J fun i _ => hA i
    have key := environmentLaw_restrict_inter μ (S j) (J.biUnion S) hdisj
      (extendZero (S j) ⁻¹' A j) (extendZero (J.biUnion S) ⁻¹' ⋂ i ∈ J, A i)
      (measurable_extendZero _ (hA j)) (measurable_extendZero _ hBm)
    rwa [← eq_preimage_restrict_of_local (S j) (A j) (hloc j),
      ← eq_preimage_restrict_of_local (J.biUnion S) _ hlocB] at key

/-- Translated copies of one measurable event determined by the weights on
`K`, with pairwise disjoint translated supports, all fail with probability
exactly `(1 - P E)^N`. -/
theorem environmentLaw_iInter_translate_compl
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set Environment) (K : Finset Lattice) (hE : MeasurableSet E)
    (hloc : ∀ ω ω' : Environment, (∀ z ∈ K, ω z = ω' z) → (ω ∈ E ↔ ω' ∈ E))
    (N : ℕ) (c : Fin N → Lattice)
    (hdisj : Pairwise fun i j => Disjoint (K.map (addLeftEmbedding (c i)))
      (K.map (addLeftEmbedding (c j)))) :
    (environmentLaw μ).real
        (⋂ j, ((environmentTranslationEquiv (c j)) ⁻¹' E)ᶜ) =
      (1 - (environmentLaw μ).real E) ^ N := by
  classical
  let A : Fin N → Set Environment := fun j =>
    ((environmentTranslationEquiv (c j)) ⁻¹' E)ᶜ
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    ((environmentTranslationEquiv (c j)).measurable hE).compl
  have hAloc : ∀ j (ω ω' : Environment),
      (∀ z ∈ K.map (addLeftEmbedding (c j)), ω z = ω' z) →
        (ω ∈ A j ↔ ω' ∈ A j) := by
    intro j ω ω' h
    have h' : environmentTranslationEquiv (c j) ω ∈ E ↔
        environmentTranslationEquiv (c j) ω' ∈ E :=
      hloc _ _ fun z hz => h (c j + z) (Finset.mem_map.mpr ⟨z, hz, rfl⟩)
    exact not_congr h'
  have hind := iIndepSet_environment_of_disjoint_supports μ A
    (fun j => K.map (addLeftEmbedding (c j))) hAm hAloc hdisj
  have hprod := hind.meas_biInter Finset.univ
  have hcompl : ∀ j, environmentLaw μ (A j) = 1 - environmentLaw μ E := by
    intro j
    rw [prob_compl_eq_one_sub ((environmentTranslationEquiv (c j)).measurable hE),
      (measurePreserving_environmentTranslationEquiv μ (c j)).measure_preimage_equiv]
  have hiInter : (⋂ j, A j) = ⋂ j ∈ (Finset.univ : Finset (Fin N)), A j := by
    simp
  show (environmentLaw μ).real (⋂ j, A j) = _
  rw [measureReal_def, hiInter, hprod]
  simp only [hcompl, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, measureReal_def]

end LPPDifferentiability
