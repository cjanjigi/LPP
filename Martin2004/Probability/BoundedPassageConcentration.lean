/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.BoundedEnvironmentCoordinates
public import LPP_Foundations.Probability.PassageMeanBounds
public import LPP_Foundations.Model.LastPassage.AntidiagonalOscillation
public import ProbabilityBasics.Analysis.MartinConcentrationConstants
public import ProbabilityBasics.Probability.FiniteProductConcentration

/-!
# Concentration of the finite passage maximum

The passage maximum is split into independent antidiagonal blocks, each a function of its own
environment values. Changing one block moves the maximum by at most twice the bound on the
weights, so a Hoeffding-type exponential-moment bound applies to the whole maximum. Martin (2004),
Lemma 3.1, uses Talagrand's concentration inequality at this point instead. The bound proved
here has a different constant, which is stronger, and the finite representation below is
private to the proof.
-/

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

private abbrev PassageBox (d : ℕ × ℕ) :=
  {z : Lattice // z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
    z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ)}

private abbrev PassageFiber (d : ℕ × ℕ) (k : Fin (d.1 + d.2)) :=
  {z : PassageBox d // z.val.1 + z.val.2 = (k.val : ℤ)}

private noncomputable instance passageBoxFintype (d : ℕ × ℕ) : Fintype (PassageBox d) :=
  (collected_box_finite d).fintype

private noncomputable instance passageFiberFintype (d : ℕ × ℕ)
    (k : Fin (d.1 + d.2)) : Fintype (PassageFiber d k) := by
  classical
  exact Fintype.ofFinite _

private def passageLevel {d : ℕ × ℕ} (z : PassageBox d) : Fin (d.1 + d.2) :=
  ⟨(z.val.1 + z.val.2).toNat, by
    have hfst : 0 ≤ z.val.1 := z.property.1.1.1
    have hsnd : 0 ≤ z.val.2 := z.property.1.1.2
    have hlt := z.property.2
    omega⟩

private theorem passageLevel_eq {d : ℕ × ℕ} (z : PassageBox d) :
    z.val.1 + z.val.2 = ((passageLevel z).val : ℤ) := by
  have hfst : 0 ≤ z.val.1 := z.property.1.1.1
  have hsnd : 0 ≤ z.val.2 := z.property.1.1.2
  dsimp [passageLevel]
  omega

private def passageSite {d : ℕ × ℕ} (p : Sigma (PassageFiber d)) : Lattice :=
  p.2.val.val

private theorem passageSite_injective (d : ℕ × ℕ) :
    Function.Injective (passageSite (d := d)) := by
  intro ⟨k, z⟩ ⟨j, w⟩ h
  have hk := z.property
  have hj := w.property
  have hsum := congrArg (fun v : Lattice => v.1 + v.2) h
  have hkj : k = j := Fin.ext (by dsimp [passageSite] at hsum; omega)
  subst j
  have hzw : z = w := Subtype.ext (Subtype.ext h)
  subst w
  rfl

private abbrev PassageBlocks (d : ℕ × ℕ) (L : ℝ) :=
  (k : Fin (d.1 + d.2)) → PassageFiber d k → Set.Icc (-L) L

private noncomputable def passageReconstruct (d : ℕ × ℕ) (L : ℝ)
    (q : PassageBlocks d L) : Environment := by
  classical
  exact fun z => if hz : z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ) then
    (q (passageLevel ⟨z, hz⟩) ⟨⟨z, hz⟩, passageLevel_eq ⟨z, hz⟩⟩).val else 0

private theorem measurable_passageReconstruct (d : ℕ × ℕ) (L : ℝ) :
    Measurable (passageReconstruct d L) := by
  classical
  apply measurable_pi_iff.mpr
  intro z
  by_cases hz : z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ)
  · simp only [passageReconstruct, dite_eq_left hz]
    exact measurable_subtype_coe.comp
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [passageReconstruct, dite_eq_right hz]
    exact measurable_const

private theorem abs_passageReconstruct_le (d : ℕ × ℕ) {L : ℝ} (hL : 0 ≤ L)
    (q : PassageBlocks d L) (z : Lattice) : |passageReconstruct d L q z| ≤ L := by
  classical
  unfold passageReconstruct
  split_ifs with hz
  · exact abs_le.mpr (q _ _).property
  · simpa only [abs_zero] using hL

private noncomputable def passageBlockMaximum (d : ℕ × ℕ) (L : ℝ)
    (q : PassageBlocks d L) : ℝ := lastPassage (passageReconstruct d L q) 0 d

private theorem measurable_passageBlockMaximum (d : ℕ × ℕ) (L : ℝ) :
    Measurable (passageBlockMaximum d L) :=
  (measurable_lastPassage 0 d).comp (measurable_passageReconstruct d L)

private theorem abs_passageBlockMaximum_le (d : ℕ × ℕ) {L : ℝ} (hL : 0 ≤ L)
    (q : PassageBlocks d L) : |passageBlockMaximum d L q| ≤ (d.1 + d.2 : ℕ) * L :=
  lastPassage_abs_le _ 0 d L (abs_passageReconstruct_le d hL q)

private theorem abs_passageBlockMaximum_sub_le (d : ℕ × ℕ) {L : ℝ} (hL : 0 ≤ L)
    (q r : PassageBlocks d L) (k : Fin (d.1 + d.2))
    (hqr : ∀ j, j ≠ k → q j = r j) :
    |passageBlockMaximum d L q - passageBlockMaximum d L r| ≤ 2 * L := by
  classical
  apply abs_lastPassage_sub_le_two_mul
    (abs_passageReconstruct_le d hL q) (abs_passageReconstruct_le d hL r) k
  intro z hz
  by_cases hb : z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ)
  · have hne : passageLevel (d := d) ⟨z, hb⟩ ≠ k := by
      intro heq
      apply hz
      exact (passageLevel_eq ⟨z, hb⟩).trans (congrArg (fun i => (i.val : ℤ)) heq)
    simp only [passageReconstruct, dite_eq_left hb]
    rw [hqr _ hne]
  · simp only [passageReconstruct, dite_eq_right hb]

private noncomputable def actualPassageBlocks (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L)
    (ω : Environment) : PassageBlocks d L :=
  fun k i => Set.projIcc (-L) L (neg_le_self hL) (ω (passageSite ⟨k, i⟩))

private theorem measurable_actualPassageBlocks (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    Measurable (actualPassageBlocks d L hL) :=
  measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun i =>
    (measurable_bounded_coordinate L hL).comp (measurable_environment_eval (passageSite ⟨k, i⟩))

private theorem actualPassageBlocks_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (environmentLaw μ).map (actualPassageBlocks d L hL) =
      Measure.pi (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
        μ.map (Set.projIcc (-L) L (neg_le_self hL)))) :=
  environmentLaw_map_finite_bounded_blocks μ L hL passageSite (passageSite_injective d)

private theorem ae_actualPassageBlocks_maximum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ᵐ x ∂μ, |x| ≤ L) :
    ∀ᵐ ω ∂environmentLaw μ,
      passageBlockMaximum d L (actualPassageBlocks d L hL ω) = lastPassage ω 0 d := by
  have hcoords : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, |ω z| ≤ L := by
    rw [ae_all_iff]
    intro z
    have hmap : ∀ᵐ x ∂(environmentLaw μ).map (fun ω : Environment => ω z), |x| ≤ L := by
      rw [environmentLaw_map_eval]
      exact hbound
    exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hmap
  filter_upwards [hcoords] with ω hω
  apply lastPassage_eq_of_eqOn_collected_box
  intro z hz hl
  dsimp only [passageReconstruct, actualPassageBlocks, passageSite]
  simp only [dite_eq_left (show z ∈ Set.Icc (0 : Lattice) ((d.1 : ℤ), (d.2 : ℤ)) ∧
      z.1 + z.2 < ((d.1 + d.2 : ℕ) : ℤ) from ⟨hz, hl⟩)]
  exact congrArg Subtype.val (Set.projIcc_of_mem (neg_le_self hL) (abs_le.mp (hω z)))

private theorem integrable_passageBlockMaximum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    Integrable (passageBlockMaximum d L)
      (Measure.pi (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
        μ.map (Set.projIcc (-L) L (neg_le_self hL))))) := by
  refine (integrable_const ((d.1 + d.2 : ℕ) * L)).mono'
    (measurable_passageBlockMaximum d L).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using abs_passageBlockMaximum_le d hL q

private theorem integral_passageBlocks_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ᵐ x ∂μ, |x| ≤ L) :
    (∫ ω, lastPassage ω 0 d ∂environmentLaw μ) =
      ∫ q, passageBlockMaximum d L q
        ∂Measure.pi (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
          μ.map (Set.projIcc (-L) L (neg_le_self hL)))) := by
  have hT := integrable_lastPassage_of_ae_abs_le μ L hbound 0 d
  have hcomp : Integrable (fun ω => passageBlockMaximum d L (actualPassageBlocks d L hL ω))
      (environmentLaw μ) := by
    apply (integrable_map_measure
      (measurable_passageBlockMaximum d L).aestronglyMeasurable
      (measurable_actualPassageBlocks d L hL).aemeasurable).mp
    rw [actualPassageBlocks_law μ d L hL]
    exact integrable_passageBlockMaximum μ d L hL
  have hzero : (fun ω => lastPassage ω 0 d - passageBlockMaximum d L
      (actualPassageBlocks d L hL ω)) =ᵐ[environmentLaw μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_actualPassageBlocks_maximum μ d L hL hbound] with ω hω
    rw [hω, sub_self]
  have hdiff := integral_congr_ae hzero
  rw [integral_sub hT hcomp, integral_zero] at hdiff
  calc
    _ = ∫ ω, passageBlockMaximum d L (actualPassageBlocks d L hL ω) ∂environmentLaw μ :=
      sub_eq_zero.mp hdiff
    _ = _ := integral_finite_bounded_environment_blocks μ L hL passageSite
      (passageSite_injective d) _ (measurable_passageBlockMaximum d L)

private theorem measure_centered_passageBlocks_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ᵐ x ∂μ, |x| ≤ L) (u : ℝ) :
    (environmentLaw μ).real {ω : Environment |
      u ≤ |lastPassage ω 0 d - ∫ η, lastPassage η 0 d ∂environmentLaw μ|} =
    (Measure.pi (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
      μ.map (Set.projIcc (-L) L (neg_le_self hL))))).real
      {q | u ≤ |passageBlockMaximum d L q -
        ∫ r, passageBlockMaximum d L r
          ∂Measure.pi (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
            μ.map (Set.projIcc (-L) L (neg_le_self hL))))|} := by
  rw [← integral_passageBlocks_eq μ d L hL hbound]
  calc
    _ = (environmentLaw μ).real {ω : Environment |
        u ≤ |passageBlockMaximum d L (actualPassageBlocks d L hL ω) -
          ∫ η, lastPassage η 0 d ∂environmentLaw μ|} := by
      apply measureReal_congr
      filter_upwards [ae_actualPassageBlocks_maximum μ d L hL hbound] with ω hω
      simp only [hω]
    _ = _ := by
      rw [← actualPassageBlocks_law μ d L hL]
      exact (map_measureReal_apply (measurable_actualPassageBlocks d L hL)
        (measurableSet_le measurable_const
          (by simpa only [Real.norm_eq_abs] using
            ((measurable_passageBlockMaximum d L).sub_const
              (∫ η, lastPassage η 0 d ∂environmentLaw μ)).norm))).symm

/-- A zero-length actual passage has zero probability of a positive centered deviation. -/
public theorem measure_abs_lastPassage_sub_integral_ge_eq_zero_of_length_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ × ℕ)
    (hd : d.1 + d.2 = 0) {u : ℝ} (hu : 0 < u) :
    (environmentLaw μ).real {ω : Environment |
      u ≤ |lastPassage ω 0 d - ∫ η, lastPassage η 0 d ∂environmentLaw μ|} = 0 := by
  have hd0 : d = (0, 0) := Prod.ext (by omega) (by omega)
  subst d
  simp only [lastPassage_zero, integral_zero, sub_self, abs_zero,
    not_le.mpr hu, Set.ofPred_false, measureReal_empty]

/-- A marginal with zero AE absolute bound has no positive centered passage tail. -/
public theorem measure_abs_lastPassage_sub_integral_ge_eq_zero_of_bound_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ × ℕ)
    (hbound : ∀ᵐ x ∂μ, |x| ≤ 0) {u : ℝ} (hu : 0 < u) :
    (environmentLaw μ).real {ω : Environment |
      u ≤ |lastPassage ω 0 d - ∫ η, lastPassage η 0 d ∂environmentLaw μ|} = 0 := by
  have hcoords : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice, |ω z| ≤ 0 := by
    rw [ae_all_iff]
    intro z
    have hmap : ∀ᵐ x ∂(environmentLaw μ).map (fun ω : Environment => ω z), |x| ≤ 0 := by
      rw [environmentLaw_map_eval]
      exact hbound
    exact ae_of_ae_map (measurable_environment_eval z).aemeasurable hmap
  have hT : (fun ω : Environment => lastPassage ω 0 d) =ᵐ[environmentLaw μ]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hcoords] with ω hω
    have hb := lastPassage_abs_le ω 0 d 0 hω
    rw [mul_zero] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have hmean : (∫ η, lastPassage η 0 d ∂environmentLaw μ) = 0 := by
    rw [integral_congr_ae hT, integral_zero]
  rw [hmean]
  calc
    _ = (environmentLaw μ).real (∅ : Set Environment) := by
      apply measureReal_congr
      filter_upwards [hT] with ω hω
      simp only [hω, sub_zero, abs_zero, not_le.mpr hu, Set.mem_empty_iff_false]
    _ = 0 := measureReal_empty

/-- The actual centered passage maximum has the stronger antidiagonal Hoeffding tail. -/
public theorem measure_abs_lastPassage_sub_integral_ge_le_two_mul_exp
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ × ℕ) (L : ℝ) (hL : 0 < L)
    (hbound : ∀ᵐ x ∂μ, |x| ≤ L) (hd : 0 < d.1 + d.2) {u : ℝ} (hu : 0 < u) :
    (environmentLaw μ).real {ω : Environment |
      u ≤ |lastPassage ω 0 d - ∫ η, lastPassage η 0 d ∂environmentLaw μ|} ≤
      2 * Real.exp (-u ^ 2 / (8 * (d.1 + d.2 : ℕ) * L ^ 2)) := by
  classical
  rw [measure_centered_passageBlocks_eq μ d L hL.le hbound u]
  apply measure_abs_centered_pi_ge_le_of_oscillation_two_mul
    (M := (d.1 + d.2 : ℕ) * L)
    (fun k : Fin (d.1 + d.2) => Measure.pi (fun _ : PassageFiber d k =>
      μ.map (Set.projIcc (-L) L (neg_le_self hL.le))))
    (mul_nonneg (Nat.cast_pos.mpr hd).le hL.le) hL.le
    (measurable_passageBlockMaximum d L) (abs_passageBlockMaximum_le d hL.le)
    ?_ hu.le
  intro q k y
  apply abs_passageBlockMaximum_sub_le d hL.le (Function.update q k y) q k
  intro j hj
  exact Function.update_of_ne hj y q

/-- Martin's exact displayed constant for the actual maximum, centered at its genuine mean. -/
public theorem measure_abs_lastPassage_sub_integral_ge_le_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ × ℕ) (L : ℝ) (hL : 0 < L)
    (hbound : ∀ᵐ x ∂μ, |x| ≤ L) (hd : 0 < d.1 + d.2) {u : ℝ} (hu : 0 < u) :
    (environmentLaw μ).real {ω : Environment |
      u ≤ |lastPassage ω 0 d - ∫ η, lastPassage η 0 d ∂environmentLaw μ|} ≤
      Real.exp (64 - u ^ 2 / (64 * (d.1 + d.2 : ℕ) * L ^ 2)) :=
  (measure_abs_lastPassage_sub_integral_ge_le_two_mul_exp μ d L hL hbound hd hu).trans
    (two_mul_exp_neg_u_sq_div_eight_n_l_sq_le_exp_sixty_four_sub_u_sq_div_sixty_four_n_l_sq
      (d.1 + d.2) hd L hL u)

end LPPDifferentiability
