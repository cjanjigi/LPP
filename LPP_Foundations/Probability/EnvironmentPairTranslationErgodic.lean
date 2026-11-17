/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.TranslationErgodic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Ergodicity of two independent environments under a common shift

The independent input pair is represented as an iid field of pairs of real weights.
Finite cylinders of that field are independent of sufficiently distant translates.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory Function
open scoped ENNReal symmDiff

namespace LPPDifferentiability

private def pairField : Environment × Environment → Lattice → ℝ × ℝ :=
  fun p z => (p.1 z, p.2 z)

private theorem measurable_pairField : Measurable pairField := by
  apply Measurable.of_eval
  intro z
  exact ((measurable_environment_eval z).comp measurable_fst).prodMk
    ((measurable_environment_eval z).comp measurable_snd)

private def unpairField : (Lattice → ℝ × ℝ) → Environment × Environment :=
  fun x => (fun z => (x z).1, fun z => (x z).2)

private theorem measurable_unpairField : Measurable unpairField := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro z
    exact measurable_fst.comp (measurable_pi_apply z)
  · apply Measurable.of_eval
    intro z
    exact measurable_snd.comp (measurable_pi_apply z)

private theorem pairField_law (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map pairField =
      Measure.infinitePi (fun _ : Lattice => μ.prod μ) := by
  classical
  apply Measure.eq_infinitePi
  intro S t ht
  let r : Environment → ({z : Lattice // z ∈ S} → ℝ) := S.restrict
  let q : Environment × Environment →
      (({z : Lattice // z ∈ S} → ℝ) × ({z : Lattice // z ∈ S} → ℝ)) :=
    Prod.map r r
  let E := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ S
  have hr : Measurable r := Measurable.of_eval (fun z => measurable_pi_apply z.val)
  have hq : Measurable q := hr.prodMap hr
  have hqLaw : ((environmentLaw μ).prod (environmentLaw μ)).map q =
      (Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ)).prod
        (Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ)) := by
    rw [← Measure.map_prod_map (environmentLaw μ) (environmentLaw μ) hr hr]
    simp only [r, environmentLaw, Measure.infinitePi_map_restrict]
  have hELaw :
      ((Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ)).prod
        (Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ))).map E.symm =
      Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ.prod μ) :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ S (fun _ => μ) (fun _ => μ)).symm E
      |>.map_eq
  have hform : (fun p : Environment × Environment => S.restrict (pairField p)) =
      E.symm ∘ q := by
    funext p
    funext z
    rfl
  have hfinite : ((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p => S.restrict (pairField p)) =
      Measure.pi (fun _ : {z : Lattice // z ∈ S} => μ.prod μ) := by
    rw [hform, ← Measure.map_map E.symm.measurable hq, hqLaw]
    exact hELaw
  have hbox : MeasurableSet (Set.pi (↑S) t) :=
    MeasurableSet.pi S.countable_toSet (fun z _ => ht z)
  have hfiniteBox : MeasurableSet
      (Set.pi Set.univ (fun z : {z : Lattice // z ∈ S} => t z.val)) :=
    MeasurableSet.pi countable_univ (fun z _ => ht z.val)
  have hpre : pairField ⁻¹' Set.pi (↑S) t =
      (fun p : Environment × Environment => S.restrict (pairField p)) ⁻¹'
        Set.pi Set.univ (fun z : {z : Lattice // z ∈ S} => t z.val) := by
    ext p
    simp [Set.mem_pi, Finset.restrict]
  rw [Measure.map_apply measurable_pairField hbox, hpre]
  have hfiniteMap : Measurable (fun p : Environment × Environment =>
      S.restrict (pairField p)) :=
    Measurable.of_eval (fun z => (measurable_pi_apply z.val).comp measurable_pairField)
  calc
    _ = (((environmentLaw μ).prod (environmentLaw μ)).map
        (fun p => S.restrict (pairField p)))
        (Set.pi Set.univ (fun z : {z : Lattice // z ∈ S} => t z.val)) :=
      (Measure.map_apply hfiniteMap hfiniteBox).symm
    _ = ∏ z ∈ S, μ.prod μ (t z) := by
      rw [hfinite, Measure.pi_pi]
      exact Finset.prod_attach S (fun z => μ.prod μ (t z))

private theorem iid_pair_shift_preserving (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) :
    MeasurePreserving (fun x : Lattice → ℝ × ℝ => fun z => x (v + z))
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ))
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ)) := by
  have hinj : Function.Injective (fun z : Lattice => v + z) := by
    intro z w h
    exact add_left_cancel h
  refine ⟨Measurable.of_eval (fun z => measurable_pi_apply (v + z)), ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Lattice => μ.prod μ) hinj

private theorem iid_pair_finite_approx (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set (Lattice → ℝ × ℝ)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset Lattice) (B : Set ({z : Lattice // z ∈ S} → ℝ × ℝ)),
      MeasurableSet B ∧
      Measure.infinitePi (fun _ : Lattice => μ.prod μ)
        (A ∆ {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B}) <
        ENNReal.ofReal ε := by
  have hcover : ∃ D : Set (Set (Lattice → ℝ × ℝ)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : Lattice => ℝ × ℝ) ∧
      Measure.infinitePi (fun _ : Lattice => μ.prod μ) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, ?_, ?_⟩
    · exact singleton_subset_iff.mpr (univ_mem_measurableCylinders _)
    · simp only [sUnion_singleton, compl_univ, measure_empty]
  obtain ⟨C, hC, herror⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := Measure.infinitePi (fun _ : Lattice => μ.prod μ))
    isSetRing_measurableCylinders hcover
    generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨S, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  refine ⟨S, B, hB, ?_⟩
  rw [symmDiff_comm] at herror
  exact herror

private theorem iid_pair_cylinder_inter_translation (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (S : Finset Lattice) (v : Lattice)
    (hS : Disjoint S (S.image fun z => v + z))
    (B : Set ({z : Lattice // z ∈ S} → ℝ × ℝ)) (hB : MeasurableSet B) :
    Measure.infinitePi (fun _ : Lattice => μ.prod μ)
      ({x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} ∩
        (fun x : Lattice → ℝ × ℝ => fun z => x (v + z)) ⁻¹'
          {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B}) =
    Measure.infinitePi (fun _ : Lattice => μ.prod μ)
      {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} *
    Measure.infinitePi (fun _ : Lattice => μ.prod μ)
      {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} := by
  classical
  let T := S.image fun z => v + z
  let r : ({z : Lattice // z ∈ T} → ℝ × ℝ) →
      ({z : Lattice // z ∈ S} → ℝ × ℝ) :=
    fun x z => x ⟨v + z.val, Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩
  have hr : Measurable r := measurable_pi_iff.mpr fun z => measurable_pi_apply _
  have hiid : iIndepFun (fun z (x : Lattice → ℝ × ℝ) => x z)
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ)) :=
    iIndepFun_infinitePi (P := fun _ : Lattice => μ.prod μ)
      (X := fun (_ : Lattice) (x : ℝ × ℝ) => x) (fun _ => measurable_id)
  have hind := (iIndepFun.indepFun_finset S T hS hiid
    (fun z => measurable_pi_apply z)).comp measurable_id hr
  have h := hind.measure_inter_preimage_eq_mul B B hB hB
  have hrestrict : Measurable (fun x : Lattice → ℝ × ℝ =>
      fun z : {z : Lattice // z ∈ S} => x z.val) :=
    Measurable.of_eval (fun z => measurable_pi_apply z.val)
  have hm := (iid_pair_shift_preserving μ v).measure_preimage
    ((hB.preimage hrestrict).nullMeasurableSet)
  let C : Set (Lattice → ℝ × ℝ) :=
    {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B}
  change Measure.infinitePi (fun _ : Lattice => μ.prod μ)
      (C ∩ (fun x : Lattice → ℝ × ℝ => fun z => x (v + z)) ⁻¹' C) =
    Measure.infinitePi (fun _ : Lattice => μ.prod μ) C *
      Measure.infinitePi (fun _ : Lattice => μ.prod μ)
        ((fun x : Lattice → ℝ × ℝ => fun z => x (v + z)) ⁻¹' C) at h
  change Measure.infinitePi (fun _ : Lattice => μ.prod μ)
      ((fun x : Lattice → ℝ × ℝ => fun z => x (v + z)) ⁻¹' C) =
    Measure.infinitePi (fun _ : Lattice => μ.prod μ) C at hm
  rw [hm] at h
  exact h

private theorem iid_pair_cylinder_inter_iterate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (hv : v ≠ 0) (S : Finset Lattice)
    (B : Set ({z : Lattice // z ∈ S} → ℝ × ℝ)) (hB : MeasurableSet B) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Measure.infinitePi (fun _ : Lattice => μ.prod μ)
        ({x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} ∩
          (fun x : Lattice → ℝ × ℝ => fun z => x (v + z))^[n] ⁻¹'
            {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B}) =
      Measure.infinitePi (fun _ : Lattice => μ.prod μ)
        {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} *
      Measure.infinitePi (fun _ : Lattice => μ.prod μ)
        {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B} := by
  filter_upwards [eventually_disjoint_finite_translates v hv S S] with n hn
  have hiter (x : Lattice → ℝ × ℝ) (m : ℕ) (z : Lattice) :
      ((fun x : Lattice → ℝ × ℝ => fun z => x (v + z))^[m] x) z =
        x (m • v + z) := by
    induction m generalizing z with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        change ((fun x : Lattice → ℝ × ℝ => fun z => x (v + z))^[m] x) (v + z) =
          x (Nat.succ m • v + z)
        calc
          _ = x (m • v + (v + z)) := ih (v + z)
          _ = x ((m • v + v) + z) := by rw [add_assoc]
          _ = x ((m + 1) • v + z) := by rw [← succ_nsmul]
          _ = x (Nat.succ m • v + z) := by rw [Nat.succ_eq_add_one]
  have heq : (fun x : Lattice → ℝ × ℝ => fun z => x (v + z))^[n] =
      (fun x : Lattice → ℝ × ℝ => fun z => x (n • v + z)) := by
    funext x z
    exact hiter x n z
  rw [heq]
  exact iid_pair_cylinder_inter_translation μ S (n • v) hn B hB

private theorem iid_pair_invariant_zero_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (hv : v ≠ 0) {A : Set (Lattice → ℝ × ℝ)} (hA : MeasurableSet A)
    (hinv : (fun x : Lattice → ℝ × ℝ => fun z => x (v + z)) ⁻¹' A = A) :
    Measure.infinitePi (fun _ : Lattice => μ.prod μ) A = 0 ∨
      Measure.infinitePi (fun _ : Lattice => μ.prod μ) A = 1 := by
  let ρ : Measure (Lattice → ℝ × ℝ) := Measure.infinitePi (fun _ => μ.prod μ)
  let f : (Lattice → ℝ × ℝ) → (Lattice → ℝ × ℝ) := fun x z => x (v + z)
  have hf : MeasurePreserving f ρ ρ := iid_pair_shift_preserving μ v
  have ha0 : 0 ≤ ρ.real A := measureReal_nonneg
  have ha1 : ρ.real A ≤ 1 := measureReal_le_one
  have hsquare : ρ.real A = ρ.real A * ρ.real A := by
    have hlow : ρ.real A * ρ.real A ≤ ρ.real A := by nlinarith only [ha0, ha1]
    apply le_antisymm ?_ hlow
    by_contra! hgap
    let δ : ℝ := (ρ.real A - ρ.real A * ρ.real A) / 8
    have hδ : 0 < δ := by dsimp [δ]; linarith only [hgap]
    obtain ⟨S, B, hB, herr⟩ := iid_pair_finite_approx μ hA hδ
    let C : Set (Lattice → ℝ × ℝ) :=
      {x | (fun z : {z : Lattice // z ∈ S} => x z.val) ∈ B}
    have hrestrict : Measurable (fun x : Lattice → ℝ × ℝ =>
        fun z : {z : Lattice // z ∈ S} => x z.val) :=
      Measurable.of_eval (fun z => measurable_pi_apply z.val)
    have hC : MeasurableSet C := hB.preimage hrestrict
    have he : ρ.real (A ∆ C) < δ := by
      have h := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top herr
      simpa only [measureReal_def, ρ, C, ENNReal.toReal_ofReal (le_of_lt hδ)] using h
    obtain ⟨n, hn⟩ := (iid_pair_cylinder_inter_iterate μ v hv S B hB).exists
    have hfn := hf.iterate n
    have hAn : f^[n] ⁻¹' A = A := Function.IsFixedPt.preimage_iterate hinv n
    have hCn : MeasurableSet (f^[n] ⁻¹' C) := hC.preimage hfn.measurable
    have hprod : ρ.real (C ∩ f^[n] ⁻¹' C) = ρ.real C * ρ.real C := by
      change (Measure.infinitePi (fun _ : Lattice => μ.prod μ) (C ∩ f^[n] ⁻¹' C)).toReal =
        (Measure.infinitePi (fun _ : Lattice => μ.prod μ) C).toReal *
        (Measure.infinitePi (fun _ : Lattice => μ.prod μ) C).toReal
      rw [hn, ENNReal.toReal_mul]
    have hsubset : A ∆ (C ∩ f^[n] ⁻¹' C) ⊆
        (A ∆ C) ∪ f^[n] ⁻¹' (A ∆ C) := by
      rw [preimage_symmDiff, hAn]
      intro x hx
      simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
      tauto
    have herror : ρ.real (A ∆ (C ∩ f^[n] ⁻¹' C)) ≤ 2 * ρ.real (A ∆ C) := by
      calc
        _ ≤ ρ.real ((A ∆ C) ∪ f^[n] ⁻¹' (A ∆ C)) := measureReal_mono hsubset
        _ ≤ ρ.real (A ∆ C) + ρ.real (f^[n] ⁻¹' (A ∆ C)) := measureReal_union_le _ _
        _ = 2 * ρ.real (A ∆ C) := by
          rw [hfn.measureReal_preimage (hA.symmDiff hC).nullMeasurableSet]
          ring
    have hcompare := abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet (hC.inter hCn).nullMeasurableSet (μ := ρ)
    have habs := abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hC.nullMeasurableSet (μ := ρ)
    have hac : |ρ.real A - ρ.real C| < δ := lt_of_le_of_lt habs he
    have hc0 : 0 ≤ ρ.real C := measureReal_nonneg
    have hc1 : ρ.real C ≤ 1 := measureReal_le_one
    have hc_square : ρ.real C * ρ.real C ≤ ρ.real A * ρ.real A + 2 * δ := by
      by_cases hca : ρ.real C ≤ ρ.real A
      · have h := mul_self_le_mul_self hc0 hca
        nlinarith only [h, hδ]
      · have hd : ρ.real C - ρ.real A ≤ δ := by
          have := (abs_lt.mp hac).1
          linarith only [this]
        have hsum : ρ.real C + ρ.real A ≤ 2 := by linarith only [hc1, ha1]
        have hmul := mul_le_mul hd hsum (by positivity : 0 ≤ ρ.real C + ρ.real A)
          (le_of_lt hδ)
        nlinarith only [hmul]
    have hcmp : ρ.real A ≤ ρ.real C * ρ.real C + 2 * ρ.real (A ∆ C) := by
      have hh := (abs_le.mp hcompare).2
      rw [hprod] at hh
      linarith only [hh, herror]
    dsimp [δ] at hc_square he
    linarith only [hcmp, hc_square, he, hgap]
  have hcases : ρ.real A = 0 ∨ ρ.real A = 1 := by
    have hmul : ρ.real A * (ρ.real A - 1) = 0 := by nlinarith only [hsquare]
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hcases with h | h
  · exact Or.inl ((measureReal_eq_zero_iff).mp h)
  · exact Or.inr ((ENNReal.toReal_eq_one_iff _).mp h)

private theorem iid_pair_shift_ergodic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : Lattice) (hv : v ≠ 0) :
    Ergodic (fun x : Lattice → ℝ × ℝ => fun z => x (v + z))
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ)) := by
  refine ⟨iid_pair_shift_preserving μ v, ⟨?_⟩⟩
  intro A hA hinv
  rw [eventuallyEmptyOrUniv_iff]
  rcases iid_pair_invariant_zero_one μ v hv hA hinv with h | h
  · exact Or.inr (compl_mem_ae_iff.mpr h)
  · exact Or.inl ((mem_ae_iff_prob_eq_one hA).mpr h)

/-- Two independent canonical environments are ergodic under their simultaneous
horizontal translation. -/
theorem ergodic_independent_environment_pair_horizontal_translation
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Ergodic
      (fun p : Environment × Environment =>
        (fun z : Lattice => p.1 (((1 : ℤ), (0 : ℤ)) + z),
         fun z : Lattice => p.2 (((1 : ℤ), (0 : ℤ)) + z)))
      ((environmentLaw μ).prod (environmentLaw μ)) := by
  let v : Lattice := ((1 : ℤ), (0 : ℤ))
  have hv : v ≠ 0 := by decide
  let f : (Lattice → ℝ × ℝ) → (Lattice → ℝ × ℝ) := fun x z => x (v + z)
  let g : Environment × Environment → Environment × Environment :=
    fun p => (fun z => p.1 (v + z), fun z => p.2 (v + z))
  have hf : Ergodic f (Measure.infinitePi (fun _ : Lattice => μ.prod μ)) :=
    iid_pair_shift_ergodic μ v hv
  have hpair : MeasurePreserving pairField
      ((environmentLaw μ).prod (environmentLaw μ))
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ)) :=
    ⟨measurable_pairField, pairField_law μ⟩
  have hunpair : MeasurePreserving unpairField
      (Measure.infinitePi (fun _ : Lattice => μ.prod μ))
      ((environmentLaw μ).prod (environmentLaw μ)) := by
    refine ⟨measurable_unpairField, ?_⟩
    rw [← pairField_law μ, Measure.map_map measurable_unpairField measurable_pairField]
    have hleft : unpairField ∘ pairField = id := by
      funext p
      apply Prod.ext <;> funext z <;> rfl
    rw [hleft, Measure.map_id]
  have hcomm : Semiconj unpairField f g := by
    intro x
    apply Prod.ext <;> funext z <;> rfl
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro z
      exact (measurable_pi_apply (v + z)).comp measurable_fst
    · apply Measurable.of_eval
      intro z
      exact (measurable_pi_apply (v + z)).comp measurable_snd
  have hpull : Ergodic g ((environmentLaw μ).prod (environmentLaw μ)) :=
    hunpair.ergodic_of_ergodic_semiconj hf hg hcomm
  exact hpull

end LPPDifferentiability
