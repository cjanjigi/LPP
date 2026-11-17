/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentResamplingVersion
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Intersecting two coordinate versions

For an iid environment, almost-sure versions on two coordinate sets give one
version on their intersection. The original observable itself need not be
measurable in the smaller sigma algebra.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace LPPDifferentiability

-- The named parameter `hgT` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- Under the canonical iid law, two almost-surely equal versions depending on
coordinate sets S and T have one version depending only on their intersection.
This supplies the null-set-sensitive intersection step in public
Strong Existence, line 999. -/
theorem exists_measurable_intersection_version_of_coordinate_versions
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S T : Set Lattice)
    {Z : Type*} [MeasurableSpace Z]
    (f : Environment → Z)
    (gS : (S → ℝ) → Z) (hgS : Measurable gS)
    (hS : ∀ᵐ ω ∂environmentLaw μ,
      f ω = gS (fun z : S => ω z))
    (gT : (T → ℝ) → Z) (hgT : Measurable gT)
    (hT : ∀ᵐ ω ∂environmentLaw μ,
      f ω = gT (fun z : T => ω z)) :
    ∃ g : ((↥(S ∩ T)) → ℝ) → Z, Measurable g ∧
      ∀ᵐ ω ∂environmentLaw μ,
        f ω = g (fun z : ↥(S ∩ T) => ω z) := by
  classical
  let I : Set Lattice := S ∩ T
  let A : Set Lattice := S \ T
  let R : Set Lattice := Aᶜ
  let P₀ : Measure Environment := environmentLaw μ
  let PA : Measure (A → ℝ) := Measure.infinitePi (fun _ : A => μ)
  let PR : Measure (R → ℝ) := Measure.infinitePi (fun _ : R => μ)
  let e : Environment ≃ᵐ (A → ℝ) × (R → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Lattice => ℝ)
      (fun z : Lattice => z ∈ A)

  -- The split-off coordinates and their complement have independent product laws.
  have hAmap : P₀.map (fun ω : Environment => fun z : A => ω z) = PA := by
    change (Measure.infinitePi (fun _ : Lattice => μ)).map A.domRestrict =
      Measure.infinitePi (fun _ : A => μ)
    exact Measure.infinitePi_map_restrict' (fun _ : Lattice => μ) (I := A)
  have hRmap : P₀.map (fun ω : Environment => fun z : R => ω z) = PR := by
    change (Measure.infinitePi (fun _ : Lattice => μ)).map R.domRestrict =
      Measure.infinitePi (fun _ : R => μ)
    exact Measure.infinitePi_map_restrict' (fun _ : Lattice => μ) (I := R)
  have hIndep : IndepFun
      (fun ω : Environment => fun z : A => ω z)
      (fun ω : Environment => fun z : R => ω z) P₀ := by
    exact ProbabilityBasics.indepFun_restrict_of_iIndepFun P₀
      (fun z (ω : Environment) => ω z)
      (iIndepFun_environment_eval μ)
      measurable_environment_eval A R (by
        change Disjoint A Aᶜ
        exact disjoint_compl_right)
  have hSplit : P₀.map e = PA.prod PR := by
    change P₀.map (fun ω : Environment =>
      ((fun z : A => ω z), (fun z : R => ω z))) = PA.prod PR
    rw [hIndep.map_prod_eq_prod_map_map
      (measurable_pi_iff.mpr (fun z : A => measurable_environment_eval z)).aemeasurable
      (measurable_pi_iff.mpr (fun z : R =>
        measurable_environment_eval z)).aemeasurable,
      hAmap, hRmap]

  -- The inverse split returns each original coordinate on its own side.
  have hLeft (p : (A → ℝ) × (R → ℝ)) (z : A) :
      e.symm p z.val = p.1 z := by
    have h := congrFun (congrArg Prod.fst (e.apply_symm_apply p)) z
    exact h
  have hRight (p : (A → ℝ) × (R → ℝ)) (z : R) :
      e.symm p z.val = p.2 z := by
    have h := congrFun (congrArg Prod.snd (e.apply_symm_apply p)) z
    exact h

  -- Every T coordinate lies on the retained side R.
  let restrictT : (R → ℝ) → (T → ℝ) :=
    fun r z => r ⟨z.val, by
      intro hzA
      exact hzA.2 z.property⟩
  let restrictI : (R → ℝ) → (I → ℝ) :=
    fun r z => r ⟨z.val, by
      intro hzA
      exact hzA.2 z.property.2⟩
  let fillS : (A → ℝ) → (I → ℝ) → (S → ℝ) :=
    fun a x z =>
      if hz : z.val ∈ T then
        x ⟨z.val, ⟨z.property, hz⟩⟩
      else
        a ⟨z.val, ⟨z.property, hz⟩⟩

  have hScoords (p : (A → ℝ) × (R → ℝ)) :
      (fun z : S => e.symm p z.val) = fillS p.1 (restrictI p.2) := by
    funext z
    by_cases hz : z.val ∈ T
    · have hnotA : z.val ∉ A := by
        intro hzA
        exact hzA.2 hz
      simpa [fillS, restrictI, hz] using hRight p ⟨z.val, hnotA⟩
    · have hzA : z.val ∈ A := ⟨z.property, hz⟩
      simpa [fillS, hz] using hLeft p ⟨z.val, hzA⟩
  have hTcoords (p : (A → ℝ) × (R → ℝ)) :
      (fun z : T => e.symm p z.val) = restrictT p.2 := by
    funext z
    have hnotA : z.val ∉ A := by
      intro hzA
      exact hzA.2 z.property
    simpa [restrictT] using hRight p ⟨z.val, hnotA⟩

  -- Both versions equal the same original observable almost surely.
  have hVersions : ∀ᵐ ω ∂P₀,
      gS (fun z : S => ω z.val) = gT (fun z : T => ω z.val) := by
    filter_upwards [hS, hT] with ω hs ht
    exact hs.symm.trans ht
  have hProduct : ∀ᵐ p ∂PA.prod PR,
      gS (fillS p.1 (restrictI p.2)) = gT (restrictT p.2) := by
    rw [← hSplit, ← MeasurableEquiv.map_ae e P₀]
    simp only [Filter.eventually_map]
    filter_upwards [hVersions] with ω hω
    calc
      gS (fillS (e ω).1 (restrictI (e ω).2)) =
          gS (fun z : S => e.symm (e ω) z.val) := by
            rw [hScoords]
      _ = gT (fun z : T => e.symm (e ω) z.val) := by
            rw [e.symm_apply_apply]
            exact hω
      _ = gT (restrictT (e ω).2) := by
            rw [hTcoords]

  -- Fubini selects one exclusive S array that works for almost every R array.
  have hSections : ∀ᵐ a ∂PA, ∀ᵐ r ∂PR,
      gS (fillS a (restrictI r)) = gT (restrictT r) :=
    Measure.ae_ae_of_ae_prod hProduct
  obtain ⟨a₀, ha₀⟩ := hSections.exists

  -- A fixed exclusive-coordinate section is measurable in the common array.
  have hFillMeas : Measurable (fillS a₀) := by
    apply Measurable.of_eval
    intro z
    by_cases hz : z.val ∈ T
    · simpa [fillS, hz] using
        (measurable_pi_apply (⟨z.val, ⟨z.property, hz⟩⟩ : I))
    · simp [fillS, hz]
  refine ⟨fun x => gS (fillS a₀ x), hgS.comp hFillMeas, ?_⟩

  -- Pull the chosen section back to the original iid law and compare with f.
  have hRestrictR : Measurable (fun ω : Environment => fun z : R => ω z) :=
    measurable_pi_iff.mpr (fun z : R => measurable_environment_eval z)
  have hSectionMap : ∀ᵐ r ∂P₀.map (fun ω : Environment => fun z : R => ω z),
      gS (fillS a₀ (restrictI r)) = gT (restrictT r) := by
    rw [hRmap]
    exact ha₀
  have hBack := ae_of_ae_map hRestrictR.aemeasurable hSectionMap
  filter_upwards [hT, hBack] with ω ht hb
  have hI : restrictI (fun z : R => ω z.val) =
      (fun z : I => ω z.val) := rfl
  have hT' : restrictT (fun z : R => ω z.val) =
      (fun z : T => ω z.val) := rfl
  rw [hI, hT'] at hb
  exact ht.trans hb.symm

end LPPDifferentiability
