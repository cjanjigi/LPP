/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.ConditionalPathKernel
public import Busemann.Process.RightmostPathCovariance

import Busemann.Process.RightmostPathMeasurability
import Busemann.Process.Shifts
import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
namespace LPP.Busemann

private theorem compProd_comap_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν]
    (T : α ≃ᵐ α) (hT : MeasurePreserving T ν ν)
    (K : Kernel α β) [IsFiniteKernel K] :
    ν ⊗ₘ (K.comap T T.measurable) =
      (ν ⊗ₘ K).map (Prod.map T.symm id) := by
  classical
  apply Measure.ext_prod
  intro s t hs ht
  have hTs : MeasurableSet (T '' s) :=
    T.measurableEmbedding.measurableSet_image.mpr hs
  have hpre : (Prod.map T.symm id) ⁻¹' (s ×ˢ t) = (T '' s) ×ˢ t := by
    ext p
    constructor
    · intro hp
      have hps : T.symm p.1 ∈ s := hp.1
      exact ⟨⟨T.symm p.1, hps, T.apply_symm_apply p.1⟩, hp.2⟩
    · rintro ⟨⟨x, hx, hxp⟩, ht'⟩
      change T.symm p.1 ∈ s ∧ p.2 ∈ t
      constructor
      · rw [← hxp, T.symm_apply_apply]
        exact hx
      · exact ht'
  rw [Measure.compProd_apply_prod hs ht,
    Measure.map_apply (by fun_prop) (hs.prod ht), hpre,
    Measure.compProd_apply_prod hTs ht]
  change (∫⁻ a in s, K (T a) t ∂ν) = ∫⁻ a in T '' s, K a t ∂ν
  exact hT.setLIntegral_comp_emb T.measurableEmbedding
    (fun a => K a t) s

/-- Shift covariance, as an equality of the actual conditional rightmost-path
measures, on one environment event for all lattice roots and shifts. This is
the conditional-law transport used in Strong Existence, public source
Lemma xBhatproc, equation x-cov, lines 793–840. -/
theorem conditional_rightmost_path_law_shift_covariance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∀ᵐ ω ∂environmentLaw μ, ∀ (u z : Lattice),
      κ (u + z) ω =
        (κ u (environmentTranslationEquiv z ω)).map
          (fun γ : ℕ → Lattice => fun n : ℕ => γ n + z) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  let ray (u : Lattice) (a : ProcessSample) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y a) u
  let shiftPath (z : Lattice) (γ : ℕ → Lattice) : ℕ → Lattice :=
    fun n => γ n + z
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun a : ProcessSample => ((x, y), a)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  have hRay (u : Lattice) : Measurable (ray u) := by
    apply measurable_pi_iff.mpr
    intro n
    exact measurable_rightmostCocyclePath B hBMeas u n
  have hPathMeas (z : Lattice) : Measurable (shiftPath z) := by
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply n).add measurable_const
  have hCov (z : Lattice) :
      ∀ᵐ a ∂P, ∀ (x y : Lattice),
        B (x + z) (y + z) a = B x y (processShift z a) := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    exact hB.1.2.1 x y z
  have hRayCov (u z : Lattice) :
      ∀ᵐ a ∂P, ray (u + z) a = shiftPath z (ray u (processShift z a)) := by
    filter_upwards [hCov z] with a ha
    funext n
    exact (rightmostCocyclePath_translate
      (fun x y => B x y a) (fun x y => B x y (processShift z a)) z
      (fun x y => (ha x y).symm) u n).symm
  have hJoint (u : Lattice) :
      (environmentLaw μ) ⊗ₘ κ u =
        P.map (fun a : ProcessSample => (processEnvironment a, ray u a)) := by
    rw [← hMarginal]
    exact compProd_map_condDistrib measurable_fst.aemeasurable (hRay u).aemeasurable
  have hOne (u z : Lattice) :
      ∀ᵐ ω ∂environmentLaw μ,
        κ (u + z) ω =
          (κ u (environmentTranslationEquiv z ω)).map (shiftPath z) := by
    let T := environmentTranslationEquiv z
    let F := shiftPath z
    let K : Kernel Environment (ℕ → Lattice) :=
      (κ u).comap T T.measurable |>.map F
    have hKfinite : IsFiniteKernel K := by infer_instance
    have hJointShift :
        P.map (fun a : ProcessSample =>
          (processEnvironment a, ray (u + z) a)) =
          (P.map (fun a : ProcessSample =>
            (processEnvironment a, ray u a))).map
              (Prod.map T.symm F) := by
      have hComp : Measurable (fun a : ProcessSample =>
          (T.symm (processEnvironment a), F (ray u a))) :=
        (T.symm.measurable.comp measurable_fst).prodMk
          ((hPathMeas z).comp (hRay u))
      have hJointMeas : Measurable (fun a : ProcessSample =>
          (processEnvironment a, ray u a)) :=
        measurable_fst.prodMk (hRay u)
      have hShiftMeas := measurable_processShift z
      calc
        P.map (fun a : ProcessSample =>
          (processEnvironment a, ray (u + z) a))
          = P.map (fun a : ProcessSample =>
              (processEnvironment a, F (ray u (processShift z a)))) := by
              apply Measure.map_congr
              filter_upwards [hRayCov u z] with a ha
              exact Prod.ext rfl ha
        _ = (P.map (processShift z)).map (fun a : ProcessSample =>
              (T.symm (processEnvironment a), F (ray u a))) := by
              rw [Measure.map_map hComp hShiftMeas]
              apply Measure.map_congr
              filter_upwards with a
              congr 1
              rw [processEnvironment_processShift]
              exact (T.symm_apply_apply _).symm
        _ = P.map (fun a : ProcessSample =>
              (T.symm (processEnvironment a), F (ray u a))) := by rw [hShift z]
        _ = (P.map (fun a : ProcessSample =>
              (processEnvironment a, ray u a))).map (Prod.map T.symm F) := by
              rw [Measure.map_map (by fun_prop) hJointMeas]
              rfl
    have hKjoint :
        (environmentLaw μ) ⊗ₘ K =
          P.map (fun a : ProcessSample =>
            (processEnvironment a, ray (u + z) a)) := by
      dsimp [K]
      rw [Measure.compProd_map (hPathMeas z),
        compProd_comap_measurePreserving (environmentLaw μ) T
          (measurePreserving_environmentTranslationEquiv μ z) (κ u),
        hJoint]
      have hMap1 : Measurable
          (Prod.map T.symm id :
            (Environment × (ℕ → Lattice)) → Environment × (ℕ → Lattice)) :=
        (T.symm.measurable.comp measurable_fst).prodMk measurable_snd
      have hMap2 : Measurable
          (Prod.map id F :
            (Environment × (ℕ → Lattice)) → Environment × (ℕ → Lattice)) :=
        measurable_fst.prodMk ((hPathMeas z).comp measurable_snd)
      rw [Measure.map_map hMap2 hMap1]
      have hCompose :
          (Prod.map id F) ∘ (Prod.map T.symm id) = Prod.map T.symm F := by
        funext p
        cases p
        rfl
      rw [hCompose]
      exact hJointShift.symm
    have hUnique := condDistrib_ae_eq_of_measure_eq_compProd
      (μ := P) (X := processEnvironment) (Y := ray (u + z))
      measurable_fst.aemeasurable (hRay (u + z)).aemeasurable
      (by simpa only [hMarginal] using hKjoint.symm)
    rw [hMarginal] at hUnique
    filter_upwards [hUnique] with ω hω
    change κ (u + z) ω = ((κ u).comap T T.measurable |>.map F) ω at hω
    rw [Kernel.map_apply _ (hPathMeas z), Kernel.comap_apply] at hω
    exact hω
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro z
  exact hOne u z

end LPP.Busemann
