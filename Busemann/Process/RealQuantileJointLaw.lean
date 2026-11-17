/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RealQuantileExtension
public import Busemann.Process.ConditionalPathKernel
public import Busemann.Geometry.GeodesicLowerCut
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Busemann.Geometry.GeodesicCutGenerators
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! The conditional real-quantile family reproduces the actual joint law. -/

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- The measurable real CDF quantile from the original process law samples
the original environment/rightmost-ray joint law at every root. Strong
Existence, public source Lemma Fubini-new, lines 867–901. -/
theorem real_rightmost_quantile_joint_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∀ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) →
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) →
      ∀ u : Lattice,
        (((environmentLaw μ).prod (volume : Measure unitInterval)).map
          (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
        P.map (fun a : ProcessSample =>
          (processEnvironment a,
            rightmostCocyclePath (fun x y => B x y a) u)) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  change ∀ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
    (∀ u : Lattice, Measurable
      (fun a : Environment × unitInterval => q u a.1 a.2)) →
    (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
      IsLocallyRightmostGeodesic ω u (q u ω s) ∧
      ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
        (pathSoutheastLE (q u ω s) γ ↔
          ENNReal.ofReal (s : ℝ) ≤
            (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) →
    ∀ u : Lattice,
      (((environmentLaw μ).prod (volume : Measure unitInterval)).map
        (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
      P.map (fun a : ProcessSample =>
        (processEnvironment a,
          rightmostCocyclePath (fun x y => B x y a) u))
  obtain ⟨hMarkov, hJoint, _hCDF, _hThreshold, A, hA, hAFull, hSupport⟩ :=
    conditional_rightmost_path_law_and_thresholds μ P hMarginal B hB
  intro q hqMeas hqCDF
  have hQfixed (u : Lattice) (ω : Environment) : Measurable (q u ω) :=
    (hqMeas u).comp (measurable_const.prodMk measurable_id)
  have hQpair (u : Lattice) : Measurable
      (fun a : Environment × unitInterval => (a.1, q u a.1 a.2)) :=
    measurable_fst.prodMk (hqMeas u)
  have hAae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hA).mpr hAFull
  have hFibre (u : Lattice) : ∀ᵐ ω ∂environmentLaw μ,
      (volume : Measure unitInterval).map (q u ω) = (κ u) ω := by
    filter_upwards [hqCDF, hAae] with ω hqω hAω
    let : IsMarkovKernel (κ u) := hMarkov u
    let G : Set (ℕ → Lattice) :=
      {γ | IsLocallyRightmostGeodesic ω u γ}
    have hG : MeasurableSet G := by
      have h := measurableSet_isLocallyRightmostGeodesic
      exact h.preimage
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hκG : (κ u) ω G = 1 := (hSupport ω hAω u).1
    have hκGae : ∀ᵐ γ ∂(κ u) ω, γ ∈ G :=
      (mem_ae_iff_prob_eq_one hG).mpr hκG
    let f : unitInterval → G :=
      fun s => ⟨q u ω s, (hqω u s).1⟩
    have hf : Measurable f := (hQfixed u ω).subtype_mk
    let C : Set (Set G) :=
      {S | ∃ ρ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u ρ ∧
        S = {γ | pathSoutheastLE γ.val ρ}}
    have hTrans (a b c : G)
        (hab : pathSoutheastLE a.val b.val)
        (hbc : pathSoutheastLE b.val c.val) :
        pathSoutheastLE a.val c.val := by
      have hrootab : a.val 0 = b.val 0 := a.property.1.trans b.property.1.symm
      have hrootbc : b.val 0 = c.val 0 := b.property.1.trans c.property.1.symm
      apply (pathSoutheastLE_iff_all_times_of_same_root
        a.val c.val (hrootab.trans hrootbc)).mpr
      have hAB := (pathSoutheastLE_iff_all_times_of_same_root
        a.val b.val hrootab).mp hab
      have hBC := (pathSoutheastLE_iff_all_times_of_same_root
        b.val c.val hrootbc).mp hbc
      intro n
      exact ⟨(hAB n).1.trans (hBC n).1, (hBC n).2.trans (hAB n).2⟩
    have hPi : IsPiSystem C := by
      intro S hS T hT _hne
      obtain ⟨ρ, hρ, rfl⟩ := hS
      obtain ⟨σ, hσ, rfl⟩ := hT
      rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        ω u ρ σ hρ hσ with hρσ | hσρ
      · refine ⟨ρ, hρ, ?_⟩
        ext γ
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · exact And.left
        · intro hγρ
          exact ⟨hγρ, hTrans γ ⟨ρ, hρ⟩ ⟨σ, hσ⟩ hγρ hρσ⟩
      · refine ⟨σ, hσ, ?_⟩
        ext γ
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · exact And.right
        · intro hγσ
          exact ⟨hTrans γ ⟨σ, hσ⟩ ⟨ρ, hρ⟩ hγσ hσρ, hγσ⟩
    have hCutMeas (ρ : ℕ → Lattice) :
        MeasurableSet {γ : G | pathSoutheastLE γ.val ρ} := by
      have hPath : MeasurableSet
          {γ : ℕ → Lattice | pathSoutheastLE γ ρ} :=
        measurableSet_pathSoutheastLE.preimage
          (measurable_id.prodMk measurable_const)
      exact hPath.preimage measurable_subtype_coe
    have hCutMass (ρ : ℕ → Lattice)
        (hρ : IsLocallyRightmostGeodesic ω u ρ) :
        (volume : Measure unitInterval)
          {s | pathSoutheastLE (q u ω s) ρ} =
          (κ u) ω {γ : ℕ → Lattice | pathSoutheastLE γ ρ} := by
      let p : ℝ≥0∞ := (κ u) ω {γ : ℕ → Lattice | pathSoutheastLE γ ρ}
      have hp1 : p ≤ 1 := by
        calc p ≤ (κ u) ω Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hp : p ≠ ∞ := (lt_of_le_of_lt hp1 ENNReal.one_lt_top).ne
      let t : unitInterval :=
        ⟨p.toReal, ⟨ENNReal.toReal_nonneg, by
          have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hp1
          simpa using h⟩⟩
      have hInterval : {s : unitInterval | pathSoutheastLE (q u ω s) ρ} =
          Set.Iic t := by
        ext s
        change pathSoutheastLE (q u ω s) ρ ↔ s ≤ t
        rw [(hqω u s).2 ρ hρ]
        exact ENNReal.ofReal_le_iff_le_toReal hp
      rw [hInterval, unitInterval.volume_Iic]
      exact ENNReal.ofReal_toReal hp
    have hCutEq : ∀ S ∈ C,
        ((volume : Measure unitInterval).map f) S =
          (((κ u) ω).comap (fun γ : G => γ.val)) S := by
      intro S hS
      obtain ⟨ρ, hρ, rfl⟩ := hS
      rw [Measure.map_apply hf (hCutMeas ρ),
        comap_subtype_coe_apply hG]
      have hImage : (fun γ : G => γ.val) ''
          {γ : G | pathSoutheastLE γ.val ρ} =
          G ∩ {γ : ℕ → Lattice | pathSoutheastLE γ ρ} := by
        ext γ
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.property, hx⟩
        · rintro ⟨hγ, hcut⟩
          exact ⟨⟨γ, hγ⟩, hcut, rfl⟩
      rw [hImage, Measure.measure_inter_eq_of_ae hκGae]
      exact hCutMass ρ hρ
    have hSubEq :
        (volume : Measure unitInterval).map f =
          ((κ u) ω).comap (fun γ : G => γ.val) := by
      apply MeasureTheory.ext_of_generate_finite C
        (geodesic_lower_cuts_generate_borel ω u) hPi hCutEq
      rw [Measure.map_apply hf MeasurableSet.univ,
        comap_subtype_coe_apply hG]
      simpa only [Set.preimage_univ, Set.image_univ, Subtype.range_coe,
        measure_univ] using hκG.symm
    have hPush := congrArg
      (fun τ : Measure G => τ.map (fun γ : G => γ.val)) hSubEq
    rw [Measure.map_map measurable_subtype_coe hf,
      map_comap_subtype_coe hG,
      Measure.restrict_eq_self_of_ae_mem hκGae] at hPush
    simpa only [Function.comp_def, f] using hPush
  intro u
  let : IsMarkovKernel (κ u) := hMarkov u
  have hJointQuantile :
      (((environmentLaw μ).prod (volume : Measure unitInterval)).map
        (fun a : Environment × unitInterval => (a.1, q u a.1 a.2))) =
      (environmentLaw μ) ⊗ₘ (κ u) := by
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply (hQpair u) hS,
      Measure.prod_apply ((hQpair u) hS),
      Measure.compProd_apply hS]
    apply lintegral_congr_ae
    filter_upwards [hFibre u] with ω hω
    have hSection : MeasurableSet (Prod.mk ω ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    have hEval := congrArg (fun τ : Measure (ℕ → Lattice) =>
      τ (Prod.mk ω ⁻¹' S)) hω
    rw [Measure.map_apply (hQfixed u ω) hSection] at hEval
    simpa only [Set.preimage_preimage, Function.comp_def] using hEval
  exact hJointQuantile.trans (hJoint u)

end LPP.Busemann
