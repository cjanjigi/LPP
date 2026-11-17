/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.ConditionalJointRayCoalescence
public import Busemann.Geometry.CoalescingBarrierOrder
public import Busemann.Geometry.GeodesicMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace LPP.Busemann

/-- The original one-ray conditional lower-cut masses agree at coalescing
barriers, using the joint conditional law of two rays from the same sample.
Strong Existence, lem:coal-equiv, public source lines 913–927. -/
theorem conditional_rightmost_lower_cut_eq_of_coalescing_barriers
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun s : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y s) u)
        processEnvironment P
    ∀ᵐ ω ∂environmentLaw μ, ∀ u v : Lattice,
      ∀ π γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u π →
        IsLocallyRightmostGeodesic ω v γ →
        (∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, π (m + k) = γ (n + k)) →
        (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η π} =
          (κ v) ω {η : ℕ → Lattice | pathSoutheastLE η γ} := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun s : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let κ₂ : Lattice → Lattice →
      Kernel Environment ((ℕ → Lattice) × (ℕ → Lattice)) :=
    fun u v => condDistrib
      (fun s : ProcessSample =>
        (rightmostCocyclePath (fun x y => B x y s) u,
         rightmostCocyclePath (fun x y => B x y s) v))
      processEnvironment P
  let tailPiece (u v : Lattice) (m n : ℕ) :
      Set ((ℕ → Lattice) × (ℕ → Lattice)) :=
    {p | u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)}
  let tailEvent (u v : Lattice) :
      Set ((ℕ → Lattice) × (ℕ → Lattice)) :=
    {p | ∃ m n : ℕ,
      u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)}
  change ∀ᵐ ω ∂environmentLaw μ, ∀ u v : Lattice,
    ∀ π γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u π →
      IsLocallyRightmostGeodesic ω v γ →
      (∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, π (m + k) = γ (n + k)) →
      (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η π} =
        (κ v) ω {η : ℕ → Lattice | pathSoutheastLE η γ}

  have hOneRay := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  have hSingleSupport : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      (κ u) ω {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω u η} = 1 := by
    obtain ⟨A, hAmeas, hAone, hAproperty⟩ := hOneRay.2.2.2.2
    filter_upwards [
      (mem_ae_iff_prob_eq_one hAmeas).mpr hAone] with ω hω
    intro u
    exact (hAproperty ω hω u).1

  have hJointRay : ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      ((κ₂ u v) ω).map Prod.fst = (κ u) ω ∧
      ((κ₂ u v) ω).map Prod.snd = (κ v) ω ∧
      (κ₂ u v) ω
        {p | ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} = 1 := by
    exact conditional_joint_rightmost_rays_coalesce
      μ P hMarginal B hB hCoal

  have hJointAll : ∀ᵐ ω ∂environmentLaw μ, ∀ u v : Lattice,
      ((κ₂ u v) ω).map Prod.fst = (κ u) ω ∧
      ((κ₂ u v) ω).map Prod.snd = (κ v) ω ∧
      (κ₂ u v) ω
        {p | ∃ m n : ℕ,
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} = 1 := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    exact hJointRay u v

  have hTailCoordinateEq (m n k : ℕ) :
      MeasurableSet
        {p : (ℕ → Lattice) × (ℕ → Lattice) |
          p.1 (m + k) = p.2 (n + k)} := by
    apply measurableSet_eq_fun
    · exact (measurable_pi_apply (m + k)).comp measurable_fst
    · exact (measurable_pi_apply (n + k)).comp measurable_snd
  have hTailPieceMeas (u v : Lattice) (m n : ℕ) :
      MeasurableSet (tailPiece u v m n) := by
    by_cases hAlign : u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ)
    · have hEq : tailPiece u v m n =
          {p : (ℕ → Lattice) × (ℕ → Lattice) |
            ∀ k : ℕ, p.1 (m + k) = p.2 (n + k)} := by
        ext p
        simp [tailPiece, hAlign]
      rw [hEq]
      simpa only [Set.ofPred_forall] using
        (MeasurableSet.iInter fun k => hTailCoordinateEq m n k)
    · have hEq : tailPiece u v m n = ∅ := by
        ext p
        simp [tailPiece, hAlign]
      rw [hEq]
      exact MeasurableSet.empty
  have hTailUnion (u v : Lattice) :
      tailEvent u v = ⋃ m : ℕ, ⋃ n : ℕ, tailPiece u v m n := by
    ext p
    simp [tailEvent, tailPiece]
  have hTailMeas (u v : Lattice) : MeasurableSet (tailEvent u v) := by
    rw [hTailUnion u v]
    exact MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun n => hTailPieceMeas u v m n

  filter_upwards [hSingleSupport, hJointAll] with ω hSupport hJoint
  intro u v π γ hBarrierU hBarrierV hBarriers
  rcases hJoint u v with ⟨hFirst, hSecond, hTailMass⟩
  have hTailMass' : (κ₂ u v) ω (tailEvent u v) = 1 := by
    simpa only [tailEvent] using hTailMass
  have hTailAE : ∀ᵐ p ∂(κ₂ u v) ω, p ∈ tailEvent u v :=
    (mem_ae_iff_prob_eq_one (hTailMeas u v)).mpr hTailMass'

  have hLocalUSet : MeasurableSet
      {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω u η} :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hLocalVSet : MeasurableSet
      {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω v η} :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hLocalUJointSet : MeasurableSet
      {p : (ℕ → Lattice) × (ℕ → Lattice) |
        IsLocallyRightmostGeodesic ω u p.1} :=
    hLocalUSet.preimage measurable_fst
  have hLocalVJointSet : MeasurableSet
      {p : (ℕ → Lattice) × (ℕ → Lattice) |
        IsLocallyRightmostGeodesic ω v p.2} :=
    hLocalVSet.preimage measurable_snd
  have hLocalUMass : (κ₂ u v) ω
      {p : (ℕ → Lattice) × (ℕ → Lattice) |
        IsLocallyRightmostGeodesic ω u p.1} = 1 := by
    have h := hSupport u
    rw [← hFirst, Measure.map_apply measurable_fst hLocalUSet] at h
    simpa only [Set.preimage, Function.comp_apply, Set.mem_ofPred_eq] using h
  have hLocalVMass : (κ₂ u v) ω
      {p : (ℕ → Lattice) × (ℕ → Lattice) |
        IsLocallyRightmostGeodesic ω v p.2} = 1 := by
    have h := hSupport v
    rw [← hSecond, Measure.map_apply measurable_snd hLocalVSet] at h
    simpa only [Set.preimage, Function.comp_apply, Set.mem_ofPred_eq] using h
  have hRayU : ∀ᵐ p ∂(κ₂ u v) ω,
      IsLocallyRightmostGeodesic ω u p.1 := by
    filter_upwards [
      (mem_ae_iff_prob_eq_one hLocalUJointSet).mpr hLocalUMass] with p hp
    exact hp
  have hRayV : ∀ᵐ p ∂(κ₂ u v) ω,
      IsLocallyRightmostGeodesic ω v p.2 := by
    filter_upwards [
      (mem_ae_iff_prob_eq_one hLocalVJointSet).mpr hLocalVMass] with p hp
    exact hp

  have hCutUSet : MeasurableSet
      {η : ℕ → Lattice | pathSoutheastLE η π} :=
    measurableSet_pathSoutheastLE.preimage
      (measurable_id.prodMk measurable_const)
  have hCutVSet : MeasurableSet
      {η : ℕ → Lattice | pathSoutheastLE η γ} :=
    measurableSet_pathSoutheastLE.preimage
      (measurable_id.prodMk measurable_const)
  have hCutMass : (κ₂ u v) ω
        {p : (ℕ → Lattice) × (ℕ → Lattice) |
          pathSoutheastLE p.1 π} =
      (κ₂ u v) ω
        {p : (ℕ → Lattice) × (ℕ → Lattice) |
          pathSoutheastLE p.2 γ} := by
    apply measure_congr
    filter_upwards [hRayU, hRayV, hTailAE] with p hpU hpV hpTail
    change ∃ m n : ℕ,
      u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, p.1 (m + k) = p.2 (n + k) at hpTail
    obtain ⟨m, n, hAlign, hTail⟩ := hpTail
    exact propext <| pathSoutheastLE_iff_of_coalescing_locallyRightmost_pairs
      ω u v p.1 π p.2 γ hpU hBarrierU hpV hBarrierV
      ⟨m, n, hAlign, hTail⟩ hBarriers

  calc
    (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η π} =
        ((κ₂ u v) ω).map Prod.fst
          {η : ℕ → Lattice | pathSoutheastLE η π} := by
      rw [← hFirst]
    _ = (κ₂ u v) ω
          {p : (ℕ → Lattice) × (ℕ → Lattice) |
            pathSoutheastLE p.1 π} := by
      rw [Measure.map_apply measurable_fst hCutUSet]
      rfl
    _ = (κ₂ u v) ω
          {p : (ℕ → Lattice) × (ℕ → Lattice) |
            pathSoutheastLE p.2 γ} := hCutMass
    _ = ((κ₂ u v) ω).map Prod.snd
          {η : ℕ → Lattice | pathSoutheastLE η γ} := by
      rw [Measure.map_apply measurable_snd hCutVSet]
      rfl
    _ = (κ v) ω {η : ℕ → Lattice | pathSoutheastLE η γ} := by
      rw [hSecond]

end LPP.Busemann
