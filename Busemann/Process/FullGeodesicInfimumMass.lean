/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.ConditionalPathKernel
public import Busemann.Geometry.GeodesicInfimum
public import Busemann.Geometry.RightIsolatedGeodesicFamily
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Sequences
import Busemann.Geometry.GeodesicInfimumSequence
import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

/-! Conditional CDF mass at the infimum of all qualifying geodesics. -/

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability Filter
open scoped ENNReal Topology
namespace LPP.Busemann

private theorem pathSoutheastLE_trans_of_same_root
    (a b c : ℕ → Lattice) (hab : pathSoutheastLE a b)
    (hbc : pathSoutheastLE b c) (hrootab : a 0 = b 0)
    (hrootbc : b 0 = c 0) : pathSoutheastLE a c := by
  apply (pathSoutheastLE_iff_all_times_of_same_root a c
    (hrootab.trans hrootbc)).mpr
  have hab' := (pathSoutheastLE_iff_all_times_of_same_root a b hrootab).mp hab
  have hbc' := (pathSoutheastLE_iff_all_times_of_same_root b c hrootbc).mp hbc
  intro n
  exact ⟨(hab' n).1.trans (hbc' n).1, (hbc' n).2.trans (hab' n).2⟩

private theorem mass_at_descending_geodesic_limit
    (ν : Measure (ℕ → Lattice)) [IsProbabilityMeasure ν]
    (ω : Environment) (u : Lattice)
    (hSupport : ν {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω u η} = 1)
    (q : ℕ → Lattice) (hqvalid : IsLocallyRightmostGeodesic ω u q)
    (ρ : ℕ → (ℕ → Lattice))
    (hρvalid : ∀ n, IsLocallyRightmostGeodesic ω u (ρ n))
    (hqlower : ∀ n, pathSoutheastLE q (ρ n))
    (hρdesc : ∀ n, pathSoutheastLE (ρ (n + 1)) (ρ n))
    (hρlimit : Tendsto ρ atTop (𝓝 q))
    (c : ENNReal)
    (hCDF : ∀ n, c ≤ ν {η : ℕ → Lattice | pathSoutheastLE η (ρ n)}) :
    c ≤ ν {η : ℕ → Lattice | pathSoutheastLE η q} := by
  let G : Set (ℕ → Lattice) :=
    {η | IsLocallyRightmostGeodesic ω u η}
  let C (a : ℕ → Lattice) : Set (ℕ → Lattice) :=
    {η | pathSoutheastLE η a}
  let A (n : ℕ) : Set (ℕ → Lattice) := G ∩ C (ρ n)
  have hGmeas : MeasurableSet G :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hCmeas (a : ℕ → Lattice) : MeasurableSet (C a) :=
    measurableSet_pathSoutheastLE.preimage
      (measurable_id.prodMk measurable_const)
  have hGnull : ν Gᶜ = 0 :=
    (prob_compl_eq_zero_iff hGmeas).mpr hSupport
  have hAmass (n : ℕ) : ν (A n) = ν (C (ρ n)) := by
    change ν (G ∩ C (ρ n)) = ν (C (ρ n))
    rw [Set.inter_comm]
    exact measure_inter_conull hGnull
  have hQmass : ν (G ∩ C q) = ν (C q) := by
    rw [Set.inter_comm]
    exact measure_inter_conull hGnull
  have hAmeas (n : ℕ) : MeasurableSet (A n) :=
    hGmeas.inter (hCmeas (ρ n))
  have hAsucc (n : ℕ) : A (n + 1) ⊆ A n := by
    intro η hη
    refine ⟨hη.1, ?_⟩
    exact pathSoutheastLE_trans_of_same_root η (ρ (n + 1)) (ρ n)
      hη.2 (hρdesc n)
      (hη.1.1.trans (hρvalid (n + 1)).1.symm)
      ((hρvalid (n + 1)).1.trans (hρvalid n).1.symm)
  have hAanti : Antitone A := antitone_nat_of_succ_le hAsucc
  have hIntersection : (⋂ n, A n) = G ∩ C q := by
    ext η
    constructor
    · intro hη
      have hηvalid : IsLocallyRightmostGeodesic ω u η :=
        (Set.mem_iInter.mp hη 0).1
      have hroot (n : ℕ) : η 0 = (ρ n) 0 :=
        hηvalid.1.trans (hρvalid n).1.symm
      have hCoordinate (n : ℕ) :
          ∀ k : ℕ, (η k).1 ≤ ((ρ n) k).1 ∧ ((ρ n) k).2 ≤ (η k).2 :=
        (pathSoutheastLE_iff_all_times_of_same_root η (ρ n) (hroot n)).mp
          (Set.mem_iInter.mp hη n).2
      have hClosed : IsClosed
          {a : ℕ → Lattice |
            ∀ k : ℕ, (η k).1 ≤ (a k).1 ∧ (a k).2 ≤ (η k).2} := by
        rw [Set.ofPred_forall]
        apply isClosed_iInter
        intro k
        have hfirst : Continuous (fun a : ℕ → Lattice => (a k).1) :=
          continuous_fst.comp (continuous_apply k)
        have hsecond : Continuous (fun a : ℕ → Lattice => (a k).2) :=
          continuous_snd.comp (continuous_apply k)
        exact (isClosed_le continuous_const hfirst).inter
          (isClosed_le hsecond continuous_const)
      have hηq : pathSoutheastLE η q := by
        apply (pathSoutheastLE_iff_all_times_of_same_root η q
          (hηvalid.1.trans hqvalid.1.symm)).mpr
        exact hClosed.mem_of_tendsto hρlimit
          (Filter.Eventually.of_forall hCoordinate)
      exact ⟨hηvalid, hηq⟩
    · rintro ⟨hηvalid, hηq⟩
      apply Set.mem_iInter.mpr
      intro n
      refine ⟨hηvalid, ?_⟩
      exact pathSoutheastLE_trans_of_same_root η q (ρ n)
        hηq (hqlower n)
        (hηvalid.1.trans hqvalid.1.symm)
        (hqvalid.1.trans (hρvalid n).1.symm)
  have hContinuity : ν (⋂ n, A n) = ⨅ n, ν (A n) :=
    hAanti.measure_iInter (fun n => (hAmeas n).nullMeasurableSet)
      ⟨0, measure_ne_top ν (A 0)⟩
  calc
    c ≤ ⨅ n, ν (A n) := le_iInf fun n => by rw [hAmass n]; exact hCDF n
    _ = ν (⋂ n, A n) := hContinuity.symm
    _ = ν (G ∩ C q) := by rw [hIntersection]
    _ = ν (C q) := hQmass

/-- At the infimum of all qualifying geodesics, the conditional order CDF
still reaches the rational threshold. The lower-bound clauses identify the
full-geodesic infimum, distinct from the right-isolated infimum. Strong
Existence, public source lines 810–814. -/
theorem rational_full_geodesic_infimum_cdf_mass
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (u : Lattice) :
    let κ : Kernel Environment (ℕ → Lattice) :=
      condDistrib
        (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
        processEnvironment P
    ∀ᵐ ω ∂environmentLaw μ, ∀ (r : ℚ), 0 ≤ r → r ≤ 1 →
      ∃! q : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u q ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          ENNReal.ofReal (r : ℝ) ≤
            κ ω {η : ℕ → Lattice | pathSoutheastLE η γ} →
          pathSoutheastLE q γ) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η γ} →
            pathSoutheastLE δ γ) →
          pathSoutheastLE δ q) ∧
        ENNReal.ofReal (r : ℝ) ≤
          κ ω {η : ℕ → Lattice | pathSoutheastLE η q} := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
    Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hR := Classical.choose_spec
    (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  obtain ⟨A, hAmeas, hAone, hAproperty⟩ := hKernel.2.2.2.2
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAone
  filter_upwards [hAE] with ω hω
  intro r hr0 hr1
  let : IsMarkovKernel κ := hKernel.1 u
  let : IsProbabilityMeasure (κ ω) := (hKernel.1 u).isProbabilityMeasure ω
  let i₀ : Σ d : ℕ × ℕ, Path u d :=
    ⟨(0, 0), horizontalFirst u (0, 0)⟩
  have hRactual : IsLocallyRightmostGeodesic ω u (R i₀ ω) := by
    obtain ⟨e, p, hg, _, _⟩ := hR.2.2.1 i₀ ω
    exact hg
  have hZeroPrefix (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      ∀ k : Fin (i₀.1.1 + i₀.1.2 + 1), i₀.2.vertex k = γ k.val := by
    intro k
    have hk : k.val = 0 := by
      have hlt : k.val < 1 := by simp [i₀]
      omega
    have hkFin : k = 0 := Fin.ext hk
    subst k
    simpa [i₀] using (horizontalFirst u (0, 0)).start.trans hγ.1.symm
  have hTop (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      pathSoutheastLE γ (R i₀ ω) := by
    have hExists : ∃ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (i₀.1.1 + i₀.1.2 + 1), i₀.2.vertex k = γ k.val :=
      ⟨R i₀ ω, hRactual, hZeroPrefix (R i₀ ω) hRactual⟩
    have hPrefix := (hR.2.1 i₀ ω).1 hExists
    exact hPrefix.2.2 γ hγ (fun k => (hZeroPrefix γ hγ k).symm)
  have hTopMass :
      κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i₀ ω)} = 1 := by
    have hSubset :
        {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω u η} ⊆
          {η : ℕ → Lattice | pathSoutheastLE η (R i₀ ω)} :=
      fun η hη => hTop η hη
    have hUpper :
        κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i₀ ω)} ≤ 1 := by
      calc
        κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i₀ ω)} ≤
            κ ω Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact le_antisymm hUpper
      (by rw [← (hAproperty ω hω u).1]; exact measure_mono hSubset)
  have hLevel : ENNReal.ofReal (r : ℝ) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (show (r : ℝ) ≤ 1 by exact_mod_cast hr1)
  let F : Set (ℕ → Lattice) :=
    {γ | IsLocallyRightmostGeodesic ω u γ ∧
      ENNReal.ofReal (r : ℝ) ≤
        κ ω {η : ℕ → Lattice | pathSoutheastLE η γ}}
  have hFnonempty : F.Nonempty := by
    refine ⟨R i₀ ω, hRactual, ?_⟩
    rw [hTopMass]
    exact hLevel
  have hFvalid : ∀ γ ∈ F, IsLocallyRightmostGeodesic ω u γ :=
    fun _ hγ => hγ.1
  obtain ⟨q, hq, hqUnique⟩ :=
    exists_unique_geodesic_infimum ω u F hFnonempty hFvalid
  obtain ⟨ρ, hρF, hρdesc, hρlimit⟩ :=
    exists_descending_geodesics_tendsto_infimum ω u F hFnonempty hFvalid
      q hq.1 hq.2.1 hq.2.2
  have hMass : ENNReal.ofReal (r : ℝ) ≤
      κ ω {η : ℕ → Lattice | pathSoutheastLE η q} := by
    exact mass_at_descending_geodesic_limit (κ ω) ω u
      (hAproperty ω hω u).1 q hq.1 ρ
      (fun n => (hρF n).1)
      (fun n => hq.2.1 (ρ n) (hρF n))
      hρdesc hρlimit (ENNReal.ofReal (r : ℝ))
      (fun n => (hρF n).2)
  refine ⟨q, ?_, ?_⟩
  · refine ⟨hq.1, ?_, ?_, hMass⟩
    · intro γ hγ hγmass
      exact hq.2.1 γ ⟨hγ, hγmass⟩
    · intro δ hδ hδlower
      apply hq.2.2 δ hδ
      intro γ hγF
      exact hδlower γ hγF.1 hγF.2
  · intro q' hq'
    apply hqUnique q'
    refine ⟨hq'.1, ?_, ?_⟩
    · intro γ hγF
      exact hq'.2.1 γ hγF.1 hγF.2
    · intro δ hδ hδlower
      apply hq'.2.2.1 δ hδ
      intro γ hγ hγmass
      exact hδlower γ ⟨hγ, hγmass⟩

end LPP.Busemann
