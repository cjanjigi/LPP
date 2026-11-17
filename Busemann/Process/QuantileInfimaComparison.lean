/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.ConditionalPathQuantileInfimum
public import Busemann.Process.FullGeodesicInfimumMass
import Mathlib.Tactic

/-! Identification of the rational right-isolated and full-geodesic infima. -/

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability Filter
open scoped ENNReal Topology
namespace LPP.Busemann

private theorem southeast_refl (a : ℕ → Lattice) : pathSoutheastLE a a :=
  (pathSoutheastLE_iff_all_times_of_same_root a a rfl).mpr
    (fun _ => ⟨le_rfl, le_rfl⟩)

private theorem southeast_trans_same_root
    (a b c : ℕ → Lattice) (hab : pathSoutheastLE a b)
    (hbc : pathSoutheastLE b c) (hrootab : a 0 = b 0)
    (hrootbc : b 0 = c 0) : pathSoutheastLE a c := by
  apply (pathSoutheastLE_iff_all_times_of_same_root a c
    (hrootab.trans hrootbc)).mpr
  have hab' := (pathSoutheastLE_iff_all_times_of_same_root a b hrootab).mp hab
  have hbc' := (pathSoutheastLE_iff_all_times_of_same_root b c hrootbc).mp hbc
  intro n
  exact ⟨(hab' n).1.trans (hbc' n).1, (hbc' n).2.trans (hab' n).2⟩

private theorem southeast_antisymm_same_root
    (a b : ℕ → Lattice) (hroot : a 0 = b 0)
    (hab : pathSoutheastLE a b) (hba : pathSoutheastLE b a) : a = b := by
  have hf := (pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp hab
  have hb := (pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp hba
  funext n
  exact Prod.ext (le_antisymm (hf n).1 (hb n).1)
    (le_antisymm (hb n).2 (hf n).2)

/-- For rational thresholds, the right-isolated quantile infimum is the
infimum over all qualifying locally rightmost geodesics. This is the
identification after the full-infimum mass bound in Strong Existence,
public source lines 804–815. -/
theorem rational_right_isolated_infimum_eq_full_geodesic_infimum
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
    let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
      Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
    ∀ᵐ ω ∂environmentLaw μ, ∀ (r : ℚ), 0 ≤ r → r ≤ 1 →
      ∃! q : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u q ∧
        (∀ i : Σ d : ℕ × ℕ, Path u d,
          ENNReal.ofReal (r : ℝ) ≤
            κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
          pathSoutheastLE q (R i ω)) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
            pathSoutheastLE δ (R i ω)) →
          pathSoutheastLE δ q) ∧
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
          pathSoutheastLE δ q) := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
    Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hR := Classical.choose_spec
    (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hRI := exists_unique_rational_right_isolated_quantile_inf
    μ P hMarginal B hB u
  have hFull := rational_full_geodesic_infimum_cdf_mass
    μ P hMarginal B hB u
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  obtain ⟨A, hAmeas, hAone, hAproperty⟩ := hKernel.2.2.2.2
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAone
  filter_upwards [hRI, hFull, hAE] with ω hRIω hFullω hAω
  intro r hr0 hr1
  obtain ⟨qR, hqR, hqRunique⟩ := hRIω r hr0 hr1
  obtain ⟨qF, hqF, _⟩ := hFullω r hr0 hr1
  have hRvalid (i : Σ d : ℕ × ℕ, Path u d) :
      IsLocallyRightmostGeodesic ω u (R i ω) := by
    obtain ⟨e, p, hg, _, _⟩ := hR.2.2.1 i ω
    exact hg

  -- The full family contains every qualifying right-isolated ray.
  have hFleR : pathSoutheastLE qF qR := by
    apply hqR.2.2 qF hqF.1
    intro i hi
    exact hqF.2.1 (R i ω) (hRvalid i) hi

  -- The right-isolated family supplies arbitrarily long prefix approximants.
  have hApprox (N : ℕ) :
      ∃ i : Σ d : ℕ × ℕ, Path u d,
        pathSoutheastLE qF (R i ω) ∧
        ∀ k : ℕ, k ≤ N → R i ω k = qF k :=
    hR.2.2.2.2 ω qF hqF.1 N
  let i (N : ℕ) : Σ d : ℕ × ℕ, Path u d := Classical.choose (hApprox N)
  let a (N : ℕ) : ℕ → Lattice := R (i N) ω
  have hAabove (N : ℕ) : pathSoutheastLE qF (a N) :=
    (Classical.choose_spec (hApprox N)).1
  have hAprefix (N k : ℕ) (hk : k ≤ N) : a N k = qF k :=
    (Classical.choose_spec (hApprox N)).2 k hk
  have hAvalid (N : ℕ) : IsLocallyRightmostGeodesic ω u (a N) :=
    hRvalid (i N)

  -- Geodesic support makes order-cone monotonicity valid for this kernel.
  let : IsProbabilityMeasure (κ ω) := (hKernel.1 u).isProbabilityMeasure ω
  let G : Set (ℕ → Lattice) :=
    {η | IsLocallyRightmostGeodesic ω u η}
  let C (b : ℕ → Lattice) : Set (ℕ → Lattice) :=
    {η | pathSoutheastLE η b}
  have hGmeas : MeasurableSet G :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hGnull : κ ω Gᶜ = 0 :=
    (prob_compl_eq_zero_iff hGmeas).mpr (hAproperty ω hAω u).1
  have hCmass (b : ℕ → Lattice) : κ ω (G ∩ C b) = κ ω (C b) := by
    rw [Set.inter_comm]
    exact measure_inter_conull hGnull
  have hAmass (N : ℕ) :
      ENNReal.ofReal (r : ℝ) ≤ κ ω (C (a N)) := by
    have hSubset : G ∩ C qF ⊆ G ∩ C (a N) := by
      intro η hη
      refine ⟨hη.1, ?_⟩
      exact southeast_trans_same_root η qF (a N) hη.2 (hAabove N)
        (hη.1.1.trans hqF.1.1.symm)
        (hqF.1.1.trans (hAvalid N).1.symm)
    calc
      ENNReal.ofReal (r : ℝ) ≤ κ ω (C qF) := hqF.2.2.2
      _ = κ ω (G ∩ C qF) := (hCmass qF).symm
      _ ≤ κ ω (G ∩ C (a N)) := measure_mono hSubset
      _ = κ ω (C (a N)) := hCmass (a N)

  -- Running minima are still members of the qualifying right-isolated family.
  let ρ : ℕ → (ℕ → Lattice) :=
    Nat.rec (a 0)
      (fun N prev => if pathSoutheastLE (a (N + 1)) prev then a (N + 1) else prev)
  have hρzero : ρ 0 = a 0 := rfl
  have hρsucc (N : ℕ) :
      ρ (N + 1) = if pathSoutheastLE (a (N + 1)) (ρ N) then a (N + 1) else ρ N :=
    rfl
  have hρRI : ∀ N : ℕ, ∃ j : Σ d : ℕ × ℕ, Path u d,
      ρ N = R j ω ∧
      ENNReal.ofReal (r : ℝ) ≤ κ ω (C (R j ω)) := by
    intro N
    induction N with
    | zero => exact ⟨i 0, rfl, hAmass 0⟩
    | succ N ih =>
      rw [hρsucc]
      split_ifs with h
      · exact ⟨i (N + 1), rfl, hAmass (N + 1)⟩
      · exact ih
  have hρvalid (N : ℕ) : IsLocallyRightmostGeodesic ω u (ρ N) := by
    obtain ⟨j, hj, _⟩ := hρRI N
    rw [hj]
    exact hRvalid j
  have hρdesc (N : ℕ) : pathSoutheastLE (ρ (N + 1)) (ρ N) := by
    rw [hρsucc]
    split_ifs with h
    · exact h
    · exact southeast_refl (ρ N)
  have hFbelowρ (N : ℕ) : pathSoutheastLE qF (ρ N) := by
    induction N with
    | zero => exact hAabove 0
    | succ N ih =>
      rw [hρsucc]
      split_ifs with h
      · exact hAabove (N + 1)
      · exact ih
  have hρbelowA (N : ℕ) : pathSoutheastLE (ρ N) (a N) := by
    cases N with
    | zero => exact southeast_refl (a 0)
    | succ N =>
      rw [hρsucc]
      by_cases h : pathSoutheastLE (a (N + 1)) (ρ N)
      · rw [ite_eq_left h]
        exact southeast_refl (a (N + 1))
      · rw [ite_eq_right h]
        rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
          ω u (ρ N) (a (N + 1)) (hρvalid N) (hAvalid (N + 1)) with hle | hle
        · exact hle
        · exact False.elim (h hle)

  -- The printed decreasing right-isolated sequence converges to the full infimum.
  have hρlimit : Tendsto ρ atTop (𝓝 qF) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop k] with N hNk
    have hak : a N k = qF k := hAprefix N k hNk
    have hroot₁ : qF 0 = (ρ N) 0 := hqF.1.1.trans (hρvalid N).1.symm
    have hroot₂ : (ρ N) 0 = (a N) 0 := (hρvalid N).1.trans (hAvalid N).1.symm
    have hlow := (pathSoutheastLE_iff_all_times_of_same_root qF (ρ N) hroot₁).mp
      (hFbelowρ N) k
    have hupp := (pathSoutheastLE_iff_all_times_of_same_root (ρ N) (a N) hroot₂).mp
      (hρbelowA N) k
    have hfst : (a N k).1 = (qF k).1 := congrArg Prod.fst hak
    have hsnd : (a N k).2 = (qF k).2 := congrArg Prod.snd hak
    have hfirst : (ρ N k).1 ≤ (qF k).1 := by simpa only [hfst] using hupp.1
    have hsecond : (qF k).2 ≤ (ρ N k).2 := by simpa only [hsnd] using hupp.2
    apply Prod.ext
    · exact le_antisymm hfirst hlow.1
    · exact le_antisymm hlow.2 hsecond

  -- The right-isolated GLB lies below every member of the decreasing sequence.
  have hRbelowρ (N : ℕ) : pathSoutheastLE qR (ρ N) := by
    obtain ⟨j, hj, hjMass⟩ := hρRI N
    rw [hj]
    exact hqR.2.1 j hjMass
  have hClosed : IsClosed
      {b : ℕ → Lattice |
        ∀ k : ℕ, (qR k).1 ≤ (b k).1 ∧ (b k).2 ≤ (qR k).2} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro k
    have hfirst : Continuous (fun b : ℕ → Lattice => (b k).1) :=
      continuous_fst.comp (continuous_apply k)
    have hsecond : Continuous (fun b : ℕ → Lattice => (b k).2) :=
      continuous_snd.comp (continuous_apply k)
    exact (isClosed_le continuous_const hfirst).inter
      (isClosed_le hsecond continuous_const)
  have hRleF : pathSoutheastLE qR qF := by
    apply (pathSoutheastLE_iff_all_times_of_same_root qR qF
      (hqR.1.1.trans hqF.1.1.symm)).mpr
    apply hClosed.mem_of_tendsto hρlimit
    apply Filter.Eventually.of_forall
    intro N
    exact (pathSoutheastLE_iff_all_times_of_same_root qR (ρ N)
      (hqR.1.1.trans (hρvalid N).1.symm)).mp (hRbelowρ N)
  have hEq : qR = qF :=
    southeast_antisymm_same_root qR qF
      (hqR.1.1.trans hqF.1.1.symm) hRleF hFleR
  subst qR

  -- The same path has both complete GLB characterizations.
  refine ⟨qF, ?_, ?_⟩
  · exact ⟨hqF.1, hqR.2.1, hqR.2.2, hqF.2.1, hqF.2.2.1⟩
  · intro q hq
    apply hqRunique q
    exact ⟨hq.1, hq.2.1, hq.2.2.1⟩

end LPP.Busemann
