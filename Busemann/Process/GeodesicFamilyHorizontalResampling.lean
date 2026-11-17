/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicLowerCut
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Geometry.HalfPlaneGeodesicOrder
import Busemann.Geometry.HalfPlaneGeodesicLocality
import Busemann.Geometry.CrossedGeodesicCoalescence
import Busemann.Geometry.GeodesicMeasurability
import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingErgodic
import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingSymmetry
import ProbabilityBasics.Probability.ErgodicPositiveEventReturns
import Mathlib.MeasureTheory.Measure.Prod
import Lean.Elab.Tactic.Omega

/-! A generic measurable shift-covariant family of locally rightmost
geodesics has the same zero-root path after resampling below the horizontal
axis, almost surely under the horizontal half-plane coupling. -/

@[expose] public section
open MeasureTheory LPPDifferentiability Filter
namespace LPP.Busemann

/-- A measurable shift-covariant coalescing family of locally rightmost
geodesics has the same zero-root path after independent resampling below the
horizontal axis. Public Strong Existence, lines 985–999. -/
theorem ae_geodesic_family_eq_horizontal_halfPlane_resample
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (π : Lattice → Environment → (ℕ → Lattice))
    (hMeas : ∀ u : Lattice, Measurable (π u))
    (hGeo : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      IsLocallyRightmostGeodesic ω u (π u ω))
    (hShift : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u))
    (hCoal : ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      paths_coalesce u v (π u ω) (π v ω)) :
    ∀ᵐ p : Environment × Environment ∂
      (((environmentLaw μ).prod (environmentLaw μ)).map
        (fun q : Environment × Environment =>
          (q.1, fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z))),
      π 0 p.1 = π 0 p.2 := by
  classical
  let P : Measure Environment := environmentLaw μ
  let input : Measure (Environment × Environment) := P.prod P
  let C : Environment × Environment → Environment × Environment :=
    fun q => (q.1, fun z => if 0 ≤ z.2 then q.1 z else q.2 z)
  let Q : Measure (Environment × Environment) := input.map C
  let T : Environment × Environment → Environment × Environment :=
    fun p => (fun z => p.1 ((1, 0) + z), fun z => p.2 ((1, 0) + z))
  let ray (ω : Environment) (u : Lattice) : ℕ → Lattice := π u ω
  change ∀ᵐ p ∂Q, ray p.1 (0, 0) = ray p.2 (0, 0)

  -- Both correlated outputs have the original iid marginal law.
  have hC : Measurable C := by
    exact measurable_fst.prodMk measurable_horizontal_halfPlane_resample
  have hFirstMap : Q.map Prod.fst = P := by
    dsimp [Q, input]
    rw [Measure.map_map measurable_fst hC]
    change (P.prod P).map Prod.fst = P
    simp
  have hSecondMap : Q.map Prod.snd = P := by
    dsimp [Q, input]
    rw [Measure.map_map measurable_snd hC]
    change input.map
      (fun q : Environment × Environment =>
        fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z) = P
    exact environmentLaw_map_horizontal_halfPlane_resample μ
  have hFirstAE {R : Environment → Prop} (hR : ∀ᵐ ω ∂P, R ω) :
      ∀ᵐ p ∂Q, R p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hFirstMap]
    exact hR
  have hSecondAE {R : Environment → Prop} (hR : ∀ᵐ ω ∂P, R ω) :
      ∀ᵐ p ∂Q, R p.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hSecondMap]
    exact hR

  -- Countability makes the supplied geodesic, shift, and coalescence facts
  -- simultaneous over all signed roots of one environment.
  have hGeoAll : ∀ᵐ ω ∂P, ∀ u : Lattice,
      IsLocallyRightmostGeodesic ω u (π u ω) := by
    exact ae_all_iff.mpr fun u => hGeo u
  have hShiftAll : ∀ᵐ ω ∂P, ∀ u : Lattice,
      π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u) := by
    exact ae_all_iff.mpr fun u => hShift u
  have hCoalAll : ∀ᵐ ω ∂P, ∀ u v : Lattice,
      paths_coalesce u v (π u ω) (π v ω) := by
    exact ae_all_iff.mpr fun u => ae_all_iff.mpr fun v => hCoal u v
  have hFirstGeo := hFirstAE hGeoAll
  have hSecondGeo := hSecondAE hGeoAll
  have hFirstShift := hFirstAE hShiftAll
  have hSecondShift := hSecondAE hShiftAll
  have hFirstCoal := hFirstAE hCoalAll
  have hSecondCoal := hSecondAE hCoalAll
  have hUpperMeas : MeasurableSet
      {p : Environment × Environment |
        ∀ z : Lattice, 0 ≤ z.2 → p.1 z = p.2 z} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro z
    exact MeasurableSet.iInter fun _ : 0 ≤ z.2 =>
      measurableSet_eq_fun ((measurable_environment_eval z).comp measurable_fst)
        ((measurable_environment_eval z).comp measurable_snd)
  have hUpperAE : ∀ᵐ p ∂Q,
      ∀ z : Lattice, 0 ≤ z.2 → p.1 z = p.2 z := by
    change ∀ᵐ p ∂input.map C, p ∈
      {p : Environment × Environment | ∀ z : Lattice, 0 ≤ z.2 → p.1 z = p.2 z}
    apply (ae_map_iff hC.aemeasurable hUpperMeas).2
    filter_upwards [] with q
    intro z hz
    exact horizontal_halfPlane_resample_apply_nonneg q z hz |>.symm

  -- Family measurability makes the two opposite strict comparisons measurable.
  have hRayMeas (u : Lattice) : Measurable (fun ω : Environment => ray ω u) :=
    hMeas u
  have hPairMeas : Measurable (fun p : Environment × Environment =>
      (ray p.1 (0, 0), ray p.2 (0, 0))) :=
    (hRayMeas (0, 0)).comp measurable_fst |>.prodMk
      ((hRayMeas (0, 0)).comp measurable_snd)
  let A : Set (Environment × Environment) :=
    {p | pathSoutheastLE (ray p.1 (0, 0)) (ray p.2 (0, 0)) ∧
      ray p.1 (0, 0) ≠ ray p.2 (0, 0)}
  let A' : Set (Environment × Environment) :=
    {p | pathSoutheastLE (ray p.2 (0, 0)) (ray p.1 (0, 0)) ∧
      ray p.2 (0, 0) ≠ ray p.1 (0, 0)}
  have hEqMeas : MeasurableSet
      {p : Environment × Environment | ray p.1 (0, 0) = ray p.2 (0, 0)} := by
    have hf : Measurable (fun p : Environment × Environment => ray p.1 (0, 0)) :=
      (hRayMeas (0, 0)).comp measurable_fst
    have hg : Measurable (fun p : Environment × Environment => ray p.2 (0, 0)) :=
      (hRayMeas (0, 0)).comp measurable_snd
    exact measurableSet_eq_fun hf hg
  have hAMeas : MeasurableSet A :=
    (measurableSet_pathSoutheastLE.preimage hPairMeas).inter hEqMeas.compl
  have hA'Meas : MeasurableSet A' := by
    have hSwapPair : Measurable (fun p : Environment × Environment =>
        (ray p.2 (0, 0), ray p.1 (0, 0))) := hPairMeas.comp measurable_swap
    have hReverseEq : MeasurableSet
        {p : Environment × Environment | ray p.2 (0, 0) = ray p.1 (0, 0)} := by
      simpa only [eq_comm] using hEqMeas
    exact (measurableSet_pathSoutheastLE.preimage hSwapPair).inter hReverseEq.compl

  -- Positive disagreement gives positive mass to both directions by exchangeability.
  have hSwap : Q = Q.map Prod.swap := by
    exact environmentLaw_horizontal_halfPlane_coupling_swap μ
  by_contra hNotEqual
  have hAeq : Q A = Q A' := by
    calc
      Q A = (Q.map Prod.swap) A := by rw [← hSwap]
      _ = Q A' := by
        rw [Measure.map_apply measurable_swap hAMeas]
        rfl
  have hAPos : 0 < Q A := by
    by_contra hNotPos
    have hZero : Q A = 0 := le_antisymm (le_of_not_gt hNotPos) zero_le
    have hZero' : Q A' = 0 := hAeq.symm.trans hZero
    have hAE_A : ∀ᵐ p ∂Q, p ∉ A := measure_eq_zero_iff_ae_notMem.mp hZero
    have hAE_A' : ∀ᵐ p ∂Q, p ∉ A' := measure_eq_zero_iff_ae_notMem.mp hZero'
    have hEqual : ∀ᵐ p ∂Q, ray p.1 (0, 0) = ray p.2 (0, 0) := by
      filter_upwards [hAE_A, hAE_A', hFirstGeo, hSecondGeo, hUpperAE]
        with p hna hna' hfirst hsecond hu
      rcases pathSoutheastLE_total_of_nonnegative_height_agreement
        p.1 p.2 hu _ _ (hfirst (0, 0)) (hsecond (0, 0)) with h12 | h21
      · by_contra hne
        exact hna ⟨h12, hne⟩
      · by_contra hne
        exact hna' ⟨h21, Ne.symm hne⟩
    exact hNotEqual hEqual
  have hA'Pos : 0 < Q A' := hAeq ▸ hAPos

  -- Ergodic recurrence supplies a first visit and a later opposite visit.
  have hErgodic : Ergodic T Q := by
    exact ergodic_environmentLaw_horizontal_halfPlane_coupling μ
  have hVisitA : ∀ᵐ p ∂Q, ∃ᶠ n in atTop, T^[n] p ∈ A :=
    ProbabilityBasics.ergodic_ae_frequently_iterate_mem Q hErgodic A hAMeas hAPos
  have hVisitA' : ∀ᵐ p ∂Q, ∃ᶠ n in atTop, T^[n] p ∈ A' :=
    ProbabilityBasics.ergodic_ae_frequently_iterate_mem Q hErgodic A' hA'Meas hA'Pos

  -- Natural horizontal iterates agree with the actual environment translations.
  have hIterate (n : ℕ) (p : Environment × Environment) :
      T^[n] p =
        (environmentTranslationEquiv ((n : ℤ), 0) p.1,
         environmentTranslationEquiv ((n : ℤ), 0) p.2) := by
    induction n with
    | zero =>
        apply Prod.ext
        · funext z
          change p.1 z = p.1 ((0 : Lattice) + z)
          simp
        · funext z
          change p.2 z = p.2 ((0 : Lattice) + z)
          simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        apply Prod.ext
        · funext z
          change p.1 (((n : ℤ), 0) + ((1, 0) + z)) =
            p.1 ((((n + 1 : ℕ) : ℤ), 0) + z)
          apply congrArg p.1
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
        · funext z
          change p.2 (((n : ℤ), 0) + ((1, 0) + z)) =
            p.2 ((((n + 1 : ℕ) : ℤ), 0) + z)
          apply congrArg p.2
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

  -- The full marginal events and recurrence events have a common witness.
  have hEqual : ∀ᵐ p ∂Q, ray p.1 (0, 0) = ray p.2 (0, 0) := by
    filter_upwards [hFirstGeo, hSecondGeo, hFirstShift, hSecondShift,
      hFirstCoal, hSecondCoal, hVisitA, hVisitA', hUpperAE]
      with p hfirstGeo hsecondGeo hfirstShift hsecondShift
        hfirstCoal hsecondCoal hreturnsA hreturnsA' hu
    obtain ⟨k, _hk, hkA⟩ := (frequently_atTop'.1 hreturnsA) 0
    obtain ⟨ell, hkell, hellA⟩ := (frequently_atTop'.1 hreturnsA') (k + 1)
    have hkell' : k < ell := by omega
    let zk : Lattice := ((k : ℤ), 0)
    let zell : Lattice := ((ell : ℤ), 0)
    have hzkell : (k : ℤ) < (ell : ℤ) := by exact_mod_cast hkell'

  -- The supplied shift identity identifies translated zero-root rays with
  -- rays from signed roots.
    have hZero : (0 : Lattice) = (0, 0) := by
      ext <;> simp
    have hPathTranslateFirst (n m : ℕ) :
      ray ((T^[n] p).1) (0, 0) m + ((n : ℤ), 0) =
        ray p.1 ((n : ℤ), 0) m := by
      let z : Lattice := ((n : ℤ), 0)
      have hEnv : environmentTranslationEquiv z p.1 = (T^[n] p).1 := by
        simpa [z] using (congrArg Prod.fst (hIterate n p)).symm
      have hAtRoot := congrFun (hfirstShift z) m
      rw [hEnv] at hAtRoot
      rw [hZero] at hAtRoot
      simpa [ray, z] using hAtRoot.symm
    have hPathTranslateSecond (n m : ℕ) :
      ray ((T^[n] p).2) (0, 0) m + ((n : ℤ), 0) =
        ray p.2 ((n : ℤ), 0) m := by
      let z : Lattice := ((n : ℤ), 0)
      have hEnv : environmentTranslationEquiv z p.2 = (T^[n] p).2 := by
        simpa [z] using (congrArg Prod.snd (hIterate n p)).symm
      have hAtRoot := congrFun (hsecondShift z) m
      rw [hEnv] at hAtRoot
      rw [hZero] at hAtRoot
      simpa [ray, z] using hAtRoot.symm
    have hRootShiftFirst (n : ℕ) :
        ray ((T^[n] p).1) (0, 0) 0 = (0, 0) := by
      let z : Lattice := ((n : ℤ), 0)
      have hAtRoot := hPathTranslateFirst n 0
      have hGeoRoot : ray p.1 z 0 = z := by
        simpa [ray] using (hfirstGeo z).1
      rw [hGeoRoot] at hAtRoot
      have hCancel : ray ((T^[n] p).1) (0, 0) 0 + z = (0 : Lattice) + z := by
        simpa only [zero_add] using hAtRoot
      exact add_right_cancel hCancel
    have hRootShiftSecond (n : ℕ) :
        ray ((T^[n] p).2) (0, 0) 0 = (0, 0) := by
      let z : Lattice := ((n : ℤ), 0)
      have hAtRoot := hPathTranslateSecond n 0
      have hGeoRoot : ray p.2 z 0 = z := by
        simpa [ray] using (hsecondGeo z).1
      rw [hGeoRoot] at hAtRoot
      have hCancel : ray ((T^[n] p).2) (0, 0) 0 + z = (0 : Lattice) + z := by
        simpa only [zero_add] using hAtRoot
      exact add_right_cancel hCancel
    have hRootAtFirst (n : ℕ) :
        ray p.1 ((n : ℤ), 0) 0 = ((n : ℤ), 0) := by
      simpa [ray] using (hfirstGeo ((n : ℤ), 0)).1
    have hRootAtSecond (n : ℕ) :
        ray p.2 ((n : ℤ), 0) 0 = ((n : ℤ), 0) := by
      simpa [ray] using (hsecondGeo ((n : ℤ), 0)).1

    have hOrderTransport (n : ℕ)
      (h : pathSoutheastLE (ray (T^[n] p).1 (0, 0))
        (ray (T^[n] p).2 (0, 0))) :
      pathSoutheastLE (ray p.1 ((n : ℤ), 0))
        (ray p.2 ((n : ℤ), 0)) := by
      intro m r hlevel
      have hmr : m = r := by
        have hcast : (m : ℤ) = (r : ℤ) := by
          rw [hRootAtFirst n, hRootAtSecond n] at hlevel
          exact add_left_cancel hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by
        simp only [hRootShiftFirst n, hRootShiftSecond n, zero_add])
      have htr1 := hPathTranslateFirst n m
      have htr2 := hPathTranslateSecond n m
      rcases hshiftOrder with ⟨hfst, hsnd⟩
      have hfst1 := congrArg Prod.fst htr1
      have hfst2 := congrArg Prod.fst htr2
      have hsnd1 := congrArg Prod.snd htr1
      have hsnd2 := congrArg Prod.snd htr2
      simp only [Prod.fst_add, Prod.snd_add, add_zero] at hfst1 hfst2 hsnd1 hsnd2
      constructor <;> omega
    have hReverseOrderTransport (n : ℕ)
      (h : pathSoutheastLE (ray (T^[n] p).2 (0, 0))
        (ray (T^[n] p).1 (0, 0))) :
      pathSoutheastLE (ray p.2 ((n : ℤ), 0))
        (ray p.1 ((n : ℤ), 0)) := by
      intro m r hlevel
      have hmr : m = r := by
        have hcast : (m : ℤ) = (r : ℤ) := by
          rw [hRootAtSecond n, hRootAtFirst n] at hlevel
          exact add_left_cancel hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by
        simp only [hRootShiftFirst n, hRootShiftSecond n, zero_add])
      have htr1 := hPathTranslateFirst n m
      have htr2 := hPathTranslateSecond n m
      rcases hshiftOrder with ⟨hfst, hsnd⟩
      have hfst1 := congrArg Prod.fst htr1
      have hfst2 := congrArg Prod.fst htr2
      have hsnd1 := congrArg Prod.snd htr1
      have hsnd2 := congrArg Prod.snd htr2
      simp only [Prod.fst_add, Prod.snd_add, add_zero] at hfst1 hfst2 hsnd1 hsnd2
      constructor <;> omega
    have hDifferentTransport (n : ℕ)
      (h : ray (T^[n] p).1 (0, 0) ≠ ray (T^[n] p).2 (0, 0)) :
      ray p.1 ((n : ℤ), 0) ≠ ray p.2 ((n : ℤ), 0) := by
      intro heq
      apply h
      funext m
      have htr1 := hPathTranslateFirst n m
      have htr2 := hPathTranslateSecond n m
      rw [heq] at htr1
      exact add_right_cancel (htr1.trans htr2.symm)
    have hkOrder : pathSoutheastLE (ray p.1 zk) (ray p.2 zk) ∧
      ray p.1 zk ≠ ray p.2 zk := by
      exact ⟨hOrderTransport k hkA.1, hDifferentTransport k hkA.2⟩
    have hellOrder : pathSoutheastLE (ray p.2 zell) (ray p.1 zell) ∧
      ray p.2 zell ≠ ray p.1 zell := by
      exact ⟨hReverseOrderTransport ell hellA.1,
        (hDifferentTransport ell hellA.2.symm).symm⟩

  -- The full geodesic set transfers from the second output to the first.
    have hGeoFirst (u : Lattice) :
      IsLocallyRightmostGeodesic p.1 u (ray p.1 u) :=
      hfirstGeo u
    have hGeoSecond (u : Lattice) :
      IsLocallyRightmostGeodesic p.2 u (ray p.2 u) :=
      hsecondGeo u
    have hGeoTransferred (n : ℕ) :
      IsLocallyRightmostGeodesic p.1 ((n : ℤ), 0)
        (ray p.2 ((n : ℤ), 0)) := by
      have hSets := locallyRightmostGeodesic_set_eq_of_nonnegative_height_agreement
        p.1 p.2 hu (n : ℤ)
      exact hSets.symm.subset (hGeoSecond ((n : ℤ), 0))

  -- Opposite orders and the middle coalescence contradict outer coalescence.
    have hMiddle := hsecondCoal zk zell
    have hOuter := hfirstCoal zk zell
    have hNoOuter := no_outer_coalescence_of_crossed_locallyRightmost_rays
      p.1 (k : ℤ) (ell : ℤ) hzkell
      (ray p.1 zk) (ray p.2 zk) (ray p.2 zell) (ray p.1 zell)
      (hGeoFirst zk) (hGeoTransferred k) (hGeoTransferred ell)
      (hGeoFirst zell) hkOrder hellOrder hMiddle
    exact False.elim (hNoOuter hOuter)
  exact hNotEqual hEqual

end LPP.Busemann
