/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CoalescingCocycleRepresentation
public import Busemann.Geometry.HalfPlaneGeodesicOrder
public import Busemann.Geometry.HalfPlaneGeodesicLocality
public import Busemann.Geometry.CrossedGeodesicCoalescence
public import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingErgodic
public import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingSymmetry
import Busemann.Process.RightmostPathMeasurability
import Busemann.Process.RightmostPathCovariance
import Busemann.Process.RightmostPathGeodesic
import Busemann.Geometry.GeodesicMeasurability
import ProbabilityBasics.Probability.ErgodicPositiveEventReturns
import Mathlib.MeasureTheory.Measure.Prod
import Lean.Elab.Tactic.Omega

/-! The original selected zero-root ray survives resampling below the axis. -/

@[expose] public section
open MeasureTheory LPPDifferentiability Filter
namespace LPP.Busemann

/-- The canonical selected zero-root ray is unchanged almost surely when the
environment below the horizontal axis is independently resampled. Public
Strong Existence, lines 985–998. -/
theorem ae_rightmostCocyclePath_eq_horizontal_halfPlane_resample
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : Environment => ω) B)
    (hCoal : HasCoalescingRightmostPaths (environmentLaw μ) B) :
    ∀ᵐ p : Environment × Environment ∂
      (((environmentLaw μ).prod (environmentLaw μ)).map
        (fun q : Environment × Environment =>
          (q.1, fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z))),
      rightmostCocyclePath (fun x y => B x y p.1) (0, 0) =
        rightmostCocyclePath (fun x y => B x y p.2) (0, 0) := by
  classical
  let P : Measure Environment := environmentLaw μ
  let input : Measure (Environment × Environment) := P.prod P
  let C : Environment × Environment → Environment × Environment :=
    fun q => (q.1, fun z => if 0 ≤ z.2 then q.1 z else q.2 z)
  let Q : Measure (Environment × Environment) := input.map C
  let T : Environment × Environment → Environment × Environment :=
    fun p => (fun z => p.1 ((1, 0) + z), fun z => p.2 ((1, 0) + z))
  let ray (ω : Environment) (u : Lattice) : ℕ → Lattice :=
    rightmostCocyclePath (fun x y => B x y ω) u
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

  -- The cocycle section is measurable, and its covariance is made simultaneous.
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hSection : Measurable (fun ω : Environment => ((x, y), ω)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hB.1.1.comp hSection
  have hCovAE : ∀ᵐ ω ∂P, ∀ z x y : Lattice,
      B (x + z) (y + z) ω = B x y (environmentTranslationEquiv z ω) := by
    exact ae_all_iff.mpr fun z => ae_all_iff.mpr fun x =>
      ae_all_iff.mpr fun y => hB.1.2.1 x y z
  have hOriginal : ∀ᵐ ω ∂P,
      is_additive (fun x y => B x y ω) ∧
      recovers_environment ω (fun x y => B x y ω) ∧
      (∀ u v : Lattice, ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ q : ℕ, ray ω u (m + q) = ray ω v (n + q)) ∧
      (∀ z x y : Lattice,
        B (x + z) (y + z) ω = B x y (environmentTranslationEquiv z ω)) := by
    filter_upwards [hB.1.2.2, hB.2.1, hCoal, hCovAE] with ω ha hr hc hv
    exact ⟨ha, hr, hc, hv⟩
  have hFirstOriginal := hFirstAE hOriginal
  have hSecondOriginal := hSecondAE hOriginal
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

  -- The two opposite strict comparisons are measurable.
  have hRayMeas (u : Lattice) : Measurable (fun ω : Environment => ray ω u) := by
    apply Measurable.of_eval
    intro n
    exact measurable_rightmostCocyclePath B hBMeas u n
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
      filter_upwards [hAE_A, hAE_A', hFirstOriginal, hSecondOriginal, hUpperAE]
        with p hna hna' hfirst hsecond hu
      have hgeo1 := isLocallyRightmostGeodesic_rightmostCocyclePath
        p.1 (fun x y => B x y p.1) hfirst.1 hfirst.2.1 (0, 0)
      have hgeo2 := isLocallyRightmostGeodesic_rightmostCocyclePath
        p.2 (fun x y => B x y p.2) hsecond.1 hsecond.2.1 (0, 0)
      rcases pathSoutheastLE_total_of_nonnegative_height_agreement
        p.1 p.2 hu _ _ hgeo1 hgeo2 with h12 | h21
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
    filter_upwards [hFirstOriginal, hSecondOriginal, hVisitA, hVisitA', hUpperAE]
      with p hfirst hsecond hreturnsA hreturnsA' hu
    obtain ⟨k, _hk, hkA⟩ := (frequently_atTop'.1 hreturnsA) 0
    obtain ⟨ell, hkell, hellA⟩ := (frequently_atTop'.1 hreturnsA') (k + 1)
    have hkell' : k < ell := by omega
    let zk : Lattice := ((k : ℤ), 0)
    let zell : Lattice := ((ell : ℤ), 0)
    have hzkell : (k : ℤ) < (ell : ℤ) := by exact_mod_cast hkell'

  -- Covariance identifies shifted zero-root rays with rays from signed roots.
    have hPathTranslateFirst (n m : ℕ) :
      ray ((T^[n] p).1) (0, 0) m + ((n : ℤ), 0) =
        ray p.1 ((n : ℤ), 0) m := by
      let z : Lattice := ((n : ℤ), 0)
      have hD (x y : Lattice) :
          B x y ((T^[n] p).1) = B (x + z) (y + z) p.1 := by
        rw [hIterate n p]
        exact (hfirst.2.2.2 z x y).symm
      simpa [ray, z] using rightmostCocyclePath_translate
        (fun x y => B x y p.1) (fun x y => B x y ((T^[n] p).1)) z
        hD (0, 0) m
    have hPathTranslateSecond (n m : ℕ) :
      ray ((T^[n] p).2) (0, 0) m + ((n : ℤ), 0) =
        ray p.2 ((n : ℤ), 0) m := by
      let z : Lattice := ((n : ℤ), 0)
      have hD (x y : Lattice) :
          B x y ((T^[n] p).2) = B (x + z) (y + z) p.2 := by
        rw [hIterate n p]
        exact (hsecond.2.2.2 z x y).symm
      simpa [ray, z] using rightmostCocyclePath_translate
        (fun x y => B x y p.2) (fun x y => B x y ((T^[n] p).2)) z
        hD (0, 0) m

    have hOrderTransport (n : ℕ)
      (h : pathSoutheastLE (ray (T^[n] p).1 (0, 0))
        (ray (T^[n] p).2 (0, 0))) :
      pathSoutheastLE (ray p.1 ((n : ℤ), 0))
        (ray p.2 ((n : ℤ), 0)) := by
      intro m r hlevel
      have hmr : m = r := by
        have hcast : (m : ℤ) = (r : ℤ) := by
          simpa only [ray, rightmostCocyclePath, Function.iterate_zero_apply,
            Prod.fst_add, Prod.snd_add, add_zero, zero_add,
            add_left_cancel_iff] using hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by simp [ray, rightmostCocyclePath])
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
          simpa only [ray, rightmostCocyclePath, Function.iterate_zero_apply,
            Prod.fst_add, Prod.snd_add, add_zero, zero_add,
            add_left_cancel_iff] using hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by simp [ray, rightmostCocyclePath])
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
      isLocallyRightmostGeodesic_rightmostCocyclePath p.1
        (fun x y => B x y p.1) hfirst.1 hfirst.2.1 u
    have hGeoSecond (u : Lattice) :
      IsLocallyRightmostGeodesic p.2 u (ray p.2 u) :=
      isLocallyRightmostGeodesic_rightmostCocyclePath p.2
        (fun x y => B x y p.2) hsecond.1 hsecond.2.1 u
    have hGeoTransferred (n : ℕ) :
      IsLocallyRightmostGeodesic p.1 ((n : ℤ), 0)
        (ray p.2 ((n : ℤ), 0)) := by
      have hSets := locallyRightmostGeodesic_set_eq_of_nonnegative_height_agreement
        p.1 p.2 hu (n : ℤ)
      exact hSets.symm.subset (hGeoSecond ((n : ℤ), 0))

  -- Opposite orders and the middle coalescence contradict outer coalescence.
    have hMiddle := hsecond.2.2.1 zk zell
    have hOuter := hfirst.2.2.1 zk zell
    have hNoOuter := no_outer_coalescence_of_crossed_locallyRightmost_rays
      p.1 (k : ℤ) (ell : ℤ) hzkell
      (ray p.1 zk) (ray p.2 zk) (ray p.2 zell) (ray p.1 zell)
      (hGeoFirst zk) (hGeoTransferred k) (hGeoTransferred ell)
      (hGeoFirst zell) hkOrder hellOrder hMiddle
    exact False.elim (hNoOuter hOuter)
  exact hNotEqual hEqual

end LPP.Busemann
