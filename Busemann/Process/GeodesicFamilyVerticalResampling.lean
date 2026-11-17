/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicLowerCut
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Geometry.GeodesicConeLocality
import Busemann.Geometry.CrossedGeodesicCoalescenceAtRoots
import Busemann.Geometry.GeodesicOrder
import Busemann.Geometry.GeodesicMeasurability
import LPP_Foundations.Probability.EnvironmentVerticalHalfPlaneCoupling
import ProbabilityBasics.Probability.ErgodicPositiveEventReturns
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! A coalescing family of original-space rays survives vertical half-plane resampling. -/

@[expose] public section
open MeasureTheory LPPDifferentiability Filter

namespace LPP.Busemann

/-- A measurable shift-covariant coalescing family of locally rightmost
geodesics has the same zero-root path after independent resampling left of the
vertical axis, almost surely under the vertical half-plane coupling.
Public Strong Existence, lm:pi-forward, lines 985–999. -/
theorem ae_geodesic_family_eq_vertical_halfPlane_resample
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
          (q.1, fun z : Lattice => if 0 ≤ z.1 then q.1 z else q.2 z))),
      π 0 p.1 = π 0 p.2 := by
  classical
  let P : Measure Environment := environmentLaw μ
  let input : Measure (Environment × Environment) := P.prod P
  let C : Environment × Environment → Environment × Environment :=
    fun q => (q.1, fun z => if 0 ≤ z.1 then q.1 z else q.2 z)
  let Q : Measure (Environment × Environment) := input.map C
  let T : Environment × Environment → Environment × Environment :=
    fun p =>
      (fun z => p.1 (((0 : ℤ), (1 : ℤ)) + z),
       fun z => p.2 (((0 : ℤ), (1 : ℤ)) + z))
  let ray (ω : Environment) (u : Lattice) : ℕ → Lattice :=
    π u ω
  change ∀ᵐ p ∂Q, ray p.1 (0, 0) = ray p.2 (0, 0)

  -- Both correlated outputs have the original iid marginal law.
  have hC : Measurable C := by
    exact measurable_fst.prodMk measurable_vertical_halfPlane_resample
  have hFirstMap : Q.map Prod.fst = P := by
    dsimp [Q, input]
    rw [Measure.map_map measurable_fst hC]
    change (P.prod P).map Prod.fst = P
    simp
  have hSecondMap : Q.map Prod.snd = P := by
    change ((P.prod P).map C).map Prod.snd = P
    exact environmentLaw_vertical_halfPlane_coupling_snd μ
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

  -- The original assumptions hold simultaneously at all signed roots.
  have hOriginal : ∀ᵐ ω ∂P,
      (∀ u : Lattice, IsLocallyRightmostGeodesic ω u (ray ω u)) ∧
      (∀ u v : Lattice, paths_coalesce u v (ray ω u) (ray ω v)) ∧
      (∀ u : Lattice,
        ray ω u = (fun n : ℕ => ray (environmentTranslationEquiv u ω) 0 n + u)) := by
    have hGeoAll : ∀ᵐ ω ∂P, ∀ u : Lattice,
        IsLocallyRightmostGeodesic ω u (ray ω u) :=
      ae_all_iff.mpr (fun u => hGeo u)
    have hCoalAll : ∀ᵐ ω ∂P, ∀ u v : Lattice,
        paths_coalesce u v (ray ω u) (ray ω v) :=
      ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun v => hCoal u v))
    have hShiftAll : ∀ᵐ ω ∂P, ∀ u : Lattice,
        ray ω u = (fun n : ℕ => ray (environmentTranslationEquiv u ω) 0 n + u) :=
      ae_all_iff.mpr (fun u => hShift u)
    filter_upwards [hGeoAll, hCoalAll, hShiftAll] with ω hg hc hs
    exact ⟨hg, hc, hs⟩
  have hFirstOriginal := hFirstAE hOriginal
  have hSecondOriginal := hSecondAE hOriginal

  -- The two outputs agree at every site in the retained vertical half-plane.
  have hUpperMeas : MeasurableSet
      {p : Environment × Environment |
        ∀ z : Lattice, 0 ≤ z.1 → p.1 z = p.2 z} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro z
    exact MeasurableSet.iInter fun _ : 0 ≤ z.1 =>
      measurableSet_eq_fun ((measurable_environment_eval z).comp measurable_fst)
        ((measurable_environment_eval z).comp measurable_snd)
  have hUpperAE : ∀ᵐ p ∂Q,
      ∀ z : Lattice, 0 ≤ z.1 → p.1 z = p.2 z := by
    change ∀ᵐ p ∂input.map C, p ∈
      {p : Environment × Environment | ∀ z : Lattice, 0 ≤ z.1 → p.1 z = p.2 z}
    apply (ae_map_iff hC.aemeasurable hUpperMeas).2
    filter_upwards [] with q
    intro z hz
    simp [C, hz]

  -- The two opposite strict comparisons are measurable.
  have hRayMeas (u : Lattice) : Measurable (fun ω : Environment => ray ω u) := by
    exact hMeas u
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
    exact environmentLaw_vertical_halfPlane_coupling_swap μ
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
      have hgeo1 := hfirst.1 (0, 0)
      have hgeo2 := hsecond.1 (0, 0)
      have hAgreement : Set.EqOn p.1 p.2 (Set.Ici (0, 0)) := by
        intro z hz
        exact hu z hz.1
      have hSets := locallyRightmostGeodesic_set_eq_of_eqOn_Ici
        p.1 p.2 (0, 0) hAgreement
      have hgeo2' : IsLocallyRightmostGeodesic p.1 (0, 0) (ray p.2 (0, 0)) :=
        hSets.symm.subset hgeo2
      rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
        p.1 (0, 0) (ray p.1 (0, 0)) (ray p.2 (0, 0)) hgeo1 hgeo2' with h12 | h21
      · by_contra hne
        exact hna ⟨h12, hne⟩
      · by_contra hne
        exact hna' ⟨h21, Ne.symm hne⟩
    exact hNotEqual hEqual
  have hA'Pos : 0 < Q A' := hAeq ▸ hAPos

  -- Ergodic recurrence supplies visits to both strict-order events.
  have hErgodic : Ergodic T Q := by
    exact ergodic_environmentLaw_vertical_halfPlane_coupling μ
  have hVisitA : ∀ᵐ p ∂Q, ∃ᶠ n in atTop, T^[n] p ∈ A :=
    ProbabilityBasics.ergodic_ae_frequently_iterate_mem Q hErgodic A hAMeas hAPos
  have hVisitA' : ∀ᵐ p ∂Q, ∃ᶠ n in atTop, T^[n] p ∈ A' :=
    ProbabilityBasics.ergodic_ae_frequently_iterate_mem Q hErgodic A' hA'Meas hA'Pos

  -- Natural vertical iterates are actual environment translations.
  have hIterate (n : ℕ) (p : Environment × Environment) :
      T^[n] p =
        (environmentTranslationEquiv ((0 : ℤ), (n : ℤ)) p.1,
         environmentTranslationEquiv ((0 : ℤ), (n : ℤ)) p.2) := by
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
          change p.1 (((0 : ℤ), (n : ℤ)) + (((0 : ℤ), (1 : ℤ)) + z)) =
            p.1 (((0 : ℤ), ((n + 1 : ℕ) : ℤ)) + z)
          apply congrArg p.1
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega
        · funext z
          change p.2 (((0 : ℤ), (n : ℤ)) + (((0 : ℤ), (1 : ℤ)) + z)) =
            p.2 (((0 : ℤ), ((n + 1 : ℕ) : ℤ)) + z)
          apply congrArg p.2
          ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ] <;> omega

  -- Recurrence and coalescence yield incompatible orders at two signed roots.
  have hEqual : ∀ᵐ p ∂Q, ray p.1 (0, 0) = ray p.2 (0, 0) := by
    filter_upwards [hFirstOriginal, hSecondOriginal, hVisitA, hVisitA', hUpperAE]
      with p hfirst hsecond hreturnsA hreturnsA' hu
    obtain ⟨k, _hk, hkA⟩ := (frequently_atTop'.1 hreturnsA) 0
    obtain ⟨ell, _hkell, hellA⟩ := (frequently_atTop'.1 hreturnsA') (k + 1)
    let zk : Lattice := ((0 : ℤ), (k : ℤ))
    let zell : Lattice := ((0 : ℤ), (ell : ℤ))

    -- The supplied shift law translates zero-root rays to signed roots.
    have hPathTranslateFirst (n m : ℕ) :
        ray ((T^[n] p).1) (0, 0) m + ((0 : ℤ), (n : ℤ)) =
          ray p.1 ((0 : ℤ), (n : ℤ)) m := by
      let z : Lattice := ((0 : ℤ), (n : ℤ))
      have ht := congrArg (fun f : ℕ → Lattice => f m) (hfirst.2.2 z)
      rw [hIterate n p]
      exact ht.symm
    have hPathTranslateSecond (n m : ℕ) :
        ray ((T^[n] p).2) (0, 0) m + ((0 : ℤ), (n : ℤ)) =
          ray p.2 ((0 : ℤ), (n : ℤ)) m := by
      let z : Lattice := ((0 : ℤ), (n : ℤ))
      have ht := congrArg (fun f : ℕ → Lattice => f m) (hsecond.2.2 z)
      rw [hIterate n p]
      exact ht.symm

    have hShiftRootFirst (n : ℕ) :
        ray ((T^[n] p).1) (0, 0) 0 = (0, 0) := by
      have ht := hPathTranslateFirst n 0
      rw [(hfirst.1 ((0 : ℤ), (n : ℤ))).1] at ht
      have ht' : ray ((T^[n] p).1) (0, 0) 0 + ((0 : ℤ), (n : ℤ)) =
          (0 : Lattice) + ((0 : ℤ), (n : ℤ)) := by
        simpa only [zero_add] using ht
      exact add_right_cancel ht'
    have hShiftRootSecond (n : ℕ) :
        ray ((T^[n] p).2) (0, 0) 0 = (0, 0) := by
      have ht := hPathTranslateSecond n 0
      rw [(hsecond.1 ((0 : ℤ), (n : ℤ))).1] at ht
      have ht' : ray ((T^[n] p).2) (0, 0) 0 + ((0 : ℤ), (n : ℤ)) =
          (0 : Lattice) + ((0 : ℤ), (n : ℤ)) := by
        simpa only [zero_add] using ht
      exact add_right_cancel ht'

    have hOrderTransport (n : ℕ)
        (h : pathSoutheastLE (ray (T^[n] p).1 (0, 0))
          (ray (T^[n] p).2 (0, 0))) :
        pathSoutheastLE (ray p.1 ((0 : ℤ), (n : ℤ)))
          (ray p.2 ((0 : ℤ), (n : ℤ))) := by
      intro m r hlevel
      have hmr : m = r := by
        have hcast : (m : ℤ) = (r : ℤ) := by
          have hroot1 := (hfirst.1 ((0 : ℤ), (n : ℤ))).1
          have hroot2 := (hsecond.1 ((0 : ℤ), (n : ℤ))).1
          rw [hroot1, hroot2] at hlevel
          simpa using hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by
        rw [hShiftRootFirst n, hShiftRootSecond n])
      have htr1 := hPathTranslateFirst n m
      have htr2 := hPathTranslateSecond n m
      rcases hshiftOrder with ⟨hfst, hsnd⟩
      have hfst1 := congrArg Prod.fst htr1
      have hfst2 := congrArg Prod.fst htr2
      have hsnd1 := congrArg Prod.snd htr1
      have hsnd2 := congrArg Prod.snd htr2
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
        at hfst1 hfst2 hsnd1 hsnd2
      constructor <;> omega
    have hReverseOrderTransport (n : ℕ)
        (h : pathSoutheastLE (ray (T^[n] p).2 (0, 0))
          (ray (T^[n] p).1 (0, 0))) :
        pathSoutheastLE (ray p.2 ((0 : ℤ), (n : ℤ)))
          (ray p.1 ((0 : ℤ), (n : ℤ))) := by
      intro m r hlevel
      have hmr : m = r := by
        have hcast : (m : ℤ) = (r : ℤ) := by
          have hroot1 := (hfirst.1 ((0 : ℤ), (n : ℤ))).1
          have hroot2 := (hsecond.1 ((0 : ℤ), (n : ℤ))).1
          rw [hroot1, hroot2] at hlevel
          simpa using hlevel
        exact_mod_cast hcast
      subst r
      have hshiftOrder := h m m (by
        rw [hShiftRootSecond n, hShiftRootFirst n])
      have htr1 := hPathTranslateFirst n m
      have htr2 := hPathTranslateSecond n m
      rcases hshiftOrder with ⟨hfst, hsnd⟩
      have hfst1 := congrArg Prod.fst htr1
      have hfst2 := congrArg Prod.fst htr2
      have hsnd1 := congrArg Prod.snd htr1
      have hsnd2 := congrArg Prod.snd htr2
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
        at hfst1 hfst2 hsnd1 hsnd2
      constructor <;> omega
    have hDifferentTransport (n : ℕ)
        (h : ray (T^[n] p).1 (0, 0) ≠ ray (T^[n] p).2 (0, 0)) :
        ray p.1 ((0 : ℤ), (n : ℤ)) ≠ ray p.2 ((0 : ℤ), (n : ℤ)) := by
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

    -- The vertical cone transfers the second output's actual rays into the first.
    have hGeoFirst (u : Lattice) :
        IsLocallyRightmostGeodesic p.1 u (ray p.1 u) :=
      hfirst.1 u
    have hGeoSecond (u : Lattice) :
        IsLocallyRightmostGeodesic p.2 u (ray p.2 u) :=
      hsecond.1 u
    have hGeoTransferred (n : ℕ) :
        IsLocallyRightmostGeodesic p.1 ((0 : ℤ), (n : ℤ))
          (ray p.2 ((0 : ℤ), (n : ℤ))) := by
      have hAgreement :
          Set.EqOn p.1 p.2 (Set.Ici ((0 : ℤ), (n : ℤ))) := by
        intro z hz
        exact hu z hz.1
      have hSets := locallyRightmostGeodesic_set_eq_of_eqOn_Ici
        p.1 p.2 ((0 : ℤ), (n : ℤ)) hAgreement
      exact hSets.symm.subset (hGeoSecond ((0 : ℤ), (n : ℤ)))

    -- Opposite orders and the middle coalescence contradict outer coalescence.
    have hMiddle := hsecond.2.1 zk zell
    have hOuter := hfirst.2.1 zk zell
    have hNoOuter := no_outer_coalescence_of_crossed_locallyRightmost_rays_at_roots
      p.1 zk zell
      (ray p.1 zk) (ray p.2 zk) (ray p.2 zell) (ray p.1 zell)
      (hGeoFirst zk) (hGeoTransferred k) (hGeoTransferred ell)
      (hGeoFirst zell) hkOrder hellOrder hMiddle
    exact False.elim (hNoOuter hOuter)
  exact hNotEqual hEqual

end LPP.Busemann
