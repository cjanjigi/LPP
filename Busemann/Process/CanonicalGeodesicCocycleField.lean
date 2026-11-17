/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RealGeodesicCocycles
public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.RecoveryAE
public import LPP_Foundations.Probability.TranslationEquiv
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.Paths.Coalescence
public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Process.CoalescingGeodesicCocycle
import Busemann.Process.ForwardGeodesicFamily
import Busemann.Process.CoalescingCocycleRepresentation
import Busemann.Process.ForwardLastPassageMeasurability
import LPP_Foundations.Model.LastPassage.Translate
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Lean.Elab.Tactic.Omega

/-! A supplied coalescing family on the original environment gives one forward
measurable real cocycle with passage limits at every root. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

private theorem forwardSigma_mono_for_family {u v : Lattice} (huv : u ≤ v) :
    forwardWeightSigma v ≤ forwardWeightSigma u := by
  let : MeasurableSpace Environment := forwardWeightSigma u
  have hRestriction : Measurable
      (fun ω : Environment => fun z : {z : Lattice // v ≤ z} => ω z.val) := by
    apply measurable_pi_iff.mpr
    intro z
    let w : {w : Lattice // u ≤ w} := ⟨z.val, huv.trans z.property⟩
    have hCone : Measurable
        (fun ω : Environment => fun t : {t : Lattice // u ≤ t} => ω t.val) :=
      comap_measurable _
    exact (measurable_pi_apply w).comp hCone
  exact hRestriction.comap_le

private theorem forwardSigma_le_ambient_for_family (u : Lattice) :
    forwardWeightSigma u ≤ (inferInstance : MeasurableSpace Environment) := by
  have hRestriction : Measurable
      (fun ω : Environment => fun z : {z : Lattice // u ≤ z} => ω z.val) := by
    apply measurable_pi_iff.mpr
    intro z
    exact measurable_environment_eval z.val
  simpa only [forwardWeightSigma] using hRestriction.comap_le

private theorem measurable_forward_passage_family_endpoint
    (u x : Lattice) (hux : u ≤ x)
    (V : Environment → Lattice)
    (hV : @Measurable Environment Lattice (forwardWeightSigma u)
      inferInstance V) :
    @Measurable Environment ℝ (forwardWeightSigma u) inferInstance
      (fun ω => lastPassage ω x
        (((V ω).1 - x.1).toNat, ((V ω).2 - x.2).toNat)) := by
  let : MeasurableSpace Environment := forwardWeightSigma u
  let displacement : Lattice → ℕ × ℕ :=
    fun z => ((z.1 - x.1).toNat, (z.2 - x.2).toNat)
  have hDisplacement : Measurable (fun ω => displacement (V ω)) :=
    (measurable_of_countable displacement).comp hV
  have hJoint : Measurable
      (fun p : (ℕ × ℕ) × Environment => lastPassage p.2 x p.1) := by
    apply measurable_from_prod_countable_right
    intro d
    exact measurable_forward_lastPassage_of_le u x hux d
  change Measurable
    ((fun p : (ℕ × ℕ) × Environment => lastPassage p.2 x p.1) ∘
      fun ω => (displacement (V ω), ω))
  exact hJoint.comp (hDisplacement.prodMk measurable_id)

private theorem translated_passage_family (ω : Environment) (z a v : Lattice) :
    lastPassage ω (a + z)
      (((v + z).1 - (a + z).1).toNat,
       ((v + z).2 - (a + z).2).toNat) =
      lastPassage (environmentTranslationEquiv z ω) a
        ((v.1 - a.1).toNat, (v.2 - a.2).toNat) := by
  have hDisplacement :
      (((v + z).1 - (a + z).1).toNat,
       ((v + z).2 - (a + z).2).toNat) =
      ((v.1 - a.1).toNat, (v.2 - a.2).toNat) := by
    congr 1 <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  rw [hDisplacement]
  calc
    lastPassage ω (a + z)
        ((v.1 - a.1).toNat, (v.2 - a.2).toNat) =
        lastPassage ω (z + a)
          ((v.1 - a.1).toNat, (v.2 - a.2).toNat) := by
            rw [add_comm a z]
    _ = lastPassage (fun t => ω (z + t)) a
          ((v.1 - a.1).toNat, (v.2 - a.2).toNat) :=
      (lastPassage_translate ω z a
        ((v.1 - a.1).toNat, (v.2 - a.2).toNat)).symm
    _ = lastPassage (environmentTranslationEquiv z ω) a
          ((v.1 - a.1).toNat, (v.2 - a.2).toNat) := by rfl

/-- One original measurable, covariant, coalescing geodesic family determines
an almost-surely characterized environment cocycle with a forward-measurable
version. Strong Existence, B-def, B_u and lm:B-cK, lines 1007–1038. -/
theorem exists_forward_real_cocycle_of_coalescing_geodesic_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (π : Lattice → Environment → (ℕ → Lattice))
    (hMeas : ∀ u : Lattice, Measurable (π u))
    (hGeo : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      IsLocallyRightmostGeodesic ω u (π u ω))
    (hShift : ∀ u : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      π u ω = (fun n : ℕ => π 0 (environmentTranslationEquiv u ω) n + u))
    (hCoal : ∀ u v : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      paths_coalesce u v (π u ω) (π v ω)) :
    ∃ C : Lattice → Lattice → Environment → ℝ,
      is_shift_covariant_cocycle (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω) C ∧
      recovers_weight_map_ae (environmentLaw μ)
        (fun ω : Environment => ω) C ∧
      IsForwardMeasurable C ∧
      ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
        has_passage_difference_limits ω (π u ω) (fun x y => C x y ω) := by
  classical
  let P : Measure Environment := environmentLaw μ

  obtain ⟨A, hAmeas, hAone, hAfield⟩ :=
    exists_full_event_unique_real_cocycle_of_coalescing_geodesic_family
      μ hμ hmoment
  have hAae : ∀ᵐ ω ∂P, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAone
  have hGeoAll : ∀ᵐ ω ∂P, ∀ u : Lattice,
      IsLocallyRightmostGeodesic ω u (π u ω) :=
    ae_all_iff.mpr hGeo
  have hCoalAll : ∀ᵐ ω ∂P, ∀ u v : Lattice,
      paths_coalesce u v (π u ω) (π v ω) :=
    ae_all_iff.mpr fun u => ae_all_iff.mpr (hCoal u)

  have hCoalOld (u v : Lattice) : ∀ᵐ ω ∂P,
      ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, (π u ω) (m + k) = (π v ω) (n + k) := by
    filter_upwards [hCoal u v] with ω hω
    exact hω

  -- Select the forward versions of this same original-space family.
  have hVersions :=
    exists_forwardWeightSigma_versions_of_coalescing_geodesic_family
      μ π hMeas hGeo hShift hCoalOld
  choose F hFMeas hFEq using hVersions
  have hFAll : ∀ᵐ ω ∂P, ∀ u : Lattice, π u ω = F u ω :=
    ae_all_iff.mpr hFEq

  let D (x y : Lattice) (n : ℕ) (ω : Environment) : ℝ :=
    let v := F (x ⊓ y) ω n
    lastPassage ω x ((v.1 - x.1).toNat, (v.2 - x.2).toNat) -
      lastPassage ω y ((v.1 - y.1).toNat, (v.2 - y.2).toNat)
  let C : Lattice → Lattice → Environment → ℝ :=
    fun x y ω => limUnder atTop (fun n => D x y n ω)

  -- A finite passage at the versioned random endpoint reads only forward weights.
  have hDMeas (u x y : Lattice) (hux : u ≤ x) (huy : u ≤ y)
      (n : ℕ) :
      @Measurable Environment ℝ (forwardWeightSigma u) inferInstance
        (D x y n) := by
    have hum : u ≤ x ⊓ y := le_inf hux huy
    have hRay : @Measurable Environment (ℕ → Lattice)
        (forwardWeightSigma u) inferInstance (F (x ⊓ y)) :=
      (hFMeas (x ⊓ y)).mono (forwardSigma_mono_for_family hum) le_rfl
    have hVertex : @Measurable Environment Lattice
        (forwardWeightSigma u) inferInstance
        (fun ω => F (x ⊓ y) ω n) := (measurable_pi_apply n).comp hRay
    have hX := measurable_forward_passage_family_endpoint u x hux _ hVertex
    have hY := measurable_forward_passage_family_endpoint u y huy _ hVertex
    exact hX.sub hY
  have hForwardC : IsForwardMeasurable C := by
    intro u x y hux huy
    let : MeasurableSpace Environment := forwardWeightSigma u
    have hMeasD (n : ℕ) : Measurable (D x y n) :=
      hDMeas u x y hux huy n
    exact (StronglyMeasurable.limUnder
      (fun n => (hMeasD n).stronglyMeasurable)).measurable
  have hJoint : Measurable
      (fun p : (Lattice × Lattice) × Environment =>
        C p.1.1 p.1.2 p.2) := by
    apply measurable_from_prod_countable_right
    intro xy
    have hSection : @Measurable Environment ℝ
        (forwardWeightSigma (xy.1 ⊓ xy.2)) inferInstance
        (C xy.1 xy.2) :=
      hForwardC (xy.1 ⊓ xy.2) xy.1 xy.2 inf_le_left inf_le_right
    exact hSection.mono (forwardSigma_le_ambient_for_family _) le_rfl

  -- The finite field and calibrated-tail identity identify C on one event.
  have hMain : ∀ᵐ ω ∂P,
      (∀ u : Lattice,
        has_passage_difference_limits ω (π u ω) (fun x y => C x y ω)) ∧
      (∀ u x y : Lattice, ∃ N : ℕ, ∀ n : ℕ,
        x ≤ π u ω (N + n) ∧ y ≤ π u ω (N + n)) ∧
      is_additive (fun x y => C x y ω) ∧
      recovers_environment ω (fun x y => C x y ω) := by
    filter_upwards [hAae, hGeoAll, hCoalAll, hFAll] with ω hAω hGω hCoω hFω
    obtain ⟨B, hB, _hUnique⟩ :=
      hAfield ω hAω (fun u => π u ω) hGω hCoω
    have hStart (u : Lattice) : π u ω 0 = u := (hGω u).1
    have hSteps (u : Lattice) : ∀ n : ℕ,
        π u ω (n + 1) = π u ω n + ((1 : ℤ), (0 : ℤ)) ∨
          π u ω (n + 1) = π u ω n + ((0 : ℤ), (1 : ℤ)) :=
      (hGω u).2.1
    have hTail :=
      eventually_passage_difference_eq_of_coalescing_calibrated_paths
        ω B hB.2.1 hB.2.2.1 (fun u => π u ω)
        hStart hSteps hB.2.2.2 hCoω
    have hEq (x y : Lattice) : C x y ω = B x y := by
      obtain ⟨N, hN⟩ := hTail (x ⊓ y) x y
      have hEventually : (fun n => D x y n ω) =ᶠ[atTop]
          fun _ => B x y := by
        filter_upwards [Filter.eventually_atTop.2
          ⟨N, fun n hn => hn⟩] with n hn
        have hIndex : N + (n - N) = n := Nat.add_sub_of_le hn
        have hPass := (hN (n - N)).2.2
        simpa only [D, hIndex, ← hFω (x ⊓ y)] using hPass
      have hTendsto : Tendsto (fun n => D x y n ω) atTop (𝓝 (B x y)) :=
        (tendsto_const_nhds (x := B x y)).congr' hEventually.symm
      exact hTendsto.limUnder_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u x y N hx hy
      simpa only [hEq x y] using hB.1 u x y N hx hy
    · intro u x y
      obtain ⟨N, hN⟩ := hTail u x y
      exact ⟨N, fun n => ⟨(hN n).1, (hN n).2.1⟩⟩
    · intro x y z
      change C x y ω + C y z ω = C x z ω
      rw [hEq x y, hEq y z, hEq x z]
      exact hB.2.1 x y z
    · intro x
      change min (C x (x + (1, 0)) ω) (C x (x + (0, 1)) ω) = ω x
      rw [hEq x (x + (1, 0)), hEq x (x + (0, 1))]
      exact hB.2.2.1 x

  -- Translate both passage limits along the same ray; uniqueness gives covariance.
  have hCov (x y z : Lattice) : ∀ᵐ ω ∂P,
      C (x + z) (y + z) ω = C x y (environmentTranslationEquiv z ω) := by
    have hTranslated : ∀ᵐ ω ∂P,
        (∀ u : Lattice,
          has_passage_difference_limits (environmentTranslationEquiv z ω)
            (π u (environmentTranslationEquiv z ω))
            (fun x y => C x y (environmentTranslationEquiv z ω))) ∧
        (∀ u x y : Lattice, ∃ N : ℕ, ∀ n : ℕ,
          x ≤ π u (environmentTranslationEquiv z ω) (N + n) ∧
          y ≤ π u (environmentTranslationEquiv z ω) (N + n)) ∧
        is_additive (fun a b => C a b (environmentTranslationEquiv z ω)) ∧
        recovers_environment (environmentTranslationEquiv z ω)
          (fun a b => C a b (environmentTranslationEquiv z ω)) :=
      (measurePreserving_environmentTranslationEquiv μ z).quasiMeasurePreserving.ae hMain
    filter_upwards [hMain, hShift z, hTranslated] with ω hω hShiftω hTw
    obtain ⟨N, hN⟩ := hTw.2.1 0 x y
    have hx : x ≤ π 0 (environmentTranslationEquiv z ω) N := by
      simpa only [Nat.add_zero] using (hN 0).1
    have hy : y ≤ π 0 (environmentTranslationEquiv z ω) N := by
      simpa only [Nat.add_zero] using (hN 0).2
    have hRay (n : ℕ) : π z ω n =
        π 0 (environmentTranslationEquiv z ω) n + z :=
      congrFun hShiftω n
    have hxz : x + z ≤ π z ω N := by
      rw [hRay N]
      rcases hx with ⟨hx₁, hx₂⟩
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    have hyz : y + z ≤ π z ω N := by
      rw [hRay N]
      rcases hy with ⟨hy₁, hy₂⟩
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    have hSeq (n : ℕ) :
        lastPassage ω (x + z)
          ((((π z ω) (N + n)).1 - (x + z).1).toNat,
           (((π z ω) (N + n)).2 - (x + z).2).toNat) -
        lastPassage ω (y + z)
          ((((π z ω) (N + n)).1 - (y + z).1).toNat,
           (((π z ω) (N + n)).2 - (y + z).2).toNat) =
        lastPassage (environmentTranslationEquiv z ω) x
          ((((π 0 (environmentTranslationEquiv z ω)) (N + n)).1 - x.1).toNat,
           (((π 0 (environmentTranslationEquiv z ω)) (N + n)).2 - x.2).toNat) -
        lastPassage (environmentTranslationEquiv z ω) y
          ((((π 0 (environmentTranslationEquiv z ω)) (N + n)).1 - y.1).toNat,
           (((π 0 (environmentTranslationEquiv z ω)) (N + n)).2 - y.2).toNat) := by
      rw [hRay (N + n)]
      rw [translated_passage_family ω z x
        (π 0 (environmentTranslationEquiv z ω) (N + n))]
      rw [translated_passage_family ω z y
        (π 0 (environmentTranslationEquiv z ω) (N + n))]
    have hLeft := hω.1 z (x + z) (y + z) N hxz hyz
    have hRight := hTw.1 0 x y N hx hy
    have hEqual :
        (fun n : ℕ =>
          lastPassage ω (x + z)
            ((((π z ω) (N + n)).1 - (x + z).1).toNat,
             (((π z ω) (N + n)).2 - (x + z).2).toNat) -
          lastPassage ω (y + z)
            ((((π z ω) (N + n)).1 - (y + z).1).toNat,
             (((π z ω) (N + n)).2 - (y + z).2).toNat)) =
        (fun n : ℕ =>
          lastPassage (environmentTranslationEquiv z ω) x
            ((((π 0 (environmentTranslationEquiv z ω)) (N + n)).1 - x.1).toNat,
             (((π 0 (environmentTranslationEquiv z ω)) (N + n)).2 - x.2).toNat) -
          lastPassage (environmentTranslationEquiv z ω) y
            ((((π 0 (environmentTranslationEquiv z ω)) (N + n)).1 - y.1).toNat,
             (((π 0 (environmentTranslationEquiv z ω)) (N + n)).2 - y.2).toNat)) :=
      funext fun n => hSeq n
    rw [hEqual] at hLeft
    exact tendsto_nhds_unique hLeft hRight

  have hAdd : ∀ᵐ ω ∂P, is_additive (fun x y => C x y ω) := by
    filter_upwards [hMain] with ω hω
    exact hω.2.2.1
  have hRec : recovers_weight_map_ae P (fun ω => ω) C := by
    filter_upwards [hMain] with ω hω
    exact hω.2.2.2
  have hCocycle : is_shift_covariant_cocycle P
      (fun z ω => environmentTranslationEquiv z ω) C :=
    ⟨hJoint, hCov, hAdd⟩
  have hLimits : ∀ᵐ ω ∂P, ∀ u x y : Lattice, ∀ N : ℕ,
      x ≤ π u ω N → y ≤ π u ω N →
      Tendsto (fun n : ℕ =>
        lastPassage ω x
          ((((π u ω) (N + n)).1 - x.1).toNat,
           (((π u ω) (N + n)).2 - x.2).toNat) -
        lastPassage ω y
          ((((π u ω) (N + n)).1 - y.1).toNat,
           (((π u ω) (N + n)).2 - y.2).toNat))
        atTop (𝓝 (C x y ω)) := by
    filter_upwards [hMain] with ω hω
    exact hω.1
  exact ⟨C, hCocycle, hRec, hForwardC, hLimits⟩

end LPP.Busemann
