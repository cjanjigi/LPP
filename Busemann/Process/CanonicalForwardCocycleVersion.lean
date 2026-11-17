/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.CoalescingCocycleRepresentation
import Busemann.Process.CanonicalForwardRayVersion
import Busemann.Process.ForwardLastPassageMeasurability
import Busemann.Process.RightmostPaths
import Busemann.Process.MonotoneCocycleLimitAux
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Lean.Elab.Tactic.Omega

/-!
# Forward version of a canonical coalescing cocycle

A forward version of the selected ray at the coordinatewise minimum of two
starts supplies finite passage differences for the pair. Coalescence makes
these differences eventually equal to the original cocycle increment.
-/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped Topology ENNReal

namespace LPP.Busemann

private theorem forwardWeightSigma_mono {u v : Lattice} (huv : u ≤ v) :
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

private theorem forwardWeightSigma_le_ambient (u : Lattice) :
    forwardWeightSigma u ≤ (inferInstance : MeasurableSpace Environment) := by
  have hRestriction : Measurable
      (fun ω : Environment => fun z : {z : Lattice // u ≤ z} => ω z.val) := by
    apply measurable_pi_iff.mpr
    intro z
    exact measurable_environment_eval z.val
  simpa only [forwardWeightSigma] using hRestriction.comap_le

private theorem measurable_forward_passage_at_random_endpoint
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

-- The named parameters `hmoment`, `hμ` are part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- A canonical coalescing generalized cocycle has a forward-measurable
coalescing version equal to it on one common all-pair almost-sure event.
This is the version conclusion of public Strong Existence, lines 975–1004,
followed by its passage-difference construction at g428, lines 1718–1738. -/
theorem exists_forward_version_of_coalescing_canonical_cocycle
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (B : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : Environment => ω) B)
    (hCoal : HasCoalescingRightmostPaths (environmentLaw μ) B) :
    ∃ C : Lattice → Lattice → Environment → ℝ,
      IsGeneralizedBusemann (environmentLaw μ)
        (fun z ω => environmentTranslationEquiv z ω)
        (fun ω : Environment => ω) C ∧
      HasCoalescingRightmostPaths (environmentLaw μ) C ∧
      IsForwardMeasurable C ∧
      ∀ᵐ ω ∂environmentLaw μ, ∀ x y : Lattice, C x y ω = B x y ω := by
  classical
  let P : Measure Environment := environmentLaw μ

  -- Choose one forward version of the original selected ray at every root.
  have hRayVersions :=
    exists_forwardWeightSigma_version_rightmostCocyclePath μ B hB hCoal
  choose F hFMeas hFEqual using hRayVersions

  -- A finite passage difference uses the same versioned ray for both starts.
  let D (x y : Lattice) (n : ℕ) (ω : Environment) : ℝ :=
    let v := F (x ⊓ y) ω n
    lastPassage ω x ((v.1 - x.1).toNat, (v.2 - x.2).toNat) -
      lastPassage ω y ((v.1 - y.1).toNat, (v.2 - y.2).toNat)
  let C : Lattice → Lattice → Environment → ℝ :=
    fun x y ω => limUnder atTop (fun n => D x y n ω)

  -- Every finite term and its limit are measurable from the common past root.
  have hDMeas (u x y : Lattice) (hux : u ≤ x) (huy : u ≤ y)
      (n : ℕ) :
      @Measurable Environment ℝ (forwardWeightSigma u) inferInstance
        (D x y n) := by
    have hum : u ≤ x ⊓ y := le_inf hux huy
    have hRay : @Measurable Environment (ℕ → Lattice)
        (forwardWeightSigma u) inferInstance (F (x ⊓ y)) :=
      (hFMeas (x ⊓ y)).mono (forwardWeightSigma_mono hum) le_rfl
    have hVertex : @Measurable Environment Lattice
        (forwardWeightSigma u) inferInstance
        (fun ω => F (x ⊓ y) ω n) := (measurable_pi_apply n).comp hRay
    have hX := measurable_forward_passage_at_random_endpoint u x hux _ hVertex
    have hY := measurable_forward_passage_at_random_endpoint u y huy _ hVertex
    exact hX.sub hY
  have hForwardC : IsForwardMeasurable C := by
    intro u x y hux huy
    let : MeasurableSpace Environment := forwardWeightSigma u
    have hMeas (n : ℕ) : Measurable (D x y n) := hDMeas u x y hux huy n
    exact (StronglyMeasurable.limUnder
      (fun n => (hMeas n).stronglyMeasurable)).measurable

  -- The original path family has the start, step, calibration, and
  -- coalescence properties required by the deterministic passage theorem.
  have hOriginal : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      ∃ N : ℕ, ∀ n : ℕ,
        x ≤ rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n) ∧
        y ≤ rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n) ∧
        lastPassage ω x
          ((((rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n)).1 - x.1).toNat),
           (((rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n)).2 - x.2).toNat)) -
        lastPassage ω y
          ((((rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n)).1 - y.1).toNat),
           (((rightmostCocyclePath (fun a b => B a b ω) (x ⊓ y) (N + n)).2 - y.2).toNat)) =
          B x y ω := by
    filter_upwards [hCoal, hB.1.2.2, hB.2.1] with ω hCo hAdd hRec
    let b : Lattice → Lattice → ℝ := fun x y => B x y ω
    let π : Lattice → ℕ → Lattice := fun u n => rightmostCocyclePath b u n
    have hStart : ∀ u : Lattice, π u 0 = u := by
      intro u
      simp [π, rightmostCocyclePath]
    have hSteps : ∀ (u : Lattice) (n : ℕ),
        π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
          π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)) := by
      intro u n
      simpa only [π, rightmostCocyclePath, Function.iterate_succ_apply'] using
        rightmostCocycleSuccessor_step b (rightmostCocyclePath b u n)
    have hCalibration : ∀ (u : Lattice) (n : ℕ),
        b (π u n) (π u (n + 1)) = ω (π u n) := by
      intro u n
      simpa only [π, rightmostCocyclePath, Function.iterate_succ_apply'] using
        rightmostCocycleSuccessor_calibrated ω b hRec
          (rightmostCocyclePath b u n)
    have hPathCoal : ∀ u v : Lattice, ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, π u (m + k) = π v (n + k) := by
      simpa only [π, b] using hCo
    have hEventual :=
      eventually_passage_difference_eq_of_coalescing_calibrated_paths
        ω b hAdd hRec π hStart hSteps hCalibration hPathCoal
    intro x y
    simpa only [π, b] using hEventual (x ⊓ y) x y

  -- All ray versions and all passage identities hold on one event.
  have hAllRays : ∀ᵐ ω ∂P, ∀ u : Lattice,
      rightmostCocyclePath (fun x y => B x y ω) u = F u ω :=
    ae_all_iff.mpr hFEqual
  have hPairEqual : ∀ᵐ ω ∂P, ∀ x y : Lattice,
      C x y ω = B x y ω := by
    filter_upwards [hAllRays, hOriginal] with ω hRay hPass
    intro x y
    obtain ⟨N, hTail⟩ := hPass x y
    have hEventually : (fun n => D x y n ω) =ᶠ[atTop]
        fun _ => B x y ω := by
      filter_upwards [Filter.eventually_atTop.2
        ⟨N, fun n hn => hn⟩] with n hn
      have hIndex : N + (n - N) = n := Nat.add_sub_of_le hn
      have hEq := (hTail (n - N)).2.2
      simpa only [D, hIndex, ← hRay (x ⊓ y)] using hEq
    have hTendsto : Tendsto (fun n => D x y n ω) atTop (𝓝 (B x y ω)) :=
      (tendsto_const_nhds (x := B x y ω)).congr' hEventually.symm
    exact hTendsto.limUnder_eq

  -- Literal joint measurability follows from the constructed pairwise
  -- measurability and countability of signed lattice pairs.
  have hJoint : Measurable
      (fun p : (Lattice × Lattice) × Environment =>
        C p.1.1 p.1.2 p.2) := by
    apply measurable_from_prod_countable_right
    intro xy
    have hSection : @Measurable Environment ℝ (forwardWeightSigma (xy.1 ⊓ xy.2))
        inferInstance (C xy.1 xy.2) :=
      hForwardC (xy.1 ⊓ xy.2) xy.1 xy.2 inf_le_left inf_le_right
    exact hSection.mono (forwardWeightSigma_le_ambient _) le_rfl

  -- The common equality event transfers additivity and environment recovery.
  have hAddC : ∀ᵐ ω ∂P, is_additive (fun x y => C x y ω) := by
    filter_upwards [hPairEqual, hB.1.2.2] with ω heq hadd
    intro x y z
    change C x y ω + C y z ω = C x z ω
    rw [heq x y, heq y z, heq x z]
    exact hadd x y z
  have hRecC : recovers_weight_map_ae P (fun ω => ω) C := by
    filter_upwards [hPairEqual, hB.2.1] with ω heq hrec
    intro x
    change min (C x (x + (1, 0)) ω) (C x (x + (0, 1)) ω) = ω x
    rw [heq x (x + (1, 0)), heq x (x + (0, 1))]
    exact hrec x

  -- Translate the equality event by the measure-preserving environment shift
  -- before transporting the original covariance.
  have hCovC (x y z : Lattice) : ∀ᵐ ω ∂P,
      C (x + z) (y + z) ω =
        C x y (environmentTranslationEquiv z ω) := by
    have hShifted : ∀ᵐ ω ∂P, ∀ a b : Lattice,
        C a b (environmentTranslationEquiv z ω) =
          B a b (environmentTranslationEquiv z ω) :=
      (measurePreserving_environmentTranslationEquiv μ z).quasiMeasurePreserving.ae
        hPairEqual
    filter_upwards [hPairEqual, hShifted, hB.1.2.1 x y z] with ω heq hshift hcov
    rw [heq (x + z) (y + z), hcov, hshift x y]
  have hIntC (x y : Lattice) : Integrable (C x y) P := by
    have hEq : C x y =ᵐ[P] B x y := by
      filter_upwards [hPairEqual] with ω heq
      exact heq x y
    exact (hB.2.2 x y).congr hEq.symm
  have hGeneralized : IsGeneralizedBusemann P
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : Environment => ω) C :=
    ⟨⟨hJoint, hCovC, hAddC⟩, hRecC, hIntC⟩

  -- Equality of every increment makes the two selected path families equal
  -- on the same event, so the original aligned coalescence transfers.
  have hCoalC : HasCoalescingRightmostPaths P C := by
    filter_upwards [hPairEqual, hCoal] with ω heq hcoal
    have hFields : (fun x y => C x y ω) = (fun x y => B x y ω) := by
      funext x y
      exact heq x y
    simpa only [hFields] using hcoal
  exact ⟨C, hGeneralized, hCoalC, hForwardC, hPairEqual⟩

end LPP.Busemann
