/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealQuantileJointLaw
public import Busemann.Process.RealQuantileCoalescence
public import Busemann.Process.RealGeodesicCocycles
public import Busemann.Process.CoalescingCocycleRepresentation
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
public import LPP_Foundations.Model.Paths.Coalescence
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Busemann.Process.CoalescingGeodesicCocycle
import Busemann.Process.RightmostPathMeasurability
import Busemann.Process.RightmostPathGeodesic
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory Filter ProbabilityTheory LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The original conditional quantile ray and environment jointly sample the
actual process cocycle, after an internal measurable finite-passage-limit
reconstruction. This raw representative is characterized almost surely and
does not assert exact forward measurability. Strong Existence,
lm:Bs-Bhat, lines 1055–1062. -/
theorem exists_measurable_real_quantile_field_with_original_joint_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B)
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (hqMeas : ∀ u : Lattice, Measurable
      (fun a : Environment × unitInterval => q u a.1 a.2))
    (hqCDF : ∀ᵐ ω ∂environmentLaw μ,
      ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (condDistrib
                (fun a : ProcessSample =>
                  rightmostCocyclePath (fun x y => B x y a) u)
                processEnvironment P) ω
                  {η : ℕ → Lattice | pathSoutheastLE η γ})) :
    ∃ R : Environment × unitInterval → (Lattice → Lattice → ℝ),
      Measurable R ∧
      (((environmentLaw μ).prod (volume : Measure unitInterval)).map
        (fun a : Environment × unitInterval => (a.1, R a))) =
        P.map (fun b : ProcessSample =>
          (processEnvironment b, fun x y : Lattice => B x y b)) ∧
      ∀ᵐ a ∂(environmentLaw μ).prod (volume : Measure unitInterval),
        ∀ u : Lattice,
          has_passage_difference_limits a.1 (q u a.1 a.2) (R a) := by
  classical
  let ν : Measure (Environment × unitInterval) :=
    (environmentLaw μ).prod (volume : Measure unitInterval)
  let Ray := ℕ → Lattice
  let D (x y : Lattice) (n : ℕ) (a : Environment × Ray) : ℝ :=
    lastPassage a.1 x
      (((a.2 n).1 - x.1).toNat, ((a.2 n).2 - x.2).toNat) -
    lastPassage a.1 y
      (((a.2 n).1 - y.1).toNat, ((a.2 n).2 - y.2).toNat)
  let G : Environment × Ray → (Lattice → Lattice → ℝ) :=
    fun a x y => limUnder atTop (fun n => D x y n a)

  -- A variable ray endpoint is countable, so each finite passage term is measurable.
  have hDMeas (x y : Lattice) (n : ℕ) : Measurable (D x y n) := by
    have hVertex : Measurable (fun a : Environment × Ray => a.2 n) :=
      (measurable_pi_apply n).comp measurable_snd
    have hPassMeas (z : Lattice) : Measurable (fun a : Environment × Ray =>
        lastPassage a.1 z
          (((a.2 n).1 - z.1).toNat, ((a.2 n).2 - z.2).toNat)) := by
      let displacement : Lattice → ℕ × ℕ :=
        fun v => ((v.1 - z.1).toNat, (v.2 - z.2).toNat)
      have hDisp : Measurable (fun a : Environment × Ray =>
          displacement (a.2 n)) :=
        (measurable_of_countable displacement).comp hVertex
      have hJoint : Measurable (fun p : (ℕ × ℕ) × Environment =>
          lastPassage p.2 z p.1) := by
        apply measurable_from_prod_countable_right
        intro d
        exact measurable_lastPassage z d
      have hInput : Measurable (fun a : Environment × Ray =>
          (displacement (a.2 n), a.1)) :=
        hDisp.prodMk measurable_fst
      simpa only [Function.comp_def, displacement] using hJoint.comp hInput
    have hEq : D x y n =
        (fun a : Environment × Ray => lastPassage a.1 x
          (((a.2 n).1 - x.1).toNat, ((a.2 n).2 - x.2).toNat)) -
        (fun a : Environment × Ray => lastPassage a.1 y
          (((a.2 n).1 - y.1).toNat, ((a.2 n).2 - y.2).toNat)) := by
      funext a
      simp only [D, Pi.sub_apply]
    rw [hEq]
    exact (hPassMeas x).sub (hPassMeas y)
  have hGMeas : Measurable G := by
    apply Measurable.of_eval
    intro x
    apply Measurable.of_eval
    intro y
    exact (StronglyMeasurable.limUnder
      (fun n => (hDMeas x y n).stronglyMeasurable)).measurable

  let R : Environment × unitInterval → (Lattice → Lattice → ℝ) :=
    fun a => G (a.1, q 0 a.1 a.2)
  have hRMeas : Measurable R :=
    hGMeas.comp (measurable_fst.prodMk (hqMeas 0))

  -- The actual cocycle is the measurable reconstruction of its zero-root ray.
  let rayP (b : ProcessSample) : Ray :=
    rightmostCocyclePath (fun x y => B x y b) 0
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun b : ProcessSample => ((x, y), b)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  have hRayPMeas : Measurable rayP := by
    apply Measurable.of_eval
    intro n
    exact measurable_rightmostCocyclePath B hBMeas 0 n
  have hPairP : Measurable
      (fun b : ProcessSample => (processEnvironment b, rayP b)) :=
    measurable_fst.prodMk hRayPMeas
  have hPairQ : Measurable
      (fun a : Environment × unitInterval => (a.1, q 0 a.1 a.2)) :=
    measurable_fst.prodMk (hqMeas 0)

  have hOriginal : ∀ᵐ b ∂P,
      G (processEnvironment b, rayP b) = (fun x y => B x y b) := by
    filter_upwards [hCoal, hB.1.2.2, hB.2.1] with b hco hadd hrec
    let C : Lattice → Lattice → ℝ := fun x y => B x y b
    let π : Lattice → Ray := fun u =>
      rightmostCocyclePath C u
    have hStart (u : Lattice) : π u 0 = u := by
      simp [π, rightmostCocyclePath]
    have hSteps (u : Lattice) (n : ℕ) :
        π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
          π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)) := by
      simpa only [π, rightmostCocyclePath, Function.iterate_succ_apply'] using
        rightmostCocycleSuccessor_step C (rightmostCocyclePath C u n)
    have hCal (u : Lattice) (n : ℕ) :
        C (π u n) (π u (n + 1)) = processEnvironment b (π u n) := by
      simpa only [C, π, rightmostCocyclePath, Function.iterate_succ_apply'] using
        rightmostCocycleSuccessor_calibrated (processEnvironment b) C hrec
          (rightmostCocyclePath C u n)
    have hPathCoal : ∀ u v : Lattice, ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, π u (m + k) = π v (n + k) := by
      simpa only [π, C] using hco
    have hEventual :=
      eventually_passage_difference_eq_of_coalescing_calibrated_paths
        (processEnvironment b) C hadd hrec π hStart hSteps hCal hPathCoal
    funext x y
    obtain ⟨N, hTail⟩ := hEventual 0 x y
    have hEventually :
        (fun n => D x y n (processEnvironment b, rayP b)) =ᶠ[atTop]
          fun _ => B x y b := by
      filter_upwards [Filter.eventually_atTop.2
        ⟨N, fun n hn => hn⟩] with n hn
      have hIndex : N + (n - N) = n := Nat.add_sub_of_le hn
      have hEq := (hTail (n - N)).2.2
      simpa only [D, rayP, π, C, hIndex] using hEq
    have hTendsto : Tendsto
        (fun n => D x y n (processEnvironment b, rayP b))
        atTop (𝓝 (B x y b)) :=
      (tendsto_const_nhds (x := B x y b)).congr' hEventually.symm
    exact hTendsto.limUnder_eq

  -- Push the actual environment/ray law through the measurable reconstruction.
  let T : Environment × Ray → Environment × (Lattice → Lattice → ℝ) :=
    fun a => (a.1, G a)
  have hTMeas : Measurable T := measurable_fst.prodMk hGMeas
  have hRayLaw :=
    real_rightmost_quantile_joint_law
      μ P hMarginal B hB q hqMeas hqCDF 0
  have hJointLaw :
      ν.map (fun a : Environment × unitInterval => (a.1, R a)) =
        P.map (fun b : ProcessSample =>
          (processEnvironment b, fun x y : Lattice => B x y b)) := by
    calc
      ν.map (fun a : Environment × unitInterval => (a.1, R a)) =
          (ν.map (fun a => (a.1, q 0 a.1 a.2))).map T := by
            rw [Measure.map_map hTMeas hPairQ]
            rfl
      _ = (P.map (fun b => (processEnvironment b, rayP b))).map T := by
            simpa only [ν, rayP] using congrArg (fun m => m.map T) hRayLaw
      _ = P.map (fun b : ProcessSample =>
            (processEnvironment b, fun x y : Lattice => B x y b)) := by
            rw [Measure.map_map hTMeas hPairP]
            apply Measure.map_congr
            filter_upwards [hOriginal] with b hb
            exact Prod.ext rfl hb

  -- On one product event the quantile family has a common finite real field.
  obtain ⟨A, hAmeas, hAfull, hGood⟩ :=
    exists_full_event_unique_real_cocycle_of_coalescing_geodesic_family
      μ hμ hmoment
  have hAae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAfull
  have hAprod : ∀ᵐ a ∂ν, a.1 ∈ A := by
    exact Measure.quasiMeasurePreserving_fst.ae hAae
  have hQGeo : ∀ᵐ a ∂ν, ∀ u : Lattice,
      IsLocallyRightmostGeodesic a.1 u (q u a.1 a.2) := by
    have hLift : ∀ᵐ a ∂ν,
        ∀ (u : Lattice) (s : unitInterval),
          IsLocallyRightmostGeodesic a.1 u (q u a.1 s) ∧
          ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic a.1 u γ →
            (pathSoutheastLE (q u a.1 s) γ ↔
              ENNReal.ofReal (s : ℝ) ≤
                (condDistrib
                  (fun b : ProcessSample =>
                    rightmostCocyclePath (fun x y => B x y b) u)
                  processEnvironment P) a.1
                    {η : ℕ → Lattice | pathSoutheastLE η γ}) := by
      exact Measure.quasiMeasurePreserving_fst.ae hqCDF
    filter_upwards [hLift] with a ha
    intro u
    exact (ha u a.2).1
  have hQCoal : ∀ᵐ a ∂ν, ∀ u v : Lattice,
      ∃ m n : ℕ,
        u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
        ∀ k : ℕ, q u a.1 a.2 (m + k) = q v a.1 a.2 (n + k) :=
    ae_coalescing_real_rightmost_quantile_family
      μ P hMarginal B hB hCoal q hqMeas hqCDF

  refine ⟨R, hRMeas, hJointLaw, ?_⟩
  filter_upwards [hAprod, hQGeo, hQCoal] with a ha hgeo hcoal
  let π : Lattice → Ray := fun u => q u a.1 a.2
  have hGeo (u : Lattice) : IsLocallyRightmostGeodesic a.1 u (π u) :=
    hgeo u
  have hCo (u v : Lattice) : ∃ m n : ℕ,
      u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, π u (m + k) = π v (n + k) :=
    hcoal u v
  obtain ⟨C, hC, _hCUnique⟩ := hGood a.1 ha π hGeo hCo
  have hMono (u : Lattice) : Monotone (π u) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases (hGeo u).2.1 n with he | hn
    · rw [he]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
    · rw [hn]
      constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  have hBound (u : Lattice) (n : ℕ) : u ≤ π u n := by
    have h := hMono u (Nat.zero_le n)
    rw [(hGeo u).1] at h
    exact h
  have hRField (x y : Lattice) : R a x y = C x y := by
    let w : Lattice := x ⊔ y
    obtain ⟨m, n, _halign, hTail⟩ := hCo 0 w
    have hx : x ≤ π 0 m := by
      calc
        x ≤ w := le_sup_left
        _ ≤ π w n := hBound w n
        _ = π 0 m := (hTail 0).symm
    have hy : y ≤ π 0 m := by
      calc
        y ≤ w := le_sup_right
        _ ≤ π w n := hBound w n
        _ = π 0 m := (hTail 0).symm
    have hShifted : Tendsto
        (fun k : ℕ => D x y (k + m) (a.1, π 0))
        atTop (𝓝 (C x y)) := by
      simpa only [D, π, Nat.add_comm] using hC.1 0 x y m hx hy
    have hLimit : Tendsto (fun k => D x y k (a.1, π 0))
        atTop (𝓝 (C x y)) :=
      (tendsto_add_atTop_iff_nat m).1 hShifted
    exact hLimit.limUnder_eq
  intro u x y N hx hy
  have hLimit := hC.1 u x y N hx hy
  simpa only [π, ← hRField x y] using hLimit

end LPP.Busemann
