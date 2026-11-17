/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CalibratedPaths
public import Busemann.Frozen.Definitions.GeneralizedBusemann
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Probability.TranslationEquiv
public import Mathlib.Topology.Instances.Real.Lemmas
public import LPP_Foundations.Model.Paths.Coalescence
import Busemann.Process.RightmostPaths
import Busemann.Process.RightmostPathCoalescenceApplications
import Lean.Elab.Tactic.Omega

/-! Eventual exact passage representation from calibrated coalescing paths. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

private theorem exists_ray_prefix_offset
    (π : Lattice → ℕ → Lattice)
    (hstart : ∀ u : Lattice, π u 0 = u)
    (hsteps : ∀ (u : Lattice) (n : ℕ),
      π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
        π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)))
    (u : Lattice) (N : ℕ) :
    ∃ k : ℕ, k ≤ N ∧
      π u N = u + ((k : ℤ), ((N - k : ℕ) : ℤ)) := by
  induction N with
  | zero =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hstart u]
      ext <;> simp only [Prod.fst_add, Prod.snd_add]
      all_goals omega
  | succ N ih =>
      obtain ⟨k, hk, hendpoint⟩ := ih
      rcases hsteps u N with hEast | hNorth
      · refine ⟨k + 1, by omega, ?_⟩
        rw [hEast, hendpoint]
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals omega
      · refine ⟨k, by omega, ?_⟩
        rw [hNorth, hendpoint]
        ext <;> simp only [Prod.fst_add, Prod.snd_add]
        all_goals omega

private theorem ray_prefix_passage_eq
    (ω : Environment) (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (π : Lattice → ℕ → Lattice)
    (hstart : ∀ u : Lattice, π u 0 = u)
    (hsteps : ∀ (u : Lattice) (n : ℕ),
      π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
        π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)))
    (hcal : ∀ (u : Lattice) (n : ℕ),
      C (π u n) (π u (n + 1)) = ω (π u n))
    (u : Lattice) (N : ℕ) :
    u ≤ π u N ∧
      lastPassage ω u
        (((π u N).1 - u.1).toNat, ((π u N).2 - u.2).toNat) = C u (π u N) := by
  classical
  obtain ⟨k, hk, hendpoint⟩ :=
    exists_ray_prefix_offset π hstart hsteps u N
  have hlength : k + (N - k) = N := by omega
  let p : LPPDifferentiability.Path u (k, N - k) := {
    vertex := fun i => π u i.val
    start := by simpa using hstart u
    finish := by
      simpa only [Fin.val_last, hlength] using hendpoint
    step := by
      intro i
      simpa only [Fin.val_succ, Fin.val_castSucc] using hsteps u i.val
  }
  have hpathCalibration :
      ∀ i : Fin (k + (N - k)),
        C (p.vertex i.castSucc) (p.vertex i.succ) =
          ω (p.vertex i.castSucc) := by
    intro i
    simpa only [p, Fin.val_succ, Fin.val_castSucc] using hcal u i.val
  have hweights := calibrated_path_weight_eq_and_maximizing ω C hC hrec
    u (k, N - k) p hpathCalibration
  have hdisplacement :
      (((π u N).1 - u.1).toNat, ((π u N).2 - u.2).toNat) =
        (k, N - k) := by
    rw [hendpoint]
    ext <;> simp
  constructor
  · rw [hendpoint]
    constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  · rw [hdisplacement]
    calc
      lastPassage ω u (k, N - k) = pathWeight ω p := hweights.2.symm
      _ = C u (u + ((k : ℤ), ((N - k : ℕ) : ℤ))) := hweights.1
      _ = C u (π u N) := by rw [← hendpoint]

/-- For any family of calibrated up-right rays whose tails coalesce with
absolute levels aligned, passage differences eventually equal the cocycle
increment, for all signed starts and arbitrary tie choices. Strong Existence,
g428, lines 1718–1738. -/
theorem eventually_passage_difference_eq_of_coalescing_calibrated_paths
    (ω : LPPDifferentiability.Environment)
    (C : Lattice → Lattice → ℝ)
    (hC : is_additive C) (hrec : recovers_environment ω C)
    (π : Lattice → ℕ → Lattice)
    (hstart : ∀ u : Lattice, π u 0 = u)
    (hsteps : ∀ (u : Lattice) (n : ℕ),
      π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
        π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)))
    (hcal : ∀ (u : Lattice) (n : ℕ),
      C (π u n) (π u (n + 1)) = ω (π u n))
    (hcoal : ∀ u v : Lattice, paths_coalesce u v (π u) (π v)) :
    ∀ u x y : Lattice, ∃ N : ℕ, ∀ n : ℕ,
      x ≤ π u (N + n) ∧ y ≤ π u (N + n) ∧
      lastPassage ω x
          (((π u (N + n)).1 - x.1).toNat,
           ((π u (N + n)).2 - x.2).toNat) -
        lastPassage ω y
          (((π u (N + n)).1 - y.1).toNat,
           ((π u (N + n)).2 - y.2).toNat) = C x y := by
  classical
  intro u x y
  obtain ⟨m₁, n₁, _hlevel₁, htail₁⟩ := hcoal u x
  obtain ⟨m₂, n₂, _hlevel₂, htail₂⟩ := hcoal u y
  let M : ℕ := max m₁ m₂
  have hm₁M : m₁ ≤ M := by dsimp [M]; exact le_max_left _ _
  have hm₂M : m₂ ≤ M := by dsimp [M]; exact le_max_right _ _
  let jx : ℕ → ℕ := fun n => n₁ + (M - m₁ + n)
  let jy : ℕ → ℕ := fun n => n₂ + (M - m₂ + n)
  have htailX (n : ℕ) : π u (M + n) = π x (jx n) := by
    have h := htail₁ (M - m₁ + n)
    have hindex : m₁ + (M - m₁ + n) = M + n := by omega
    simpa only [jx, hindex] using h
  have htailY (n : ℕ) : π u (M + n) = π y (jy n) := by
    have h := htail₂ (M - m₂ + n)
    have hindex : m₂ + (M - m₂ + n) = M + n := by omega
    simpa only [jy, hindex] using h
  refine ⟨M, ?_⟩
  intro n
  have hprefixX := ray_prefix_passage_eq ω C hC hrec π hstart hsteps hcal x (jx n)
  have hprefixY := ray_prefix_passage_eq ω C hC hrec π hstart hsteps hcal y (jy n)
  have hpassX :
      lastPassage ω x
          (((π u (M + n)).1 - x.1).toNat,
           ((π u (M + n)).2 - x.2).toNat) = C x (π u (M + n)) := by
    rw [htailX n]
    exact hprefixX.2
  have hpassY :
      lastPassage ω y
          (((π u (M + n)).1 - y.1).toNat,
           ((π u (M + n)).2 - y.2).toNat) = C y (π u (M + n)) := by
    rw [htailY n]
    exact hprefixY.2
  refine ⟨?_, ?_, ?_⟩
  · rw [htailX n]
    exact hprefixX.1
  · rw [htailY n]
    exact hprefixY.1
  · calc
      _ = C x (π u (M + n)) - C y (π u (M + n)) := by
        rw [hpassX, hpassY]
      _ = C x y := by linarith [hC x y (π u (M + n))]

/-- For a supplied fixed canonical forward cocycle, one common almost-sure
event represents every increment by passage differences at every common
valid entry. Strong Existence, g428, lines 1718–1738. -/
theorem ae_rightmostCocyclePath_passage_difference_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (B : Lattice → Lattice → LPPDifferentiability.Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : LPPDifferentiability.Environment => ω) B)
    (hForward : IsForwardMeasurable B) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ u x y : Lattice, ∀ N : ℕ,
      x ≤ rightmostCocyclePath (fun a b => B a b ω) u N →
      y ≤ rightmostCocyclePath (fun a b => B a b ω) u N →
      Tendsto (fun n : ℕ =>
        lastPassage ω x
            (((rightmostCocyclePath (fun a b => B a b ω) u (N + n)).1 - x.1).toNat,
             ((rightmostCocyclePath (fun a b => B a b ω) u (N + n)).2 - x.2).toNat) -
          lastPassage ω y
            (((rightmostCocyclePath (fun a b => B a b ω) u (N + n)).1 - y.1).toNat,
             ((rightmostCocyclePath (fun a b => B a b ω) u (N + n)).2 - y.2).toNat))
        atTop (𝓝 (B x y ω)) := by
  classical
  have hCoalescence : HasCoalescingRightmostPaths (environmentLaw μ) B :=
    hasCoalescingRightmostPaths_environmentLaw_of_isForwardMeasurable
      μ hμ hmoment B hB.1 hB.2.1
      (hB.2.2 0 (1, 0)) (hB.2.2 0 (0, 1)) hForward
  filter_upwards [hCoalescence, hB.1.2.2, hB.2.1] with ω hCo hAdd hRec
  let C : Lattice → Lattice → ℝ := fun x y => B x y ω
  let π : Lattice → ℕ → Lattice := fun u n =>
    rightmostCocyclePath (fun x y => B x y ω) u n
  have hC : is_additive C := by simpa only [C] using hAdd
  have hrec : recovers_environment ω C := by simpa only [C] using hRec
  have hstart : ∀ u : Lattice, π u 0 = u := by
    intro u
    simp [π, rightmostCocyclePath]
  have hsteps : ∀ (u : Lattice) (n : ℕ),
      π u (n + 1) = π u n + ((1 : ℤ), (0 : ℤ)) ∨
        π u (n + 1) = π u n + ((0 : ℤ), (1 : ℤ)) := by
    intro u n
    simpa only [π, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step (fun x y => B x y ω)
        (rightmostCocyclePath (fun x y => B x y ω) u n)
  have hcal : ∀ (u : Lattice) (n : ℕ),
      C (π u n) (π u (n + 1)) = ω (π u n) := by
    intro u n
    simpa only [C, π, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_calibrated ω C hrec
        (rightmostCocyclePath C u n)
  have hcoal : ∀ u v : Lattice, paths_coalesce u v (π u) (π v) := by
    simpa only [π, C, paths_coalesce] using hCo
  have hrepresentation :=
    eventually_passage_difference_eq_of_coalescing_calibrated_paths
      ω C hC hrec π hstart hsteps hcal hcoal
  intro u x y N _hxN _hyN
  obtain ⟨N₀, htail⟩ := hrepresentation u x y
  have hEventuallyEq :
      (fun n : ℕ =>
        lastPassage ω x
            (((π u (N + n)).1 - x.1).toNat,
             ((π u (N + n)).2 - x.2).toNat) -
          lastPassage ω y
            (((π u (N + n)).1 - y.1).toNat,
             ((π u (N + n)).2 - y.2).toNat)) =ᶠ[atTop]
        fun _ : ℕ => C x y := by
    filter_upwards [Filter.eventually_atTop.2
      ⟨N₀ - N, fun n hn => hn⟩] with n hn
    have hlarge : N₀ ≤ N + n := by omega
    have hindex : N₀ + (N + n - N₀) = N + n := Nat.add_sub_of_le hlarge
    have htailEq := htail (N + n - N₀)
    simpa only [hindex] using htailEq.2.2
  have hconst : Tendsto (fun _ : ℕ => C x y) atTop (𝓝 (C x y)) :=
    tendsto_const_nhds
  have hlimit := Filter.Tendsto.congr' hEventuallyEq.symm hconst
  simpa only [π, C] using hlimit

end LPP.Busemann
