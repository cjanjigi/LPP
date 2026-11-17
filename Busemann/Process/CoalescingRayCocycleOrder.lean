/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicCocycleOrder
public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Process.CoalescingCocycleRepresentation
public import Busemann.Frozen.Definitions.GeneralizedBusemann
public import Busemann.Frozen.Definitions.CoalescingRightmostPaths
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Probability.TranslationEquiv
import Busemann.Process.RightmostPathGeodesic
import Mathlib.Order.Filter.AtTopBot.Basic
import Lean.Elab.Tactic.Omega

/-! The edge order induced by coalescing, ordered canonical rightmost rays. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

-- Meeting rays started arbitrarily far east or north forces both coordinates
-- of every ray to leave each signed threshold.
private theorem rightmost_coordinates_escape_of_all_root_coalescence
    (C : Lattice → Lattice → ℝ)
    (hcoal : ∀ u v : Lattice, ∃ m n : ℕ,
      u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
      ∀ k : ℕ, rightmostCocyclePath C u (m + k) =
        rightmostCocyclePath C v (n + k))
    (u : Lattice) :
    Tendsto (fun n : ℕ => (rightmostCocyclePath C u n).1) atTop atTop ∧
      Tendsto (fun n : ℕ => (rightmostCocyclePath C u n).2) atTop atTop := by
  have hmono (v : Lattice) : Monotone (rightmostCocyclePath C v) := by
    apply monotone_nat_of_le_succ
    intro n
    rcases rightmostCocycleSuccessor_step C (rightmostCocyclePath C v n) with
      hEast | hNorth
    · simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
        (show rightmostCocyclePath C v n ≤
          rightmostCocycleSuccessor C (rightmostCocyclePath C v n) by
            rw [hEast]
            constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)
    · simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
        (show rightmostCocyclePath C v n ≤
          rightmostCocycleSuccessor C (rightmostCocyclePath C v n) by
            rw [hNorth]
            constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)
  constructor
  · apply tendsto_atTop.2
    intro b
    obtain ⟨m, n, _hlevel, htail⟩ := hcoal u (b, 0)
    apply Filter.eventually_atTop.2
    refine ⟨m, ?_⟩
    intro k hk
    have hroot : b ≤
        (rightmostCocyclePath C (b, 0) n).1 := by
      have hle := hmono (b, 0) (Nat.zero_le n)
      simpa only [rightmostCocyclePath, Function.iterate_zero, id_eq] using hle.1
    have hmeet : rightmostCocyclePath C u m =
        rightmostCocyclePath C (b, 0) n := by
      simpa only [Nat.add_zero] using htail 0
    have hlarge := (hmono u hk).1
    rw [hmeet] at hlarge
    exact le_trans hroot hlarge
  · apply tendsto_atTop.2
    intro b
    obtain ⟨m, n, _hlevel, htail⟩ := hcoal u (0, b)
    apply Filter.eventually_atTop.2
    refine ⟨m, ?_⟩
    intro k hk
    have hroot : (b : ℤ) ≤
        (rightmostCocyclePath C (0, b) n).2 := by
      have hle := hmono (0, b) (Nat.zero_le n)
      simpa only [rightmostCocyclePath, Function.iterate_zero, id_eq] using hle.2
    have hmeet : rightmostCocyclePath C u m =
        rightmostCocyclePath C (0, b) n := by
      simpa only [Nat.add_zero] using htail 0
    have hlarge := (hmono u hk).2
    rw [hmeet] at hlarge
    exact le_trans hroot hlarge

/-- The published crossing comparison and calibrated passage-difference
representation turn a global ray orientation into opposite edge order. -/
theorem ae_cocycle_opposite_edge_order_of_rightmostPath_order
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B C : Lattice → Lattice → Environment → ℝ)
    (hB : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) B)
    (hC : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) (fun ω => ω) C)
    (hCoalB : HasCoalescingRightmostPaths (environmentLaw μ) B)
    (hCoalC : HasCoalescingRightmostPaths (environmentLaw μ) C)
    (hPaths : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
      pathSoutheastLE
        (rightmostCocyclePath (fun x y => B x y ω) u)
        (rightmostCocyclePath (fun x y => C x y ω) u)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ x : Lattice,
      C x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
        B x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
      B x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
        C x (x + ((0 : ℤ), (1 : ℤ))) ω := by
  classical
  filter_upwards [hB.1.2.2, hB.2.1, hCoalB,
    hC.1.2.2, hC.2.1, hCoalC, hPaths] with
    ω hAddB hRecB hMeetB hAddC hRecC hMeetC hOrder
  let D : Lattice → Lattice → ℝ := fun x y => B x y ω
  let E : Lattice → Lattice → ℝ := fun x y => C x y ω
  let γ : Lattice → ℕ → Lattice := fun u n => rightmostCocyclePath D u n
  let π : Lattice → ℕ → Lattice := fun u n => rightmostCocyclePath E u n
  have hGeoB (u : Lattice) : IsLocallyRightmostGeodesic ω u (γ u) :=
    isLocallyRightmostGeodesic_rightmostCocyclePath ω D hAddB hRecB u
  have hGeoC (u : Lattice) : IsLocallyRightmostGeodesic ω u (π u) :=
    isLocallyRightmostGeodesic_rightmostCocyclePath ω E hAddC hRecC u
  have hEscapeB (u : Lattice) :
      Tendsto (fun n : ℕ => (γ u n).1) atTop atTop ∧
        Tendsto (fun n : ℕ => (γ u n).2) atTop atTop :=
    rightmost_coordinates_escape_of_all_root_coalescence D hMeetB u
  have hEscapeC (u : Lattice) :
      Tendsto (fun n : ℕ => (π u n).1) atTop atTop ∧
        Tendsto (fun n : ℕ => (π u n).2) atTop atTop :=
    rightmost_coordinates_escape_of_all_root_coalescence E hMeetC u
  have hCalB : ∀ (u : Lattice) (n : ℕ),
      D (γ u n) (γ u (n + 1)) = ω (γ u n) := by
    intro u n
    simpa only [γ, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_calibrated ω D hRecB (γ u n)
  have hCalC : ∀ (u : Lattice) (n : ℕ),
      E (π u n) (π u (n + 1)) = ω (π u n) := by
    intro u n
    simpa only [π, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_calibrated ω E hRecC (π u n)
  have hRepB := eventually_passage_difference_eq_of_coalescing_calibrated_paths
    ω D hAddB hRecB γ (fun u => (hGeoB u).1)
    (fun u => (hGeoB u).2.1) hCalB hMeetB
  have hRepC := eventually_passage_difference_eq_of_coalescing_calibrated_paths
    ω E hAddC hRecC π (fun u => (hGeoC u).1)
    (fun u => (hGeoC u).2.1) hCalC hMeetC
  have hLimitB (u x y : Lattice) (N : ℕ)
      (_hx : x ≤ γ u N) (_hy : y ≤ γ u N) :
      Tendsto (fun n : ℕ =>
        lastPassage ω x (((γ u (N + n)).1 - x.1).toNat,
          ((γ u (N + n)).2 - x.2).toNat) -
        lastPassage ω y (((γ u (N + n)).1 - y.1).toNat,
          ((γ u (N + n)).2 - y.2).toNat)) atTop (𝓝 (D x y)) := by
    obtain ⟨M, hM⟩ := hRepB u x y
    have hEq : (fun n : ℕ =>
        lastPassage ω x (((γ u (N + n)).1 - x.1).toNat,
          ((γ u (N + n)).2 - x.2).toNat) -
        lastPassage ω y (((γ u (N + n)).1 - y.1).toNat,
          ((γ u (N + n)).2 - y.2).toNat)) =ᶠ[atTop] fun _ => D x y := by
      filter_upwards [Filter.eventually_atTop.2
        ⟨M - N, fun n hn => hn⟩] with n hn
      have hlarge : M ≤ N + n := by omega
      have hindex : M + (N + n - M) = N + n := Nat.add_sub_of_le hlarge
      simpa only [hindex] using (hM (N + n - M)).2.2
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  have hLimitC (u x y : Lattice) (N : ℕ)
      (_hx : x ≤ π u N) (_hy : y ≤ π u N) :
      Tendsto (fun n : ℕ =>
        lastPassage ω x (((π u (N + n)).1 - x.1).toNat,
          ((π u (N + n)).2 - x.2).toNat) -
        lastPassage ω y (((π u (N + n)).1 - y.1).toNat,
          ((π u (N + n)).2 - y.2).toNat)) atTop (𝓝 (E x y)) := by
    obtain ⟨M, hM⟩ := hRepC u x y
    have hEq : (fun n : ℕ =>
        lastPassage ω x (((π u (N + n)).1 - x.1).toNat,
          ((π u (N + n)).2 - x.2).toNat) -
        lastPassage ω y (((π u (N + n)).1 - y.1).toNat,
          ((π u (N + n)).2 - y.2).toNat)) =ᶠ[atTop] fun _ => E x y := by
      filter_upwards [Filter.eventually_atTop.2
        ⟨M - N, fun n hn => hn⟩] with n hn
      have hlarge : M ≤ N + n := by omega
      have hindex : M + (N + n - M) = N + n := Nat.add_sub_of_le hlarge
      simpa only [hindex] using (hM (N + n - M)).2.2
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  intro x
  have hBridge := geodesic_limit_fields_order_and_eq_of_coalescing
    ω x x (γ x) (π x) D E
    (hGeoB x).1 (hGeoC x).1 (hGeoB x).2.1 (hGeoC x).2.1
    (fun m N hN => by
      obtain ⟨d, p, hd, htrace, hmax, _⟩ := (hGeoB x).2.2 m N hN
      exact ⟨d, p, hd, htrace, hmax⟩)
    (fun m N hN => by
      obtain ⟨d, p, hd, htrace, hmax, _⟩ := (hGeoC x).2.2 m N hN
      exact ⟨d, p, hd, htrace, hmax⟩)
    (hEscapeB x).1 (hEscapeB x).2 (hEscapeC x).1 (hEscapeC x).2
    (hLimitB x) (hLimitC x)
  exact hBridge.1 ⟨x.1 + x.2, le_refl _, le_refl _, by
    intro m n _hlarge hlevel
    have horder := hOrder x m n
    exact horder (by simpa only [γ, π, D, E, rightmostCocyclePath,
      Function.iterate_zero, id_eq] using hlevel)⟩ x

end LPP.Busemann
