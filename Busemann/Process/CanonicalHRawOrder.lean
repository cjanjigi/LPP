/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CanonicalHRawEnvelopes
public import Busemann.Process.CanonicalHRawSidedContinuityAux
public import Busemann.Process.CanonicalStrictCocycleOrder
public import Busemann.Frozen.StrongExistence.Definitions.StrictCrossTiltOrder
public import Busemann.Probability.CanonicalInvariantConditionalMean

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The two literal raw branches have opposite east and north edge order
at one tilt and between strictly ordered tilts. See the within-tilt and strict between-tilt order in Theorem 3.11. -/
theorem canonical_H_raw_fields_within_and_strict_cross_order
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (C : StrongField μ)
    (hClass : ForwardCoalescingClass μ C C)
    (hMean : MeanTilt μ C)
    (D : Set (CoalescingTilt μ))
    (hD : D.Countable)
    (left right : CoalescingTilt μ → ℕ → CoalescingTilt μ)
    (hSequences : ∀ h : CoalescingTilt μ,
      (h ∈ D → left h = (fun _ => h) ∧ right h = (fun _ => h)) ∧
      (h ∉ D →
        (∀ n, left h n ∈ D ∧ (left h n).val.1 < h.val.1) ∧
        StrictMono (fun n => (left h n).val.1) ∧
        Tendsto (left h) atTop (𝓝 h) ∧
        (∀ n, right h n ∈ D ∧ h.val.1 < (right h n).val.1) ∧
        StrictAnti (fun n => (right h n).val.1) ∧
        Tendsto (right h) atTop (𝓝 h)))
    (Bm Bp : StrongField μ)
    (hRaw : ∀ h x y ω,
      Bm h x y ω = limUnder atTop (fun n => C (left h n) x y ω) ∧
      Bp h x y ω = limUnder atTop (fun n => C (right h n) x y ω)) :
    WithinTiltOrder μ Bm Bp ∧ StrictCrossTiltOrder μ Bm Bp := by
  classical
  let P : Measure Environment := environmentLaw μ
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω

  -- The sampled fields inherit all three hypotheses of the strict order theorem.
  have hGen (d : CoalescingTilt μ) := (hClass d).2.1
  have hCoal (d : CoalescingTilt μ) := (hClass d).2.2.1
  have hForward (d : CoalescingTilt μ) := (hClass d).2.2.2

  -- Both origin means identify the full invariant tilt of each sampled field.
  have hTilt (d : CoalescingTilt μ) :
      ∀ᵐ ω ∂P,
        invariantCocycleTilt P T (fun ω => ω) (C d) (hGen d) ω = d.val := by
    have hMeanEast :
        (∫ ω, C d 0 (1, 0) ω ∂P) = -d.val.1 := (hMean d).1
    have hMeanNorth :
        (∫ ω, C d 0 (0, 1) ω ∂P) = -d.val.2 := (hMean d).2
    have hCondEast := canonical_condExp_full_invariants_eq_mean μ
      (C d 0 (1, 0)) ((hGen d).2.2 0 (1, 0))
    have hCondNorth := canonical_condExp_full_invariants_eq_mean μ
      (C d 0 (0, 1)) ((hGen d).2.2 0 (0, 1))
    filter_upwards [hCondEast, hCondNorth] with ω he hn
    change (-(P[C d 0 (1, 0) | latticeInvariantSigma T] ω),
      -(P[C d 0 (0, 1) | latticeInvariantSigma T] ω)) = d.val
    rw [he, hn, hMeanEast, hMeanNorth]
    simp

  -- Each strictly ordered sampled pair has one common all-site edge order event.
  have hStrictPair (a b : CoalescingTilt μ) (hab : a.val.1 < b.val.1) :
      ∀ᵐ ω ∂P, ∀ x : Lattice,
        C b x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          C a x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        C a x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          C b x (x + ((0 : ℤ), (1 : ℤ))) ω := by
    exact ae_forward_coalescing_cocycle_opposite_edge_order
      μ hμ hmoment (C a) (C b) (hGen a) (hGen b)
      (hForward a) (hForward b) (hCoal a) (hCoal b)
      a.val b.val (hTilt a) (hTilt b) hab

  have : Countable {d : CoalescingTilt μ // d ∈ D} := hD.to_subtype
  have hOrderAE :
      ∀ᵐ ω ∂P,
        ∀ a b : {d : CoalescingTilt μ // d ∈ D},
          a.val.val.1 < b.val.val.1 → ∀ x : Lattice,
            C b.val x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
              C a.val x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
            C a.val x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
              C b.val x (x + ((0 : ℤ), (1 : ℤ))) ω := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : a.val.val.1 < b.val.val.1
    · filter_upwards [hStrictPair a.val b.val hab] with ω hω
      intro _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ hab' => (hab hab').elim)

  -- The scalar order lemmas turn this event into all four raw-field bounds.
  have hComparisons (ω : Environment) (x : Lattice)
      (hω : ∀ a b : {d : CoalescingTilt μ // d ∈ D},
        a.val.val.1 < b.val.val.1 → ∀ y : Lattice,
          C b.val y (y + ((1 : ℤ), (0 : ℤ))) ω ≤
            C a.val y (y + ((1 : ℤ), (0 : ℤ))) ω ∧
          C a.val y (y + ((0 : ℤ), (1 : ℤ))) ω ≤
            C b.val y (y + ((0 : ℤ), (1 : ℤ))) ω) :
      (∀ h : CoalescingTilt μ,
        Bp h x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          Bm h x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        Bm h x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          Bp h x (x + ((0 : ℤ), (1 : ℤ))) ω) ∧
      (∀ h h' : CoalescingTilt μ, h.val.1 < h'.val.1 →
        Bm h' x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          Bp h x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        Bp h x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          Bm h' x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
    have hEastOrder (a b : CoalescingTilt μ) (ha : a ∈ D) (hb : b ∈ D)
        (hab : a.val.1 < b.val.1) :
        C b x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          C a x (x + ((1 : ℤ), (0 : ℤ))) ω := by
      exact (hω ⟨a, ha⟩ ⟨b, hb⟩ hab x).1
    have hNorthOrder (a b : CoalescingTilt μ) (ha : a ∈ D) (hb : b ∈ D)
        (hab : a.val.1 < b.val.1) :
        -(C b x (x + ((0 : ℤ), (1 : ℤ))) ω) ≤
          -(C a x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
      exact neg_le_neg (hω ⟨a, ha⟩ ⟨b, hb⟩ hab x).2
    have hEast := canonical_H_scalar_raw_limits_and_order μ D left right
      hSequences (fun d => C d x (x + ((1 : ℤ), (0 : ℤ))) ω) hEastOrder
    have hNorth := canonical_H_scalar_raw_limits_and_order μ D left right
      hSequences (fun d => -(C d x (x + ((0 : ℤ), (1 : ℤ))) ω)) hNorthOrder

    have hNorthLeftLimit (h : CoalescingTilt μ) :
        limUnder atTop (fun n => C (left h n) x (x + ((0 : ℤ), (1 : ℤ))) ω) =
          -limUnder atTop (fun n => -(C (left h n) x
            (x + ((0 : ℤ), (1 : ℤ))) ω)) := by
      have hNegConverges := (hNorth.1 h).1
      have hPositiveConverges :
          Tendsto (fun n => C (left h n) x (x + ((0 : ℤ), (1 : ℤ))) ω)
            atTop (𝓝 (-limUnder atTop (fun n => -(C (left h n) x
              (x + ((0 : ℤ), (1 : ℤ))) ω)))) := by
        simpa only [neg_neg] using hNegConverges.neg
      exact hPositiveConverges.limUnder_eq

    have hNorthRightLimit (h : CoalescingTilt μ) :
        limUnder atTop (fun n => C (right h n) x (x + ((0 : ℤ), (1 : ℤ))) ω) =
          -limUnder atTop (fun n => -(C (right h n) x
            (x + ((0 : ℤ), (1 : ℤ))) ω)) := by
      have hNegConverges := (hNorth.1 h).2
      have hPositiveConverges :
          Tendsto (fun n => C (right h n) x (x + ((0 : ℤ), (1 : ℤ))) ω)
            atTop (𝓝 (-limUnder atTop (fun n => -(C (right h n) x
              (x + ((0 : ℤ), (1 : ℤ))) ω)))) := by
        simpa only [neg_neg] using hNegConverges.neg
      exact hPositiveConverges.limUnder_eq

    constructor
    · intro h
      rcases hRaw h x (x + ((1 : ℤ), (0 : ℤ))) ω with ⟨hBmEast, hBpEast⟩
      rcases hRaw h x (x + ((0 : ℤ), (1 : ℤ))) ω with ⟨hBmNorth, hBpNorth⟩
      constructor
      · calc
          Bp h x (x + ((1 : ℤ), (0 : ℤ))) ω =
              limUnder atTop (fun n => C (right h n) x
                (x + ((1 : ℤ), (0 : ℤ))) ω) := hBpEast
          _ ≤ limUnder atTop (fun n => C (left h n) x
                (x + ((1 : ℤ), (0 : ℤ))) ω) := (hEast.2.1 h)
          _ = Bm h x (x + ((1 : ℤ), (0 : ℤ))) ω := hBmEast.symm
      · calc
          Bm h x (x + ((0 : ℤ), (1 : ℤ))) ω =
              limUnder atTop (fun n => C (left h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω) := hBmNorth
          _ = -limUnder atTop (fun n => -(C (left h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω)) := hNorthLeftLimit h
          _ ≤ -limUnder atTop (fun n => -(C (right h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω)) := neg_le_neg (hNorth.2.1 h)
          _ = limUnder atTop (fun n => C (right h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω) := (hNorthRightLimit h).symm
          _ = Bp h x (x + ((0 : ℤ), (1 : ℤ))) ω := hBpNorth.symm
    · intro h h' hfirst
      rcases hRaw h x (x + ((1 : ℤ), (0 : ℤ))) ω with ⟨_, hBpEast⟩
      rcases hRaw h' x (x + ((1 : ℤ), (0 : ℤ))) ω with ⟨hBmEast, _⟩
      rcases hRaw h x (x + ((0 : ℤ), (1 : ℤ))) ω with ⟨_, hBpNorth⟩
      rcases hRaw h' x (x + ((0 : ℤ), (1 : ℤ))) ω with ⟨hBmNorth, _⟩
      constructor
      · calc
          Bm h' x (x + ((1 : ℤ), (0 : ℤ))) ω =
              limUnder atTop (fun n => C (left h' n) x
                (x + ((1 : ℤ), (0 : ℤ))) ω) := hBmEast
          _ ≤ limUnder atTop (fun n => C (right h n) x
                (x + ((1 : ℤ), (0 : ℤ))) ω) := hEast.2.2 h h' hfirst
          _ = Bp h x (x + ((1 : ℤ), (0 : ℤ))) ω := hBpEast.symm
      · calc
          Bp h x (x + ((0 : ℤ), (1 : ℤ))) ω =
              limUnder atTop (fun n => C (right h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω) := hBpNorth
          _ = -limUnder atTop (fun n => -(C (right h n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω)) := hNorthRightLimit h
          _ ≤ -limUnder atTop (fun n => -(C (left h' n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω)) :=
                  neg_le_neg (hNorth.2.2 h h' hfirst)
          _ = limUnder atTop (fun n => C (left h' n) x
                (x + ((0 : ℤ), (1 : ℤ))) ω) := (hNorthLeftLimit h').symm
          _ = Bm h' x (x + ((0 : ℤ), (1 : ℤ))) ω := hBmNorth.symm

  constructor
  · intro h x
    filter_upwards [hOrderAE] with ω hω
    exact (hComparisons ω x hω).1 h
  · intro h h' hfirst x
    filter_upwards [hOrderAE] with ω hω
    exact (hComparisons ω x hω).2 h h' hfirst

end LPP.Busemann
