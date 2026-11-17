/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.ForwardCoalescingClass
public import Busemann.Frozen.StrongExistence.Definitions.MeanTilt
public import Busemann.Process.CanonicalStrictCocycleOrder
public import Busemann.Process.CanonicalCocycleUniqueness
public import Busemann.Process.CanonicalHFieldSelection
public import Busemann.Probability.CanonicalInvariantConditionalMean

import Busemann.Process.MonotoneCocycleLimit
import LPP_Foundations.Model.LatticeEdgeIntegration
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic

/-! Continuity of one canonical cocycle field at a countable sample of tilts. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology BigOperators
namespace LPP.Busemann

private theorem strictMono_subseq_of_below_tendsto
    (f : ℕ → ℝ) (a : ℝ) (hf : ∀ n, f n < a)
    (hlim : Tendsto f atTop (𝓝 a)) :
    ∃ φ : ℕ ↪o ℕ, StrictMono (f ∘ φ) := by
  obtain ⟨φ, hInc | hNoninc⟩ :=
    exists_increasing_or_nonincreasing_subseq (fun x y : ℝ => x < y) f
  · exact ⟨φ, fun m n hmn => hInc m n hmn⟩
  · have hφlim : Tendsto (f ∘ φ) atTop (𝓝 a) :=
      hlim.comp φ.strictMono.tendsto_atTop
    have hBound : ∀ n, f (φ n) ≤ f (φ 0) := by
      intro n
      by_cases hn : n = 0
      · subst n; exact le_rfl
      · exact le_of_not_gt (hNoninc 0 n (Nat.pos_iff_ne_zero.mpr hn))
    have ha : a ≤ f (φ 0) :=
      le_of_tendsto hφlim (Filter.Eventually.of_forall hBound)
    exact False.elim ((not_lt_of_ge ha) (hf (φ 0)))

private theorem tendsto_of_cofinal_lower_bounds
    (a b : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (𝓝 l))
    (hab : ∀ i, ∀ᶠ n in atTop, a i ≤ b n)
    (hbl : ∀ n, b n ≤ l) :
    Tendsto b atTop (𝓝 l) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    obtain ⟨i, hi⟩ : ∃ i, r < a i :=
      (ha.eventually (Ioi_mem_nhds hr)).exists
    filter_upwards [hab i] with n hn
    exact lt_of_lt_of_le hi hn
  · intro r hr
    exact Filter.Eventually.of_forall (fun n => lt_of_le_of_lt (hbl n) hr)

-- The signed-pair extension below is pointwise. Its event is chosen by the
-- caller before quantifying over arbitrary sequences.
private theorem additive_eq_signed_edge_sums_local
    (F : Lattice → Lattice → ℝ) (hF : is_additive F) (x y : Lattice) :
    F x y =
      (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1, F (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else
        -(∑ k ∈ Finset.Ico y.1 x.1,
          F (k, x.2) ((k, x.2) + finiteEdgeStep 0))) +
      (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2, F (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else
        -(∑ k ∈ Finset.Ico y.2 x.2,
          F (y.1, k) ((y.1, k) + finiteEdgeStep 1))) := by
  classical
  let E : Lattice → Fin 2 → ℝ := fun z i => F z (z + finiteEdgeStep i)
  have hCurl (z : Lattice) :
      E z 0 + E (z + (1, 0)) 1 = E z 1 + E (z + (0, 1)) 0 := by
    dsimp [E, finiteEdgeStep]
    have hz₀ : z + (1, 0) + (0, 1) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    have hz₁ : z + (0, 1) + (1, 0) = z + (1, 1) := by
      ext <;> simp [Prod.mk_add_mk, add_assoc]
    rw [hz₀, hz₁]
    exact (hF z (z + (1, 0)) (z + (1, 1))).trans
      (hF z (z + (0, 1)) (z + (1, 1))).symm
  obtain ⟨G, hGadd, hGedge, hGformula, hUnique⟩ :=
    exists_unique_lattice_edge_extension E hCurl
  have hFE (z : Lattice) :
      F z (z + (1, 0)) = E z 0 ∧ F z (z + (0, 1)) = E z 1 := by
    dsimp [E, finiteEdgeStep]
    exact ⟨rfl, rfl⟩
  have hFG : F = G := hUnique F hF hFE
  have hFormula := hGformula x y
  rw [← hFG] at hFormula
  simpa [E, finiteEdgeStep] using hFormula

private theorem tendsto_additive_pair_of_edge_tendsto
    (F : ℕ → Lattice → Lattice → ℝ)
    (G : Lattice → Lattice → ℝ)
    (hF : ∀ n, is_additive (F n))
    (hG : is_additive G)
    (hEdges : ∀ z i, Tendsto
      (fun n => F n z (z + finiteEdgeStep i)) atTop
      (𝓝 (G z (z + finiteEdgeStep i))))
    (x y : Lattice) :
    Tendsto (fun n => F n x y) atTop (𝓝 (G x y)) := by
  classical
  have hHorizontal : Tendsto
      (fun n => if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1,
          F n (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          F n (k, x.2) ((k, x.2) + finiteEdgeStep 0))) atTop
      (𝓝 (if x.1 ≤ y.1 then
        ∑ k ∈ Finset.Ico x.1 y.1,
          G (k, x.2) ((k, x.2) + finiteEdgeStep 0)
       else -(∑ k ∈ Finset.Ico y.1 x.1,
          G (k, x.2) ((k, x.2) + finiteEdgeStep 0)))) := by
    by_cases hxy : x.1 ≤ y.1
    · simpa [hxy] using tendsto_finsetSum _
        (fun k _ => hEdges (k, x.2) 0)
    · simpa [hxy] using (tendsto_finsetSum _
        (fun k _ => hEdges (k, x.2) 0)).neg
  have hVertical : Tendsto
      (fun n => if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2,
          F n (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          F n (y.1, k) ((y.1, k) + finiteEdgeStep 1))) atTop
      (𝓝 (if x.2 ≤ y.2 then
        ∑ k ∈ Finset.Ico x.2 y.2,
          G (y.1, k) ((y.1, k) + finiteEdgeStep 1)
       else -(∑ k ∈ Finset.Ico y.2 x.2,
          G (y.1, k) ((y.1, k) + finiteEdgeStep 1)))) := by
    by_cases hxy : x.2 ≤ y.2
    · simpa [hxy] using tendsto_finsetSum _
        (fun k _ => hEdges (y.1, k) 1)
    · simpa [hxy] using (tendsto_finsetSum _
        (fun k _ => hEdges (y.1, k) 1)).neg
  have hSum := hHorizontal.add hVertical
  convert hSum using 1
  · ext n
    exact additive_eq_signed_edge_sums_local (F n) (hF n) x y
  · rw [additive_eq_signed_edge_sums_local G hG x y]

/-- One full event supports sided limits of the selected canonical field at
countably many sampled tilts, along sequences in that same sample. -/
theorem ae_canonical_field_sided_continuous_on_countable_sample
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (C : StrongField μ)
    (hClass : ForwardCoalescingClass μ C C)
    (hMean : MeanTilt μ C)
    (D : Set (CoalescingTilt μ)) (hD : D.Countable) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ d : CoalescingTilt μ, d ∈ D →
      ∀ x y : Lattice,
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d x y ω))) ∧
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d x y ω))) := by
  classical
  let P : Measure Environment := environmentLaw μ
  let T : Lattice → Environment → Environment :=
    fun z ω => environmentTranslationEquiv z ω
  have hGen (h : CoalescingTilt μ) :
      IsGeneralizedBusemann P T (fun ω => ω) (C h) := (hClass h).2.1
  have hCoal (h : CoalescingTilt μ) :
      HasCoalescingRightmostPaths P (C h) := (hClass h).2.2.1
  have hForward (h : CoalescingTilt μ) : IsForwardMeasurable (C h) :=
    (hClass h).2.2.2
  have hTilt (h : CoalescingTilt μ) :
      ∀ᵐ ω ∂P, invariantCocycleTilt P T (fun ω => ω)
        (C h) (hGen h) ω = h.val := by
    let mEnv : MeasurableSpace Environment := inferInstance
    let I : MeasurableSpace Environment := @latticeInvariantSigma Environment mEnv T
    let : MeasurableSpace Environment := mEnv
    have he := canonical_condExp_full_invariants_eq_mean μ
      (C h 0 ((1 : ℤ), (0 : ℤ))) ((hGen h).2.2 0 ((1 : ℤ), (0 : ℤ)))
    have hn := canonical_condExp_full_invariants_eq_mean μ
      (C h 0 ((0 : ℤ), (1 : ℤ))) ((hGen h).2.2 0 ((0 : ℤ), (1 : ℤ)))
    filter_upwards [he, hn] with ω heω hnω
    apply Prod.ext
    · change -(P[C h 0 ((1 : ℤ), (0 : ℤ)) | I] ω) = h.val.1
      rw [heω, (hMean h).1]
      ring
    · change -(P[C h 0 ((0 : ℤ), (1 : ℤ)) | I] ω) = h.val.2
      rw [hnω, (hMean h).2]
      ring
  have hStrict (a b : CoalescingTilt μ) (hab : a.val.1 < b.val.1) :
      ∀ᵐ ω ∂P, ∀ x : Lattice,
        C b x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
          C a x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
        C a x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
          C b x (x + ((0 : ℤ), (1 : ℤ))) ω :=
    ae_forward_coalescing_cocycle_opposite_edge_order
      μ hμ hmoment (C a) (C b) (hGen a) (hGen b)
      (hForward a) (hForward b) (hCoal a) (hCoal b)
      a.val b.val (hTilt a) (hTilt b) hab
  have : Countable {d : CoalescingTilt μ // d ∈ D} := hD.to_subtype
  have hOrderAE : ∀ᵐ ω ∂P,
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
    · filter_upwards [hStrict a.val b.val hab] with ω hω
      intro _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ hab' => (hab hab').elim)
  have hAddAE : ∀ᵐ ω ∂P,
      ∀ d : {h : CoalescingTilt μ // h ∈ D},
        is_additive (fun x y => C d.val x y ω) := by
    apply ae_all_iff.mpr
    intro d
    exact (hGen d.val).1.2.2
  -- The next step chooses one monotone cofinal sample sequence at each
  -- available side. Its limit is identified with C d by same-tilt uniqueness.
  have hCofinalLimit
      (d : CoalescingTilt μ) (F : ℕ → CoalescingTilt μ)
      (hFlim : Tendsto F atTop (𝓝 d))
      (hForder :
        (∀ᵐ ω ∂P, ∀ n x,
          C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
            C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
          C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
            C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
        (∀ᵐ ω ∂P, ∀ n x,
          C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
            C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
          C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
            C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω)) :
      ∀ᵐ ω ∂P, ∀ x y : Lattice,
        Tendsto (fun n => C (F n) x y ω) atTop (𝓝 (C d x y ω)) := by
    have hPair : Tendsto (fun n => (F n).val) atTop (𝓝 d.val) :=
      continuous_subtype_val.tendsto d |>.comp hFlim
    obtain ⟨L, hL, hLforward, hLcoal, hLtilt, hLlim, _hLL1, _hLEast, _hLNorth⟩ :=
      exists_forward_coalescing_monotone_cocycle_limit
        μ hμ hmoment (fun n => C (F n)) (fun n => hGen (F n))
        (fun n => hForward (F n)) (fun n => (F n).val) d.val
        (fun n => hTilt (F n)) hPair hForder
    have hEq := ae_eq_of_coalescing_canonical_cocycles_same_tilt
      μ L (C d) hL (hGen d) hLcoal (hCoal d) d.val hLtilt (hTilt d)
    filter_upwards [hLlim, hEq] with ω hlim heq
    intro x y
    simpa only [heq x y] using hlim x y
  -- Assemble the common countable event below; all later sequence arguments
  -- are deterministic on that event.
  have hAtSample (d : {h : CoalescingTilt μ // h ∈ D}) :
      ∀ᵐ ω ∂P, ∀ x y : Lattice,
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω))) ∧
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω))) := by
    have hLeft : ∀ᵐ ω ∂P, ∀ x y : Lattice,
        ∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω)) := by
      by_cases hExists : ∃ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.val.1) ∧
          Tendsto hs atTop (𝓝 d.val)
      · obtain ⟨hs₀, hs₀side, hs₀lim⟩ := hExists
        have hs₀first : Tendsto (fun n => (hs₀ n).val.1) atTop
            (𝓝 d.val.val.1) :=
          ((continuous_fst.comp continuous_subtype_val).tendsto d.val).comp hs₀lim
        obtain ⟨φ, hφinc⟩ := strictMono_subseq_of_below_tendsto
          (fun n => (hs₀ n).val.1) d.val.val.1
          (fun n => (hs₀side n).2) hs₀first
        let F : ℕ → CoalescingTilt μ := fun n => hs₀ (φ n)
        have hFmem (n) : F n ∈ D := (hs₀side (φ n)).1
        have hFbelow (n) : (F n).val.1 < d.val.val.1 := (hs₀side (φ n)).2
        have hFinc : StrictMono (fun n => (F n).val.1) := by
          simpa only [F, Function.comp_def] using hφinc
        have hFlim : Tendsto F atTop (𝓝 d.val) :=
          hs₀lim.comp φ.strictMono.tendsto_atTop
        have hForder :
            (∀ᵐ ω ∂P, ∀ n x,
              C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
                C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
              C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
                C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
            (∀ᵐ ω ∂P, ∀ n x,
              C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
                C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
              C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
                C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
          left
          apply ae_all_iff.mpr
          intro n
          exact hStrict (F n) (F (n + 1)) (hFinc n.lt_succ_self)
        have hFlimAE := hCofinalLimit d.val F hFlim hForder
        filter_upwards [hOrderAE, hAddAE, hFlimAE] with ω hOrder hAdd hLimit
        intro x y hs hhsSide hhsLim
        have hhsFirst : Tendsto (fun n => (hs n).val.1) atTop
            (𝓝 d.val.val.1) :=
          ((continuous_fst.comp continuous_subtype_val).tendsto d.val).comp hhsLim
        have hEast (z : Lattice) : Tendsto
            (fun n => C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω) atTop
            (𝓝 (C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω)) := by
          have hLower (i) : ∀ᶠ n in atTop,
              -(C (F i) z (z + ((1 : ℤ), (0 : ℤ))) ω) ≤
                -(C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω) := by
            have hEventually : ∀ᶠ n in atTop,
                (F i).val.1 < (hs n).val.1 :=
              hhsFirst.eventually (Ioi_mem_nhds (hFbelow i))
            filter_upwards [hEventually] with n hn
            exact neg_le_neg (hOrder ⟨F i, hFmem i⟩
              ⟨hs n, (hhsSide n).1⟩ hn z).1
          have hUpper (n) :
              -(C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω) ≤
                -(C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω) :=
            neg_le_neg (hOrder ⟨hs n, (hhsSide n).1⟩ d
              (hhsSide n).2 z).1
          have hNeg := tendsto_of_cofinal_lower_bounds
            (fun i => -(C (F i) z (z + ((1 : ℤ), (0 : ℤ))) ω))
            (fun n => -(C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω))
            (-(C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω))
            (hLimit z (z + ((1 : ℤ), (0 : ℤ)))).neg hLower hUpper
          simpa only [neg_neg] using hNeg.neg
        have hNorth (z : Lattice) : Tendsto
            (fun n => C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω) atTop
            (𝓝 (C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω)) := by
          have hLower (i) : ∀ᶠ n in atTop,
              C (F i) z (z + ((0 : ℤ), (1 : ℤ))) ω ≤
                C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω := by
            have hEventually : ∀ᶠ n in atTop,
                (F i).val.1 < (hs n).val.1 :=
              hhsFirst.eventually (Ioi_mem_nhds (hFbelow i))
            filter_upwards [hEventually] with n hn
            exact (hOrder ⟨F i, hFmem i⟩
              ⟨hs n, (hhsSide n).1⟩ hn z).2
          have hUpper (n) :
              C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω ≤
                C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω :=
            (hOrder ⟨hs n, (hhsSide n).1⟩ d (hhsSide n).2 z).2
          exact tendsto_of_cofinal_lower_bounds
            (fun i => C (F i) z (z + ((0 : ℤ), (1 : ℤ))) ω)
            (fun n => C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω)
            (C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω)
            (hLimit z (z + ((0 : ℤ), (1 : ℤ)))) hLower hUpper
        have hEdges (z : Lattice) (i : Fin 2) : Tendsto
            (fun n => C (hs n) z (z + finiteEdgeStep i) ω) atTop
            (𝓝 (C d.val z (z + finiteEdgeStep i) ω)) := by
          fin_cases i
          · simpa [finiteEdgeStep] using hEast z
          · simpa [finiteEdgeStep] using hNorth z
        exact tendsto_additive_pair_of_edge_tendsto
          (fun n a b => C (hs n) a b ω)
          (fun a b => C d.val a b ω)
          (fun n => hAdd ⟨hs n, (hhsSide n).1⟩)
          (hAdd d) hEdges x y
      · exact Filter.Eventually.of_forall (fun _ x y hs hside hlim =>
          (hExists ⟨hs, hside, hlim⟩).elim)
    have hRight : ∀ᵐ ω ∂P, ∀ x y : Lattice,
        ∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω)) := by
      by_cases hExists : ∃ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.val.1 < (hs n).val.1) ∧
          Tendsto hs atTop (𝓝 d.val)
      · obtain ⟨hs₀, hs₀side, hs₀lim⟩ := hExists
        have hs₀first : Tendsto (fun n => (hs₀ n).val.1) atTop
            (𝓝 d.val.val.1) :=
          ((continuous_fst.comp continuous_subtype_val).tendsto d.val).comp hs₀lim
        obtain ⟨φ, hφinc⟩ := strictMono_subseq_of_below_tendsto
          (fun n => -((hs₀ n).val.1)) (-d.val.val.1)
          (fun n => neg_lt_neg (hs₀side n).2) hs₀first.neg
        let F : ℕ → CoalescingTilt μ := fun n => hs₀ (φ n)
        have hFmem (n) : F n ∈ D := (hs₀side (φ n)).1
        have hFabove (n) : d.val.val.1 < (F n).val.1 := (hs₀side (φ n)).2
        have hFanti : StrictAnti (fun n => (F n).val.1) := by
          intro m n hmn
          have h := hφinc hmn
          simpa only [F, Function.comp_def, neg_lt_neg_iff] using h
        have hFlim : Tendsto F atTop (𝓝 d.val) :=
          hs₀lim.comp φ.strictMono.tendsto_atTop
        have hForder :
            (∀ᵐ ω ∂P, ∀ n x,
              C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
                C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
              C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
                C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω) ∨
            (∀ᵐ ω ∂P, ∀ n x,
              C (F n) x (x + ((1 : ℤ), (0 : ℤ))) ω ≤
                C (F (n + 1)) x (x + ((1 : ℤ), (0 : ℤ))) ω ∧
              C (F (n + 1)) x (x + ((0 : ℤ), (1 : ℤ))) ω ≤
                C (F n) x (x + ((0 : ℤ), (1 : ℤ))) ω) := by
          right
          apply ae_all_iff.mpr
          intro n
          exact hStrict (F (n + 1)) (F n) (hFanti n.lt_succ_self)
        have hFlimAE := hCofinalLimit d.val F hFlim hForder
        filter_upwards [hOrderAE, hAddAE, hFlimAE] with ω hOrder hAdd hLimit
        intro x y hs hhsSide hhsLim
        have hhsFirst : Tendsto (fun n => (hs n).val.1) atTop
            (𝓝 d.val.val.1) :=
          ((continuous_fst.comp continuous_subtype_val).tendsto d.val).comp hhsLim
        have hEast (z : Lattice) : Tendsto
            (fun n => C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω) atTop
            (𝓝 (C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω)) := by
          have hLower (i) : ∀ᶠ n in atTop,
              C (F i) z (z + ((1 : ℤ), (0 : ℤ))) ω ≤
                C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω := by
            have hEventually : ∀ᶠ n in atTop,
                (hs n).val.1 < (F i).val.1 :=
              hhsFirst.eventually (Iio_mem_nhds (hFabove i))
            filter_upwards [hEventually] with n hn
            exact (hOrder ⟨hs n, (hhsSide n).1⟩
              ⟨F i, hFmem i⟩ hn z).1
          have hUpper (n) :
              C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω ≤
                C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω :=
            (hOrder d ⟨hs n, (hhsSide n).1⟩ (hhsSide n).2 z).1
          exact tendsto_of_cofinal_lower_bounds
            (fun i => C (F i) z (z + ((1 : ℤ), (0 : ℤ))) ω)
            (fun n => C (hs n) z (z + ((1 : ℤ), (0 : ℤ))) ω)
            (C d.val z (z + ((1 : ℤ), (0 : ℤ))) ω)
            (hLimit z (z + ((1 : ℤ), (0 : ℤ)))) hLower hUpper
        have hNorth (z : Lattice) : Tendsto
            (fun n => C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω) atTop
            (𝓝 (C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω)) := by
          have hLower (i) : ∀ᶠ n in atTop,
              -(C (F i) z (z + ((0 : ℤ), (1 : ℤ))) ω) ≤
                -(C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω) := by
            have hEventually : ∀ᶠ n in atTop,
                (hs n).val.1 < (F i).val.1 :=
              hhsFirst.eventually (Iio_mem_nhds (hFabove i))
            filter_upwards [hEventually] with n hn
            exact neg_le_neg (hOrder ⟨hs n, (hhsSide n).1⟩
              ⟨F i, hFmem i⟩ hn z).2
          have hUpper (n) :
              -(C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω) ≤
                -(C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω) :=
            neg_le_neg (hOrder d ⟨hs n, (hhsSide n).1⟩
              (hhsSide n).2 z).2
          have hNeg := tendsto_of_cofinal_lower_bounds
            (fun i => -(C (F i) z (z + ((0 : ℤ), (1 : ℤ))) ω))
            (fun n => -(C (hs n) z (z + ((0 : ℤ), (1 : ℤ))) ω))
            (-(C d.val z (z + ((0 : ℤ), (1 : ℤ))) ω))
            (hLimit z (z + ((0 : ℤ), (1 : ℤ)))).neg hLower hUpper
          simpa only [neg_neg] using hNeg.neg
        have hEdges (z : Lattice) (i : Fin 2) : Tendsto
            (fun n => C (hs n) z (z + finiteEdgeStep i) ω) atTop
            (𝓝 (C d.val z (z + finiteEdgeStep i) ω)) := by
          fin_cases i
          · simpa [finiteEdgeStep] using hEast z
          · simpa [finiteEdgeStep] using hNorth z
        exact tendsto_additive_pair_of_edge_tendsto
          (fun n a b => C (hs n) a b ω)
          (fun a b => C d.val a b ω)
          (fun n => hAdd ⟨hs n, (hhsSide n).1⟩)
          (hAdd d) hEdges x y
      · exact Filter.Eventually.of_forall (fun _ x y hs hside hlim =>
          (hExists ⟨hs, hside, hlim⟩).elim)
    filter_upwards [hLeft, hRight] with ω hl hr
    intro x y
    exact ⟨hl x y, hr x y⟩
  have hCommon : ∀ᵐ ω ∂P,
      ∀ d : {h : CoalescingTilt μ // h ∈ D}, ∀ x y : Lattice,
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ (hs n).val.1 < d.val.val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω))) ∧
        (∀ hs : ℕ → CoalescingTilt μ,
          (∀ n, hs n ∈ D ∧ d.val.val.1 < (hs n).val.1) →
          Tendsto hs atTop (𝓝 d.val) →
          Tendsto (fun n => C (hs n) x y ω) atTop (𝓝 (C d.val x y ω))) :=
    ae_all_iff.mpr hAtSample
  filter_upwards [hCommon] with ω hω
  intro d hd x y
  exact hω ⟨d, hd⟩ x y

end LPP.Busemann
