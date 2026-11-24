/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.Grid.GeneralGlobalEvents
public import Differentiability.FinalDraft.Grid.GeneralProbability
public import LPP_Foundations.Model.Animals.PathSets
import Differentiability.Paper.StaircaseWeights
import Differentiability.Probability.HeavyVertexEvents
import Differentiability.Probability.StairGeometryEvent
import Mathlib.Tactic

/-! # The probability bound on the four-way general grid event -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LPPDifferentiability

local notation "GridPath" => Σ u : Lattice, Σ d : ℕ × ℕ, Path u d

/-- The A2 weight estimate for a selected family whose path-count and path-length bounds
hold eventually along the record scales
(`differentiability_final_draft.tex`, Lemma `lem:stair-general` and Appendix B item `ch:family`). -/
theorem grid_staircase_weight_failure_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p' : ℝ) (hp' : 1 < p')
    (hmom : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (ε₀ cstar : ℝ) (hε₀ : 0 < ε₀) (hcstar : 0 < cstar)
    (K₂ : ℕ) (hK₂p : 24 < (K₂ : ℝ) * (p' - 1))
    (record : Set ℕ) (Q : ℕ → Set Lattice) (hQ : ∀ k, (Q k).Finite)
    (paths : ℕ → (Lattice → Bool) → Finset GridPath)
    (hmeas : ∀ k P, MeasurableSet {b | paths k b = P})
    (hvalid : ∀ᶠ k in atTop ⊓ 𝓟 record, ∀ b,
      ((paths k b).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ (11 : ℝ) ∧
      ∀ q ∈ paths k b,
        ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k ∧
        (∀ i, q.2.2.vertex i ∈ Q k) ∧
        ∀ z ∈ q.2.2.collectedSites, b z = false) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real
      (gridStaircaseWeightEvent (paths k) (StairGeometry.threshold ε₀ K₂ k)
        (ε₀ * (2 : ℝ) ^ k / (k : ℝ)) (∫ y, max (-y) 0 ∂μ))ᶜ)
      (atTop ⊓ 𝓟 record) (𝓝 0) := by
  classical
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (eventually_inf_principal.mp hvalid)
  -- Use the all-scale bound on an auxiliary family and compare on the record scales.
  let P (k : ℕ) (b : Lattice → Bool) :=
    if k₁ ≤ k ∧ k ∈ record then paths k b else (∅ : Finset GridPath)
  have hPmeas (k : ℕ) (F : Finset GridPath) : MeasurableSet {b | P k b = F} := by
    by_cases hk : k₁ ≤ k ∧ k ∈ record
    · simpa only [P, ite_eq_left hk] using hmeas k F
    · simp only [P, ite_eq_right hk]
      exact MeasurableSet.const _
  have hcard (k : ℕ) (b : Lattice → Bool) :
      ((P k b).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ (11 : ℝ) := by
    by_cases hk : k₁ ≤ k ∧ k ∈ record
    · simpa only [P, ite_eq_left hk] using (hk₁ k hk.1 hk.2 b).1
    · simp only [P, ite_eq_right hk, Finset.card_empty, Nat.cast_zero]
      positivity
  have hspec (k : ℕ) (b : Lattice → Bool) (q : GridPath) (hq : q ∈ P k b) :
      ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k ∧
      (∀ i, q.2.2.vertex i ∈ Q k) ∧ ∀ z ∈ q.2.2.collectedSites, b z = false := by
    dsimp only [P] at hq
    split_ifs at hq with hk
    · exact (hk₁ k hk.1 hk.2 b).2 q hq
    · exact (Finset.notMem_empty q hq).elim
  have hdecay := Paper.staircase_path_family_weight_failure_tendsto_zero μ p' hp' hmom
    ε₀ cstar 11 hε₀ hcstar (by norm_num) K₂ (by norm_num; exact hK₂p)
    Q hQ P hPmeas hcard (fun k b q hq => (hspec k b q hq).1)
    (fun k b q hq => (hspec k b q hq).2.1)
    (fun k b q hq => (hspec k b q hq).2.2)
  have hrecord : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, k₁ ≤ k ∧ k ∈ record :=
    eventually_inf_principal.mpr ((eventually_ge_atTop k₁).mono fun _ hk hr => ⟨hk, hr⟩)
  refine (hdecay.mono_left inf_le_left).congr' ?_
  filter_upwards [hrecord] with k hk
  apply congrArg (environmentLaw μ).real
  ext ω
  simp only [P, ite_eq_left hk, gridStaircaseWeightEvent, StairGeometry.threshold, mem_compl_iff,
    mem_ofPred_eq, not_forall, not_le, exists_prop]
  refine exists_congr fun q => and_congr ?_ Iff.rfl
  have hmem {b b' : Lattice → Bool} (hb : b = b') : q ∈ paths k b ↔ q ∈ paths k b' := by
    rw [hb]
  apply hmem
  funext z
  have hite (p : Prop) (d₁ d₂ : Decidable p) :
      @ite Bool p d₁ true false = @ite Bool p d₂ true false :=
    congrArg (fun d => @ite Bool p d true false) (Subsingleton.elim d₁ d₂)
  exact hite _ _ _

/-- The A3 upper-weight cap holds with probability tending to one on the literal
working region on record scales
(`differentiability_final_draft.tex`, Lemmas `lem:stair-general` and `lem:heavy`). -/
theorem grid_working_cap_failure_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a A R C₁ ε₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hε₀ : 0 < ε₀)
    (k0 : ℕ) (m : ℕ → ℕ) (record : Set ℕ)
    (hm3 : ∀ k, k0 ≤ k → k ∈ record → m k ≤ 3 * k) :
    Tendsto (fun k : ℕ => (environmentLaw μ).real
      (gridUpperCap (StairGeometry.workingRegion a A R C₁ m k)
        (ε₀ * (2 : ℝ) ^ k / (k : ℝ)))ᶜ) (atTop ⊓ 𝓟 record) (𝓝 0) := by
  classical
  let m' (k : ℕ) := if k ∈ record then m k else 0
  have hm' (k : ℕ) (hk : k0 ≤ k) : m' k ≤ 3 * k := by
    by_cases hr : k ∈ record
    · simpa only [m', hr, ite_true] using hm3 k hk hr
    · simp [m', hr]
  obtain ⟨B, hB, hdecay⟩ :=
    heavy_working_region_event_tendsto μ hp hmom m' k0 hm' a A R C₁ ε₀ hA hR hC₁ hε₀
  have hrecord : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, k0 ≤ k ∧ k ∈ record :=
    eventually_inf_principal.mpr ((eventually_ge_atTop k0).mono fun _ hk hr => ⟨hk, hr⟩)
  refine (hdecay.mono_left inf_le_left).congr' ?_
  filter_upwards [hrecord] with k hk
  have hregion (z : Lattice) : z ∈ B k ↔ z ∈ StairGeometry.workingRegion a A R C₁ m k := by
    simpa only [StairGeometry.workingRegion, m', hk.2, ite_true, mem_ofPred_eq] using hB k hk.1 z
  apply congrArg (environmentLaw μ).real
  ext ω
  simp only [gridUpperCap, mem_compl_iff, mem_ofPred_eq, hregion]

/-- The four-way good event has failure probability at most twice the fixed
tail, as soon as the selected family has the source path bounds and measurable
fibres. This is the probability assembly of `rk:gridprob-general` and
Appendix B item U7 in `differentiability_final_draft.tex`. -/
theorem general_grid_good_event_failure_eventually_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p': ℝ) (hp' : 1 < p')
    (hmom' : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p : ℝ) (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a G K cstar A R C₁ ε₀ q0 : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hcstar : 1 ≤ cstar)
    (hA : 0 < A) (hR : 0 < R) (hC₁ : 0 ≤ C₁) (hε₀ : 0 < ε₀) (hq0 : 0 < q0)
    (K₁ K₂ K₃ : ℕ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hK₃ : 1 ≤ K₃)
    (hK₃p : 4 < (K₃ : ℝ) * p') (hK₁p : 4 < ((K₁ : ℝ) + 1) * p')
    (hK₂p : 24 < (K₂ : ℝ) * (p' - 1))
    (k0 J : ℕ) (hk0 : 0 < k0) (hJ : 1 ≤ J) (m : ℕ → ℕ) (record : Set ℕ)
    (hm3 : ∀ k, k0 ≤ k → k ∈ record → m k ≤ 3 * k)
    (htrial : ∀ k ∈ record, 4 * k0 + 3 ≤ k → ∀ j : ℕ, j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
      (∀ n : ℕ, 1 ≤ n → (n : ℝ) < (2 : ℝ) ^ (m k - 4 * j - 1) →
        q0 < (environmentLaw μ).real {ω : Environment |
          ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
            (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
              8 * (2 : ℝ) ^ (k - j)) ∧
            G * (n : ℝ) - K * (2 : ℝ) ^ (k - j) < pathWeight ω q}) ∧
      (1 < (2 : ℝ) ^ (m k - 4 * j - 1) →
        (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2))
    (paths : ℕ → (Lattice → Bool) → Finset GridPath)
    (hmeas : ∀ k P, MeasurableSet {b | paths k b = P})
    (hvalid : ∀ᶠ k in atTop ⊓ 𝓟 record, ∀ b,
      ((paths k b).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ (11 : ℝ) ∧
      ∀ q ∈ paths k b,
        ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k ∧
        (∀ i, q.2.2.vertex i ∈ StairGeometry.workingRegion a A R C₁ m k) ∧
        ∀ z ∈ q.2.2.collectedSites, b z = false) :
    ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, (environmentLaw μ).real
      (generalGridGoodEventForPaths paths a G K cstar A R C₁ ε₀
        (∫ y, max (-y) 0 ∂μ) m k J K₁ K₂ K₃)ᶜ ≤ 2 * generalGridBeta A R q0 J := by
  let Q := StairGeometry.workingRegion a A R C₁ m
  let T := StairGeometry.threshold ε₀ K₂
  let t (k : ℕ) : ℝ := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
  let Cm : ℝ := ∫ y, max (-y) 0 ∂μ
  let Egeo (k : ℕ) := StairGeometry.goodEvent (StairGeometry.slopeCutoff a) K₁ K₃ (T k) (Q k)
  let Eweights (k : ℕ) := gridStaircaseWeightEvent (paths k) (T k) (t k) Cm
  let Ecap (k : ℕ) := gridUpperCap (Q k) (t k)
  let β := generalGridBeta A R q0 J
  have hβ : 0 < β / 3 := by
    dsimp only [β]
    exact div_pos (general_grid_beta_pos hA hR hq0 J) (by norm_num)
  have hQ (k : ℕ) : (Q k).Finite :=
    (stair_working_collars_finite a A R C₁ ha₀ ha₁ hA hR hC₁ m 0 k).subset
      fun z hz => ⟨z, hz, by simp [StairGeometry.latticeDistance]⟩
  have hgeo : Tendsto (fun k => (environmentLaw μ).real (Egeo k)ᶜ)
      (atTop ⊓ 𝓟 record) (𝓝 0) :=
    stair_geometry_event_tendsto_final μ p' hp' hmom' a ha₀ ha₁ A R C₁ ε₀ 11
      hA hR hC₁ hε₀ (by norm_num) K₁ K₂ K₃ hK₁ hK₂ hK₃ hK₃p hK₁p
      (by norm_num; exact hK₂p) k0 m record hm3
  have hweights : Tendsto (fun k => (environmentLaw μ).real (Eweights k)ᶜ)
      (atTop ⊓ 𝓟 record) (𝓝 0) :=
    grid_staircase_weight_failure_tendsto μ p' hp' hmom' ε₀ cstar hε₀
      (zero_lt_one.trans_le hcstar) K₂ hK₂p record Q hQ paths hmeas hvalid
  have hcap : Tendsto (fun k => (environmentLaw μ).real (Ecap k)ᶜ)
      (atTop ⊓ 𝓟 record) (𝓝 0) :=
    grid_working_cap_failure_tendsto μ hp hmom a A R C₁ ε₀ hA hR hC₁ hε₀ k0 m record hm3
  have hCp : 0 ≤ ∫ x : ℝ, (max x 0) ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hsmall := (heavy_vertex_block_tail_decay hp hCp hq0).2.filter_mono
    (inf_le_left : atTop ⊓ 𝓟 record ≤ atTop)
  have hrecord : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, 4 * k0 + 3 ≤ k ∧ k ∈ record :=
    eventually_inf_principal.mpr
      ((eventually_ge_atTop (4 * k0 + 3)).mono fun _ hk hr => ⟨hk, hr⟩)
  filter_upwards [hrecord, hsmall, hgeo.eventually (ge_mem_nhds hβ),
    hweights.eventually (ge_mem_nhds hβ), hcap.eventually (ge_mem_nhds hβ)] with k hk hs hg hw hh
  let Ecells := generalGridCellsGood a G K cstar A R k J (m k)
  have hcell : (environmentLaw μ).real Ecellsᶜ ≤ β :=
    general_grid_cells_failure_le μ hp hmom a G K cstar A R q0 hcstar hA hR hq0
      k0 k J (m k) hk0 hk.1 hJ (hm3 k (by omega) hk.2) (htrial k hk.2 hk.1) hs
  change (environmentLaw μ).real
    (((Ecells ∩ Egeo k) ∩ Eweights k) ∩ Ecap k)ᶜ ≤ 2 * β
  rw [Set.compl_inter, Set.compl_inter, Set.compl_inter]
  calc
    _ ≤ (environmentLaw μ).real ((Ecellsᶜ ∪ (Egeo k)ᶜ) ∪ (Eweights k)ᶜ) +
        (environmentLaw μ).real (Ecap k)ᶜ := measureReal_union_le _ _
    _ ≤ ((environmentLaw μ).real (Ecellsᶜ ∪ (Egeo k)ᶜ) +
        (environmentLaw μ).real (Eweights k)ᶜ) +
        (environmentLaw μ).real (Ecap k)ᶜ := by
      have h := measureReal_union_le (μ := environmentLaw μ) (Ecellsᶜ ∪ (Egeo k)ᶜ) (Eweights k)ᶜ
      linarith only [h]
    _ ≤ ((environmentLaw μ).real Ecellsᶜ + (environmentLaw μ).real (Egeo k)ᶜ) +
        (environmentLaw μ).real (Eweights k)ᶜ + (environmentLaw μ).real (Ecap k)ᶜ := by
      have h := measureReal_union_le (μ := environmentLaw μ) Ecellsᶜ (Egeo k)ᶜ
      linarith only [h]
    _ ≤ 2 * β := by linarith only [hcell, hg, hw, hh]

end LPPDifferentiability
