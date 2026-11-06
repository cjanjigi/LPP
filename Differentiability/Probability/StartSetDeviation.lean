/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Quadrant
public import LPP_Foundations.Probability.TranslationCylinder
public import LPP_Foundations.Probability.PassageMeasurable
public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Model.LastPassage.OptimalSplit
public import LPP_Foundations.Model.LastPassage.Axes
public import LPP_Foundations.Model.LastPassage.Bounds
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Expected positive deviation over start sets of linear size (finitely many base points) -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

private noncomputable def dev (g : Quadrant → ℝ) (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    ℝ :=
  lastPassage ω u d - ω u + ω (u + ((d.1 : ℤ), (d.2 : ℤ))) - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))

private theorem exists_scale (x : Quadrant) (h0 : x.1 + x.2 ≠ 0) :
    ∃ c : ℝ≥0, c * (x.1 + x.2) = 1 ∧ c * x.1 ≤ 1 ∧ c * x.2 ≤ 1 := by
  refine ⟨(x.1 + x.2)⁻¹, inv_mul_cancel₀ h0, ?_, ?_⟩ <;>
    calc _ ≤ (x.1 + x.2)⁻¹ * (x.1 + x.2) := by gcongr; simp
      _ = 1 := inv_mul_cancel₀ h0

private theorem exists_abs_bound (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x : Quadrant, |g x| ≤ Cg * ((x.1 : ℝ) + x.2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : Quadrant) (1, 1))).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases h0 : x.1 + x.2 = 0
  · obtain ⟨h1, h2⟩ := add_eq_zero.1 h0
    have h := hgh 0 x
    simp only [h1, h2, mul_zero, NNReal.coe_zero, zero_mul] at h
    rw [(Prod.ext h1 h2 : x = (0, 0)), h]; simp
  · obtain ⟨c, hc, h1, h2⟩ := exists_scale x h0
    have hb := hC _ (⟨bot_le, Prod.mk_le_mk.2 ⟨h1, h2⟩⟩ :
      ((c * x.1, c * x.2) : Quadrant) ∈ Icc (0 : Quadrant) (1, 1))
    rw [hgh, Real.norm_eq_abs, abs_mul, NNReal.abs_eq] at hb
    have hcR : (c : ℝ) * ((x.1 : ℝ) + x.2) = 1 := by exact_mod_cast hc
    calc |g x| = ((x.1 : ℝ) + x.2) * ((c : ℝ) * |g x|) := by
          rw [← mul_assoc, mul_comm ((x.1 : ℝ) + x.2), hcR, one_mul]
      _ ≤ ((x.1 : ℝ) + x.2) * max C 0 :=
          mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (by positivity)
      _ = max C 0 * ((x.1 : ℝ) + x.2) := mul_comm _ _

private theorem exists_modulus (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x) {η κ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ κ ∧ ∀ x a : Quadrant, x.1 + x.2 ≠ 0 →
      (a.1 : ℝ) + a.2 ≤ τ * ((x.1 : ℝ) + x.2) →
      g (a.1 + x.1, a.2 + x.2) ≤ g x + η * ((x.1 : ℝ) + x.2) := by
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (0 : Quadrant) (2, 2))).uniformContinuousOn_of_continuous
      hgc.continuousOn) η hη
  obtain ⟨τ, hτ0, hτ1, hτ2, hτ3⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ δ / 2 ∧ τ ≤ 1 ∧ τ ≤ κ :=
    ⟨min (min (δ / 2) 1) κ, lt_min (lt_min (half_pos hδ) one_pos) hκ,
      (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  refine ⟨τ, hτ0, hτ3, fun x a h0 hxa => ?_⟩
  obtain ⟨c, hc, hx1, hx2⟩ := exists_scale x h0
  have hcR : (c : ℝ) * ((x.1 : ℝ) + x.2) = 1 := by exact_mod_cast hc
  have hsR : (0 : ℝ) < (x.1 : ℝ) + x.2 := by exact_mod_cast pos_iff_ne_zero.2 h0
  have e1 : (c : ℝ) * x.1 ≤ 1 := by exact_mod_cast hx1
  have e2 : (c : ℝ) * x.2 ≤ 1 := by exact_mod_cast hx2
  have n1 : 0 ≤ (c : ℝ) * a.1 := by positivity
  have n2 : 0 ≤ (c : ℝ) * a.2 := by positivity
  have hca : (c : ℝ) * a.1 + c * a.2 ≤ τ :=
    calc _ = (c : ℝ) * ((a.1 : ℝ) + a.2) := by ring
      _ ≤ c * (τ * ((x.1 : ℝ) + x.2)) := mul_le_mul_of_nonneg_left hxa c.coe_nonneg
      _ = τ := by rw [mul_left_comm, hcR, mul_one]
  have hxm : ((c * x.1, c * x.2) : Quadrant) ∈ Icc (0 : Quadrant) (2, 2) :=
    ⟨bot_le, Prod.mk_le_mk.2 ⟨hx1.trans (by norm_num), hx2.trans (by norm_num)⟩⟩
  have hym : ((c * a.1 + c * x.1, c * a.2 + c * x.2) : Quadrant) ∈ Icc (0 : Quadrant) (2, 2) := by
    refine ⟨bot_le, Prod.mk_le_mk.2 ⟨?_, ?_⟩⟩
    · have : ((c * a.1 + c * x.1 : ℝ≥0) : ℝ) ≤ 2 := by push_cast; linarith
      exact_mod_cast this
    · have : ((c * a.2 + c * x.2 : ℝ≥0) : ℝ) ≤ 2 := by push_cast; linarith
      exact_mod_cast this
  have hdist : dist ((c * a.1 + c * x.1, c * a.2 + c * x.2) : Quadrant) (c * x.1, c * x.2) < δ := by
    rw [Prod.dist_eq, NNReal.dist_eq, NNReal.dist_eq]
    simp only [NNReal.coe_add, NNReal.coe_mul]
    refine max_lt ?_ ?_ <;> rw [abs_lt] <;> constructor <;> linarith
  have hlt := hu _ hym _ hxm hdist
  rw [Real.dist_eq, abs_lt] at hlt
  have hy : ((c * a.1 + c * x.1, c * a.2 + c * x.2) : Quadrant) =
      (c * (a.1 + x.1), c * (a.2 + x.2)) := by rw [mul_add, mul_add]
  have h1 : g (c * (a.1 + x.1), c * (a.2 + x.2)) = (c : ℝ) * g (a.1 + x.1, a.2 + x.2) :=
    hgh c (a.1 + x.1, a.2 + x.2)
  have h2 : g (c * x.1, c * x.2) = (c : ℝ) * g x := hgh c x
  rw [hy, h1, h2] at hlt
  have hlt' : (c : ℝ) * (g (a.1 + x.1, a.2 + x.2) - g x) < η := by linarith [hlt.2]
  have hfin : g (a.1 + x.1, a.2 + x.2) - g x ≤ η * ((x.1 : ℝ) + x.2) :=
    calc _ = ((x.1 : ℝ) + x.2) * ((c : ℝ) * (g (a.1 + x.1, a.2 + x.2) - g x)) := by
          rw [← mul_assoc, mul_comm ((x.1 : ℝ) + x.2), hcR, one_mul]
      _ ≤ ((x.1 : ℝ) + x.2) * η := mul_le_mul_of_nonneg_left hlt'.le hsR.le
      _ = _ := mul_comm _ _
  linarith

private theorem ex_split (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) :
    ∃ e : ℕ × ℕ, e ≤ d ∧ e.1 + e.2 = 1 ∧
      lastPassage ω u d - ω u = lastPassage ω (u + ((e.1 : ℤ), (e.2 : ℤ))) (d - e) := by
  obtain ⟨e, he, hl, h⟩ := exists_lastPassage_eq_split ω u d ⟨1, by omega⟩
  have hl' : e.1 + e.2 = 1 := hl
  have h1 : lastPassage ω u e = ω u := by
    obtain ⟨a, b⟩ := e
    dsimp only at hl'
    rcases (by omega : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [lastPassage_horizontal]
    · simp [lastPassage_vertical]
  exact ⟨e, he, hl', by rw [h, h1]; ring⟩

private theorem dev_le_crude (g : Quadrant → ℝ) (Cg : ℝ)
    (hCg : ∀ x : Quadrant, |g x| ≤ Cg * ((x.1 : ℝ) + x.2)) (ω : Environment)
    (h : ∀ z, ω z ≤ 1) (u : Lattice) (d : ℕ × ℕ) :
    dev g ω u d ≤ (1 + Cg) * ((d.1 : ℝ) + d.2) := by
  have h3 := (abs_le.mp (hCg ((d.1 : ℝ≥0), (d.2 : ℝ≥0)))).1
  simp only [NNReal.coe_natCast] at h3
  have hv := h (u + ((d.1 : ℤ), (d.2 : ℤ)))
  unfold dev
  rcases Nat.eq_zero_or_pos (d.1 + d.2) with h0 | hpos
  · obtain ⟨h1, h2⟩ : d.1 = 0 ∧ d.2 = 0 := by omega
    have hu0 : u + ((d.1 : ℤ), (d.2 : ℤ)) = u := Prod.ext (by simp [h1]) (by simp [h2])
    rw [hu0]
    obtain rfl : d = (0, 0) := Prod.ext h1 h2
    simpa using h3
  · obtain ⟨e, he, hl, hs⟩ := ex_split ω u d hpos
    have hle := lastPassage_le_const ω (u + ((e.1 : ℤ), (e.2 : ℤ))) (d - e) 1 h
    have hc : (((d - e).1 + (d - e).2 : ℕ) : ℝ) + 1 = (d.1 : ℝ) + d.2 := by
      obtain ⟨he1, he2⟩ := Prod.le_def.1 he
      have : (d - e).1 + (d - e).2 + 1 = d.1 + d.2 := by
        show d.1 - e.1 + (d.2 - e.2) + 1 = d.1 + d.2; omega
      exact_mod_cast this
    linarith

private theorem exists_base (C q N m k : ℕ) (hNm : N ≤ q * m) (hk : k ≤ C * N) (hm : 0 < m) :
    ∃ j : ℕ, j ≤ C * q ∧ ∃ a : ℕ × ℕ, a.1 + a.2 = m ∧
      ((-(((j + 1) * m : ℕ) : ℤ), ((j * m : ℕ) : ℤ)) : Lattice) + ((a.1 : ℤ), (a.2 : ℤ)) =
        (-(k : ℤ), (k : ℤ)) := by
  obtain ⟨j, r, hr, hjr, hj⟩ : ∃ j r : ℕ, r < m ∧ m * j + r = k ∧ j ≤ C * q :=
    ⟨k / m, k % m, Nat.mod_lt _ hm, Nat.div_add_mod k m, Nat.div_le_of_le_mul (by
      calc k ≤ C * N := hk
        _ ≤ C * (q * m) := Nat.mul_le_mul_left C hNm
        _ = m * (C * q) := by ring)⟩
  subst hjr
  refine ⟨j, hj, (m - r, r), by show m - r + r = m; omega, ?_⟩
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  have h1 : ((m - r : ℕ) : ℤ) = (m : ℤ) - r := Nat.cast_sub hr.le
  constructor
  · rw [h1]; push_cast; ring
  · push_cast; ring

private theorem dev_le (g : Quadrant → ℝ) (Cg ε η τ : ℝ) (S m N : ℕ) (hN : 0 < N)
    (hCg : ∀ x : Quadrant, |g x| ≤ Cg * ((x.1 : ℝ) + x.2))
    (hmod : ∀ x a : Quadrant, x.1 + x.2 ≠ 0 → (a.1 : ℝ) + a.2 ≤ τ * ((x.1 : ℝ) + x.2) →
      g (a.1 + x.1, a.2 + x.2) ≤ g x + η * ((x.1 : ℝ) + x.2))
    (hmτ : (m : ℝ) ≤ τ * N) (hSm : S ≤ m) (ω : Environment) (hω1 : ∀ z, ω z ≤ 1)
    (o u : Lattice) (a d : ℕ × ℕ) (hu : o + ((a.1 : ℤ), (a.2 : ℤ)) = u) (ha : a.1 + a.2 = m)
    (hd : d.1 + d.2 = N)
    (hgood : ∀ z : ℕ × ℕ, S ≤ z.1 + z.2 →
      |lastPassage ω o z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ)) :
    dev g ω u d ≤ η * N + (Cg + 2 * ε) * m + ε * N + (Cg + ε + 1) := by
  unfold dev
  obtain ⟨e, he, hl, hs⟩ := ex_split ω u d (by omega)
  obtain ⟨he1, he2⟩ := Prod.le_def.1 he
  have hae : a + e + (d - e) = a + d :=
    Prod.ext (show a.1 + e.1 + (d.1 - e.1) = a.1 + d.1 by omega)
      (show a.2 + e.2 + (d.2 - e.2) = a.2 + d.2 by omega)
  have hue : o + (((a + e).1 : ℤ), ((a + e).2 : ℤ)) = u + ((e.1 : ℤ), (e.2 : ℤ)) := by
    rw [← hu]; ext <;> simp [add_assoc]
  have hsup := lastPassage_superadditive ω o (a + e) (d - e)
  rw [hae, hue] at hsup
  have hz : (a + d).1 + (a + d).2 = m + N := by show (a.1 + d.1) + (a.2 + d.2) = m + N; omega
  have hz' : (a + e).1 + (a + e).2 = m + 1 := by show (a.1 + e.1) + (a.2 + e.2) = m + 1; omega
  have hA := abs_le.mp (hgood (a + d) (by rw [hz]; omega))
  have hB := abs_le.mp (hgood (a + e) (by rw [hz']; omega))
  have hzc : (((a + d).1 + (a + d).2 : ℕ) : ℝ) = (m : ℝ) + N := by rw [hz]; push_cast; ring
  have hzc' : (((a + e).1 + (a + e).2 : ℕ) : ℝ) = (m : ℝ) + 1 := by rw [hz']; push_cast; ring
  have hgz : ((((a + d).1 : ℕ) : ℝ≥0), (((a + d).2 : ℕ) : ℝ≥0)) =
      ((a.1 : ℝ≥0) + d.1, (a.2 : ℝ≥0) + d.2) := by ext <;> simp
  rw [hzc, hgz] at hA
  rw [hzc'] at hB
  have hdc : (d.1 : ℝ) + d.2 = N := by exact_mod_cast hd
  have hmc : (a.1 : ℝ) + a.2 = m := by exact_mod_cast ha
  have hm' := hmod ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) ((a.1 : ℝ≥0), (a.2 : ℝ≥0))
    (by show (d.1 : ℝ≥0) + d.2 ≠ 0; rw [← Nat.cast_add, hd]; exact Nat.cast_ne_zero.2 hN.ne')
    (by simp only [NNReal.coe_natCast]; rw [hmc, hdc]; exact hmτ)
  have hga := (abs_le.mp (hCg (((a + e).1 : ℝ≥0), ((a + e).2 : ℝ≥0)))).1
  simp only [NNReal.coe_natCast] at hm' hga
  have hec : (((a + e).1 : ℕ) : ℝ) + ((a + e).2 : ℕ) = m + 1 := by exact_mod_cast hz'
  have hv := hω1 (u + ((d.1 : ℤ), (d.2 : ℤ)))
  rw [hdc] at hm'
  rw [hec] at hga
  linarith [hA.1, hA.2, hB.1, hB.2]

private theorem exists_cutoff (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : Quadrant → ℝ)
    (hgs : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ (S : ℕ) (B : Set Environment), MeasurableSet B ∧ (environmentLaw ν).real B ≤ ρ ∧
      ∀ ω ∉ B, ∀ z : ℕ × ℕ, S ≤ z.1 + z.2 →
        |lastPassage ω 0 z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  let B : ℕ → Set Environment := fun S => ⋃ z : ℕ × ℕ, ⋃ (_ : S ≤ z.1 + z.2),
    {ω : Environment | ε * ((z.1 + z.2 : ℕ) : ℝ) <
      |lastPassage ω 0 z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))|}
  have hmeas : ∀ S, MeasurableSet (B S) := fun S =>
    MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const ((measurable_lastPassage 0 z).sub_const _).abs
  have hanti : Antitone B := fun S T hST ω hω => by
    obtain ⟨z, hz0⟩ := mem_iUnion.1 hω
    obtain ⟨hz, hlt⟩ := mem_iUnion.1 hz0
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨hST.trans hz, hlt⟩⟩
  have hnull : environmentLaw ν (⋂ S, B S) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hgs)
    show ¬ _
    intro hshape
    obtain ⟨N, _, hN⟩ := hshape ε hε
    obtain ⟨z, hz0⟩ := mem_iUnion.1 (mem_iInter.1 hω N)
    obtain ⟨hz, hlt⟩ := mem_iUnion.1 hz0
    exact absurd (hN z hz) (not_le.2 hlt)
  have hlim := tendsto_measure_iInter_atTop (μ := environmentLaw ν)
    (fun S => (hmeas S).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hnull] at hlim
  obtain ⟨S, hS⟩ := ((tendsto_order.1 hlim).2 (ENNReal.ofReal ρ) (ENNReal.ofReal_pos.2 hρ)).exists
  refine ⟨S, B S, hmeas S, ENNReal.toReal_le_of_le_ofReal hρ.le hS.le, ?_⟩
  intro ω hω z hz
  exact not_lt.1 fun hlt => hω (mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨hz, hlt⟩⟩)

theorem expected_max_positive_deviation_startSet (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (C : ℕ) :
    let D : ℕ → Environment → ℝ := fun N ω =>
      ⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
        max (lastPassage ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) - ω (-(k : ℤ), (k : ℤ)) +
          ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
          g (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0))) 0
    (∀ N : ℕ, Integrable (D N) (environmentLaw ν)) ∧
      Tendsto (fun N : ℕ => (∫ ω, D N ω ∂environmentLaw ν) / N) atTop (𝓝 0) := by
  intro D
  have _ := hgconc
  have _ := hneg
  obtain ⟨Cg, hCg0, hCg⟩ := exists_abs_bound g hgcont hghom
  have hle1 : ∀ᵐ ω ∂environmentLaw ν, ∀ z : Lattice, ω z ≤ 1 :=
    ae_all_iff.2 fun z => ae_of_ae_map (p := fun t : ℝ => t ≤ 1)
      (measurable_environment_eval z).aemeasurable (by rw [environmentLaw_map_eval]; exact hle)
  have hDdef : ∀ (N : ℕ) (ω : Environment), D N ω = ⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
      max (dev g ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i)) 0 := fun _ _ => rfl
  have hD0 : ∀ (N : ℕ) (ω : Environment), 0 ≤ D N ω := fun N ω => by
    rw [hDdef]
    exact le_ciSup_of_le (Set.finite_range _).bddAbove 0
      (le_ciSup_of_le (Set.finite_range _).bddAbove 0 (le_max_right _ _))
  have hDle : ∀ (N : ℕ) (ω : Environment), (∀ z, ω z ≤ 1) → D N ω ≤ (1 + Cg) * N := by
    intro N ω hω
    rw [hDdef]
    refine ciSup_le fun k => ciSup_le fun i =>
      max_le ?_ (mul_nonneg (by linarith) (Nat.cast_nonneg N))
    have h : dev g ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) ≤
        (1 + Cg) * (((i : ℕ) : ℝ) + ((N - i : ℕ) : ℝ)) :=
      dev_le_crude g Cg hCg ω hω _ ((i : ℕ), N - i)
    have hi : (i : ℕ) + (N - i) = N := by have := i.isLt; omega
    rwa [← Nat.cast_add, hi] at h
  have hDmeas : ∀ N, Measurable (D N) := fun N => by
    have : D N = fun ω => ⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
        max (dev g ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i)) 0 := funext (hDdef N)
    rw [this]
    exact Measurable.iSup fun k => Measurable.iSup fun i =>
      ((((measurable_lastPassage _ _).sub (measurable_environment_eval _)).add
        (measurable_environment_eval _)).sub_const _).max measurable_const
  have hint : ∀ N, Integrable (D N) (environmentLaw ν) := fun N =>
    Integrable.of_bound (hDmeas N).aestronglyMeasurable ((1 + Cg) * N) (by
      filter_upwards [hle1] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 N ω)]; exact hDle N ω hω)
  refine ⟨hint, ?_⟩
  have key : ∀ η0 : ℝ, 0 < η0 → ∃ N1 : ℕ, ∀ N ≥ N1,
      (∫ ω, D N ω ∂environmentLaw ν) / N ≤ η0 := by
    intro η0 hη0
    obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = η0 / 8 := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hεd]; positivity
    obtain ⟨τ, hτ, hτκ, hmod⟩ := exists_modulus g hgcont hghom hε
      (by positivity : 0 < ε / (Cg + 2 * ε))
    obtain ⟨q, hq⟩ := exists_nat_ge (2 / τ)
    have hq1 : 0 < q := by exact_mod_cast lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / τ) hq
    have hqτ : 2 ≤ τ * q := by have := (div_le_iff₀ hτ).1 hq; linarith
    obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = η0 / (4 * (1 + Cg)) := ⟨_, rfl⟩
    have hρ : 0 < ρ := by rw [hρd]; positivity
    have hK0 : (1 + Cg) ≠ 0 := by positivity
    have hρK : ρ * (1 + Cg) = η0 / 4 := by rw [hρd]; field_simp
    have hCq0 : ((C * q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcne : Cg + 2 * ε ≠ 0 := by positivity
    obtain ⟨S, Bd, hBm, hBp, hBg⟩ := exists_cutoff ν g hgshape ε (ρ / ((C * q + 1 : ℕ) : ℝ)) hε
      (by positivity)
    obtain ⟨N3, hN3⟩ := exists_nat_ge ((S + 1) / τ)
    obtain ⟨N4, hN4⟩ := exists_nat_ge (4 * (Cg + ε + 1) / η0)
    refine ⟨q + N3 + N4, fun N hN => ?_⟩
    have hNq : q ≤ N := by omega
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (hq1.trans_le hNq)
    have hNτ : (S : ℝ) + 1 ≤ τ * N := by
      have := (div_le_iff₀ hτ).1 (hN3.trans (by exact_mod_cast (by omega : N3 ≤ N) : (N3 : ℝ) ≤ N))
      linarith
    obtain ⟨m, hmd⟩ : ∃ m : ℕ, m = ⌊τ * N⌋₊ := ⟨_, rfl⟩
    have hmτ : (m : ℝ) ≤ τ * N := by rw [hmd]; exact Nat.floor_le (by positivity)
    have hmlt : τ * N < m + 1 := by rw [hmd]; exact Nat.lt_floor_add_one _
    have hSm : S + 1 ≤ m := by rw [hmd]; exact Nat.le_floor (by push_cast; exact hNτ)
    have hm1 : N ≤ q * m := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have h1 : (N : ℝ) ≤ q * m := by
        nlinarith [mul_le_mul_of_nonneg_right hqτ hNpos.le, mul_lt_mul_of_pos_left hmlt hqR,
          (by exact_mod_cast hNq : (q : ℝ) ≤ N)]
      exact_mod_cast h1
    have hmε : (Cg + 2 * ε) * m ≤ ε * N :=
      calc _ ≤ (Cg + 2 * ε) * (τ * N) := mul_le_mul_of_nonneg_left hmτ (by positivity)
        _ ≤ (Cg + 2 * ε) * (ε / (Cg + 2 * ε) * N) := by gcongr
        _ = ε * N := by field_simp
    obtain ⟨Bj, hBj⟩ : ∃ Bj : ℕ → Set Environment, ∀ j, Bj j = (fun ω : Environment => fun z =>
        ω ((-(((j + 1) * m : ℕ) : ℤ), ((j * m : ℕ) : ℤ)) + z)) ⁻¹' Bd := ⟨_, fun _ => rfl⟩
    have hBjr : ∀ j, (environmentLaw ν).real (Bj j) ≤ ρ / ((C * q + 1 : ℕ) : ℝ) := fun j => by
      rw [hBj, (measurePreserving_environment_translation ν _).measureReal_preimage
        hBm.nullMeasurableSet]
      exact hBp
    obtain ⟨bad, hbadd⟩ : ∃ bad : Set Environment,
        bad = ⋃ j ∈ Finset.range (C * q + 1), Bj j := ⟨_, rfl⟩
    have hbadm : MeasurableSet bad := by
      rw [hbadd]
      exact Finset.measurableSet_biUnion _ fun j _ => by
        rw [hBj]; exact (measurePreserving_environment_translation ν _).measurable hBm
    have hbadr : (environmentLaw ν).real bad ≤ ρ := by
      rw [hbadd]
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      calc _ ≤ ∑ j ∈ Finset.range (C * q + 1), ρ / ((C * q + 1 : ℕ) : ℝ) :=
            Finset.sum_le_sum fun j _ => hBjr j
        _ = ρ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    have hpt : ∀ ω : Environment, (∀ z, ω z ≤ 1) → ω ∉ bad →
        D N ω ≤ ε * N + (Cg + 2 * ε) * m + ε * N + (Cg + ε + 1) := by
      intro ω hω hnb
      rw [hDdef]
      refine ciSup_le fun k => ciSup_le fun i => max_le ?_ (by positivity)
      obtain ⟨j, hj, a, ha, hu⟩ := exists_base C q N m k hm1 (by have := k.isLt; omega)
        (by omega)
      have hnj : ω ∉ Bj j := fun h => hnb (by
        rw [hbadd]; exact mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (by omega), h⟩)
      rw [hBj] at hnj
      refine dev_le g Cg ε ε τ S m N (by omega) hCg hmod hmτ (by omega) ω hω _ _ a
        ((i : ℕ), N - i) hu ha (by have := i.isLt; show (i : ℕ) + (N - i) = N; omega) ?_
      intro z hz
      have := hBg (fun z => ω ((-(((j + 1) * m : ℕ) : ℤ), ((j * m : ℕ) : ℤ)) + z)) hnj z hz
      rwa [lastPassage_translate, add_zero] at this
    have hg : Integrable (fun ω => (ε * N + (Cg + 2 * ε) * m + ε * N + (Cg + ε + 1)) +
        bad.indicator (fun _ => (1 + Cg) * N) ω) (environmentLaw ν) :=
      (integrable_const _).add ((integrable_const _).indicator hbadm)
    have hae : ∀ᵐ ω ∂environmentLaw ν, D N ω ≤ (ε * N + (Cg + 2 * ε) * m + ε * N + (Cg + ε + 1)) +
        bad.indicator (fun _ => (1 + Cg) * N) ω := by
      filter_upwards [hle1] with ω hω
      by_cases hb : ω ∈ bad
      · simp only [indicator_of_mem hb]
        have : 0 ≤ ε * N + (Cg + 2 * ε) * m + ε * N + (Cg + ε + 1) := by positivity
        linarith [hDle N ω hω]
      · simp only [indicator_of_notMem hb, add_zero]; exact hpt ω hω hb
    have hmono := integral_mono_ae (hint N) hg hae
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hbadm), integral_const,
      integral_indicator_const _ hbadm, probReal_univ, smul_eq_mul, smul_eq_mul, one_mul] at hmono
    rw [div_le_iff₀ hNpos]
    have hbd : (environmentLaw ν).real bad * ((1 + Cg) * N) ≤ ρ * ((1 + Cg) * N) :=
      mul_le_mul_of_nonneg_right hbadr (by positivity)
    have hρN : ρ * ((1 + Cg) * N) = η0 / 4 * N := by rw [← mul_assoc, hρK]
    have hK : 4 * (Cg + ε + 1) ≤ η0 * N := by
      have := (div_le_iff₀ hη0).1 (hN4.trans (by exact_mod_cast (by omega : N4 ≤ N) : (N4 : ℝ) ≤ N))
      linarith
    subst hεd
    linarith [mul_pos hη0 hNpos]
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun N => lt_of_lt_of_le hx
    (div_nonneg (integral_nonneg (hD0 N)) (Nat.cast_nonneg N)), fun x hx => ?_⟩
  obtain ⟨N1, hN1⟩ := key (x / 2) (by linarith)
  exact eventually_atTop.2 ⟨N1, fun N hN => lt_of_le_of_lt (hN1 N hN) (by linarith)⟩

end LPPDifferentiability
