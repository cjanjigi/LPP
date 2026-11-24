/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.ReachableSetContour
public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Model.Paths.Concat
public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Probability.CoordinateLaw
public import LPP_Foundations.Probability.DisjointSupportEvents
public import Differentiability.Probability.FiniteContourFamilyBadEvent
import Differentiability.FinalDraft.StairGeometry.Reach
import Mathlib.Tactic

/-!
# Tail of the reachable set

The probability that the forward or backward reachable set of a site is finite and large,
when very bad sites are rare, is small, by the contour argument.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The forward reachable set, as in the statements below. -/
private abbrev reachSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  StairGeometry.reachSet ω T z

/-- The backward reachable set, as in the statements below. -/
private abbrev reachBackSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  StairGeometry.reachBackSet ω T z

private theorem vertex_mem_reach {ω : Environment} {T : ℝ} {z : Lattice} {d : ℕ × ℕ}
    (q : Path z d) (hg : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : q.vertex k ∈ reachSet ω T z := by
  refine ⟨q.splitDisplacement k, q.prefixPath k, (q.split_vertex k).symm, fun i hi => ?_⟩
  have hk := q.splitDisplacement_length k
  have hk2 := k.isLt
  exact hg ⟨i.val, by show i.val < _; omega⟩ (by show i.val < _; omega)

private theorem reach_step {ω : Environment} {T : ℝ} {z y : Lattice} (hy : y ∈ reachSet ω T z)
    (hg : -T ≤ ω y) (e : ℕ × ℕ) (he : e = (1, 0) ∨ e = (0, 1)) :
    y + ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachSet ω T z :=
  StairGeometry.reach_step hy hg e he

private theorem reach_pred {ω : Environment} {T : ℝ} {z y : Lattice} (hy : y ∈ reachSet ω T z)
    (hne : y ≠ z) : ∃ e : ℕ × ℕ, (e = (1, 0) ∨ e = (0, 1)) ∧
      y - ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachSet ω T z := by
  obtain ⟨d, q, rfl, hq⟩ := hy
  have hd : 1 ≤ d.1 + d.2 := by
    by_contra h
    exact hne (by apply Prod.ext <;> simp <;> omega)
  have hm := vertex_mem_reach q hq ⟨d.1 + d.2 - 1, by omega⟩
  have hs : (⟨d.1 + d.2 - 1, by omega⟩ : Fin (d.1 + d.2)).succ = Fin.last (d.1 + d.2) :=
    Fin.ext (by simp; omega)
  have hsl := q.step ⟨d.1 + d.2 - 1, by omega⟩
  rw [hs, q.finish] at hsl
  rcases hsl with h | h
  · refine ⟨(1, 0), Or.inl rfl, ?_⟩
    convert hm using 1
    rw [h]; apply Prod.ext <;> simp
  · refine ⟨(0, 1), Or.inr rfl, ?_⟩
    convert hm using 1
    rw [h]; apply Prod.ext <;> simp

private theorem vertex_mem_reachBack {ω : Environment} {T : ℝ} {z y : Lattice} {d : ℕ × ℕ}
    (q : Path y d) (hz : y + ((d.1 : ℤ), (d.2 : ℤ)) = z)
    (hg : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : q.vertex k ∈ reachBackSet ω T z := by
  have hle := q.splitDisplacement_le k
  refine ⟨d - q.splitDisplacement k, q.suffix k, ?_, fun i hi => ?_⟩
  · have h1 := q.splitDisplacement_fst_cast k
    have h2 := q.splitDisplacement_snd_cast k
    rw [← hz]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
  · have hl := q.suffix_length k
    have hk2 := k.isLt
    exact hg ⟨k.val + i.val, by show k.val + i.val < _; omega⟩ (by show k.val + i.val < _; omega)

private theorem reachBack_step {ω : Environment} {T : ℝ} {z y : Lattice}
    (e : ℕ × ℕ) (he : e = (1, 0) ∨ e = (0, 1))
    (hy : y + ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachBackSet ω T z) (hg : -T ≤ ω y) :
    y ∈ reachBackSet ω T z :=
  StairGeometry.reachBack_step e he hy hg

private theorem reachBack_succ {ω : Environment} {T : ℝ} {z y : Lattice}
    (hy : y ∈ reachBackSet ω T z) (hne : y ≠ z) : ∃ e : ℕ × ℕ, (e = (1, 0) ∨ e = (0, 1)) ∧
      y + ((e.1 : ℤ), (e.2 : ℤ)) ∈ reachBackSet ω T z := by
  obtain ⟨d, q, hz, hq⟩ := hy
  have hd : 1 ≤ d.1 + d.2 := by
    by_contra h
    exact hne (by rw [← hz]; apply Prod.ext <;> simp <;> omega)
  have hm := vertex_mem_reachBack q hz hq ⟨1, by omega⟩
  have hs := q.step ⟨0, by omega⟩
  rw [show ((⟨0, by omega⟩ : Fin (d.1 + d.2)).castSucc : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext rfl,
    q.start, show (⟨0, by omega⟩ : Fin (d.1 + d.2)).succ = (⟨1, by omega⟩ : Fin (d.1 + d.2 + 1))
      from Fin.ext rfl] at hs
  rcases hs with h | h
  · refine ⟨(1, 0), Or.inl rfl, ?_⟩
    convert hm using 1
    rw [h]; apply Prod.ext <;> simp
  · refine ⟨(0, 1), Or.inr rfl, ?_⟩
    convert hm using 1
    rw [h]; apply Prod.ext <;> simp

private theorem forward_cells {ω : Environment} {T : ℝ} {z : Lattice}
    (hfin : (reachSet ω T z).Finite) :
    ∃ Tf : Finset Lattice, Tf.card = (reachSet ω T z).ncard ∧ (∀ x ∈ Tf, 0 ≤ x.1 ∧ 0 ≤ x.2) ∧
      ((0, 0) : Lattice) ∈ Tf ∧ (∀ x ∈ Tf, x ≠ (0, 0) → x - (1, 0) ∈ Tf ∨ x - (0, 1) ∈ Tf) ∧
      (∀ x ∈ Tf, -T ≤ ω (z + x) → x + (1, 0) ∈ Tf ∧ x + (0, 1) ∈ Tf) := by
  classical
  have hmem : ∀ x, x ∈ hfin.toFinset.image (· - z) ↔ z + x ∈ reachSet ω T z := by
    intro x
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun h => ⟨z + x, h, by simp⟩⟩
  have hz : z ∈ reachSet ω T z := ⟨(0, 0), horizontalFirst z (0, 0), by simp, fun i hi => by simp at hi⟩
  refine ⟨hfin.toFinset.image (· - z), ?_, fun x hx => ?_, ?_, fun x hx hne => ?_, fun x hx hg => ?_⟩
  · rw [Finset.card_image_of_injective _ sub_left_injective, Set.ncard_eq_toFinset_card _ hfin]
  · obtain ⟨d, q, h, -⟩ := (hmem x).mp hx
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    constructor <;> omega
  · exact (hmem _).mpr (by rw [show ((0, 0) : Lattice) = 0 from rfl, add_zero]; exact hz)
  · obtain ⟨e, he, hp⟩ := reach_pred ((hmem x).mp hx) (fun h => hne (by simpa using h : x = 0))
    rcases he with rfl | rfl
    · exact Or.inl ((hmem _).mpr (by simpa [add_sub_assoc] using hp))
    · exact Or.inr ((hmem _).mpr (by simpa [add_sub_assoc] using hp))
  · have h := (hmem x).mp hx
    exact ⟨(hmem _).mpr (by simpa [add_assoc] using reach_step h hg (1, 0) (Or.inl rfl)),
      (hmem _).mpr (by simpa [add_assoc] using reach_step h hg (0, 1) (Or.inr rfl))⟩

private theorem backward_cells {ω : Environment} {T : ℝ} {z : Lattice}
    (hfin : (reachBackSet ω T z).Finite) :
    ∃ Tb : Finset Lattice, Tb.card = (reachBackSet ω T z).ncard ∧ (∀ x ∈ Tb, 0 ≤ x.1 ∧ 0 ≤ x.2) ∧
      ((0, 0) : Lattice) ∈ Tb ∧ (∀ x ∈ Tb, x ≠ (0, 0) → x - (1, 0) ∈ Tb ∨ x - (0, 1) ∈ Tb) ∧
      (∀ x ∈ Tb, -T ≤ ω (z - (x + (1, 0))) → x + (1, 0) ∈ Tb) ∧
      (∀ x ∈ Tb, -T ≤ ω (z - (x + (0, 1))) → x + (0, 1) ∈ Tb) := by
  classical
  have hmem : ∀ x, x ∈ hfin.toFinset.image (fun y => z - y) ↔ z - x ∈ reachBackSet ω T z := by
    intro x
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun h => ⟨z - x, h, by simp⟩⟩
  have hz : z ∈ reachBackSet ω T z :=
    ⟨(0, 0), horizontalFirst z (0, 0), by simp, fun i hi => by simp at hi⟩
  refine ⟨hfin.toFinset.image (fun y => z - y), ?_, fun x hx => ?_, ?_, fun x hx hne => ?_,
    fun x hx hg => ?_, fun x hx hg => ?_⟩
  · rw [Finset.card_image_of_injective _ sub_right_injective, Set.ncard_eq_toFinset_card _ hfin]
  · obtain ⟨d, q, h, -⟩ := (hmem x).mp hx
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h1 h2
    constructor <;> omega
  · exact (hmem _).mpr (by rw [show ((0, 0) : Lattice) = 0 from rfl, sub_zero]; exact hz)
  · obtain ⟨e, he, hp⟩ := reachBack_succ ((hmem x).mp hx) (fun h => hne (by simpa using h : x = 0))
    rcases he with rfl | rfl
    · exact Or.inl ((hmem _).mpr (by convert hp using 1; simp; abel))
    · exact Or.inr ((hmem _).mpr (by convert hp using 1; simp; abel))
  · exact (hmem _).mpr (reachBack_step (1, 0) (Or.inl rfl) (by simpa [sub_add_eq_sub_sub] using (hmem x).mp hx) hg)
  · exact (hmem _).mpr (reachBack_step (0, 1) (Or.inr rfl) (by simpa [sub_add_eq_sub_sub] using (hmem x).mp hx) hg)
private theorem measureReal_iUnion_le_tsum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : ℕ → Set Ω) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (hs : Summable t)
    (hE : ∀ n, P.real (E n) ≤ t n) : P.real (⋃ n, E n) ≤ ∑' n, t n := by
  have hEach (n : ℕ) : P (E n) ≤ ENNReal.ofReal (t n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E n))]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have hUnion : P (⋃ n, E n) ≤ ENNReal.ofReal (∑' n, t n) :=
    calc _ ≤ ∑' n, P (E n) := measure_iUnion_le E
      _ ≤ ∑' n, ENNReal.ofReal (t n) := ENNReal.tsum_le_tsum hEach
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg ht hs).symm
  simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg ht)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hUnion

/-- Independent coordinates: some walk of a finite family has all its labelled sites very bad
with probability at most the family size times `ζ ^ ((n + 4) / 8)`. -/
private theorem bad_family_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (φ : ℕ × ℕ → Lattice) (hφ : Function.Injective φ) (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hζ : μ.real (Set.Iio (-T)) ≤ ζ) (n : ℕ) {ι : Type*} (W : Finset ι) (L : ι → Finset (ℕ × ℕ))
    (hL : ∀ v ∈ W, n + 4 ≤ 8 * (L v).card) :
    (environmentLaw μ).real {ω : Environment | ∃ v ∈ W, ∀ x ∈ L v, ω (φ x) < -T} ≤
      W.card * ζ ^ (((n : ℝ) + 4) / 8) := by
  classical
  let G : ℕ × ℕ → Set Environment := fun x => {ω | -T ≤ ω (φ x)}
  have hGm : ∀ x, MeasurableSet (G x) := fun x =>
    measurableSet_le measurable_const (measurable_environment_eval _)
  have hmarg : ∀ x, MeasurableSet (G x) → (environmentLaw μ).real (G x)ᶜ ≤ ζ := by
    intro x _
    have : (G x)ᶜ = (fun ω : Environment => ω (φ x)) ⁻¹' Set.Iio (-T) := by ext ω; simp [G]
    rw [this, ← map_measureReal_apply (measurable_environment_eval _) measurableSet_Iio,
      environmentLaw_map_eval]
    exact hζ
  have hindep : ∀ S : Finset (ℕ × ℕ), (∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      0 < Nat.dist u.1 v.1 ∨ 0 < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u // u ∈ S} => G v.1) (environmentLaw μ) := by
    intro S _
    refine iIndepSet_environment_of_disjoint_supports μ _ (fun v => {φ v.1}) (fun v => hGm _)
      (fun v ω ω' h => ?_) (fun v w hvw => ?_)
    · show -T ≤ ω (φ v.1) ↔ -T ≤ ω' (φ v.1)
      rw [h (φ v.1) (Finset.mem_singleton_self _)]
    · exact Finset.disjoint_singleton.mpr fun h => hvw (Subtype.ext (hφ h))
  have := (measurable_and_measureReal_exists_all_bad_natural_site_family_le (environmentLaw μ) G
    hGm 0 (n + 4) ζ hζ0 hζ1 hmarg hindep W L hL).2
  convert this using 3 <;> simp [G]

/-- The union bound over all walk lengths from `4 m1 - 4` on. -/
private theorem union_bound (m1 : ℕ) (hm1 : 1 ≤ m1)
    (W : (n : ℕ) → Finset (Fin (n + 5) → Lattice))
    (L : (n : ℕ) → (Fin (n + 5) → Lattice) → Finset (ℕ × ℕ))
    (hW : ∀ n, (W n).card ≤ (n + 6) ^ 2 * 4 * 3 ^ (n + 3))
    (hL : ∀ n, ∀ v ∈ W n, n + 4 ≤ 8 * (L n v).card) :
    ∃ K p : ℝ, 0 < p ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (φ : ℕ × ℕ → Lattice),
      Function.Injective φ → μ.real (Set.Iio (-T)) ≤ p →
      (environmentLaw μ).real (⋃ j : ℕ, {ω : Environment | ∃ v ∈ W (4 * m1 - 4 + j),
        ∀ x ∈ L (4 * m1 - 4 + j) v, ω (φ x) < -T}) ≤ K * (μ.real (Set.Iio (-T))) ^ ((m1 : ℝ) / 2) := by
  classical
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = 4 * m1 - 4 := ⟨_, rfl⟩
  have hn04 : n0 + 4 = 4 * m1 := by omega
  rw [← hn0]
  have hm1r : (0 : ℝ) < m1 := by exact_mod_cast hm1
  refine ⟨2 * (4 ^ (n0 + 7) * 3 ^ (n0 + 3)), (1 / 24 : ℝ) ^ 8, by positivity, ?_⟩
  intro μ _ T φ hφ hp
  set pT := μ.real (Set.Iio (-T)) with hpT
  have key : ∀ ζ : ℝ, 0 < ζ → ζ ≤ (1 / 24 : ℝ) ^ 8 → pT ≤ ζ →
      (environmentLaw μ).real (⋃ j : ℕ, {ω : Environment | ∃ v ∈ W (n0 + j),
        ∀ x ∈ L (n0 + j) v, ω (φ x) < -T}) ≤
        2 * (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * ζ ^ ((m1 : ℝ) / 2) := by
    intro ζ hζ0 hζp hpζ
    have hζ1 : ζ < 1 := lt_of_le_of_lt hζp (by norm_num)
    have hr0 : 0 ≤ ζ ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hζ0.le _
    have hr : ζ ^ ((1 : ℝ) / 8) ≤ 1 / 24 :=
      calc ζ ^ ((1 : ℝ) / 8) ≤ ((1 / 24 : ℝ) ^ 8) ^ ((1 : ℝ) / 8) :=
            Real.rpow_le_rpow hζ0.le hζp (by norm_num)
        _ = 1 / 24 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    let t : ℕ → ℝ := fun j =>
      (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * ζ ^ ((m1 : ℝ) / 2) * (1 / 2) ^ j
    have hE : ∀ j, (environmentLaw μ).real {ω : Environment | ∃ v ∈ W (n0 + j),
        ∀ x ∈ L (n0 + j) v, ω (φ x) < -T} ≤ t j := by
      intro j
      have h1 := bad_family_bound μ T φ hφ ζ hζ0 hζ1 hpζ (n0 + j) (W (n0 + j)) (L (n0 + j))
        (hL (n0 + j))
      have hsq : (n0 + j + 6) ^ 2 ≤ 4 ^ (n0 + j + 6) := by
        have := Nat.lt_two_pow_self (n := n0 + j + 6)
        calc _ ≤ (2 ^ (n0 + j + 6)) ^ 2 := Nat.pow_le_pow_left this.le 2
          _ = _ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hcard : ((W (n0 + j)).card : ℝ) ≤
          4 ^ (n0 + 7) * 3 ^ (n0 + 3) * (4 ^ j * 3 ^ j) := by
        have : (W (n0 + j)).card ≤ 4 ^ (n0 + 7) * 3 ^ (n0 + 3) * (4 ^ j * 3 ^ j) :=
          (hW _).trans (by
            calc _ ≤ 4 ^ (n0 + j + 6) * 4 * 3 ^ (n0 + j + 3) := by gcongr
              _ = _ := by ring)
        exact_mod_cast this
      have hexp : ζ ^ (((↑(n0 + j) : ℝ) + 4) / 8) = ζ ^ ((m1 : ℝ) / 2) * (ζ ^ ((1 : ℝ) / 8)) ^ j := by
        have : ((↑(n0 + j) : ℝ) + 4) / 8 = (m1 : ℝ) / 2 + (1 / 8) * j := by
          have : ((n0 : ℕ) : ℝ) + 4 = 4 * m1 := by exact_mod_cast hn04
          push_cast; linarith
        rw [this, Real.rpow_add hζ0, Real.rpow_mul_natCast hζ0.le]
      rw [hexp] at h1
      have hz : 0 ≤ ζ ^ ((m1 : ℝ) / 2) := Real.rpow_nonneg hζ0.le _
      have h12 : (4 : ℝ) ^ j * 3 ^ j * (ζ ^ ((1 : ℝ) / 8)) ^ j ≤ (1 / 2) ^ j := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) j
      calc _ ≤ _ := h1
        _ ≤ 4 ^ (n0 + 7) * 3 ^ (n0 + 3) * (4 ^ j * 3 ^ j) *
            (ζ ^ ((m1 : ℝ) / 2) * (ζ ^ ((1 : ℝ) / 8)) ^ j) := by gcongr
        _ = (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * ζ ^ ((m1 : ℝ) / 2) *
            (4 ^ j * 3 ^ j * (ζ ^ ((1 : ℝ) / 8)) ^ j) := by ring
        _ ≤ t j := mul_le_mul_of_nonneg_left h12 (by positivity)
    calc _ ≤ ∑' j, t j := measureReal_iUnion_le_tsum _ _ t (fun j => by positivity)
          (summable_geometric_two.mul_left _) hE
      _ = _ := by simp only [t]; rw [tsum_mul_left, tsum_geometric_two]; ring
  rcases (show 0 ≤ pT from measureReal_nonneg).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), mul_zero]
    have hev : ∀ᶠ ζ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (environmentLaw μ).real (⋃ j : ℕ,
        {ω : Environment | ∃ v ∈ W (n0 + j), ∀ x ∈ L (n0 + j) v, ω (φ x) < -T}) ≤
          2 * (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * ζ ^ ((m1 : ℝ) / 2) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (1 / 24) ^ 8 by positivity)] with ζ hζ
      exact key ζ hζ.1 hζ.2.le (by rw [← h0]; exact hζ.1.le)
    have hlim : Filter.Tendsto (fun ζ : ℝ => 2 * (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * ζ ^ ((m1 : ℝ) / 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (2 * (4 ^ (n0 + 7) * 3 ^ (n0 + 3)) * (0 : ℝ) ^ ((m1 : ℝ) / 2))) :=
      ((Real.continuousAt_rpow_const 0 ((m1 : ℝ) / 2) (Or.inr (by positivity))).tendsto.const_mul
        _).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow (by positivity), mul_zero] at hlim
    exact ge_of_tendsto hlim hev
  · exact key pT hpos hp le_rfl
/-- For every `m1 ≥ 1` the probability that the forward reachable set of a site is finite with at
least `m1 ^ 2` elements is at most a constant times `pT ^ (m1 / 2)`, uniformly in the law, the
threshold and the site, once the very bad probability `pT` is at most a fixed cutoff. -/
theorem reach_large_finite_tail (m1 : ℕ) (hm1 : 1 ≤ m1) :
    let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
      {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
    ∃ C p : ℝ, 0 < p ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (z : Lattice),
      μ.real (Set.Iio (-T)) ≤ p →
        (environmentLaw μ).real {ω | (m1 : ℝ) ^ 2 ≤ ((reach ω T z).ncard : ℝ) ∧
          (reach ω T z).Finite} ≤ C * (μ.real (Set.Iio (-T))) ^ ((m1 : ℝ) / 2) := by
  intro reach
  obtain ⟨W, B, C, hW, hBC, hcover⟩ := exists_cell_set_contour_cover
  obtain ⟨K, p, hp, hub⟩ := union_bound m1 hm1 W B hW fun n v hv => (hBC n v hv).1
  refine ⟨K, p, hp, fun μ _ T z hpT => ?_⟩
  have hinj : Function.Injective (fun x : ℕ × ℕ => z + ((x.1 : ℤ), (x.2 : ℤ))) := by
    intro a b h
    have := add_left_cancel h
    exact Prod.ext (by simpa using congrArg Prod.fst this) (by simpa using congrArg Prod.snd this)
  refine le_trans (measureReal_mono ?_) (hub μ T _ hinj hpT)
  rintro ω ⟨hbig, hfin⟩
  obtain ⟨Tf, hcard, hq, h0, hc, hcl⟩ := forward_cells (ω := ω) (T := T) (z := z) hfin
  obtain ⟨n, v, hv, harea, hB, -⟩ := hcover Tf hq h0 hc
  have hn : 4 * m1 ≤ n + 4 := by
    have h2 : m1 ^ 2 ≤ Tf.card := by
      have : (m1 : ℝ) ^ 2 ≤ (Tf.card : ℝ) := by rw [hcard]; exact hbig
      exact_mod_cast this
    by_contra h
    replace h := not_le.mp h
    nlinarith [Nat.pow_lt_pow_left h (by norm_num : (2 : ℕ) ≠ 0)]
  obtain ⟨j, rfl⟩ : ∃ j, n = 4 * m1 - 4 + j := ⟨n - (4 * m1 - 4), by omega⟩
  refine Set.mem_iUnion.mpr ⟨j, v, hv, fun x hx => ?_⟩
  by_contra hgood
  have := hcl _ (hB x hx).1 (by simpa using not_lt.mp hgood)
  rcases (hB x hx).2 with h | h
  · exact h (by simpa using this.1)
  · exact h (by simpa using this.2)

/-- The same bound for the backward reachable set, with the reversed terminal convention. -/
theorem reachBack_large_finite_tail (m1 : ℕ) (hm1 : 1 ≤ m1) :
    let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
      {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
    ∃ C p : ℝ, 0 < p ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (z : Lattice),
      μ.real (Set.Iio (-T)) ≤ p →
        (environmentLaw μ).real {ω | (m1 : ℝ) ^ 2 ≤ ((reachBack ω T z).ncard : ℝ) ∧
          (reachBack ω T z).Finite} ≤ C * (μ.real (Set.Iio (-T))) ^ ((m1 : ℝ) / 2) := by
  intro reachBack
  obtain ⟨W, B, C, hW, hBC, hcover⟩ := exists_cell_set_contour_cover
  obtain ⟨K, p, hp, hub⟩ := union_bound m1 hm1 W C hW fun n v hv => (hBC n v hv).2
  refine ⟨K, p, hp, fun μ _ T z hpT => ?_⟩
  have hinj : Function.Injective (fun x : ℕ × ℕ => z - ((x.1 : ℤ), (x.2 : ℤ))) := by
    intro a b h
    have := sub_right_injective h
    exact Prod.ext (by simpa using congrArg Prod.fst this) (by simpa using congrArg Prod.snd this)
  refine le_trans (measureReal_mono ?_) (hub μ T _ hinj hpT)
  rintro ω ⟨hbig, hfin⟩
  obtain ⟨Tb, hcard, hq, h0, hc, hcl1, hcl2⟩ := backward_cells (ω := ω) (T := T) (z := z) hfin
  obtain ⟨n, v, hv, harea, -, hC⟩ := hcover Tb hq h0 hc
  have hn : 4 * m1 ≤ n + 4 := by
    have h2 : m1 ^ 2 ≤ Tb.card := by
      have : (m1 : ℝ) ^ 2 ≤ (Tb.card : ℝ) := by rw [hcard]; exact hbig
      exact_mod_cast this
    by_contra h
    replace h := not_le.mp h
    nlinarith [Nat.pow_lt_pow_left h (by norm_num : (2 : ℕ) ≠ 0)]
  obtain ⟨j, rfl⟩ : ∃ j, n = 4 * m1 - 4 + j := ⟨n - (4 * m1 - 4), by omega⟩
  refine Set.mem_iUnion.mpr ⟨j, v, hv, fun x hx => ?_⟩
  by_contra hgood
  have hg := not_lt.mp hgood
  obtain ⟨hout, hin⟩ := hC x hx
  rcases hin with h | h
  · refine hout ?_
    have h' : ((x.1 : ℤ), (x.2 : ℤ)) - (1, 0) ∈ Tb := by simpa using h
    simpa using hcl1 _ h' (by simpa using hg)
  · refine hout ?_
    have h' : ((x.1 : ℤ), (x.2 : ℤ)) - (0, 1) ∈ Tb := by simpa using h
    simpa using hcl2 _ h' (by simpa using hg)

end LPPDifferentiability
