/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.HeavyWorkingRegion
public import Differentiability.Model.Paths.GreedyAttachmentSequence
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The index box and the measurability of the staircase family (item (C5) of Appendix B)

Helper facts for the family `𝒫_k` of the staircase event of Lemma B.6 of the differentiability
preprint:

* `{b | (reach b y).Finite}` is measurable in the product sigma-algebra on masks
  (a countable union of countable intersections of events on finitely many coordinates),
  and so is the same set for the backward reach set;
* the greedy vertex of a mask-dependent avoided set is measurable in the mask, if the
  membership events of the avoided set are;
* a finite box of labels with at most `(2^k)^11` elements that contains every member of the
  four clauses of the family, and a finite cover of the region `𝒬_k`.
-/

public section

open MeasureTheory Filter
open scoped Topology Classical

namespace LPPDifferentiability

private theorem path_vertex_injective (u : Lattice) (d : ℕ × ℕ) :
    Function.Injective (fun p : Path u d => p.vertex) := by
  intro p q h
  cases p
  cases q
  simp only at h
  subst h
  rfl

private theorem measurableSet_coord_false (y : Lattice) :
    MeasurableSet {b : Lattice → Bool | b y = false} :=
  show MeasurableSet ((fun b : Lattice → Bool => b y) ⁻¹' {false}) from
    (measurable_pi_apply y) (measurableSet_singleton false)

private theorem measurableSet_finite_image (σ e : ℕ × ℕ → Lattice) (he : Function.Injective e) :
    MeasurableSet {b : Lattice → Bool | {y' | ∃ (d : ℕ × ℕ) (q : Path (σ d) d), e d = y' ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}.Finite} := by
  let D : (Lattice → Bool) → Set (ℕ × ℕ) := fun b => {d | ∃ q : Path (σ d) d,
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}
  have hD : ∀ d, MeasurableSet {b : Lattice → Bool | d ∈ D b} := by
    intro d
    have : Countable (Path (σ d) d) := (path_vertex_injective _ _).countable
    have hset : {b : Lattice → Bool | d ∈ D b} = ⋃ q : Path (σ d) d,
        ⋂ i : Fin (d.1 + d.2 + 1),
          {b : Lattice → Bool | i.val < d.1 + d.2 → b (q.vertex i) = false} := by
      ext b
      simp only [D, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iInter fun i => ?_
    by_cases h : i.val < d.1 + d.2
    · simp only [h, true_implies]
      exact measurableSet_coord_false _
    · simp only [h, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  have hiff : ∀ b : Lattice → Bool,
      {y' | ∃ (d : ℕ × ℕ) (q : Path (σ d) d), e d = y' ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}.Finite ↔
        ∃ N : ℕ, ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 → d ∉ D b := by
    intro b
    have himg : {y' | ∃ (d : ℕ × ℕ) (q : Path (σ d) d), e d = y' ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false} = e '' D b := by
      ext y'
      simp only [D, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨d, q, hd, hq⟩
        exact ⟨d, ⟨q, hq⟩, hd⟩
      · rintro ⟨d, ⟨q, hq⟩, hd⟩
        exact ⟨d, q, hd, hq⟩
    rw [himg]
    constructor
    · intro hfin
      have hDfin : (D b).Finite := hfin.of_finite_image he.injOn
      obtain ⟨M, hM⟩ := (hDfin.image (fun d : ℕ × ℕ => d.1 + d.2)).bddAbove
      refine ⟨M + 1, fun d hd hdD => ?_⟩
      have := hM (Set.mem_image_of_mem (fun d : ℕ × ℕ => d.1 + d.2) hdD)
      omega
    · rintro ⟨N, hN⟩
      refine Set.Finite.image e (Set.Finite.subset
        ((Set.finite_Iio N).prod (Set.finite_Iio N)) ?_)
      intro d hd
      have := hN d
      simp only [Set.mem_prod, Set.mem_Iio]
      by_contra hcon
      exact this (by omega) hd
  have hset : {b : Lattice → Bool | {y' | ∃ (d : ℕ × ℕ) (q : Path (σ d) d), e d = y' ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}.Finite} =
      ⋃ N : ℕ, ⋂ d : ℕ × ℕ, {b : Lattice → Bool | N ≤ d.1 + d.2 → d ∉ D b} := by
    ext b
    simp only [Set.mem_ofPred_eq, hiff b, Set.mem_iUnion, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun d => ?_
  by_cases h : N ≤ d.1 + d.2
  · simp only [h, true_implies]
    exact (hD d).compl
  · simp only [h, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

/-- The event that the reach set of `y` (admissible paths collecting only sites with mask value
`false`, the terminal site not collected) is finite is measurable for the product
sigma-algebra on masks. -/
theorem measurableSet_reach_finite (y : Lattice) :
    MeasurableSet {b : Lattice → Bool |
      {y' | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = y' ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}.Finite} :=
  measurableSet_finite_image (fun _ => y) (fun d => y + ((d.1 : ℤ), (d.2 : ℤ)))
    (fun d e h => by
      have h' := (add_right_inj _).mp h
      simp only [Prod.mk.injEq, Nat.cast_inj] at h'
      exact Prod.ext h'.1 h'.2)

/-- The same for the backward reach set of `z` (starts of admissible paths that end at `z`). -/
theorem measurableSet_reachBack_finite (z : Lattice) :
    MeasurableSet {b : Lattice → Bool |
      {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false}.Finite} := by
  have key : ∀ b : Lattice → Bool,
      {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false} =
      {y' | ∃ (d : ℕ × ℕ) (q : Path ((fun d : ℕ × ℕ => z - ((d.1 : ℤ), (d.2 : ℤ))) d) d),
        (fun d : ℕ × ℕ => z - ((d.1 : ℤ), (d.2 : ℤ))) d = y' ∧
        ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → b (q.vertex i) = false} := by
    intro b
    ext y
    constructor
    · rintro ⟨d, q, hq, hadm⟩
      have hy : y = z - ((d.1 : ℤ), (d.2 : ℤ)) := eq_sub_of_add_eq hq
      subst hy
      exact ⟨d, q, rfl, hadm⟩
    · rintro ⟨d, q, rfl, hadm⟩
      exact ⟨d, q, sub_add_cancel _ _, hadm⟩
  simp only [key]
  exact measurableSet_finite_image (fun d : ℕ × ℕ => z - ((d.1 : ℤ), (d.2 : ℤ)))
    (fun d : ℕ × ℕ => z - ((d.1 : ℤ), (d.2 : ℤ)))
    (fun d e h => by
      have h' := (sub_right_inj).mp h
      simp only [Prod.mk.injEq, Nat.cast_inj] at h'
      exact Prod.ext h'.1 h'.2)

/-- The greedy vertex is measurable in the mask when the avoided set has measurable
membership events. -/
theorem measurable_greedy_vertex (u : Lattice) (q : ℝ) (V : (Lattice → Bool) → Set Lattice)
    (hV : ∀ y, MeasurableSet {b : Lattice → Bool | y ∈ V b}) (s : ℕ) :
    Measurable (fun b : Lattice → Bool => GreedyAttachment.vertex u q (V b) s) := by
  induction s with
  | zero =>
    have hfun : (fun b : Lattice → Bool => GreedyAttachment.vertex u q (V b) 0) =
        fun _ => u := funext fun b => GreedyAttachment.vertex_zero u q (V b)
    rw [hfun]
    exact measurable_const
  | succ s ih =>
    have hforced : MeasurableSet {b : Lattice → Bool |
        GreedyAttachment.forced u q (V b) s} := by
      have hset : {b : Lattice → Bool | GreedyAttachment.forced u q (V b) s} =
          ⋃ y : Lattice, ({b : Lattice → Bool | GreedyAttachment.vertex u q (V b) s = y} ∩
            {b : Lattice → Bool | GreedyAttachment.preferred u q s y ∈ V b}) := by
        ext b
        simp only [GreedyAttachment.forced, Set.mem_ofPred_eq, Set.mem_iUnion,
          Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨_, rfl, h⟩
        · rintro ⟨y, rfl, h⟩
          exact h
      rw [hset]
      exact MeasurableSet.iUnion fun y => (ih (measurableSet_singleton y)).inter (hV _)
    have hf : Measurable (fun b : Lattice → Bool =>
        GreedyAttachment.alternate u q s (GreedyAttachment.vertex u q (V b) s)) :=
      (measurable_of_countable (GreedyAttachment.alternate u q s)).comp ih
    have hg : Measurable (fun b : Lattice → Bool =>
        GreedyAttachment.preferred u q s (GreedyAttachment.vertex u q (V b) s)) :=
      (measurable_of_countable (GreedyAttachment.preferred u q s)).comp ih
    have hfun : (fun b : Lattice → Bool => GreedyAttachment.vertex u q (V b) (s + 1)) =
        fun b => if GreedyAttachment.forced u q (V b) s then
          GreedyAttachment.alternate u q s (GreedyAttachment.vertex u q (V b) s)
        else GreedyAttachment.preferred u q s (GreedyAttachment.vertex u q (V b) s) :=
      funext fun b => GreedyAttachment.vertex_succ u q (V b) s
    rw [hfun]
    exact Measurable.ite hforced hf hg

private theorem measurableSet_eval_false (w : (Lattice → Bool) → Lattice) (hw : Measurable w) :
    MeasurableSet {b : Lattice → Bool | b (w b) = false} := by
  have h : {b : Lattice → Bool | b (w b) = false} =
      ⋃ y : Lattice, ({b | w b = y} ∩ {b | b y = false}) := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨w b, rfl, h⟩, fun ⟨y, hy, h⟩ => by rw [hy]; exact h⟩
  rw [h]
  exact MeasurableSet.iUnion fun y => (hw (measurableSet_singleton y)).inter
    (measurableSet_coord_false y)

/-- For measurable streams `Y i` of sites, the event that the first `n` sites are not very bad and
lie in `Q`, and that the set of the first `n` sites equals `s`, is measurable in the mask. -/
theorem measurableSet_stream_family (Y : ℕ → (Lattice → Bool) → Lattice)
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) (Q : Set Lattice) (s : Finset Lattice) :
    MeasurableSet {b : Lattice → Bool | (∀ i < n, b (Y i b) = false ∧ Y i b ∈ Q) ∧
      (Finset.range n).image (fun i => Y i b) = s} := by
  have h1 : MeasurableSet {b : Lattice → Bool | ∀ i < n, b (Y i b) = false ∧ Y i b ∈ Q} := by
    have : {b : Lattice → Bool | ∀ i < n, b (Y i b) = false ∧ Y i b ∈ Q} =
        ⋂ i, ⋂ (_ : i < n), ({b | b (Y i b) = false} ∩ {b | Y i b ∈ Q}) := by
      ext b; simp
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_eval_false _ (hY i)).inter (hY i (Set.to_countable Q).measurableSet)
  have h2 : ∀ y, MeasurableSet {b : Lattice → Bool |
      y ∈ (Finset.range n).image (fun i => Y i b)} := by
    intro y
    have : {b : Lattice → Bool | y ∈ (Finset.range n).image (fun i => Y i b)} =
        ⋃ i, ⋃ (_ : i < n), {b | Y i b = y} := by
      ext b; simp
    rw [this]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
      hY i (measurableSet_singleton y)
  have h3 : MeasurableSet {b : Lattice → Bool | (Finset.range n).image (fun i => Y i b) = s} := by
    have : {b : Lattice → Bool | (Finset.range n).image (fun i => Y i b) = s} =
        ⋂ y, {b | y ∈ (Finset.range n).image (fun i => Y i b) ↔ y ∈ s} := by
      ext b; simp [Finset.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun y => ?_
    by_cases hy : y ∈ s
    · have e : {b : Lattice → Bool | y ∈ (Finset.range n).image (fun i => Y i b) ↔ y ∈ s} =
          {b | y ∈ (Finset.range n).image (fun i => Y i b)} := Set.ext fun b => by simp [hy]
      rw [e]; exact h2 y
    · have e : {b : Lattice → Bool | y ∈ (Finset.range n).image (fun i => Y i b) ↔ y ∈ s} =
          {b | y ∈ (Finset.range n).image (fun i => Y i b)}ᶜ := Set.ext fun b => by simp [hy]
      rw [e]; exact (h2 y).compl
  exact h1.inter h3

/-- A finite box of labels `(c, z, u, p, r)` for the four clauses of the staircase family. -/
theorem exists_staircase_index (Qf : Finset Lattice) (S2 N : ℕ) :
    ∃ F : Finset (ℕ × Lattice × Lattice × ℕ × ℕ),
      (∀ z ∈ Qf, ∀ i ≤ S2, ∀ n ≤ N, (0, z, (0, 0), i, n) ∈ F ∧ (1, z, (0, 0), i, n) ∈ F) ∧
      (∀ z ∈ Qf, ∀ v ∈ Qf, ∀ n ≤ N, (2, z, v, 0, n) ∈ F) ∧
      (∀ z ∈ Qf, ∀ u ∈ Qf, ∀ d ≤ N, ∀ n ≤ N, (3, z, u, d, n) ∈ F) ∧
      F.card ≤ 2 * Qf.card * (S2 + 1) * (N + 1) + Qf.card ^ 2 * (N + 1) +
        Qf.card ^ 2 * (N + 1) ^ 2 := by
  let F0 : Finset (ℕ × Lattice × Lattice × ℕ × ℕ) :=
    ({0, 1} : Finset ℕ) ×ˢ Qf ×ˢ ({(0, 0)} : Finset Lattice) ×ˢ Finset.range (S2 + 1) ×ˢ
      Finset.range (N + 1)
  let F2 : Finset (ℕ × Lattice × Lattice × ℕ × ℕ) :=
    ({2} : Finset ℕ) ×ˢ Qf ×ˢ Qf ×ˢ ({0} : Finset ℕ) ×ˢ Finset.range (N + 1)
  let F3 : Finset (ℕ × Lattice × Lattice × ℕ × ℕ) :=
    ({3} : Finset ℕ) ×ˢ Qf ×ˢ Qf ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)
  refine ⟨F0 ∪ F2 ∪ F3, ?_, ?_, ?_, ?_⟩
  · intro z hz i hi n hn
    constructor <;> simp [F0, F2, F3, hz, hi, hn]
  · intro z hz v hv n hn
    simp [F0, F2, F3, hz, hv, hn]
  · intro z hz u hu d hd n hn
    simp [F0, F2, F3, hz, hu, hd, hn]
  · have h01 : ({0, 1} : Finset ℕ).card = 2 := by decide
    have e : F0.card + F2.card + F3.card =
        2 * Qf.card * (S2 + 1) * (N + 1) + Qf.card ^ 2 * (N + 1) +
          Qf.card ^ 2 * (N + 1) ^ 2 := by
      simp only [F0, F2, F3, Finset.card_product, Finset.card_singleton, Finset.card_range, h01]
      ring
    calc (F0 ∪ F2 ∪ F3).card ≤ (F0 ∪ F2).card + F3.card := Finset.card_union_le _ _
      _ ≤ F0.card + F2.card + F3.card := by
        have := Finset.card_union_le F0 F2
        omega
      _ = _ := e

/-- A finite cover of `𝒬_k` and the label boxes of the four clauses, with at most `(2^k)^11`
labels for large `k`. -/
theorem exists_staircase_region_index (a A B cstar : ℝ) (hA : 0 < A)
    (hc : 0 < cstar) (k0 : ℕ) (m : ℕ → ℕ) (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k) :
    ∃ k1 : ℕ, k0 ≤ k1 ∧ ∃ (Qf : ℕ → Finset Lattice)
      (F : ℕ → Finset (ℕ × Lattice × Lattice × ℕ × ℕ)), ∀ k : ℕ, k1 ≤ k →
        (∀ z : Lattice, |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k →
          |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ B * (2 : ℝ) ^ k → z ∈ Qf k) ∧
        ((F k).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ 11 ∧
        (∀ z ∈ Qf k, ∀ i ≤ ⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊,
          ∀ n ≤ ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊,
            (0, z, (0, 0), i, n) ∈ F k ∧ (1, z, (0, 0), i, n) ∈ F k) ∧
        (∀ z ∈ Qf k, ∀ v ∈ Qf k, ∀ n ≤ ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊,
          (2, z, v, 0, n) ∈ F k) ∧
        (∀ z ∈ Qf k, ∀ u ∈ Qf k, ∀ d ≤ ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊,
          ∀ n ≤ ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊, (3, z, u, d, n) ∈ F k) := by
  set R : ℝ := max B 10 with hRdef
  have hBR : B ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_max_of_lt_right (by norm_num)
  have hex : ∀ k : ℕ, ∃ Q : Finset Lattice, k0 ≤ k →
      (∀ z : Lattice, z ∈ Q ↔ |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * 0 + 10) * (2 : ℝ) ^ k) ∧
      (Q.card : ℝ) ≤ (2 * A + 11) * (2 * R + 4 * 0 + 21) * ((2 : ℝ) ^ k) ^ 4 := by
    intro k
    by_cases hk : k0 ≤ k
    · have hells : ((2 ^ m k : ℕ) : ℝ) ≤ ((2 : ℝ) ^ k) ^ 3 := by
        have hmk := hm3 k hk
        push_cast
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      obtain ⟨Q, h1, h2⟩ := exists_finset_heavy_working_region a A R 0 ((2 : ℝ) ^ k) (2 ^ m k)
        hA hRpos le_rfl (one_le_pow₀ (by norm_num)) Nat.one_le_two_pow hells
      refine ⟨Q, fun _ => ⟨fun z => ?_, h2⟩⟩
      have := h1 z
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using this
    · exact ⟨∅, fun h => (hk h).elim⟩
  choose Qf hQf using hex
  choose F hF using fun k : ℕ => exists_staircase_index (Qf k)
    ⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ ⌊8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k⌋₊
  set C0 : ℝ := (2 * A + 11) * (2 * R + 4 * 0 + 21) with hC0
  set C1 : ℝ := 2 * (A + 5) + 1 with hC1
  set C2 : ℝ := 8 * cstar + 1 with hC2
  have hC0pos : 0 < C0 := by rw [hC0]; positivity
  have hC1pos : 0 < C1 := by rw [hC1]; positivity
  have hC2pos : 0 < C2 := by rw [hC2]; positivity
  set G : ℝ := 2 * C0 * C1 * C2 + C0 ^ 2 * C2 + C0 ^ 2 * C2 ^ 2 with hG
  obtain ⟨k2, hk2⟩ : ∃ k2 : ℕ, ∀ k : ℕ, k2 ≤ k → G * (k : ℝ) ^ 4 ≤ (2 : ℝ) ^ k := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt 4
      (by norm_num : (1 : ℝ) < 2)).const_mul G
    rw [mul_zero] at h
    obtain ⟨k2, hk2⟩ := Filter.eventually_atTop.1
      (h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    refine ⟨k2, fun k hk => ?_⟩
    have h1 := hk2 k hk
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [← mul_div_assoc, div_le_one hpos] at h1
    exact h1
  refine ⟨max (max k0 k2) 1, le_trans (le_max_left _ _) (le_max_left _ _),
    Qf, F, fun k hk => ?_⟩
  have hk0 : k0 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2' : k2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨hQmem, hQcard⟩ := hQf k hk0
  obtain ⟨hF0, hF2, hF3, hFcard⟩ := hF k
  refine ⟨fun z h1 h2 => (hQmem z).2 ⟨h1, ?_⟩, ?_, hF0, hF2, hF3⟩
  · refine le_trans h2 ?_
    gcongr
    linarith
  · set s : ℝ := (2 : ℝ) ^ k with hs
    have hs1 : 1 ≤ s := one_le_pow₀ (by norm_num)
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hcast : ((F k).card : ℝ) ≤ 2 * ((Qf k).card : ℝ) *
        ((⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ : ℝ) + 1) *
          ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) +
        ((Qf k).card : ℝ) ^ 2 * ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) +
        ((Qf k).card : ℝ) ^ 2 * ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) ^ 2 := by
      exact_mod_cast hFcard
    have hm3' : (2 : ℝ) ^ m k ≤ s ^ 3 := by
      have hmk := hm3 k hk0
      rw [hs, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
    have hP : ((Qf k).card : ℝ) ≤ C0 * s ^ 4 := hQcard
    have hS : (⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ : ℝ) + 1 ≤ C1 * s ^ 3 := by
      have h1 : (⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ : ℝ) ≤ 2 * (A + 5) * (2 : ℝ) ^ m k :=
        Nat.floor_le (by positivity)
      have h2 : 2 * (A + 5) * (2 : ℝ) ^ m k ≤ 2 * (A + 5) * s ^ 3 := by gcongr
      calc (⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ : ℝ) + 1 ≤ 2 * (A + 5) * s ^ 3 + s ^ 3 := by
            linarith
        _ = C1 * s ^ 3 := by rw [hC1]; ring
    have hZ : (⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1 ≤ C2 * (k : ℝ) ^ 2 * s := by
      have h1 : (⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * s :=
        Nat.floor_le (by positivity)
      have h2 : 1 ≤ (k : ℝ) ^ 2 * s := by
        have : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkr
        nlinarith
      calc (⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1 ≤ 8 * cstar * (k : ℝ) ^ 2 * s +
            (k : ℝ) ^ 2 * s := by linarith
        _ = C2 * (k : ℝ) ^ 2 * s := by rw [hC2]; ring
    have hk24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := pow_le_pow_right₀ hkr (by norm_num)
    have hs8 : s ^ 8 ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
    have hs9 : s ^ 9 ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
    have hk4s : 0 ≤ (k : ℝ) ^ 4 := by positivity
    have hGk : G * (k : ℝ) ^ 4 ≤ s := hk2 k hk2'
    calc ((F k).card : ℝ)
        ≤ 2 * ((Qf k).card : ℝ) * ((⌊2 * (A + 5) * (2 : ℝ) ^ m k⌋₊ : ℝ) + 1) *
          ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) +
          ((Qf k).card : ℝ) ^ 2 * ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) +
          ((Qf k).card : ℝ) ^ 2 * ((⌊8 * cstar * (k : ℝ) ^ 2 * s⌋₊ : ℝ) + 1) ^ 2 := hcast
      _ ≤ 2 * (C0 * s ^ 4) * (C1 * s ^ 3) * (C2 * (k : ℝ) ^ 2 * s) +
          (C0 * s ^ 4) ^ 2 * (C2 * (k : ℝ) ^ 2 * s) +
          (C0 * s ^ 4) ^ 2 * (C2 * (k : ℝ) ^ 2 * s) ^ 2 := by gcongr
      _ = 2 * C0 * C1 * C2 * ((k : ℝ) ^ 2 * s ^ 8) + C0 ^ 2 * C2 * ((k : ℝ) ^ 2 * s ^ 9) +
          C0 ^ 2 * C2 ^ 2 * ((k : ℝ) ^ 4 * s ^ 10) := by ring
      _ ≤ 2 * C0 * C1 * C2 * ((k : ℝ) ^ 4 * s ^ 10) + C0 ^ 2 * C2 * ((k : ℝ) ^ 4 * s ^ 10) +
          C0 ^ 2 * C2 ^ 2 * ((k : ℝ) ^ 4 * s ^ 10) := by
        gcongr
      _ = (G * (k : ℝ) ^ 4) * s ^ 10 := by rw [hG]; ring
      _ ≤ s * s ^ 10 := by gcongr
      _ = s ^ 11 := by ring

end LPPDifferentiability
