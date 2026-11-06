/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Probability.DisjointSupportEvents
public import LPP_Foundations.Probability.TranslationEquiv
public import Mathlib.Data.Nat.Dist
import LPP_Foundations.Model.Paths.Fintype
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Translate
import Mathlib.Tactic

/-!
# Black-block events: measurability, stationarity and independence

A black block of scale `N` is an event about the top sites of the environment. This
file proves three facts about these events, as used by the coarse counting argument of
the flat-segment branch. The differentiability preprint, Section 2.3, does not mention block
events.

* Each black-block event is measurable. It is a countable intersection, over start and
  end sites, of "no open path joins them", and an open path joining two fixed sites is a
  finite choice of path with finitely many sites required to have weight one.
* All black-block events have the same probability, because translating the environment
  by `N z` carries the event of block `0` to the event of block `z` and the environment
  law is translation invariant.
* Black-block events of blocks that are far apart (more than `2` in some block
  coordinate) are independent. Block `z` reads only sites in the square
  `N z + [0, 2N]^2` and strictly above the middle level of the block, and these sets are
  disjoint for such blocks.

Level locality (`openReachSet_congr`) is not enough here, since independence needs
locality in the plane. The locality lemma below is proved from the fact that an open path
from `u` to `v` stays in the rectangle between them.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-! ## Private helpers -/

/-- An open path from `u` to `v` only reads sites in the rectangle between `u` and `v`
that lie strictly above the level of `u`. -/
private theorem openReach_of_agree {O O' : Set Lattice} {u v : Lattice}
    (h : ∀ w : Lattice, u ≤ w → w ≤ v → u.1 + u.2 < w.1 + w.2 → w ∈ O → w ∈ O')
    (hr : OpenReach O u v) : OpenReach O' u v := by
  obtain ⟨d, hd, p, hp⟩ := hr
  refine ⟨d, hd, p, fun i => ?_⟩
  have hI := p.vertex_mem_Icc i.succ
  rw [hd] at hI
  have hl := p.level i.succ
  rw [Fin.val_succ] at hl
  refine h _ hI.1 hI.2 ?_ (hp i)
  push_cast at hl
  omega

/-- The sites that the black-block event of block `z` can read. -/
private def blockSupport (N : ℕ) (z : Lattice) : Finset Lattice :=
  (Finset.Icc ((N : ℤ) * z.1, (N : ℤ) * z.2)
      ((N : ℤ) * z.1 + 2 * (N : ℤ), (N : ℤ) * z.2 + 2 * (N : ℤ))).filter
    fun w => (N : ℤ) * z.1 + (N : ℤ) * z.2 + (N : ℤ) < w.1 + w.2

/-- The event of block `z` is determined by the weights on `blockSupport N z`. -/
private theorem isBlackBlock_of_agree (N : ℕ) (c₁ : ℝ) (z : Lattice) {ω ω' : Environment}
    (h : ∀ w ∈ blockSupport N z, ω w = ω' w) :
    IsBlackBlock (topSites ω) N c₁ z → IsBlackBlock (topSites ω') N c₁ z := by
  intro hb u v h1 h2 h3 h4 h5 hr
  refine hb u v h1 h2 h3 h4 h5 (openReach_of_agree ?_ hr)
  intro w huw hwv hl hw
  simp only [Prod.le_def] at h1 h2 huw hwv
  have hmem : w ∈ blockSupport N z := by
    simp only [blockSupport, Finset.mem_filter, Finset.mem_Icc, Prod.le_def]
    omega
  show ω w = 1
  rw [h w hmem]
  exact hw

private theorem isBlackBlock_iff_of_agree (N : ℕ) (c₁ : ℝ) (z : Lattice)
    {ω ω' : Environment} (h : ∀ w ∈ blockSupport N z, ω w = ω' w) :
    (ω ∈ {ω : Environment | IsBlackBlock (topSites ω) N c₁ z}) ↔
      (ω' ∈ {ω : Environment | IsBlackBlock (topSites ω) N c₁ z}) :=
  ⟨isBlackBlock_of_agree N c₁ z h, isBlackBlock_of_agree N c₁ z fun w hw => (h w hw).symm⟩

/-- Measurability of an open-path event between two fixed sites. -/
private theorem measurableSet_openReach (u v : Lattice) :
    MeasurableSet {ω : Environment | OpenReach (topSites ω) u v} := by
  have hset : {ω : Environment | OpenReach (topSites ω) u v} =
      ⋃ (d : ℕ × ℕ) (_ : u + ((d.1 : ℤ), (d.2 : ℤ)) = v) (p : Path u d),
        ⋂ i : Fin (d.1 + d.2), {ω : Environment | ω (p.vertex i.succ) = 1} := by
    ext ω
    constructor
    · rintro ⟨d, hd, p, hp⟩
      exact Set.mem_iUnion.2 ⟨d, Set.mem_iUnion.2 ⟨hd, Set.mem_iUnion.2
        ⟨p, Set.mem_iInter.2 fun i => hp i⟩⟩⟩
    · intro h
      obtain ⟨d, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hd, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨p, h⟩ := Set.mem_iUnion.1 h
      exact ⟨d, hd, p, fun i => Set.mem_iInter.1 h i⟩
  rw [hset]
  refine MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun p => MeasurableSet.iInter fun i => ?_
  exact measurable_environment_eval _ (measurableSet_singleton (1 : ℝ))

/-- A set cut out by a condition that does not depend on the point. -/
private theorem measurableSet_imp {α : Type*} [MeasurableSpace α] (C : Prop)
    {P : α → Prop} (hP : MeasurableSet {a | P a}) : MeasurableSet {a | C → P a} := by
  by_cases hC : C
  · have : {a | C → P a} = {a | P a} := Set.ext fun a => ⟨fun h => h hC, fun h _ => h⟩
    rw [this]
    exact hP
  · have : {a | C → P a} = Set.univ :=
      Set.ext fun a => ⟨fun _ => trivial, fun _ h => absurd h hC⟩
    rw [this]
    exact MeasurableSet.univ

private theorem measurableSet_blackBlock (N : ℕ) (c₁ : ℝ) (z : Lattice) :
    MeasurableSet {ω : Environment | IsBlackBlock (topSites ω) N c₁ z} := by
  have hset : {ω : Environment | IsBlackBlock (topSites ω) N c₁ z} =
      ⋂ u : Lattice, ⋂ v : Lattice, {ω : Environment |
        (((N : ℤ) * z.1, (N : ℤ) * z.2) ≤ u ∧ u ≤ v ∧
          (u.1 - (N : ℤ) * z.1) + (u.2 - (N : ℤ) * z.2) = N ∧
          (v.1 - u.1) + (v.2 - u.2) = N ∧ c₁ * N ≤ ((v.1 - u.1 : ℤ) : ℝ)) →
        ¬ OpenReach (topSites ω) u v} := by
    ext ω
    constructor
    · intro h
      refine Set.mem_iInter.2 fun u => Set.mem_iInter.2 fun v => ?_
      intro hc
      exact h u v hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
    · intro h u v h1 h2 h3 h4 h5
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 h u) v) ⟨h1, h2, h3, h4, h5⟩
  rw [hset]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_
  exact measurableSet_imp _ (measurableSet_openReach u v).compl

/-- Translating the start of an open path translates the open set. -/
private theorem openReach_translate (O : Set Lattice) (t u v : Lattice) :
    OpenReach ((fun z => t + z) ⁻¹' O) u v ↔ OpenReach O (t + u) (t + v) := by
  constructor
  · rintro ⟨d, hd, p, hp⟩
    exact ⟨d, by rw [add_assoc, hd], p.translate t, fun i => hp i⟩
  · rintro ⟨d, hd, p, hp⟩
    refine ⟨d, ?_, Path.untranslate t p, fun i => ?_⟩
    · rw [add_assoc] at hd
      exact add_left_cancel hd
    · show t + (-t + p.vertex i.succ) ∈ O
      rw [add_neg_cancel_left]
      exact hp i

private theorem fst_sub_shift (t u v : Lattice) : (v - t).1 - (u - t).1 = v.1 - u.1 := by
  simp only [Prod.fst_sub]
  omega

private theorem fst_add_shift (t u v : Lattice) : (t + v).1 - (t + u).1 = v.1 - u.1 := by
  simp only [Prod.fst_add]
  omega

private theorem add_sub_self' (t x : Lattice) : t + (x - t) = x := by
  abel

/-- The black-block event of block `z` is the event of block `0` for the environment
translated by `N z`. -/
private theorem isBlackBlock_translate (O : Set Lattice) (N : ℕ) (c₁ : ℝ) (z : Lattice) :
    IsBlackBlock ((fun w : Lattice => ((N : ℤ) * z.1, (N : ℤ) * z.2) + w) ⁻¹' O) N c₁ 0 ↔
      IsBlackBlock O N c₁ z := by
  constructor
  · intro hb u v h1 h2 h3 h4 h5 hr
    refine hb (u - ((N : ℤ) * z.1, (N : ℤ) * z.2)) (v - ((N : ℤ) * z.1, (N : ℤ) * z.2))
      ?_ ?_ ?_ ?_ ?_ ((openReach_translate O _ _ _).2 ?_)
    · simp only [Prod.le_def] at h1
      simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero,
        mul_zero]
      omega
    · simp only [Prod.le_def] at h2
      simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
      omega
    · simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, mul_zero]
      omega
    · simp only [Prod.fst_sub, Prod.snd_sub]
      omega
    · rw [fst_sub_shift]
      exact h5
    · rwa [add_sub_self', add_sub_self']
  · intro hb u v h1 h2 h3 h4 h5 hr
    refine hb (((N : ℤ) * z.1, (N : ℤ) * z.2) + u) (((N : ℤ) * z.1, (N : ℤ) * z.2) + v)
      ?_ ?_ ?_ ?_ ?_ ((openReach_translate O _ _ _).1 hr)
    · simp only [Prod.le_def, Prod.fst_zero, Prod.snd_zero, mul_zero] at h1
      simp only [Prod.le_def, Prod.fst_add, Prod.snd_add]
      omega
    · simp only [Prod.le_def] at h2
      simp only [Prod.le_def, Prod.fst_add, Prod.snd_add]
      omega
    · simp only [Prod.fst_zero, Prod.snd_zero, mul_zero] at h3
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    · simp only [Prod.fst_add, Prod.snd_add]
      omega
    · rw [fst_add_shift]
      exact h5

private theorem blackBlock_real_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (N : ℕ)
    (c₁ : ℝ) (z : Lattice) :
    (environmentLaw ν).real {ω : Environment | IsBlackBlock (topSites ω) N c₁ z} =
      (environmentLaw ν).real {ω : Environment | IsBlackBlock (topSites ω) N c₁ 0} := by
  have hset : {ω : Environment | IsBlackBlock (topSites ω) N c₁ z} =
      environmentTranslationEquiv ((N : ℤ) * z.1, (N : ℤ) * z.2) ⁻¹'
        {ω : Environment | IsBlackBlock (topSites ω) N c₁ 0} := by
    ext ω
    exact (isBlackBlock_translate (topSites ω) N c₁ z).symm
  rw [hset]
  simp only [measureReal_def]
  rw [(measurePreserving_environmentTranslationEquiv ν _).measure_preimage_equiv]

/-- Two squares of side `2 N` whose block coordinates differ by at least three have no
common point in their first coordinate. -/
private theorem coord_disjoint (N : ℕ) (hN : 1 ≤ N) {a b x : ℤ} (hab : a + 3 ≤ b)
    (h1 : (N : ℤ) * b ≤ x) (h2 : x ≤ (N : ℤ) * a + 2 * (N : ℤ)) : False := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have h3 : (N : ℤ) * (a + 3) ≤ (N : ℤ) * b :=
    mul_le_mul_of_nonneg_left hab (by positivity)
  nlinarith

/-! ## The statement -/

theorem blackBlock_measurable_stationary_independent (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (c₁ : ℝ) :
    (∀ z : Lattice, MeasurableSet {ω : Environment | IsBlackBlock (topSites ω) N c₁ z}) ∧
    (∀ z : Lattice, (environmentLaw ν).real {ω | IsBlackBlock (topSites ω) N c₁ z} =
      (environmentLaw ν).real {ω | IsBlackBlock (topSites ω) N c₁ 0}) ∧
    ∀ T : Finset (ℕ × ℕ),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v → 2 < Nat.dist u.1 v.1 ∨ 2 < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} =>
        {ω : Environment | IsBlackBlock (topSites ω) N c₁ ((v.1.1 : ℤ), (v.1.2 : ℤ))})
        (environmentLaw ν) := by
  refine ⟨fun z => measurableSet_blackBlock N c₁ z, fun z => blackBlock_real_eq ν N c₁ z, ?_⟩
  intro T hT
  refine iIndepSet_environment_of_disjoint_supports ν
    (fun v : {u : ℕ × ℕ // u ∈ T} =>
      {ω : Environment | IsBlackBlock (topSites ω) N c₁ ((v.1.1 : ℤ), (v.1.2 : ℤ))})
    (fun v : {u : ℕ × ℕ // u ∈ T} => blockSupport N ((v.1.1 : ℤ), (v.1.2 : ℤ)))
    (fun v => measurableSet_blackBlock N c₁ _)
    (fun v ω ω' h => isBlackBlock_iff_of_agree N c₁ _ h) ?_
  intro v w hvw
  have hd := hT v.1 v.2 w.1 w.2 (fun h => hvw (Subtype.ext h))
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [blockSupport, Finset.mem_filter, Finset.mem_Icc, Prod.le_def] at hx hx'
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · have hN0 : (N : ℤ) = 0 := by exact_mod_cast h0
    rw [hN0] at hx
    omega
  · have hN' : 1 ≤ N := hN
    have hd' : ((v.1.1 : ℤ) + 3 ≤ (w.1.1 : ℤ) ∨ (w.1.1 : ℤ) + 3 ≤ (v.1.1 : ℤ)) ∨
        ((v.1.2 : ℤ) + 3 ≤ (w.1.2 : ℤ) ∨ (w.1.2 : ℤ) + 3 ≤ (v.1.2 : ℤ)) := by
      unfold Nat.dist at hd
      omega
    rcases hd' with (h | h) | (h | h)
    · exact coord_disjoint N hN' h (x := x.1) (by omega) (by omega)
    · exact coord_disjoint N hN' h (x := x.1) (by omega) (by omega)
    · exact coord_disjoint N hN' h (x := x.2) (by omega) (by omega)
    · exact coord_disjoint N hN' h (x := x.2) (by omega) (by omega)

end LPPDifferentiability
