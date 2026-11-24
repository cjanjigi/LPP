/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.Probability.LevelIndependence
public import Differentiability.Model.OrientedPercolation
import all Differentiability.Probability.HalfLineEdgeDeviation
import Differentiability.Model.OrientedPercolationLaws

/-!
# Half-line edges restarted at the current edge

The restarted process has the law of the whole original half-line edge row
and is independent of the weights through the restart level. These are the
rows and consecutive blocks used in the subadditive edge-speed argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace LPPDifferentiability.FinalDraft

/-- At level `m`, start from all sites to the left of the current edge of
the original half-line process, including the edge. Read the edge after
`k` further steps relative to the restart point. -/
noncomputable def restartedHalfLineEdge (m k : ℕ) (ω : Environment) : ℤ :=
  halfLineEdge (fun z => ω ((halfLineEdge ω m, (m : ℤ) - halfLineEdge ω m) + z)) k

/-- Restarting from the full half-line at the old edge bounds the later
edge of the original process from above. -/
theorem ae_halfLineEdge_add_le_restartedHalfLineEdge (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : 0 < ν {1}) (m k : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν,
      halfLineEdge ω (m + k) ≤ halfLineEdge ω m + restartedHalfLineEdge m k ω :=
  ae_halfLineEdge_add_le ν hν m k

/-- The `k`-step half-line edge only uses levels one through `k`. -/
private theorem halfLineEdge_eq_of_eqOn_levels (k : ℕ) (ω η : Environment)
    (h : ∀ z : Lattice, 0 < z.1 + z.2 → z.1 + z.2 ≤ k → ω z = η z) :
    halfLineEdge ω k = halfLineEdge η k := by
  unfold halfLineEdge openEdge
  rw [openReachSet_congr (topSites ω) (topSites η) antidiagHalfLine 0 k
    antidiagHalfLine_subset_levelSet (fun z h₁ h₂ => by
      show ω z = 1 ↔ η z = 1
      rw [h z h₁ (by simpa only [zero_add] using h₂)])]

/-- The whole restarted row has the original edge law and is independent of
any measurable observation through the restart level. -/
theorem restartedHalfLineEdge_indepFun_identDistrib_row (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (m : ℕ) {γ : Type*} [MeasurableSpace γ]
    (G : Environment → γ) (hG : Measurable[levelsAtMost (m : ℤ)] G) :
    IndepFun G (fun ω k => restartedHalfLineEdge m k ω) (environmentLaw ν) ∧
      IdentDistrib (fun ω k => restartedHalfLineEdge m k ω)
        (fun ω k => halfLineEdge ω k) (environmentLaw ν) (environmentLaw ν) := by
  let T (ω : Environment) : Lattice := (halfLineEdge ω m, (m : ℤ) - halfLineEdge ω m)
  have hT : Measurable[levelsAtMost (m : ℤ)] T :=
    (Measurable.of_discrete (f := fun a : ℤ => ((a, (m : ℤ) - a) : Lattice))).comp
      (measurable_halfLineEdge_levels m)
  have hTlevel (ω : Environment) : (T ω).1 + (T ω).2 = m := by
    dsimp only [T]
    omega
  exact indepFun_identDistrib_shift_of_levelsAtMost ν (m : ℤ) T hT hTlevel
    (fun ω k => halfLineEdge ω k) (Measurable.of_eval measurable_halfLineEdge)
    (fun ω η h => funext fun k => halfLineEdge_eq_of_eqOn_levels k ω η (fun z hz _ => h z hz))
    G hG

/-- The edge read from a fixed site on level `m` for the next `k` levels is
measurable using only the weights through level `m + k`. -/
private theorem measurable_shift_halfLineEdge_atMost (m k : ℕ) (t : Lattice)
    (ht : t.1 + t.2 = m) :
    Measurable[levelsAtMost ((m + k : ℕ) : ℤ)]
      (fun ω : Environment => halfLineEdge (fun z => ω (t + z)) k) := by
  let truncate (ω : Environment) (z : Lattice) : ℝ :=
    if z.1 + z.2 ≤ k then ω (t + z) else 0
  have hMeas {mΩ : MeasurableSpace Environment}
      (h : ∀ z, Measurable[mΩ] (fun ω => truncate ω z)) :
      @Measurable Environment (Lattice → ℝ) mΩ MeasurableSpace.pi truncate :=
    Measurable.of_eval h
  have htruncate : Measurable[levelsAtMost ((m + k : ℕ) : ℤ)] truncate := by
    refine hMeas (mΩ := levelsAtMost ((m + k : ℕ) : ℤ)) (fun z => ?_)
    by_cases hz : z.1 + z.2 ≤ k
    · simp only [truncate, ite_eq_left hz]
      apply Measurable.of_comap_le
      refine le_iSup₂ (f := fun (y : Lattice)
          (_ : y.1 + y.2 ≤ ((m + k : ℕ) : ℤ)) =>
          MeasurableSpace.comap (fun ω : Environment => ω y)
            (inferInstance : MeasurableSpace ℝ)) (t + z) ?_
      simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]
      omega
    · simp only [truncate, ite_eq_right hz]
      exact measurable_const
  have hEq : (fun ω : Environment => halfLineEdge (fun z => ω (t + z)) k) =
      (fun ω : Environment => halfLineEdge (truncate ω) k) := by
    funext ω
    exact halfLineEdge_eq_of_eqOn_levels _ _ _ (fun z _ hz => by simp [truncate, hz])
  rw [hEq]
  exact (measurable_halfLineEdge k).comp htruncate

/-- The `k`-step restarted edge is determined by the weights through level
`m + k`, including those used to choose the restart point. -/
theorem measurable_restartedHalfLineEdge_levelsAtMost (m k : ℕ) :
    Measurable[levelsAtMost ((m + k : ℕ) : ℤ)] (restartedHalfLineEdge m k) := by
  let T (ω : Environment) : Lattice := (halfLineEdge ω m, (m : ℤ) - halfLineEdge ω m)
  have hT : Measurable[levelsAtMost ((m + k : ℕ) : ℤ)] T := by
    have hm : (m : ℤ) ≤ ((m + k : ℕ) : ℤ) := by omega
    exact ((Measurable.of_discrete
      (f := fun a : ℤ => ((a, (m : ℤ) - a) : Lattice))).comp
        (measurable_halfLineEdge_levels m)).mono (levelsAtMost_mono hm) le_rfl
  intro s hs
  let sites := {t : Lattice | t.1 + t.2 = m}
  have hpre : restartedHalfLineEdge m k ⁻¹' s = ⋃ t : sites,
      (T ⁻¹' {t.val}) ∩
        (fun ω : Environment => halfLineEdge (fun z => ω (t.val + z)) k) ⁻¹' s := by
    ext ω
    constructor
    · intro h
      have hLevel : T ω ∈ sites := by
        change (T ω).1 + (T ω).2 = m
        dsimp only [T]
        omega
      exact mem_iUnion.mpr ⟨⟨T ω, hLevel⟩, rfl, h⟩
    · intro h
      obtain ⟨t, ht, hpass⟩ := mem_iUnion.mp h
      have hTt : T ω = t.val := ht
      change halfLineEdge (fun z => ω (T ω + z)) k ∈ s
      rw [hTt]
      exact hpass
  rw [hpre]
  exact MeasurableSet.iUnion (fun t =>
    (hT (measurableSet_singleton t.val)).inter
      (measurable_shift_halfLineEdge_atMost m k t.val t.property hs))

end LPPDifferentiability.FinalDraft
