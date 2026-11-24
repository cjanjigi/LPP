/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Streams
public import Differentiability.Model.CoarseCrossingBlocks
public import Mathlib.Data.Finset.Option
import all Differentiability.Probability.StairGeometryEvent
import Mathlib.Tactic

/-! The finite family of selected paths in Appendix B, item (U5). -/

@[expose] public section

namespace LPPDifferentiability.SelectedGridPaths

open StairGeometry Set
open scoped Classical

/-- The mesh and width of a grid scale. -/
abbrev mesh (mk j : ℕ) : ℕ := 2 ^ (mk - 4 * j - 1)

/-- The source bin width. -/
abbrev width (k j : ℕ) : ℕ := 2 ^ (k - j)

/-- All source scale indices. The family is independent of the lower
index used when estimating crossing probabilities. -/
noncomputable def scales (mk : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌈((mk : ℝ) - 1) / 4⌉₊

/-- The source grid levels on one scale. -/
noncomputable def gridLevels (A : ℝ) (mk j : ℕ) : Finset ℤ :=
  let H := (A + 4) * (2 : ℝ) ^ mk
  (Finset.Icc ⌈-H⌉ ⌊H⌋).filter (fun I => (mesh mk j : ℤ) ∣ I)

theorem mem_gridLevels {A : ℝ} {mk j : ℕ} {I : ℤ} :
    I ∈ gridLevels A mk j ↔ (mesh mk j : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * (2 : ℝ) ^ mk := by
  simp only [gridLevels, Finset.mem_filter, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  exact and_comm

/-- The bins whose half-open transverse intervals meet the source interval. -/
noncomputable def gridBins (R : ℝ) (k j : ℕ) : Finset ℤ :=
  let B := R * (2 : ℝ) ^ k
  let w : ℝ := width k j
  Finset.Icc ⌊-B / w⌋ ⌊B / w⌋

theorem mem_gridBins {R : ℝ} {k j : ℕ} {h : ℤ} (hR : 0 ≤ R) :
    h ∈ gridBins R k j ↔ ∃ ρ : ℝ,
      (h : ℝ) * (width k j : ℝ) ≤ ρ ∧ ρ < ((h : ℝ) + 1) * (width k j : ℝ) ∧
      |ρ| ≤ R * (2 : ℝ) ^ k := by
  let B := R * (2 : ℝ) ^ k
  let w : ℝ := width k j
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw : 0 < w := by dsimp [w, width]; positivity
  change h ∈ Finset.Icc ⌊-B / w⌋ ⌊B / w⌋ ↔
    ∃ ρ : ℝ, (h : ℝ) * w ≤ ρ ∧ ρ < ((h : ℝ) + 1) * w ∧ |ρ| ≤ B
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨hl, hr⟩
    have hcast : ((⌊-B / w⌋ : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hl
    have h₁ : -B < ((h : ℝ) + 1) * w := (div_lt_iff₀ hw).mp
      (by linarith [Int.lt_floor_add_one (-B / w)])
    have h₂ : (h : ℝ) * w ≤ B := (le_div_iff₀ hw).mp (Int.le_floor.mp hr)
    refine ⟨max (-B) ((h : ℝ) * w), le_max_right _ _, max_lt h₁ ?_, abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) h₂⟩⟩
    exact mul_lt_mul_of_pos_right (by linarith) hw
  · rintro ⟨ρ, h₁, h₂, h₃⟩
    obtain ⟨hl, hr⟩ := abs_le.mp h₃
    refine ⟨Int.lt_add_one_iff.mp (Int.floor_lt.mpr ?_),
      Int.le_floor.mpr ((le_div_iff₀ hw).mpr (h₁.trans hr))⟩
    simpa only [Int.cast_add, Int.cast_one] using (div_lt_iff₀ hw).mpr (hl.trans_lt h₂)

theorem workingRegion_finite (a A R C₁ : ℝ) (m : ℕ → ℕ) (k : ℕ) :
    (workingRegion a A R C₁ m k).Finite := by
  let H := (A + 5) * (2 : ℝ) ^ m k
  let B := (R + 2 * C₁ + 10) * (2 : ℝ) ^ k
  apply (boxS_finite_ncard_le a (max 0 H) (max 0 B) (le_max_left _ _) (le_max_left _ _)).1.subset
  rintro z ⟨hz₁, hz₂⟩
  exact ⟨hz₁.trans (le_max_right _ _), hz₂.trans (le_max_right _ _)⟩

/-- The exact finite working window. -/
noncomputable def regionSites (a A R C₁ : ℝ) (m : ℕ → ℕ) (k : ℕ) : Finset Lattice :=
  (workingRegion_finite a A R C₁ m k).toFinset

@[simp] theorem mem_regionSites {a A R C₁ : ℝ} {m : ℕ → ℕ} {k : ℕ} {u : Lattice} :
    u ∈ regionSites a A R C₁ m k ↔ u ∈ workingRegion a A R C₁ m k :=
  Set.Finite.mem_toFinset _

/-- The source trimming window of one block, before clipping to its levels. -/
noncomputable def trimWindow (a : ℝ) (w : ℕ) (I : ℤ) (r₀ : ℕ) (c : Lattice) : Finset Lattice :=
  (exists_finset_signed_level_tube a (8 * (w : ℝ)) (fun _ => transverse a c) I r₀ (by positivity)).choose

theorem trimWindow_spec (a : ℝ) (w : ℕ) (I : ℤ) (r₀ : ℕ) (c : Lattice) :
    (∀ z, z ∈ trimWindow a w I r₀ c ↔
      I ≤ lev z ∧ lev z ≤ I + (r₀ : ℤ) ∧ |transverse a z - transverse a c| ≤ 8 * (w : ℝ)) ∧
    ((trimWindow a w I r₀ c).card : ℝ) ≤ ((r₀ + 1 : ℕ) : ℝ) * (16 * (w : ℝ) + 2) := by
  have h := (exists_finset_signed_level_tube a (8 * (w : ℝ)) (fun _ => transverse a c) I r₀
    (by positivity)).choose_spec
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A fine cell contributes its literal staircase segment when both levels are covered. -/
noncomputable def fineChoice (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ)
    (u : Lattice) (I : ℤ) (l : ℕ) : Option PackedPath :=
  if gammaDefined Q b a u I ∧ gammaDefined Q b a u (I + (l : ℤ)) then
    checkedPath Q b (gammaStream b a u I) l
  else none

/-- The source arrivals start at a defined, nontrapped staircase vertex.
The candidate must reach the target through its prescribed free box. -/
noncomputable def arrivalChoice (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ)
    (L : ℕ) (u v : Lattice) (I : ℤ) : Option PackedPath :=
  let z := gammaPoint b a u I
  let n := (lev v - I).toNat
  if gammaDefined Q b a u I ∧ z ∉ forwardTrapped (maskEnvironment b) 0 ∧
      boxFree (maskEnvironment b) 0 L v ∧ L ≤ n ∧ arrivalStream b L z v n = v then
    checkedPath Q b (arrivalStream b L z v) n
  else none

/-- A nontrapped crossing end contributes the greedy path up to its first
meeting with the staircase and the defined staircase suffix. -/
noncomputable def mergeChoices (Q : Set Lattice) (b : Lattice → Bool) (a : ℝ)
    (Δ₀ : ℕ) (u v : Lattice) (I Λ : ℤ) : Finset PackedPath :=
  if gammaDefined Q b a u I ∧ gammaPoint b a u I ∉ forwardTrapped (maskEnvironment b) 0 ∧
      v ∉ forwardTrapped (maskEnvironment b) 0 then
    match firstMeeting Q b a Δ₀ u v Λ with
    | none => ∅
    | some i =>
      match checkedPath Q b (mergeStream b a Δ₀ u v Λ) i with
      | none => ∅
      | some q =>
        insert q (if gammaDefined Q b a u Λ then
          (checkedPath Q b (gammaStream b a u (lev v + (i : ℤ))) ((Λ - lev v).toNat - i)).toFinset
          else ∅)
  else ∅

/-- The source family `P_k`. There is one fine segment per covered grid
interval, and the coarse candidates are indexed by the literal trimmed
levels of each fixed rounded crossing block. -/
noncomputable def pathFamily (a cstar A R C₁ : ℝ) (m : ℕ → ℕ) (k K₁ K₃ : ℕ)
    (b : Lattice → Bool) : Finset PackedPath :=
  let Q := workingRegion a A R C₁ m k
  let θ₁ := slopeCutoff a
  let L := arrivalBoxSize θ₁ K₁ K₃
  let r₀ := trimLength θ₁ K₁ K₃
  let Δ₀ := deviationBound K₁ K₃
  (regionSites a A R C₁ m k).biUnion fun u =>
    (scales (m k)).biUnion fun j =>
      (gridLevels A (m k) j).biUnion fun I =>
        let l := mesh (m k) j
        let w := width k j
        let B := cstar * ((j : ℝ) ^ 2 * (w : ℝ))
        if (l : ℝ) < 8 * B then (fineChoice Q b a u I l).toFinset
        else
          ((gridBins R k j).filter fun (h : ℤ) =>
            (h : ℝ) * w ≤ transverse a u ∧ transverse a u < ((h : ℝ) + 1) * w).biUnion fun h =>
            (Finset.univ : Finset (Fin (j ^ 2))).biUnion fun ν =>
              let m' := ⌈B⌉₊
              let c := coarseCrossingCentre a h w I m' (ν.val + 1)
              let left := I + (m' : ℤ)
              let right := I + (l : ℤ) - (m' : ℤ)
              ((trimWindow a w left r₀ c).filter fun v => lev v ≤ right).biUnion
                (fun v => (arrivalChoice Q b a L u v I).toFinset) ∪
              ((trimWindow a w (right - (r₀ : ℤ)) r₀ c).filter fun v => left ≤ lev v).biUnion
                (fun v => mergeChoices Q b a Δ₀ u v I (I + (l : ℤ)))

end LPPDifferentiability.SelectedGridPaths
